use expr::{Expr};
use types::{SortKind,Value};
use embed::{Embed};
use std::io::{Read,Write,Error,stderr};
use std::collections::HashMap;
use std::process::{Command, Stdio, ChildStdin, ChildStdout };
use parser::*;
use unique::*;
use std::str;
use std::str::FromStr;
use std::fmt;

pub trait Backend : Embed {
    fn enable_models(&mut self) -> Result<(),Self::Error>;
    fn enable_proofs(&mut self) -> Result<(),Self::Error>;
    fn enable_unsat_cores(&mut self) -> Result<(),Self::Error>;
    fn enable_interpolants(&mut self) -> Result<(),Self::Error>;
    fn solver_name(&mut self) -> Result<String,Self::Error>;
    fn solver_version(&mut self) -> Result<String,Self::Error>;
    fn comment(&mut self,&str) -> Result<(),Self::Error>;
    fn push(&mut self) -> Result<(),Self::Error>;
    fn pop(&mut self) -> Result<(),Self::Error>;
    fn declare_var(&mut self,Self::Sort) -> Result<Self::Var,Self::Error>;
    fn define_var(&mut self,Self::Expr) -> Result<Self::Var,Self::Error>;
    fn assert(&mut self,Self::Expr) -> Result<(),Self::Error>;
    fn check_sat(&mut self) -> Result<CheckSatResult,Self::Error>;
    fn get_value(&mut self,Self::Expr) -> Result<Value,Self::Error>;
    fn declare(&mut self,srt: Self::Sort) -> Result<Self::Expr,Self::Error> {
        let var = self.declare_var(srt)?;
        self.embed(Expr::Var(var))
    }
    fn define(&mut self,e: Self::Expr) -> Result<Self::Expr,Self::Error> {
        let var = self.define_var(e)?;
        self.embed(Expr::Var(var))
    }
}

pub struct Pipe<R : Read, W : Write> {
    reader: R,
    writer: W,
    sorts: Uniquer<SortKind<PipeSort>>,
    vars: HashMap<PipeVar,PipeSort>,
    exprs: Uniquer<Expr<PipeSort,PipeVar,PipeExpr,PipeFun>>,
    funs: HashMap<usize,(Vec<PipeSort>,PipeSort)>
}

const PIPE_VAR_NAME: &'static str = "v";
const PIPE_FUN_NAME: &'static str = "f";

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct PipeSort(UniqueRef<SortKind<PipeSort>>);
#[derive(PartialEq,Eq,Hash,Clone,Debug,Copy)]
pub struct PipeVar(usize);
#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct PipeExpr(UniqueRef<Expr<PipeSort,PipeVar,PipeExpr,PipeFun>>);
pub type PipeFun = usize;

impl<Inp : Read,Outp : Write> Pipe<Inp,Outp> {
    pub fn new(inp: Inp,outp: Outp) -> Self {
        Pipe { reader: inp,
               writer: outp,
               sorts: Uniquer::new(),
               vars: HashMap::new(),
               exprs: Uniquer::new(),
               funs: HashMap::new() }
    }
}

impl Pipe<ChildStdout,ChildStdin> {
    pub fn new_process(bin: &str,args: &[&str])
                       -> Result<Pipe<ChildStdout,ChildStdin>,Error> {
        let child = Command::new(bin)
            .args(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()?;
        Ok(Pipe::new(child.stdout.expect("Process API misbehaving"),
                     child.stdin.expect("Process API misbehaving")))
    }
}

#[derive(Debug)]
pub enum PipeError {
    ParseError(ParseError<PipeSort>),
    IOError(Error)
}

pub struct DebugWrite<W : Write>(W);

impl<W : Write> Write for DebugWrite<W> {
    fn write(&mut self,buf: &[u8]) -> Result<usize,Error> {
        let DebugWrite(ref mut w) = *self;
        
        let sz = w.write(buf)?;
        stderr().write(&buf[0..sz])?;
        Ok(sz)
    }
    fn flush(&mut self) -> Result<(),Error> {
        let DebugWrite(ref mut w) = *self;
        w.flush()?;
        stderr().flush()
    }
}

impl<R : Read, W : Write> Pipe<R,W> {
    pub fn debug_write(self) -> Pipe<R,DebugWrite<W>> {
        Pipe { reader: self.reader,
               writer: DebugWrite(self.writer),
               sorts: self.sorts,
               vars: self.vars,
               exprs: self.exprs,
               funs: self.funs }
    }
}

impl<R : Read, W : Write> Embed for Pipe<R,W> {
    type Sort = PipeSort;
    type Var = PipeVar;
    type Expr = PipeExpr;
    type Fun = PipeFun;
    type Error = PipeError;
    fn embed_sort(&mut self,tp: SortKind<PipeSort>)
                  -> Result<PipeSort,PipeError> {
        let utp = self.sorts.get(tp);
        Ok(PipeSort(utp))
    }
    fn unbed_sort(&mut self,tp: &PipeSort)
                  -> Result<SortKind<PipeSort>,PipeError> {
        let PipeSort(ref r) = *tp;
        let tp : &SortKind<PipeSort> = r.get();
        Ok(tp.clone())
    }
    fn embed(&mut self,e: Expr<PipeSort,PipeVar,PipeExpr,PipeFun>)
             -> Result<PipeExpr,PipeError> {
        Ok(PipeExpr(self.exprs.get(e)))
    }
    fn unbed(&mut self,e: &PipeExpr)
             -> Result<Expr<PipeSort,PipeVar,PipeExpr,PipeFun>,PipeError> {
        let PipeExpr(ref ne) = *e;
        let re : &Expr<PipeSort,PipeVar,PipeExpr,PipeFun> = ne.get();
        Ok(re.clone())
    }
    fn type_of(&mut self,e: &PipeExpr) -> Result<PipeSort,PipeError> {
        let PipeExpr(ref e) = *e;
        e.sort(self)
    }
    fn type_of_fun(&mut self,f: &PipeFun)
                   -> Result<PipeSort,PipeError> {
        match self.funs.get(f) {
            Some(&(_,ref srt)) => Ok(srt.clone()),
            None => panic!("Getting type of undeclared function")
        }
    }
    fn type_of_arg(&mut self,f: &PipeFun,arg: usize)
                   -> Result<PipeSort,PipeError> {
        match self.funs.get(f) {
            Some(&(ref args,_)) => Ok(args[arg].clone()),
            None => panic!("Getting argument type of undeclared function")
        }
    }
    fn arity(&mut self,f: &PipeFun) -> Result<usize,PipeError> {
        match self.funs.get(f) {
            Some(&(ref args,_)) => Ok(args.len()),
            None => panic!("Getting arity of undeclared function")
        }
    }
    fn type_of_var(&mut self,v: &PipeVar)
                   -> Result<PipeSort,PipeError> {
        match self.vars.get(v) {
            Some(srt) => Ok(srt.clone()),
            None => panic!("Getting type of undeclared variable")
        }
    }
}

impl fmt::Display for PipeVar {
    fn fmt(&self,f: &mut fmt::Formatter) -> Result<(),fmt::Error> {
        let PipeVar(id) = *self;
        write!(f,"v{}",id)
    }
}

impl fmt::Display for PipeSort {
    fn fmt(&self,f: &mut fmt::Formatter) -> Result<(),fmt::Error> {
        let PipeSort(ref s) = *self;
        fmt::Display::fmt(s.as_ref(),f)
    }
}

impl fmt::Display for PipeExpr {
    fn fmt(&self,f: &mut fmt::Formatter) -> Result<(),fmt::Error> {
        let PipeExpr(ref e) = *self;
        fmt::Display::fmt(e.as_ref(),f)
    }
}

impl From<Error> for PipeError {
    fn from(err: Error) -> PipeError { PipeError::IOError(err) }
}

fn smt_response<R : Read,W : Write,T,F>(p: &mut Pipe<R,W>,parse: F) -> Result<T,PipeError>
    where F : for<'inp> Fn(&'inp[u8],&mut Pos,&mut Pipe<R,W>) -> PResult<'inp,T,Pipe<R,W>> {

    let mut buf = Vec::with_capacity(1024);
    let mut pos = 0;
    buf.resize(1024,0);
    loop {
        if pos==buf.len() {
            buf.resize(pos+1024,0);
        }
        match p.reader.read(&mut buf[pos..]) {
            Err(e) => return Err(PipeError::IOError(e)),
            Ok(sz) => { pos+=sz }
        }
        let mut syn_pos = Pos { line: 0, col: 0 };
        match parse(&buf[0..pos],&mut syn_pos,p) {
            PResult::Done(res,_) => return Ok(res),
            PResult::Incomplete => continue,
            PResult::SyntaxError(err) => return Err(PipeError::ParseError(err)),
            PResult::EmbedError(err) => return Err(err)
        }
    }
}

impl<R : Read,W : Write> Backend for Pipe<R,W> {
    fn enable_models(&mut self) -> Result<(),PipeError> {
        write!(self.writer,"(set-option :produce-models true)\n")
            .map_err(PipeError::IOError)
    }
    fn enable_proofs(&mut self) -> Result<(),PipeError> {
        write!(self.writer,"(set-option :produce-proofs true)\n")
            .map_err(PipeError::IOError)
    }
    fn enable_unsat_cores(&mut self) -> Result<(),PipeError> {
        write!(self.writer,"(set-option :produce-unsat-cores true)\n")
            .map_err(PipeError::IOError)
    }
    fn enable_interpolants(&mut self) -> Result<(),PipeError> {
        write!(self.writer,"(set-option :produce-interpolants true)\n")
            .map_err(PipeError::IOError)
    }
    fn solver_name(&mut self) -> Result<String,PipeError> {
        write!(self.writer,"(get-info :name)\n")
            .map_err(PipeError::IOError)?;
        self.writer.flush().map_err(PipeError::IOError)?;
        smt_response(self,parse_info_response_name)
    }
    fn solver_version(&mut self) -> Result<String,PipeError> {
        write!(self.writer,"(get-info :version)\n").map_err(PipeError::IOError)?;
        self.writer.flush().map_err(PipeError::IOError)?;
        smt_response(self,parse_info_response_version)
    }
    fn comment(&mut self,comment: &str) -> Result<(),PipeError> {
        write!(self.writer,"; {}\n",comment).map_err(PipeError::IOError)
    }
    fn push(&mut self) -> Result<(),PipeError> {
        write!(self.writer,"(push 1)\n").map_err(PipeError::IOError)
    }
    fn pop(&mut self) -> Result<(),PipeError> {
        write!(self.writer,"(pop 1)\n").map_err(PipeError::IOError)
    }
    fn declare_var(&mut self,tp: PipeSort) -> Result<PipeVar,PipeError> {
        let vid = self.vars.len();
        write!(self.writer,"(declare-fun {}{} () {})\n",PIPE_VAR_NAME,vid,tp).map_err(PipeError::IOError)?;
        self.vars.insert(PipeVar(vid),tp);
        Ok(PipeVar(vid))
    }
    fn define_var(&mut self,e: PipeExpr) -> Result<PipeVar,PipeError> {
        let vid = self.vars.len();
        let tp = self.type_of(&e)?;
        write!(self.writer,"(define-fun {}{} () {} {})\n",PIPE_VAR_NAME,vid,tp,e)
            .map_err(PipeError::IOError)?;
        self.vars.insert(PipeVar(vid),tp);
        Ok(PipeVar(vid))
    }
    fn assert(&mut self,expr: PipeExpr) -> Result<(),PipeError> {
        write!(self.writer,"(assert {})\n",expr).map_err(PipeError::IOError)
    }
    fn check_sat(&mut self) -> Result<CheckSatResult,PipeError> {
        write!(self.writer,"(check-sat)\n")?;
        self.writer.flush()?;
        smt_response(self,parse_checksat_result)
    }
    fn get_value(&mut self,expr: PipeExpr) -> Result<Value,PipeError> {
        write!(self.writer,"(get-value ({}))\n",expr).map_err(PipeError::IOError)?;
        self.writer.flush().map_err(PipeError::IOError)?;
        let hint = self.type_of(&expr)?;
        smt_response(self,|inp,pos,p| parse_get_value_result(inp,pos,p,&hint))
    }
}

impl<R : Read,W : Write> Parser for Pipe<R,W> {
    fn parse_var(&mut self,inp: &[u8]) -> Result<PipeVar,PipeError> {
        let pref = PIPE_VAR_NAME.len();
        match str::from_utf8(inp) {
            Err(_) => Err(PipeError::ParseError(ParseError::UnknownVar)),
            Ok(nstr) => if nstr.len() < pref {
                Err(PipeError::ParseError(ParseError::UnknownVar))
            } else if &nstr[0..pref] != PIPE_VAR_NAME {
                Err(PipeError::ParseError(ParseError::UnknownVar))
            } else {
                match FromStr::from_str(&nstr[pref..]) {
                    Err(_) => Err(PipeError::ParseError(ParseError::UnknownVar)),
                    Ok(n) => Ok(PipeVar(n))
                }
            }
        }
    }
    fn parse_fun(&mut self,inp: &[u8]) -> Result<PipeFun,PipeError> {
        let pref = PIPE_FUN_NAME.len();
        match str::from_utf8(&inp[pref..]) {
            Err(_) => Err(PipeError::ParseError(ParseError::UnknownFun)),
            Ok(nstr) => if nstr.len() < pref {
                Err(PipeError::ParseError(ParseError::UnknownFun))
            } else {
                match FromStr::from_str(&nstr[pref..]) {
                    Err(_) => Err(PipeError::ParseError(ParseError::UnknownFun)),
                    Ok(n) => Ok(n)
                }
            }
        }
    }

}

#[test]
fn test_z3() {
    let mut solver = Pipe::new_process("z3",&["-smt2","-in"])
        .expect("Cannot create Z3 solver").debug_write();
    solver.enable_models().expect("Cannot enable models");
    let name = solver.solver_name().expect("Cannot get solver name");
    assert_eq!(name,"Z3".to_string());
    let vers = solver.solver_version().expect("Cannot get solver version");
    assert_eq!(vers,"4.4.1".to_string());
    let tint = solver.tp_int().expect("Cannot create inttype");
    let v1 = solver.declare(tint.clone()).expect("Cannot declare var");
    let v2 = solver.declare(tint).expect("Cannot declare var");
    let eq = solver.eq(v1.clone(),v2.clone()).expect("Cannot create = expr");
    solver.assert(eq.clone()).expect("Cannot assert");
    let res1 = solver.check_sat().expect("Cannot checksat");
    assert_eq!(res1,CheckSatResult::Sat);
    let rv1 = solver.get_value(v1).expect("Canot get-value");
    let rv2 = solver.get_value(v2).expect("Canot get-value");
    assert_eq!(rv1,rv2);
    let neq = solver.not(eq).expect("Cannot create not expr");
    solver.assert(neq).expect("Cannot assert");
    let res2 = solver.check_sat().expect("Cannot checksat");
    assert_eq!(res2,CheckSatResult::Unsat);
}
