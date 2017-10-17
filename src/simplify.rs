use embed::Embed;
use backend::Backend;
use expr::{Expr,Function};
use types::{SortKind,Value};
use parser::CheckSatResult;

pub struct Simplify<B>(B);

impl<B> Simplify<B> {
    pub fn new(backend: B) -> Self {
        Simplify(backend)
    }
}

impl<B : Embed> Embed for Simplify<B> {
    type Sort = B::Sort;
    type Var = B::Var;
    type Expr = B::Expr;
    type Fun = B::Fun;
    type Error = B::Error;
    fn embed_sort(&mut self,k: SortKind<Self::Sort>)
                  -> Result<Self::Sort,Self::Error> {
        self.0.embed_sort(k)
    }
    fn unbed_sort(&mut self,s: &Self::Sort)
                  -> Result<SortKind<Self::Sort>,Self::Error> {
        self.0.unbed_sort(s)
    }
    fn embed(&mut self,e: Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>)
             -> Result<Self::Expr,Self::Error> {
        match e {
            Expr::App(ref fun,ref args) => match *fun {
                Function::Eq(ref s,_) => match self.0.unbed_sort(s)? {
                    SortKind::Bool => {
                        let mut num_false = 0;
                        let mut num_true = 0;
                        for arg in args.iter() {
                            match self.0.unbed(arg)? {
                                Expr::Const(Value::Bool(true)) => {
                                    num_true += 1
                                },
                                Expr::Const(Value::Bool(false)) => {
                                    num_false += 1
                                },
                                _ => {}
                            }
                        }
                        if num_true>0 && num_false>0 {
                            return self.0.embed(Expr::Const(Value::Bool(false)))
                        }
                        if num_true==args.len() || num_false==args.len() {
                            return self.0.embed(Expr::Const(Value::Bool(true)))
                        }
                        if num_true==args.len()-1 {
                            for arg in args.iter() {
                                match self.0.unbed(arg)? {
                                    Expr::Const(Value::Bool(_)) => {},
                                    _ => {
                                        return Ok(arg.clone())
                                    }
                                }
                            }
                        }
                        if num_false>0 || num_true>0 {
                            let mut nargs = Vec::with_capacity(args.len()-num_false-num_true);
                            for arg in args.iter() {
                                match self.0.unbed(arg)? {
                                    Expr::Const(Value::Bool(_)) => {},
                                    _ => {
                                        nargs.push(arg.clone());
                                    }
                                }
                            }
                            if num_true>0 {
                                return self.0.embed(Expr::App(Function::And(args.len()-num_true),
                                                              nargs))
                            }
                            if num_false==args.len()-1 {
                                return self.0.embed(Expr::App(Function::Not,nargs))
                            }
                            for narg in nargs.iter_mut() {
                                *narg = self.0.embed(Expr::App(Function::Not,vec![narg.clone()]))?;
                            }
                            return self.0.embed(Expr::App(Function::And(nargs.len()),nargs))
                        }
                    },
                    _ => {}
                },
                Function::Not => match self.0.unbed(&args[0])? {
                    Expr::Const(Value::Bool(c)) => return self.0.embed(Expr::Const(Value::Bool(!c))),
                    Expr::App(Function::Not,ref not_args) => return Ok(not_args[0].clone()),
                    _ => {}
                },
                Function::And(_) => {
                    let mut num_true = 0;
                    let mut pos = 0;
                    for (n,arg) in args.iter().enumerate() {
                        match self.0.unbed(arg)? {
                            Expr::Const(Value::Bool(true)) => { num_true+=1 },
                            Expr::Const(Value::Bool(false)) => {
                                return self.0.embed(Expr::Const(Value::Bool(false)))
                            },
                            _ => { pos = n }
                        }
                    }
                    match args.len()-num_true {
                        0 => return self.0.embed(Expr::Const(Value::Bool(true))),
                        1 => return Ok(args[pos].clone()),
                        _ => {}
                    }
                    if num_true>0 {
                        let mut nargs = Vec::with_capacity(args.len()-num_true);
                        for arg in args.iter() {
                            match self.0.unbed(arg)? {
                                Expr::Const(Value::Bool(true)) => {},
                                _ => nargs.push(arg.clone())
                            }
                        }
                        return self.0.embed(Expr::App(Function::And(nargs.len()),nargs))
                    }
                },
                Function::ITE(_) => match self.0.unbed(&args[0])? {
                    Expr::Const(Value::Bool(true)) => return Ok(args[1].clone()),
                    Expr::Const(Value::Bool(false)) => return Ok(args[2].clone()),
                    _ => if args[1]==args[2] {
                        return Ok(args[1].clone())
                    } else {
                        match self.0.unbed(&args[1])? {
                            Expr::Const(Value::Bool(c1)) => match self.0.unbed(&args[2])? {
                                Expr::Const(Value::Bool(_)) => if c1 {
                                    // c2 must be false
                                    return Ok(args[0].clone())
                                } else {
                                    return self.0.embed(Expr::App(Function::Not,vec![args[0].clone()]))
                                },
                                _ => if c1 {
                                    return self.0.embed(Expr::App(Function::Or(2),
                                                                  vec![args[0].clone(),
                                                                       args[2].clone()]))
                                } else {
                                    let n0 = self.0.embed(Expr::App(Function::Not,
                                                                    vec![args[0].clone()]))?;
                                    return self.0.embed(Expr::App(Function::And(2),
                                                                  vec![n0,
                                                                       args[2].clone()]))
                                }
                            },
                            _ => match self.0.unbed(&args[2])? {
                                Expr::Const(Value::Bool(c2)) => if c2 {
                                    let n0 = self.0.embed(Expr::App(Function::Not,
                                                                    vec![args[0].clone()]))?;
                                    return self.0.embed(Expr::App(Function::Or(2),
                                                                  vec![n0,
                                                                       args[1].clone()]))
                                } else {
                                    return self.0.embed(Expr::App(Function::And(2),
                                                                  vec![args[0].clone(),
                                                                       args[1].clone()]))
                                },
                                _ => {}
                            }
                        }
                    }
                },
                _ => {}
            },
            _ => {}
        }
        self.0.embed(e)
    }
    fn unbed(&mut self,e: &Self::Expr)
             -> Result<Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>,Self::Error> {
        self.0.unbed(e)
    }
    fn type_of_var(&mut self,v: &Self::Var)
                   -> Result<Self::Sort,Self::Error> {
        self.0.type_of_var(v)
    }
    fn type_of_fun(&mut self,f: &Self::Fun)
                   -> Result<Self::Sort,Self::Error> {
        self.0.type_of_fun(f)
    }
    fn arity(&mut self,f: &Self::Fun) -> Result<usize,Self::Error> {
        self.0.arity(f)
    }
    fn type_of_arg(&mut self,f: &Self::Fun,arg: usize)
                   -> Result<Self::Sort,Self::Error> {
        self.0.type_of_arg(f,arg)
    }
}

impl<B : Backend> Backend for Simplify<B> {
    fn enable_models(&mut self) -> Result<(),Self::Error> {
        self.0.enable_models()
    }
    fn enable_proofs(&mut self) -> Result<(),Self::Error> {
        self.0.enable_proofs()
    }
    fn enable_unsat_cores(&mut self) -> Result<(),Self::Error> {
        self.0.enable_unsat_cores()
    }
    fn enable_interpolants(&mut self) -> Result<(),Self::Error> {
        self.0.enable_interpolants()
    }
    fn solver_name(&mut self) -> Result<String,Self::Error> {
        self.0.solver_name()
    }
    fn solver_version(&mut self) -> Result<String,Self::Error> {
        self.0.solver_version()
    }
    fn comment(&mut self,comment: &str) -> Result<(),Self::Error> {
        self.0.comment(comment)
    }
    fn push(&mut self) -> Result<(),Self::Error> {
        self.0.push()
    }
    fn pop(&mut self) -> Result<(),Self::Error> {
        self.0.pop()
    }
    fn declare_var(&mut self,srt: Self::Sort,name: Option<String>) -> Result<Self::Var,Self::Error> {
        self.0.declare_var(srt,name)
    }
    fn define_var(&mut self,e: Self::Expr) -> Result<Self::Var,Self::Error> {
        self.0.define_var(e)
    }
    fn assert(&mut self,e: Self::Expr) -> Result<(),Self::Error> {
        self.0.assert(e)
    }
    fn check_sat(&mut self) -> Result<CheckSatResult,Self::Error> {
        self.0.check_sat()
    }
    fn get_value(&mut self,e: Self::Expr) -> Result<Value,Self::Error> {
        self.0.get_value(e)
    }
}
