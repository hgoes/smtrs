use types::{Value};
use embed::Embed;
use std::fmt::{Debug,Display,Formatter,Error};

#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub struct NVar<S> {
    id : usize,
    sort : S
}

#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub struct NFun<S> {
    id : usize,
    sort : S,
    arg_sorts : Vec<S>
}

#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub struct NoVar { }

#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub enum Expr<S,V,E,F> {
    Var(V),
    QVar(NVar<S>),
    LVar(NVar<S>),
    Const(Value),
    App(Function<S,F>,Vec<E>),
    AsArray(Function<S,F>),
    Exists(Vec<NVar<S>>,E),
    Forall(Vec<NVar<S>>,E),
    Let(Vec<(NVar<S>,E)>,E)
}

#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub enum Function<S,F> {
    Fun(F),
    Eq(S,usize),
    Distinct(S,usize),
    Map(Box<Function<S,F>>,Vec<S>),
    OrdInt(OrdOp),
    OrdReal(OrdOp),
    ArithInt(ArithOp,usize),
    ArithReal(ArithOp,usize),
    Div,Mod,Rem,Exp,
    Divide,
    AbsInt,AbsReal,
    Not,And(usize),Or(usize),XOr(usize),Implies(usize),
    AtLeast(usize,usize), //X out of Y
    AtMost(usize,usize),
    ToReal,ToInt,
    ITE(S),
    BV(usize,BVOp),
    Select(Vec<S>,S),Store(Vec<S>,S),ConstArray(Vec<S>,S)
}

#[derive(Debug,PartialEq,Eq,Hash,Clone,Copy)]
pub enum OrdOp {
    Ge,Gt,Le,Lt
}

#[derive(Debug,PartialEq,Eq,Hash,Clone,Copy)]
pub enum ArithOp {
    Add,Sub,Mult
}

#[derive(Debug,PartialEq,Eq,Hash,Clone,Copy)]
pub enum BVOp {
    Ord(bool,OrdOp), // signed?, op
    Arith(ArithOp),
    Rem(bool),
    Div(bool),
    SHL,LSHR,ASHR,
    XOr,And,Or,
    Not,Neg,
    Extract(usize,usize) // start, len
}

impl<S : Clone + Eq + Debug,
     V : Clone + Eq + Debug,
     E : Clone + Eq + Debug,
     F : Clone + Eq + Debug> Expr<S,V,E,F> {
    pub fn sort<Em : Embed<Sort=S,
                           Var=V,
                           Expr=E,
                           Fun=F>>(&self,em: &mut Em)
                                   -> Result<S,Em::Error> {
        match *self {
            Expr::Var(ref v) => em.type_of_var(v),
            Expr::QVar(ref v) => Ok((*v).sort.clone()),
            Expr::LVar(ref v) => Ok((*v).sort.clone()),
            Expr::Const(ref c) => (*c).sort(em),
            Expr::App(ref f,_) => (*f).sort(em),
            Expr::AsArray(ref f) => {
                let n = f.arity(em)?;
                let mut idx = Vec::with_capacity(n);
                for i in 0..n {
                    let tp = f.arg_sort(em,i)?;
                    idx.push(tp);
                }
                let el = f.sort(em)?;
                em.tp_array(idx,el)
            },
            Expr::Exists(_,_) => em.tp_bool(),
            Expr::Forall(_,_) => em.tp_bool(),
            Expr::Let(_,ref e) => em.type_of(e)
        }
    }
    pub fn map_expr<NE,Fun : Fn(&E) -> NE>(&self,f: Fun) -> Expr<S,V,NE,F> {
        match *self {
            Expr::Var(ref v) => Expr::Var(v.clone()),
            Expr::QVar(ref v) => Expr::QVar(v.clone()),
            Expr::LVar(ref v) => Expr::LVar(v.clone()),
            Expr::Const(ref c) => Expr::Const(c.clone()),
            Expr::App(ref fun,ref args) => {
                let mut nargs = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    nargs.push(f(arg));
                }
                Expr::App(fun.clone(),nargs)
            }
            Expr::AsArray(ref fun) => Expr::AsArray(fun.clone()),
            Expr::Exists(ref vars,ref body) => Expr::Exists(vars.clone(),f(body)),
            Expr::Forall(ref vars,ref body) => Expr::Forall(vars.clone(),f(body)),
            Expr::Let(ref binds,ref body) => {
                let mut nbinds = Vec::with_capacity(binds.len());
                for &(ref var,ref b) in binds.iter() {
                    nbinds.push((var.clone(),f(b)));
                }
                Expr::Let(nbinds,f(body))
            }
        }
    }
}

impl<S : Clone + Eq + Debug,F : Clone + Eq + Debug> Function<S,F> {
    pub fn sort<Em : Embed<Sort=S,Fun=F>>(&self,em: &mut Em)
                                          -> Result<S,Em::Error> {
        match *self {
            Function::Fun(ref f) => em.type_of_fun(f),
            Function::Eq(_,_) => em.tp_bool(),
            Function::Distinct(_,_) => em.tp_bool(),
            Function::Map(ref f,ref idx) => {
                let fsort = f.sort(em)?;
                em.tp_array((*idx).clone(),fsort)
            },
            Function::OrdInt(_) => em.tp_bool(),
            Function::OrdReal(_) => em.tp_bool(),
            Function::ArithInt(_,_) => em.tp_int(),
            Function::ArithReal(_,_) => em.tp_real(),
            Function::Div => em.tp_int(),
            Function::Mod => em.tp_int(),
            Function::Rem => em.tp_int(),
            Function::Exp => em.tp_int(),
            Function::Divide => em.tp_real(),
            Function::AbsInt => em.tp_int(),
            Function::AbsReal => em.tp_real(),
            Function::Not => em.tp_bool(),
            Function::And(_) => em.tp_bool(),
            Function::Or(_) => em.tp_bool(),
            Function::XOr(_) => em.tp_bool(),
            Function::Implies(_) => em.tp_bool(),
            Function::AtLeast(_,_) => em.tp_bool(),
            Function::AtMost(_,_) => em.tp_bool(),
            Function::ToReal => em.tp_real(),
            Function::ToInt => em.tp_int(),
            Function::ITE(ref s) => Ok((*s).clone()),
            Function::BV(sz,ref op) => match *op {
                BVOp::Ord(_,_) => em.tp_bool(),
                BVOp::Extract(_,len) => em.tp_bitvec(len),
                _ => em.tp_bitvec(sz)
            },
            Function::Select(_,ref r) => Ok((*r).clone()),
            Function::Store(ref idx,ref r) => em.tp_array((*idx).clone(),(*r).clone()),
            Function::ConstArray(ref idx,ref r) => em.tp_array((*idx).clone(),(*r).clone())
        }
    }
    pub fn arity<Em : Embed<Sort=S,Fun=F>>(&self,em: &mut Em) -> Result<usize,Em::Error> {
        match *self {
            Function::Fun(ref f) => em.arity(f),
            Function::Eq(_,sz) => Ok(sz),
            Function::Distinct(_,sz) => Ok(sz),
            Function::Map(_,_) => Ok(1),
            Function::OrdInt(_) => Ok(2),
            Function::OrdReal(_) => Ok(2),
            Function::ArithInt(_,sz) => Ok(sz),
            Function::ArithReal(_,sz) => Ok(sz),
            Function::Div => Ok(2),
            Function::Mod => Ok(2),
            Function::Rem => Ok(2),
            Function::Exp => Ok(2),
            Function::Divide => Ok(2),
            Function::AbsInt => Ok(1),
            Function::AbsReal => Ok(1),
            Function::Not => Ok(1),
            Function::And(sz) => Ok(sz),
            Function::Or(sz) => Ok(sz),
            Function::XOr(sz) => Ok(sz),
            Function::Implies(sz) => Ok(sz),
            Function::AtLeast(_,sz) => Ok(sz),
            Function::AtMost(_,sz) => Ok(sz),
            Function::ToReal => Ok(1),
            Function::ToInt => Ok(1),
            Function::ITE(_) => Ok(3),
            Function::BV(_,ref op) => match *op {
                BVOp::Not | BVOp::Neg | BVOp::Extract(_,_) => Ok(1),
                _ => Ok(2)
            },
            Function::Select(ref idx,_) => Ok(idx.len()+1),
            Function::Store(ref idx,_) => Ok(idx.len()+2),
            Function::ConstArray(_,_) => Ok(1)
        }
    }
    pub fn arg_sort<Em : Embed<Sort=S,Fun=F>>(&self,em: &mut Em, arg: usize)
                                          -> Result<Em::Sort,Em::Error> {
        match *self {
            Function::Fun(ref f) => em.type_of_arg(f,arg),
            Function::Eq(ref s,_) => Ok((*s).clone()),
            Function::Distinct(ref s,_) => Ok((*s).clone()),
            Function::Map(ref fun,ref idx)
                => { let arr_idx = (*idx).clone();
                     let arr_el = fun.arg_sort(em,arg)?;
                     em.tp_array(arr_idx,arr_el) },
            Function::OrdInt(_) => em.tp_int(),
            Function::OrdReal(_) => em.tp_real(),
            Function::ArithInt(_,_) => em.tp_int(),
            Function::ArithReal(_,_) => em.tp_real(),
            Function::Div => em.tp_int(),
            Function::Mod => em.tp_int(),
            Function::Rem => em.tp_int(),
            Function::Exp => em.tp_int(),
            Function::Divide => em.tp_real(),
            Function::AbsInt => em.tp_int(),
            Function::AbsReal => em.tp_real(),
            Function::Not => em.tp_bool(),
            Function::And(_) => em.tp_bool(),
            Function::Or(_) => em.tp_bool(),
            Function::XOr(_) => em.tp_bool(),
            Function::Implies(_) => em.tp_bool(),
            Function::AtLeast(_,_) => em.tp_bool(),
            Function::AtMost(_,_) => em.tp_bool(),
            Function::ToReal => em.tp_int(),
            Function::ToInt => em.tp_real(),
            Function::ITE(ref s) => if arg==0 {
                em.tp_bool()
            } else {
                Ok((*s).clone())
            },
            Function::BV(sz,_) => em.tp_bitvec(sz),
            Function::Select(ref idx,ref srt)
                => if arg==0 {
                    let arr_idx = (*idx).clone();
                    let arr_el = (*srt).clone();
                    em.tp_array(arr_idx,arr_el)
                } else {
                    Ok((*idx)[arg-1].clone())
                },
            Function::Store(ref idx,ref srt)
                => if arg==0 {
                    let arr_idx = (*idx).clone();
                    let arr_el = (*srt).clone();
                    em.tp_array(arr_idx,arr_el)
                } else if arg<=(*idx).len() {
                    Ok((*idx)[arg-1].clone())
                } else {
                    Ok((*srt).clone())
                },
            Function::ConstArray(_,ref srt)
                => Ok((*srt).clone())
        }
    }
}

impl<S,F> Function<S,F> {
    pub fn is_overloaded(&self) -> bool {
        match *self {
            Function::Fun(_) => false,
            Function::Eq(_,_) => true,
            Function::Distinct(_,_) => true,
            Function::ArithInt(_,_) => true,
            Function::ArithReal(_,_) => true,
            Function::And(_) => true,
            Function::Or(_) => true,
            Function::XOr(_) => true,
            Function::Implies(_) => true,
            Function::AtLeast(_,_) => true,
            Function::AtMost(_,_) => true,
            Function::ITE(_) => true,
            Function::BV(_,_) => true,
            Function::Select(_,_) => true,
            Function::Store(_,_) => true,
            _ => false
        }
    }
    pub fn map<S_,F_,Err,TrS,TrF>(&self,trs: &mut TrS,trf: &mut TrF) -> Result<Function<S_,F_>,Err>
        where TrS : FnMut(&S) -> Result<S_,Err>, TrF : FnMut(&F) -> Result<F_,Err> {
        match self {
            &Function::Fun(ref v) => {
                let nv = trf(v)?;
                Ok(Function::Fun(nv))
            },
            &Function::Eq(ref srt,sz) => {
                let nsrt = trs(srt)?;
                Ok(Function::Eq(nsrt,sz))
            },
            &Function::Distinct(ref srt,sz) => {
                let nsrt = trs(srt)?;
                Ok(Function::Distinct(nsrt,sz))
            },
            &Function::Map(ref g,ref idx) => {
                let mut nidx = Vec::with_capacity(idx.len());
                let ng = g.map(trs,trf)?;
                for i in idx.iter() {
                    nidx.push(trs(i)?)
                }
                Ok(Function::Map(Box::new(ng),nidx))
            },
            &Function::OrdInt(op) => Ok(Function::OrdInt(op)),
            &Function::OrdReal(op) => Ok(Function::OrdReal(op)),
            &Function::ArithInt(op,sz) => Ok(Function::ArithInt(op,sz)),
            &Function::ArithReal(op,sz) => Ok(Function::ArithReal(op,sz)),
            &Function::Div => Ok(Function::Div),
            &Function::Mod => Ok(Function::Mod),
            &Function::Rem => Ok(Function::Rem),
            &Function::Exp => Ok(Function::Exp),
            &Function::Divide => Ok(Function::Divide),
            &Function::AbsInt => Ok(Function::AbsInt),
            &Function::AbsReal => Ok(Function::AbsReal),
            &Function::Not => Ok(Function::Not),
            &Function::And(sz) => Ok(Function::And(sz)),
            &Function::Or(sz) => Ok(Function::Or(sz)),
            &Function::XOr(sz) => Ok(Function::XOr(sz)),
            &Function::Implies(sz) => Ok(Function::Implies(sz)),
            &Function::AtLeast(p,sz) => Ok(Function::AtLeast(p,sz)),
            &Function::AtMost(p,sz) => Ok(Function::AtMost(p,sz)),
            &Function::ToReal => Ok(Function::ToReal),
            &Function::ToInt => Ok(Function::ToInt),
            &Function::ITE(ref srt) => {
                let nsrt = trs(srt)?;
                Ok(Function::ITE(nsrt))
            },
            &Function::BV(bw,op) => Ok(Function::BV(bw,op)),
            &Function::Select(ref idx,ref el) => {
                let mut nidx = Vec::with_capacity(idx.len());
                for i in idx.iter() {
                    nidx.push(trs(i)?)
                }
                let nel = trs(el)?;
                Ok(Function::Select(nidx,nel))
            },
            &Function::Store(ref idx,ref el) => {
                let mut nidx = Vec::with_capacity(idx.len());
                for i in idx.iter() {
                    nidx.push(trs(i)?)
                }
                let nel = trs(el)?;
                Ok(Function::Store(nidx,nel))
            },
            &Function::ConstArray(ref idx,ref el) => {
                let mut nidx = Vec::with_capacity(idx.len());
                for i in idx.iter() {
                    nidx.push(trs(i)?)
                }
                let nel = trs(el)?;
                Ok(Function::ConstArray(nidx,nel))
            }
        }
    }
}

impl Display for OrdOp {
    fn fmt(&self,f: &mut Formatter) -> Result<(),Error> {
        match *self {
            OrdOp::Ge => write!(f,">="),
            OrdOp::Gt => write!(f,">"),
            OrdOp::Le => write!(f,"<="),
            OrdOp::Lt => write!(f,"<")
        }
    }
}

impl Display for ArithOp {
    fn fmt(&self,f: &mut Formatter) -> Result<(),Error> {
        match *self {
            ArithOp::Add => write!(f,"+"),
            ArithOp::Sub => write!(f,"-"),
            ArithOp::Mult => write!(f,"*")
        }
    }
}

impl Display for BVOp {
    fn fmt(&self,f: &mut Formatter) -> Result<(),Error> {
        match *self {
            BVOp::Ord(signed,op) => {
                if signed {
                    write!(f,"bvs")?
                } else {
                    write!(f,"bvu")?
                }
                match op {
                    OrdOp::Ge => write!(f,"ge"),
                    OrdOp::Gt => write!(f,"gt"),
                    OrdOp::Le => write!(f,"le"),
                    OrdOp::Lt => write!(f,"lt")
                }
            },
            BVOp::Arith(op) => match op {
                ArithOp::Add => write!(f,"bvadd"),
                ArithOp::Sub => write!(f,"bvsub"),
                ArithOp::Mult => write!(f,"bvmul")
            },
            BVOp::Rem(false) => write!(f,"bvurem"),
            BVOp::Rem(true) => write!(f,"bvsrem"),
            BVOp::Div(false) => write!(f,"bvudiv"),
            BVOp::Div(true) => write!(f,"bvsdiv"),
            BVOp::SHL => write!(f,"bvshl"),
            BVOp::LSHR => write!(f,"bvlshr"),
            BVOp::ASHR => write!(f,"bvashr"),
            BVOp::XOr => write!(f,"bvxor"),
            BVOp::And => write!(f,"bvand"),
            BVOp::Or => write!(f,"bvor"),
            BVOp::Not => write!(f,"bvnot"),
            BVOp::Neg => write!(f,"bvneg"),
            BVOp::Extract(start,len) => {
                let end = start+len;
                write!(f,"(_ extract {} {})",end,start)
            }
        }
    }
}

impl<S : Display,F : Display> Display for Function<S,F> {
    fn fmt(&self,f: &mut Formatter) -> Result<(),Error> {
        match *self {
            Function::Fun(ref fun) => Display::fmt(&fun,f),
            Function::Eq(_,_) => write!(f,"="),
            Function::Distinct(_,_) => write!(f,"distinct"),
            Function::Map(ref fun,_) => write!(f,"(_ map {})",fun),
            Function::OrdInt(op) => Display::fmt(&op,f),
            Function::OrdReal(op) => Display::fmt(&op,f),
            Function::ArithInt(op,_) => Display::fmt(&op,f),
            Function::ArithReal(op,_) => Display::fmt(&op,f),
            Function::Div => write!(f,"div"),
            Function::Mod => write!(f,"mod"),
            Function::Rem => write!(f,"rem"),
            Function::Exp => write!(f,"exp"),
            Function::Divide => write!(f,"/"),
            Function::AbsInt => write!(f,"abs"),
            Function::AbsReal => write!(f,"abs"),
            Function::Not => write!(f,"not"),
            Function::And(_) => write!(f,"and"),
            Function::Or(_) => write!(f,"or"),
            Function::XOr(_) => write!(f,"xor"),
            Function::Implies(_) => write!(f,"=>"),
            Function::AtLeast(x,_) => write!(f,"(_ at-least {})",x),
            Function::AtMost(x,_) => write!(f,"(_ at-most {})",x),
            Function::ToReal => write!(f,"to-real"),
            Function::ToInt => write!(f,"to-int"),
            Function::ITE(_) => write!(f,"ite"),
            Function::BV(_,ref op) => Display::fmt(&op,f),
            Function::Select(_,_) => write!(f,"select"),
            Function::Store(_,_) => write!(f,"store"),
            Function::ConstArray(ref idx,ref el) => {
                write!(f,"(as const (Array ")?;
                for i in idx.iter() {
                    Display::fmt(&i,f)?;
                    write!(f," ")?;
                }
                Display::fmt(&el,f)?;
                write!(f,")")
            }
        }
    }
}

impl<S : Display,
     V : Display,
     E : Display,
     F : Display> Display for Expr<S,V,E,F> {
    
    fn fmt(&self,f: &mut Formatter) -> Result<(),Error> {
        match *self {
            Expr::Var(ref v) => Display::fmt(&v,f),
            Expr::QVar(ref v) => write!(f,"qv{}",v.id),
            Expr::LVar(ref v) => write!(f,"lv{}",v.id),
            Expr::Const(ref c) => Display::fmt(&c,f),
            Expr::App(ref fun,ref args) => {
                write!(f,"({}",fun)?;
                for arg in args.iter() {
                    write!(f," ")?;
                    Display::fmt(&arg,f)?;
                }
                write!(f,")")
            },
            Expr::AsArray(ref fun) => write!(f,"(_ as-array {})",fun),
            Expr::Exists(ref vars,ref body) => {
                write!(f,"(exists (")?;
                for var in vars.iter() {
                    write!(f,"(qv{} {}) ",var.id,var.sort)?;
                }
                write!(f,") {})",body)
            },
            Expr::Forall(ref vars,ref body) => {
                write!(f,"(forall (")?;
                for var in vars.iter() {
                    write!(f,"(qv{} {}) ",var.id,var.sort)?;
                }
                write!(f,") {})",body)
            },
            Expr::Let(ref vars,ref body) => {
                write!(f,"(let (")?;
                for &(ref var,ref bind) in vars.iter() {
                    write!(f,"(lv{} {}) ",var.id,bind)?;
                }
                write!(f,") {})",body)
            }
        }
    }
}

impl Display for NoVar {
    fn fmt(&self,_: &mut Formatter) -> Result<(),Error> {
        unreachable!()
    }
}
