use expr::{Expr,Function};
use types::{Value};
use embed::Embed;
use composite::*;
use std::fmt::Debug;

pub trait Domain<T : Composite> {
    fn full(&T) -> Self;
    fn is_full(&self) -> bool;
    fn union(&mut self,&Self) -> ();
    fn intersection(&mut self,&Self) -> bool;
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(&mut self,&Em::Expr,&mut Em,&F) -> Result<bool,Em::Error>;
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> usize>(&self,&Em::Expr,&mut Em,&F)
                                                      -> Result<Option<Value>,Em::Error>;
}

pub trait Attribute : Sized + Clone {
    fn full() -> Self;
    fn is_full(&self) -> bool;
    fn union(&self,&Self) -> Self;
    fn intersection(&self,&Self) -> Option<Self>;
    fn derive<Em : Embed,Fun : Debug>(Expr<Em::Sort,Self,Self,Fun>,&mut Em) -> Self;
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(&Em::Expr,&mut Vec<Self>,&mut Em,&F) -> Result<bool,Em::Error>;
    fn can_derive_const() -> bool;
    fn is_const(&self) -> Option<Value>;
}

pub struct AttributeDomain<Attr : Attribute> {
    attrs: Vec<Attr>
}

impl<Attr : Attribute> AttributeDomain<Attr> {
    fn expr_attribute<Em : Embed,F : Fn(&Em::Var) -> usize>(&self,e: &Em::Expr,em:&mut Em,f:&F)
                                                            -> Result<Attr,Em::Error> {
        match em.unbed(e)? {
            Expr::Var(ref v) => Ok(self.attrs[f(v)].clone()),
            Expr::Const(v) => {
                let e : Expr<Em::Sort,Attr,Attr,()> = Expr::Const(v);
                Ok(Attr::derive(e,em))
            },
            Expr::App(fun,args) => {
                let mut nargs = Vec::with_capacity(args.len());
                for arg in args {
                    nargs.push(self.expr_attribute(&arg,em,f)?);
                }
                Ok(Attr::derive(Expr::App(fun,nargs),em))
            },
            _ => Ok(Attr::full())
        }
    }
}

impl<Attr : Attribute,T : Composite> Domain<T> for AttributeDomain<Attr> {
    fn full(obj: &T) -> AttributeDomain<Attr> {
        let sz = obj.num_elem();
        let mut vec = Vec::with_capacity(sz as usize);
        vec.resize(sz as usize,Attr::full());
        AttributeDomain { attrs: vec }
    }
    fn is_full(&self) -> bool {
        for i in self.attrs.iter() {
            if !i.is_full() { return false }
        }
        true
    }
    fn union(&mut self,oth: &AttributeDomain<Attr>) {
        let sz = self.attrs.len();
        assert_eq!(sz,oth.attrs.len());
        for i in 0..sz {
            self.attrs[i] = self.attrs[i].union(&oth.attrs[i]);
        }
    }
    fn intersection(&mut self,oth: &AttributeDomain<Attr>) -> bool {
        let sz = self.attrs.len();
        assert_eq!(sz,oth.attrs.len());
        for i in 0..sz {
            match self.attrs[i].intersection(&oth.attrs[i]) {
                Some(nel) => self.attrs[i] = nel,
                None => return false
            }
        }
        true
    }
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(&mut self,e: &Em::Expr,em: &mut Em,f: &F)
                                                    -> Result<bool,Em::Error> {
        Attr::refine(e,&mut self.attrs,em,f)
    }
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> usize>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                                                      -> Result<Option<Value>,Em::Error> {
        if Attr::can_derive_const() {
            let attr = self.expr_attribute(e,em,f)?;
            Ok(attr.is_const())
        } else {
            Ok(None)
        }
    }

}

#[derive(Clone,Debug)]
enum Const {
    IsConst(Value),
    NotConst
}

impl Const {
    fn is_const(&self) -> bool {
        match self {
            &Const::IsConst(_) => true,
            &Const::NotConst => false
        }
    }
}

impl Attribute for Const {
    fn full() -> Const {
        Const::NotConst
    }
    fn is_full(&self) -> bool {
        self.is_const()
    }
    fn union(&self,oth: &Const) -> Const {
        match self {
            &Const::NotConst => Const::NotConst,
            &Const::IsConst(ref v1) => match oth {
                &Const::NotConst => Const::NotConst,
                &Const::IsConst(ref v2) => if *v1==*v2 {
                    Const::IsConst((*v1).clone())
                } else {
                    Const::NotConst
                }
            }
        }
    }
    fn intersection(&self,oth: &Const) -> Option<Const> {
        match self {
            &Const::NotConst => Some(oth.clone()),
            &Const::IsConst(ref v1) => match oth {
                &Const::NotConst => Some(self.clone()),
                &Const::IsConst(ref v2) => if *v1==*v2 {
                    Some(self.clone())
                } else {
                    None
                }
            }
        }
    }
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(e: &Em::Expr,mp: &mut Vec<Const>,em: &mut Em,f: &F)
                                                    -> Result<bool,Em::Error> {
        match em.unbed(e)? {
            Expr::Const(Value::Bool(v)) => Ok(v),
            Expr::Var(ref v) => {
                let rv : usize = f(v);
                match mp[rv] {
                    Const::IsConst(Value::Bool(false))
                        => Ok(false),
                    _ => { mp[rv] = Const::IsConst(Value::Bool(true));
                           Ok(true) }
                }
            },
            Expr::App(ref fun,ref args) => match *fun {
                Function::Not => match em.unbed(&args[0])? {
                    Expr::Var(ref v) => {
                        let rv : usize = f(v);
                        match mp[rv] {
                            Const::IsConst(Value::Bool(false))
                                => Ok(false),
                            _ => { mp[rv] = Const::IsConst(Value::Bool(false));
                                   Ok(true) }
                        }
                    },
                    _ => Ok(true)
                },
                Function::And(_) => {
                    for arg in args.iter() {
                        if !(Self::refine(arg,mp,em,f)?) { return Ok(false) }
                    }
                    Ok(true)
                },
                _ => Ok(true)
            },
            _ => Ok(true)
        }
    }
    fn derive<Em : Embed,Fun : Debug>(e: Expr<Em::Sort,Const,Const,Fun>,_: &mut Em) -> Const {
        match e {
            Expr::Var(val)   => val,
            Expr::Const(val) => Const::IsConst(val),
            Expr::App(fun,args) => match fun {
                Function::Eq(_,_) => if args.len()==0 {
                    Const::IsConst(Value::Bool(true))
                } else {
                    match args[0] {
                        Const::IsConst(ref v) => {
                            for el in args[1..].iter() {
                                match *el {
                                    Const::IsConst(ref nv) => if v!=nv { return Const::NotConst },
                                    Const::NotConst => return Const::NotConst
                                }
                            }
                            Const::IsConst(v.clone())
                        },
                        Const::NotConst => Const::NotConst
                    }
                },
                _ => panic!("Derive function: {:?}",fun)
            },
            _ => panic!("Derive: {:?}",e)
        }
    }
    fn can_derive_const() -> bool { true }
    fn is_const(&self) -> Option<Value> {
        match *self {
            Const::IsConst(ref v) => Some(v.clone()),
            Const::NotConst => None
        }
    }
}

impl<T : Composite> Domain<T> for () {
    fn full(_:&T) -> () { () }
    fn is_full(&self) -> bool { true }
    fn union(&mut self,_:&()) -> () { }
    fn intersection(&mut self,_:&()) -> bool { true }
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(&mut self,_:&Em::Expr,_:&mut Em,_:&F)
                                                    -> Result<bool,Em::Error> {
        Ok(true)
    }
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> usize>(&self,_:&Em::Expr,_:&mut Em,_:&F)
                                                      -> Result<Option<Value>,Em::Error> {
        Ok(None)
    }

}

impl<T : Composite,D1 : Domain<T>,D2 : Domain<T>> Domain<T> for (D1,D2) {
    fn full(obj: &T) -> (D1,D2) {
        let d1 = D1::full(obj);
        let d2 = D2::full(obj);
        (d1,d2)
    }
    fn is_full(&self) -> bool {
        self.0.is_full() &&
            self.1.is_full()
    }
    fn union(&mut self,oth: &(D1,D2)) -> () {
        self.0.union(&oth.0);
        self.1.union(&oth.1);
    }
    fn intersection(&mut self,oth: &(D1,D2)) -> bool {
        if !self.0.intersection(&oth.0) {
            return false
        }
        if !self.1.intersection(&oth.1) {
            return false
        }
        true
    }
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(&mut self,e:&Em::Expr,em:&mut Em,f:&F)
                                                    -> Result<bool,Em::Error> {
        if !self.0.refine(e,em,f)? {
            return Ok(false)
        }
        self.1.refine(e,em,f)
    }
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> usize>(&self,e:&Em::Expr,em:&mut Em,f:&F)
                                                      -> Result<Option<Value>,Em::Error> {
        if let Some(v) = self.0.is_const(e,em,f)? {
            return Ok(Some(v))
        }
        self.1.is_const(e,em,f)
    }
}

impl<T : Composite,D1 : Domain<T>,D2 : Domain<T>,D3 : Domain<T>> Domain<T> for (D1,D2,D3) {
    fn full(obj: &T) -> (D1,D2,D3) {
        let d1 = D1::full(obj);
        let d2 = D2::full(obj);
        let d3 = D3::full(obj);
        (d1,d2,d3)
    }
    fn is_full(&self) -> bool {
        self.0.is_full() &&
            self.1.is_full() &&
            self.2.is_full()
    }
    fn union(&mut self,oth: &(D1,D2,D3)) -> () {
        self.0.union(&oth.0);
        self.1.union(&oth.1);
        self.2.union(&oth.2);
    }
    fn intersection(&mut self,oth: &(D1,D2,D3)) -> bool {
        if !self.0.intersection(&oth.0) {
            return false
        }
        if !self.1.intersection(&oth.1) {
            return false
        }
        if !self.2.intersection(&oth.2) {
            return false
        }
        true
    }
    fn refine<Em : Embed,F : Fn(&Em::Var) -> usize>(&mut self,e:&Em::Expr,em:&mut Em,f:&F)
                                                    -> Result<bool,Em::Error> {
        if !self.0.refine(e,em,f)? {
            return Ok(false)
        }
        if !self.1.refine(e,em,f)? {
            return Ok(false)
        }
        self.2.refine(e,em,f)
    }
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> usize>(&self,e:&Em::Expr,em:&mut Em,f:&F)
                                                      -> Result<Option<Value>,Em::Error> {
        if let Some(v) = self.0.is_const(e,em,f)? {
            return Ok(Some(v))
        }
        if let Some(v) = self.1.is_const(e,em,f)? {
            return Ok(Some(v))
        }
        self.2.is_const(e,em,f)
    }
}
