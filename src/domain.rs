use expr::{Expr,Function,BVOp,ArithOp,OrdOp};
use types::{Value,bv_signed_value,bv_from_signed_value};
use embed::Embed;
use composite::*;
use std::fmt::Debug;
use std::iter::{Empty,Once,once};
use std::cmp::Ordering;
use num_bigint::BigUint;
use std::ops::{Shl,Shr};
use num_traits::{CheckedSub,ToPrimitive};

pub trait Domain<T : Composite> : Sized {
    type ValueIterator : Iterator<Item=Value>+Clone;
    fn full(&T) -> Self;
    fn is_full(&self) -> bool;
    fn union(&mut self,&Self) -> ();
    fn intersection(&mut self,&Self) -> bool;
    fn refine<Em : Embed,F>(&mut self,&Em::Expr,&mut Em,&F)
                            -> Result<bool,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        Ok(true)
    }
    fn derive<Em : Embed,F>(&self,&[Em::Expr],&mut Em,&F)
                            -> Result<Self,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize>;
    fn is_const<Em : Embed,F>(&self,&Em::Expr,&mut Em,&F)
                              -> Result<Option<Value>,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        Ok(None)
    }
    fn values<Em : Embed,F>(&self,&Em::Expr,&mut Em,&F)
                            -> Result<Option<Self::ValueIterator>,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        Ok(None)
    }
    fn forget_var(&mut self,usize) -> ();
}

pub trait Attribute : Sized + Clone {
    type ValueIterator : Iterator<Item=Value>+Clone;
    fn full() -> Self;
    fn is_full(&self) -> bool;
    fn union(&self,&Self) -> Self;
    fn intersection(&self,&Self) -> Option<Self>;
    fn derive<Em : Embed,Fun : Debug>(Expr<Em::Sort,Self,Self,Fun>,&mut Em) -> Self;
    fn refine<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&Em::Expr,&mut Vec<Self>,&mut Em,&F) -> Result<bool,Em::Error>;
    fn can_derive_const() -> bool;
    fn is_const(&self) -> Option<Value>;
    fn can_derive_values() -> bool;
    fn values(&self) -> Option<Self::ValueIterator>;
}

#[derive(Debug,Clone)]
pub struct AttributeDomain<Attr : Attribute> {
    attrs: Vec<Attr>
}

impl<Attr : Attribute> AttributeDomain<Attr> {
    fn expr_attribute<Em : Embed,F>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                                    -> Result<Attr,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        match em.unbed(e)? {
            Expr::Var(ref v) => match f(v) {
                None => Ok(Attr::full()),
                Some(rv) => Ok(self.attrs[rv].clone())
            },
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
    type ValueIterator = Attr::ValueIterator;
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
    fn refine<Em : Embed,F>(&mut self,e: &Em::Expr,em: &mut Em,f: &F)
                            -> Result<bool,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        Attr::refine(e,&mut self.attrs,em,f)
    }
    fn derive<Em : Embed,F>(&self,exprs: &[Em::Expr],em: &mut Em,f: &F)
                            -> Result<Self,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        let mut ndom = Vec::with_capacity(exprs.len());
        for e in exprs.iter() {
            ndom.push(self.expr_attribute(e,em,f)?);
        }
        Ok(AttributeDomain { attrs: ndom })
    }
    fn is_const<Em : Embed,F>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                              -> Result<Option<Value>,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        if Attr::can_derive_const() {
            let attr = self.expr_attribute(e,em,f)?;
            Ok(attr.is_const())
        } else {
            Ok(None)
        }
    }
    fn values<Em : Embed,F>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                            -> Result<Option<Self::ValueIterator>,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        if Attr::can_derive_values() {
            let attr = self.expr_attribute(e,em,f)?;
            Ok(attr.values())
        } else {
            Ok(None)
        }
    }
    fn forget_var(&mut self,var: usize) -> () {
        self.attrs[var] = Attr::full()
    }
}

#[derive(Clone,Debug)]
pub enum Const {
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
    type ValueIterator = Once<Value>;
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
    fn refine<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(e: &Em::Expr,mp: &mut Vec<Const>,em: &mut Em,f: &F)
                                                            -> Result<bool,Em::Error> {
        match em.unbed(e)? {
            Expr::Const(Value::Bool(v)) => Ok(v),
            Expr::Var(ref v) => match f(v) {
                None => Ok(true),
                Some(rv) => {
                    match mp[rv] {
                        Const::IsConst(Value::Bool(false))
                            => Ok(false),
                        _ => { mp[rv] = Const::IsConst(Value::Bool(true));
                               Ok(true) }
                    }
                }
            },
            Expr::App(ref fun,ref args) => match *fun {
                Function::Not => match em.unbed(&args[0])? {
                    Expr::Var(ref v) => match f(v) {
                        None => Ok(true),
                        Some(rv) => match mp[rv] {
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
                                    Const::IsConst(ref nv) => if v!=nv { return Const::IsConst(Value::Bool(false)) },
                                    Const::NotConst => return Const::NotConst
                                }
                            }
                            Const::IsConst(Value::Bool(true))
                        },
                        Const::NotConst => Const::NotConst
                    }
                },
                Function::Not => match args[0] {
                    Const::IsConst(Value::Bool(x)) => Const::IsConst(Value::Bool(!x)),
                    _ => Const::NotConst
                },
                Function::And(_) => {
                    let mut all_true = true;
                    for arg in args.iter() {
                        match arg {
                            &Const::IsConst(Value::Bool(x)) => if !x {
                                return Const::IsConst(Value::Bool(false))
                            },
                            _ => { all_true = false; }
                        }
                    }
                    if all_true {
                        Const::IsConst(Value::Bool(true))
                    } else {
                        Const::NotConst
                    }
                },
                Function::Or(_) => {
                    let mut all_false = true;
                    for arg in args.iter() {
                        match arg {
                            &Const::IsConst(Value::Bool(x)) => if x {
                                return Const::IsConst(Value::Bool(true))
                            },
                            _ => { all_false = false; }
                        }
                    }
                    if all_false {
                        Const::IsConst(Value::Bool(false))
                    } else {
                        Const::NotConst
                    }
                },
                Function::XOr(_) => {
                    let mut val = false;
                    for arg in args.iter() {
                        match arg {
                            &Const::IsConst(Value::Bool(x)) => {
                                val = val^x;
                            },
                            _ => return Const::NotConst
                        }
                    }
                    Const::IsConst(Value::Bool(val))
                },
                Function::ITE(_) => match args[0] {
                    Const::IsConst(Value::Bool(c)) => if c {
                        args[1].clone()
                    } else {
                        args[2].clone()
                    },
                    _ => match args[1] {
                        Const::IsConst(ref v1) => match args[2] {
                            Const::IsConst(ref v2) => if v1==v2 {
                                Const::IsConst(v1.clone())
                            } else {
                                Const::NotConst
                            },
                            _ => Const::NotConst
                        },
                        _ => Const::NotConst
                    }
                },
                Function::BV(bw,BVOp::Ord(signed,op)) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            if signed {
                                let s_lhs = bv_signed_value(bw,lhs);
                                let s_rhs = bv_signed_value(bw,rhs);
                                let res = match op {
                                    OrdOp::Ge => s_lhs>=s_rhs,
                                    OrdOp::Gt => s_lhs> s_rhs,
                                    OrdOp::Le => s_lhs<=s_rhs,
                                    OrdOp::Lt => s_lhs< s_rhs
                                };
                                Const::IsConst(Value::Bool(res))
                            } else {
                                let res = match op {
                                    OrdOp::Ge => lhs>=rhs,
                                    OrdOp::Gt => lhs> rhs,
                                    OrdOp::Le => lhs<=rhs,
                                    OrdOp::Lt => lhs< rhs
                                };
                                Const::IsConst(Value::Bool(res))
                            }
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::Arith(ArithOp::Add)) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let res = lhs+rhs;
                            let limit = BigUint::from(1 as u8).shl(bw);
                            let nres = if res >= limit {
                                res-limit
                            } else {
                                res
                            };
                            Const::IsConst(Value::BitVec(bw,nres))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::Arith(ArithOp::Sub)) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let res = match lhs.checked_sub(rhs) {
                                Some(r) => r,
                                None => lhs+BigUint::from(1 as u8).shl(bw)-rhs
                            };
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::Arith(ArithOp::Mult)) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let limit = BigUint::from(1 as u8).shl(bw);
                            let res = (lhs*rhs) % limit ;
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::Div(true)) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let rl = bv_signed_value(bw,lhs);
                            let rr = bv_signed_value(bw,rhs);
                            let res = bv_from_signed_value(bw,&(rl/rr));
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::SHL) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let mask = BigUint::from(1 as u8).shl(bw)-(1 as u8);
                            let amount = match rhs.to_usize() {
                                None => bw,
                                Some(r) => if r>bw { bw } else { r }
                            };
                            let shifted = lhs.shl(amount);
                            let res = shifted&mask;
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::ASHR) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let mask = BigUint::from(1 as u8).shl(bw-1);
                            let sgn  = lhs & mask.clone();
                            let amount = match rhs.to_usize() {
                                None => bw,
                                Some(r) => if r>bw { bw } else { r }
                            };
                            let shifted = lhs.shr(amount);
                            let res = if sgn==mask {
                                let ones : BigUint = BigUint::from(1 as u8).shl(amount)-(1 as u8); 
                                shifted | ones.shl(bw-amount)
                            } else {
                                shifted
                            };
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::XOr) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let res = lhs^rhs;
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::And) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(_,ref rhs)) => {
                            let res = lhs&rhs;
                            Const::IsConst(Value::BitVec(bw,res))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::Extract(start,len)) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref x)) => {
                        let x1 = x.shr(start);
                        let mask = BigUint::from(1 as u8).shl(len)-(1 as u8);
                        Const::IsConst(Value::BitVec(bw,x1 & mask))
                    },
                    _ => Const::NotConst
                },
                Function::BV(bw,BVOp::Concat) => match args[0] {
                    Const::IsConst(Value::BitVec(_,ref lhs)) => match args[1] {
                        Const::IsConst(Value::BitVec(bwr,ref rhs)) => {
                            Const::IsConst(Value::BitVec(bw,lhs.shl(bwr) | rhs))
                        },
                        _ => Const::NotConst
                    },
                    _ => Const::NotConst
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
    fn can_derive_values() -> bool { true }
    fn values(&self) -> Option<Self::ValueIterator> {
        match *self {
            Const::IsConst(ref v) => Some(once(v.clone())),
            Const::NotConst => None
        }
    }
}

impl<T : Composite> Domain<T> for () {
    type ValueIterator = Empty<Value>;
    fn full(_:&T) -> () { () }
    fn is_full(&self) -> bool { true }
    fn union(&mut self,_:&()) -> () { }
    fn intersection(&mut self,_:&()) -> bool { true }
    fn derive<Em : Embed,F>(&self,_:&[Em::Expr],_:&mut Em,_:&F)
                            -> Result<Self,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        Ok(())
    }
    fn forget_var(&mut self,_:usize) -> () {}
}

#[derive(Clone)]
pub enum OptIntersection2<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> {
    Only1(It1),
    Only2(It2),
    Both(Intersection2<V,It1,It2>)
}

#[derive(Clone)]
pub struct Intersection2<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> {
    it1: It1,
    it2: It2
}

#[derive(Clone)]
pub struct Union2<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> {
    it1: It1,
    it2: It2,
    buf: Option<(bool,V)>,
}

impl<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> Iterator for OptIntersection2<V,It1,It2> {
    type Item = V;
    fn next(&mut self) -> Option<V> {
        match *self {
            OptIntersection2::Only1(ref mut it) => it.next(),
            OptIntersection2::Only2(ref mut it) => it.next(),
            OptIntersection2::Both(ref mut it) => it.next()
        }
    }
}

impl<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> Union2<V,It1,It2> {
    pub fn new(it1: It1,it2: It2) -> Self {
        Union2 { it1: it1,
                 it2: it2,
                 buf: None }
    }
}

impl<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> Intersection2<V,It1,It2> {
    pub fn new(it1: It1,it2: It2) -> Self {
        Intersection2 { it1: it1,
                        it2: it2 }
    }
}

impl<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> Iterator for Intersection2<V,It1,It2> {
    type Item = V;
    fn next(&mut self) -> Option<V> {
        let mut v1 = match self.it1.next() {
            None => return None,
            Some(v) => v
        };
        let mut v2 = match self.it2.next() {
            None => return None,
            Some(v) => v
        };
        loop {
            match v1.cmp(&v2) {
                Ordering::Equal => return Some(v1),
                Ordering::Less => match self.it1.next() {
                    None => return None,
                    Some(nv1) => v1 = nv1
                },
                Ordering::Greater => match self.it2.next() {
                    None => return None,
                    Some(nv2) => v2 = nv2
                }
            }
        }
    }
    
}

impl<V : Ord,It1 : Iterator<Item=V>,It2 : Iterator<Item=V>> Iterator for Union2<V,It1,It2> {
    type Item = V;
    fn next(&mut self) -> Option<V> {
        let (v1,v2) = match self.buf.take() {
            None => match self.it1.next() {
                None => return self.it2.next(),
                Some(rv1) => match self.it2.next() {
                    None => return Some(rv1),
                    Some(rv2) => (rv1,rv2)
                }
            },
            Some((true,rv1)) => match self.it2.next() {
                None => return Some(rv1),
                Some(rv2) => (rv1,rv2)
            },
            Some((false,rv2)) => match self.it1.next() {
                None => return Some(rv2),
                Some(rv1) => (rv1,rv2)
            }
        };
        
        match v1.cmp(&v2) {
            Ordering::Equal => {
                Some(v1)
            },
            Ordering::Less => {
                self.buf = Some((false,v2));
                Some(v1)
            },
            Ordering::Greater => {
                self.buf = Some((true,v1));
                Some(v2)
            }
        }
    }
}

impl<T : Composite,D1 : Domain<T>,D2 : Domain<T>> Domain<T> for (D1,D2) {
    type ValueIterator = OptIntersection2<Value,D1::ValueIterator,D2::ValueIterator>;
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
    fn refine<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&mut self,e:&Em::Expr,em:&mut Em,f:&F)
                                                            -> Result<bool,Em::Error> {
        if !self.0.refine(e,em,f)? {
            return Ok(false)
        }
        self.1.refine(e,em,f)
    }
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&self,e:&Em::Expr,em:&mut Em,f:&F)
                                                              -> Result<Option<Value>,Em::Error> {
        if let Some(v) = self.0.is_const(e,em,f)? {
            return Ok(Some(v))
        }
        self.1.is_const(e,em,f)
    }
    fn values<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                                                            -> Result<Option<Self::ValueIterator>,Em::Error> {
        match self.0.values(e,em,f)? {
            None => match self.1.values(e,em,f)? {
                None => Ok(None),
                Some(it2) => Ok(Some(OptIntersection2::Only2(it2)))
            },
            Some(it1) => match self.1.values(e,em,f)? {
                None => Ok(Some(OptIntersection2::Only1(it1))),
                Some(it2) => Ok(Some(OptIntersection2::Both(Intersection2::new(it1,it2))))
            }
        }
    }
    fn derive<Em : Embed,F>(&self,exprs: &[Em::Expr],em: &mut Em,f: &F)
                            -> Result<Self,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        let ndom1 = self.0.derive(exprs,em,f)?;
        let ndom2 = self.1.derive(exprs,em,f)?;
        Ok((ndom1,ndom2))
    }
    fn forget_var(&mut self,var: usize) -> () {
        self.0.forget_var(var);
        self.1.forget_var(var);
    }
}
/*
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
*/
