use expr::{Expr,Function};
use types::{Sort,Value};
use composite::*;

pub trait Domain<T : Composite> {
    fn full(&T) -> Self;
    fn is_full(&self) -> bool;
    fn union(&mut self,&Self) -> ();
    fn intersection(&mut self,&Self) -> bool;
}

pub trait Attribute : Sized + Clone {
    fn full() -> Self;
    fn is_full(&self) -> bool;
    fn union(&self,&Self) -> Self;
    fn intersection(&self,&Self) -> Option<Self>;
    fn derive(Expr<Sort,Self,Self,()>) -> Self;
    fn refine<T : Composite>(&CompExpr<T>,&mut Vec<Self>) -> bool;
}

pub struct AttributeDomain<Attr : Attribute> {
    attrs: Vec<Attr>
}

/*impl<Attr : Attribute> AttributeDomain {
    fn expr_attribute<'a,T : Composite<'a>>(&self,e: &CompExpr<'a,T>) -> Attr {
        
    }
}*/

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
    fn refine<T : Composite>(e: &CompExpr<T>,mp: &mut Vec<Const>) -> bool {
        match *e.0 {
            Expr::Const(Value::Bool(v)) => v,
            Expr::Var(ref v) => match mp[*v as usize] {
                Const::IsConst(Value::Bool(false))
                    => false,
                _ => { mp[*v as usize] = Const::IsConst(Value::Bool(true));
                       true }
            },
            Expr::App(ref fun,ref args) => match *fun {
                Function::Not => match *args[0].0 {
                    Expr::Var(ref v) => match mp[*v as usize] {
                        Const::IsConst(Value::Bool(false))
                            => false,
                        _ => { mp[*v as usize] = Const::IsConst(Value::Bool(false));
                               true }
                    },
                    _ => true
                },
                Function::And(_) => {
                    for arg in args.iter() {
                        if !(Self::refine(arg,mp)) { return false }
                    }
                    true
                },
                _ => true
            },
            _ => true
        }
    }
    fn derive(e: Expr<Sort,Const,Const,()>) -> Const {
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
}
