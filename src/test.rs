use expr::{Expr};
use types::{Sort,SortKind};
use embed::Embed;
use parser::Parser;
use composite::Transformation;
use std::collections::HashMap;
use std::hash::Hash;
use std::str;
use std::fmt::Debug;
use std::clone::Clone;

#[derive(Debug,PartialEq,Eq,Clone,Hash)]
pub struct SimpleExpr<V>(Expr<Sort,V,Box<SimpleExpr<V>>,()>);

#[derive(Debug,PartialEq,Eq,Clone)]
pub struct Simple<V : Eq + Hash + Debug> {
    vars: HashMap<V,Sort>
}

impl<V : Eq + Hash + Debug + Clone> Simple<V> {
    pub fn new() -> Simple<V> {
        Simple { vars: HashMap::new() }
    }
    pub fn add_var(&mut self,v: V,s: Sort) -> Result<Box<SimpleExpr<V>>,()> {
        self.vars.insert(v.clone(),s);
        self.embed(Expr::Var(v))
    }
}

impl<V : Clone + Eq + Hash + Debug> Embed for Simple<V> {
    type Sort = Sort;
    type Var = V;
    type Expr = Box<SimpleExpr<V>>;
    type Fun = ();
    type Error = ();
    fn embed_sort(&mut self,s: SortKind<Sort>)
                  -> Result<Sort,()> {
        Ok(Sort::from_kind(s))
    }
    fn unbed_sort(&mut self,s: &Sort)
                  -> Result<SortKind<Sort>,()> {
        Ok(s.kind())
    }
    fn embed(&mut self,e: Expr<Sort,V,Box<SimpleExpr<V>>,()>)
             -> Result<Box<SimpleExpr<V>>,()> {
        Ok(Box::new(SimpleExpr(e)))
    }
    fn unbed(&mut self,e: &Box<SimpleExpr<V>>)
             -> Result<Expr<Sort,V,Box<SimpleExpr<V>>,()>,()> {
        let SimpleExpr(ref ne) = **e;
        Ok(ne.clone())
    }
    fn type_of_var(&mut self,v: &V)
                   -> Result<Sort,()> {
        match self.vars.get(v) {
            Some(srt) => Ok(srt.clone()),
            None => panic!("Invalid variable")
        }
    }
    fn type_of_fun(&mut self,_: &()) -> Result<Sort,()> {
        Err(())
    }
    fn arity(&mut self,_: &()) -> Result<usize,()> {
        Err(())
    }
    fn type_of_arg(&mut self,_: &(),_: usize) -> Result<Sort,()> {
        Err(())
    }
    fn type_of(&mut self,e: &Box<SimpleExpr<V>>) -> Result<Sort,()> {
        let SimpleExpr(ref re) = **e;
        re.sort(self)
    }
}

impl Parser for Simple<u64> {
    fn parse_var(&mut self,inp: &[u8]) -> Result<u64,()> {
        if inp.len()<3 || inp[0]==b'a' {
            Err(())
        } else {
            match str::from_utf8(&inp[1..]) {
                Err(_) => Err(()),
                Ok(n) => match str::FromStr::from_str(n) {
                    Err(_) => Err(()),
                    Ok(r) => Ok(r)
                }
            }
        }
    }
    fn parse_fun(&mut self,_: &[u8]) -> Result<(),()> {
        Err(())
    }
}

/// Transformation tests
#[test]
fn test_transformation() {
    let mut em : Simple<usize> = Simple::new();
    let tr1 = Transformation::concat(&[Transformation::const_bool(true,&mut em).unwrap(),
                                       Transformation::const_bool(false,&mut em).unwrap()]);
    let ctrue = em.const_bool(true).unwrap();
    let cfalse = em.const_bool(false).unwrap();

    let ivec = [cfalse.clone(),ctrue.clone()];

    let res = tr1.get_all(&ivec,&mut em).unwrap();
    assert_eq!(res,vec![ctrue,cfalse]);
}
