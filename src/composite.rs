use expr;
use types;
use types::{SortKind,Value};
use embed::{Embed,DeriveConst,DeriveValues};
use domain::{Domain};
use unique::{Uniquer,UniqueRef};
use std::cmp::{Ordering,max,min};
use std::collections::BTreeMap;
use std::rc::Rc;
use std::cell;
use std::cell::RefCell;
use std::hash::Hash;
use std::fmt::Debug;
use std::slice;
use std::vec;
use num_bigint::BigInt;
use num_traits::cast::ToPrimitive;
use std::ops::{Range};
use std::iter::{Peekable,Once};
use std::usize;
use std::fmt;
use std::marker::PhantomData;

pub trait Composite : Sized + Eq + Hash + Clone {

    fn num_elem(&self) -> usize;
    fn elem_sort<Em : Embed>(&self,usize,&mut Em)
                             -> Result<Em::Sort,Em::Error>;

    fn combine<'a,Em,FComb,FL,FR>(OptRef<'a,Self>,OptRef<'a,Self>,
                                  Transf<Em>,Transf<Em>,
                                  &FComb,&FL,&FR,&mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>;

    fn invariant<Em : Embed,F>(&self,&mut Em,&F,&mut usize,&mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {
        Ok(())
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub struct CompVar(pub usize);

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct CompExpr<C : Composite>(pub UniqueRef<expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>>);

pub struct Comp<'a,C : Composite + 'a> {
    pub referenced: &'a C,
    pub exprs: &'a mut Uniquer<expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>>
}

pub struct CompDom<'a,C : Composite + 'a,Dom : 'a+Domain<C>> {
    pub comp: Comp<'a,C>,
    pub domain: &'a Dom
}

impl fmt::Display for CompVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"v{}",self.0)
    }
}

impl<'a,C : Composite + Debug> Embed for Comp<'a,C> {
    type Sort = types::Sort;
    type Var = CompVar;
    type Expr = CompExpr<C>;
    type Fun = expr::NoVar;
    type Error = ();
    fn embed_sort(&mut self,tp: SortKind<types::Sort>)
                  -> Result<types::Sort,()> {
        Ok(types::Sort::from_kind(tp))
    }
    fn unbed_sort(&mut self,tp: &types::Sort) -> Result<SortKind<types::Sort>,()> {
        Ok(tp.kind())
    }
    fn embed(&mut self,e: expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>)
             -> Result<CompExpr<C>,()> {
        Ok(CompExpr(self.exprs.get(e)))
    }
    fn unbed(&mut self,e: &CompExpr<C>)
             -> Result<expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>,()> {
        Ok((*e.0).clone())
    }
    fn type_of_var(&mut self,var: &CompVar) -> Result<types::Sort,()> {
        self.referenced.elem_sort(var.0,self)
    }
    fn type_of_fun(&mut self,_:&expr::NoVar) -> Result<types::Sort,()> {
        panic!("Composite expressions don't have functions")
    }
    fn arity(&mut self,_:&expr::NoVar) -> Result<usize,()> {
        panic!("Composite expressions don't have functions")
    }
    fn type_of_arg(&mut self,_:&expr::NoVar,_:usize) -> Result<types::Sort,()> {
        panic!("Composite expressions don't have functions")
    }
}

impl<'a,C : Composite+Debug,Dom : Domain<C>> Embed for CompDom<'a,C,Dom> {
    type Sort = <Comp<'a,C> as Embed>::Sort;
    type Var = <Comp<'a,C> as Embed>::Var;
    type Expr = <Comp<'a,C> as Embed>::Expr;
    type Fun = <Comp<'a,C> as Embed>::Fun;
    type Error = <Comp<'a,C> as Embed>::Error;
    fn embed_sort(&mut self,tp: SortKind<Self::Sort>)
                  -> Result<Self::Sort,Self::Error> {
        self.comp.embed_sort(tp)
    }
    fn unbed_sort(&mut self,tp: &types::Sort) -> Result<SortKind<types::Sort>,Self::Error> {
        self.comp.unbed_sort(tp)
    }
    fn embed(&mut self,e: expr::Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>)
             -> Result<CompExpr<C>,Self::Error> {
        self.comp.embed(e)
    }
    fn unbed(&mut self,e: &Self::Expr)
             -> Result<expr::Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>,Self::Error> {
        self.comp.unbed(e)
    }
    fn type_of_var(&mut self,var: &Self::Var) -> Result<Self::Sort,Self::Error> {
        self.comp.type_of_var(var)
    }
    fn type_of_fun(&mut self,fun:&Self::Fun) -> Result<Self::Sort,Self::Error> {
        self.comp.type_of_fun(fun)
    }
    fn arity(&mut self,fun:&Self::Fun) -> Result<usize,Self::Error> {
        self.comp.arity(fun)
    }
    fn type_of_arg(&mut self,fun:&Self::Fun,p:usize) -> Result<Self::Sort,Self::Error> {
        self.comp.type_of_arg(fun,p)
    }
}

impl<'a,C : Composite+Debug,Dom : Domain<C>> DeriveConst for CompDom<'a,C,Dom> {
    fn derive_const(&mut self,e: &Self::Expr) -> Result<Option<Value>,Self::Error> {
        self.domain.is_const(e,&mut self.comp,&|v:&CompVar| Some(v.0))
    }
}

impl<'a,C : Composite+Debug,Dom : Domain<C>> DeriveValues for CompDom<'a,C,Dom> {
    type ValueIterator = Dom::ValueIterator;
    fn derive_values(&mut self,e: &Self::Expr) -> Result<Option<Self::ValueIterator>,Self::Error> {
        self.domain.values(e,&mut self.comp,&|v:&CompVar| Some(v.0))
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub struct Singleton(pub types::Sort);

impl Composite for Singleton {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,pos:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        debug_assert_eq!(pos,0);
        self.0.embed(em)
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,_: &FL,_: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        if lhs.as_ref().0 == rhs.as_ref().0 {
            Ok(Some((lhs,comb(inp_lhs,inp_rhs,em)?)))
        } else {
            Ok(None)
        }
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Copy,Debug)]
pub struct SingletonBool {}

pub static BOOL_SINGLETON : SingletonBool = SingletonBool {};

impl Composite for SingletonBool {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,pos:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        debug_assert_eq!(pos,0);
        em.tp_bool()
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,_: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,_: &FL,_: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        Ok(Some((lhs,comb(inp_lhs,inp_rhs,em)?)))
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Copy,Debug)]
pub struct SingletonBitVec(pub usize);

impl Composite for SingletonBitVec {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,pos:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        debug_assert_eq!(pos,0);
        em.tp_bitvec(self.0)
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,_: &FL,_: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        if lhs.as_ref().0==rhs.as_ref().0 {
            Ok(Some((lhs,comb(inp_lhs,inp_rhs,em)?)))
        } else {
            Ok(None)
        }
    }
}

impl<T : Composite> Composite for Vec<T> {
    fn num_elem(&self) -> usize {
        let mut acc = 0;
        for el in self.iter() {
            acc+=el.num_elem()
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,n: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let mut acc = 0;
        for el in self.iter() {
            let num = el.num_elem();
            if acc+num > n {
                return el.elem_sort(n-acc,em)
            }
            acc+=num;
        }
        panic!("Invalid index {}",n)
    }
    fn combine<'a,Em,FComb,FL,FR>(mut lhs: OptRef<'a,Self>,mut rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let l_size = lhs.as_ref().len();
        let r_size = rhs.as_ref().len();
        let max_size = max(l_size,r_size);

        let mut new = Vec::with_capacity(max_size);
        let mut ntrans = Vec::with_capacity(max_size);
        let mut l_off = 0;
        let mut r_off = 0;

        let mut l_iter = lhs.iter();
        let mut r_iter = rhs.iter();

        loop {
            match l_iter.next() {
                None => {
                    for el in r_iter {
                        let sz = el.as_ref().num_elem();
                        new.push(el.as_obj());
                        ntrans.push(only_r(Transformation::view(r_off,sz,inp_rhs.clone()),em)?);
                        r_off+=sz;
                    }
                    break
                },
                Some(l_el) => match r_iter.next() {
                    None => {
                        let l_sz = l_el.as_ref().num_elem();
                        new.push(l_el.as_obj());
                        ntrans.push(only_l(Transformation::view(l_off,l_sz,inp_lhs.clone()),em)?);
                        l_off+=l_sz;
                        for el in l_iter {
                            let sz = el.as_ref().num_elem();
                            new.push(el.as_obj());
                            ntrans.push(only_l(Transformation::view(l_off,sz,inp_lhs.clone()),em)?);
                            l_off+=sz;
                        }
                        break
                    },
                    Some(r_el) => {
                        let l_sz = l_el.as_ref().num_elem();
                        let r_sz = r_el.as_ref().num_elem();
                        match T::combine(l_el,r_el,
                                         Transformation::view(l_off,l_sz,inp_lhs.clone()),
                                         Transformation::view(r_off,r_sz,inp_rhs.clone()),
                                         comb,only_l,only_r,em)? {
                            None => return Ok(None),
                            Some((nel,ntr)) => {
                                new.push(nel.as_obj());
                                ntrans.push(ntr);
                                l_off+=l_sz;
                                r_off+=r_sz;
                            }
                        }
                    }
                }
            }
        }
        Ok(Some((OptRef::Owned(new),Transformation::concat(&ntrans[0..]))))
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {

        for el in self.iter() {
            el.invariant(em,f,off,res)?;
        }
        Ok(())
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Choice<T>(Vec<T>);

pub struct Choices<'a,T : 'a,Em : Embed> {
    transf: Transf<Em>,
    off: usize,
    iter: slice::Iter<'a,T>
}

impl<'a,T : 'a + Composite,Em : Embed> Iterator for Choices<'a,T,Em> {
    type Item = (&'a T,Transf<Em>,Transf<Em>);
    fn next(&mut self) -> Option<(&'a T,Transf<Em>,Transf<Em>)> {
        match self.iter.next() {
            None => None,
            Some(el) => {
                let sz = el.num_elem();
                let cond = Transformation::view(self.off,1,self.transf.clone());
                let inp = Transformation::view(self.off+1,sz,self.transf.clone());
                self.off+=sz+1;
                Some((el,cond,inp))
            }
        }
    }
}

impl<'a,T : 'a+Composite+Ord> Choice<T> {
    pub fn new() -> Self {
        Choice(Vec::new())
    }
    pub fn choices<Em : Embed>(&'a self,tr: Transf<Em>) -> Choices<'a,T,Em> {
        Choices { transf: tr,
                  off: 0,
                  iter: self.0.iter() }
    }
    pub fn add(&mut self,el: T) -> () {
        for pos in 0..self.0.len() {
            match el.cmp(&self.0[pos]) {
                Ordering::Equal => return (),
                Ordering::Greater => {},
                Ordering::Less => {
                    self.0.insert(pos,el);
                    return ()
                }
            }
        }
        self.0.push(el)
    }
    pub fn map<Em : Embed,F>(self,inp: Transf<Em>,em: &mut Em,f: &F)
                             -> Result<(Self,Transf<Em>),Em::Error>
        where F : Fn(Transf<Em>,T,Transf<Em>,&mut Em) -> Result<(Transf<Em>,T,Transf<Em>),Em::Error> {
        let mut nvec = Vec::with_capacity(self.0.len());
        let mut ninp = Vec::with_capacity(self.0.len()*2);
        let mut off = 0;
        for el in self.0.into_iter() {
            let sz = el.num_elem();
            let inp_cond = Transformation::view(off,1,inp.clone());
            let inp_el = Transformation::view(off+1,sz,inp.clone());
            let (inp_ncond,nel,inp_nel) = f(inp_cond,el,inp_el,em)?;
            ninp.push(inp_ncond);
            ninp.push(inp_nel);
            nvec.push(nel);
            off+=sz+1;
        }
        Ok((Choice(nvec),Transformation::concat(&ninp[..])))
    }
}

impl<'a,T : 'a> OptRef<'a,Choice<T>> {
    fn elements(self) -> OptRef<'a,Vec<T>> {
        match self {
            OptRef::Ref(r) => OptRef::Ref(&r.0),
            OptRef::Owned(r) => OptRef::Owned(r.0)
        }
    }
}

impl<T : Composite + Ord> Composite for Choice<T> {
    fn num_elem(&self) -> usize {
        let mut acc = 0;
        for el in self.0.iter() {
            acc+=el.num_elem()+1
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,n: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let mut acc = 0;
        for el in self.0.iter() {
            if n==acc {
                return em.embed_sort(SortKind::Bool)
            }
            acc+=1;
            let num = el.num_elem();
            if acc+num > n {
                return el.elem_sort(n-acc,em)
            }
            acc+=num;
        }
        panic!("Invalid index {}",n)
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let l_size = lhs.as_ref().0.len();
        let r_size = rhs.as_ref().0.len();
        let max_size = max(l_size,r_size);

        let mut new = Vec::with_capacity(max_size);
        let mut ntrans = Vec::with_capacity(max_size);
        let mut l_off = 0;
        let mut r_off = 0;

        let mut l_elems = lhs.elements();
        let mut r_elems = rhs.elements();
        let mut l_iter = l_elems.iter();
        let mut r_iter = r_elems.iter();

        let mut l_cur : Option<OptRef<'a,T>> = None;
        let mut r_cur : Option<OptRef<'a,T>> = None;
        
        loop {
            let l_el = match l_cur {
                None => match l_iter.next() {
                    None => {
                        match r_cur {
                            None => {},
                            Some(r_el) => {
                                let obj = r_el.as_obj();
                                let sz = obj.num_elem();
                                new.push(obj);
                                ntrans.push(only_r(Transformation::view(r_off,sz+1,inp_rhs.clone()),em)?);
                                r_off+=sz+1;
                            }
                        }
                        for el in r_iter {
                            let obj = el.as_obj();
                            let sz = obj.num_elem();
                            new.push(obj);
                            ntrans.push(only_r(Transformation::view(r_off,sz+1,inp_rhs.clone()),em)?);
                            r_off+=sz+1;
                        }
                        break
                    },
                    Some(r) => r
                },
                Some(r) => r
            };
            let r_el = match r_cur {
                None => match r_iter.next() {
                    None => {
                        let l_obj = l_el.as_obj();
                        let l_sz = l_obj.num_elem();
                        new.push(l_obj);
                        ntrans.push(only_l(Transformation::view(l_off,l_sz+1,inp_lhs.clone()),em)?);
                        l_off+=l_sz+1;
                        for el in l_iter {
                            let obj = el.as_obj();
                            let sz = obj.num_elem();
                            new.push(obj);
                            ntrans.push(only_l(Transformation::view(l_off,sz+1,inp_lhs.clone()),em)?);
                            l_off+=sz+1;
                        }
                        break
                    },
                    Some(r) => r
                },
                Some(r) => r
            };
            match l_el.as_ref().cmp(r_el.as_ref()) {
                Ordering::Equal => {
                    let l_sz = l_el.as_ref().num_elem();
                    let r_sz = r_el.as_ref().num_elem();
                    let ncond = comb(Transformation::view(l_off,1,inp_lhs.clone()),
                                     Transformation::view(r_off,1,inp_rhs.clone()),em)?;
                    match T::combine(l_el,r_el,
                                     Transformation::view(l_off+1,l_sz,inp_lhs.clone()),
                                     Transformation::view(r_off+1,r_sz,inp_rhs.clone()),
                                     comb,only_l,only_r,em)? {
                        None => return Ok(None),
                        Some((nel,ntr)) => {
                            new.push(nel.as_obj());
                            ntrans.push(ncond);
                            ntrans.push(ntr);
                            l_off+=l_sz+1;
                            r_off+=r_sz+1;
                            l_cur = None;
                            r_cur = None;
                        }
                    }
                },
                Ordering::Less => {
                    let l_obj = l_el.as_obj();
                    let l_sz = l_obj.num_elem();
                    new.push(l_obj);
                    ntrans.push(only_l(Transformation::view(l_off,l_sz+1,inp_lhs.clone()),em)?);
                    l_off+=l_sz+1;
                    l_cur = None;
                    r_cur = Some(r_el);
                },
                Ordering::Greater => {
                    let r_obj = r_el.as_obj();
                    let r_sz = r_obj.num_elem();
                    new.push(r_obj);
                    ntrans.push(only_r(Transformation::view(r_off,r_sz+1,inp_rhs.clone()),em)?);
                    r_off+=r_sz+1;
                    l_cur = Some(l_el);
                    r_cur = None;
                }
            }
        }
        Ok(Some((OptRef::Owned(Choice(new)),Transformation::concat(&ntrans[0..]))))
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {

        let mut selectors = Vec::with_capacity(self.0.len());

        for el in self.0.iter() {
            let sel = f(*off,em)?;
            
            *off+=1;

            let last_pos = res.len();
            el.invariant(em,f,off,res)?;
            for i in last_pos..res.len() {
                let new = em.embed(expr::Expr::App(expr::Function::Implies(2),vec![sel.clone(),res[i].clone()]))?;
                res[i] = new;
            }
            
            selectors.push(sel);
        }

        let inv1 = em.embed(expr::Expr::App(expr::Function::AtMost(1,selectors.len()),selectors.clone()))?;
        res.push(inv1);
        let inv2 = em.embed(expr::Expr::App(expr::Function::AtLeast(1,selectors.len()),selectors))?;
        res.push(inv2);
        Ok(())
    }
}

impl<K : Ord + Clone + Hash,T : Composite> Composite for BTreeMap<K,T> {
    fn num_elem(&self) -> usize {
        let mut acc = 0;
        for v in self.values() {
            acc+=v.num_elem();
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,n: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let mut acc = 0;
        for v in self.values() {
            let sz = v.num_elem();
            if acc+sz > n {
                return v.elem_sort(n-acc,em)
            }
            acc+=sz;
        }
        panic!("Invalid index: {}",n)
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let mut new = BTreeMap::new();
        let mut ntrans = Vec::new();
        
        let mut l_iter = lhs.as_ref().iter();
        let mut r_iter = rhs.as_ref().iter();
        let mut l_off = 0;
        let mut r_off = 0;

        let mut l_cur : Option<(&K,&T)> = None;
        let mut r_cur : Option<(&K,&T)> = None;

        loop {
            let (l_key,l_el) = match l_cur {
                None => match l_iter.next() {
                    None => {
                        match r_cur {
                            None => {},
                            Some((k,el)) => {
                                let sz = el.num_elem();
                                new.insert(k.clone(),el.clone());
                                ntrans.push(only_r(Transformation::view(r_off,sz,inp_rhs.clone()),em)?);
                                r_off+=sz;
                            }
                        }
                        for (k,el) in r_iter {
                            let sz = el.num_elem();
                            new.insert(k.clone(),el.clone());
                            ntrans.push(only_r(Transformation::view(r_off,sz,inp_rhs.clone()),em)?);
                            r_off+=sz;
                        }
                        break
                    },
                    Some(el) => el
                },
                Some(el) => el
            };
            let (r_key,r_el) = match r_cur {
                None => match r_iter.next() {
                    None => {
                        let l_sz = l_el.num_elem();
                        new.insert(l_key.clone(),l_el.clone());
                        ntrans.push(only_l(Transformation::view(l_off,l_sz,inp_lhs.clone()),em)?);
                        l_off+=l_sz;
                        for (k,el) in l_iter {
                            let sz = el.num_elem();
                            new.insert(k.clone(),el.clone());
                            ntrans.push(only_r(Transformation::view(l_off,sz,inp_lhs.clone()),em)?);
                            l_off+=sz;
                        }
                        break
                    },
                    Some(el) => el
                },
                Some(el) => el
            };
            match l_key.cmp(r_key) {
                Ordering::Equal => {
                    let l_sz = l_el.num_elem();
                    let r_sz = r_el.num_elem();
                    match T::combine(OptRef::Ref(l_el),OptRef::Ref(r_el),
                                     Transformation::view(l_off,l_sz,inp_lhs.clone()),
                                     Transformation::view(r_off,r_sz,inp_rhs.clone()),
                                     comb,only_l,only_r,em)? {
                        None => return Ok(None),
                        Some((nel,ntr)) => {
                            new.insert(l_key.clone(),nel.as_obj());
                            ntrans.push(ntr);
                            l_off+=l_sz;
                            r_off+=r_sz;
                            l_cur = None;
                            r_cur = None;
                        }
                    }
                },
                Ordering::Less => {
                    let l_sz = l_el.num_elem();
                    new.insert(l_key.clone(),l_el.clone());
                    ntrans.push(only_l(Transformation::view(l_off,l_sz,inp_lhs.clone()),em)?);
                    l_off+=l_sz;
                    l_cur = None;
                    r_cur = Some((r_key,r_el));
                },
                Ordering::Greater => {
                    let r_sz = r_el.num_elem();
                    new.insert(r_key.clone(),r_el.clone());
                    ntrans.push(only_r(Transformation::view(r_off,r_sz,inp_rhs.clone()),em)?);
                    r_off+=r_sz;
                    l_cur = Some((l_key,l_el));
                    r_cur = None;
                }
            }
        }
        Ok(Some((OptRef::Owned(new),Transformation::concat(&ntrans[0..]))))
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {

        for el in self.values() {
            el.invariant(em,f,off,res)?;
        }
        Ok(())
    }
}

impl<T : Composite> Composite for Option<T> {
    fn num_elem(&self) -> usize {
        match *self {
            None => 0,
            Some(ref c) => c.num_elem()
        }
    }
    fn elem_sort<Em : Embed>(&self,n: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match *self {
            None => panic!("Invalid index: {}",n),
            Some(ref c) => c.elem_sort(n,em)
        }
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        match lhs {
            OptRef::Ref(&None) |
            OptRef::Owned(None) => match rhs {
                OptRef::Ref(&None) |
                OptRef::Owned(None) => Ok(Some((OptRef::Owned(None),Transformation::id(0)))),
                _ => Ok(Some((rhs,only_r(inp_rhs,em)?)))
            },
            OptRef::Ref(&Some(ref x)) => match rhs {
                OptRef::Ref(&None) |
                OptRef::Owned(None) => Ok(Some((lhs,only_l(inp_lhs,em)?))),
                OptRef::Ref(&Some(ref y)) => match T::combine(OptRef::Ref(x),OptRef::Ref(y),
                                                              inp_lhs,inp_rhs,
                                                              comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nel,ntrans)) => Ok(Some((nel.some(),ntrans)))
                },
                OptRef::Owned(Some(y)) => match T::combine(OptRef::Ref(x),OptRef::Owned(y),
                                                           inp_lhs,inp_rhs,
                                                           comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nel,ntrans)) => Ok(Some((nel.some(),ntrans)))
                }
            },
            OptRef::Owned(Some(x)) => match rhs {
                OptRef::Ref(&None) |
                OptRef::Owned(None) => Ok(Some((OptRef::Owned(Some(x)),only_l(inp_lhs,em)?))),
                OptRef::Ref(&Some(ref y)) => match T::combine(OptRef::Owned(x),OptRef::Ref(y),
                                                              inp_lhs,inp_rhs,
                                                              comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nel,ntrans)) => Ok(Some((nel.some(),ntrans)))
                },
                OptRef::Owned(Some(y)) => match T::combine(OptRef::Owned(x),OptRef::Owned(y),
                                                           inp_lhs,inp_rhs,
                                                           comb,only_l,only_r,em)? {
                    None => Ok(None),
                    Some((nel,ntrans)) => Ok(Some((nel.some(),ntrans)))
                }
            }
        }
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {
        match *self {
            None => Ok(()),
            Some(ref el) => el.invariant(em,f,off,res)
        }
    }
}

#[derive(PartialEq,Eq,Hash,Clone)]
pub struct Array<Idx : Composite,T : Composite> {
    index: Idx,
    element: T
}

impl<Idx : Composite + Eq,T : Composite> Composite for Array<Idx,T> {
    fn num_elem(&self) -> usize {
        self.element.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,n: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let srt = self.element.elem_sort(n,em)?;
        let idx_sz = self.index.num_elem();
        let mut idx_arr = Vec::with_capacity(idx_sz as usize);
        for i in 0..idx_sz {
            idx_arr.push(self.index.elem_sort(i,em)?);
        }
        em.embed_sort(SortKind::Array(idx_arr,srt))
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        if lhs.as_ref().index != rhs.as_ref().index {
            return Ok(None)
        }
        let (idx,n_lhs) = match lhs {
            OptRef::Ref(ref x) => (x.index.clone(),OptRef::Ref(&x.element)),
            OptRef::Owned(x) => (x.index,OptRef::Owned(x.element))
        };
        let n_rhs = match rhs {
            OptRef::Ref(ref x) => OptRef::Ref(&x.element),
            OptRef::Owned(x) => OptRef::Owned(x.element)
        };
        match T::combine(n_lhs,n_rhs,inp_lhs,inp_rhs,
                         comb,only_l,only_r,em)? {
            None => Ok(None),
            Some((nel,ninp)) => Ok(Some((OptRef::Owned(Array { index: idx,
                                                               element: nel.as_obj() }),ninp)))
        }
    }
    // FIXME: Forall invariants
}

impl Composite for () {
    fn num_elem(&self) -> usize { 0 }
    fn elem_sort<Em : Embed>(&self,n: usize,_: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        panic!("Invalid index: {}",n)
    }
    fn combine<'a,Em,FComb,FL,FR>(_: OptRef<'a,Self>,_: OptRef<'a,Self>,
                                  _: Transf<Em>,_: Transf<Em>,
                                  _: &FComb,_: &FL,_: &FR,
                                  _: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        Ok(Some((OptRef::Owned(()),Transformation::id(0))))
    }
}

impl<A : Composite,B : Composite> Composite for (A,B) {
    fn num_elem(&self) -> usize {
        self.0.num_elem() + self.1.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,n: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        let sz0 = self.0.num_elem();
        if n>=sz0 {
            self.1.elem_sort(n-sz0,em)
        } else {
            self.0.elem_sort(n,em)
        }
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                  em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        let (l_fst,l_snd) = match lhs {
            OptRef::Ref(&(ref x,ref y)) => (OptRef::Ref(x),OptRef::Ref(y)),
            OptRef::Owned((x,y)) => (OptRef::Owned(x),OptRef::Owned(y))
        };
        let (r_fst,r_snd) = match rhs {
            OptRef::Ref(&(ref x,ref y)) => (OptRef::Ref(x),OptRef::Ref(y)),
            OptRef::Owned((x,y)) => (OptRef::Owned(x),OptRef::Owned(y))
        };
        let l_fst_sz = l_fst.as_ref().num_elem();
        let l_snd_sz = l_snd.as_ref().num_elem();
        let r_fst_sz = r_fst.as_ref().num_elem();
        let r_snd_sz = r_snd.as_ref().num_elem();
        
        match A::combine(l_fst,r_fst,
                         Transformation::view(0,l_fst_sz,inp_lhs.clone()),
                         Transformation::view(0,r_fst_sz,inp_rhs.clone()),
                         comb,only_l,only_r,em)? {
            None => Ok(None),
            Some((nfst,ninp_1)) => match B::combine(l_snd,r_snd,
                                                    Transformation::view(l_fst_sz,l_snd_sz,inp_lhs),
                                                    Transformation::view(r_fst_sz,r_snd_sz,inp_rhs),
                                                    comb,only_l,only_r,em)? {
                None => Ok(None),
                Some((nsnd,ninp_2)) => Ok(Some((OptRef::Owned((nfst.as_obj(),nsnd.as_obj())),
                                                Transformation::concat(&[ninp_1,ninp_2]))))
            }
        }
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {

        self.0.invariant(em,f,off,res)?;
        self.1.invariant(em,f,off,res)
    }

}

pub fn decompose_tuple<'a,A,B,Em>(tuple: OptRef<'a,(A,B)>,
                                  inp: Transf<Em>)
                                  -> (OptRef<'a,A>,
                                      Transf<Em>,
                                      OptRef<'a,B>,
                                      Transf<Em>)
    where A : Composite,B : Composite,Em : Embed {
    let (fst,snd) = match tuple {
        OptRef::Owned((x,y)) => (OptRef::Owned(x),OptRef::Owned(y)),
        OptRef::Ref(&(ref x,ref y)) => (OptRef::Ref(x),OptRef::Ref(y))
    };
    let sz_fst = fst.as_ref().num_elem();
    let sz_snd = snd.as_ref().num_elem();
    let fst_inp = Transformation::view(0,sz_fst,inp.clone());
    let snd_inp = Transformation::view(sz_fst,sz_snd,inp);
    (fst,fst_inp,snd,snd_inp)
}

pub fn fst<'a,A,B,Em>(tuple: OptRef<'a,(A,B)>,inp: Transf<Em>)
                      -> Result<(OptRef<'a,A>,Transf<Em>),Em::Error>
    where A : Composite,B : Composite,Em : Embed {
    let el = match tuple {
        OptRef::Owned(t) => OptRef::Owned(t.0),
        OptRef::Ref(t) => OptRef::Ref(&t.0)
    };
    let outp = Transformation::view(0,el.as_ref().num_elem(),inp);
    Ok((el,outp))
}

pub fn snd<'a,A,B,Em>(tuple: OptRef<'a,(A,B)>,inp: Transf<Em>)
                      -> Result<(OptRef<'a,B>,Transf<Em>),Em::Error>
    where A : Composite,B : Composite,Em : Embed {
    let off = tuple.as_ref().0.num_elem();
    let el = match tuple {
        OptRef::Owned(t) => OptRef::Owned(t.1),
        OptRef::Ref(t) => OptRef::Ref(&t.1)
    };
    let outp = Transformation::view(off,el.as_ref().num_elem(),inp);
    Ok((el,outp))
}

pub fn tuple<'a,'b,A,B,Em>(el_a: OptRef<'a,A>,el_b: OptRef<'a,B>,
                           inp_a: Transf<Em>,inp_b: Transf<Em>)
                           -> (OptRef<'b,(A,B)>,Transf<Em>)
    where A : Composite,B : Composite,Em : Embed {
    let res = OptRef::Owned((el_a.as_obj(),el_b.as_obj()));
    let outp = Transformation::concat(&[inp_a,inp_b]);
    (res,outp)
}

pub enum OptRef<'a,T : 'a> {
    Ref(&'a T),
    Owned(T)
}

impl<'a,T : 'a> OptRef<'a,T> {
    pub fn as_ref(&'a self) -> &'a T {
        match *self {
            OptRef::Ref(r) => r,
            OptRef::Owned(ref x) => x
        }
    }
    pub fn to_ref(&'a self) -> OptRef<'a,T> {
        OptRef::Ref(self.as_ref())
    }
}

impl<'a,T : 'a + Clone> OptRef<'a,T> {
    pub fn as_obj(self) -> T {
        match self {
            OptRef::Ref(x) => (*x).clone(),
            OptRef::Owned(x) => x
        }
    }
    pub fn to_owned<'b>(self) -> OptRef<'b,T> {
        OptRef::Owned(self.as_obj())
    }
    pub fn some(self) -> OptRef<'a,Option<T>> {
        match self {
            OptRef::Ref(x) => OptRef::Owned(Some(x.clone())),
            OptRef::Owned(x) => OptRef::Owned(Some(x))
        }
    }
}

enum OptRefVecIter<'a,'b,T : 'a + 'b> {
    RefVecIter(slice::Iter<'a,T>),
    OwnedVecIter(vec::Drain<'b,T>)
}

impl<'a,'b,T : 'a> Iterator for OptRefVecIter<'a,'b,T> {
    type Item = OptRef<'a,T>;
    fn next(&mut self) -> Option<OptRef<'a,T>> {
        match *self {
            OptRefVecIter::RefVecIter(ref mut it) => match it.next() {
                Some(el) => Some(OptRef::Ref(el)),
                None => None
            },
            OptRefVecIter::OwnedVecIter(ref mut it) => match it.next() {
                Some(el) => Some(OptRef::Owned(el)),
                None => None
            }
        }
    }
}

impl<'a,T : 'a> OptRef<'a,Vec<T>> {
    fn iter<'b>(&'b mut self) -> OptRefVecIter<'a,'b,T> {
        match *self {
            OptRef::Owned(ref mut v) => {
                let it = v.drain(0..);
                OptRefVecIter::OwnedVecIter(it)
            },
            OptRef::Ref(v) => OptRefVecIter::RefVecIter(v.iter()),
        }
    }
}

pub type Transf<Em> = Rc<Transformation<Em>>;

pub enum Transformation<Em : Embed> {
    Id(usize),
    View(usize,usize,Rc<Transformation<Em>>), // View with an offset and size
    Concat(usize,Vec<Rc<Transformation<Em>>>), // Record size to prevent recursion
    Constant(Vec<Em::Expr>),
    Map(usize, // Resulting size
        Box<Fn(&[Em::Expr],&mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>, // mapping function
        Rc<Transformation<Em>>, // transformation
        RefCell<Option<Vec<Em::Expr>>> // cache
    ),
    Zip2(usize,
         Box<Fn(&[Em::Expr],&[Em::Expr],
                &mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>,
         Rc<Transformation<Em>>,
         Rc<Transformation<Em>>,
         RefCell<Option<Vec<Em::Expr>>>
    ),
    Zip3(usize,
         Box<Fn(&[Em::Expr],&[Em::Expr],&[Em::Expr],
                &mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>,
         Rc<Transformation<Em>>,
         Rc<Transformation<Em>>,
         Rc<Transformation<Em>>,
         RefCell<Option<Vec<Em::Expr>>>
    ),
    Write(usize, // Resulting size
          usize, // Write offset
          usize, // Previous size
          Rc<Transformation<Em>>, // Write source
          Rc<Transformation<Em>> // Write target
    ),
    MapByElem(Box<for <'a,'b> Fn(&'a [Em::Expr],usize,Em::Expr,&'b mut Em) -> Result<Em::Expr,Em::Error>>,
              Rc<Transformation<Em>>),
    ZipsByElem(Box<for <'a,'b> Fn(&'a [Em::Expr],&'b mut Em) -> Result<Em::Expr,Em::Error>>,
               Vec<Rc<Transformation<Em>>>,
               RefCell<Vec<Em::Expr>> // Buffer
    ),
    ITE(usize,Vec<(Rc<Transformation<Em>>,Rc<Transformation<Em>>)>,
        Rc<Transformation<Em>>)
}

enum BorrowedSlice<'a,T : 'a> {
    BorrowedSlice(&'a [T]),
    CachedSlice(cell::Ref<'a,Vec<T>>,usize,usize),
    OwnedSlice(Vec<T>)
}

impl<'a,T : 'a> BorrowedSlice<'a,T> {
    fn get(&'a self) -> &'a [T] {
        match *self {
            BorrowedSlice::BorrowedSlice(sl) => sl,
            BorrowedSlice::CachedSlice(ref sl,start,end) => &(*sl)[start..end],
            BorrowedSlice::OwnedSlice(ref sl) => &sl[..]
        }
    }
}

impl<Em : Embed> Transformation<Em> {
    pub fn id(sz: usize) -> Transf<Em> {
        Rc::new(Transformation::Id(sz))
    }
    pub fn constant(els: Vec<Em::Expr>) -> Rc<Transformation<Em>> {
        Rc::new(Transformation::Constant(els))
    }
    pub fn const_bool(val: bool,em: &mut Em) -> Result<Rc<Transformation<Em>>,Em::Error> {
        Ok(Rc::new(Transformation::Constant(vec![em.const_bool(val)?])))
    }
    pub fn map(rsz: usize,
               f: Box<Fn(&[Em::Expr],&mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>,
               tr: Transf<Em>)
               -> Rc<Transformation<Em>> {
        Rc::new(Transformation::Map(rsz,f,tr,RefCell::new(None)))
    }
               
    pub fn view(off: usize,len: usize,t: Rc<Transformation<Em>>) -> Rc<Transformation<Em>> {
        debug_assert!(off+len<=t.size());
        if len==0 {
            Rc::new(Transformation::Id(0))
        } else if off==0 && t.size()==len {
            t
        } else if let Transformation::View(coff,_,ref t2) = *t {
            Rc::new(Transformation::View(coff+off,len,t2.clone()))
        } else {
            Rc::new(Transformation::View(off,len,t.clone()))
        }
    }
    pub fn concat(trs: &[Rc<Transformation<Em>>]) -> Rc<Transformation<Em>> {
        let mut only_one = None;
        let mut none = true;
        let mut req_alloc = 0;
        let mut sz = 0;
        for tr in trs.iter() {
            if tr.size()==0 {
                continue
            }
            match **tr {
                Transformation::Concat(nsz,ref ntrs) => {
                    sz+=nsz;
                    req_alloc+=ntrs.len();
                },
                _ => {
                    sz+=tr.size();
                    req_alloc+=1;
                }
            }
            only_one = if none { Some(tr) } else { None };
            none = false;
        }
        if none {
            return Rc::new(Transformation::Id(0));
        }
        if let Some(only) = only_one {
            return only.clone()
        }
        let mut rvec = Vec::with_capacity(req_alloc);
        for tr in trs.iter() {
            if tr.size()==0 {
                continue
            }
            match **tr {
                Transformation::Concat(_,ref ntrs) => {
                    rvec.extend_from_slice(&ntrs[..]);
                },
                _ => {
                    rvec.push(tr.clone());
                }
            }
        }
        Rc::new(Transformation::Concat(sz,rvec))
    }
    pub fn zip2(sz: usize,
                f: Box<Fn(&[Em::Expr],&[Em::Expr],&mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>,
                lhs: Rc<Transformation<Em>>,
                rhs: Rc<Transformation<Em>>)
                -> Rc<Transformation<Em>> {
        Rc::new(Transformation::Zip2(sz,f,lhs,rhs,RefCell::new(None)))
    }
    pub fn zip3(sz: usize,
                f: Box<Fn(&[Em::Expr],&[Em::Expr],&[Em::Expr],
                          &mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>,
                e1: Rc<Transformation<Em>>,
                e2: Rc<Transformation<Em>>,
                e3: Rc<Transformation<Em>>)
                -> Rc<Transformation<Em>> {
        Rc::new(Transformation::Zip3(sz,f,e1,e2,e3,RefCell::new(None)))
    }
    pub fn map_by_elem(f: Box<for <'a,'b> Fn(&'a [Em::Expr],usize,Em::Expr,&'b mut Em)
                                             -> Result<Em::Expr,Em::Error>>,
                       tr: Rc<Transformation<Em>>)
                       -> Rc<Transformation<Em>> {
        Rc::new(Transformation::MapByElem(f,tr))
    }
    pub fn zips_by_elem(f: Box<for <'a,'b> Fn(&'a [Em::Expr],&'b mut Em) -> Result<Em::Expr,Em::Error>>,
                        trs: Vec<Rc<Transformation<Em>>>)
                        -> Rc<Transformation<Em>> {
        let buf = Vec::with_capacity(trs.len());
        Rc::new(Transformation::ZipsByElem(f,trs,RefCell::new(buf)))
    }
    pub fn ite(cond: Transf<Em>,
               if_true: Transf<Em>,
               if_false: Transf<Em>)
               -> Transf<Em> {
        Rc::new(Transformation::ITE(if_true.size(),
                                    vec![(cond,
                                          if_true)],
                                    if_false))
    }
    pub fn not(tr: Transf<Em>)
               -> Transf<Em> {
        Rc::new(Transformation::MapByElem(Box::new(|_,_,e,em| { em.not(e) }),tr))
    }
    pub fn and(trs: Vec<Rc<Transformation<Em>>>)
               -> Rc<Transformation<Em>> {
        Transformation::zips_by_elem(Box::new(|els,em| { em.and(els.to_vec()) }),trs)
    }
    pub fn or(trs: Vec<Rc<Transformation<Em>>>)
              -> Rc<Transformation<Em>> {
        Transformation::zips_by_elem(Box::new(|els,em| { em.or(els.to_vec()) }),trs)
    }
    pub fn size(&self) -> usize {
        match *self {
            Transformation::Id(sz) => sz,
            Transformation::View(_,nsz,_) => nsz,
            Transformation::Concat(sz,_) => sz,
            Transformation::Constant(ref vec) => vec.len(),
            Transformation::Map(sz,_,_,_) => sz,
            Transformation::Zip2(sz,_,_,_,_) => sz,
            Transformation::Zip3(sz,_,_,_,_,_) => sz,
            Transformation::Write(sz,_,_,_,_) => sz,
            Transformation::MapByElem(_,ref tr) => tr.size(),
            Transformation::ZipsByElem(_,ref trs,_) => trs[0].size(),
            Transformation::ITE(sz,_,_) => sz
        }
    }
    pub fn clear_cache(&self) -> () {
        match *self {
            Transformation::Id(_) => (),
            Transformation::View(_,_,ref tr) => tr.clear_cache(),
            Transformation::Concat(_,ref vec) => for el in vec.iter() {
                el.clear_cache()
            },
            Transformation::Constant(_) => (),
            Transformation::Map(_,_,ref tr,ref cache) => {
                tr.clear_cache();
                *cache.borrow_mut() = None;
            },
            Transformation::Zip2(_,_,ref tr1,ref tr2,ref cache) => {
                tr1.clear_cache();
                tr2.clear_cache();
                *cache.borrow_mut() = None;
            },
            Transformation::Zip3(_,_,ref tr1,ref tr2,ref tr3,ref cache) => {
                tr1.clear_cache();
                tr2.clear_cache();
                tr3.clear_cache();
                *cache.borrow_mut() = None;
            },
            Transformation::Write(_,_,_,ref obj,ref trg) => {
                obj.clear_cache();
                trg.clear_cache();
            },
            Transformation::MapByElem(_,ref tr) => tr.clear_cache(),
            Transformation::ZipsByElem(_,ref trs,_) => for tr in trs.iter() {
                tr.clear_cache()
            },
            Transformation::ITE(_,ref arr,ref def) => {
                for &(ref cond,ref el) in arr.iter() {
                    cond.clear_cache();
                    el.clear_cache();
                }
                def.clear_cache()
            }
        }
    }
    fn as_slice<'a>(&'a self,arr: &'a [Em::Expr],off: usize,len: usize)
                    -> Option<BorrowedSlice<'a,Em::Expr>> {
        match *self {
            Transformation::Id(sz) => {
                debug_assert!(off+len<=sz);
                Some(BorrowedSlice::BorrowedSlice(&arr[off..off+len]))
            },
            Transformation::View(noff,sz,ref tr) => {
                debug_assert!(len<=sz);
                tr.as_slice(arr,off+noff,len)
            },
            Transformation::Concat(_,ref vec) => {
                let mut acc = 0;
                for el in vec.iter() {
                    let sz = el.size();
                    if off < acc+sz {
                        if off-acc+len<=sz {
                            return el.as_slice(arr,off-acc,len)
                        } else {
                            return None
                        }
                    }
                    acc+=sz;
                }
                panic!("Invalid index: {}",off)
            },
            Transformation::Constant(ref vec) => Some(BorrowedSlice::BorrowedSlice(&vec[off..off+len])),
            Transformation::Map(sz,_,_,ref cache) => {
                debug_assert!(len<=sz);
                let cache_ref : cell::Ref<Option<Vec<Em::Expr>>> = cache.borrow();
                match *cache_ref {
                    None => None,
                    Some(_) => {
                        let vec_ref : cell::Ref<Vec<Em::Expr>> = cell::Ref::map(cache_ref,|x| match x {
                            &Some(ref x) => x,
                            &None => unreachable!()
                        });
                        Some(BorrowedSlice::CachedSlice(vec_ref,off,off+len))
                    }
                }
            },
            Transformation::Zip2(_,_,_,_,ref cache) => {
                let cache_ref : cell::Ref<Option<Vec<Em::Expr>>> = cache.borrow();
                match *cache_ref {
                    None => None,
                    Some(_) => {
                        let vec_ref : cell::Ref<Vec<Em::Expr>> = cell::Ref::map(cache_ref,|x| match x {
                            &Some(ref x) => x,
                            &None => unreachable!()
                        });
                        Some(BorrowedSlice::CachedSlice(vec_ref,off,off+len))
                    }
                }
            },
            Transformation::Zip3(_,_,_,_,_,ref cache) => {
                let cache_ref : cell::Ref<Option<Vec<Em::Expr>>> = cache.borrow();
                match *cache_ref {
                    None => None,
                    Some(_) => {
                        let vec_ref : cell::Ref<Vec<Em::Expr>> = cell::Ref::map(cache_ref,|x| match x {
                            &Some(ref x) => x,
                            &None => unreachable!()
                        });
                        Some(BorrowedSlice::CachedSlice(vec_ref,off,off+len))
                    }
                }
            },
            Transformation::Write(_,wr_off,repl_sz,ref obj,ref trg) => if off+len <= wr_off {
                trg.as_slice(arr,off,len)
            } else if off >= wr_off && off+len <= wr_off+obj.size() {
                obj.as_slice(arr,off-wr_off,len)
            } else if off >= wr_off+obj.size() {
                trg.as_slice(arr,off-obj.size()+repl_sz,len)
            } else {
                None
            },
            _ => None
        }
    }
    fn to_slice<'a>(&'a self,arr: &'a [Em::Expr],off: usize,len: usize,em: &mut Em)
                    -> Result<BorrowedSlice<'a,Em::Expr>,Em::Error> {
        if let Some(res) = self.as_slice(arr,off,len) {
            return Ok(res)
        }
        let mut rvec = Vec::with_capacity(len);
        for i in 0..len {
            rvec.push(self.get(arr,off+i,em)?);
        }
        return Ok(BorrowedSlice::OwnedSlice(rvec))
    }
    pub fn get(&self,arr: &[Em::Expr],idx: usize,em: &mut Em)
               -> Result<Em::Expr,Em::Error> {
        match *self {
            Transformation::Id(_) => Ok(arr[idx].clone()),
            Transformation::View(off,_,ref tr)
                => tr.get(arr,off+idx,em),
            Transformation::Concat(_,ref vec) => {
                let mut acc = 0;
                for el in vec.iter() {
                    let sz = el.size();
                    if idx < acc+sz {
                        return el.get(arr,idx-acc,em)
                    }
                    acc+=sz;
                }
                panic!("Invalid index: {}",idx)
            },
            Transformation::Constant(ref vec) => Ok(vec[idx].clone()),
            Transformation::Map(sz,ref f,ref tr,ref cache) => {
                let mut cache_ref : cell::RefMut<Option<Vec<Em::Expr>>> = (*cache).borrow_mut();
                match *cache_ref {
                    Some(ref rcache) => return Ok(rcache[idx].clone()),
                    None => {}
                }
                let sl = tr.to_slice(arr,0,tr.size(),em)?;
                let mut narr = Vec::with_capacity(sz);
                f(sl.get(),&mut narr,em)?;
                let res = narr[idx].clone();
                *cache_ref = Some(narr);
                return Ok(res)
            },
            Transformation::Zip2(sz,ref f,ref tr1,ref tr2,ref cache) => {
                let mut cache_ref : cell::RefMut<Option<Vec<Em::Expr>>> = (*cache).borrow_mut();
                match *cache_ref {
                    Some(ref rcache) => return Ok(rcache[idx].clone()),
                    None => {}
                }
                let sl1 = tr1.to_slice(arr,0,tr1.size(),em)?;
                let sl2 = tr2.to_slice(arr,0,tr2.size(),em)?;
                let mut narr = Vec::with_capacity(sz);
                f(sl1.get(),sl2.get(),&mut narr,em)?;
                let res = narr[idx].clone();
                *cache_ref = Some(narr);
                return Ok(res)
            },
            Transformation::Zip3(sz,ref f,ref tr1,ref tr2,ref tr3,ref cache) => {
                let mut cache_ref : cell::RefMut<Option<Vec<Em::Expr>>> = (*cache).borrow_mut();
                match *cache_ref {
                    Some(ref rcache) => return Ok(rcache[idx].clone()),
                    None => {}
                }
                let sl1 = tr1.to_slice(arr,0,tr1.size(),em)?;
                let sl2 = tr2.to_slice(arr,0,tr2.size(),em)?;
                let sl3 = tr3.to_slice(arr,0,tr3.size(),em)?;
                let mut narr = Vec::with_capacity(sz);
                f(sl1.get(),sl2.get(),sl3.get(),&mut narr,em)?;
                let res = narr[idx].clone();
                *cache_ref = Some(narr);
                return Ok(res)
            },
            Transformation::Write(_,wr_off,repl_sz,ref obj,ref trg) => if idx < wr_off {
                trg.get(arr,idx,em)
            } else if idx >= wr_off && idx < wr_off+obj.size() {
                obj.get(arr,idx-wr_off,em)
            } else {
                trg.get(arr,idx-obj.size()+repl_sz,em)
            },
            Transformation::MapByElem(ref f,ref tr)
                => f(arr,idx,tr.get(arr,idx,em)?,em),
            Transformation::ZipsByElem(ref f,ref trs,ref buf_cell) => {
                let mut buf = (*buf_cell).borrow_mut();
                buf.clear();
                for tr in trs.iter() {
                    buf.push(tr.get(arr,idx,em)?);
                }
                f(&buf[..],em)
            },
            Transformation::ITE(_,ref conds,ref def) => {
                let mut expr = def.get(arr,idx,em)?;
                for &(ref cond,ref el) in conds.iter() {
                    let rcond = cond.get(arr,0,em)?;
                    let rel = el.get(arr,idx,em)?;
                    expr = em.ite(rcond,rel,expr)?;
                }
                Ok(expr)
            }
        }
    }
    pub fn get_all(&self,arr: &[Em::Expr],em: &mut Em) -> Result<Vec<Em::Expr>,Em::Error> {
        Ok(self.to_slice(arr,0,self.size(),em)?.get().to_vec())
    }
}

pub struct VecRead<'a,T : 'a,Em : 'a+Embed> {
    vec: &'a Vec<T>,
    pos: usize,
    inp: &'a Transf<Em>,
    off: usize
}

impl<'a,T : 'a,Em : 'a+Embed> VecRead<'a,T,Em> {
    pub fn new(v: &'a Vec<T>,inp_v: &'a Transf<Em>) -> Self {
        VecRead { vec: v,
                  pos: 0,
                  inp: inp_v,
                  off: 0 }
    }
}

impl<'a,T : 'a+Composite,Em : 'a+Embed> Iterator for VecRead<'a,T,Em> {
    type Item = (&'a T,Transf<Em>);
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos<self.vec.len() {
            let el = &self.vec[self.pos];
            let sz_el = el.num_elem();
            let inp_el = Transformation::view(self.off,sz_el,self.inp.clone());
            self.pos+=1;
            self.off+=sz_el;
            Some((el,inp_el))
        } else {
            None
        }
    }
}

pub struct CondVecAccess<T,Tp,It : Iterator<Item=Value>,Em : Embed> {
    cmp_expr: Transf<Em>,
    accessor: VecAccess<T,Em>,
    indices: Peekable<IndexIterator<Tp,It>>,
    no_elems: bool
}

impl<T : Composite,Tp,It : Iterator<Item=Value>,Em : Embed> CondVecAccess<T,Tp,It,Em> {
    pub fn new(cmp: Transf<Em>,vec: Vec<T>,inp_vec: Transf<Em>,ind: IndexIterator<Tp,It>)
               -> Self {
        CondVecAccess { cmp_expr: cmp,
                        accessor: VecAccess::new(vec,inp_vec),
                        indices: ind.peekable(),
                        no_elems: true }
    }
    pub fn next(&mut self) -> Result<Option<(Option<Transf<Em>>,&mut T,&mut Transf<Em>)>,Em::Error> {
        match self.indices.next() {
            None => Ok(None),
            Some((idx,val)) => {
                let (el,inp_el) = self.accessor.next(idx);
                let cond = if self.no_elems && self.indices.peek().is_some() {
                    self.no_elems = false;
                    None
                } else {
                    self.no_elems = false;
                    let inp_fun = move |_:&[Em::Expr],_:usize,e:Em::Expr,em:&mut Em| {
                        let cv = em.embed(expr::Expr::Const(val.clone()))?;
                        em.eq(e,cv)
                    };
                    Some(Transformation::map_by_elem(Box::new(inp_fun),self.cmp_expr.clone()))
                };
                Ok(Some((cond,el,inp_el)))
            }
        }
    }
    pub fn finish(self) -> (Vec<T>,Transf<Em>) {
        self.accessor.finish()
    }
}

/// Used to access elements of an array in an element-by-element fashion.
pub struct VecAccess<T,Em : Embed> {
    next_idx: usize,
    last_off: usize,
    vec: Vec<T>,
    vec_inp: Transf<Em>,
    nvec_inp: Vec<Transf<Em>>
}

impl<T : Composite,Em : Embed> VecAccess<T,Em> {
    /// Create a new accessor from a vector, a transformation and an iterator over the indices.
    pub fn new(v: Vec<T>,tr: Transf<Em>) -> Self {
        VecAccess { next_idx: 0,
                    last_off: 0,
                    vec: v,
                    vec_inp: tr,
                    nvec_inp: Vec::new() }
    }
    /// Get the next element of the vector.
    pub fn next(&mut self,idx: usize) -> (&mut T,&mut Transf<Em>) {
        assert!(idx >= self.next_idx);
        if self.next_idx<idx {
            let mut skip = 0;
            for i in self.next_idx..idx {
                skip+=self.vec[i].num_elem();
            }
            self.nvec_inp.push(Transformation::view(self.last_off,skip,self.vec_inp.clone()));
            self.last_off+=skip;
        }
        self.next_idx = idx+1;
        let sz = self.vec[idx].num_elem();
        self.nvec_inp.push(Transformation::view(self.last_off,sz,self.vec_inp.clone()));
        self.last_off+=sz;
        if let Some(last_ref) = self.nvec_inp.last_mut() {
            (&mut self.vec[idx],last_ref)
        } else {
            unreachable!()
        }
    }
    /// Destroy the iterator and return the resulting vector and transformation.
    pub fn finish(mut self) -> (Vec<T>,Transf<Em>) {
        if self.next_idx < self.vec.len() {
            let mut skip = 0;
            for i in self.next_idx..self.vec.len() {
                skip+=self.vec[i].num_elem();
            }
            self.nvec_inp.push(Transformation::view(self.last_off,skip,self.vec_inp));
        }
        (self.vec,Transformation::concat(&self.nvec_inp[..]))
    }
}

pub fn value_as_index(val: &Value) -> usize {
    match *val {
        Value::Bool(x) => if x { 1 } else { 0 },
        Value::Int(ref x) => match x.to_usize() {
            Some(rx) => rx,
            None => panic!("Index overflow")
        },
        Value::BitVec(_,ref x) => match x.to_usize() {
            Some(rx) => rx,
            None => panic!("Index overflow")
        },
        _ => panic!("Value {:?} cannot be used as index",*val)
    }
}

pub fn index_as_value<T>(tp: &SortKind<T>,idx: usize) -> Value {
    match *tp {
        SortKind::Bool => Value::Bool(idx!=0),
        SortKind::Int => Value::Int(BigInt::from(idx)),
        SortKind::BitVec(bw) => Value::BitVec(bw,BigInt::from(idx)),
        _ => panic!("Cannot make value from index")
    }
}

pub fn max_index<T>(tp: &SortKind<T>) -> usize {
    match *tp {
        SortKind::Bool => 1,
        SortKind::Int => usize::MAX,
        SortKind::BitVec(bw) => match (1 as usize).checked_shl(bw as u32) {
            None => usize::MAX,
            Some(r) => r-1
        },
        _ => panic!("Unsuitable index type")
    }
}

#[derive(Clone)]
pub enum IndexIterator<Tp,It : Iterator<Item=Value>> {
    Limited(It),
    Unlimited(SortKind<Tp>,Range<usize>)
}

impl<Tp,It : Iterator<Item=Value>> Iterator for IndexIterator<Tp,It> {
    type Item = (usize,Value);
    fn next(&mut self) -> Option<Self::Item> {
        match *self {
            IndexIterator::Limited(ref mut it) => match it.next() {
                None => None,
                Some(val) => Some((value_as_index(&val),val))
            },
            IndexIterator::Unlimited(ref tp,ref mut rng) => match rng.next() {
                None => None,
                Some(idx) => Some((idx,index_as_value(tp,idx)))
            }
        }
    }
    fn size_hint(&self) -> (usize,Option<usize>) {
        match *self {
            IndexIterator::Limited(ref it) => it.size_hint(),
            IndexIterator::Unlimited(_,ref it) => it.size_hint()
        }
    }
}

pub fn expr_as_vec_index<'a,Em,F>(limit: usize,e: &Em::Expr,em: &mut Em)
                                  -> Result<IndexIterator<Em::Sort,Em::ValueIterator>,Em::Error>
    where Em : DeriveValues,F : Fn(&Em::Var) -> usize {
    match em.derive_values(e)? {
        None => {
            let srt = em.type_of(e)?;
            let srtk = em.unbed_sort(&srt)?;
            Ok(IndexIterator::Unlimited(srtk,0..limit))
        },
        Some(it) => {
            Ok(IndexIterator::Limited(it))
        }
    }
}

pub fn get_vec_elem<'a,T,Em>(pos: usize,vec: OptRef<'a,Vec<T>>,inp: Transf<Em>)
                             -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error>
    where T : Composite, Em : Embed {
    let mut off = 0;
    for el in vec.as_ref().iter().take(pos) {
        off+=el.num_elem();
    }
    let len = vec.as_ref()[pos].num_elem();
    let rvec = match vec {
        OptRef::Ref(rvec) => OptRef::Ref(&rvec[pos]),
        OptRef::Owned(mut rvec) => OptRef::Owned(rvec.remove(pos))
    };
    Ok((rvec,Transformation::view(off,len as usize,inp)))
}

pub fn get_vec_elem_dyn<'a,T,Em
                        >(vec: OptRef<'a,Vec<T>>,
                          inp_pos: Transf<Em>,
                          inp_vec: Transf<Em>,
                          exprs: &[Em::Expr],
                          em: &mut Em)
                          -> Result<Option<(OptRef<'a,T>,Transf<Em>)>,Em::Error>
    where T : Composite,Em : DeriveConst {

    let idx = inp_pos.get(exprs,0,em)?;
    let c = em.derive_const(&idx)?;
    match vec.as_ref().len() {
        0 => panic!("Indexing empty vector"),
        1 => return Ok(Some(get_vec_elem(0,vec,inp_vec)?)),
        _ => {}
    }
    match c {
        Some(Value::Bool(x)) => if x {
            Ok(Some(get_vec_elem(1,vec,inp_vec)?))
        } else {
            Ok(Some(get_vec_elem(0,vec,inp_vec)?))
        },
        Some(Value::Int(x)) => match x.to_usize() {
            Some(rx) => Ok(Some(get_vec_elem(rx,vec,inp_vec)?)),
            None => panic!("Index overflow")
        },
        Some(Value::BitVec(_,x)) => match x.to_usize() {
            Some(rx) => Ok(Some(get_vec_elem(rx,vec,inp_vec)?)),
            None => panic!("Index overflow")
        },
        Some(Value::Real(_)) => panic!("Cannot index vector with Real"),
        None => {
            let srt = em.type_of(&idx)?;
            //let rvec = OptRef::Ref(vec.as_ref());
            let (def_el,def_inp) = get_vec_elem(0,OptRef::Ref(vec.as_ref()),inp_vec.clone())?;
            let mut el = def_el;
            let mut inp = def_inp;
            match em.unbed_sort(&srt)? {
                SortKind::BitVec(sz) => {
                    for i in 1..vec.as_ref().len() {
                        let (n_el,n_inp) = get_vec_elem(i,OptRef::Ref(vec.as_ref()),inp_vec.clone())?;
                        let cond_fun = move |vec:&[Em::Expr],res:&mut Vec<Em::Expr>,em:&mut Em| {
                            let val = em.const_bitvec(sz,BigInt::from(i))?;
                            let expr = em.eq(vec[0].clone(),val)?;
                            res.push(expr);
                            Ok(())
                        };
                        let cond = Transformation::map(1,Box::new(cond_fun),
                                                       inp_pos.clone());
                        let (r_el,r_inp) = match ite(n_el,el,cond,n_inp,inp,em)? {
                            Some(r) => r,
                            None => return Ok(None)
                        };
                        el = r_el;
                        inp = r_inp;
                    }
                },
                _ => unimplemented!()
            }
            Ok(Some((OptRef::Owned(el.as_obj()),inp)))
        }
    }
}

pub fn access_vec_dyn<'a,T,Em
                      >(vec: OptRef<'a,Vec<T>>,
                        inp_vec: Transf<Em>,
                        inp_idx: Transf<Em>,
                        exprs: &[Em::Expr],
                        em: &mut Em)
                        -> Result<CondVecAccess<T,Em::Sort,Em::ValueIterator,Em>,Em::Error>
    where T : Composite,Em : DeriveValues {
    let idx = inp_idx.get(exprs,0,em)?;
    let opt_vals = em.derive_values(&idx)?;
    let it = match opt_vals {
        Some(rvals) => IndexIterator::Limited(rvals),
        None => {
            let idx_srt = em.type_of(&idx)?;
            let idx_rsrt = em.unbed_sort(&idx_srt)?;
            IndexIterator::Unlimited(idx_rsrt,0..vec.as_ref().len())
        }
    };
    Ok(CondVecAccess::new(inp_idx,vec.as_obj(),inp_vec,it))
}

pub fn set_vec_elem<'a,'b,T,Em
                    >(pos: usize,
                      vec: OptRef<'a,Vec<T>>,
                      el: OptRef<'a,T>,
                      inp_vec: Transf<Em>,
                      inp_el: Transf<Em>)
                      -> Result<(OptRef<'b,Vec<T>>,Transf<Em>),Em::Error>
    where T : Composite + Clone, Em : Embed {

    let vlen = vec.as_ref().num_elem();
    let mut off_store = 0;
    for el in vec.as_ref().iter().take(pos) {
        off_store+=el.num_elem();
    }
    let old = vec.as_ref()[pos].num_elem();
    let mut rvec = vec.as_obj();
    rvec[pos] = el.as_obj();
    Ok((OptRef::Owned(rvec),
        Transformation::concat(&[Transformation::view(0,off_store,inp_vec.clone()),
                                 inp_el,
                                 Transformation::view(off_store+old,
                                                      vlen-off_store-old,inp_vec)])))
}

pub fn set_vec_elem_dyn<'a,'b,T,Em
                        >(vec: OptRef<'a,Vec<T>>,
                          el: OptRef<'a,T>,
                          inp_pos: Transf<Em>,
                          inp_vec: Transf<Em>,
                          inp_el: Transf<Em>,
                          exprs: &[Em::Expr],
                          em: &mut Em)
                          -> Result<Option<(OptRef<'b,Vec<T>>,Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let idx = inp_pos.get(exprs,0,em)?;
    let c = em.derive_const(&idx)?;
    match c {
        Some(Value::Bool(x)) => if x {
            Ok(Some(set_vec_elem(1,vec,el,inp_vec,inp_el)?))
        } else {
            Ok(Some(set_vec_elem(0,vec,el,inp_vec,inp_el)?))
        },
        Some(Value::Int(x)) => match x.to_usize() {
            Some(rx) => Ok(Some(set_vec_elem(rx,vec,el,inp_vec,inp_el)?)),
            None => panic!("Index overflow")
        },
        Some(Value::BitVec(_,x)) => match x.to_usize() {
            Some(rx) => Ok(Some(set_vec_elem(rx,vec,el,inp_vec,inp_el)?)),
            None => panic!("Index overflow")
        },
        Some(Value::Real(_)) => panic!("Cannot index vector with Real"),
        None => {
            let srt = em.type_of(&idx)?;
            let mut nvec = OptRef::Owned(vec.as_ref().clone());
            let mut inp_nvec = inp_vec.clone();
            let tp = em.unbed_sort(&srt)?;
            let max_idx = min(max_index(&tp),vec.as_ref().len());
            for i in 0..max_idx {
                let (cel,inp_cel) = get_vec_elem(i,OptRef::Ref(vec.as_ref()),inp_vec.clone())?;
                let cval = index_as_value(&tp,i);
                let cond_fun = move |vec:&[Em::Expr],res:&mut Vec<Em::Expr>,em:&mut Em| {
                    let val = em.embed(expr::Expr::Const(cval.clone()))?;
                    let expr = em.eq(vec[0].clone(),val)?;
                    res.push(expr);
                    Ok(())
                };
                let cond = Transformation::map(1,Box::new(cond_fun),
                                               inp_pos.clone());
                let (nel,inp_nel) = match ite(OptRef::Ref(el.as_ref()),
                                              cel,cond,
                                              inp_el.clone(),
                                              inp_cel,em)? {
                    Some(r) => r,
                    None => return Ok(None)
                };
                let (cvec,inp_cvec) = set_vec_elem(i,nvec,nel,inp_nvec,inp_nel)?;
                nvec = cvec;
                inp_nvec = inp_cvec;
            }
            Ok(Some((OptRef::Owned(nvec.as_obj()),inp_nvec)))
        }
    }
}

pub fn push_vec_elem<'a,T,Em>(vec: OptRef<'a,Vec<T>>,
                              el: OptRef<'a,T>,
                              inp_vec: Transf<Em>,
                              inp_el: Transf<Em>) -> Result<(OptRef<'a,Vec<T>>,Transf<Em>),Em::Error>
    where T : Composite + Clone, Em : Embed {

    let mut rvec = vec.as_obj();
    rvec.push(el.as_obj());
    Ok((OptRef::Owned(rvec),
        Transformation::concat(&[inp_vec,inp_el])))
}

pub fn get_array_elem<'a,Idx,T,Em>(arr: OptRef<'a,Array<Idx,T>>,
                                   inp_arr: Transf<Em>,
                                   inp_idx: Transf<Em>) -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error>
    where Idx : Composite, T : Composite, Em : 'static + Embed {

    let num_idx = arr.as_ref().index.num_elem();
    let fun = move |carr: &[Em::Expr],_: usize,e: Em::Expr,em: &mut Em| -> Result<Em::Expr,Em::Error> {
        let mut rvec = Vec::with_capacity(num_idx);
        for i in 0..num_idx {
            let idx_el = inp_idx.get(carr,i,em)?;
            rvec.push(idx_el);
        }
        em.select(e,rvec)
    };
    let mp = Rc::new(Transformation::MapByElem(Box::new(fun),inp_arr));
    let res = match arr {
        OptRef::Owned(rarr) => OptRef::Owned(rarr.element),
        OptRef::Ref(rarr) => OptRef::Ref(&rarr.element)
    };
    Ok((res,mp))
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub struct Data<T>(pub T);

impl<T : Eq + Hash + Clone> Composite for Data<T> {
    fn num_elem(&self) -> usize { 0 }
    fn elem_sort<Em : Embed>(&self,_:usize,_:&mut Em)
                             -> Result<Em::Sort,Em::Error> {
        panic!("Cannot get sort of Data")
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  _: Transf<Em>,_: Transf<Em>,
                                  _: &FComb,_: &FL,_: &FR,
                                  _: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        if lhs.as_ref().0 == rhs.as_ref().0 {
            Ok(Some((lhs,Transformation::id(0))))
        } else {
            Ok(None)
        }
        
    }
}

pub trait Container<T : Composite> : Composite {
    type Index : Composite;
    fn empty<'a,Em : Embed>(OptRef<'a,T>,Transf<Em>,&mut Em)
                            -> Result<(OptRef<'a,Self>,Transf<Em>),Em::Error>;
    fn index<'a,Em : Embed>(OptRef<'a,Self::Index>,OptRef<'a,Self>,Transf<Em>,Transf<Em>)
                            -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error>;
}

pub trait Stack<T : Composite> : Container<T> {
    fn stack_push<'a,Em : Embed>(OptRef<'a,T>,OptRef<'a,Self>,Transf<Em>,Transf<Em>)
                                 -> Result<(OptRef<'a,Self::Index>,OptRef<'a,Self>,Transf<Em>,Transf<Em>),Em::Error>;
}

pub trait Pool<T : Composite> : Container<T> {
    fn alloc<'a,Em : Embed,F>(&F,OptRef<'a,T>,OptRef<'a,Self>,Transf<Em>,Transf<Em>)
                              -> Result<(OptRef<'a,Self::Index>,OptRef<'a,Self>,Transf<Em>,Transf<Em>),Em::Error>
        where F : Fn(&T,Transf<Em>) -> bool;
}

impl<T : Composite + Clone> Container<T> for Vec<T> {
    type Index = Data<usize>;
    fn empty<'a,Em : Embed>(_:OptRef<'a,T>,_:Transf<Em>,_:&mut Em)
                            -> Result<(OptRef<'a,Vec<T>>,Transf<Em>),Em::Error> {
        Ok((OptRef::Owned(Vec::new()),Transformation::constant(Vec::new())))
    }
    fn index<'a,Em : Embed>(idx: OptRef<'a,Data<usize>>,vec: OptRef<'a,Vec<T>>,_:Transf<Em>,inp_vec: Transf<Em>)
                            -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error> {
        get_vec_elem(idx.as_ref().0,vec,inp_vec)
    }
}

impl<T : Composite + Clone> Stack<T> for Vec<T> {
    fn stack_push<'a,Em : Embed>(el: OptRef<'a,T>,vec: OptRef<'a,Vec<T>>,inp_el: Transf<Em>,inp_vec: Transf<Em>)
                                 -> Result<(OptRef<'a,Data<usize>>,OptRef<'a,Vec<T>>,Transf<Em>,Transf<Em>),Em::Error> {
        let len = vec.as_ref().len();
        let (nvec,ninp_vec) = push_vec_elem(vec,el,inp_vec,inp_el)?;
        Ok((OptRef::Owned(Data(len)),nvec,Transformation::constant(vec![]),ninp_vec))
    }
}

impl<T : Composite + Clone> Pool<T> for Vec<T> {
    fn alloc<'a,Em : Embed,F>(is_free:&F,el: OptRef<'a,T>,vec: OptRef<'a,Vec<T>>,inp_el: Transf<Em>,inp_vec: Transf<Em>)
                              -> Result<(OptRef<'a,Data<usize>>,OptRef<'a,Vec<T>>,Transf<Em>,Transf<Em>),Em::Error>
        where F : Fn(&T,Transf<Em>) -> bool {

        let len = vec.as_ref().len();
        for i in 0..len {
            let can_use = {
                let (cel,cinp) = get_vec_elem(i,OptRef::Ref(vec.as_ref()),inp_vec.clone())?;
                is_free(cel.as_ref(),cinp)
            };
            if can_use {
                let (nvec,ninp_vec) = set_vec_elem(i,vec,el,inp_vec,inp_el)?;
                return Ok((OptRef::Owned(Data(i)),nvec,Transformation::constant(vec![]),ninp_vec))
            }
        }
        let (nvec,ninp_vec) = push_vec_elem(vec,el,inp_vec,inp_el)?;
        Ok((OptRef::Owned(Data(len)),nvec,Transformation::constant(vec![]),ninp_vec))
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct BitVecVectorStack<T> {
    pub top: SingletonBitVec,
    pub elements: Vec<T>
}

impl<T : Composite + Clone> Composite for BitVecVectorStack<T> {
    fn num_elem(&self) -> usize {
        self.elements.num_elem()+1
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        if pos==0 {
            em.tp_bitvec(self.top.0)
        } else {
            self.elements.elem_sort(pos-1,em)
        }
    }
    fn combine<'a,Em,FComb,FL,FR>(x: OptRef<'a,Self>,y: OptRef<'a,Self>,
                                  inp_x: Transf<Em>,inp_y: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {

        if x.as_ref().top != y.as_ref().top {
            return Ok(None)
        }
        let bitwidth = x.as_ref().top;
        let top_inp = comb(Transformation::view(0,1,inp_x.clone()),
                           Transformation::view(0,1,inp_y.clone()),em)?;
        let vec_x = match x {
            OptRef::Ref(ref rx) => OptRef::Ref(&rx.elements),
            OptRef::Owned(rx) => OptRef::Owned(rx.elements)
        };
        let vec_y = match y {
            OptRef::Ref(ref ry) => OptRef::Ref(&ry.elements),
            OptRef::Owned(ry) => OptRef::Owned(ry.elements)
        };
        match Vec::combine(vec_x,vec_y,
                           Transformation::view(1,inp_x.size()-1,inp_x),
                           Transformation::view(1,inp_y.size()-1,inp_y),
                           comb,only_l,only_r,em)? {
            None => Ok(None),
            Some((nvec,nvec_inp))
                => Ok(Some((OptRef::Owned(BitVecVectorStack
                                          { top: bitwidth,
                                            elements: nvec.as_obj() }),
                            Transformation::concat(&[top_inp,nvec_inp]))))
        }
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,
                               off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {

        *off+=1;
        self.elements.invariant(em,f,off,res)
    }
}

pub fn bv_vec_stack_empty<'a,T,Em>(bitwidth: usize,em: &mut Em)
                                   -> Result<(OptRef<'a,BitVecVectorStack<T>>,Transf<Em>),Em::Error>
    where T : Composite, Em : Embed {
    let res = OptRef::Owned(BitVecVectorStack { top: SingletonBitVec(bitwidth), elements: vec![] });
    let outp = Transformation::constant(vec![em.const_bitvec(bitwidth,BigInt::from(0))?]);
    Ok((res,outp))
}

pub fn bv_vec_stack_singleton<'a,T,Em>(bitwidth: usize,
                                       el: OptRef<T>,
                                       inp_el: Transf<Em>,
                                       em: &mut Em)
                                       -> Result<(OptRef<'a,BitVecVectorStack<T>>,Transf<Em>),Em::Error>
    where T : Composite+Clone, Em : Embed {
    let res = OptRef::Owned(BitVecVectorStack { top: SingletonBitVec(bitwidth),
                                                elements: vec![el.as_obj()] });
    let inp_res = Transformation::concat(&[Transformation::constant(vec![em.const_bitvec(bitwidth,BigInt::from(1))?]),
                                           inp_el]);
    Ok((res,inp_res))
}

pub fn bv_vec_stack_access<'a,'b,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                       inp_stack: Transf<Em>,
                                       inp_idx: Transf<Em>,
                                       exprs: &[Em::Expr],
                                       em: &mut Em)
                                       -> Result<CondVecAccess<T,Em::Sort,Em::ValueIterator,Em>,Em::Error>
    where T : Composite + Clone,Em : DeriveValues {

    let vec = match stack {
        OptRef::Ref(ref rst) => OptRef::Ref(&rst.elements),
        OptRef::Owned(rst) => OptRef::Owned(rst.elements)
    };
    let sz = inp_stack.size();
    let inp_top = Transformation::view(0,1,inp_stack.clone());
    let inp_vec = Transformation::view(1,sz-1,inp_stack);
    let mut acc = access_vec_dyn(vec,inp_vec,inp_idx,exprs,em)?;
    acc.accessor.nvec_inp.push(inp_top);
    Ok(acc)
}

pub fn bv_vec_stack_get<'a,'b,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                    inp_stack: Transf<Em>,
                                    inp_idx: Transf<Em>,
                                    exprs: &[Em::Expr],
                                    em: &mut Em)
                                    -> Result<Option<(OptRef<'a,T>,Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let vec = match stack {
        OptRef::Ref(ref rst) => OptRef::Ref(&rst.elements),
        OptRef::Owned(rst) => OptRef::Owned(rst.elements)
    };
    let sz = inp_stack.size();
    let inp_vec = Transformation::view(1,sz-1,inp_stack);
    get_vec_elem_dyn(vec,inp_idx,inp_vec,exprs,em)
}

pub fn bv_vec_stack_set<'a,'b,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                    inp_stack: Transf<Em>,
                                    inp_idx: Transf<Em>,
                                    el: OptRef<'a,T>,
                                    el_inp: Transf<Em>,
                                    exprs: &[Em::Expr],
                                    em: &mut Em)
                                    -> Result<Option<(OptRef<'b,BitVecVectorStack<T>>,Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let bw = stack.as_ref().top;
    let vec = match stack {
        OptRef::Ref(ref rst) => OptRef::Ref(&rst.elements),
        OptRef::Owned(rst) => OptRef::Owned(rst.elements)
    };
    let sz = inp_stack.size();
    let inp_vec = Transformation::view(1,sz-1,inp_stack.clone());
    match set_vec_elem_dyn(vec,el,inp_idx,inp_vec,el_inp,exprs,em)? {
        None => Ok(None),
        Some((nvec,inp_nvec)) => {
            let res = OptRef::Owned(BitVecVectorStack { top: bw,
                                                        elements: nvec.as_obj() });
            let inp_top = Transformation::view(0,1,inp_stack);
            let inp_res = Transformation::concat(&[inp_top,inp_nvec]);
            Ok(Some((res,inp_res)))
        }
    }
}

pub fn bv_vec_stack_top<'a,Em>(inp_stack: Transf<Em>)
                               -> Transf<Em>
    where Em : Embed {

    Transformation::view(0,1,inp_stack)
}

pub fn bv_vec_stack_access_top<'a,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                        inp_stack: Transf<Em>,
                                        exprs: &[Em::Expr],
                                        em: &mut Em)
                                        -> Result<CondVecAccess<T,Em::Sort,Em::ValueIterator,Em>,Em::Error>
    where T : Composite + Clone,Em : DeriveValues {

    let top = bv_vec_stack_top(inp_stack.clone());
    bv_vec_stack_access(stack,inp_stack,top,exprs,em)
}

pub fn bv_vec_stack_get_top<'a,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                     inp_stack: Transf<Em>,
                                     exprs: &[Em::Expr],
                                     em: &mut Em)
                                     -> Result<Option<(OptRef<'a,T>,Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let top = bv_vec_stack_top(inp_stack.clone());
    bv_vec_stack_get(stack,inp_stack,top,exprs,em)
}

pub fn bv_vec_stack_set_top<'a,'b,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                        inp_stack: Transf<Em>,
                                        el: OptRef<'a,T>,
                                        inp_el: Transf<Em>,
                                        exprs: &[Em::Expr],
                                        em: &mut Em)
                                        -> Result<Option<(OptRef<'b,BitVecVectorStack<T>>,Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let top = bv_vec_stack_top(inp_stack.clone());
    bv_vec_stack_set(stack,inp_stack,top,el,inp_el,exprs,em)
}

pub fn bv_vec_stack_push<'a,'b,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                     el: OptRef<'a,T>,
                                     inp_stack: Transf<Em>,
                                     inp_el: Transf<Em>,
                                     exprs: &[Em::Expr],
                                     em: &mut Em)
                                     -> Result<Option<(OptRef<'b,BitVecVectorStack<T>>,Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let sz = stack.as_ref().elements.len();
    let vec_sz = stack.as_ref().elements.num_elem();
    let top = inp_stack.get(exprs,0,em)?;
    let bitwidth = stack.as_ref().top;
    let vec = match stack {
        OptRef::Ref(ref st) => OptRef::Ref(&st.elements),
        OptRef::Owned(st) => OptRef::Owned(st.elements)
    };
    let inp_vec = Transformation::view(1,vec_sz,inp_stack.clone());
    let c = em.derive_const(&top)?;
    match c {
        Some(Value::BitVec(bitwidth2,x)) => {
            debug_assert_eq!(bitwidth.0,bitwidth2);
            match x.to_usize() {
                Some(rx) => match rx.cmp(&sz) {
                    Ordering::Greater => panic!("top of bitvector stack out of range"),
                    Ordering::Less => {
                        let (nvec,inp_nvec) = set_vec_elem(rx,vec,el,inp_vec,inp_el)?;
                        let ntop = em.const_bitvec(bitwidth.0,x+1)?;
                        let inp_ntop = Transformation::constant(vec![ntop]);
                        Ok(Some((OptRef::Owned(BitVecVectorStack { top: bitwidth,
                                                                   elements: nvec.as_obj() }),
                                 Transformation::concat(&[inp_ntop,inp_nvec]))))
                    },
                    Ordering::Equal => {
                        let (nvec,inp_nvec) = push_vec_elem(vec,el,inp_vec,inp_el)?;
                        let ntop = em.const_bitvec(bitwidth.0,x+1)?;
                        let inp_ntop = Transformation::constant(vec![ntop]);
                        Ok(Some((OptRef::Owned(BitVecVectorStack { top: bitwidth,
                                                                   elements: nvec.as_obj() }),
                                 Transformation::concat(&[inp_ntop,inp_nvec]))))
                    }
                },
                None => panic!("Index overflow")
            }
        },
        Some(_) => panic!("Invalid index type for bitvector stack"),
        None => {
            match set_vec_elem_dyn(vec,OptRef::Ref(el.as_ref()),Transformation::view(0,1,inp_stack.clone()),
                                   inp_vec.clone(),inp_el.clone(),exprs,em)? {
                None => Ok(None),
                Some((nvec1,inp_nvec1)) => {
                    let (nvec2,inp_nvec2) = push_vec_elem(nvec1,OptRef::Ref(el.as_ref()),inp_nvec1.clone(),inp_el.clone())?;
                    let ntop_fun = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                        let one = em.const_bitvec(bitwidth.0,BigInt::from(1))?;
                        em.bvadd(e,one)
                    };
                    let ntop_inp = Transformation::map_by_elem(Box::new(ntop_fun),
                                                               Transformation::view(0,1,inp_stack.clone()));
                    Ok(Some((OptRef::Owned(BitVecVectorStack { top: bitwidth,
                                                               elements: nvec2.as_obj() }),
                             Transformation::concat(&[ntop_inp,inp_nvec2]))))
                }
            }
        }
    }
}

pub fn bv_vec_stack_pop<'a,T,Em>(stack: OptRef<'a,BitVecVectorStack<T>>,
                                 inp_stack: Transf<Em>,
                                 exprs: &[Em::Expr],
                                 em: &mut Em)
                                 -> Result<Option<(OptRef<'a,BitVecVectorStack<T>>,
                                                   Transf<Em>)>,Em::Error>
    where T : Composite + Clone,Em : DeriveConst {

    let vec_sz = stack.as_ref().elements.num_elem();
    let top = inp_stack.get(exprs,0,em)?;
    let bitwidth = stack.as_ref().top;
    let inp_vec = Transformation::view(1,vec_sz,inp_stack.clone());
    let c = em.derive_const(&top)?;
    match c {
        Some(Value::BitVec(bitwidth2,x)) => {
            debug_assert_eq!(bitwidth.0,bitwidth2);
            match x.to_usize() {
                Some(rx) => if rx==0 || rx==1 {
                    let zero = em.const_bitvec(bitwidth.0,BigInt::from(0))?;
                    Ok(Some((OptRef::Owned(BitVecVectorStack { top: bitwidth,
                                                               elements: vec![] }),
                             Transformation::constant(vec![zero]))))
                } else {
                    let nst = match stack {
                        OptRef::Ref(ref st)
                            => OptRef::Owned(BitVecVectorStack { top: bitwidth,
                                                                 elements: st.elements.iter().take(rx)
                                                                 .map(Clone::clone).collect()
                            }),
                        OptRef::Owned(mut v) => {
                            v.elements.truncate(rx-1);
                            OptRef::Owned(BitVecVectorStack { top: bitwidth,
                                                              elements: v.elements })
                        }
                    };
                    let inp_nvec = Transformation::view(1,nst.as_ref().elements.num_elem(),inp_stack);
                    let inp_ntop = Transformation::constant(vec![em.const_bitvec(bitwidth.0,BigInt::from(rx-1))?]);
                    Ok(Some((nst,Transformation::concat(&[inp_ntop,inp_nvec]))))
                },
                None => panic!("Index overflow")
            }
        },
        Some(_) => panic!("Invalid index type"),
        None => {
            let ntop_fun = move |_:&[Em::Expr],_:usize,e: Em::Expr,em: &mut Em| {
                let zero = em.const_bitvec(bitwidth.0,BigInt::from(0))?;
                let one = em.const_bitvec(bitwidth.0,BigInt::from(1))?;
                let cond = em.eq(e.clone(),zero.clone())?;
                let ne = em.bvsub(e.clone(),one)?;
                em.ite(cond,e,ne)
            };
            let inp_ntop = Transformation::map_by_elem(Box::new(ntop_fun),Transformation::view(0,1,inp_stack));
            Ok(Some((stack,Transformation::concat(&[inp_ntop,inp_vec]))))
        }
    }
}

pub fn ite<'a,T,Em>(if_t: OptRef<'a,T>,if_f: OptRef<'a,T>,
                    inp_cond: Transf<Em>,
                    inp_if_t: Transf<Em>,
                    inp_if_f: Transf<Em>,
                    em: &mut Em)
                    -> Result<Option<(OptRef<'a,T>,Transf<Em>)>,Em::Error>
    where T : Composite, Em : Embed {

    T::combine(if_t,if_f,inp_if_t,inp_if_f,
               &|inp_l,inp_r,_| {
                   Ok(Transformation::zip3(inp_l.size(),
                                           Box::new(|c:&[Em::Expr],le:&[Em::Expr],re:&[Em::Expr],res: &mut Vec<Em::Expr>,em:&mut Em| {
                                               for (et,ef) in le.iter().zip(re.iter()) {
                                                   res.push(em.ite(c[0].clone(),et.clone(),ef.clone())?);
                                               }
                                               Ok(())
                                           }),
                                           inp_cond.clone(),inp_l,inp_r))
               },
               &|tr,_| Ok(tr),
               &|tr,_| Ok(tr),
               em)
}

pub fn vec_pool_alloc<'a,'b,T,F,Em>(vec: OptRef<'a,Vec<T>>,
                                    el: OptRef<'a,T>,
                                    vec_inp: Transf<Em>,
                                    el_inp: Transf<Em>,
                                    is_free: &F)
                                    -> Result<(usize,OptRef<'b,Vec<T>>,Transf<Em>),Em::Error>
    where T : Composite + Clone,
          F : Fn(&T,Transf<Em>) -> bool,
          Em : Embed {
    let mut nvec = vec.as_obj();
    let mut off = 0;
    let mut pos = 0;
    while pos<nvec.len() {
        let sz = nvec[pos].num_elem();
        let vw = Transformation::view(off,sz,vec_inp.clone());
        if is_free(&nvec[pos],vw) {
            nvec[pos] = el.as_obj();
            let ntrans = Transformation::concat(&[Transformation::view(0,off,vec_inp.clone()),
                                                  el_inp,
                                                  Transformation::view(off+sz,vec_inp.size()-off-sz,vec_inp.clone())]);
            return Ok((pos,OptRef::Owned(nvec),ntrans))
        }
        off += sz;
        pos += 1;
    }
    nvec.push(el.as_obj());
    Ok((pos,OptRef::Owned(nvec),
        Transformation::concat(&[vec_inp,el_inp])))
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct Assoc<K,V>(Vec<(K,V)>);

impl<K : Ord+Hash+Clone,V : Composite> Assoc<K,V> {
    pub fn new() -> Self {
        Assoc(Vec::new())
    }
    pub fn access(&self,key: &K) -> &V {
        match self.0.binary_search_by(|&(ref k,_)| k.cmp(key)) {
            Ok(res) => &self.0[res].1,
            Err(_) => panic!("Assoc key not found")
        }
    }
    pub fn access_mut(&mut self,key: &K) -> &V {
        match self.0.binary_search_by(|&(ref k,_)| k.cmp(key)) {
            Ok(res) => &mut self.0[res].1,
            Err(_) => panic!("Assoc key not found")
        }
    }
    pub fn access_ext(&self,key: &K) -> (usize,&V) {
        let mut off = 0;
        for &(ref k,ref el) in self.0.iter() {
            match k.cmp(key) {
                Ordering::Less => { off+=el.num_elem() },
                Ordering::Greater => panic!("Assoc key not found"),
                Ordering::Equal => return (off,el)
            }
        }
        panic!("Assoc key not found")
    }
    pub fn access_mut_ext(&mut self,key: &K) -> (usize,&mut V) {
        let mut off = 0;
        for &mut (ref k,ref mut el) in self.0.iter_mut() {
            match k.cmp(key) {
                Ordering::Less => { off+=el.num_elem() },
                Ordering::Greater => panic!("Assoc key not found"),
                Ordering::Equal => return (off,el)
            }
        }
        panic!("Assoc key not found")
    }
}

impl<K : Ord + Hash + Clone,V : Composite + Clone> Composite for Assoc<K,V> {
    fn num_elem(&self) -> usize {
        let mut acc = 0;
        for el in self.0.iter() {
            acc+=el.1.num_elem()
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        debug_assert!(pos<self.num_elem());
        let mut off = 0;
        for el in self.0.iter() {
            let sz = el.1.num_elem();
            if pos<off+sz {
                return el.1.elem_sort(pos-off,em)
            }
            off+=sz;
        }
        panic!("Invalid index")
    }
    fn combine<'a,Em,FComb,FL,FR>(lhs: OptRef<'a,Self>,rhs: OptRef<'a,Self>,
                                  inp_lhs: Transf<Em>,inp_rhs: Transf<Em>,
                                  comb: &FComb,only_l: &FL,only_r: &FR,em: &mut Em)
                                  -> Result<Option<(OptRef<'a,Self>,Transf<Em>)>,Em::Error>
        where Em : Embed,
              FComb : Fn(Transf<Em>,Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FL : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error>,
              FR : Fn(Transf<Em>,&mut Em) -> Result<Transf<Em>,Em::Error> {
        let mut new : Vec<(K,V)> = Vec::new();
        let mut ntrans = Vec::new();

        let mut l_iter = lhs.as_ref().0.iter();
        let mut r_iter = rhs.as_ref().0.iter();

        let mut l_cur : Option<(&K,&V)> = None;
        let mut r_cur : Option<(&K,&V)> = None;

        let mut l_off = 0;
        let mut r_off = 0;

        loop {
            let (l_key,l_el) = match l_cur {
                None => match l_iter.next() {
                    None => {
                        match r_cur {
                            None => {},
                            Some((k,el)) => {
                                let sz = el.num_elem();
                                new.push((k.clone(),el.clone()));
                                ntrans.push(only_r(Transformation::view(r_off,sz,inp_rhs.clone()),em)?);
                                r_off+=sz;
                            }
                        }
                        for &(ref k,ref el) in r_iter {
                            let sz = el.num_elem();
                            new.push((k.clone(),el.clone()));
                            ntrans.push(only_r(Transformation::view(r_off,sz,inp_rhs.clone()),em)?);
                            r_off+=sz;
                        }
                        break
                    },
                    Some(&(ref k,ref el)) => (k,el)
                },
                Some(el) => el
            };
            let (r_key,r_el) = match r_cur {
                None => match r_iter.next() {
                    None => {
                        let l_sz = l_el.num_elem();
                        new.push((l_key.clone(),l_el.clone()));
                        ntrans.push(only_l(Transformation::view(l_off,l_sz,inp_lhs.clone()),em)?);
                        l_off+=l_sz;

                        for &(ref k,ref el) in l_iter {
                            let sz = el.num_elem();
                            new.push((k.clone(),el.clone()));
                            ntrans.push(only_r(Transformation::view(l_off,sz,inp_lhs.clone()),em)?);
                            l_off+=sz;
                        }
                        break
                    },
                    Some(&(ref k,ref el)) => (k,el)
                },
                Some(el) => el
            };
            match l_key.cmp(r_key) {
                Ordering::Equal => {
                    let l_sz = l_el.num_elem();
                    let r_sz = r_el.num_elem();
                    match V::combine(OptRef::Ref(l_el),OptRef::Ref(r_el),
                                     Transformation::view(l_off,l_sz,inp_lhs.clone()),
                                     Transformation::view(r_off,r_sz,inp_rhs.clone()),
                                     comb,only_l,only_r,em)? {
                        None => return Ok(None),
                        Some((nel,ntr)) => {
                            new.push((l_key.clone(),nel.as_obj()));
                            ntrans.push(ntr);
                            l_cur = None;
                            r_cur = None;
                            l_off+=l_sz;
                            r_off+=r_sz;
                        }
                    }
                },
                Ordering::Less => {
                    let l_sz = l_el.num_elem();
                    new.push((l_key.clone(),l_el.clone()));
                    ntrans.push(only_l(Transformation::view(l_off,l_sz,inp_lhs.clone()),em)?);
                    l_off+=l_sz;
                    l_cur = None;
                    r_cur = Some((r_key,r_el));
                },
                Ordering::Greater => {
                    let r_sz = r_el.num_elem();
                    new.push((r_key.clone(),r_el.clone()));
                    ntrans.push(only_r(Transformation::view(r_off,r_sz,inp_rhs.clone()),em)?);
                    r_off+=r_sz;
                    l_cur = Some((l_key,l_el));
                    r_cur = None;
                }
            }
        }
        Ok(Some((OptRef::Owned(Assoc(new)),
                 Transformation::concat(&ntrans[0..]))))
    }
}

pub fn assoc_empty<'a,K,V,Em>() -> Result<(OptRef<'a,Assoc<K,V>>,Transf<Em>),Em::Error>
    where K : Ord,Em : Embed {
    Ok((OptRef::Owned(Assoc(Vec::new())),
        Transformation::id(0)))
}

pub fn assoc_get<'a,K,V,Em>(assoc: OptRef<'a,Assoc<K,V>>,
                            inp_assoc: Transf<Em>,
                            key: &K)
                            -> Result<Option<(OptRef<'a,V>,Transf<Em>)>,Em::Error>
    where K : Ord + Hash + Clone, V : Composite + Clone, Em : Embed {
    debug_assert_eq!(assoc.as_ref().num_elem(),inp_assoc.size());
    match assoc {
        OptRef::Ref(ref rassoc) => {
            let mut off = 0;
            for &(ref k,ref el) in rassoc.0.iter() {
                match k.cmp(key) {
                    Ordering::Less => { off+=el.num_elem() },
                    Ordering::Greater => return Ok(None),
                    Ordering::Equal => {
                        let sz = el.num_elem();
                        return Ok(Some((OptRef::Ref(el),
                                        Transformation::view(off,sz,inp_assoc))))
                    }
                }
            }
            Ok(None)
        },
        OptRef::Owned(mut rassoc) => {
            let mut off = 0;
            for (k,el) in rassoc.0.drain(..) {
                match k.cmp(key) {
                    Ordering::Less => { off+=el.num_elem() },
                    Ordering::Greater => return Ok(None),
                    Ordering::Equal => {
                        let sz = el.num_elem();
                        return Ok(Some((OptRef::Owned(el),
                                        Transformation::view(off,sz,inp_assoc))))
                    }
                }
            }
            Ok(None)
        }
    }
}

pub fn assoc_insert<'a,'b,K,V,Em>(assoc: OptRef<'a,Assoc<K,V>>,
                                  inp_assoc: Transf<Em>,
                                  key: &K,
                                  value: OptRef<'a,V>,
                                  inp_value: Transf<Em>)
                                  -> Result<(OptRef<'b,Assoc<K,V>>,Transf<Em>),Em::Error>
    where K : Ord + Hash + Clone, V : Composite + Clone, Em : Embed {
    debug_assert_eq!(assoc.as_ref().num_elem(),inp_assoc.size());
    debug_assert_eq!(value.as_ref().num_elem(),inp_value.size());
    let mut rassoc = assoc.as_obj();
    let mut off = 0;
    for i in 0..rassoc.0.len() {
        match rassoc.0[i].0.cmp(key) {
            Ordering::Less => { off+=rassoc.0[i].1.num_elem() },
            Ordering::Greater => {
                rassoc.0.insert(i,(key.clone(),value.as_obj()));
                let before = Transformation::view(0,off,inp_assoc.clone());
                let after = Transformation::view(off,inp_assoc.size()-off,
                                                 inp_assoc);
                let ninp = Transformation::concat(&[before,inp_value,after]);
                return Ok((OptRef::Owned(rassoc),ninp))
            },
            Ordering::Equal => {
                let osize = rassoc.0[i].1.num_elem();
                rassoc.0[i].1 = value.as_obj();
                let before = Transformation::view(0,off,inp_assoc.clone());
                let after = Transformation::view(off+osize,
                                                 inp_assoc.size()-osize-off,
                                                 inp_assoc);
                let ninp = Transformation::concat(&[before,inp_value,after]);
                return Ok((OptRef::Owned(rassoc),ninp))
            }
        }
    }
    rassoc.0.push((key.clone(),value.as_obj()));
    Ok((OptRef::Owned(rassoc),
        Transformation::concat(&[inp_assoc,inp_value])))
}

pub fn choice_empty<T,Em : Embed>() -> (Choice<T>,Transf<Em>) {
    (Choice(vec![]),
     Transformation::id(0))
}

pub fn choice_insert<'a,T,Em>(choice: OptRef<'a,Choice<T>>,
                              inp_choice: Transf<Em>,
                              inp_cond: Transf<Em>,
                              el: OptRef<'a,T>,
                              inp_el: Transf<Em>)
                              -> Result<(OptRef<'a,Choice<T>>,
                                         Transf<Em>),Em::Error>
    where T : Composite+Clone+Ord,Em : Embed {
    let el_sz = inp_el.size();
    let ch_sz = inp_choice.size();

    debug_assert_eq!(choice.as_ref().num_elem(),ch_sz);
    debug_assert_eq!(inp_cond.size(),1);
    debug_assert_eq!(el.as_ref().num_elem(),el_sz);

    let mut pos = 0;
    let mut off = 0;
    let mut replace = false;
    for cel in choice.as_ref().0.iter() {
        let sz = cel.num_elem();
        match el.as_ref().cmp(&cel) {
            Ordering::Equal => {
                replace = true;
                break
            },
            Ordering::Less => break,
            Ordering::Greater => {
                pos+=1;
                off+=sz;
            }
        }
    }
    if replace {
        let or_fun = |lhs:&[Em::Expr],rhs:&[Em::Expr],res:&mut Vec<Em::Expr>,em:&mut Em| {
            res.push(em.or(vec![lhs[0].clone(),rhs[0].clone()])?);
            Ok(())
        };
        let ncond = Transformation::zip2(1,Box::new(or_fun),inp_cond.clone(),
                                         Transformation::view(off,1,inp_choice.clone()));
        let ninp = Transformation::ite(inp_cond,inp_el,
                                       Transformation::view(off+1,el_sz,inp_choice.clone()));
        let rinp = Transformation::concat(&[Transformation::view(0,off,inp_choice.clone()),
                                            ncond,ninp,
                                            Transformation::view(off+1+el_sz,ch_sz-off-1-el_sz,inp_choice)]);
        Ok((choice,rinp))
    } else {
        let mut nchoice = choice.as_obj();
        nchoice.0.insert(pos,el.as_obj());
        let ninp = Transformation::concat(&[Transformation::view(0,off,inp_choice.clone()),
                                            inp_cond,inp_el,
                                            Transformation::view(off,ch_sz-off,inp_choice)]);
        Ok((OptRef::Owned(nchoice),ninp))
    }
}

pub fn choice_set_chosen<'a,T,Em>(choice: OptRef<'a,Choice<T>>,
                                  inp_choice: Transf<Em>,
                                  inp_cond: Transf<Em>,
                                  el: OptRef<'a,T>,
                                  inp_el: Transf<Em>)
                                  -> Result<(OptRef<'a,Choice<T>>,
                                             Transf<Em>),Em::Error>
    where T : Composite+Clone+Ord,Em : Embed {
    debug_assert_eq!(choice.as_ref().num_elem(),inp_choice.size());
    debug_assert_eq!(inp_cond.size(),1);
    debug_assert_eq!(el.as_ref().num_elem(),inp_el.size());

    let inp_ncond = Transformation::not(inp_cond.clone());
    let mut off = 0;
    let mut insert_pos = None;
    let mut replace = false;
    let mut ninp = Vec::with_capacity(choice.as_ref().num_elem()*2);
    for (pos,cel) in choice.as_ref().0.iter().enumerate() {
        let sz = cel.num_elem();
        let old_cond = Transformation::view(off,1,inp_choice.clone());
        let inp_cel = Transformation::view(off+1,sz,inp_choice.clone());
        if insert_pos.is_some() {
            let new_cond = Transformation::and(vec![inp_ncond.clone(),old_cond]);
            ninp.push(new_cond);
            ninp.push(inp_cel);
        } else {
            match el.as_ref().cmp(&cel) {
                Ordering::Equal => {
                    insert_pos = Some(pos);
                    replace = true;
                    let new_cond = Transformation::or(vec![inp_cond.clone(),old_cond]);
                    let new_el = Transformation::ite(inp_cond.clone(),inp_el.clone(),inp_cel);
                    ninp.push(new_cond);
                    ninp.push(new_el);
                },
                Ordering::Less => {
                    insert_pos = Some(pos);
                    replace = false;
                    ninp.push(inp_cond.clone());
                    ninp.push(inp_el.clone());
                    let new_cond = Transformation::and(vec![inp_ncond.clone(),old_cond]);
                    ninp.push(new_cond);
                    ninp.push(inp_cel);
                },
                Ordering::Greater => {
                    let new_cond = Transformation::and(vec![inp_ncond.clone(),old_cond]);
                    ninp.push(new_cond);
                    ninp.push(inp_cel);
                }
            }
        }
        off+=sz+1;
    }
    let nchoice = match insert_pos {
        None => {
            ninp.push(inp_cond);
            ninp.push(inp_el);
            let mut vec = choice.as_obj().0;
            vec.push(el.as_obj());
            OptRef::Owned(Choice(vec))
        },
        Some(pos) => if replace {
            choice
        } else {
            let mut vec = choice.as_obj().0;
            vec.insert(pos,el.as_obj());
            OptRef::Owned(Choice(vec))
        }
    };
    Ok((nchoice,Transformation::concat(&ninp[..])))
}

pub struct ChoiceAccess<T,Em : Embed> {
    next_idx: usize,
    last_off: usize,
    choice: Vec<T>,
    choice_inp: Transf<Em>,
    nchoice_inp: Vec<Transf<Em>>
}

impl<T : Composite,Em : Embed> ChoiceAccess<T,Em> {
    pub fn new(ch: Choice<T>,tr: Transf<Em>) -> Self {
        ChoiceAccess { next_idx: 0,
                       last_off: 0,
                       choice: ch.0,
                       choice_inp: tr,
                       nchoice_inp: Vec::new() }
    }
    pub fn next(&mut self) -> Option<(&mut Transf<Em>,&mut T,&mut Transf<Em>)> {
        if self.next_idx < self.choice.len() {
            let nxt = self.next_idx;
            Some(self.next_to(nxt))
        } else {
            None
        }
    }
    pub fn next_to(&mut self,idx: usize) -> (&mut Transf<Em>,&mut T,&mut Transf<Em>) {
        assert!(idx >= self.next_idx);
        if self.next_idx<idx {
            let mut skip = 0;
            for i in self.next_idx..idx {
                skip+=self.choice[i].num_elem()+1;
            }
            self.nchoice_inp.push(Transformation::view(self.last_off,skip,self.choice_inp.clone()));
            self.last_off+=skip;
        }
        self.next_idx = idx+1;
        let sz = self.choice[idx].num_elem();
        let l = self.nchoice_inp.len();
        self.nchoice_inp.push(Transformation::view(self.last_off,1,self.choice_inp.clone()));
        self.nchoice_inp.push(Transformation::view(self.last_off+1,sz,self.choice_inp.clone()));
        self.last_off+=sz+1;
        let (a,b) = self.nchoice_inp.split_at_mut(l+1);
        (&mut a[l],&mut self.choice[idx],&mut b[0])
    }
    /// Destroy the iterator and return the resulting vector and transformation.
    pub fn finish(mut self) -> (Choice<T>,Transf<Em>) {
        if self.next_idx < self.choice.len() {
            let mut skip = 0;
            for i in self.next_idx..self.choice.len() {
                skip+=self.choice[i].num_elem()+1;
            }
            self.nchoice_inp.push(Transformation::view(self.last_off,skip,self.choice_inp));
        }
        (Choice(self.choice),Transformation::concat(&self.nchoice_inp[..]))
    }
}

impl<Em : Embed> Debug for Transformation<Em> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Transformation::Id(w) => fmt.debug_tuple("Id").field(&w).finish(),
            &Transformation::View(off,len,ref tr)
                => fmt.debug_tuple("View")
                .field(&off)
                .field(&len)
                .field(tr)
                .finish(),
            &Transformation::Concat(sz,ref trs)
                => fmt.debug_tuple("Concat")
                .field(&sz).field(trs).finish(),
            &Transformation::Constant(ref cs)
                => fmt.debug_tuple("Constant")
                .field(cs).finish(),
            &Transformation::Map(sz,_,ref tr,ref cache)
                => fmt.debug_tuple("Map")
                .field(&sz)
                .field(tr)
                .field(cache)
                .finish(),
            &Transformation::Zip2(sz,_,ref tr1,ref tr2,ref cache)
                => fmt.debug_tuple("Zip2")
                .field(&sz)
                .field(tr1)
                .field(tr2)
                .field(cache)
                .finish(),
            &Transformation::Zip3(sz,_,ref tr1,ref tr2,ref tr3,ref cache)
                => fmt.debug_tuple("Zip3")
                .field(&sz)
                .field(tr1)
                .field(tr2)
                .field(tr3)
                .field(cache)
                .finish(),
            &Transformation::Write(sz,wr_off,repl_sz,ref obj,ref trg)
                => fmt.debug_tuple("Write")
                .field(&sz)
                .field(&wr_off)
                .field(&repl_sz)
                .field(obj)
                .field(trg)
                .finish(),
            &Transformation::MapByElem(_,ref tr)
                => fmt.debug_tuple("MapByElem")
                .field(tr).finish(),
            &Transformation::ZipsByElem(_,ref trs,ref cache)
                => fmt.debug_tuple("ZipsByElem")
                .field(trs)
                .field(cache)
                .finish(),
            &Transformation::ITE(sz,ref ites,ref def)
                => fmt.debug_tuple("ITE")
                .field(&sz)
                .field(ites)
                .field(def)
                .finish()
        }
    }
}

impl<C : Composite> fmt::Display for CompExpr<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self.0.get(),f)
    }
}

pub fn vec_iter<'a,T,Em : Embed>(vec: OptRef<'a,Vec<T>>,inp: Transf<Em>) -> VecIter<'a,T,Em> {
    match vec {
        OptRef::Ref(ref rvec) => VecIter::Ref(inp,0,rvec.iter()),
        OptRef::Owned(rvec) => VecIter::Owned(inp,0,rvec.into_iter())
    }
}

pub enum VecIter<'a,T : 'a,Em : Embed> {
    Ref(Transf<Em>,usize,slice::Iter<'a,T>),
    Owned(Transf<Em>,usize,vec::IntoIter<T>)
}

impl<'a,T : Composite,Em : Embed> Iterator for VecIter<'a,T,Em> {
    type Item = (OptRef<'a,T>,Transf<Em>);
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut VecIter::Ref(ref inp,ref mut off,ref mut it) => match it.next() {
                None => None,
                Some(ref nxt) => {
                    let sz = nxt.num_elem();
                    let old = *off;
                    *off+=sz;
                    Some((OptRef::Ref(nxt),
                          Transformation::view(old,sz,inp.clone())))
                }
            },
            &mut VecIter::Owned(ref inp,ref mut off,ref mut it) => match it.next() {
                None => None,
                Some(nxt) => {
                    let sz = nxt.num_elem();
                    let old = *off;
                    *off+=sz;
                    Some((OptRef::Owned(nxt),
                          Transformation::view(old,sz,inp.clone())))
                }
            }
        }
    }
}

#[derive(Copy,Clone)]
pub struct AssocKey<'a,K : 'a>(pub &'a K);

pub trait CondIterator<Em : Embed> : Sized {
    type Item;
    fn next(&mut self,&mut Vec<Transf<Em>>,usize,&mut Em)
            -> Result<Option<Self::Item>,Em::Error>;
    fn cond_iter(self) -> CondIter<Em,Self> {
        CondIter { conds: Vec::new(),
                   iter: self }
    }
    fn get<'a,Obj>(self,obj: &'a Obj,obj_inp: Transf<Em>) -> Getter<'a,Em,Obj,Self> {
        Getter { obj: obj,
                 obj_inp: obj_inp,
                 iter: self }
    }
    fn get_element<'a,Obj>(self,obj: &'a Obj) -> GetterElement<'a,Obj,Self> {
        GetterElement { obj: obj,
                        iter: self }
    }
    fn then<V>(self,view: V) -> ThenIterator<V,Self> {
        ThenIterator { view: view,
                       iter: self }
    }
    fn before<V>(self,view: V) -> BeforeIterator<V,Self> {
        BeforeIterator { view: view,
                         iter: self }
    }
    fn seq<It,Ctx,F>(self,ctx: Ctx,f: F) -> Seq<Self,It,Ctx,F>
        where F : FnMut(&Ctx,Self::Item,&mut Em) -> Result<It,Em::Error> {
        Seq { ctx: ctx,
              iter1: self,
              iter2: None,
              f: f }
    }
    fn seq_pure<It,Ctx,F>(self,ctx: Ctx,f: F) -> SeqPure<Self,It,Ctx,F>
        where F : FnMut(&Ctx,Self::Item) -> It {
        SeqPure { iter1: self,
                  iter2: None,
                  ctx: ctx,
                  f: f }
    }
    fn product<It : Clone+CondIterator<Em>>(self,it: It) -> Product<Em,Self,It> {
        Product::new(self,it)
    }
    fn map<A,F>(self,f: F) -> Map<Self,F>
        where F : FnMut(Self::Item,&mut Em) -> Result<A,Em::Error> {
        Map { iter: self,
              f: f }
    }
    fn adjust_idx<Idx>(self,idx: Idx) -> AdjustIdx<Self,Idx> {
        AdjustIdx { iter: self,
                    idx: idx }
    }
    fn filter<Ctx,F,R>(self,ctx: Ctx,f: F) -> Filter<Self,Ctx,F>
        where F : FnMut(&Ctx,Self::Item) -> Option<R> {
        Filter { ctx: ctx,
                 iter: self,
                 f: f }
    }
    fn context<Ctx>(self,ctx: Ctx) -> Context<Self,Ctx> {
        Context { ctx: ctx,
                  iter: self }
    }
}

pub struct CondIter<Em : Embed,It : CondIterator<Em>> {
    conds: Vec<Transf<Em>>,
    iter: It,
}

impl<Em : Embed,It : CondIterator<Em>> CondIter<Em,It> {
    pub fn next(&mut self,em: &mut Em)
                -> Result<Option<(&[Transf<Em>],It::Item)>,Em::Error> {
        match self.iter.next(&mut self.conds,0,em)? {
            None => Ok(None),
            Some(r) => Ok(Some((&self.conds[..],r)))
        }
    }
    pub fn find<P>(&mut self,mut predicate: P,em: &mut Em)
                   -> Result<Option<(&[Transf<Em>],It::Item)>,Em::Error>
        where P : FnMut(&It::Item) -> bool {
        while let Some(x) = self.iter.next(&mut self.conds,0,em)? {
            if predicate(&x) {
                return Ok(Some((&self.conds[..],x)))
            }
        }
        Ok(None)
    }
}

impl<'a,Em : Embed,
     V : ViewMut,
     It : CondIterator<Em,Item=(V,V::Element,Transf<Em>)>
     > CondIter<Em,It> {

    pub fn apply(mut self,obj: &mut V::Viewed,inp: Transf<Em>,em: &mut Em)
                 -> Result<Transf<Em>,Em::Error> {
        let mut ninp : Updates<Em> = Vec::new();
        while let Some((cond,(view,el,inp_el))) = self.next(em)? {
            if cond.len()==0 {
                let (off,osize) = {
                    let (off,ptr) = view.get_el_mut_ext(obj);
                    let osize = ptr.num_elem();
                    *ptr = el;
                    (off,osize)
                };
                insert_updates(&mut ninp,off,osize,inp_el);
            } else {
                let (off,osize,inp_nel) = {
                    let (off,ptr) = view.get_el_mut_ext(obj);
                    let osize = ptr.num_elem();
                    let (rptr,ninp) = {
                        let (nptr,ninp) = ite(OptRef::Owned(el),
                                              OptRef::Ref(ptr),
                                              Transformation::and(cond.to_vec()),
                                              inp_el,
                                              Transformation::view(off,ptr.num_elem(),inp.clone()),
                                              em)?.expect("Failed to apply because of mismatching new entry");
                        let rptr = nptr.as_obj();
                        (rptr,ninp)
                    };
                    *ptr = rptr;
                    (off,osize,ninp)
                };
                insert_updates(&mut ninp,off,osize,inp_nel);
            }
        }
        Ok(finish_updates(ninp,inp))
    }
}

impl<Em : Embed,El : Composite,It : CondIterator<Em,Item=(El,Transf<Em>)>> CondIter<Em,It> {
    pub fn collect(mut self,def: El,inp_def: Transf<Em>,em: &mut Em) -> Result<(El,Transf<Em>),Em::Error> {
        let mut cur = def;
        let mut inp_cur = inp_def;
        while let Some((cond,(el,inp_el))) = self.next(em)? {
            let rcond = Transformation::and(cond.to_vec());
            let (res,inp_res) = ite(OptRef::Owned(el),
                                    OptRef::Owned(cur),
                                    rcond,inp_el,inp_cur,em)?.expect("Failed to collect");
            cur = res.as_obj();
            inp_cur = inp_res;
        }
        Ok((cur,inp_cur))
    }
    pub fn collect1(mut self,em: &mut Em) -> Result<(El,Transf<Em>),Em::Error> {
        match self.next(em)? {
            None => panic!("Failed to collect: Empty iterator"),
            Some((_,(el,inp_el))) => self.collect(el,inp_el,em)
        }
    }
}
impl<Em : Embed,El : Ord+Composite,It : CondIterator<Em,Item=(El,Transf<Em>)>> CondIter<Em,It> {
    pub fn to_choice(mut self,em: &mut Em)
                     -> Result<(Choice<El>,Transf<Em>),Em::Error> {
        let mut els : Vec<El> = Vec::new();
        let mut inps : Vec<Transf<Em>> = Vec::new();
        while let Some((cond,(el,inp_el))) = self.next(em)? {
            let rcond = Transformation::and(cond.to_vec());
            let mut inserted = false;
            for i in 0..els.len() {
                match els[i].cmp(&el) {
                    Ordering::Equal => {
                        let inp_nel = Transformation::ite(rcond.clone(),
                                                          inp_el.clone(),
                                                          inps[i*2+1].clone());
                        let ncond = Transformation::or(vec![rcond.clone(),inps[i*2].clone()]);
                        inps[i*2] = ncond;
                        inps[i*2+1] = inp_nel;
                        inserted = true;
                        break
                    },
                    Ordering::Less => {
                        els.insert(i,el.clone());
                        inps.insert(i*2,rcond.clone());
                        inps.insert(i*2+1,inp_el.clone());
                        inserted = true;
                        break
                    },
                    Ordering::Greater => {}
                }
            }
            if !inserted {
                els.push(el);
                inps.push(rcond);
                inps.push(inp_el);
            }
        }
        Ok((Choice(els),Transformation::concat(&inps[..])))
    }
}

#[derive(Clone)]
pub struct Getter<'a,Em : Embed,Obj : 'a,It> {
    obj: &'a Obj,
    obj_inp: Transf<Em>,
    iter: It
}

impl<'a,Em : Embed,Obj : 'a+Composite,It : CondIterator<Em>> CondIterator<Em> for Getter<'a,Em,Obj,It>
    where It::Item : 'a+View<Viewed=Obj> {
    type Item = (It::Item,&'a <It::Item as View>::Element,Transf<Em>);
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(view) => {
                let (off,el) = view.get_el_ext(self.obj);
                let el_sz = el.num_elem();
                let el_inp = Transformation::view(off,el_sz,self.obj_inp.clone());
                Ok(Some((view,el,el_inp)))
            }
        }
    }
}

pub struct GetterElement<'a,Obj : 'a,It> {
    obj: &'a Obj,
    iter: It
}

impl<'a,Em : Embed,Obj : 'a+Composite,It : CondIterator<Em>> CondIterator<Em> for GetterElement<'a,Obj,It>
    where It::Item : 'a+View<Viewed=Obj> {
    type Item = &'a <It::Item as View>::Element;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(view) => {
                let el = view.get_el(self.obj);
                Ok(Some(el))
            }
        }
    }
}

impl<'a,Obj : 'a,It : Clone> Clone for GetterElement<'a,Obj,It> {
    fn clone(&self) -> Self {
        GetterElement { obj: self.obj,
                        iter: self.iter.clone() }
    }
}

#[derive(Clone)]
pub struct ThenIterator<V,It> {
    view: V,
    iter: It
}

impl<Em : Embed,V : Clone,It : CondIterator<Em>> CondIterator<Em> for ThenIterator<V,It> {
    type Item = Then<It::Item,V>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(res) => Ok(Some(Then::new(res,self.view.clone())))
        }
    }
}

#[derive(Clone)]
pub struct BeforeIterator<V,It> {
    view: V,
    iter: It
}

impl<Em : Embed,V : Clone,It : CondIterator<Em>> CondIterator<Em> for BeforeIterator<V,It> {
    type Item = Then<V,It::Item>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(res) => Ok(Some(Then::new(self.view.clone(),res)))
        }
    }
}

pub struct Seq<It1,It2,Ctx,F> {
    ctx: Ctx,
    iter1: It1,
    iter2: Option<(It2,usize)>,
    f: F
}

impl<It1 : Clone,It2 : Clone,Ctx : Clone,F : Copy> Clone for Seq<It1,It2,Ctx,F> {
    fn clone(&self) -> Self {
        Seq { ctx: self.ctx.clone(),
              iter1: self.iter1.clone(),
              iter2: self.iter2.clone(),
              f: self.f }
    }
}

impl<Em,It1,It2,Ctx,F> CondIterator<Em> for Seq<It1,It2,Ctx,F>
    where Em : Embed,
          It1 : CondIterator<Em>,
          It2 : CondIterator<Em>,
          F : FnMut(&Ctx,It1::Item,&mut Em) -> Result<It2,Em::Error> {

    type Item = It2::Item;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        let el2 = match self.iter2 {
            Some((ref mut it2,off)) => match it2.next(conds,off,em)? {
                Some(el) => Some(el),
                None => None
            },
            None => None
        };
        match el2 {
            Some(el) => Ok(Some(el)),
            None => loop {
                match self.iter1.next(conds,pos,em)? {
                    None => return Ok(None),
                    Some(el) => {
                        let npos = conds.len();
                        let mut niter = (self.f)(&self.ctx,el,em)?;
                        match niter.next(conds,npos,em)? {
                            None => {},
                            Some(nel) => {
                                self.iter2 = Some((niter,npos));
                                return Ok(Some(nel))
                            }
                        }
                    }
                }
            }
        }
    }
}

pub struct SeqPure<It1,It2,Ctx,F> {
    iter1: It1,
    iter2: Option<(It2,usize)>,
    ctx: Ctx,
    f: F
}

impl<Em,It1,It2,Ctx,F> CondIterator<Em> for SeqPure<It1,It2,Ctx,F>
    where Em : Embed,
          It1 : CondIterator<Em>,
          It2 : CondIterator<Em>,
          F : FnMut(&Ctx,It1::Item) -> It2 {

    type Item = It2::Item;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        let el2 = match self.iter2 {
            Some((ref mut it2,off)) => match it2.next(conds,off,em)? {
                Some(el) => Some(el),
                None => None
            },
            None => None
        };
        match el2 {
            Some(el) => Ok(Some(el)),
            None => loop {
                match self.iter1.next(conds,pos,em)? {
                    None => return Ok(None),
                    Some(el) => {
                        let npos = conds.len();
                        let mut niter = (self.f)(&self.ctx,el);
                        match niter.next(conds,npos,em)? {
                            None => {},
                            Some(nel) => {
                                self.iter2 = Some((niter,npos));
                                return Ok(Some(nel))
                            }
                        }
                    }
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct Product<Em : Embed,It1 : CondIterator<Em>,It2> {
    iter1: It1,
    iter2: It2,
    state: Option<(It1::Item,usize,It2)>
}

impl<Em : Embed,It1 : CondIterator<Em>,It2 : Clone+CondIterator<Em>> Product<Em,It1,It2> {
    pub fn new(it1: It1,it2: It2) -> Self {
        Product { iter1: it1,
                  iter2: it2,
                  state: None }
    }
    fn take_state(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
                  -> Result<Option<(It1::Item,usize,It2)>,Em::Error> {
        match self.state.take() {
            Some(r) => Ok(Some(r)),
            None => {
                conds.truncate(pos);
                match self.iter1.next(conds,pos,em)? {
                    None => Ok(None),
                    Some(el) => Ok(Some((el,pos,self.iter2.clone())))
                }
            }
        }
    }
}

impl<Em : Embed,It1 : CondIterator<Em>,It2 : Clone+CondIterator<Em>> CondIterator<Em> for Product<Em,It1,It2>
    where It1::Item : Clone {
    type Item = (It1::Item,It2::Item);
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        while let Some((el1,pos1,mut it2)) = self.take_state(conds,pos,em)? {
            match it2.next(conds,pos1,em)? {
                None => continue,
                Some(el2) => {
                    self.state = Some((el1.clone(),pos1,it2));
                    return Ok(Some((el1,el2)))
                }
            }
        }
        Ok(None)
    }
}

#[derive(Clone)]
pub struct Map<It,F> {
    iter: It,
    f: F
}

impl<Em,It,A,F> CondIterator<Em> for Map<It,F>
    where Em : Embed,
          It : CondIterator<Em>,
          F : FnMut(It::Item,&mut Em) -> Result<A,Em::Error> {

    type Item = A;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<A>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(el) => Ok(Some((self.f)(el,em)?))
        }
    }
}

pub struct IndexedIter<Em : DeriveValues> {
    iter: IndexIterator<Em::Sort,Em::ValueIterator>,
    idx: Transf<Em>
}

impl<Em : DeriveValues> CondIterator<Em> for IndexedIter<Em> {
    type Item = usize;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,_: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next() {
            None => Ok(None),
            Some((i,val)) => {
                conds.truncate(pos);
                let cond_fun = move |_:&[Em::Expr],_:usize,e:Em::Expr,em:&mut Em| {
                    let cv = em.embed(expr::Expr::Const(val.clone()))?;
                    em.eq(e,cv)
                };
                let cond = Transformation::map_by_elem(Box::new(cond_fun),self.idx.clone());
                conds.push(cond);
                Ok(Some(i))
            }
        }
    }
}

impl<Em : DeriveValues> Clone for IndexedIter<Em> {
    fn clone(&self) -> Self {
        IndexedIter { iter: self.iter.clone(),
                      idx: self.idx.clone() }
    }
}

pub fn access_dyn<T,Em : DeriveValues>(vec: &Vec<T>,
                                       pos: Transf<Em>,
                                       exprs: &[Em::Expr],
                                       em: &mut Em)
                                       -> Result<IndexedIter<Em>,Em::Error> {
    let idx = pos.get(exprs,0,em)?;
    let opt_vals = em.derive_values(&idx)?;
    let it = match opt_vals {
        Some(rvals) => IndexIterator::Limited(rvals),
        None => {
            let idx_srt = em.type_of(&idx)?;
            let idx_rsrt = em.unbed_sort(&idx_srt)?;
            IndexIterator::Unlimited(idx_rsrt,0..vec.len())
        }
    };
    Ok(IndexedIter { iter: it,
                     idx: pos })
}

pub struct Chosen<'a,T : 'a,Em : Embed> {
    choice: &'a Choice<T>,
    inp_choice: Transf<Em>,
    idx: usize,
    off: usize
}

impl<'a,Em : Embed,T : Composite> CondIterator<Em> for Chosen<'a,T,Em> {
    type Item = ChoiceView<T>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,_: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        if self.idx<self.choice.0.len() {
            conds.truncate(pos);
            conds.push(Transformation::view(self.off,1,self.inp_choice.clone()));
            self.off+=self.choice.0[self.idx].num_elem()+1;
            let res = self.idx;
            self.idx+=1;
            Ok(Some(ChoiceView::new(res)))
        } else {
            Ok(None)
        }
    }
}

impl<'a,T : 'a,Em : Embed> Clone for Chosen<'a,T,Em> {
    fn clone(&self) -> Self {
        Chosen { choice: self.choice,
                 inp_choice: self.inp_choice.clone(),
                 idx: self.idx,
                 off: self.off }
    }
}

impl<T> Choice<T> {
    pub fn chosen<'a,Em : Embed>(&'a self,inp: Transf<Em>) -> Chosen<'a,T,Em> {
        Chosen { choice: self,
                 inp_choice: inp,
                 idx: 0,
                 off: 0 }
    }
}

impl<T : Composite> BitVecVectorStack<T> {
    pub fn access_top<Em : DeriveValues>(&self,
                                         inp: Transf<Em>,
                                         exprs: &[Em::Expr],
                                         em: &mut Em)
                                         -> Result<BitVecVectorStackAccess<T,Em>,Em::Error> {
        let idx = inp.get(exprs,0,em)?;
        let opt_vals = em.derive_values(&idx)?;
        let it = match opt_vals {
            Some(rvals) => IndexIterator::Limited(rvals),
            None => {
                let idx_srt = em.type_of(&idx)?;
                let idx_rsrt = em.unbed_sort(&idx_srt)?;
                IndexIterator::Unlimited(idx_rsrt,0..self.elements.len())
            }
        };
        Ok(BitVecVectorStackAccess { iter: IndexedIter { iter: it,
                                                         idx: Transformation::view(0,1,inp) },
                                     phantom: PhantomData })

    }
}

pub struct IndexRec<Idx,SIdx>(Idx,SIdx);
#[derive(Clone,Copy)]
pub struct PositionRec<P,SP>(P,SP);

impl<Em : Embed,Idx> CondIterator<Em> for Once<Idx> {
    type Item = Idx;
    fn next(&mut self,_: &mut Vec<Transf<Em>>,_: usize,_: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        Ok(<Self as Iterator>::next(self))
    }
}

pub struct AdjustIdx<It,Idx> {
    iter: It,
    idx: Idx
}

impl<Em : Embed,Idx : Copy,It : CondIterator<Em>> CondIterator<Em> for AdjustIdx<It,Idx> {
    type Item = IndexRec<Idx,It::Item>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(idx) => Ok(Some(IndexRec(self.idx,idx)))
        }
    }
}

pub trait View {
    type Viewed : Composite;
    type Element : Composite;
    fn get_el<'a>(&self,obj: &'a Self::Viewed)
                  -> &'a Self::Element where Self : 'a {
        self.get_el_ext(obj).1
    }
    fn get_el_ext<'a>(&self,&'a Self::Viewed)
                      -> (usize,&'a Self::Element) where Self : 'a;
    fn get_with_inp<'a,Em : Embed>(&self,obj: &'a Self::Viewed,inp: Transf<Em>) -> (&'a Self::Element,Transf<Em>) where Self : 'a {
        let (off,el) = self.get_el_ext(obj);
        (el,Transformation::view(off,el.num_elem(),inp))
    }
    fn then<V : View<Viewed=Self::Element>>(self,v: V) -> Then<Self,V>
        where Self : Sized {
        Then::new(self,v)
    }
}

pub trait ViewMut : View {
    fn get_el_mut<'a>(&self,obj: &'a mut Self::Viewed)
                      -> &'a mut Self::Element where Self : 'a {
        self.get_el_mut_ext(obj).1
    }
    fn get_el_mut_ext<'a>(&self,obj: &'a mut Self::Viewed)
                          -> (usize,&'a mut Self::Element) where Self : 'a;

    fn write<Em : Embed>(&self,
                         el: Self::Element,
                         el_inp: Transf<Em>,
                         new: &mut Self::Viewed,
                         upd: &mut Updates<Em>) -> () {
        let (off,ref_new) = self.get_el_mut_ext(new);
        let old_sz = ref_new.num_elem();
        *ref_new = el;
        insert_updates(upd,off,old_sz,el_inp);
    }
}

pub trait ViewOpt : View {
    fn get_el_opt<'a>(&self,obj: &'a Self::Viewed)
                      -> Option<&'a Self::Element> where Self : 'a {
        match self.get_el_opt_ext(obj) {
            None => None,
            Some((_,el)) => Some(el)
        }
    }
    fn get_el_opt_ext<'a>(&self,&'a Self::Viewed)
                          -> Option<(usize,&'a Self::Element)> where Self : 'a;
    fn get_opt_with_inp<'a,Em : Embed>(&self,obj: &'a Self::Viewed,inp: Transf<Em>) -> Option<(&'a Self::Element,Transf<Em>)> where Self : 'a {
        match self.get_el_opt_ext(obj) {
            Some((off,el)) => Some((el,Transformation::view(off,el.num_elem(),inp))),
            None => None
        }
    }
}

pub trait ViewInsert : ViewOpt {
    fn insert_el(&self,obj: &mut Self::Viewed,el: Self::Element)
                 -> (usize,usize);
    fn insert<Em : Embed>(&self,
                          obj: &mut Self::Viewed,
                          el: Self::Element,
                          el_inp: Transf<Em>,
                          upd: &mut Updates<Em>) -> () {
        let (off,old_sz) = self.insert_el(obj,el);
        insert_updates(upd,off,old_sz,el_inp);
    }
}

#[derive(Clone,PartialEq,Eq)]
pub struct VecView<T> {
    pub idx: usize,
    phantom: PhantomData<T>
}

impl<T> VecView<T> {
    pub fn new(idx: usize) -> Self {
        VecView { idx: idx,
                  phantom: PhantomData }
    }
}

impl<T : Composite> View for VecView<T> {
    type Viewed = Vec<T>;
    type Element = T;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj[self.idx]
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        let mut off = 0;
        for i in 0..self.idx {
            off+=obj[i].num_elem();
        }
        let res = &obj[self.idx];
        (off,res)
    }
}

impl<'a,T : Composite> ViewMut for VecView<T> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj[self.idx]
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        let mut off = 0;
        for i in 0..self.idx {
            off+=obj[i].num_elem();
        }
        let res = &mut obj[self.idx];
        (off,res)
    }
}

#[derive(PartialEq,Eq)]
pub struct AssocView<K,V> {
    pub key: K,
    phantom: PhantomData<V>
}

impl<K : Clone,V> Clone for AssocView<K,V> {
    fn clone(&self) -> Self {
        AssocView { key: self.key.clone(),
                    phantom: PhantomData }
    }
}

impl<K,V> AssocView<K,V> {
    pub fn new(key: K) -> Self {
        AssocView { key: key,
                    phantom: PhantomData }
    }
}

impl<K : Ord+Clone+Hash,V : Composite> View for AssocView<K,V> {
    type Viewed = Assoc<K,V>;
    type Element = V;
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        let mut off = 0;
        for &(ref k,ref el) in obj.0.iter() {
            match k.cmp(&self.key) {
                Ordering::Equal => return (off,el),
                Ordering::Less => { off+=el.num_elem() },
                Ordering::Greater => panic!("Assoc element not found")
            }
        }
        panic!("Assoc element not found")
    }
}

impl<K : Ord+Clone+Hash,V : Composite> ViewMut for AssocView<K,V> {
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        let mut off = 0;
        for &mut (ref k,ref mut el) in obj.0.iter_mut() {
            match k.cmp(&self.key) {
                Ordering::Equal => return (off,el),
                Ordering::Less => { off+=el.num_elem() },
                Ordering::Greater => panic!("Assoc element not found")
            }
        }
        panic!("Assoc element not found")
    }
}

impl<K : Ord+Clone+Hash,V : Composite> ViewOpt for AssocView<K,V> {
    fn get_el_opt_ext<'b>(&self,obj: &'b Self::Viewed)
                          -> Option<(usize,&'b Self::Element)> where Self : 'b {
        let mut off = 0;
        for &(ref k,ref el) in obj.0.iter() {
            match k.cmp(&self.key) {
                Ordering::Equal => return Some((off,el)),
                Ordering::Less => { off+=el.num_elem() },
                Ordering::Greater => return None
            }
        }
        None
    }
}

impl<K : Ord+Clone+Hash,V : Composite> ViewInsert for AssocView<K,V> {
    fn insert_el(&self,obj: &mut Self::Viewed,el: Self::Element)
                 -> (usize,usize) {
        let mut off = 0;
        for i in 0..obj.0.len() {
            match obj.0[i].0.cmp(&self.key) {
                Ordering::Equal => {
                    let old_sz = obj.0[i].1.num_elem();
                    obj.0[i].1 = el;
                    return (off,old_sz)
                },
                Ordering::Less => { off+=obj.0[i].1.num_elem() },
                Ordering::Greater => {
                    obj.0.insert(i,(self.key.clone(),el));
                    return (off,0)
                }
            }
        }
        obj.0.push((self.key.clone(),el));
        (off,0)
    }
}

type Updates<Em> = Vec<(usize,usize,Transf<Em>)>;

fn insert_updates<Em : Embed>(upd: &mut Updates<Em>,
                              off: usize,old: usize,
                              new: Transf<Em>) -> () {
    for i in 0..upd.len() {
        let (coff,old_sz,_) = upd[i];
        if coff < off {
            debug_assert!(coff+upd[i].2.size()<=off);
            continue
        }
        if coff==off {
            debug_assert_eq!(old_sz,old);
            debug_assert_eq!(upd[i].2.size(),new.size());
            upd[i].2 = new;
            return
        }
        debug_assert!(off+old<=coff);
        let nsz = new.size();
        if old!=nsz {
            for j in i..upd.len() {
                upd[j].1 = upd[j].1 + nsz - old;
            }
        }
        upd.insert(i,(off,old,new));
        return
    }
    upd.push((off,old,new))
}

pub fn finish_updates<Em : Embed>(mut upd: Updates<Em>,orig: Transf<Em>) -> Transf<Em> {
    let mut last = 0;
    let mut orig_off = 0;
    let mut res = Vec::new();
    for (off,old,new) in upd.drain(..) {
        debug_assert!(off>=last);
        if off > last {
            res.push(Transformation::view(orig_off,off-last,orig.clone()));
        }
        orig_off+=old;
        last = off+new.size();
        res.push(new);
    }
    if orig_off!=orig.size() {
        res.push(Transformation::view(orig_off,orig.size()-orig_off,orig));
    }
    Transformation::concat(&res[..])
}

#[derive(Clone,PartialEq,Eq)]
pub struct BitVecVectorStackView<T> {
    pub idx: usize,
    phantom: PhantomData<T>
}

impl<Up> BitVecVectorStackView<Up> {
    pub fn new(idx: usize) -> Self {
        BitVecVectorStackView { idx: idx,
                                phantom: PhantomData }
    }
}

impl<T : Composite> View for BitVecVectorStackView<T> {
    type Viewed = BitVecVectorStack<T>;
    type Element = T;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.elements[self.idx]
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        let mut off = 0;
        for i in 0..self.idx {
            off+=obj.elements[i].num_elem();
        }
        let res = &obj.elements[self.idx];
        (off,res)
    }
}

impl<T : Composite> ViewMut for BitVecVectorStackView<T> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.elements[self.idx]
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        let mut off = 0;
        for i in 0..self.idx {
            off+=obj.elements[i].num_elem();
        }
        let res = &mut obj.elements[self.idx];
        (off,res)
    }
}

#[derive(Clone,PartialEq,Eq)]
pub struct Then<Up,V>(pub Up,pub V);

impl<Up,V> Then<Up,V> {
    pub fn new(up: Up,nxt: V) -> Self {
        Then(up,nxt)
    }
}

impl<Up : View,V : View<Viewed=Up::Element>> View for Then<Up,V> {
    type Viewed = Up::Viewed;
    type Element = V::Element;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        self.1.get_el(self.0.get_el(obj))
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        let (off1,sub) = self.0.get_el_ext(obj);
        let (off2,res) = self.1.get_el_ext(sub);
        (off1+off2,res)
    }
}

impl<Up : ViewMut,V : ViewMut<Viewed=Up::Element>> ViewMut for Then<Up,V> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        self.1.get_el_mut(self.0.get_el_mut(obj))
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        let (off1,sub) = self.0.get_el_mut_ext(obj);
        let (off2,res) = self.1.get_el_mut_ext(sub);
        (off1+off2,res)
    }
}

impl<Up : View,V : ViewOpt<Viewed=Up::Element>> ViewOpt for Then<Up,V> {
    fn get_el_opt<'b>(&self,obj: &'b Self::Viewed)
                      -> Option<&'b Self::Element> where Self : 'b {
        self.1.get_el_opt(self.0.get_el(obj))
    }
    fn get_el_opt_ext<'b>(&self,obj: &'b Self::Viewed)
                          -> Option<(usize,&'b Self::Element)> where Self : 'b {
        let (off1,sub) = self.0.get_el_ext(obj);
        match self.1.get_el_opt_ext(sub) {
            None => None,
            Some((off2,res)) => Some((off1+off2,res))
        }
    }
}

impl<Up : ViewMut,V : ViewInsert<Viewed=Up::Element>> ViewInsert for Then<Up,V> {
    fn insert_el(&self,obj: &mut Self::Viewed,el: Self::Element)
                 -> (usize,usize) {
        let (off1,sub) = self.0.get_el_mut_ext(obj);
        let (off2,old_sz) = self.1.insert_el(sub,el);
        (off1+off2,old_sz)
    }
}


#[derive(PartialEq,Eq)]
pub struct FstView<A,B>(PhantomData<(A,B)>);

impl<A,B> Clone for FstView<A,B> {
    fn clone(&self) -> Self {
        FstView(PhantomData)
    }
}

#[derive(PartialEq,Eq)]
pub struct SndView<A,B>(PhantomData<(A,B)>);

impl<A,B> Clone for SndView<A,B> {
    fn clone(&self) -> Self {
        SndView(PhantomData)
    }
}

impl<A,B> FstView<A,B> {
    pub fn new() -> Self {
        FstView(PhantomData)
    }
}

impl<A,B> SndView<A,B> {
    pub fn new() -> Self {
        SndView(PhantomData)
    }
}

impl<A : Composite,B : Composite> View for FstView<A,B> {
    type Viewed = (A,B);
    type Element = A;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.0
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (0,&obj.0)
    }
}

impl<A : Composite,B : Composite> View for SndView<A,B> {
    type Viewed = (A,B);
    type Element = B;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.1
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        (obj.0.num_elem(),&obj.1)
    }
}

impl<A : Composite,B : Composite> ViewMut for FstView<A,B> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.0
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        (0,&mut obj.0)
    }
}

impl<A : Composite,B : Composite> ViewMut for SndView<A,B> {
    fn get_el_mut<'b>(&self,obj: &'b mut Self::Viewed)
                      -> &'b mut Self::Element where Self : 'b {
        &mut obj.1
    }
    fn get_el_mut_ext<'b>(&self,obj: &'b mut Self::Viewed)
                          -> (usize,&'b mut Self::Element) where Self : 'b {
        (obj.0.num_elem(),&mut obj.1)
    }
}

#[derive(Clone,PartialEq,Eq)]
pub struct ChoiceView<T> {
    idx: usize,
    phantom: PhantomData<T>
}

impl<T> ChoiceView<T> {
    pub fn new(idx: usize) -> Self {
        ChoiceView { idx: idx,
                     phantom: PhantomData }
    }
}

impl<T : Ord+Composite> View for ChoiceView<T> {
    type Viewed = Choice<T>;
    type Element = T;
    fn get_el<'b>(&self,obj: &'b Self::Viewed)
                  -> &'b Self::Element where Self : 'b {
        &obj.0[self.idx]
    }
    fn get_el_ext<'b>(&self,obj: &'b Self::Viewed)
                      -> (usize,&'b Self::Element) where Self : 'b {
        let mut off = self.idx;
        for i in 0..self.idx {
            off+=obj.0[i].num_elem();
        }
        (off,&obj.0[self.idx])
    }
}

pub struct BitVecVectorStackAccess<T,Em : DeriveValues> {
    iter: IndexedIter<Em>,
    phantom: PhantomData<T>
}

impl<T,Em : DeriveValues> Clone for BitVecVectorStackAccess<T,Em> {
    fn clone(&self) -> Self {
        BitVecVectorStackAccess { iter: self.iter.clone(),
                                  phantom: PhantomData }
    }
}

impl<T,Em : DeriveValues> CondIterator<Em> for BitVecVectorStackAccess<T,Em> {
    type Item = BitVecVectorStackView<T>;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(idx) => Ok(Some(BitVecVectorStackView::new(idx)))
        }
    }
}

impl<It : CondIterator<Em>,Em : Embed> CondIterator<Em> for Option<It> {
    type Item = It::Item;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self {
            &mut None => Ok(None),
            &mut Some(ref mut it) => it.next(conds,pos,em)
        }
    }
}

pub struct Filter<It,Ctx,F> {
    ctx: Ctx,
    iter: It,
    f: F
}

impl<Em : Embed,Ctx,It : CondIterator<Em>,R,F : FnMut(&Ctx,It::Item) -> Option<R>> CondIterator<Em> for Filter<It,Ctx,F> {
    type Item = R;
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        while let Some(res) = self.iter.next(conds,pos,em)? {
            match (self.f)(&self.ctx,res) {
                None => {},
                Some(nres) => return Ok(Some(nres))
            }
        }
        Ok(None)
    }
}

impl<It : Clone,Ctx : Clone,F : Copy> Clone for Filter<It,Ctx,F> {
    fn clone(&self) -> Self {
        Filter { ctx: self.ctx.clone(),
                 iter: self.iter.clone(),
                 f: self.f }
    }
}

#[derive(Clone)]
pub struct Context<It,Ctx> {
    ctx: Ctx,
    iter: It
}

impl<Em : Embed,Ctx : Clone,It : CondIterator<Em>> CondIterator<Em> for Context<It,Ctx> {
    type Item = (Ctx,It::Item);
    fn next(&mut self,conds: &mut Vec<Transf<Em>>,pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.iter.next(conds,pos,em)? {
            None => Ok(None),
            Some(el) => Ok(Some((self.ctx.clone(),el)))
        }
    }
}

impl<It1,It2,Ctx,F> Clone for SeqPure<It1,It2,Ctx,F>
    where It1 : Clone, It2 : Clone, Ctx : Clone, F : Copy {
    fn clone(&self) -> Self {
        SeqPure { iter1: self.iter1.clone(),
                  iter2: self.iter2.clone(),
                  ctx: self.ctx.clone(),
                  f: self.f }
    }
}
