use expr;
use types;
use types::{SortKind};
use embed::Embed;
use unique::{Uniquer,UniqueRef};
use std::cmp::{Ordering,min,max};
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::rc::Rc;
use std::cell;
use std::cell::RefCell;
use std::hash::Hash;
use std::fmt::Debug;

pub trait Composite : Sized + Eq + Hash {

    fn num_elem(&self) -> usize;
    fn elem_sort<Em : Embed>(&self,usize,&mut Em)
                             -> Result<Em::Sort,Em::Error>;

    fn combine(&self,&Self) -> Option<Self>;

    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,&Self,
                                                  &'a[Em::Expr],&'b[Em::Expr],&mut Vec<Em::Expr>,
                                                  &FComb,&FL,&FR,&mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>;

    fn invariant<Em : Embed,F>(&self,&mut Em,&F,&mut usize,&mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {
        Ok(())
    }
}

#[derive(PartialEq,Eq,Hash,Clone,Debug)]
pub struct CompExpr<C : Composite>(pub UniqueRef<expr::Expr<types::Sort,usize,CompExpr<C>,()>>);

pub struct Comp<'a,C : Composite + 'a> {
    referenced: &'a C,
    exprs: Uniquer<expr::Expr<types::Sort,usize,CompExpr<C>,()>>
}

impl<'a,C : Composite + Clone + Debug> Embed for Comp<'a,C> {
    type Sort = types::Sort;
    type Var = usize;
    type Expr = CompExpr<C>;
    type Fun = ();
    type Error = ();
    fn embed_sort(&mut self,tp: SortKind<types::Sort>)
                  -> Result<types::Sort,()> {
        Ok(types::Sort::from_kind(tp))
    }
    fn unbed_sort(&mut self,tp: &types::Sort) -> Result<SortKind<types::Sort>,()> {
        Ok(tp.kind())
    }
    fn embed(&mut self,e: expr::Expr<types::Sort,usize,CompExpr<C>,()>)
             -> Result<CompExpr<C>,()> {
        Ok(CompExpr(self.exprs.get(e)))
    }
    fn unbed(&mut self,e: &CompExpr<C>)
             -> Result<expr::Expr<types::Sort,usize,CompExpr<C>,()>,()> {
        Ok((*e.0).clone())
    }
    fn type_of_var(&mut self,var: &usize) -> Result<types::Sort,()> {
        self.referenced.elem_sort(*var,self)
    }
    fn type_of_fun(&mut self,_:&()) -> Result<types::Sort,()> {
        panic!("Composite expressions don't have functions")
    }
    fn arity(&mut self,_:&()) -> Result<usize,()> {
        panic!("Composite expressions don't have functions")
    }
    fn type_of_arg(&mut self,_:&(),_:usize) -> Result<types::Sort,()> {
        panic!("Composite expressions don't have functions")
    }
}

#[derive(PartialEq,Eq,Hash)]
pub struct Singleton(types::Sort);

impl Composite for Singleton {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,_:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        self.0.embed(em)
    }
    fn combine(&self,oth: &Self) -> Option<Self> {
        if self.0==oth.0 {
            None
        } else {
            Some(Singleton(self.0.clone()))
        }
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,_: &Singleton,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,_: &FL,_: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        res.push(comb(&lhs[0],&rhs[0],em)?);
        Ok((&lhs[1..],&rhs[1..]))
    }
}

#[derive(PartialEq,Eq,Hash)]
pub struct SingletonBool {}

pub static BOOL_SINGLETON : SingletonBool = SingletonBool {};

impl Composite for SingletonBool {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em : Embed>(&self,_:usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        em.tp_bool()
    }
    fn combine(&self,_: &Self) -> Option<Self> {
        Some(SingletonBool {})
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,_: &SingletonBool,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,_: &FL,_: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        res.push(comb(&lhs[0],&rhs[0],em)?);
        Ok((&lhs[1..],&rhs[1..]))
    }
}

impl<T : Composite + Clone> Composite for Vec<T> {
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
    fn combine(&self,oth: &Vec<T>) -> Option<Vec<T>> {
        let ssize = self.len();
        let osize = oth.len();
        let min_size = min(ssize,osize);
        let max_size = max(ssize,osize);

        let mut res = Vec::with_capacity(max_size);
        
        for i in 0..min_size {
            match self[i].combine(&oth[i]) {
                None => return None,
                Some(nel) => { res.push(nel) }
            }
        }

        if ssize > osize {
            for i in osize..ssize {
                res.push(self[i].clone())
            }
        } else if osize > ssize {
            for i in ssize..osize {
                res.push(oth[i].clone())
            }
        }
        Some(res)
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,oth: &Vec<T>,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let min_size = min(self.len(),oth.len());
        let mut clhs = lhs;
        let mut crhs = rhs;
        for i in 0..min_size {
            let (nlhs,nrhs) = self[i].combine_elem(&oth[i],clhs,crhs,res,comb,only_l,only_r,em)?;
            clhs = nlhs;
            crhs = nrhs;
        }
        if self.len() > oth.len() {
            for i in min_size..self.len() {
                let ref el = self[i];
                for _ in 0..el.num_elem() {
                    res.push(only_l(&clhs[0],em)?);
                    clhs = &clhs[1..];
                }
            }
        } else if oth.len() > self.len() {
            for i in min_size..oth.len() {
                let ref el = self[i];
                for _ in 0..el.num_elem() {
                    res.push(only_r(&crhs[0],em)?);
                    crhs = &crhs[1..];
                }
            }
        }
        Ok((clhs,crhs))
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

#[derive(PartialEq,Eq,Hash)]
pub struct Choice<T>(Vec<T>);

impl<T : Composite + Ord + Clone> Composite for Choice<T> {
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
    fn combine(&self,oth: &Choice<T>) -> Option<Choice<T>> {
        let mut offs = 0;
        let mut offo = 0;
        let mut res = Vec::new();
        loop {
            if offs >= self.0.len() {
                for i in offo..oth.0.len() {
                    res.push(oth.0[i].clone())
                }
                break
            }
            if offo >= oth.0.len() {
                for i in offs..self.0.len() {
                    res.push(self.0[i].clone())
                }
                break
            }
            match self.0[offs].cmp(&oth.0[offo]) {
                Ordering::Equal => match self.0[offs].combine(&oth.0[offo]) {
                    None => return None,
                    Some(nel) => {
                        offs+=1;
                        offo+=1;
                        res.push(nel);
                    }
                },
                Ordering::Less => {
                    offs+=1;
                    res.push(self.0[offs].clone());
                },
                Ordering::Greater => {
                    offo+=1;
                    res.push(oth.0[offo].clone());
                }
            }
        }
        Some(Choice(res))
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
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,oth: &Choice<T>,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let mut pos_l = 0;
        let mut pos_r = 0;
        let mut clhs = lhs;
        let mut crhs = rhs;

        loop {
            if pos_l >= self.0.len() {
                for i in pos_r..oth.0.len() {
                    for _ in 0..oth.0[i].num_elem()+1 {
                        res.push(only_r(&crhs[0],em)?);
                        crhs = &crhs[1..];
                    }
                }
                break;
            }
            if pos_r >= oth.0.len() {
                for i in pos_l..self.0.len() {
                    for _ in 0..self.0[i].num_elem()+1 {
                        res.push(only_l(&clhs[0],em)?);
                        clhs = &clhs[1..];
                    }
                }
                break;
            }
            let ref l = self.0[pos_l];
            let ref r = oth.0[pos_r];
            match l.cmp(&r) {
                Ordering::Equal => {
                    res.push(comb(&clhs[0],&crhs[0],em)?);
                    clhs = &clhs[1..];
                    crhs = &crhs[1..];
                    let (nlhs,nrhs) = l.combine_elem(&r,clhs,crhs,res,comb,only_l,only_r,em)?;
                    clhs = nlhs;
                    crhs = nrhs;
                    pos_l+=1;
                    pos_r+=1;
                },
                Ordering::Less => {
                    for _ in 0..l.num_elem() {
                        res.push(only_l(&clhs[0],em)?);
                        clhs = &clhs[1..];
                    }
                    pos_l+=1;
                },
                Ordering::Greater => {
                    for _ in 0..r.num_elem() {
                        res.push(only_r(&crhs[0],em)?);
                        crhs = &crhs[1..];
                    }
                    pos_r+=1;
                }
            }
        }
        Ok((clhs,crhs))
    }
}

impl<K : Ord + Clone + Hash,T : Composite + Clone> Composite for BTreeMap<K,T> {
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
    fn combine(&self,oth: &BTreeMap<K,T>) -> Option<BTreeMap<K,T>> {
        let mut res = (*self).clone();
        for (k,v) in oth.iter() {
            match res.entry(k.clone()) {
                Entry::Occupied(mut e) => match e.get().combine(v) {
                    None => return None,
                    Some(nv) => { e.insert(nv); }
                },
                Entry::Vacant(e) => { e.insert(v.clone()) ; }
            }
        }
        Some(res)
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,oth: &BTreeMap<K,T>,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let mut iter_l = self.iter();
        let mut iter_r = oth.iter();
        let mut cur_l : Option<(&K,&T)> = None;
        let mut cur_r : Option<(&K,&T)> = None;
        let mut clhs = lhs;
        let mut crhs = rhs;

        loop {
            let (key_l,el_l) = match cur_l {
                None => match iter_l.next() {
                    None => {
                        match cur_r {
                            None => {},
                            Some((_,el)) => for _ in 0..el.num_elem() {
                                res.push(only_r(&crhs[0],em)?);
                                crhs = &crhs[1..];
                            }
                        }
                        for (_,el) in iter_r {
                            for _ in 0..el.num_elem() {
                                res.push(only_r(&crhs[0],em)?);
                                crhs = &crhs[1..];
                            }
                        }
                        return Ok((clhs,crhs))
                    },
                    Some(el) => el
                },
                Some(el) => el
            };
            let (key_r,el_r) = match cur_r {
                None => match iter_r.next() {
                    None => {
                        for _ in 0..el_l.num_elem() {
                            res.push(only_l(&clhs[0],em)?);
                            clhs = &clhs[1..];
                        }
                        for (_,el) in iter_l {
                            for _ in 0..el.num_elem() {
                                res.push(only_l(&clhs[0],em)?);
                                clhs = &clhs[1..];
                            }
                        }
                        return Ok((clhs,crhs))
                    },
                    Some(el) => el
                },
                Some(el) => el
            };
            match key_l.cmp(key_r) {
                Ordering::Equal => {
                    let (nlhs,nrhs) = el_l.combine_elem(el_r,clhs,crhs,res,comb,only_l,only_r,em)?;
                    clhs = nlhs;
                    crhs = nrhs;
                    cur_l = None;
                    cur_r = None;
                },
                Ordering::Less => {
                    for _ in 0..el_l.num_elem() {
                        res.push(only_l(&clhs[0],em)?);
                        clhs = &clhs[1..];
                    }
                    cur_l = None;
                    cur_r = Some((key_r,el_r));
                },
                Ordering::Greater => {
                    for _ in 0..el_r.num_elem() {
                        res.push(only_r(&crhs[0],em)?);
                        crhs = &crhs[1..];
                    }
                    cur_l = Some((key_l,el_r));
                    cur_r = None;
                }
            }
        }
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

impl<T : Composite + Clone> Composite for Option<T> {
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
    fn combine(&self,oth: &Option<T>) -> Option<Option<T>> {
        match *self {
            None => Some((*oth).clone()),
            Some(ref c1) => match *oth {
                None => Some(Some(c1.clone())),
                Some(ref c2) => match c1.combine(&c2) {
                    None => None,
                    Some(r) => Some(Some(r))
                }
            }
        }
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,oth: &Option<T>,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        match *self {
            None => match *oth {
                None => Ok((lhs,rhs)),
                Some(ref el) => {
                    let mut clhs = lhs;
                    for _ in 0..el.num_elem() {
                        res.push(only_r(&clhs[0],em)?);
                        clhs = &clhs[1..];
                    }
                    Ok((clhs,rhs))
                }
            },
            Some(ref el1) => match *oth {
                None => {
                    let mut crhs = rhs;
                    for _ in 0..el1.num_elem() {
                        res.push(only_l(&rhs[0],em)?);
                        crhs = &crhs[1..];
                    }
                    Ok((lhs,crhs))
                },
                Some(ref el2) => el1.combine_elem(el2,lhs,rhs,res,comb,only_l,only_r,em)
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

#[derive(PartialEq,Eq,Hash)]
pub struct Array<Idx : Composite,T : Composite> {
    index: Idx,
    element: T
}

impl<Idx : Composite + Eq + Clone,T : Composite> Composite for Array<Idx,T> {
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
    fn combine(&self,oth: &Array<Idx,T>) -> Option<Array<Idx,T>> {
        if self.index!=oth.index {
            return None
        }
        match self.element.combine(&oth.element) {
            None => None,
            Some(nel) => Some(Array { index: self.index.clone(),
                                      element: nel })
        }
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,oth: &Array<Idx,T>,
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {
        self.element.combine_elem(&oth.element,lhs,rhs,res,comb,only_l,only_r,em)
    }
    // FIXME: Forall invariants
}

impl Composite for () {
    fn num_elem(&self) -> usize { 0 }
    fn elem_sort<Em : Embed>(&self,n: usize,_: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        panic!("Invalid index: {}",n)
    }
    fn combine(&self,_:&()) -> Option<()> {
        Some(())
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,_: &(),
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  _: &mut Vec<Em::Expr>,
                                                  _: &FComb,_: &FL,_: &FR,
                                                  _: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {
        Ok((lhs,rhs))
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
    fn combine(&self,oth: &(A,B)) -> Option<(A,B)> {
        match self.0.combine(&oth.0) {
            None => None,
            Some(n0) => match self.1.combine(&oth.1) {
                None => None,
                Some(n1) => Some((n0,n1))
            }
        }
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,oth: &(A,B),
                                                  lhs: &'a[Em::Expr],
                                                  rhs: &'b[Em::Expr],
                                                  res: &mut Vec<Em::Expr>,
                                                  comb: &FComb,only_l: &FL,only_r: &FR,
                                                  em: &mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {
        let (lhs1,rhs1) = self.0.combine_elem(&oth.0,lhs,rhs,res,comb,only_l,only_r,em)?;
        self.1.combine_elem(&oth.1,lhs1,rhs1,res,comb,only_l,only_r,em)
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut usize,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(usize,&mut Em) -> Result<Em::Expr,Em::Error> {

        self.0.invariant(em,f,off,res)?;
        self.1.invariant(em,f,off,res)
    }

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
}

impl<'a,T : 'a + Clone> OptRef<'a,T> {
    pub fn as_obj(self) -> T {
        match self {
            OptRef::Ref(x) => (*x).clone(),
            OptRef::Owned(x) => x
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
         Box<Fn(&[Em::Expr],&[Em::Expr],&mut Vec<Em::Expr>,&mut Em) -> Result<(),Em::Error>>,
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
    pub fn constant(els: Vec<Em::Expr>) -> Rc<Transformation<Em>> {
        Rc::new(Transformation::Constant(els))
    }
    pub fn view(off: usize,len: usize,t: Rc<Transformation<Em>>) -> Rc<Transformation<Em>> {
        if len==0 {
            Rc::new(Transformation::Id(0))
        } else if off==0 && t.size()==len {
            t
        } else {
            Rc::new(Transformation::View(off,len,t))
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
    pub fn size(&self) -> usize {
        match *self {
            Transformation::Id(sz) => sz,
            Transformation::View(_,nsz,_) => nsz,
            Transformation::Concat(sz,_) => sz,
            Transformation::Constant(ref vec) => vec.len(),
            Transformation::Map(sz,_,_,_) => sz,
            Transformation::Zip2(sz,_,_,_,_) => sz,
            Transformation::Write(sz,_,_,_,_) => sz,
            Transformation::MapByElem(_,ref tr) => tr.size()
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
            Transformation::Write(_,_,_,ref obj,ref trg) => {
                obj.clear_cache();
                trg.clear_cache();
            },
            Transformation::MapByElem(_,ref tr) => tr.clear_cache()
        }
    }
    fn as_slice<'a>(&'a self,arr: &'a [Em::Expr],off: usize,len: usize)
                    -> Option<BorrowedSlice<'a,Em::Expr>> {
        match *self {
            Transformation::Id(_) => Some(BorrowedSlice::BorrowedSlice(&arr[off..off+len])),
            Transformation::View(noff,_,ref tr) => tr.as_slice(arr,off+noff,len),
            Transformation::Concat(_,ref vec) => {
                let mut acc = 0;
                for el in vec.iter() {
                    let sz = el.size();
                    if off < acc+sz {
                        if sz<=len {
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
            Transformation::Map(_,_,_,ref cache) => {
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
        match self.as_slice(arr,off,len) {
            Some(res) => Ok(res),
            None => {
                let mut rvec = Vec::with_capacity(len);
                for i in 0..len {
                    rvec.push(self.get(arr,off+i,em)?);
                }
                Ok(BorrowedSlice::OwnedSlice(rvec))
            }
        }
    }
    pub fn get(&self,arr: &[Em::Expr],idx: usize,em: &mut Em) -> Result<Em::Expr,Em::Error> {
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
                let sl = tr.to_slice(arr,0,arr.len(),em)?;
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
                let sl1 = tr1.to_slice(arr,0,arr.len(),em)?;
                let sl2 = tr2.to_slice(arr,0,arr.len(),em)?;
                let mut narr = Vec::with_capacity(sz);
                f(sl1.get(),sl2.get(),&mut narr,em)?;
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
                => f(arr,idx,tr.get(arr,idx,em)?,em)
        }
    }
}

pub fn get_vec_elem<'a,T,Em>(pos: usize,vec: OptRef<'a,Vec<T>>,inp: Transf<Em>) -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error>
    where T : Composite + Clone, Em : Embed {
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

pub fn set_vec_elem<'a,T,Em>(pos: usize,
                             vec: OptRef<'a,Vec<T>>,
                             el: OptRef<'a,T>,
                             inp_vec: Transf<Em>,
                             inp_el: Transf<Em>) -> Result<(OptRef<'a,Vec<T>>,Transf<Em>),Em::Error>
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
    fn combine(&self,oth: &Data<T>) -> Option<Data<T>> {
        if self.0==oth.0 {
            Some(Data(self.0.clone()))
        } else {
            None
        }
    }
    fn combine_elem<'a,'b,Em : Embed,FComb,FL,FR>(&self,_:&Self,
                                                  lhs:&'a[Em::Expr],rhs:&'b[Em::Expr],
                                                  _:&mut Vec<Em::Expr>,
                                                  _:&FComb,_:&FL,_:&FR,_:&mut Em)
                                                  -> Result<(&'a[Em::Expr],&'b[Em::Expr]),Em::Error>
        where FComb : Fn(&Em::Expr,&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FL : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
              FR : Fn(&Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        Ok((lhs,rhs))
    }
}

pub trait Pool<T : Composite,Em : Embed> : Composite {
    type PoolIndex : Composite;
    fn empty<'a>(OptRef<'a,T>,Transf<Em>,&mut Em) -> Result<(OptRef<'a,Self>,Transf<Em>),Em::Error>;
    fn alloc<'a,F>(&F,OptRef<'a,T>,OptRef<'a,Self>,Transf<Em>,Transf<Em>)
                   -> Result<(OptRef<'a,Self::PoolIndex>,OptRef<'a,Self>,Transf<Em>,Transf<Em>),Em::Error>
        where F : Fn(&T,Transf<Em>) -> bool;
    fn index<'a>(OptRef<'a,Self::PoolIndex>,OptRef<'a,Self>,Transf<Em>,Transf<Em>)
                 -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error>;
}

impl<T : Composite + Clone,Em : Embed> Pool<T,Em> for Vec<T> {
    type PoolIndex = Data<usize>;
    fn empty<'a>(_:OptRef<'a,T>,_:Transf<Em>,_:&mut Em) -> Result<(OptRef<'a,Vec<T>>,Transf<Em>),Em::Error> {
        Ok((OptRef::Owned(Vec::new()),Transformation::constant(Vec::new())))
    }
    fn alloc<'a,F>(is_free:&F,el: OptRef<'a,T>,vec: OptRef<'a,Vec<T>>,inp_el: Transf<Em>,inp_vec: Transf<Em>)
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
    fn index<'a>(idx: OptRef<'a,Data<usize>>,vec: OptRef<'a,Vec<T>>,_:Transf<Em>,inp_vec: Transf<Em>)
                 -> Result<(OptRef<'a,T>,Transf<Em>),Em::Error> {
        get_vec_elem(idx.as_ref().0,vec,inp_vec)
    }
}
