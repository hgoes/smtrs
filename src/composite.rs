use expr;
use types;
use types::{SortKind};
use embed::Embed;
use std::cmp::{Ordering,min,max};
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;
use std::marker::PhantomData;

pub trait Composite : Sized + 'static {
    
    fn num_elem(&self) -> u64;
    fn elem_sort<Em : Embed>(&self,u64,&mut Em)
                             -> Result<Em::Sort,Em::Error>;
    fn combine(&self,&Self) -> Option<Self>;

    fn combine_elem<FComb,FL,FR,Acc>(&self,&Self,&FComb,&FL,&FR,Acc,&mut u64,&mut u64,&mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc;

    fn invariant<Em : Embed,F>(&self,&mut Em,&F,&mut u64,&mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {
        Ok(())
    }
}

pub struct CompExpr<C : Composite> {
    pub expr: Box<expr::Expr<types::Sort,u64,CompExpr<C>,()>>,
    phantom: PhantomData<C>
}

pub fn view<'a,T : Composite,Em : Embed>(obj: &'a T) -> View<'a,T,Em> {
    View { offset: 0,
           comp: obj,
           indirection: Vec::new() }
}

pub struct View<'a,T : Composite + 'a,Em : Embed> {
    offset: u64,
    comp: &'a T,
    indirection: Vec<Indirection<Em>>
}

enum Indirection<Em: Embed> {
    ArraySelect(Em::Expr)
}

impl<Em : Embed> Indirection<Em> {
    fn apply(&self,em: &mut Em,e: Em::Expr) -> Result<Em::Expr,Em::Error> {
        match *self {
            Indirection::ArraySelect(ref idx) => em.select(e,vec![idx.clone()])
        }
    }
}

impl<Em : Embed> Clone for Indirection<Em> {
    fn clone(&self) -> Indirection<Em> {
        match *self {
            Indirection::ArraySelect(ref e)
                => Indirection::ArraySelect(e.clone())
        }
    }
}

pub struct Singleton(types::Sort);

impl Composite for Singleton {
    fn num_elem(&self) -> u64 { 1 }
    fn elem_sort<Em : Embed>(&self,_:u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,_: &Self,f: &FComb,_: &FL,_: &FR,acc: Acc,offl: &mut u64,offr: &mut u64,offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {
        let nacc = f(acc,*offl,*offr,*offn);
        *offl+=1;
        *offr+=1;
        *offn+=1;
        nacc
    }
}

impl<'a,Em : Embed> View<'a,Singleton,Em> {
    pub fn get<F>(&self,em: &mut Em,f: &F) -> Result<Em::Expr,Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {

        let mut e = f(self.offset,em)?;
        for indir in self.indirection.iter() {
            e = indir.apply(em,e)?;
        }
        Ok(e)
    }
}

pub struct SingletonBool {}

pub static BOOL_SINGLETON : SingletonBool = SingletonBool {};

impl Composite for SingletonBool {
    fn num_elem(&self) -> u64 { 1 }
    fn elem_sort<Em : Embed>(&self,_:u64,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        em.tp_bool()
    }
    fn combine(&self,_: &Self) -> Option<Self> {
        Some(SingletonBool {})
    }
    fn combine_elem<FComb,FL,FR,Acc>(&self,_: &Self,f: &FComb,_: &FL,_: &FR,acc: Acc,offl: &mut u64,offr: &mut u64,offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {
        let nacc = f(acc,*offl,*offr,*offn);
        *offl+=1;
        *offr+=1;
        *offn+=1;
        nacc
    }
}

impl<'a,Em : Embed> View<'a,SingletonBool,Em> {
    pub fn get<F>(&self,em: &mut Em,f: &F) -> Result<Em::Expr,Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {

        let mut e = f(self.offset,em)?;
        for indir in self.indirection.iter() {
            e = indir.apply(em,e)?;
        }
        Ok(e)
    }
}

impl<T : Composite + Clone> Composite for Vec<T> {
    fn num_elem(&self) -> u64 {
        let mut acc = 0;
        for el in self.iter() {
            acc+=el.num_elem()
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,n: u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,
                                     oth: &Vec<T>,
                                     comb: &FComb,
                                     onlyl: &FL,
                                     onlyr: &FR,
                                     acc: Acc,
                                     offl: &mut u64,
                                     offr: &mut u64,
                                     offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {

        let ssize = self.len();
        let osize = oth.len();
        let min_size = min(ssize,osize);
        let mut cacc = acc;
        
        for i in 0..min_size {
            cacc = self[i].combine_elem(&oth[i],comb,onlyl,onlyr,cacc,offl,offr,offn)
        }

        if ssize > osize {
            for i in osize..ssize {
                for _ in 0..self[i].num_elem() {
                    cacc = onlyl(cacc,*offl,*offn);
                    *offl += 1;
                    *offn += 1;
                }
            }
        } else if osize > ssize {
            for i in ssize..osize {
                for _ in 0..oth[i].num_elem() {
                    cacc = onlyl(cacc,*offl,*offn);
                    *offl += 1;
                    *offn += 1;
                }
            }
        }
        cacc
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut u64,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {

        for el in self.iter() {
            el.invariant(em,f,off,res)?;
        }
        Ok(())
    }
}

impl<'a,T : 'a + Composite + Clone,Em : Embed> View<'a,Vec<T>,Em> {
    pub fn get(self,n: usize) -> View<'a,T,Em> {
        let mut off = self.offset;
        for el in self.comp.iter().take(n) {
            off+=el.num_elem();
        }
        View { offset: off,
               comp: &self.comp[n],
               indirection: self.indirection }
    }
}

pub struct Choice<T>(Vec<T>);

impl<'a,T : 'a + Composite + Ord + Clone,Em : Embed> View<'a,Choice<T>,Em> {
    pub fn idx_of(&self,descr: &T) -> Option<usize> {
        for (n,el) in self.comp.0.iter().enumerate() {
            if *el==*descr {
                return Some(n)
            }
        }
        None
    }
    pub fn selector(self,n: usize) -> View<'a,SingletonBool,Em> {
        let mut off = self.offset;
        for el in self.comp.0.iter().take(n) {
            off+=el.num_elem()+1;
        }
        View { offset: off,
               comp: &BOOL_SINGLETON,
               indirection: self.indirection }
    }
    pub fn get(self,n: usize) -> View<'a,T,Em> {
        let mut off = self.offset;
        for el in self.comp.0.iter().take(n) {
            off+=el.num_elem()+1;
        }
        View { offset: off+1,
               comp: &self.comp.0[n],
               indirection: self.indirection }
    }
}

impl<T : Composite + Ord + Clone> Composite for Choice<T> {
    fn num_elem(&self) -> u64 {
        let mut acc = 0;
        for el in self.0.iter() {
            acc+=el.num_elem()+1
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,n: u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,
                                     oth: &Choice<T>,
                                     comb: &FComb,
                                     onlyl: &FL,
                                     onlyr: &FR,
                                     acc: Acc,
                                     offl: &mut u64,
                                     offr: &mut u64,
                                     offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {

        let mut offs = 0;
        let mut offo = 0;
        let mut cacc = acc;

        loop {
            if offs >= self.0.len() {
                for i in offo..oth.0.len() {
                    for _ in 0..oth.0[i].num_elem()+1 {
                        cacc = onlyr(cacc,*offr,*offn);
                        *offr+=1;
                        *offn+=1;
                    }
                }
                break;
            }
            if offo >= oth.0.len() {
                for i in offs..self.0.len() {
                    for _ in 0..self.0[i].num_elem()+1 {
                        cacc = onlyl(cacc,*offl,*offn);
                        *offl+=1;
                        *offn+=1;
                    }
                }
                break;
            }
            let ref l = self.0[offs];
            let ref r = oth.0[offo];
            match l.cmp(&r) {
                Ordering::Equal => {
                    cacc = comb(cacc,*offl,*offr,*offn);
                    *offl+=1;
                    *offr+=1;
                    *offn+=1;
                    cacc = l.combine_elem(&r,comb,onlyl,onlyr,cacc,offl,offr,offn);
                    offs+=1;
                    offo+=1;
                },
                Ordering::Less => {
                    for _ in 0..l.num_elem()+1 {
                        cacc = onlyl(cacc,*offl,*offn);
                        *offl+=1;
                        *offn+=1;
                    }
                    offs+=1;
                },
                Ordering::Greater => {
                    for _ in 0..r.num_elem()+1 {
                        cacc = onlyr(cacc,*offr,*offn);
                        *offr+=1;
                        *offn+=1;
                    }
                    offo+=1;
                }
            }
        }
        cacc
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut u64,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {

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

impl<K : Ord + Clone + 'static,T : Composite + Clone> Composite for BTreeMap<K,T> {
    fn num_elem(&self) -> u64 {
        let mut acc = 0;
        for v in self.values() {
            acc+=v.num_elem();
        }
        acc
    }
    fn elem_sort<Em : Embed>(&self,n: u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,oth: &BTreeMap<K,T>,
                                     comb: &FComb,onlyl: &FL,onlyr: &FR,
                                     acc: Acc,
                                     offl: &mut u64,offr: &mut u64,offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {

        let mut cacc = acc;
        let mut iter_l = self.iter();
        let mut iter_r = oth.iter();
        let mut cur_l = None;
        let mut cur_r : Option<(&K,&T)> = None;

        loop {
            let (key_l,el_l) = match cur_l {
                None => match iter_l.next() {
                    None => {
                        match cur_r {
                            None => {},
                            Some((_,el)) => for _ in 0..el.num_elem() {
                                cacc = onlyr(cacc,*offr,*offn);
                                *offr+=1;
                                *offn+=1;
                            }
                        }
                        for (_,el) in iter_r {
                            for _ in 0..el.num_elem() {
                                cacc = onlyr(cacc,*offr,*offn);
                                *offr+=1;
                                *offn+=1;
                            }
                        }
                        return cacc
                    },
                    Some(el) => el
                },
                Some(el) => el
            };
            let (key_r,el_r) = match cur_r {
                None => match iter_r.next() {
                    None => {
                        for _ in 0..el_l.num_elem() {
                            cacc = onlyl(cacc,*offl,*offn);
                            *offl+=1;
                            *offn+=1;
                        }
                        for (_,el) in iter_l {
                            for _ in 0..el.num_elem() {
                                cacc = onlyl(cacc,*offl,*offn);
                                *offl+=1;
                                *offn+=1;
                            }
                        }
                        return cacc
                    },
                    Some(el) => el
                },
                Some(el) => el
            };
            match key_l.cmp(key_r) {
                Ordering::Equal => {
                    cacc = el_l.combine_elem(el_r,comb,onlyl,onlyr,cacc,offl,offr,offn);
                    cur_l = None;
                    cur_r = None;
                },
                Ordering::Less => {
                    for _ in 0..el_l.num_elem() {
                        cacc = onlyl(cacc,*offl,*offn);
                        *offl+=1;
                        *offn+=1;
                    }
                    cur_l = None;
                    cur_r = Some((key_r,el_r));
                },
                Ordering::Greater => {
                    for _ in 0..el_r.num_elem() {
                        cacc = onlyr(cacc,*offr,*offn);
                        *offr+=1;
                        *offn+=1;
                    }
                    cur_l = Some((key_l,el_r));
                    cur_r = None;
                }
            }
        }
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut u64,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {

        for el in self.values() {
            el.invariant(em,f,off,res)?;
        }
        Ok(())
    }
}

impl<'a,T : Composite + Clone,Em : Embed> View<'a,Option<T>,Em> {
    pub fn get(self) -> Option<View<'a,T,Em>> {
        match *self.comp {
            None => None,
            Some(ref x) => Some(View { offset: self.offset,
                                       comp: x,
                                       indirection: self.indirection })
        }
    }
}

impl<T : Composite + Clone> Composite for Option<T> {
    fn num_elem(&self) -> u64 {
        match *self {
            None => 0,
            Some(ref c) => c.num_elem()
        }
    }
    fn elem_sort<Em : Embed>(&self,n: u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,oth: &Option<T>,
                                     comb: &FComb,onlyl: &FL,onlyr: &FR,
                                     acc: Acc,offl: &mut u64,offr: &mut u64,offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {

        match *self {
            None => match *oth {
                None => acc,
                Some(ref el) => {
                    let mut cacc = acc;
                    for _ in 0..el.num_elem() {
                        cacc = onlyr(cacc,*offr,*offn);
                        *offr+=1;
                        *offl+=1;
                    }
                    cacc
                }
            },
            Some(ref el1) => match *oth {
                None => {
                    let mut cacc = acc;
                    for _ in 0..el1.num_elem() {
                        cacc = onlyl(cacc,*offl,*offn);
                        *offl+=1;
                        *offr+=1;
                    }
                    cacc
                },
                Some(ref el2) => el1.combine_elem(el2,comb,onlyl,onlyr,acc,offl,offr,offn)
            }
        }
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut u64,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {
        match *self {
            None => Ok(()),
            Some(ref el) => el.invariant(em,f,off,res)
        }
    }
}

pub struct Array<Idx : Composite,T : Composite> {
    index: Idx,
    element: T
}

/*impl<'a,T : Composite,Em : Embed> View<'a,Array<T>,Em> {
    pub fn get(self,idx: Em::Expr) -> View<'a,T,Em> {
        let mut indir = self.indirection;
        indir.push(Indirection::ArraySelect(idx));
        View { offset: self.offset,
               comp: &self.comp.element,
               indirection: indir }
    }
}*/

impl<Idx : Composite + Eq + Clone,T : Composite> Composite for Array<Idx,T> {
    fn num_elem(&self) -> u64 {
        self.element.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,n: u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,oth: &Array<Idx,T>,
                                     comb: &FComb,onlyl: &FL,onlyr: &FR,
                                     acc: Acc,offl: &mut u64,offr: &mut u64,offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {
        self.element.combine_elem(&oth.element,comb,onlyl,onlyr,
                                  acc,offl,offr,offn)
    }
    // FIXME: Forall invariants
}

impl Composite for () {
    fn num_elem(&self) -> u64 { 0 }
    fn elem_sort<Em : Embed>(&self,n: u64,_: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        panic!("Invalid index: {}",n)
    }
    fn combine(&self,_:&()) -> Option<()> {
        Some(())
    }
    fn combine_elem<FComb,FL,FR,Acc>(&self,_:&(),_:&FComb,_:&FL,_:&FR,
                                     acc:Acc,_:&mut u64,_:&mut u64,_:&mut u64)
                                     -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {
        acc
    }
        
}

impl<A : Composite,B : Composite> Composite for (A,B) {
    fn num_elem(&self) -> u64 {
        self.0.num_elem() + self.1.num_elem()
    }
    fn elem_sort<Em : Embed>(&self,n: u64,em: &mut Em)
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
    fn combine_elem<FComb,FL,FR,Acc>(&self,oth: &(A,B),
                                     comb: &FComb,onlyl: &FL,onlyr: &FR,
                                     acc: Acc,offl: &mut u64,offr: &mut u64,offn: &mut u64) -> Acc
        where FComb : Fn(Acc,u64,u64,u64) -> Acc, FL : Fn(Acc,u64,u64) -> Acc, FR : Fn(Acc,u64,u64) -> Acc {
        let acc1 = self.0.combine_elem(&oth.0,comb,onlyl,onlyr,
                                       acc,offl,offr,offn);
        self.1.combine_elem(&oth.1,comb,onlyl,onlyr,
                            acc1,offl,offr,offn)
    }
    fn invariant<Em : Embed,F>(&self,em: &mut Em,f: &F,off: &mut u64,res: &mut Vec<Em::Expr>)
                               -> Result<(),Em::Error>
        where F : Fn(u64,&mut Em) -> Result<Em::Expr,Em::Error> {

        self.0.invariant(em,f,off,res)?;
        self.1.invariant(em,f,off,res)
    }

}

pub trait GetElem<Em : Embed> {
    fn get_elem(&self,u64,&mut Em) -> Result<Em::Expr,Em::Error>;
}

#[derive(Clone)]
pub struct OffsetGetter<Em : Embed,Get : GetElem<Em>> {
    getter: Get,
    offset: u64,
    phantom: PhantomData<Em>
}

impl<Em : Embed,Get : GetElem<Em>> GetElem<Em> for OffsetGetter<Em,Get> {
    fn get_elem(&self,n: u64,em: &mut Em) -> Result<Em::Expr,Em::Error> {
        self.getter.get_elem(n+self.offset,em)
    }
}

pub enum OptRef<'a,T : 'a> {
    Ref(&'a T),
    Owned(T)
}

impl<'a,T : 'a + Clone> OptRef<'a,T> {
    fn as_ref(&'a self) -> &'a T {
        match *self {
            OptRef::Ref(r) => r,
            OptRef::Owned(ref x) => x
        }
    }
    fn as_obj(self) -> T {
        match self {
            OptRef::Ref(x) => (*x).clone(),
            OptRef::Owned(x) => x
        }
    }
}

pub trait Transition<'a,Em : Embed,Input : GetElem<Em>,
                     Src : Composite,Trg : Composite> {
    type Output : GetElem<Em>;

    fn apply(&self,OptRef<'a,Src>,&Input,&mut Em)
             -> Result<(OptRef<'a,Trg>,Self::Output),Em::Error>;
}

pub struct Seq<'a,Em : 'a + Embed,
               Input : 'a + GetElem<Em>,
               A : Composite,B : Composite,C : Composite,
               T1 : Transition<'a,Em,Input,A,B>,
               T2 : Transition<'a,Em,T1::Output,B,C>> {
    t1: T1,
    t2: T2,
    phantom: PhantomData<&'a (Em,Input,A,B,C)>,
}

impl<'a,Em : Embed, Input : GetElem<Em>,
     A : Composite, B : Composite, C : Composite,
     T1 : Transition<'a,Em,Input,A,B>,
     T2 : Transition<'a,Em,T1::Output,B,C>
     > Transition<'a,Em,Input,A,C> for Seq<'a,Em,Input,A,B,C,T1,T2> {

    type Output = T2::Output;

    fn apply(&self,a: OptRef<'a,A>,get_a: &Input,em: &mut Em)
             -> Result<(OptRef<'a,C>,T2::Output),Em::Error> {
        let (b,get_b) = self.t1.apply(a,get_a,em)?;
        self.t2.apply(b,&get_b,em)
    }    
}

pub struct GetVecElem<Em : Embed, Input : GetElem<Em>, T : Composite> {
    which: usize,
    phantom: PhantomData<(Em,Input,T)>
}

impl<'a,Em : Embed, Input : GetElem<Em> + Clone, T : Composite + Clone
     > Transition<'a,Em,Input,Vec<T>,T> for GetVecElem<Em,Input,T> {
    type Output = OffsetGetter<Em,Input>;
    fn apply(&self,vec: OptRef<'a,Vec<T>>,inp: &Input,_: &mut Em) -> Result<(OptRef<'a,T>,OffsetGetter<Em,Input>),Em::Error> {
        match vec {
            OptRef::Ref(rvec) => {
                let mut off = 0;
                for el in rvec.iter().take(self.which) {
                    off+=el.num_elem();
                }
                Ok((OptRef::Ref(&rvec[self.which]),
                    OffsetGetter { getter: (*inp).clone(),
                                   offset: off,
                                   phantom: PhantomData }))
            },
            OptRef::Owned(mut rvec) => {
                let mut off = 0;
                for el in rvec.iter().take(self.which) {
                    off+=el.num_elem();
                }
                Ok((OptRef::Owned(rvec.remove(self.which)),
                    OffsetGetter { getter: (*inp).clone(),
                                   offset: off,
                                   phantom: PhantomData }))
            }
        }
    }
}

pub struct SetVecElem<Em : Embed, Input : GetElem<Em>, T : Composite> {
    which: usize,
    phantom: PhantomData<(Em,Input,T)>
}

pub struct SetVecElemGetter<Em : Embed,Get : GetElem<Em>> {
    getter: Get,
    offset_store: u64,
    offset_elem: u64,
    old_size: u64,
    new_size: u64,
    phantom: PhantomData<Em>
}

impl<Em : Embed,Get : GetElem<Em>> GetElem<Em> for SetVecElemGetter<Em,Get> {
    fn get_elem(&self,n: u64,em: &mut Em)
                -> Result<Em::Expr,Em::Error> {

        if n >= self.offset_store {
            if n >= self.offset_store + self.new_size {
                self.getter.get_elem(n-self.new_size+self.old_size,em)
            } else {
                self.getter.get_elem(self.offset_elem - self.offset_store + n,em)
            }
        } else {
            self.getter.get_elem(n,em)
        }
    }
}

impl<'a,Em : Embed, Input : GetElem<Em> + Clone, T : Composite + Clone
     > Transition<'a,Em,Input,(Vec<T>,T),Vec<T>> for SetVecElem<Em,Input,T> {
    type Output = SetVecElemGetter<Em,Input>;
    fn apply(&self,args: OptRef<'a,(Vec<T>,T)>,inp: &Input,_:&mut Em)
             -> Result<(OptRef<'a,Vec<T>>,SetVecElemGetter<Em,Input>),Em::Error> {
        match args {
            OptRef::Ref(&(ref vec,ref el)) => {
                let mut off_store = 0;
                for el in vec.iter().take(self.which) {
                    off_store+=el.num_elem();
                }
                let old = vec[self.which].num_elem();
                let new = el.num_elem();
                let mut rvec = vec.clone();
                rvec[self.which] = el.clone();
                Ok((OptRef::Owned(rvec),
                    SetVecElemGetter { getter: inp.clone(),
                                       offset_store: off_store,
                                       offset_elem: vec.num_elem(),
                                       old_size: old,
                                       new_size: new,
                                       phantom: PhantomData }))
            },
            OptRef::Owned((mut vec,el)) => {
                let mut off_store = 0;
                for el in vec.iter().take(self.which) {
                    off_store+=el.num_elem();
                }
                let off_elem = vec.num_elem();
                let old = vec[self.which].num_elem();
                let new = el.num_elem();
                vec[self.which] = el;
                Ok((OptRef::Owned(vec),
                    SetVecElemGetter { getter: inp.clone(),
                                       offset_store: off_store,
                                       offset_elem: off_elem,
                                       old_size: old,
                                       new_size: new,
                                       phantom: PhantomData }))
            }
        }
    }
}

struct GetArrayElem<Em : Embed, Input : GetElem<Em>, T : Composite> {
    phantom: PhantomData<(Em,Input,T)>
}

struct GetArrayElemGetter<Em : Embed,Get : GetElem<Em>,Idx : Composite> {
    getter: Get,
    index_sz: u64,
    offset_index: u64,
    phantom: PhantomData<(Em,Idx)>
}

impl<Em : Embed, Get : GetElem<Em>,Idx : Composite
     > GetElem<Em> for GetArrayElemGetter<Em,Get,Idx> {
    
    fn get_elem(&self,n: u64,em: &mut Em) -> Result<Em::Expr,Em::Error> {
        let mut idx_arr = Vec::with_capacity(self.index_sz as usize);
        for i in 0..self.index_sz {
            idx_arr.push(self.getter.get_elem(self.offset_index+i,em)?);
        }
        let arr = self.getter.get_elem(n,em)?;
        em.select(arr,idx_arr)
    }
}

impl<'a,Em : Embed, Input : GetElem<Em> + Clone,
     Idx : Composite + Eq + Clone, T : Composite
     > Transition<'a,Em,Input,(Array<Idx,T>,Idx),T> for GetArrayElem<Em,Input,T> {
    type Output = GetArrayElemGetter<Em,Input,Idx>;
    fn apply(&self,args: OptRef<'a,(Array<Idx,T>,Idx)>,inp: &Input,em:&mut Em)
             -> Result<(OptRef<'a,T>,GetArrayElemGetter<Em,Input,Idx>),Em::Error> {
        match args {
            OptRef::Owned((arr,idx)) => {
                assert!(arr.index==idx);
                let off_idx = arr.element.num_elem();
                Ok((OptRef::Owned(arr.element),
                    GetArrayElemGetter { getter: inp.clone(),
                                         index_sz: arr.index.num_elem(),
                                         offset_index: off_idx,
                                         phantom: PhantomData }))
            },
            OptRef::Ref(&(ref arr,ref idx)) => {
                assert!(arr.index==*idx);
                let off_idx = arr.element.num_elem();
                Ok((OptRef::Ref(&arr.element),
                    GetArrayElemGetter { getter: inp.clone(),
                                         index_sz: arr.index.num_elem(),
                                         offset_index: off_idx,
                                         phantom: PhantomData }))
            }
        }
        
    }
        
}

