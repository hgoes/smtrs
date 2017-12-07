use composite::*;

use embed::{Embed};
use std::marker::PhantomData;
use std::cmp::{min,max};
use std::ops::Index;

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct CompVec<T>(Vec<(usize,T)>);

pub struct CompVecP<T>(usize,PhantomData<T>);

pub struct VecAccess<'a,T,P: 'a,It> {
    path:    &'a P,
    it:      It,
    phantom: PhantomData<T>
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub struct VecMeaning<M> {
    pub index: usize,
    pub meaning: M,
}

impl<T> Clone for CompVecP<T> {
    fn clone(&self) -> Self {
        CompVecP(self.0,PhantomData)
    }
}

impl<T: HasSorts> HasSorts for CompVec<T> {
    fn num_elem(&self) -> usize {
        match self.0.last() {
            None => 0,
            Some(&(len,_)) => len
        }
    }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        let mut idx = match self.0.binary_search_by(|&(ref off,_)| { off.cmp(&pos) }) {
            Ok(i) => i+1,
            Err(i) => i
        };
        while self.0[idx].1.num_elem()==0 {
            idx+=1;
        }
        let off = if idx==0 { 0 } else { self.0[idx-1].0 };
        self.0[idx].1.elem_sort(pos-off,em)
    }
}

impl<'a,T: Composite<'a>> Composite<'a> for CompVec<T> {
    fn combine<Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,arrl: &[Em::Expr],
        pr: &PR,fromr: &PR::From,arrr: &[Em::Expr],
        comb: &FComb,fl: &FL,fr: &FR,
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Em: Embed,
        PL: Path<'a,Em,To=Self>,
        PR: Path<'a,Em,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let vecl = pl.get(froml);
        let vecr = pr.get(fromr);

        let shared = min(vecl.0.len(),vecr.0.len());
        let res_len = max(vecl.0.len(),vecr.0.len());
        
        let mut rvec = Vec::with_capacity(res_len);
        let mut off = 0;
        
        for i in 0..shared {
            match T::combine(&pl.clone().then(CompVec::element(i)),froml,arrl,
                             &pr.clone().then(CompVec::element(i)),fromr,arrr,
                             comb,fl,fr,res,em)? {
                None => return Ok(None),
                Some(el) => {
                    off+=el.num_elem();
                    rvec.push((off,el));
                }
            }
        }
        if vecl.0.len() > vecr.0.len() {
            for i in vecr.0.len()..vecl.0.len() {
                let path = pl.clone().then(CompVec::element(i));
                let el = &vecl.0[i].1;
                let len = el.num_elem();
                off+=len;
                rvec.push((off,el.clone()));
                for j in 0..len {
                    let expr = path.read(froml,j,arrl,em)?;
                    res.push(fl(expr,em)?);
                }
            }
        } else if vecl.0.len() < vecr.0.len() {
            for i in vecl.0.len()..vecr.0.len() {
                let path = pr.clone().then(CompVec::element(i));
                let el = &vecr.0[i].1;
                let len = el.num_elem();
                off+=len;
                rvec.push((off,el.clone()));
                for j in 0..len {
                    let expr = path.read(fromr,j,arrr,em)?;
                    res.push(fr(expr,em)?);
                }
            }
        }
        Ok(Some(CompVec(rvec)))
    }
}

impl<T: HasSorts> CompVec<T> {
    pub fn new<Em: Embed>(_: &mut Vec<Em::Expr>,_: &mut Em)
                          -> Result<Self,Em::Error> {
        Ok(CompVec(Vec::new()))
    }
    pub fn len(&self) -> usize {
        self.0.len()
    }
    pub fn offset(&self,i: usize) -> usize {
        if i==0 {
            0
        } else {
            self.0[i-1].0
        }
    }
    pub fn element(idx: usize) -> CompVecP<T> {
        CompVecP(idx,PhantomData)
    }
    pub fn push<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        path: &P,
        from: &mut P::From,
        from_cont: &mut Vec<Em::Expr>,
        elem: T,
        cont: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        debug_assert_eq!(elem.num_elem(),cont.len());
        let old_len = {
            let vec = path.get_mut(from);
            let res = vec.num_elem();
            vec.0.push((res+cont.len(),elem));
            res
        };
        path.write_slice(from,old_len,0,cont,from_cont,em)
    }
    pub fn pop<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        from: &mut P::From,
        from_cont: &mut Vec<Em::Expr>,
        path: &P,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        let old_len = {
            let vec = path.get_mut(from);
            let res = vec.num_elem();
            vec.0.pop();
            res
        };
        let mut cont = Vec::new();
        path.write_slice(from,old_len,0,&mut cont,from_cont,em)
    }
    pub fn insert<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        from: &mut P::From,
        from_cont: &mut Vec<Em::Expr>,
        path: &P,
        at: usize,
        elem: T,
        cont: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        debug_assert_eq!(elem.num_elem(),cont.len());
        let off = {
            let vec = path.get_mut(from);
            let off = vec.offset(at);
            vec.0.insert(at,(off+cont.len(),elem));
            for n in at+1..vec.0.len() {
                vec.0[n].0+=cont.len();
            }
            off
        };
        path.write_slice(from,off,0,cont,from_cont,em)
    }
    pub fn access<'a,Em: Embed,P: Path<'a,Em,To=Self>,It: CondIterator<Em,Item=usize>>(
        path: &'a P,
        it: It
    ) -> VecAccess<'a,T,P,It> where T: 'a {
        VecAccess { path: path,
                    it: it,
                    phantom: PhantomData }
    }
    pub fn alloc<'a,Em: Embed,P: Path<'a,Em,To=Self>,F>(
        path:    &P,
        from:    &mut P::From,
        arr:     &mut Vec<Em::Expr>,
        el:      T,
        el_cont: &mut Vec<Em::Expr>,
        is_free: &F,
        em:      &mut Em
    ) -> Result<usize,Em::Error>
        where F: Fn(&Then<P,CompVecP<T>>,
                    &P::From,
                    &[Em::Expr],
                    &mut Em) -> Result<bool,Em::Error> {
        let size = path.get(from).0.len();
        for n in 0..size {
            if is_free(&path.clone().then(Self::element(n)),
                       from,&arr[..],em)? {
                Self::insert(from,arr,path,n,el,el_cont,em)?;
                return Ok(n)
            }
        }
        Self::push(path,from,arr,el,el_cont,em)?;
        Ok(size)
    }
}

impl<'a,T: 'a+HasSorts,Em: Embed> PathEl<'a,Em> for CompVecP<T> {
    type From = CompVec<T>;
    type To = T;
    fn get<'b>(&self,arr: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &arr.0[self.0].1
    }
    fn get_mut<'b>(&self,arr: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut arr.0[self.0].1
    }
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {

        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.read(from,off+pos,arr,em)
    }
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,len: usize,arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.read_slice(from,off+pos,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,expr: Em::Expr,
        arr: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.write(from,off+pos,expr,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &mut Prev::From,
        pos: usize,
        old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {

        let off = {
            let vec = prev.get_mut(from);
            if old_len<src.len() {
                let diff = src.len()-old_len;
                for i in self.0..vec.0.len() {
                    vec.0[i].0+=diff;
                }
            } else if old_len>src.len() {
                let diff = old_len-src.len();
                for i in self.0..vec.0.len() {
                    vec.0[i].0-=diff;
                }
            }
            vec.offset(self.0)
        };
        prev.write_slice(from,pos+off,old_len,src,trg,em)
    }
}

impl<'a,Em: Embed,T: 'a+HasSorts,P: 'a+Path<'a,Em,To=CompVec<T>>,
     It: CondIterator<Em,Item=usize>> CondIterator<Em> for VecAccess<'a,T,P,It> {
    type Item = Then<P,CompVecP<T>>;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.it.next(conds,cond_pos,em)? {
            None => Ok(None),
            Some(idx) => {
                let npath = self.path.clone().then(CompVec::element(idx));
                Ok(Some(npath))
            }
        }
    }
}

impl<T : Semantic+HasSorts> Semantic for CompVec<T> {
    type Meaning = VecMeaning<T::Meaning>;
    type MeaningCtx = T::MeaningCtx;
    fn meaning(&self,n: usize) -> Self::Meaning {
        let mut idx = match self.0.binary_search_by(|&(ref off,_)| { off.cmp(&n) }) {
            Ok(i) => i+1,
            Err(i) => i
        };
        while self.0[idx].1.num_elem()==0 {
            idx+=1;
        }
        let off = if idx==0 { 0 } else { self.0[idx-1].0 };
        VecMeaning { index: idx,
                     meaning: self.0[idx].1.meaning(n-off) }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        write!(fmt,"{}.",m.index)?;
        self.0[m.index].1.fmt_meaning(&m.meaning,fmt)
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        for (idx,&(_,ref el)) in self.0.iter().enumerate() {
            if let Some((ctx,m)) = el.first_meaning() {
                return Some((ctx,VecMeaning { index: idx,
                                              meaning: m }))
            }
        }
        None
    }
    fn next_meaning(&self,
                    ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        if self.0[m.index].1.next_meaning(ctx,&mut m.meaning) {
            return true
        }
        for idx in m.index+1..self.0.len() {
            if let Some((nctx,nm)) = self.0[idx].1.first_meaning() {
                *ctx = nctx;
                m.index = idx;
                m.meaning = nm;
                return true
            }
        }
        false
    }
}

impl<T> Index<usize> for CompVec<T> {
    type Output = T;
    fn index(&self,index: usize) -> &T {
        &self.0[index].1
    }
}
