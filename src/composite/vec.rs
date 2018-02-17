use composite::*;

use embed::{Embed,DeriveValues};
use types::{Value,SortKind};
use expr::Expr;
use std::cmp::{min,max};
use std::ops::Index;
use std::ops::Range;
use std::iter::Peekable;
use num_bigint::{BigInt,BigUint};
use num_traits::ToPrimitive;

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct CompVec<T>(Vec<(usize,T)>);

#[derive(Clone)]
pub struct CompVecP(pub usize);

pub struct VecAccess<P,It> {
    path:    P,
    it:      It,
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub struct VecMeaning<M> {
    pub index: usize,
    pub meaning: M,
}

pub struct Elements<P> {
    path: P,
    indices: Range<usize>
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
    fn combine<Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,arrl: &[Em::Expr],
        pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
        comb: &FComb,fl: &FL,fr: &FR,
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Self: 'a,
        Em: Embed,
        PL: Path<'a,Em,FromL,To=Self>,
        PR: Path<'a,Em,FromR,To=Self>,
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
            match T::combine(&pl.clone().then(Self::element(i)),froml,arrl,
                             &pr.clone().then(Self::element(i)),fromr,arrr,
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
                let path = pl.clone().then(Self::element(i));
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
                let path = pr.clone().then(Self::element(i));
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

pub type IndexedIter<Em: DeriveValues>
    = IndexIterator<IndexValue<Em::ValueIterator>,Em>;

pub type DynVecAccess<P,Em: DeriveValues>
    = VecAccess<P,IndexedIter<Em>>;

impl<T: HasSorts> CompVec<T> {
    pub fn new<Em: Embed>(_: &mut Vec<Em::Expr>,_: &mut Em)
                          -> Result<Self,Em::Error> {
        Ok(CompVec(Vec::new()))
    }
    pub fn singleton<Em,FEl>(el: FEl,res: &mut Vec<Em::Expr>,em: &mut Em)
                             -> Result<Self,Em::Error>
        where
        Em: Embed,
        FEl: FnOnce(&mut Vec<Em::Expr>,&mut Em) -> Result<T,Em::Error> {
        let rel = el(res,em)?;
        let sz = rel.num_elem();
        Ok(CompVec(vec![(sz,rel)]))
    }
    pub fn with_capacity<Em: Embed>(sz: usize,_: &mut Vec<Em::Expr>,_: &mut Em)
                                    -> Result<Self,Em::Error> {
        Ok(CompVec(Vec::with_capacity(sz)))
    }
    pub fn construct<Em: Embed,It: Iterator,F>(
        it: It,
        f: F,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error>
        where
        F: Fn(It::Item,&mut Vec<Em::Expr>,&mut Em) -> Result<T,Em::Error> {
        let mut vec = match it.size_hint().1 {
            None => Vec::new(),
            Some(sz) => Vec::with_capacity(sz)
        };
        let mut off = 0;
        for el in it {
            let rel = f(el,res,em)?;
            let sz = rel.num_elem();
            off+=sz;
            vec.push((off,rel));
        }
        Ok(CompVec(vec))
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
    pub fn element(idx: usize) -> CompVecP {
        CompVecP(idx)
    }
    pub fn elements<'a,From,P: SimplePath<'a,From,To=Self>>(
        path: P,
        from: &From) -> Elements<P>
        where T: 'a {
        let rng = match path.get(from).len() {
            0 => 1..0,
            n => 0..n-1
        };
        Elements { path: path,
                   indices: rng }
    }
    pub fn push<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &mut From,
        from_cont: &mut Vec<Em::Expr>,
        elem: T,
        cont: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error>
        where T: 'a {
        debug_assert_eq!(elem.num_elem(),cont.len());
        let old_len = {
            let vec = path.get_mut(from);
            let res = vec.num_elem();
            vec.0.push((res+cont.len(),elem));
            res
        };
        path.write_slice(from,old_len,0,cont,from_cont,em)
    }
    pub fn pop<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        from: &mut From,
        from_cont: &mut Vec<Em::Expr>,
        path: &P,
        em: &mut Em
    ) -> Result<(),Em::Error>
        where T: 'a {
        let old_len = {
            let vec = path.get_mut(from);
            let res = vec.num_elem();
            vec.0.pop();
            res
        };
        let mut cont = Vec::new();
        path.write_slice(from,old_len,0,&mut cont,from_cont,em)
    }
    pub fn insert<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        from: &mut From,
        from_cont: &mut Vec<Em::Expr>,
        path: &P,
        at: usize,
        elem: T,
        cont: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error>
        where T: 'a {
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
    pub fn access<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>,
                  It: CondIterator<Em,Item=usize>>(
        path: P,
        it: It
    ) -> VecAccess<P,It> where T: 'a {
        VecAccess { path: path,
                    it: it }
    }
    pub fn access_dyn_iter<'a,Em: DeriveValues,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        idx:  Em::Expr,
        em:   &mut Em
    ) -> Result<IndexedIter<Em>,Em::Error>
        where T: 'a {
        let len  = path.get(from).len();
        let vals = IndexValue::new(&idx,len,em)?;
        Ok(IndexIterator::new(idx,vals))
    }
    pub fn access_dyn<'a,Em: DeriveValues,From,P: Path<'a,Em,From,To=Self>>(
        path: P,
        from: &From,
        idx: Em::Expr,
        em: &mut Em
    ) -> Result<DynVecAccess<P,Em>,Em::Error>
        where T: 'a {
        let it = Self::access_dyn_iter(&path,from,idx,em)?;
        Ok(Self::access(path,it))
    }
    pub fn alloc<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>,F>(
        path:    &P,
        from:    &mut From,
        arr:     &mut Vec<Em::Expr>,
        el:      T,
        el_cont: &mut Vec<Em::Expr>,
        is_free: &F,
        em:      &mut Em
    ) -> Result<CompVecP,Em::Error>
        where T: 'a,
              F: Fn(&Then<P,CompVecP>,
                    &From,
                    &[Em::Expr],
                    &mut Em) -> Result<bool,Em::Error> {
        let size = path.get(from).0.len();
        for n in 0..size {
            if is_free(&path.clone().then(Self::element(n)),
                       from,&arr[..],em)? {
                Self::insert(from,arr,path,n,el,el_cont,em)?;
                return Ok(Self::element(n))
            }
        }
        Self::push(path,from,arr,el,el_cont,em)?;
        Ok(Self::element(size))
    }
}

impl<'a,T: 'a+HasSorts> SimplePathEl<'a,CompVec<T>> for CompVecP {
    type To = T;
    fn get<'b>(&self,arr: &'b CompVec<T>) -> &'b Self::To where 'a: 'b {
        &arr.0[self.0].1
    }
    fn get_mut<'b>(&self,arr: &'b mut CompVec<T>) -> &'b mut Self::To where 'a: 'b {
        &mut arr.0[self.0].1
    }
}

impl<'a,T: 'a+HasSorts,Em: Embed> PathEl<'a,Em,CompVec<T>> for CompVecP {
    fn read<From,Prev: Path<'a,Em,From,To=CompVec<T>>>(
        &self,
        prev: &Prev,
        from: &From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {

        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.read(from,off+pos,arr,em)
    }
    fn read_slice<'b,From,Prev: Path<'a,Em,From,To=CompVec<T>>>(
        &self,prev: &Prev,from: &From,pos: usize,len: usize,arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.read_slice(from,off+pos,len,arr)
    }
    fn write<From,Prev: Path<'a,Em,From,To=CompVec<T>>>(
        &self,prev: &Prev,from: &From,pos: usize,expr: Em::Expr,
        arr: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.write(from,off+pos,expr,arr,em)
    }
    fn write_slice<From,Prev: Path<'a,Em,From,To=CompVec<T>>>(
        &self,
        prev: &Prev,
        from: &mut From,
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

impl<'a,Em,P,It> CondIterator<Em> for VecAccess<P,It>
    where Em: Embed,
          P: Clone,
          It: CondIterator<Em,Item=usize> {
    type Item = Then<P,CompVecP>;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.it.next(conds,cond_pos,em)? {
            None => Ok(None),
            Some(idx) => {
                let npath = Then { first: self.path.clone(),
                                   then: CompVecP(idx) };
                Ok(Some(npath))
            }
        }
    }
}

impl<T: Semantic+HasSorts> Semantic for CompVec<T> {
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

pub enum IndexValue<It> {
    Limited(It),
    Unlimited(usize,Range<usize>)
}

impl<It> IndexValue<It> {
    pub fn new<Em: DeriveValues<ValueIterator=It>>(
        expr: &Em::Expr,
        max: usize,
        em: &mut Em)
        -> Result<Self,Em::Error>
    where It: Clone+Iterator<Item=Value> {
        match em.derive_values(&expr)? {
            None => {
                let tp = em.type_of(&expr)?;
                match em.is_bitvec(&tp)? {
                    None => panic!("Index value from non-bitvec expression"),
                    Some(bw) => {
                        let rng = if max==0 { 1..0 } else { 0..max-1 };
                        Ok(IndexValue::Unlimited(bw,rng))
                    }
                }
            },
            Some(it) => Ok(IndexValue::Limited(it))
        }
    }
}

impl<It: Iterator<Item=Value>> Iterator for IndexValue<It> {
    type Item = Value;
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut IndexValue::Limited(ref mut it) => it.next(),
            &mut IndexValue::Unlimited(bw,ref mut it) => match it.next() {
                None => None,
                Some(i) => Some(Value::BitVec(bw,BigUint::from(i)))
            }
        }
    }
}

pub struct IndexIterator<It: Iterator,Em: Embed> {
    expr: Em::Expr,
    first: bool,
    values: Peekable<It>
}

impl<It,Em> IndexIterator<It,Em>
    where It: Iterator<Item=Value>,
          Em: Embed {
    pub fn new(expr: Em::Expr,it: It) -> Self {
        IndexIterator { expr: expr,
                        first: true,
                        values: it.peekable() }
    }
}

impl<It,Em> CondIterator<Em> for IndexIterator<It,Em>
    where It: Iterator<Item=Value>,
          Em: Embed {
    type Item = usize;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        conds.truncate(cond_pos);
        match self.values.next() {
            None => Ok(None),
            Some(val) => {
                let idx = value_as_index(&val);
                if self.first {
                    self.first = false;
                    match self.values.peek() {
                        None => return Ok(Some(idx)),
                        Some(_) => {}
                    }
                }
                let val_expr = em.embed(Expr::Const(val))?;
                let cond = em.eq(self.expr.clone(),val_expr)?;
                conds.push(cond);
                Ok(Some(idx))
            }
        }
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
        SortKind::BitVec(bw) => Value::BitVec(bw,BigUint::from(idx)),
        _ => panic!("Cannot make value from index")
    }
}

impl<P: Clone> Iterator for Elements<P> {
    type Item = Then<P,CompVecP>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.indices.next() {
            None => None,
            Some(idx) => Some(Then { first: self.path.clone(),
                                     then: CompVecP(idx) })
        }
    }
}
