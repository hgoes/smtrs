use composite::*;
use composite::vec::*;
use types::{Value,SortKind};
use expr::Expr;
use embed::DeriveValues;

use std::iter::Peekable;
use num_bigint::{BigInt,BigUint};
use num_traits::ToPrimitive;
use std::ops::Range;

#[derive(Hash,Clone,PartialEq,Eq)]
pub struct BitVecVectorStack<T> {
    bitwidth: usize,
    elements: CompVec<T>
}

pub struct BitVecVectorStackElements<T>(PhantomData<T>);

pub enum IndexValue<It> {
    Limited(It),
    Unlimited(usize,Range<usize>)
}

pub struct IndexIterator<It: Iterator,Em: Embed> {
    expr: Em::Expr,
    first: bool,
    values: Peekable<It>
}

pub struct BitVecVectorStackIndex<P,T,It: Iterator,Em: Embed> {
    index: IndexIterator<It,Em>,
    path: P,
    phantom: PhantomData<T>
}

impl<T: Composite> BitVecVectorStack<T> {
    pub fn elements() -> BitVecVectorStackElements<T> {
        BitVecVectorStackElements(PhantomData)
    }
    fn top_iter<'a,Em: DeriveValues,P: Path<'a,Em,To=Self>>(
        path: &P,
        from: &P::From,
        arr:  &[Em::Expr],
        em:   &mut Em
    ) -> Result<IndexIterator<IndexValue<Em::ValueIterator>,Em>,Em::Error> {
        let top = path.read(from,0,arr,em)?;
        let it = match em.derive_values(&top)? {
            Some(vals) => IndexValue::Limited(vals),
            None => {
                let st = path.get(from);
                let n_elem = st.elements.len();
                let rng = if n_elem==0 {
                    1..0
                } else {
                    0..n_elem-1
                };
                IndexValue::Unlimited(st.bitwidth,rng)
            }
        };
        Ok(IndexIterator::new(top,it))
    }
    pub fn top<'a,Em: DeriveValues,P: Path<'a,Em,To=Self>>(
        path:  P,
        from:  &P::From,
        arr:   &[Em::Expr],
        em:    &mut Em
    ) -> Result<BitVecVectorStackIndex<P,T,IndexValue<Em::ValueIterator>,Em>,
                Em::Error> {
        let it = Self::top_iter(&path,from,arr,em)?;
        Ok(BitVecVectorStackIndex { index: it,
                                    path: path,
                                    phantom: PhantomData })
    }
    pub fn push<'a,Em: DeriveValues,P: Path<'a,Em,To=Self>>(
        path:  &P,
        from:  &mut P::From,
        arr:   &mut Vec<Em::Expr>,
        conds: &mut Vec<Em::Expr>,
        el:    &T,
        elc:   &Vec<Em::Expr>,
        em:    &mut Em
    ) -> Result<(),Em::Error> {
        let mut it = Self::top_iter(path,from,arr,em)?;
        let cond_pos = conds.len();
        let n_elem = path.get(from).elements.len();
        while let Some(idx) = it.next(conds,cond_pos,em)? {
            if n_elem > 0 && idx < n_elem-1 {
                let el_path = path.clone()
                    .then(BitVecVectorStack::elements())
                    .then(CompVec::element(idx+1));
                if conds.len()==0 {
                    let old_len = {
                        let el_ref = el_path.get_mut(from);
                        let old_len = el_ref.num_elem();
                        *el_ref = el.clone();
                        old_len
                    };
                    el_path.write_slice(from,0,old_len,&mut elc.clone(),arr,em)?;
                } else {
                    let cond = em.and(conds.clone())?;
                    let mut nelc = Vec::new();
                    let old_len = el_path.get(from).num_elem();
                    let nel = ite(&cond,
                                  &el_path,from,arr,
                                  &Id(PhantomData),el,&elc[..],
                                  &mut nelc,em)?.expect("Failed to merge");
                    *(el_path.get_mut(from)) = nel;
                    el_path.write_slice(from,0,old_len,&mut nelc,arr,em)?;
                }
            } else {
                CompVec::push(from,arr,
                              &path.clone().then(BitVecVectorStack::elements()),
                              el.clone(),
                              &mut elc.clone(),
                              em)?;
            }
        }
        conds.truncate(cond_pos);
        let bw      = path.get(from).bitwidth;
        let old_top = path.read(from,0,arr,em)?;
        let one     = em.const_bitvec(bw,BigUint::from(0u8))?;
        let add_top = em.bvadd(old_top.clone(),one)?;
        let new_top = if conds.len()==0 {
            add_top
        } else {
            let cond = em.and(conds.clone())?;
            em.ite(cond,add_top,old_top)?
        };
        path.write(from,0,new_top,arr,em)?;
        Ok(())
    }
    pub fn pop<'a,Em: DeriveValues,P: Path<'a,Em,To=Self>>(
        path:  &P,
        from:  &mut P::From,
        arr:   &mut Vec<Em::Expr>,
        conds: &mut Vec<Em::Expr>,
        em:    &mut Em
    ) -> Result<(),Em::Error> {
        let bw      = path.get(from).bitwidth;
        let old_top = path.read(from,0,arr,em)?;
        let one     = em.const_bitvec(bw,BigUint::from(0u8))?;
        let sub_top = em.bvsub(old_top.clone(),one)?;
        let new_top = if conds.len()==0 {
            CompVec::pop(from,arr,&path.clone()
                         .then(Self::elements()),em)?;
            sub_top
        } else {
            let cond = em.and(conds.clone())?;
            em.ite(cond,sub_top,old_top)?
        };
        path.write(from,0,new_top,arr,em)?;
        Ok(())
    }
}

impl<T> Clone for BitVecVectorStackElements<T> {
    fn clone(&self) -> Self {
        BitVecVectorStackElements(PhantomData)
    }
}

impl<T : HasSorts> HasSorts for BitVecVectorStack<T> {
    fn num_elem(&self) -> usize {
        self.elements.num_elem()+1
    }
    fn elem_sort<Em : Embed>(&self,pos: usize,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        if pos==0 {
            em.tp_bitvec(self.bitwidth)
        } else {
            self.elements.elem_sort(pos-1,em)
        }
    }
}

impl<'a,Em: Embed,T: 'a> PathEl<'a,Em> for BitVecVectorStackElements<T> {
    type From = BitVecVectorStack<T>;
    type To   = CompVec<T>;
    fn get<'b>(&self,from: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &from.elements
    }
    fn get_mut<'b>(&self,from: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut from.elements
    }
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,arr: &[Em::Expr],em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos+1,arr,em)
    }
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,len: usize,arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        match prev.read_slice(from,pos+1,len,arr) {
            None => None,
            Some(sl) => Some(sl)
        }
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,expr: Em::Expr,
        arr: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {

        prev.write(from,pos+1,expr,arr,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &mut Prev::From,
        pos: usize,old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {

        prev.write_slice(from,pos+1,old_len,src,trg,em)
    }

}

impl<T: Composite> Composite for BitVecVectorStack<T> {

    fn combine<'a,Em,PL,PR,FComb,FL,FR>(
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

        let bwl = pl.get(froml).bitwidth;
        let bwr = pr.get(fromr).bitwidth;

        if bwl!=bwr {
            return Ok(None)
        }
        
        let topl = pl.read(froml,0,arrl,em)?;
        let topr = pr.read(fromr,0,arrr,em)?;

        let ntop = comb(topl,topr,em)?;
        res.push(ntop);

        match CompVec::combine(&pl.clone().then(BitVecVectorStack::elements()),
                               froml,arrl,
                               &pr.clone().then(BitVecVectorStack::elements()),
                               fromr,arrr,
                               comb,fl,fr,
                               res,em)? {
            None => Ok(None),
            Some(nelem) => Ok(Some(BitVecVectorStack { bitwidth: bwl,
                                                       elements: nelem }))
        }
    }

    fn invariant<'a,Em,P>(path: &P,from: &P::From,arr: &[Em::Expr],
                          res: &mut Vec<Em::Expr>,
                          em: &mut Em)
                          -> Result<(),Em::Error>
        where Em: Embed,
              P: Path<'a,Em,To=Self> {
        CompVec::invariant(&path.clone().then(BitVecVectorStack::elements()),
                           from,arr,res,em)
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

impl<'a,Em,T,P,It> CondIterator<Em> for BitVecVectorStackIndex<P,T,It,Em>
    where Em: Embed,
          T: 'a+Composite,
          P: Path<'a,Em,To=BitVecVectorStack<T>>,
          It: Iterator<Item=Value> {
    type Item = Then<Then<P,BitVecVectorStackElements<T>>,
                     CompVecP<T>>;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.index.next(conds,cond_pos,em)? {
            None => Ok(None),
            Some(idx) => {
                let npath = self.path.clone()
                    .then(BitVecVectorStack::elements())
                    .then(CompVec::element(idx));
                Ok(Some(npath))
            }
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
