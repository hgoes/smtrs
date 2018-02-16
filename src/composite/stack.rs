use composite::*;
use composite::vec::*;
use embed::DeriveValues;
use num_bigint::BigUint;

#[derive(Hash,Clone,PartialEq,Eq,Debug)]
pub struct BitVecVectorStack<T> {
    bitwidth: usize,
    elements: CompVec<T>
}

#[derive(Clone)]
pub struct BitVecVectorStackElements;

pub struct BitVecVectorStackAccess<P,It> {
    path: P,
    index: It
}

pub type DynBitVecVectorStackAccess<P,Em: DeriveValues>
    = BitVecVectorStackAccess<P,IndexedIter<Em>>;

impl<T: Composite> BitVecVectorStack<T> {
    pub fn empty<Em: Embed>(bw: usize,res: &mut Vec<Em::Expr>,em: &mut Em)
                            -> Result<Self,Em::Error> {
        let top = em.const_bitvec(bw,BigUint::from(0u8))?;
        res.push(top);
        let vec = CompVec::new(res,em)?;
        Ok(BitVecVectorStack { bitwidth: bw,
                               elements: vec })
    }
    pub fn singleton<Em,FEl>(bw: usize,el: FEl,res: &mut Vec<Em::Expr>,em: &mut Em)
                             -> Result<Self,Em::Error>
        where
        Em: Embed,
        FEl: FnOnce(&mut Vec<Em::Expr>,&mut Em) -> Result<T,Em::Error> {
        let top = em.const_bitvec(bw,BigUint::from(1u8))?;
        res.push(top);
        let vec = CompVec::singleton(el,res,em)?;
        Ok(BitVecVectorStack { bitwidth: bw,
                               elements: vec })
    }
    pub fn elements() -> BitVecVectorStackElements {
        BitVecVectorStackElements
    }
    fn top_iter<'a,Em: DeriveValues,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        arr:  &[Em::Expr],
        em:   &mut Em
    ) -> Result<IndexedIter<Em>,Em::Error>
        where T: 'a {
        let top = path.read(from,0,arr,em)?;
        let len = path.get(from).elements.len();
        let it = IndexValue::new(&top,len,em)?;
        Ok(IndexIterator::new(top,it))
    }
    pub fn top<'a,Em: DeriveValues,From,P: Path<'a,Em,From,To=Self>>(
        path:  P,
        from:  &From,
        arr:   &[Em::Expr],
        em:    &mut Em
    ) -> Result<DynBitVecVectorStackAccess<P,Em>,
                Em::Error>
        where T: 'a {
        let it = Self::top_iter(&path,from,arr,em)?;
        Ok(BitVecVectorStackAccess { path: path,
                                     index: it })
    }
    pub fn push<'a,Em: DeriveValues,From,P: Path<'a,Em,From,To=Self>>(
        path:  &P,
        from:  &mut From,
        arr:   &mut Vec<Em::Expr>,
        conds: &mut Vec<Em::Expr>,
        el:    &T,
        elc:   &Vec<Em::Expr>,
        em:    &mut Em
    ) -> Result<(),Em::Error>
        where T: 'a {
        let mut it = Self::top_iter(path,from,arr,em)?;
        let cond_pos = conds.len();
        let n_elem = path.get(from).elements.len();
        while let Some(idx) = it.next(conds,cond_pos,em)? {
            if n_elem > 0 && idx < n_elem-1 {
                let el_path = Then { first: Then { first: path.clone(),
                                                   then: BitVecVectorStackElements },
                                     then: CompVecP(idx+1) };
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
                                  &Id,el,&elc[..],
                                  &mut nelc,em)?.expect("Failed to merge");
                    *(el_path.get_mut(from)) = nel;
                    el_path.write_slice(from,0,old_len,&mut nelc,arr,em)?;
                }
            } else {
                CompVec::push(&Then { first: path.clone(),
                                      then: BitVecVectorStackElements },
                              from,arr,
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
    pub fn pop<'a,Em: DeriveValues,From,P: Path<'a,Em,From,To=Self>>(
        path:  &P,
        from:  &mut From,
        arr:   &mut Vec<Em::Expr>,
        conds: &mut Vec<Em::Expr>,
        em:    &mut Em
    ) -> Result<(),Em::Error>
        where T: 'a {
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

impl<'a,T: 'a> SimplePathEl<'a,BitVecVectorStack<T>> for BitVecVectorStackElements {
    type To   = CompVec<T>;
    fn get<'b>(&self,from: &'b BitVecVectorStack<T>)
               -> &'b Self::To where 'a: 'b {
        &from.elements
    }
    fn get_mut<'b>(&self,from: &'b mut BitVecVectorStack<T>)
                   -> &'b mut Self::To where 'a: 'b {
        &mut from.elements
    }
}

impl<'a,Em: Embed,T: 'a> PathEl<'a,Em,BitVecVectorStack<T>> for BitVecVectorStackElements {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitVecVectorStack<T>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,arr: &[Em::Expr],em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos+1,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitVecVectorStack<T>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,len: usize,arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        match prev.read_slice(from,pos+1,len,arr) {
            None => None,
            Some(sl) => Some(sl)
        }
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitVecVectorStack<T>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,expr: Em::Expr,
        arr: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {

        prev.write(from,pos+1,expr,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=BitVecVectorStack<T>>>(
        &self,prev: &Prev,from: &mut PrevFrom,
        pos: usize,old_len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error> {

        prev.write_slice(from,pos+1,old_len,src,trg,em)
    }
}

impl<T: Composite> Composite for BitVecVectorStack<T> {

    fn combine<'a,Em,FromL,PL,FromR,PR,FComb,FL,FR>(
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

        let bwl = pl.get(froml).bitwidth;
        let bwr = pr.get(fromr).bitwidth;

        if bwl!=bwr {
            return Ok(None)
        }
        
        let topl = pl.read(froml,0,arrl,em)?;
        let topr = pr.read(fromr,0,arrr,em)?;

        let ntop = comb(topl,topr,em)?;
        res.push(ntop);

        match CompVec::<T>::combine(
            &Then { first: pl.clone(),
                    then: BitVecVectorStackElements },
            froml,arrl,
            &Then { first: pr.clone(),
                    then: BitVecVectorStackElements },
            fromr,arrr,
            comb,fl,fr,
            res,em)? {
            None => Ok(None),
            Some(nelem) => Ok(Some(BitVecVectorStack { bitwidth: bwl,
                                                       elements: nelem }))
        }
    }

    fn invariant<'a,Em,From,P>(
        path: &P,from: &From,arr: &[Em::Expr],
        res: &mut Vec<Em::Expr>,
        em: &mut Em)
        -> Result<(),Em::Error>
        where Self: 'a,
              Em: Embed,
              P: Path<'a,Em,From,To=Self> {
        CompVec::<T>::invariant(
            &Then { first: path.clone(),
                    then: BitVecVectorStackElements },
            from,arr,res,em)
    }
}

impl<'a,Em,P,It> CondIterator<Em> for BitVecVectorStackAccess<P,It>
    where P: Clone,
          Em: Embed,
          It: CondIterator<Em,Item=usize> {
    type Item = Then<Then<P,BitVecVectorStackElements>,
                     CompVecP>;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        match self.index.next(conds,cond_pos,em)? {
            None => Ok(None),
            Some(idx) => {
                let npath = Then { first: Then { first: self.path.clone(),
                                                 then: BitVecVectorStackElements },
                                   then: CompVecP(idx) };
                Ok(Some(npath))
            }
        }
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub enum BitVecVectorStackMeaning<M> {
    Top,
    Elem(VecMeaning<M>)
}

impl<T> Semantic for BitVecVectorStack<T>
    where T : Semantic+HasSorts {
    type Meaning = BitVecVectorStackMeaning<T::Meaning>;
    type MeaningCtx = Option<T::MeaningCtx>;
    fn meaning(&self,n: usize) -> Self::Meaning {
        if n==0 {
            BitVecVectorStackMeaning::Top
        } else {
            BitVecVectorStackMeaning::Elem(self.elements.meaning(n-1))
        }
    }
    fn fmt_meaning<F: fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &BitVecVectorStackMeaning::Top => write!(fmt,"top"),
            &BitVecVectorStackMeaning::Elem(ref nm) => {
                self.elements.fmt_meaning(nm,fmt)
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        Some((None,BitVecVectorStackMeaning::Top))
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        match m {
            &mut BitVecVectorStackMeaning::Top => {
                if let Some((nctx,nm)) = self.elements.first_meaning() {
                    *ctx = Some(nctx);
                    *m   = BitVecVectorStackMeaning::Elem(nm);
                    true
                } else {
                    false
                }
            },
            &mut BitVecVectorStackMeaning::Elem(ref mut cm)
                => match ctx {
                    &mut Some(ref mut cctx) => self.elements.next_meaning(cctx,cm),
                    &mut None => unreachable!()
                }
        }
    }
}
