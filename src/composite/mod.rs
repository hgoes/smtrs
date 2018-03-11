use embed::Embed;
use types::Sort;
use std::hash::Hash;
use std;
use std::fmt;
use std::fmt::Debug;

pub mod expr;
pub mod vec;
pub mod map;
pub mod choice;
pub mod singleton;
pub mod stack;
pub mod tuple;
pub mod option;

/// Objects with this traits can provide sorts for variables.
pub trait HasSorts {
    fn num_elem(&self) -> usize;
    fn elem_sort<Em: Embed>(&self,usize,&mut Em)
                            -> Result<Em::Sort,Em::Error>;
}

pub trait Composite<'a>: HasSorts + Sized + Eq + Hash + Clone {

    fn combine<Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        &PL,&FromL,&[Em::Expr],
        &PR,&FromR,&[Em::Expr],
        &FComb,&FL,&FR,
        &mut Vec<Em::Expr>,
        &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Self: 'a,
        Em: Embed,
        PL: Path<'a,Em,FromL,To=Self>,
        PR: Path<'a,Em,FromR,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>;

    fn combine_into<Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &mut FromL,arrl: &mut Vec<Em::Expr>,
        pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
        comb: &FComb,only_l: &FL,only_r: &FR,
        em: &mut Em)
        -> Result<bool,Em::Error>
        where
        Self: 'a,
        Em: Embed,
        PL: Path<'a,Em,FromL,To=Self>,
        PR: Path<'a,Em,FromR,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let old_len = pl.get(froml).num_elem();
        let mut res_arr = Vec::new();
        let res = Self::combine(pl,froml,&arrl[..],
                                pr,fromr,arrr,
                                comb,only_l,only_r,
                                &mut res_arr,em)?;
        match res {
            None => Ok(false),
            Some(r) => {
                pl.set(froml,arrl,r,&mut res_arr,em)?;
                Ok(true)
            }
        }
    }
    
    fn invariant<Em,From,P>(&P,&From,&[Em::Expr],
                            &mut Vec<Em::Expr>,
                            &mut Em)
                            -> Result<(),Em::Error>
        where Self: 'a,
              Em: Embed,
              P: Path<'a,Em,From,To=Self> {
        Ok(())
    }
}

pub fn ite<'a,FromL,PL,FromR,PR,Em>(
    cond: &Em::Expr,
    pl: &PL,froml: &FromL,arrl: &[Em::Expr],
    pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
    res: &mut Vec<Em::Expr>,
    em: &mut Em
) -> Result<Option<PL::To>,Em::Error>
    where PL: Path<'a,Em,FromL>,
          PR: Path<'a,Em,FromR,To=PL::To>,
          PL::To: Composite<'a>,
          Em: Embed {
    PL::To::combine(pl,froml,arrl,
                    pr,fromr,arrr,
                    &|x,y,em| em.ite(cond.clone(),x,y),
                    &|x,_| Ok(x),
                    &|y,_| Ok(y),
                    res,em)
}

pub fn comp_eq<'a,FromL,PL,FromR,PR,Em>(
    pl: &PL,froml: &FromL,arrl: &[Em::Expr],
    pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
    em: &mut Em
) -> Result<Option<Em::Expr>,Em::Error>
    where PL: Path<'a,Em,FromL>,
          PR: Path<'a,Em,FromR,To=PL::To>,
          PL::To: Composite<'a>,
          Em: Embed {
    let objl = pl.get(froml);
    let objr = pr.get(fromr);
    if *objl==*objr {
        let sz = objl.num_elem();
        if sz==0 {
            return Ok(Some(em.const_bool(true)?))
        }
        let mut conj = Vec::with_capacity(sz);
        for i in 0..sz {
            let el_l = pl.read(froml,i,arrl,em)?;
            let el_r = pr.read(fromr,i,arrr,em)?;
            let cmp = em.eq(el_l,el_r)?;
            conj.push(cmp);
        }
        Ok(Some(em.and(conj)?))
    } else {
        Ok(None)
    }
}

pub trait SimplePath<'a,From>: Sized {
    type To: 'a;
    fn get<'b>(&self,&'b From) -> &'b Self::To where 'a: 'b;
    fn get_mut<'b>(&self,&'b mut From) -> &'b mut Self::To where 'a: 'b;
    fn then<P>(self,then: P) -> Then<Self,P> {
        Then { first: self,
               then: then }
    }
}

pub fn then<X,Y>(first: X,then: Y) -> Then<X,Y> {
    Then { first: first,
           then: then }
}

pub trait Path<'a,Em: Embed,From>: SimplePath<'a,From>+Clone {
    fn read(&self,&From,usize,&[Em::Expr],&mut Em)
            -> Result<Em::Expr,Em::Error>;
    fn read_slice<'b>(&self,&From,usize,usize,&'b [Em::Expr])
                      -> Option<&'b [Em::Expr]>;
    fn read_into(&self,
                 from: &From,
                 pos: usize,
                 len: usize,
                 src: &[Em::Expr],
                 trg: &mut Vec<Em::Expr>,
                 em: &mut Em) -> Result<(),Em::Error> {
        match self.read_slice(from,pos,len,src) {
            Some(sl) => {
                trg.extend_from_slice(sl);
            },
            None => {
                for n in pos..pos+len {
                    let e = self.read(from,n,src,em)?;
                    trg.push(e);
                }
            }
        }
        Ok(())
    }
    fn write(&self,&From,usize,Em::Expr,&mut Vec<Em::Expr>,&mut Em)
             -> Result<(),Em::Error>;
    fn write_slice(&self,&mut From,usize,usize,&mut Vec<Em::Expr>,&mut Vec<Em::Expr>,&mut Em)
                   -> Result<(),Em::Error>;
    fn set(&self,
           from: &mut From,
           from_cont: &mut Vec<Em::Expr>,
           new: Self::To,
           new_cont: &mut Vec<Em::Expr>,
           em: &mut Em) -> Result<(),Em::Error>
        where Self::To: HasSorts {
        let old_len = self.get(from).num_elem();
        *self.get_mut(from) = new;
        self.write_slice(from,0,old_len,new_cont,from_cont,em)
    }
    fn set_cond(&self,
                from: &mut From,
                from_cont: &mut Vec<Em::Expr>,
                new: Self::To,
                new_cont: &mut Vec<Em::Expr>,
                cond: &Em::Expr,
                em: &mut Em) -> Result<bool,Em::Error>
        where Self::To: Composite<'a> {

        let mut res_inp = Vec::new();
        match ite(cond,self,from,&from_cont[..],
                  &Id,&new,&new_cont[..],
                  &mut res_inp,em)? {
            None => Ok(false),
            Some(res) => {
                let old_len = self.get(from).num_elem();
                *self.get_mut(from) = res;
                self.write_slice(from,0,old_len,&mut res_inp,from_cont,em)?;
                Ok(true)
            }
        }
    }
}

#[derive(Clone)]
pub struct Id;

impl Id {
    pub fn new() -> Self {
        Id
    }
}

impl<'a,T: 'a> SimplePath<'a,T> for Id {
    type To = T;
    fn get<'b>(&self,from: &'b T) -> &'b Self::To where 'a: 'b {
        from
    }
    fn get_mut<'b>(&self,from: &'b mut T) -> &'b mut Self::To where 'a: 'b {
        from
    }
}

impl<'a,T: 'a,Em: Embed> Path<'a,Em,T> for Id {
    fn read(&self,_: &T,pos: usize,arr: &[Em::Expr],_: &mut Em)
            -> Result<Em::Expr,Em::Error> {
        Ok(arr[pos].clone())
    }
    fn read_slice<'b>(&self,_: &T,pos: usize,len: usize,arr: &'b [Em::Expr])
                     -> Option<&'b [Em::Expr]> {
        Some(&arr[pos..pos+len])
    }
    fn write(&self,_: &T,
             pos: usize,expr: Em::Expr,
             arr: &mut Vec<Em::Expr>,_: &mut Em)
             -> Result<(),Em::Error> {
        arr[pos] = expr;
        Ok(())
    }
    fn write_slice(&self,
                   _: &mut T,
                   pos: usize,
                   old_len: usize,
                   src: &mut Vec<Em::Expr>,
                   trg: &mut Vec<Em::Expr>,
                   _: &mut Em)
                   -> Result<(),Em::Error> {
        if src.len()==old_len {
            for (n,el) in src.drain(..).enumerate() {
                trg[pos+n] = el;
            }
        } else if src.len()<old_len {
            for (n,el) in src.drain(..).enumerate() {
                trg[pos+n] = el;
            }
            trg.drain(pos+src.len()..pos+old_len);
        } else if pos==trg.len() {
            assert_eq!(old_len,0);
            trg.reserve(src.len());
            for el in src.drain(..) {
                trg.push(el);
            }
        } else {
            // Insert the replacement for the old element
            for (i,el) in src.drain(..old_len).enumerate() {
                trg[pos+i] = el;
            }
            let old = trg.len();
            let ins = src.len()-old_len;
            // Extend the size so that it can fit the new element
            trg.reserve_exact(ins);
            unsafe {
                trg.set_len(old+ins);
                let from = trg.as_mut_ptr().offset(pos as isize);
                let dst = from.offset(ins as isize);
                std::ptr::copy(dst,from,ins);
                for (n,el) in src.drain(..).enumerate() {
                    trg[pos+old_len+n] = el;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone,PartialEq,Eq)]
pub struct Then<P1,P2> {
    pub first: P1,
    pub then: P2
}

impl<'a,From,P1: SimplePath<'a,From>,P2: SimplePathEl<'a,P1::To>
     > SimplePath<'a,From> for Then<P1,P2> {
    type To = P2::To;
    fn get<'b>(&self,from: &'b From) -> &'b Self::To where 'a: 'b {
        self.then.get(self.first.get(from))
    }
    fn get_mut<'b>(&self,from: &'b mut From) -> &'b mut Self::To where 'a: 'b {
        self.then.get_mut(self.first.get_mut(from))
    }
}

impl<'a,Em: Embed,From,P1: Path<'a,Em,From>,P2: PathEl<'a,Em,P1::To>
     > Path<'a,Em,From> for Then<P1,P2> {
    fn read(&self,from: &From,pos: usize,arr: &[Em::Expr],em: &mut Em)
            -> Result<Em::Expr,Em::Error> {
        self.then.read(&self.first,from,pos,arr,em)
    }
    fn read_slice<'b>(&self,from: &From,pos: usize,len: usize,arr: &'b [Em::Expr])
                     -> Option<&'b [Em::Expr]> {
        self.then.read_slice(&self.first,from,pos,len,arr)
    }
    fn write(&self,from: &From,
             pos: usize,expr: Em::Expr,
             arr: &mut Vec<Em::Expr>,em: &mut Em)
             -> Result<(),Em::Error> {
        self.then.write(&self.first,from,pos,expr,arr,em)
    }
    fn write_slice(&self,
                   from: &mut From,
                   pos: usize,
                   old_len: usize,
                   src: &mut Vec<Em::Expr>,
                   trg: &mut Vec<Em::Expr>,
                   em: &mut Em)
                   -> Result<(),Em::Error> {
        self.then.write_slice(&self.first,from,pos,old_len,src,trg,em)
    }
}

pub trait SimplePathEl<'a,From> {
    type To: 'a;
    fn get<'b>(&self,&'b From) -> &'b Self::To where 'a: 'b;
    fn get_mut<'b>(&self,&'b mut From) -> &'b mut Self::To where 'a: 'b;
    fn path(self) -> Then<Id,Self>
        where Self: Sized {
        Then { first: Id,
               then: self }
    }
}

pub trait PathEl<'a,Em: Embed,From: 'a>: SimplePathEl<'a,From>+Clone {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=From>>
        (&self,&Prev,&PrevFrom,usize,&[Em::Expr],&mut Em)
         -> Result<Em::Expr,Em::Error>;
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=From>>(
        &self,&Prev,&PrevFrom,usize,usize,&'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        None
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=From>>
        (&self,&Prev,&PrevFrom,usize,Em::Expr,&mut Vec<Em::Expr>,&mut Em)
         -> Result<(),Em::Error>;
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=From>>(
        &self,&Prev,&mut PrevFrom,usize,usize,&mut Vec<Em::Expr>,&mut Vec<Em::Expr>,&mut Em)
        -> Result<(),Em::Error>;
}

pub trait CondIterator<Em: Embed>: Sized {
     type Item;
    fn next(&mut self,&mut Vec<Em::Expr>,usize,&mut Em)
            -> Result<Option<Self::Item>,Em::Error>;
    fn then<I,F: FnMut(Self::Item,&mut Em) -> Result<I,Em::Error>>(
        self,f: F
    ) -> ThenIter<Self,I,F> {
        ThenIter {
            f: f,
            it1: self,
            it2: None
        }
    }
}

pub struct ThenIter<It1,It2,F> {
    f:   F,
    it1: It1,
    it2: Option<(It2,usize)>
}

impl<Em: Embed,It1: CondIterator<Em>,It2: CondIterator<Em>,F> CondIterator<Em> for ThenIter<It1,It2,F>
    where F: FnMut(It1::Item,&mut Em) -> Result<It2,Em::Error> {
    type Item = It2::Item;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        loop {
            if let Some((ref mut it2,ref mut cond_pos2)) = self.it2 {
                if let Some(res) = it2.next(conds,*cond_pos2,em)? {
                    return Ok(Some(res))
                }
            }
            match self.it1.next(conds,cond_pos,em)? {
                None => return Ok(None),
                Some(el) => self.it2 = Some(((self.f)(el,em)?,conds.len()))
            }
        }
    }
}

pub trait Semantic {
    type Meaning : Ord+Hash+Debug+Clone;
    type MeaningCtx;
    fn meaning(&self,usize) -> Self::Meaning;
    fn fmt_meaning<F : fmt::Write>(&self,&Self::Meaning,&mut F) -> Result<(),fmt::Error>;
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)>;
    fn next_meaning(&self,&mut Self::MeaningCtx,&mut Self::Meaning) -> bool;
}

pub struct Semantics<'a,T : 'a+Semantic> {
    obj: &'a T,
    meaning: Option<(T::MeaningCtx,T::Meaning)>
}

impl<'a,T : Semantic> Semantics<'a,T> {
    pub fn new(obj: &'a T) -> Self {
        Semantics { obj: obj,
                    meaning: None }
    }
    pub fn next_ref<'b>(&'b mut self) -> Option<&'b T::Meaning> {
        self.meaning = match self.meaning {
            None => match self.obj.first_meaning() {
                None => return None,
                Some(r) => Some(r)
            },
            Some((ref mut ctx,ref mut m)) => if self.obj.next_meaning(ctx,m) {
                return Some(m)
            } else {
                return None
            }
        };
        match self.meaning {
            Some((_,ref m)) => Some(m),
            None => unreachable!()
        }
    }
}

impl<'a,T : Semantic> Iterator for Semantics<'a,T> {
    type Item = T::Meaning;
    fn next(&mut self) -> Option<Self::Item> {
        self.meaning = match self.meaning {
            None => match self.obj.first_meaning() {
                None => return None,
                Some(r) => Some(r)
            },
            Some((ref mut ctx,ref mut m)) => if self.obj.next_meaning(ctx,m) {
                return Some(m.clone())
            } else {
                return None
            }
        };
        match self.meaning {
            Some((_,ref m)) => Some(m.clone()),
            None => unreachable!()
        }
    }
}

pub struct MeaningOf<'a,T : 'a+Semantic> {
    obj: &'a T,
    meaning: &'a T::Meaning
}

impl<'a,T : Semantic> MeaningOf<'a,T> {
    pub fn new(obj: &'a T,m: &'a T::Meaning) -> Self {
        MeaningOf { obj: obj,
                    meaning: m }
    }
}

impl<'a,T : Semantic> fmt::Display for MeaningOf<'a,T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        self.obj.fmt_meaning(self.meaning,f)
    }
}

/// Helper path to implement offset calculations.
#[derive(Clone)]
pub struct Offset(usize);

impl Offset {
    pub fn new(off: usize) -> Self {
        Offset(off)
    }
}

impl<'a,T: 'a> SimplePathEl<'a,T> for Offset {
    type To = T;
    fn get<'b>(&self,from: &'b T) -> &'b Self::To where 'a: 'b {
        from
    }
    fn get_mut<'b>(&self,from: &'b mut T) -> &'b mut Self::To
        where 'a: 'b {
        from
    }
}

impl<'a,T: 'a,Em: Embed> PathEl<'a,Em,T> for Offset {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=T>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos+self.0,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=T>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        len: usize,
        arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos+self.0,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=T>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos:  usize,
        expr: Em::Expr,
        arr:  &mut Vec<Em::Expr>,
        em:   &mut Em) -> Result<(),Em::Error> {
        prev.write(from,pos,expr,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=T>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
        pos: usize,
        len: usize,
        src: &mut Vec<Em::Expr>,
        trg: &mut Vec<Em::Expr>,
        em: &mut Em) -> Result<(),Em::Error> {
        prev.write_slice(from,pos+self.0,len,src,trg,em)
    }
}

impl<'a,C: HasSorts> HasSorts for &'a C {
    fn num_elem(&self) -> usize {
        (*self).num_elem()
    }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        (*self).elem_sort(pos,em)
    }
}

impl HasSorts for Vec<Sort> {
    fn num_elem(&self) -> usize {
        self.len()
    }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        self[pos].embed(em)
    }
}
