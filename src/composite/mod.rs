use embed::{Embed};
use std::hash::Hash;
use std::marker::PhantomData;
use std;
use std::fmt;
use std::fmt::Debug;

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

    fn combine<Em,PL,PR,FComb,FL,FR>(
        &PL,&PL::From,&[Em::Expr],
        &PR,&PR::From,&[Em::Expr],
        &FComb,&FL,&FR,
        &mut Vec<Em::Expr>,
        &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Em: Embed,
        PL: Path<'a,Em,To=Self>,
        PR: Path<'a,Em,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>;

    fn invariant<Em,P>(&P,&P::From,&[Em::Expr],
                       &mut Vec<Em::Expr>,
                       &mut Em)
                       -> Result<(),Em::Error>
        where Em: Embed,
              P: Path<'a,Em,To=Self> {
        Ok(())
    }
}

pub fn ite<'a,T,PL,PR,Em>(
    cond: &Em::Expr,
    pl: &PL,froml: &PL::From,arrl: &[Em::Expr],
    pr: &PR,fromr: &PR::From,arrr: &[Em::Expr],
    res: &mut Vec<Em::Expr>,
    em: &mut Em
) -> Result<Option<T>,Em::Error>
    where T: Composite<'a>,
          PL: Path<'a,Em,To=T>,
          PR: Path<'a,Em,To=T>,
          Em: Embed {
    T::combine(pl,froml,arrl,
               pr,fromr,arrr,
               &|x,y,em| em.ite(cond.clone(),x,y),
               &|x,_| Ok(x),
               &|y,_| Ok(y),
               res,em)
}

pub trait Path<'a,Em: Embed>: Sized+Clone {
    type From : 'a;
    type To : 'a;
    fn get<'b>(&self,&'b Self::From) -> &'b Self::To where 'a: 'b;
    fn get_mut<'b>(&self,&'b mut Self::From) -> &'b mut Self::To where 'a: 'b;
    fn read(&self,&Self::From,usize,&[Em::Expr],&mut Em)
            -> Result<Em::Expr,Em::Error>;
    fn read_slice<'b>(&self,&Self::From,usize,usize,&'b [Em::Expr])
                      -> Option<&'b [Em::Expr]>;
    fn read_into(&self,
                 from: &Self::From,
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
    fn write(&self,&Self::From,usize,Em::Expr,&mut Vec<Em::Expr>,&mut Em)
             -> Result<(),Em::Error>;
    fn write_slice(&self,&mut Self::From,usize,usize,&mut Vec<Em::Expr>,&mut Vec<Em::Expr>,&mut Em)
                   -> Result<(),Em::Error>;
    fn then<T: PathEl<'a,Em,From=Self::To>>(self,then: T) -> Then<Self,T> {
        Then { first: self,
               then: then }
    }
}

pub struct Id<T>(PhantomData<T>);

impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        Id(PhantomData)
    }
}

impl<T> Id<T> {
    pub fn new() -> Self {
        Id(PhantomData)
    }
}

impl<'a,T: 'a,Em: Embed> Path<'a,Em> for Id<T> {
    type From = T;
    type To = T;
    fn get<'b>(&self,from: &'b Self::From) -> &'b Self::To where 'a: 'b {
        from
    }
    fn get_mut<'b>(&self,from: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        from
    }
    fn read(&self,_: &Self::From,pos: usize,arr: &[Em::Expr],_: &mut Em)
            -> Result<Em::Expr,Em::Error> {
        Ok(arr[pos].clone())
    }
    fn read_slice<'b>(&self,_: &Self::From,pos: usize,len: usize,arr: &'b [Em::Expr])
                     -> Option<&'b [Em::Expr]> {
        Some(&arr[pos..pos+len])
    }
    fn write(&self,_: &Self::From,
             pos: usize,expr: Em::Expr,
             arr: &mut Vec<Em::Expr>,_: &mut Em)
             -> Result<(),Em::Error> {
        arr[pos] = expr;
        Ok(())
    }
    fn write_slice(&self,
                   _: &mut Self::From,
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

#[derive(Clone)]
pub struct Then<P1,P2> {
    first: P1,
    then: P2
}

impl<'a,Em: Embed,P1: Path<'a,Em>,P2: PathEl<'a,Em,From=P1::To>> Path<'a,Em> for Then<P1,P2> {
    type From = P1::From;
    type To = P2::To;
    fn get<'b>(&self,from: &'b Self::From) -> &'b Self::To where 'a: 'b {
        self.then.get(self.first.get(from))
    }
    fn get_mut<'b>(&self,from: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        self.then.get_mut(self.first.get_mut(from))
    }
    fn read(&self,from: &Self::From,pos: usize,arr: &[Em::Expr],em: &mut Em)
            -> Result<Em::Expr,Em::Error> {
        self.then.read(&self.first,from,pos,arr,em)
    }
    fn read_slice<'b>(&self,from: &Self::From,pos: usize,len: usize,arr: &'b [Em::Expr])
                     -> Option<&'b [Em::Expr]> {
        self.then.read_slice(&self.first,from,pos,len,arr)
    }
    fn write(&self,from: &Self::From,
             pos: usize,expr: Em::Expr,
             arr: &mut Vec<Em::Expr>,em: &mut Em)
             -> Result<(),Em::Error> {
        self.then.write(&self.first,from,pos,expr,arr,em)
    }
    fn write_slice(&self,
                   from: &mut Self::From,
                   pos: usize,
                   old_len: usize,
                   src: &mut Vec<Em::Expr>,
                   trg: &mut Vec<Em::Expr>,
                   em: &mut Em)
                   -> Result<(),Em::Error> {
        self.then.write_slice(&self.first,from,pos,old_len,src,trg,em)
    }
}

pub trait PathEl<'a,Em: Embed>: Sized+Clone {
    type From: 'a;
    type To: 'a;
    fn get<'b>(&self,&'b Self::From) -> &'b Self::To where 'a: 'b;
    fn get_mut<'b>(&self,&'b mut Self::From) -> &'b mut Self::To where 'a: 'b;
    fn read<Prev: Path<'a,Em,To=Self::From>>
        (&self,&Prev,&Prev::From,usize,&[Em::Expr],&mut Em)
         -> Result<Em::Expr,Em::Error>;
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,&Prev,&Prev::From,usize,usize,&'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        None
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>
        (&self,&Prev,&Prev::From,usize,Em::Expr,&mut Vec<Em::Expr>,&mut Em)
         -> Result<(),Em::Error>;
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,&Prev,&mut Prev::From,usize,usize,&mut Vec<Em::Expr>,&mut Vec<Em::Expr>,&mut Em)
        -> Result<(),Em::Error>;
    fn path(self) -> Then<Id<Self::From>,Self> {
        Then { first: Id(PhantomData),
               then: self }
    }
}

pub trait CondIterator<Em: Embed>: Sized {
    type Item;
    fn next(&mut self,&mut Vec<Em::Expr>,usize,&mut Em)
            -> Result<Option<Self::Item>,Em::Error>;
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
