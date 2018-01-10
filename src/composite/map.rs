use composite::*;

use std::cmp::{Ordering,max};
use std::hash::Hasher;

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct Assoc<K,V>(Vec<(usize,K,V)>);

pub struct AssocP<K,V>(usize,PhantomData<(K,V)>);

pub struct AssocMeaning<K,T : Semantic> {
    pub key: K,
    pub meaning: T::Meaning
}

impl<K,V> Clone for AssocP<K,V> {
    fn clone(&self) -> Self {
        AssocP(self.0,PhantomData)
    }
}

impl<K: Ord,V: HasSorts> Assoc<K,V> {
    pub fn offset(&self,i: usize) -> usize {
        if i==0 {
            0
        } else {
            self.0[i-1].0
        }
    }
    pub fn element(i: usize) -> AssocP<K,V> {
        AssocP(i,PhantomData)
    }
    pub fn lookup<'a,Em: Embed,P: Path<'a,Em,To=Self>>(path: P,from: &P::From,key: &K)
                                                       -> Option<Then<P,AssocP<K,V>>> {
        let assoc = path.get(from);
        match assoc.0.binary_search_by(|&(_,ref k,_)| key.cmp(k)) {
            Ok(idx) => Some(Then { first: path,
                                   then: AssocP(idx,PhantomData) }),
            Err(_) => None
        }
    }
    pub fn insert<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        assoc: &P,
        assoc_from: &mut P::From,
        assoc_cont: &mut Vec<Em::Expr>,
        key: K,
        el: V,
        el_cont: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<(),Em::Error> {
        match assoc.get(assoc_from).0.binary_search_by(|&(_,ref k,_)| k.cmp(&key)) {
            Ok(idx) => {
                let path = assoc.clone().then(Assoc::element(idx));
                let old_len = {
                    let el_ref = path.get_mut(assoc_from);
                    let old_len = el_ref.num_elem();
                    *el_ref = el;
                    old_len
                };
                path.write_slice(assoc_from,0,old_len,el_cont,assoc_cont,em)
            },
            Err(idx) => {
                let off = {
                    let rassoc = assoc.get_mut(assoc_from);
                    let len = el_cont.len();
                    let off = rassoc.offset(idx);
                    rassoc.0.insert(idx,(off+len,key,el));
                    for i in idx+1..rassoc.0.len() {
                        rassoc.0[i].0+=len;
                    }
                    off
                };
                assoc.write_slice(assoc_from,off,0,el_cont,assoc_cont,em)
            }
        }
    }
}

impl<K: Ord+Hash,V: HasSorts> HasSorts for Assoc<K,V> {
    fn num_elem(&self) -> usize {
        match self.0.last() {
            None => 0,
            Some(&(len,_,_)) => len
        }
    }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        let mut idx = match self.0.binary_search_by(|&(ref off,_,_)| { off.cmp(&pos) }) {
            Ok(i) => i+1,
            Err(i) => i
        };
        while self.0[idx].2.num_elem()==0 {
            idx+=1;
        }
        let off = if idx==0 { 0 } else { self.0[idx-1].0 };
        self.0[idx].2.elem_sort(pos-off,em)
    }
}

impl<'a,K: Ord+Hash+Clone,V: Composite<'a>> Composite<'a> for Assoc<K,V> {
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

        let mut pos_l = 0;
        let mut pos_r = 0;
        let mut roff  = 0;
        let mut rvec  = Vec::with_capacity(max(vecl.0.len(),vecr.0.len()));

        loop {
            if pos_l >= vecl.0.len() {
                for i in pos_r..vecr.0.len() {
                    let path = pr.clone().then(Assoc::element(i));
                    let key  = &vecr.0[i].1;
                    let el   = &vecr.0[i].2;
                    let len  = el.num_elem();
                    roff+=len;
                    rvec.push((roff,key.clone(),el.clone()));
                    for j in 0..len {
                        let expr = path.read(fromr,j,arrr,em)?;
                        res.push(fr(expr,em)?);
                    }
                }
                break
            }
            if pos_r >= vecr.0.len() {
                for i in pos_l..vecl.0.len() {
                    let path = pl.clone().then(Assoc::element(i));
                    let key  = &vecl.0[i].1;
                    let el   = &vecl.0[i].2;
                    let len  = el.num_elem();
                    roff+=len;
                    rvec.push((roff,key.clone(),el.clone()));
                    for j in 0..len {
                        let expr = path.read(froml,j,arrl,em)?;
                        res.push(fl(expr,em)?);
                    }
                }
                break
            }
            let key_l = &vecl.0[pos_l].1;
            let key_r = &vecr.0[pos_r].1;
            match key_l.cmp(key_r) {
                Ordering::Equal => {
                    match V::combine(&pl.clone().then(Assoc::element(pos_l)),froml,arrl,
                                     &pr.clone().then(Assoc::element(pos_r)),fromr,arrr,
                                     comb,fl,fr,res,em)? {
                        None => return Ok(None),
                        Some(el) => {
                            roff+=el.num_elem();
                            rvec.push((roff,key_l.clone(),el));
                            pos_l+=1;
                            pos_r+=1;
                        }
                    }
                },
                Ordering::Less => {
                    let path = pl.clone().then(Assoc::element(pos_l));
                    let key  = &vecl.0[pos_l].1;
                    let el   = &vecl.0[pos_l].2;
                    let len  = el.num_elem();
                    roff+=len;
                    rvec.push((roff,key.clone(),el.clone()));
                    for j in 0..len {
                        let expr = path.read(froml,j,arrl,em)?;
                        res.push(fl(expr,em)?);
                    }
                    pos_l+=1;
                },
                Ordering::Greater => {
                    let path = pr.clone().then(Assoc::element(pos_r));
                    let key  = &vecr.0[pos_r].1;
                    let el   = &vecr.0[pos_r].2;
                    let len  = el.num_elem();
                    roff+=len;
                    rvec.push((roff,key.clone(),el.clone()));
                    for j in 0..len {
                        let expr = path.read(fromr,j,arrr,em)?;
                        res.push(fr(expr,em)?);
                    }
                    pos_r+=1;
                }
            }
        }
        Ok(Some(Assoc(rvec)))
    }
}

impl<'a,K: 'a+Ord,V: 'a+HasSorts> SimplePathEl<'a> for AssocP<K,V> {
    type From = Assoc<K,V>;
    type To   = V;
    fn get<'b>(&self,assoc: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &assoc.0[self.0].2
    }
    fn get_mut<'b>(&self,assoc: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut assoc.0[self.0].2
    }
}

impl<'a,K: 'a+Ord,V: 'a+HasSorts,Em: Embed> PathEl<'a,Em> for AssocP<K,V> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {

        let assoc = prev.get(from);
        let off = assoc.offset(self.0);
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

impl<K : PartialEq,T : Semantic> PartialEq for AssocMeaning<K,T> {
    fn eq(&self,other: &AssocMeaning<K,T>) -> bool {
        self.key==other.key &&
            self.meaning==other.meaning
    }
}

impl<K : Eq,T : Semantic> Eq for AssocMeaning<K,T> {}

impl<K : PartialOrd,T : Semantic> PartialOrd for AssocMeaning<K,T> {
    fn partial_cmp(&self,other: &AssocMeaning<K,T>) -> Option<Ordering> {
        match self.key.partial_cmp(&other.key) {
            None => None,
            Some(Ordering::Equal) => self.meaning.partial_cmp(&other.meaning),
            Some(r) => Some(r)
        }
    }
}

impl<K : Ord,T : Semantic> Ord for AssocMeaning<K,T> {
    fn cmp(&self,other: &AssocMeaning<K,T>) -> Ordering {
        match self.key.cmp(&other.key) {
            Ordering::Equal => self.meaning.cmp(&other.meaning),
            r => r
        }
    }
}

impl<K : Hash,T : Semantic> Hash for AssocMeaning<K,T> {
    fn hash<H>(&self, state: &mut H) where H: Hasher {
        self.key.hash(state);
        self.meaning.hash(state);
    }
}

impl<K : Debug,T : Semantic> Debug for AssocMeaning<K,T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        f.debug_struct("AssocMeaning")
            .field("key",&self.key)
            .field("meaning",&self.meaning)
            .finish()
    }
}

impl<K : Clone,T : Semantic> Clone for AssocMeaning<K,T> {
    fn clone(&self) -> Self {
        AssocMeaning { key: self.key.clone(),
                       meaning: self.meaning.clone() }
    }
}

impl<K : Ord+Hash+Debug+Clone,T : Semantic+HasSorts> Semantic for Assoc<K,T> {
    type Meaning = AssocMeaning<K,T>;
    type MeaningCtx = (usize,T::MeaningCtx);
    fn meaning(&self,n: usize) -> Self::Meaning {
        let mut idx = match self.0.binary_search_by(|&(ref off,_,_)| { off.cmp(&n) }) {
            Ok(i) => i+1,
            Err(i) => i
        };
        while self.0[idx].2.num_elem()==0 {
            idx+=1;
        }
        let key = self.0[idx].1.clone();
        let off = if idx==0 { 0 } else { self.0[idx-1].0 };
        
        AssocMeaning { key: key,
                       meaning: self.0[idx].2.meaning(n-off) }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        write!(fmt,"key({:?}).",m.key)?;
        for &(_,ref k,ref el) in self.0.iter() {
            if *k==m.key {
                return el.fmt_meaning(&m.meaning,fmt)
            }
        }
        panic!("Key {:?} not found in Assoc",m.key)
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        for (idx,&(_,ref k,ref el)) in self.0.iter().enumerate() {
            if let Some((ctx,m)) = el.first_meaning() {
                return Some(((idx,ctx),AssocMeaning { key: k.clone(),
                                                      meaning: m }))
            }
        }
        None
    }
    fn next_meaning(&self,
                    &mut (ref mut idx,ref mut ctx): &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        if self.0[*idx].2.next_meaning(ctx,&mut m.meaning) {
            return true
        }
        for ni in *idx+1..self.0.len() {
            if let Some((nctx,nm)) = self.0[ni].2.first_meaning() {
                *idx = ni;
                *ctx = nctx;
                m.key = self.0[ni].1.clone();
                m.meaning = nm;
                return true
            }
        }
        false
    }
}
