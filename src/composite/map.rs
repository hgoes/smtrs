use composite::*;

use std::cmp::{Ordering,max};
use std::hash::Hasher;

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct Assoc<K,V>(Vec<(usize,K,V)>);

#[derive(Clone)]
pub struct AssocP(usize);

pub struct AssocMeaning<K,T : Semantic> {
    pub key: K,
    pub meaning: T::Meaning
}

impl<K: Ord,V: HasSorts> Assoc<K,V> {
    pub fn empty<Em: Embed>(_: &mut Vec<Em::Expr>,_: &mut Em) -> Result<Self,Em::Error> {
        Ok(Assoc(Vec::new()))
    }
    pub fn singleton<Em: Embed,
                     FEl: FnOnce(&mut Vec<Em::Expr>,&mut Em) -> Result<V,Em::Error>>(
        key: K,
        el: FEl,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error> {
        let rel = el(res,em)?;
        let sz = rel.num_elem();
        Ok(Assoc(vec![(sz,key,rel)]))
    }
    pub fn construct<Em,It,FEl>(
        it: It,
        sorted: bool,
        el: FEl,
        res: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<Self,Em::Error>
        where
        Em: Embed,
        It: Iterator,
        FEl: Fn(It::Item,&mut Vec<Em::Expr>,&mut Em)
                -> Result<(K,V),Em::Error> {
        let (low,up) = it.size_hint();
        let sz = match up {
            None => low,
            Some(rup) => rup
        };
        let mut vec = Vec::with_capacity(sz);
        if sorted {
            let mut pos = 0;
            for i in it {
                let (key,rel) = el(i,res,em)?;
                pos+=rel.num_elem();
                vec.push((pos,key,rel));
            }
            Ok(Assoc(vec))
        } else {
            let off = res.len();
            let path = Then { first: Id,
                              then: Offset::new(off) };
            let mut cassoc = Assoc(vec);
            let mut buf = Vec::new();
            for i in it {
                buf.clear();
                let (key,rel) = el(i,&mut buf,em)?;
                Self::insert(&path,&mut cassoc,res,
                             key,rel,&mut buf,em)?;
            }
            Ok(cassoc)
        }
    }
    pub fn offset(&self,i: usize) -> usize {
        if i==0 {
            0
        } else {
            self.0[i-1].0
        }
    }
    pub fn element(i: usize) -> AssocP {
        AssocP(i)
    }
    pub fn lookup<'a,From,P: SimplePath<'a,From,To=Self>>(
        path: P,
        from: &From,
        key: &K) -> Option<Then<P,AssocP>>
        where V: 'a,
              K: 'a {
        let assoc = path.get(from);
        match assoc.0.binary_search_by(|&(_,ref k,_)| key.cmp(k)) {
            Ok(idx) => Some(Then { first: path,
                                   then: AssocP(idx) }),
            Err(_) => None
        }
    }
    pub fn insert<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        assoc: &P,
        assoc_from: &mut From,
        assoc_cont: &mut Vec<Em::Expr>,
        key: K,
        el: V,
        el_cont: &mut Vec<Em::Expr>,
        em: &mut Em
    ) -> Result<AssocP,Em::Error>
        where V: 'a,
              K: 'a {
        match assoc.get(assoc_from).0.binary_search_by(|&(_,ref k,_)| k.cmp(&key)) {
            Ok(idx) => {
                let path = Then { first: assoc.clone(),
                                  then: AssocP(idx) };
                let old_len = {
                    let el_ref = path.get_mut(assoc_from);
                    let old_len = el_ref.num_elem();
                    *el_ref = el;
                    old_len
                };
                path.write_slice(assoc_from,0,old_len,el_cont,assoc_cont,em)?;
                Ok(Self::element(idx))
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
                assoc.write_slice(assoc_from,off,0,el_cont,assoc_cont,em)?;
                Ok(Self::element(idx))
            }
        }
    }
    pub fn insert_cond<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        assoc: P,
        assoc_from: &mut From,
        assoc_cont: &mut Vec<Em::Expr>,
        key: K,
        el: V,
        el_cont: &mut Vec<Em::Expr>,
        cond: &Em::Expr,
        em: &mut Em
    ) -> Result<AssocP,Em::Error>
        where V: 'a+Composite<'a>,
              K: 'a {
        match assoc.get(assoc_from).0.binary_search_by(|&(_,ref k,_)| k.cmp(&key)) {
            Ok(idx) => {
                let path = Then { first: assoc.clone(),
                                  then: AssocP(idx) };
                let mut res_cont = Vec::new();
                let res = ite(cond,
                              &path,assoc_from,&assoc_cont[..],
                              &Id::new(),&el,&el_cont[..],
                              &mut res_cont,em)?
                .expect("Cannot merge when inserting into Assoc");
                let old_len = {
                    let el_ref = path.get_mut(assoc_from);
                    let old_len = el_ref.num_elem();
                    *el_ref = res;
                    old_len
                };
                path.write_slice(assoc_from,0,old_len,&mut res_cont,assoc_cont,em)?;
                Ok(Self::element(idx))
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
                assoc.write_slice(assoc_from,off,0,el_cont,assoc_cont,em)?;
                Ok(Self::element(idx))
            }
        }
    }
    pub fn lookup_or_insert<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>,
                            F: FnOnce(&mut Vec<Em::Expr>,&mut Em) -> Result<V,Em::Error>
                            >(
        path: P,
        from: &mut From,
        arr:  &mut Vec<Em::Expr>,
        key: K,
        create: F,
        em: &mut Em
    ) -> Result<(bool,Then<P,AssocP>),Em::Error>
        where V: 'a,
              K: 'a {
        match path.get(from).0.binary_search_by(|&(_,ref k,_)| key.cmp(k)) {
            Ok(idx) => Ok((true,Then { first: path,
                                       then: AssocP(idx) })),
            Err(idx) => {
                let mut inp = Vec::new();
                let el = create(&mut inp,em)?;
                debug_assert_eq!(el.num_elem(),inp.len());
                let len = inp.len();
                let off = {
                    let assoc = path.get_mut(from);
                    let off = assoc.offset(idx);
                    assoc.0.insert(idx,(off+len,key,el));
                    for i in idx+1..assoc.0.len() {
                        assoc.0[i].0+=len;
                    }
                    off
                };
                path.write_slice(from,off,0,&mut inp,arr,em)?;
                Ok((false,Then { first: path,
                                 then: AssocP(idx) }))
            }
        }
    }
    pub fn is_single(&self) -> Option<&(usize,K,V)> {
        if self.0.len()==1 {
            Some(&self.0[0])
        } else {
            None
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

        let mut pos_l = 0;
        let mut pos_r = 0;
        let mut roff  = 0;
        let mut rvec  = Vec::with_capacity(max(vecl.0.len(),vecr.0.len()));

        loop {
            if pos_l >= vecl.0.len() {
                for i in pos_r..vecr.0.len() {
                    let path = Then { first: pr.clone(),
                                      then: AssocP(i) };
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
                    let path = Then { first: pl.clone(),
                                      then: AssocP(i) };
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
                    match V::combine(&Then { first: pl.clone(),
                                             then: AssocP(pos_l) },froml,arrl,
                                     &Then { first: pr.clone(),
                                             then: AssocP(pos_r) },fromr,arrr,
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
                    let path = Then { first: pl.clone(),
                                      then: AssocP(pos_l) };
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
                    let path = Then { first: pr.clone(),
                                      then: AssocP(pos_r) };
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

impl<'a,K: 'a+Ord,V: 'a+HasSorts> SimplePathEl<'a,Assoc<K,V>> for AssocP {
    type To = V;
    fn get<'b>(&self,assoc: &'b Assoc<K,V>) -> &'b Self::To where 'a: 'b {
        &assoc.0[self.0].2
    }
    fn get_mut<'b>(&self,assoc: &'b mut Assoc<K,V>) -> &'b mut Self::To where 'a: 'b {
        &mut assoc.0[self.0].2
    }
}

impl<'a,K: 'a+Ord,V: 'a+HasSorts,Em: Embed> PathEl<'a,Em,Assoc<K,V>> for AssocP {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Assoc<K,V>>>(
        &self,
        prev: &Prev,
        from: &PrevFrom,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {

        let assoc = prev.get(from);
        let off = assoc.offset(self.0);
        prev.read(from,off+pos,arr,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Assoc<K,V>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,len: usize,arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.read_slice(from,off+pos,len,arr)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Assoc<K,V>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,expr: Em::Expr,
        arr: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.write(from,off+pos,expr,arr,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Assoc<K,V>>>(
        &self,
        prev: &Prev,
        from: &mut PrevFrom,
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
