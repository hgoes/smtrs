use composite::*;

use std::cmp::{Ordering,max};

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct Choice<T>(Vec<(usize,T)>);

pub struct ChoiceEl<T>(usize,PhantomData<T>);

pub struct Choices<'a,Em: Embed,T: 'a,P: 'a+Path<'a,Em,To=Choice<T>>> where Em::Expr: 'a {
    path: &'a P,
    from: &'a P::From,
    choice: &'a Choice<T>,
    pos: usize,
    arr: &'a [Em::Expr]
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub enum ChoiceMeaning<M> {
    Selector(usize),
    Item(usize,M)
}

impl<T> Clone for ChoiceEl<T> {
    fn clone(&self) -> Self {
        ChoiceEl(self.0,PhantomData)
    }
}

impl<T: Ord+HasSorts> Choice<T> {
    pub fn empty<Em: Embed>(_: &mut Vec<Em::Expr>,
                            _: &mut Em)
                            -> Result<Self,Em::Error> {
        Ok(Choice(Vec::new()))
    }
    pub fn singleton<Em: Embed>(el: T,
                                el_cont: &[Em::Expr],
                                res: &mut Vec<Em::Expr>,
                                em: &mut Em)
                                -> Result<Self,Em::Error> {
        let cond = em.const_bool(true)?;
        res.reserve(1+el_cont.len());
        res.push(cond);
        res.extend_from_slice(el_cont);
        let mut els = Vec::with_capacity(1);
        els.push((el.num_elem(),el));
        Ok(Choice(els))
    }
    pub fn offset(&self,i: usize) -> usize {
        if i==0 {
            0
        } else {
            self.0[i-1].0
        }
    }
    pub fn element(i: usize) -> ChoiceEl<T> {
        ChoiceEl(i,PhantomData)
    }
    pub fn is_selected<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        path: &Then<P,ChoiceEl<T>>,
        from: &P::From,
        cont: &[Em::Expr],
        em: &mut Em) -> Result<Em::Expr,Em::Error> {

        let ch = path.first.get(from);
        let off = ch.offset(path.then.0);
        path.first.read(from,off,cont,em)
    }
    pub fn choices<'a,Em: Embed,P: Path<'a,Em,To=Self>>(
        path: &'a P,
        from: &'a P::From,
        arr:  &'a [Em::Expr]
    ) -> Choices<'a,Em,T,P> {
        Choices { path: path,
                  from: from,
                  choice: path.get(from),
                  pos: 0,
                  arr: arr }
    }
    pub fn sym_eq<'a,Em: Embed,
                  P1: Path<'a,Em,To=Self>,
                  P2: Path<'a,Em,To=Self>>(
        pl: &P1,
        froml: &P1::From,
        arrl: &[Em::Expr],
        pr: &P2,
        fromr: &P2::From,
        arrr: &[Em::Expr],
        em: &mut Em
    ) -> Result<Option<Em::Expr>,Em::Error> {
        let lhs = pl.get(froml);
        let rhs = pr.get(fromr);
        let mut lpos = 0;
        let mut rpos = 0;
        let mut loff = 0;
        let mut roff = 0;
        let mut disj = Vec::new();

        while lpos<lhs.0.len() && rpos<rhs.0.len() {
            let (nloff,ref lobj) = lhs.0[lpos];
            let (nroff,ref robj) = rhs.0[rpos];
            match lobj.cmp(robj) {
                Ordering::Equal => {
                    let lcond = pl.read(froml,loff,arrl,em)?;
                    let rcond = pr.read(fromr,roff,arrr,em)?;
                    let sz = lobj.num_elem();
                    let mut conj = Vec::with_capacity(sz+2);
                    conj.push(lcond);
                    conj.push(rcond);
                    for i in 0..sz {
                        let l = pl.read(froml,loff+1+i,arrl,em)?;
                        let r = pr.read(fromr,roff+1+i,arrr,em)?;
                        let eq = em.eq(l,r)?;
                        conj.push(eq);
                    }
                    let all = em.and(conj)?;
                    disj.push(all);
                    lpos+=1;
                    rpos+=1;
                },
                Ordering::Less => {
                    lpos+=1;
                },
                Ordering::Greater => {
                    rpos+=1;
                }
            }
            loff = nloff;
            roff = nroff;
        }
        if disj.len()==0 {
            Ok(None)
        } else {
            let res = em.or(disj)?;
            Ok(Some(res))
        }
    }
    pub fn compare_using<'a,Em: Embed,
                         P1: Path<'a,Em,To=Self>,
                         P2: Path<'a,Em,To=Self>,
                         Cmp>(
        pl: &P1,
        froml: &P1::From,
        arrl: &[Em::Expr],
        pr: &P2,
        fromr: &P2::From,
        arrr: &[Em::Expr],
        cmp: Cmp,
        em: &mut Em
    ) -> Result<Option<Em::Expr>,Em::Error>
        where Cmp: Fn(&Then<P1,ChoiceEl<T>>,&P1::From,&[Em::Expr],
                      &Then<P2,ChoiceEl<T>>,&P2::From,&[Em::Expr],
                      &mut Em) -> Result<Option<Em::Expr>,Em::Error> {

        let lhs = pl.get(froml);
        let rhs = pr.get(fromr);
        let mut disj = Vec::new();

        for lpos in 0..lhs.0.len() {
            let lpath = pl.clone().then(Choice::element(lpos));
            let loff = lhs.offset(lpos);

            for rpos in 0..rhs.0.len() {
                let rpath = pr.clone().then(Choice::element(rpos));
                let roff = rhs.offset(rpos);

                if let Some(cond) = cmp(&lpath,froml,arrl,
                                        &rpath,fromr,arrr,
                                        em)? {

                    let lcond = pl.read(froml,loff,arrl,em)?;
                    let rcond = pr.read(fromr,roff,arrr,em)?;
                    let conj = em.and(vec![lcond,rcond,cond])?;
                    disj.push(conj);
                }
            }
        }
        if disj.len()==0 {
            Ok(None)
        } else {
            let res = em.or(disj)?;
            Ok(Some(res))
        }
    }
}

impl<T: HasSorts> HasSorts for Choice<T> {
    fn num_elem(&self) -> usize {
        match self.0.last() {
            None => 0,
            Some(&(len,_)) => len
        }
    }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        let idx = match self.0.binary_search_by(|&(ref off,_)| { off.cmp(&pos) }) {
            Ok(i) => i+1,
            Err(i) => i
        };
        let off = if idx==0 { 0 } else { self.0[idx-1].0 };
        match pos-off {
            0 => em.tp_bool(),
            n => self.0[idx].1.elem_sort(n-1,em)
        }
    }
}

impl<'a,T: Ord+Composite<'a>> Composite<'a> for Choice<T> {
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
                    let off  = if i==0 { 0 } else { vecr.0[i-1].0 };
                    let el   = &vecr.0[i].1;
                    let len  = el.num_elem();
                    roff+=len+1;
                    rvec.push((roff,el.clone()));
                    for j in 0..len+1 {
                        let expr = pr.read(fromr,off+j,arrr,em)?;
                        res.push(fr(expr,em)?);
                    }
                }
                break
            }
            if pos_r >= vecr.0.len() {
                for i in pos_l..vecl.0.len() {
                    let off  = if i==0 { 0 } else { vecl.0[i-1].0 };
                    let el   = &vecl.0[i].1;
                    let len  = el.num_elem();
                    roff+=len+1;
                    rvec.push((roff,el.clone()));
                    for j in 0..len+1 {
                        let expr = pl.read(froml,off+j,arrl,em)?;
                        res.push(fl(expr,em)?);
                    }
                }
                break
            }
            let el_l = &vecl.0[pos_l].1;
            let el_r = &vecr.0[pos_r].1;
            match el_l.cmp(el_r) {
                Ordering::Equal => {
                    let off_l = if pos_l==0 { 0 } else { vecl.0[pos_l-1].0 };
                    let off_r = if pos_r==0 { 0 } else { vecr.0[pos_r-1].0 };
                    let sel_l = pl.read(froml,off_l,arrl,em)?;
                    let sel_r = pr.read(fromr,off_r,arrr,em)?;
                    let nsel  = comb(sel_l,sel_r,em)?;
                    res.push(nsel);
                    match T::combine(&pl.clone().then(Choice::element(pos_l)),froml,arrl,
                                     &pr.clone().then(Choice::element(pos_r)),fromr,arrr,
                                     comb,fl,fr,res,em)? {
                        None => return Ok(None),
                        Some(el) => {
                            roff+=el.num_elem()+1;
                            rvec.push((roff,el));
                            pos_l+=1;
                            pos_r+=1;
                        }
                    }
                },
                Ordering::Less => {
                    let off  = if pos_l==0 { 0 } else { vecl.0[pos_l-1].0 };
                    let el   = &vecl.0[pos_l].1;
                    let len  = el.num_elem();
                    roff+=len+1;
                    rvec.push((roff,el.clone()));
                    for j in 0..len+1 {
                        let expr = pl.read(froml,off+j,arrl,em)?;
                        res.push(fl(expr,em)?);
                    }
                    pos_l+=1;
                },
                Ordering::Greater => {
                    let off  = if pos_r==0 { 0 } else { vecr.0[pos_r-1].0 };
                    let el   = &vecr.0[pos_r].1;
                    let len  = el.num_elem();
                    roff+=len+1;
                    rvec.push((roff,el.clone()));
                    for j in 0..len+1 {
                        let expr = pr.read(fromr,off+j,arrr,em)?;
                        res.push(fr(expr,em)?);
                    }
                    pos_r+=1;
                }
            }
        }
        Ok(Some(Choice(rvec)))
    }
}

impl<'a,T: 'a+Ord+HasSorts> SimplePathEl<'a> for ChoiceEl<T> {
    type From = Choice<T>;
    type To   = T;
    fn get<'b>(&self,ch: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &ch.0[self.0].1
    }
    fn get_mut<'b>(&self,ch: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut ch.0[self.0].1
    }
}

impl<'a,T: 'a+Ord+HasSorts,Em: Embed> PathEl<'a,Em> for ChoiceEl<T> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,
        from: &Prev::From,
        pos: usize,
        arr: &[Em::Expr],
        em: &mut Em)
        -> Result<Em::Expr,Em::Error> {

        let ch = prev.get(from);
        let off = ch.offset(self.0);
        prev.read(from,off+1+pos,arr,em)
    }
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,len: usize,arr: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        let ch = prev.get(from);
        let off = ch.offset(self.0);
        prev.read_slice(from,off+pos+1,len,arr)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,expr: Em::Expr,
        arr: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        let vec = prev.get(from);
        let off = vec.offset(self.0);
        prev.write(from,off+pos+1,expr,arr,em)
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
            let ch = prev.get_mut(from);
            if old_len<src.len() {
                let diff = src.len()-old_len;
                for i in self.0..ch.0.len() {
                    ch.0[i].0+=diff;
                }
            } else if old_len>src.len() {
                let diff = old_len-src.len();
                for i in self.0..ch.0.len() {
                    ch.0[i].0-=diff;
                }
            }
            ch.offset(self.0)
        };
        prev.write_slice(from,pos+off+1,old_len,src,trg,em)
    }
}

impl<'a,Em: Embed,T: 'a+Ord+HasSorts,P: 'a+Path<'a,Em,To=Choice<T>>> CondIterator<Em> for Choices<'a,Em,T,P> {
    type Item = Then<P,ChoiceEl<T>>;
    fn next(&mut self,conds: &mut Vec<Em::Expr>,cond_pos: usize,em: &mut Em)
            -> Result<Option<Self::Item>,Em::Error> {
        if self.pos >= self.choice.0.len() {
            return Ok(None)
        }
        let off = self.choice.offset(self.pos);
        conds.truncate(cond_pos);
        let cond = self.path.read(self.from,off,self.arr,em)?;
        conds.push(cond);
        let npath = self.path.clone().then(Choice::element(self.pos));
        self.pos+=1;
        Ok(Some(npath))
    }
}

impl<T : Ord+Semantic+Debug+HasSorts> Semantic for Choice<T> {
    type Meaning = ChoiceMeaning<T::Meaning>;
    type MeaningCtx = Option<T::MeaningCtx>;
    fn meaning(&self,pos: usize) -> Self::Meaning {
        let idx = match self.0.binary_search_by(|&(ref off,_)| { off.cmp(&pos) }) {
            Ok(i) => i+1,
            Err(i) => i
        };
        let off = if idx==0 { 0 } else { self.0[idx-1].0 };
        match pos-off {
            0 => ChoiceMeaning::Selector(idx),
            n => ChoiceMeaning::Item(idx,self.0[idx].1.meaning(n-1))
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &ChoiceMeaning::Selector(idx) => {
                write!(fmt,"selector({:?})",self.0[idx].1)
            },
            &ChoiceMeaning::Item(idx,ref nm) => {
                write!(fmt,"choice({:?}).",self.0[idx].1)?;
                self.0[idx].1.fmt_meaning(nm,fmt)
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        if self.0.len() > 0 {
            Some((None,ChoiceMeaning::Selector(0)))
        } else {
            None
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        let nm = match m {
            &mut ChoiceMeaning::Selector(ref mut idx)
                => match self.0[*idx].1.first_meaning() {
                    None => if *idx+1 < self.0.len() {
                        *ctx = None;
                        *idx = *idx+1;
                        return true
                    } else {
                        return false
                    },
                    Some((nctx,nm)) => {
                        *ctx = Some(nctx);
                        ChoiceMeaning::Item(*idx,nm)
                    }
                },
            &mut ChoiceMeaning::Item(idx,ref mut cm)
                => {
                    let (nm,nctx) = match ctx {
                        &mut Some(ref mut rctx) => if self.0[idx].1.next_meaning(rctx,cm) {
                            return true
                        } else if idx+1<self.0.len() {
                            (ChoiceMeaning::Selector(idx+1),None)
                        } else {
                            return false
                        },
                        _ => unreachable!()
                    };
                    *ctx = nctx;
                    nm
                }
        };
        *m = nm;
        true
    }
}
