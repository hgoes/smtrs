use composite::*;

pub struct Element1Of2<A,B>(PhantomData<(A,B)>);
pub struct Element2Of2<A,B>(PhantomData<(A,B)>);

pub fn tuple<Em,F1,F2,X,Y>(f1: F1,f2: F2,res: &mut Vec<Em::Expr>,em: &mut Em)
                           -> Result<(X,Y),Em::Error>
    where
    Em: Embed,
    F1: FnOnce(&mut Vec<Em::Expr>,&mut Em) -> Result<X,Em::Error>,
    F2: FnOnce(&mut Vec<Em::Expr>,&mut Em) -> Result<Y,Em::Error> {

    let x = f1(res,em)?;
    let y = f2(res,em)?;
    Ok((x,y))
}

pub fn element1of2<A,B>() -> Element1Of2<A,B> {
    Element1Of2(PhantomData)
}

pub fn element2of2<A,B>() -> Element2Of2<A,B> {
    Element2Of2(PhantomData)
}

impl<A,B> Clone for Element1Of2<A,B> {
    fn clone(&self) -> Self { Element1Of2(PhantomData) }
}

impl<A,B> Clone for Element2Of2<A,B> {
    fn clone(&self) -> Self { Element2Of2(PhantomData) }
}

impl<'a,A: 'a,B: 'a> SimplePathEl<'a> for Element1Of2<A,B> {
    type From = (A,B);
    type To = A;
    fn get<'b>(&self,from: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &from.0
    }
    fn get_mut<'b>(&self,from: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut from.0
    }
}

impl<'a,Em: Embed,A: 'a,B: 'a> PathEl<'a,Em> for Element1Of2<A,B> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,from: &Prev::From,
        pos: usize,src: &[Em::Expr],em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,src,em)
    }
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,len: usize,src: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos,len,src)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,
        pos: usize,ne: Em::Expr,
        trg: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(from,pos,ne,trg,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &mut Prev::From,pos: usize,old_len: usize,
        src: &mut Vec<Em::Expr>,trg: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<'a,A: 'a+HasSorts,B: 'a> SimplePathEl<'a> for Element2Of2<A,B> {
    type From = (A,B);
    type To = B;
    fn get<'b>(&self,from: &'b Self::From) -> &'b Self::To where 'a: 'b {
        &from.1
    }
    fn get_mut<'b>(&self,from: &'b mut Self::From) -> &'b mut Self::To where 'a: 'b {
        &mut from.1
    }
}

impl<'a,Em: Embed,A: 'a+HasSorts,B: 'a> PathEl<'a,Em> for Element2Of2<A,B> {
    fn read<Prev: Path<'a,Em,To=Self::From>>(
        &self,
        prev: &Prev,from: &Prev::From,
        pos: usize,src: &[Em::Expr],em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        let len0 = prev.get(from).0.num_elem();
        prev.read(from,len0+pos,src,em)
    }
    fn read_slice<'b,Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,pos: usize,len: usize,src: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        let len0 = prev.get(from).0.num_elem();
        prev.read_slice(from,len0+pos,len,src)
    }
    fn write<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &Prev::From,
        pos: usize,ne: Em::Expr,
        trg: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        let len0 = prev.get(from).0.num_elem();
        prev.write(from,len0+pos,ne,trg,em)
    }
    fn write_slice<Prev: Path<'a,Em,To=Self::From>>(
        &self,prev: &Prev,from: &mut Prev::From,pos: usize,old_len: usize,
        src: &mut Vec<Em::Expr>,trg: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        let len0 = prev.get(from).0.num_elem();
        prev.write_slice(from,len0+pos,old_len,src,trg,em)
    }
}

impl<A: HasSorts,B: HasSorts> HasSorts for (A,B) {
    fn num_elem(&self) -> usize {
        self.0.num_elem()+
            self.1.num_elem()
    }
    fn elem_sort<Em: Embed>(&self,n: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        let len0 = self.0.num_elem();
        if n<len0 {
            return self.0.elem_sort(n,em)
        }
        self.1.elem_sort(n-len0,em)
    }
}

impl<'a,A: Composite<'a>,B: Composite<'a>> Composite<'a> for (A,B) {
    fn combine<Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,srcl: &[Em::Expr],
        pr: &PR,fromr: &PR::From,srcr: &[Em::Expr],
        comb: &FComb,only_l: &FL,only_r: &FR,
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

        let el1_l = pl.clone().then(element1of2());
        let el1_r = pr.clone().then(element1of2());

        if let Some(nel1) = A::combine(&el1_l,froml,srcl,
                                       &el1_r,fromr,srcr,
                                       comb,only_l,only_r,
                                       res,em)? {
            let el2_l = pl.clone().then(element2of2());
            let el2_r = pr.clone().then(element2of2());

            if let Some(nel2) = B::combine(&el2_l,froml,srcl,
                                           &el2_r,fromr,srcr,
                                           comb,only_l,only_r,
                                           res,em)? {
                Ok(Some((nel1,nel2)))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }

    fn invariant<Em,P>(path: &P,from: &P::From,src: &[Em::Expr],
                       res: &mut Vec<Em::Expr>,
                       em: &mut Em)
                       -> Result<(),Em::Error>
        where Em: Embed,
              P: Path<'a,Em,To=Self> {
        let p1 = path.clone().then(element1of2());
        A::invariant(&p1,from,src,res,em)?;
        let p2 = path.clone().then(element2of2());
        B::invariant(&p2,from,src,res,em)
    }
}

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Debug,Clone)]
pub enum TupleMeaning<T,U> {
    Fst(T),
    Snd(U)
}

impl<T,U> Semantic for (T,U)
    where T : Semantic+HasSorts, U : Semantic {
    type Meaning = TupleMeaning<T::Meaning,U::Meaning>;
    type MeaningCtx = TupleMeaning<T::MeaningCtx,U::MeaningCtx>;
    fn meaning(&self,n: usize) -> Self::Meaning {
        let sz_0 = self.0.num_elem();
        if n<sz_0 {
            TupleMeaning::Fst(self.0.meaning(n))
        } else {
            TupleMeaning::Snd(self.1.meaning(n-sz_0))
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match m {
            &TupleMeaning::Fst(ref nm) => {
                write!(fmt,"0.")?;
                self.0.fmt_meaning(nm,fmt)
            },
            &TupleMeaning::Snd(ref nm) => {
                write!(fmt,"1.")?;
                self.1.fmt_meaning(nm,fmt)
            }
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self.0.first_meaning() {
            Some((ctx,m)) => Some((TupleMeaning::Fst(ctx),
                                   TupleMeaning::Fst(m))),
            None => match self.1.first_meaning() {
                Some((ctx,m)) => Some((TupleMeaning::Snd(ctx),
                                       TupleMeaning::Snd(m))),
                None => None
            }
        }
    }
    fn next_meaning(&self,
                    ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        let nm = match m {
            &mut TupleMeaning::Fst(ref mut cm) => {
                let (nm,nctx) = match ctx {
                    &mut TupleMeaning::Fst(ref mut cctx)
                        => if self.0.next_meaning(cctx,cm) {
                            return true
                        } else {
                            match self.1.first_meaning() {
                                None => return false,
                                Some((nctx,nm)) => {
                                    (TupleMeaning::Snd(nm),
                                     TupleMeaning::Snd(nctx))
                                }
                            }
                        },
                    _ => unreachable!()
                };
                *ctx = nctx;
                nm
            },
            &mut TupleMeaning::Snd(ref mut cm) => match ctx {
                &mut TupleMeaning::Snd(ref mut cctx)
                    => return self.1.next_meaning(cctx,cm),
                _ => unreachable!()
            }
        };
        *m = nm;
        true
    }
}
