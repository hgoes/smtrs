use composite::*;

#[derive(Clone)]
pub struct SomeP;

pub fn set_some<'a,Em: Embed,From,T: 'a+HasSorts+Clone,
                P: Path<'a,Em,From,To=Option<T>>,
                FromSrc,PSrc: Path<'a,Em,FromSrc,To=T>>(
    path: &P,
    from: &mut From,
    arr:  &mut Vec<Em::Expr>,
    path_src: &PSrc,
    from_src: &FromSrc,
    arr_src:  &[Em::Expr],
    em: &mut Em
) -> Result<(),Em::Error> {
    let old_sz = match path.get(from) {
        &None => 0,
        &Some(ref old) => old.num_elem()
    };
    let src = path_src.get(from_src);
    *path.get_mut(from) = Some(src.clone());
    let len = src.num_elem();
    let mut buf = Vec::with_capacity(len);
    path_src.read_into(from_src,0,len,arr_src,&mut buf,em)?;
    path.write_slice(from,0,old_sz,arr,&mut buf,em)
}

pub fn option<'a,T: 'a,From,P: SimplePath<'a,From,To=Option<T>>>(
    path: P,
    from: &From) -> Option<Then<P,SomeP>> {
    match path.get(from) {
        &None => None,
        &Some(_) => Some(Then { first: path,
                                then: SomeP })
    }
}

pub fn some() -> SomeP {
    SomeP
}

impl<'a,T: 'a> SimplePathEl<'a,Option<T>> for SomeP {
    type To = T;
    fn get<'b>(&self,from: &'b Option<T>) -> &'b Self::To where 'a: 'b {
        from.as_ref().expect("get called on None")
    }
    fn get_mut<'b>(&self,from: &'b mut Option<T>)
                   -> &'b mut Self::To where 'a: 'b {
        from.as_mut().expect("get_mut called on None")
    }
}

impl<'a,Em: Embed,T: 'a> PathEl<'a,Em,Option<T>> for SomeP {
    fn read<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Option<T>>>(
        &self,
        prev: &Prev,from: &PrevFrom,
        pos: usize,src: &[Em::Expr],em: &mut Em)
        -> Result<Em::Expr,Em::Error> {
        prev.read(from,pos,src,em)
    }
    fn read_slice<'b,PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Option<T>>>(
        &self,prev: &Prev,from: &PrevFrom,pos: usize,len: usize,src: &'b [Em::Expr])
        -> Option<&'b [Em::Expr]> {
        prev.read_slice(from,pos,len,src)
    }
    fn write<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Option<T>>>(
        &self,prev: &Prev,from: &PrevFrom,
        pos: usize,ne: Em::Expr,
        trg: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write(from,pos,ne,trg,em)
    }
    fn write_slice<PrevFrom,Prev: Path<'a,Em,PrevFrom,To=Option<T>>>(
        &self,prev: &Prev,from: &mut PrevFrom,pos: usize,old_len: usize,
        src: &mut Vec<Em::Expr>,trg: &mut Vec<Em::Expr>,em: &mut Em)
        -> Result<(),Em::Error> {
        prev.write_slice(from,pos,old_len,src,trg,em)
    }
}

impl<T: HasSorts> HasSorts for Option<T> {
    fn num_elem(&self) -> usize {
        match self {
            &None => 0,
            &Some(ref x) => x.num_elem()
        }
    }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        match self {
            &None => panic!("elem_sort called on None"),
            &Some(ref x) => x.elem_sort(pos,em)
        }
    }
}

impl<T: Composite> Composite for Option<T> {
    fn combine<'a,Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,srcl: &[Em::Expr],
        pr: &PR,fromr: &FromR,srcr: &[Em::Expr],
        comb: &FComb,only_l: &FL,only_r: &FR,
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

        let lhs = pl.get(froml);
        let rhs = pr.get(fromr);

        match lhs {
            &None => match rhs {
                &None => {
                    Ok(Some(None))
                },
                &Some(ref rhs_) => {
                    for i in 0..rhs_.num_elem() {
                        let el = pr.read(fromr,i,srcr,em)?;
                        let nel = only_r(el,em)?;
                        res.push(nel);
                    }
                    Ok(Some(Some(rhs_.clone())))
                }
            },
            &Some(ref lhs_) => match rhs {
                &None => {
                    for i in 0..lhs_.num_elem() {
                        let el = pl.read(froml,i,srcl,em)?;
                        let nel = only_l(el,em)?;
                        res.push(nel);
                    }
                    Ok(Some(Some(lhs_.clone())))
                },
                &Some(_) => {
                    let npl = pl.clone().then(some());
                    let npr = pr.clone().then(some());
                    match T::combine(&npl,froml,srcl,
                                     &npr,fromr,srcr,
                                     comb,only_l,only_r,res,em)? {
                        None => Ok(None),
                        Some(res) => Ok(Some(Some(res)))
                    }
                }
            }
        }
    }
}

impl<T: Semantic> Semantic for Option<T> {
    type Meaning = T::Meaning;
    type MeaningCtx = T::MeaningCtx;
    fn meaning(&self,n: usize) -> Self::Meaning {
        match self {
            &None => panic!("meaning called for None"),
            &Some(ref obj) => obj.meaning(n)
        }
    }
    fn fmt_meaning<F : fmt::Write>(&self,m: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
        match self {
            &None => panic!("fmt_meaning called for None"),
            &Some(ref obj) => obj.fmt_meaning(m,fmt)
        }
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        match self {
            &None => None,
            &Some(ref obj) => obj.first_meaning()
        }
    }
    fn next_meaning(&self,ctx: &mut Self::MeaningCtx,
                    m: &mut Self::Meaning) -> bool {
        match self {
            &None => false,
            &Some(ref obj) => obj.next_meaning(ctx,m)
        }
    }
}
