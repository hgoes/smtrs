use composite::*;

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord)]
pub struct Data<T>(T);

impl<T> Data<T> {
    pub fn get<'a,'b,Em: Embed,P: Path<'a,Em,To=Self>>(path: &P,from: &'b P::From) -> &'b T where 'a: 'b {
        &path.get(from).0
    }
}

impl<T> HasSorts for Data<T> {
    fn num_elem(&self) -> usize { 0 }
    fn elem_sort<Em: Embed>(&self,_: usize,_: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        unreachable!()
    }
}

impl<T: Clone+Hash+Eq> Composite for Data<T> {
    fn combine<'a,Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,_: &[Em::Expr],
        pr: &PR,fromr: &PR::From,_: &[Em::Expr],
        _: &FComb,_: &FL,_: &FR,
        _: &mut Vec<Em::Expr>,
        _: &mut Em)
        -> Result<Option<Self>,Em::Error>
        where
        Em: Embed,
        PL: Path<'a,Em,To=Self>,
        PR: Path<'a,Em,To=Self>,
        FComb: Fn(Em::Expr,Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FL: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error>,
        FR: Fn(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {

        let lhs = pl.get(froml);
        let rhs = pr.get(fromr);
        if lhs.0==rhs.0 {
            Ok(Some(Data(lhs.0.clone())))
        } else {
            Ok(None)
        }
    }
}

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord)]
pub struct SingletonBool;

pub static SINGLETON_BOOL: SingletonBool = SingletonBool;

impl HasSorts for SingletonBool {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        debug_assert_eq!(pos,0);
        em.tp_bool()
    }
}

impl Composite for SingletonBool {
    fn combine<'a,Em,PL,PR,FComb,FL,FR>(
        pl: &PL,froml: &PL::From,arrl: &[Em::Expr],
        pr: &PR,fromr: &PR::From,arrr: &[Em::Expr],
        comb: &FComb,_: &FL,_: &FR,
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

        let lhs = pl.read(froml,0,arrl,em)?;
        let rhs = pr.read(fromr,0,arrr,em)?;

        let ne = comb(lhs,rhs,em)?;

        res.push(ne);
        Ok(Some(SingletonBool))
    }
}

impl<D : Eq+Clone+Hash> Semantic for Data<D> {
    type Meaning = ();
    type MeaningCtx = ();
    fn meaning(&self,_:usize) -> Self::Meaning {
        ()
    }
    fn fmt_meaning<F : fmt::Write>(&self,_: &Self::Meaning,fmt: &mut F) -> Result<(),fmt::Error> {
       write!(fmt,"#")
    }
    fn first_meaning(&self) -> Option<(Self::MeaningCtx,Self::Meaning)> {
        None
    }
    fn next_meaning(&self,_:&mut Self::MeaningCtx,_:&mut Self::Meaning) -> bool {
        false
    }
}
