use composite::*;
use types;

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct Data<T>(pub T);

impl<T> Data<T> {
    pub fn get<'a,'b,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(path: &P,from: &'b From) -> &'b T
        where 'a: 'b, T: 'a {
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
    fn combine<'a,Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,_: &[Em::Expr],
        pr: &PR,fromr: &FromR,_: &[Em::Expr],
        _: &FComb,_: &FL,_: &FR,
        _: &mut Vec<Em::Expr>,
        _: &mut Em)
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
        if lhs.0==rhs.0 {
            Ok(Some(Data(lhs.0.clone())))
        } else {
            Ok(None)
        }
    }
}

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord)]
pub struct Singleton(pub types::Sort);

impl Singleton {
    pub fn get<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &From,
        src:  &[Em::Expr],
        em:   &mut Em
    ) -> Result<Em::Expr,Em::Error> {
        path.read(from,0,src,em)
    }
    pub fn set<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &mut From,
        src:  &mut Vec<Em::Expr>,
        expr: Em::Expr,
        em:   &mut Em
    ) -> Result<(),Em::Error> {
        let nsort_em = em.type_of(&expr)?;
        let nsort = types::Sort::from_embed(&nsort_em,em)?;
        path.write(from,0,expr,src,em)?;
        path.get_mut(from).0 = nsort;
        Ok(())
    }
    pub fn set_same_type<'a,Em: Embed,From,P: Path<'a,Em,From,To=Self>>(
        path: &P,
        from: &mut From,
        src:  &mut Vec<Em::Expr>,
        expr: Em::Expr,
        em:   &mut Em
    ) -> Result<(),Em::Error> {
        path.write(from,0,expr,src,em)
    }
    pub fn update<'a,Em,From,P,F>(
        path: &P,
        from: &mut From,
        src:  &mut Vec<Em::Expr>,
        fun:  F,
        em:   &mut Em
    ) -> Result<(),Em::Error>
        where Em: Embed,
              P: Path<'a,Em,From,To=Self>,
              F: FnOnce(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {
        let expr = path.read(from,0,&src[..],em)?;
        let nexpr = fun(expr,em)?;
        let nsort_em = em.type_of(&nexpr)?;
        let nsort = types::Sort::from_embed(&nsort_em,em)?;
        path.write(from,0,nexpr,src,em)?;
        let sing = path.get_mut(from);
        sing.0 = nsort;
        Ok(())
    }
    pub fn update_same_type<'a,Em,From,P,F>(
        path: &P,
        from: &From,
        src:  &mut Vec<Em::Expr>,
        fun:  F,
        em:   &mut Em
    ) -> Result<(),Em::Error>
        where Em: Embed,
              P: Path<'a,Em,From,To=Self>,
              F: FnOnce(Em::Expr,&mut Em) -> Result<Em::Expr,Em::Error> {
        let expr = path.read(from,0,&src[..],em)?;
        let nexpr = fun(expr,em)?;
        path.write(from,0,nexpr,src,em)
    }
}

impl HasSorts for Singleton {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        debug_assert_eq!(pos,0);
        self.0.embed(em)
    }
}

impl Composite for Singleton {
    fn combine<'a,Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,arrl: &[Em::Expr],
        pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
        comb: &FComb,_: &FL,_: &FR,
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

        let lhs = pl.read(froml,0,arrl,em)?;
        let rhs = pr.read(fromr,0,arrr,em)?;

        if pl.get(froml) == pr.get(fromr) {
            let ne = comb(lhs,rhs,em)?;

            res.push(ne);
            Ok(Some(pl.get(froml).clone()))
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
    fn combine<'a,Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,arrl: &[Em::Expr],
        pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
        comb: &FComb,_: &FL,_: &FR,
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

#[derive(Clone,Hash,PartialEq,Eq,PartialOrd,Ord,Debug)]
pub struct SingletonBitVec(pub usize);

impl HasSorts for SingletonBitVec {
    fn num_elem(&self) -> usize { 1 }
    fn elem_sort<Em: Embed>(&self,pos: usize,em: &mut Em)
                            -> Result<Em::Sort,Em::Error> {
        debug_assert_eq!(pos,0);
        em.tp_bitvec(self.0)
    }
}

impl Composite for SingletonBitVec {
    fn combine<'a,Em,FromL,PL,FromR,PR,FComb,FL,FR>(
        pl: &PL,froml: &FromL,arrl: &[Em::Expr],
        pr: &PR,fromr: &FromR,arrr: &[Em::Expr],
        comb: &FComb,_: &FL,_: &FR,
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

        if pl.get(froml).0 != pr.get(fromr).0 {
            return Ok(None)
        }

        let lhs = pl.read(froml,0,arrl,em)?;
        let rhs = pr.read(fromr,0,arrr,em)?;

        let ne = comb(lhs,rhs,em)?;

        res.push(ne);
        Ok(Some(pl.get(froml).clone()))
    }
}
