use composite::*;
use types::{SortKind};
use types;
use expr;
use domain::Domain;
use embed::{DeriveConst,DeriveValues};

use std::rc::Rc;
use std::marker::PhantomData;

#[derive(PartialEq,Eq,PartialOrd,Ord,Hash,Clone,Debug)]
pub struct CompVar(pub usize);

#[derive(Hash,Debug)]
pub struct CompExpr<C>(pub Rc<expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>>,PhantomData<C>);

impl<C: HasSorts> CompExpr<C> {
    pub fn new(e: expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>) -> Self {
        CompExpr(Rc::new(e),PhantomData)
    }
}

impl<C: HasSorts> PartialEq for CompExpr<C> {
    fn eq(&self,oth: &Self) -> bool {
        Rc::ptr_eq(&self.0,&oth.0) ||
            self.0==oth.0
    }
}

impl<C: HasSorts> Eq for CompExpr<C> {}

impl<C> Clone for CompExpr<C> {
    fn clone(&self) -> Self {
        CompExpr(self.0.clone(),PhantomData)
    }
}

pub struct Comp<C: HasSorts> {
    pub referenced: C,
}

pub struct CompDom<'a,C: 'a+HasSorts,Dom: 'a> {
    pub comp: Comp<&'a C>,
    pub domain: &'a Dom
}

impl fmt::Display for CompVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"v{}",self.0)
    }
}

impl<C: HasSorts+Debug> Embed for Comp<C> {
    type Sort = types::Sort;
    type Var = CompVar;
    type Expr = CompExpr<C>;
    type Fun = expr::NoVar;
    type Error = ();
    fn embed_sort(&mut self,tp: SortKind<types::Sort>)
                  -> Result<types::Sort,()> {
        Ok(types::Sort::from_kind(tp))
    }
    fn unbed_sort(&mut self,tp: &types::Sort) -> Result<SortKind<types::Sort>,()> {
        Ok(tp.kind())
    }
    fn embed(&mut self,e: expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>)
             -> Result<CompExpr<C>,()> {
        Ok(CompExpr(Rc::new(e),PhantomData))
    }
    fn unbed(&mut self,e: &CompExpr<C>)
             -> Result<expr::Expr<types::Sort,CompVar,CompExpr<C>,expr::NoVar>,()> {
        Ok((*e.0).clone())
    }
    fn type_of_var(&mut self,var: &CompVar) -> Result<types::Sort,()> {
        let mut ncomp = Comp { referenced: &self.referenced };
        self.referenced.elem_sort(var.0,&mut ncomp)
    }
    fn type_of_fun(&mut self,_:&expr::NoVar) -> Result<types::Sort,()> {
        panic!("Composite expressions don't have functions")
    }
    fn arity(&mut self,_:&expr::NoVar) -> Result<usize,()> {
        panic!("Composite expressions don't have functions")
    }
    fn type_of_arg(&mut self,_:&expr::NoVar,_:usize) -> Result<types::Sort,()> {
        panic!("Composite expressions don't have functions")
    }
}

impl<'a,C: 'a+HasSorts+Debug,Dom: Domain<C>> Embed for CompDom<'a,C,Dom> {
    type Sort = <Comp<&'a C> as Embed>::Sort;
    type Var = <Comp<&'a C> as Embed>::Var;
    type Expr = <Comp<&'a C> as Embed>::Expr;
    type Fun = <Comp<&'a C> as Embed>::Fun;
    type Error = <Comp<&'a C> as Embed>::Error;
    fn embed_sort(&mut self,tp: SortKind<Self::Sort>)
                  -> Result<Self::Sort,Self::Error> {
        self.comp.embed_sort(tp)
    }
    fn unbed_sort(&mut self,tp: &types::Sort) -> Result<SortKind<types::Sort>,Self::Error> {
        self.comp.unbed_sort(tp)
    }
    fn embed(&mut self,e: expr::Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>)
             -> Result<CompExpr<&'a C>,Self::Error> {
        self.comp.embed(e)
    }
    fn unbed(&mut self,e: &Self::Expr)
             -> Result<expr::Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>,Self::Error> {
        self.comp.unbed(e)
    }
    fn type_of_var(&mut self,var: &Self::Var) -> Result<Self::Sort,Self::Error> {
        self.comp.type_of_var(var)
    }
    fn type_of_fun(&mut self,fun:&Self::Fun) -> Result<Self::Sort,Self::Error> {
        self.comp.type_of_fun(fun)
    }
    fn arity(&mut self,fun:&Self::Fun) -> Result<usize,Self::Error> {
        self.comp.arity(fun)
    }
    fn type_of_arg(&mut self,fun:&Self::Fun,p:usize) -> Result<Self::Sort,Self::Error> {
        self.comp.type_of_arg(fun,p)
    }
}

impl<'a,C: 'a+HasSorts+Debug,Dom: Domain<C>> DeriveConst for CompDom<'a,C,Dom> {
    fn derive_const(&mut self,e: &Self::Expr)
                    -> Result<Option<types::Value>,Self::Error> {
        self.domain.is_const(e,&mut self.comp,&|v:&CompVar| Some(v.0))
    }
}

impl<'a,C: 'a+HasSorts+Debug,Dom: Domain<C>> DeriveValues for CompDom<'a,C,Dom> {
    type ValueIterator = Dom::ValueIterator;
    fn derive_values(&mut self,e: &Self::Expr)
                     -> Result<Option<Self::ValueIterator>,Self::Error> {
        self.domain.values(e,&mut self.comp,&|v:&CompVar| Some(v.0))
    }
}

impl<C: HasSorts> fmt::Display for CompExpr<C> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(&*self.0,f)
    }
}

impl<C : HasSorts> CompExpr<C> {
    pub fn translate<Em : Embed,F>(&self,f: &mut F,em: &mut Em) -> Result<Em::Expr,Em::Error>
        where F : FnMut(usize,&mut Em) -> Result<Em::Expr,Em::Error> {
        match *self.0 {
            expr::Expr::Var(ref v) => f(v.0,em),
            expr::Expr::Const(ref c) => em.embed(expr::Expr::Const(c.clone())),
            expr::Expr::App(ref fun,ref args) => {
                let nfun = fun.map(&mut |srt| srt.embed(em),&mut |_| unreachable!())?;
                let mut nargs = Vec::with_capacity(args.len());
                for arg in args.iter() {
                    nargs.push(arg.translate(f,em)?)
                }
                em.embed(expr::Expr::App(nfun,nargs))
            },
            expr::Expr::AsArray(ref fun) => {
                let nfun = fun.map(&mut |srt| srt.embed(em),&mut |_| unreachable!())?;
                em.embed(expr::Expr::AsArray(nfun))
            }
            _ => unreachable!()
        }
    }
}
