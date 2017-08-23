use types::*;
use expr::{Expr,Function};
use num_bigint::BigInt;
use num_rational::Ratio;
use std::fmt::Debug;

pub trait Embed : Sized {
    type Sort : Clone + Eq + Debug;
    type Var : Clone + Eq + Debug;
    type Expr : Clone + Eq + Debug;
    type Fun : Clone + Eq + Debug;
    type Error : Debug;
    fn embed_sort(&mut self,SortKind<Self::Sort>)
                  -> Result<Self::Sort,Self::Error>;
    fn unbed_sort(&mut self,&Self::Sort)
                  -> Result<SortKind<Self::Sort>,Self::Error>;
    fn embed(&mut self,Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>)
             -> Result<Self::Expr,Self::Error>;
    fn unbed(&mut self,&Self::Expr)
             -> Result<Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>,
                       Self::Error>;
    fn type_of_var(&mut self,&Self::Var)
                   -> Result<Self::Sort,Self::Error>;
    fn type_of_fun(&mut self,&Self::Fun)
                   -> Result<Self::Sort,Self::Error>;
    fn arity(&mut self,&Self::Fun) -> Result<usize,Self::Error>;
    fn type_of_arg(&mut self,&Self::Fun,usize)
                   -> Result<Self::Sort,Self::Error>;
    fn type_of(&mut self,e: &Self::Expr)
               -> Result<Self::Sort,Self::Error> {
        let e = self.unbed(e)?;
        e.sort(self)
    }
    
    fn tp_bool(&mut self) -> Result<Self::Sort,Self::Error> {
        self.embed_sort(SortKind::Bool)
    }
    
    fn tp_int(&mut self) -> Result<Self::Sort,Self::Error> {
        self.embed_sort(SortKind::Int)
    }

    fn tp_real(&mut self) -> Result<Self::Sort,Self::Error> {
        self.embed_sort(SortKind::Real)
    }

    fn tp_bitvec(&mut self,sz: usize) -> Result<Self::Sort,Self::Error> {
        self.embed_sort(SortKind::BitVec(sz))
    }
    
    fn tp_array(&mut self,idx: Vec<Self::Sort>,el: Self::Sort)
                -> Result<Self::Sort,Self::Error> {
        self.embed_sort(SortKind::Array(idx,el))
    }
    fn const_bool(&mut self,val: bool)
                  -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::Const(Value::Bool(val)))
    }
    fn const_int(&mut self,val: BigInt)
                  -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::Const(Value::Int(val)))
    }
    fn const_real(&mut self,val: Ratio<BigInt>)
                  -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::Const(Value::Real(val)))
    }
    fn const_bitvec(&mut self,bw: usize,val: BigInt)
                    -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::Const(Value::BitVec(bw,val)))
    }
    fn eq(&mut self,e1: Self::Expr,e2: Self::Expr)
          -> Result<Self::Expr,Self::Error> {
        let tp1 = self.type_of(&e1)?;
        self.embed(Expr::App(Function::Eq(tp1,2),vec![e1,e2]))
    }
    fn not(&mut self,e: Self::Expr)
           -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::App(Function::Not,vec![e]))
    }
    fn eq_many(&mut self,args: Vec<Self::Expr>)
               -> Result<Self::Expr,Self::Error> {
        debug_assert!(args.len() > 0);
        let srt = self.type_of(&args[0])?;
        //debug_assert!(args[1..].iter().all(|el| el.sort()==srt));
        self.embed(Expr::App(Function::Eq(srt,args.len()),args))
    }

    fn select(&mut self,arr: Self::Expr,idx: Vec<Self::Expr>)
              -> Result<Self::Expr,Self::Error> {
        let arr_tp = self.type_of(&arr)?;
        let (idx_tp,el_tp) = match self.unbed_sort(&arr_tp)? {
            SortKind::Array(tps,tp) => (tps,tp),
            _ => panic!("select argument isn't an array")
        };

        debug_assert!(idx_tp.len()==idx.len());
        debug_assert!(idx.iter().zip(idx_tp.iter()).all(
            |(i,tp)| { match self.type_of(i) {
                Err(_) => false,
                Ok(tp2) => *tp==tp2
            }
            }));

        self.embed(Expr::App(Function::Select(idx_tp,el_tp),idx))
    }
}
