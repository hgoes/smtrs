use types::*;
use expr::{Expr,Function,BVOp,ArithOp};
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
    fn is_bool(&mut self,srt: &Self::Sort) -> Result<bool,Self::Error> {
        match self.unbed_sort(srt)? {
            SortKind::Bool => Ok(true),
            _ => Ok(false)
        }
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
    fn is_bitvec(&mut self,srt: &Self::Sort) -> Result<Option<usize>,Self::Error> {
        match self.unbed_sort(srt)? {
            SortKind::BitVec(bw) => Ok(Some(bw)),
            _ => Ok(None)
        }
    }
    fn tp_array(&mut self,idx: Vec<Self::Sort>,el: Self::Sort)
                -> Result<Self::Sort,Self::Error> {
        self.embed_sort(SortKind::Array(idx,el))
    }
    fn var(&mut self,var: Self::Var) -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::Var(var))
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
    fn eq_many(&mut self,args: Vec<Self::Expr>)
               -> Result<Self::Expr,Self::Error> {
        debug_assert!(args.len() > 0);
        let srt = self.type_of(&args[0])?;
        debug_assert!(args[1..].iter().all(|el| match self.type_of(el) {
            Ok(srt2) => srt==srt2,
            Err(_) => false
        }));
        self.embed(Expr::App(Function::Eq(srt,args.len()),args))
    }
    fn add_int(&mut self,mut args: Vec<Self::Expr>)
               -> Result<Self::Expr,Self::Error> {
        match args.len() {
            0 => self.const_int(BigInt::from(0)),
            1 => Ok(args.remove(0)),
            l => self.embed(Expr::App(Function::ArithInt(ArithOp::Add,l),
                                      args))
        }
    }
    fn sub_int(&mut self,args: Vec<Self::Expr>)
               -> Result<Self::Expr,Self::Error> {
        match args.len() {
            0 => self.const_int(BigInt::from(0)),
            l => self.embed(Expr::App(Function::ArithInt(ArithOp::Sub,l),
                                      args))
        }
    }
    fn not(&mut self,e: Self::Expr)
           -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::App(Function::Not,vec![e]))
    }
    fn and(&mut self,args: Vec<Self::Expr>)
           -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::App(Function::And(args.len()),args))
    }
    fn or(&mut self,args: Vec<Self::Expr>)
          -> Result<Self::Expr,Self::Error> {
        self.embed(Expr::App(Function::Or(args.len()),args))
    }
    fn ite(&mut self,cond: Self::Expr,if_t: Self::Expr,if_f: Self::Expr)
           -> Result<Self::Expr,Self::Error> {
        let srt = self.type_of(&if_t)?;
        debug_assert!(match self.type_of(&cond) {
            Err(_) => false,
            Ok(srt_cond) => match self.type_of(&if_f) {
                Err(_) => false,
                Ok(srt_f) => match self.is_bool(&srt_cond) {
                    Ok(true) => srt==srt_f,
                    _ => false
                }
            }
        });
        self.embed(Expr::App(Function::ITE(srt),vec![cond,if_t,if_f]))
    }
    fn bvadd(&mut self,lhs: Self::Expr,rhs: Self::Expr)
             -> Result<Self::Expr,Self::Error> {
        let srt_lhs = self.type_of(&lhs)?;
        let bw = match self.is_bitvec(&srt_lhs)? {
            Some(r) => r,
            None => panic!("Argument to bvadd not a bitvector")
        };
        debug_assert!(match self.type_of(&rhs) {
            Ok(tp_r) => match self.is_bitvec(&tp_r) {
                Ok(Some(bw_r)) => bw==bw_r,
                _ => false
            },
            Err(_) => false
        });
        self.embed(Expr::App(Function::BV(bw,BVOp::Arith(ArithOp::Add)),
                             vec![lhs,rhs]))
    }
    fn bvsub(&mut self,lhs: Self::Expr,rhs: Self::Expr)
             -> Result<Self::Expr,Self::Error> {
        let srt_lhs = self.type_of(&lhs)?;
        let bw = match self.is_bitvec(&srt_lhs)? {
            Some(r) => r,
            None => panic!("Argument to bvsub not a bitvector")
        };
        debug_assert!(match self.type_of(&rhs) {
            Ok(tp_r) => match self.is_bitvec(&tp_r) {
                Ok(Some(bw_r)) => bw==bw_r,
                _ => false
            },
            Err(_) => false
        });
        self.embed(Expr::App(Function::BV(bw,BVOp::Arith(ArithOp::Sub)),
                             vec![lhs,rhs]))
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

pub trait DeriveConst : Embed {
    fn derive_const(&mut self,&Self::Expr) -> Result<Option<Value>,Self::Error>;
}

pub trait DeriveValues : DeriveConst {
    type ValueIterator : Iterator<Item=Value>;
    fn derive_values(&mut self,&Self::Expr) -> Result<Option<Self::ValueIterator>,Self::Error>;
}
