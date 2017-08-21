extern crate num_bigint;
extern crate num_rational;

use self::num_bigint::BigInt;
use self::num_rational::Ratio;
use smt::embed::Embed;
use std::fmt::{Display,Formatter,Error};

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub enum SortKind<T> {
    Bool,
    Int,
    Real,
    BitVec(usize),
    Array(Vec<T>,T)
}

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub enum Value {
    Bool(bool),
    Int(BigInt),
    Real(Ratio<BigInt>),
    BitVec(usize,BigInt)
}

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub struct Sort(pub Box<SortKind<Sort>>);

impl Value {
    pub fn sort<E : Embed>(&self,em: &mut E) -> Result<E::Sort,E::Error> {
        match *self {
            Value::Bool(_) => em.tp_bool(),
            Value::Int(_) => em.tp_int(),
            Value::Real(_) => em.tp_real(),
            Value::BitVec(sz,_) => em.tp_bitvec(sz)
        }
    }
}

impl<T> SortKind<T> {
    pub fn map<U,F : Fn(&T) -> U>(&self,f: F) -> SortKind<U> {
        match *self {
            SortKind::Bool => SortKind::Bool,
            SortKind::Int => SortKind::Int,
            SortKind::Real => SortKind::Real,
            SortKind::BitVec(sz) => SortKind::BitVec(sz),
            SortKind::Array(ref arr,ref el) => {
                let mut narr = Vec::with_capacity(arr.len());
                for e in arr.iter() {
                    narr.push(f(e))
                }
                SortKind::Array(narr,f(&el))
            }
        }
    }
}

impl<T : Display> Display for SortKind<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match *self {
            SortKind::Bool => write!(f,"Bool"),
            SortKind::Int => write!(f,"Int"),
            SortKind::Real => write!(f,"Real"),
            SortKind::BitVec(ref sz) => write!(f,"(_ BitVec {})",sz),
            SortKind::Array(ref idx,ref el) => {
                write!(f,"(Array ")?;
                for i in idx.iter() {
                    write!(f,"{} ",i)?;
                }
                write!(f,"{})",el)
            }
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> Result<(),Error> {
        match *self {
            Value::Bool(true) => f.write_str("true"),
            Value::Bool(false) => f.write_str("false"),
            Value::Int(ref v) => v.fmt(f),
            Value::Real(ref rv) => write!(f,"(/ {} {})",rv.numer(),rv.denom()),
            Value::BitVec(sz,ref v) => if sz%4==0 {
                write!(f,"#x{0:1$X}",v,sz/4)
            } else {
                write!(f,"#b{0:1$b}",v,sz)
            }
        }
    }
}

impl Sort {
    pub fn embed<Em : Embed>(&self,em: &mut Em)
                             -> Result<Em::Sort,Em::Error> {
        match *self.0 {
            SortKind::Bool => em.embed_sort(SortKind::Bool),
            SortKind::Int => em.embed_sort(SortKind::Int),
            SortKind::Real => em.embed_sort(SortKind::Real),
            SortKind::BitVec(sz) => em.embed_sort(SortKind::BitVec(sz)),
            SortKind::Array(ref idx,ref el) => {
                let mut nidx = Vec::with_capacity(idx.len());
                for i in idx.iter() {
                    let ni = i.embed(em)?;
                    nidx.push(ni)
                }
                let nel = el.embed(em)?;
                em.embed_sort(SortKind::Array(nidx,nel))
            }
        }
    }
}
