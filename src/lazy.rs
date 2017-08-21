/*pub trait Lazy<'a> {
    type Result;
    fn base(Self::Result) -> Self;
    fn eval(self) -> Self::Result;
}*/

pub trait Lazy<'a> {
    type Repr;
    fn lazy(self) -> Self::Repr;
    fn lazy_ref(&'a self) -> Self::Repr;
    fn eval(Self::Repr) -> Self;
}

pub enum LazyVec<'a,T : 'a + Lazy<'a>> {
    Base(Vec<T>),
    BaseRef(&'a Vec<T>),
    Insert(usize,T::Repr,Box<LazyVec<'a,T>>)
}

impl<'a,T : 'a + Lazy<'a> + Clone> Lazy<'a> for Vec<T> {
    type Repr = LazyVec<'a,T>;
    fn lazy(self) -> LazyVec<'a,T> {
        LazyVec::Base(self)
    }
    fn lazy_ref(&'a self) -> LazyVec<'a,T> {
        LazyVec::BaseRef(self)
    }
    fn eval(lvec: LazyVec<'a,T>) -> Vec<T> {
        match lvec {
            LazyVec::Base(vec) => vec,
            LazyVec::BaseRef(rvec) => (*rvec).clone(),
            LazyVec::Insert(pos,el,rest) => {
                let mut result = Vec::eval(*rest);
                result[pos] = T::eval(el);
                result
            }
        }
    }
}

/*
impl<'a,R,T : AsLazy<'a>> AsLazy<'a> for Vec<T> {
    type Result = LazyVec<'a,T::Result>;
    fn lazy(self) -> LazyVec<'a,T::Result> {
        LazyVec::Base(self)
    }
}

impl<'a,R : Clone,T : 'a + Lazy<'a,Result=R>> Lazy<'a> for LazyVec<'a,T> {
    type Result = Vec<T::Result>;
    fn base(r: Vec<T::Result>) -> LazyVec<'a,T> {
        LazyVec::Base(r)
    }
    fn eval(self) -> Vec<T::Result> {
        match self {
            LazyVec::Base(v) => v,
            LazyVec::BaseRef(v) => (*v).clone(),
            LazyVec::Insert(pos,el,lazy) => {
                let mut res = lazy.eval();
                res[pos] = el.eval();
                res
            }
        }
    }
}*/
