extern crate num_bigint;
extern crate num_rational;

use self::num_bigint::BigInt;
use self::num_rational::Ratio;
use types::{SortKind};
use expr::{Expr,Function,OrdOp,ArithOp,BVOp};
use types::Value;
use embed::Embed;
use std::str;
use std::str::FromStr;
#[cfg(test)]
use test::{Simple};

#[derive(PartialEq,Debug)]
pub enum CheckSatResult {
    Sat, Unsat, Unknown
}

pub trait Parser : Embed {
    fn parse_var(&mut self,&[u8]) -> Result<Self::Var,Self::Error>;
    fn parse_fun(&mut self,&[u8]) -> Result<Self::Fun,Self::Error>;
}

#[derive(Debug,Clone,PartialEq,Eq)]
pub enum ParseError<Sort> {
    NumberNotOfSort(BigInt,Sort),
    InvalidNumberFormat(u8),
    ExpectedValue,
    ExpectedBV,
    ExpectedOpenPar,
    ExpectedClosePar,
    ExpectedUnderscore,
    TypeMismatch(Sort,Sort),
    WrongNumberOfArgs(usize,usize,bool),
    ExpectedNumeric(Sort),
    ExpectedBitVec(Sort),
    ExpectedId,
    ExpectedParFun,
    ExpectedArray,
    ExpectedAs,
    ExpectedConst,
    ExpectedSort,
    ExpectedLitBitVec,
    ExpectedArraySort(Sort),
    UnknownVar,
    UnknownFun,
    ExpectedLiteral(&'static[u8]),
    ExpectedQuote,
    InvalidUTF8,
    ExpectedCheckSatResult,
    ExpectedExpr
}

#[derive(Debug,PartialEq,Eq)]
pub enum PResult<'inp,R,P : Parser> {
    Done(R,&'inp[u8]),
    SyntaxError(ParseError<P::Sort>),
    EmbedError(P::Error),
    Incomplete
}

#[derive(Debug,Clone,PartialEq,Eq)]
pub struct Pos { pub line: usize,
                 pub col: usize }

#[inline]
fn eat_ws<'inp>(inp: &'inp[u8],pos: &mut Pos) -> &'inp[u8] {
    let mut off = 0;
    loop {
        if off >= inp.len() { return &inp[off..] }
        match inp[off] {
            b' ' | b'\t' => { pos.col+=1; }
            b'\n' => {
                pos.line+=1;
                pos.col=0;
            },
            _ => return &inp[off..]
        }
        off+=1;
    }
}

#[inline]
fn is_sym_char(c: u8) -> bool {
    c!=b' ' &&
        c!=b'\t' &&
        c!=b'\n' &&
        c!=b')' &&
        c!=b'('
}

pub fn parse_var<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P) -> PResult<'inp,P::Var,P> {
    if input.len()==0 {
        return PResult::Incomplete
    }
    let mut off = 0;
    loop {
        match input[off] {
            b' ' | b'\t' | b'\n' | b'(' | b')' => break,
            _ => {}
        }
        off+=1;
        if off >= input.len() { break }
    }
    match p.parse_var(&input[0..off]) {
        Ok(v) => {
            pos.col+=off;
            PResult::Done(v,&input[off..])
        },
        Err(e) => PResult::EmbedError(e)
    }
}

pub fn parse_fun<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P) -> PResult<'inp,P::Fun,P> {
    if input.len()==0 {
        return PResult::Incomplete
    }
    let mut off = 0;
    loop {
        match input[off] {
            b' ' | b'\t' | b'\n' | b'(' | b')' => break,
            _ => {}
        }
        off+=1;
        if off >= input.len() { break }
    }
    match p.parse_fun(&input[0..off]) {
        Ok(v) => {
            pos.col+=off;
            PResult::Done(v,&input[off..])
        },
        Err(e) => PResult::EmbedError(e)
    }
}

fn parse_expr<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P, hint: Option<&P::Sort>)
                               -> PResult<'inp,P::Expr,P> {
    let old_pos = pos.clone();
    match parse_value(input,pos,p,hint) {
        PResult::Done(v,ninp) => match p.embed(Expr::Const(v)) {
            Ok(e) => PResult::Done(e,ninp),
            Err(e) => PResult::EmbedError(e)
        },
        PResult::Incomplete => PResult::Incomplete,
        _ => if input[0]==b'(' {
            *pos = old_pos;
            pos.col+=1;
            let input1=eat_ws(&input[1..],pos);
            match parse_function(input1,pos,p,hint,0,
                                 &|inp,pos,p,n,indir,hint| {
                                     let rhint = if indir==0 { hint } else { None };
                                     let mut ninp = eat_ws(inp,pos);
                                     if n==0 {
                                         for _ in 0..indir {
                                             if ninp.len()==0 {
                                                 return PResult::Incomplete
                                             }
                                             if ninp[0]!=b')' {
                                                 return PResult::SyntaxError
                                                     (ParseError::ExpectedClosePar)
                                             }
                                             pos.col+=1;
                                             ninp = eat_ws(&ninp[1..],pos);
                                         }
                                     }
                                     if ninp.len()==0 {
                                         return PResult::Incomplete
                                     }
                                     if ninp[0]==b')' {
                                         pos.col+=1;
                                         return PResult::Done(None,&ninp[1..])
                                     }
                                     match parse_expr(ninp,pos,p,rhint) {
                                         PResult::Done(e,ninp2)
                                             => match p.type_of(&e) {
                                                 Err(e) => PResult::EmbedError(e),
                                                 Ok(tp) => {
                                                     let mut indices = Vec::new();
                                                     let mut ctp = tp;
                                                     for _ in 0..indir {
                                                         match p.unbed_sort(&ctp) {
                                                             Err(e) => return PResult::EmbedError(e),
                                                             Ok(SortKind::Array(idx,el)) => {
                                                                 ctp = el;
                                                                 indices.push(idx);
                                                             },
                                                             Ok(_) => return PResult::SyntaxError
                                                                 (ParseError::ExpectedArray)
                                                         }
                                                     }
                                                     PResult::Done(Some((ctp,e,indices)),ninp2)
                                                 }
                                             },
                                         PResult::Incomplete
                                             => PResult::Incomplete,
                                         PResult::SyntaxError(e)
                                             => PResult::SyntaxError(e),
                                         PResult::EmbedError(e)
                                             => PResult::EmbedError(e)
                                     }
                                 }) {
                PResult::Done((fun,mut args,_,complete),ninput) => {
                    let mut input1=ninput;
                    if !complete {
                        let mut narg=args.len();
                        loop {
                            input1 = eat_ws(input1,pos);
                            if input1.len()==0 {
                                return PResult::Incomplete
                            }
                            if input1[0]==b')' {
                                pos.col+=1;
                                input1=&input1[1..];
                                break
                            }
                            match fun.arg_sort(p,narg) {
                                Err(e) => return PResult::EmbedError(e),
                                Ok(srt) => match parse_expr(input1,pos,p,Some(&srt)) {
                                    PResult::Done(e,ninp) => {
                                        args.push(e);
                                        narg+=1;
                                        input1=ninp;
                                    },
                                    PResult::Incomplete
                                        => return PResult::Incomplete,
                                    PResult::EmbedError(e)
                                        => return PResult::EmbedError(e),
                                    PResult::SyntaxError(e)
                                        => return PResult::SyntaxError(e)
                                }
                            }
                        }
                        match fun.arity(p) {
                            Err(e) => return PResult::EmbedError(e),
                            Ok(ar) => if ar!=narg {
                                return PResult::SyntaxError
                                    (ParseError::WrongNumberOfArgs(narg,ar,false))
                            }
                        }
                    }
                    match p.embed(Expr::App(fun,args)) {
                        Err(e) => PResult::EmbedError(e),
                        Ok(res) => PResult::Done(res,input1)
                    }
                },
                PResult::Incomplete => PResult::Incomplete,
                PResult::EmbedError(e) => PResult::EmbedError(e),
                PResult::SyntaxError(e) => PResult::SyntaxError(e)
            }
        } else if is_sym_char(input[0]) {
            let mut off=1;
            while off<input.len() {
                if !is_sym_char(input[off]) { break }
                off+=1
            }
            match p.parse_var(&input[0..off]) {
                Ok(v) => match p.embed(Expr::Var(v)) {
                    Ok(rv) => {
                        pos.col+=off;
                        PResult::Done(rv,&input[off..])
                    },
                    Err(e) => PResult::EmbedError(e)
                },
                Err(e) => PResult::EmbedError(e)
            }
        } else {
            PResult::SyntaxError(ParseError::ExpectedExpr)
        }
    }
}

fn parse_function<'inp,P : Parser,F,Sub>(input: &'inp[u8],
                                         pos: &mut Pos,
                                         p: &mut P,
                                         hint: Option<&P::Sort>,
                                         indir: usize,
                                         rec: &F)
                                         -> PResult<'inp,(Function<P::Sort,P::Fun>,
                                                          Vec<Sub>,Vec<Vec<Vec<P::Sort>>>,bool),P>
    where F : Fn(&'inp[u8],
                 &mut Pos,
                 &mut P,
                 usize, // arg num
                 usize, // indir
                 Option<&P::Sort>) -> PResult<'inp,Option<(P::Sort,Sub,Vec<Vec<P::Sort>>)>,P> {
    if input.len()==0 {
        return PResult::Incomplete
    }
    if is_sym_char(input[0]) {
        let mut off=1;
        while off<input.len() {
            if !is_sym_char(input[off]) { break }
            off+=1;
        }
        match &input[0..off] {
            b"=" | b"distinct" => {
                let is_eq = input[0]==b'=';
                pos.col+=off;
                match rec(&input[off..],pos,p,0,indir,None) {
                    PResult::Done(Some((srt,sub,_)),ninp) => {
                        let mut narg = 1;
                        let mut args = Vec::with_capacity(2);
                        let mut indices = Vec::with_capacity(2);
                        let mut input1 = ninp;
                        args.push(sub);
                        loop {
                            match rec(input1,pos,p,narg,indir,Some(&srt)) {
                                PResult::Done(Some((srt1,sub1,idx1)),ninp) => {
                                    if srt!=srt1 {
                                        return PResult::SyntaxError
                                            (ParseError::TypeMismatch
                                             (srt,srt1))
                                    }
                                    narg+=1;
                                    args.push(sub1);
                                    indices.push(idx1);
                                    input1=ninp;
                                },
                                PResult::Done(None,ninp)
                                    => { input1=ninp;
                                         break },
                                PResult::Incomplete
                                    => return PResult::Incomplete,
                                PResult::SyntaxError(e)
                                    => return PResult::SyntaxError(e),
                                PResult::EmbedError(e)
                                    => return PResult::EmbedError(e)
                            }
                        }
                        PResult::Done((if is_eq {Function::Eq(srt,
                                                              args.len())}
                                       else {Function::Distinct(srt,
                                                                args.len())},
                                       args,indices,true),
                                      input1)
                    },
                    PResult::Done(None,_)
                        => PResult::SyntaxError
                        (ParseError::WrongNumberOfArgs(0,1,true)),
                    PResult::Incomplete
                        => PResult::Incomplete,
                    PResult::SyntaxError(e)
                        => PResult::SyntaxError(e),
                    PResult::EmbedError(e)
                        => PResult::EmbedError(e)
                }
            },
            b"<" | b">" | b"<=" | b">=" => {
                let op = match &input[0..off] {
                    b"<" => OrdOp::Lt,
                    b">" => OrdOp::Gt,
                    b"<=" => OrdOp::Le,
                    b">=" => OrdOp::Ge,
                    _ => unreachable!()
                };
                pos.col+=off;
                match rec(&input[off..],pos,p,0,indir,None) {
                    PResult::Done(None,_)
                        => PResult::SyntaxError
                        (ParseError::WrongNumberOfArgs(0,2,false)),
                    PResult::Done(Some((tp,sub,_)),ninp) => match p.unbed_sort(&tp) {
                        Err(e) => PResult::EmbedError(e),
                        Ok(SortKind::Int)
                            => PResult::Done((Function::OrdInt(op),
                                              vec![sub],vec![vec![]],false),ninp),
                        Ok(SortKind::Real)
                            => PResult::Done((Function::OrdReal(op),
                                              vec![sub],vec![vec![]],false),ninp),
                        Ok(_) => PResult::SyntaxError
                            (ParseError::ExpectedNumeric(tp))
                    },
                    PResult::Incomplete => PResult::Incomplete,
                    PResult::EmbedError(e) => PResult::EmbedError(e),
                    PResult::SyntaxError(e) => PResult::SyntaxError(e)
                }
            },
            b"+" | b"-" | b"*" => {
                let op = match input[0] {
                    b'+' => ArithOp::Add,
                    b'-' => ArithOp::Sub,
                    b'*' => ArithOp::Mult,
                    _ => unreachable!()
                };
                pos.col+=1;
                match hint {
                    Some(srt) => match p.unbed_sort(srt) {
                        Err(e) => PResult::EmbedError(e),
                        Ok(SortKind::Int)
                            => PResult::Done((Function::ArithInt(op,2),
                                              vec![],vec![],false),
                                             &input[off..]),
                        Ok(SortKind::Real)
                            => PResult::Done((Function::ArithReal(op,2),
                                              vec![],vec![],false),
                                             &input[off..]),
                        Ok(_) => PResult::SyntaxError
                            (ParseError::ExpectedNumeric(srt.clone()))
                    },
                    None => match rec(&input[1..],pos,p,0,indir,None) {
                        PResult::Done(None,_)
                            => PResult::SyntaxError
                            (ParseError::WrongNumberOfArgs(0,2,false)),
                        PResult::Done(Some((tp,sub,idx)),ninp) => {
                            let mut args = vec![sub];
                            let mut indices = vec![idx];
                            let mut input1 = ninp;
                            let mut narg = 1;
                            loop {
                                match rec(input1,pos,p,narg,indir,Some(&tp)) {
                                    PResult::Done(None,ninp) => {
                                        input1 = ninp;
                                        break
                                    },
                                    PResult::Done(Some((tp2,sub,idx)),ninp) => {
                                        if tp!=tp2 {
                                            return PResult::SyntaxError
                                                (ParseError::TypeMismatch(tp2,tp))
                                        }
                                        input1 = ninp;
                                        args.push(sub);
                                        indices.push(idx);
                                        narg+=1;
                                    },
                                    PResult::Incomplete => return PResult::Incomplete,
                                    PResult::EmbedError(e) => return PResult::EmbedError(e),
                                    PResult::SyntaxError(e) => return PResult::SyntaxError(e)
                                }
                            }
                            match p.unbed_sort(&tp) {
                                Err(e) => PResult::EmbedError(e),
                                Ok(SortKind::Int)
                                    => PResult::Done(
                                        (Function::ArithInt(op,args.len()),
                                         args,indices,true),input1),
                                Ok(SortKind::Real)
                                    => PResult::Done(
                                        (Function::ArithReal(op,args.len()),
                                         args,indices,true),ninp),
                                Ok(_) => PResult::SyntaxError
                                    (ParseError::ExpectedNumeric(tp))
                            }
                        },
                        PResult::Incomplete => PResult::Incomplete,
                        PResult::EmbedError(e) => PResult::EmbedError(e),
                        PResult::SyntaxError(e) => PResult::SyntaxError(e)
                    }
                }
            },
            b"div" => {
                pos.col+=off;
                PResult::Done((Function::Div,vec![],vec![],false),
                              &input[off..])
            },
            b"mod" => {
                pos.col+=off;
                PResult::Done((Function::Mod,vec![],vec![],false),
                              &input[off..])
            },
            b"rem" => {
                pos.col+=off;
                PResult::Done((Function::Rem,vec![],vec![],false),
                              &input[off..])
            },
            b"exp" => {
                pos.col+=off;
                PResult::Done((Function::Exp,vec![],vec![],false),
                              &input[off..])
            },
            b"/" => {
                pos.col+=off;
                PResult::Done((Function::Divide,vec![],vec![],false),
                              &input[off..])
            },
            b"abs" => {
                pos.col+=off;
                match hint {
                    Some(srt) => match p.unbed_sort(srt) {
                        Err(e) => PResult::EmbedError(e),
                        Ok(SortKind::Int)
                            => PResult::Done((Function::AbsInt,vec![],vec![],false),
                                             &input[off..]),
                        Ok(SortKind::Real)
                            => PResult::Done((Function::AbsReal,vec![],vec![],false),
                                             &input[off..]),
                        Ok(_) => PResult::SyntaxError
                            (ParseError::ExpectedNumeric(srt.clone()))
                    },
                    None => match rec(&input[off..],pos,p,0,indir,None) {
                        PResult::Done(None,_)
                            => PResult::SyntaxError
                            (ParseError::WrongNumberOfArgs(0,1,false)),
                        PResult::Done(Some((srt,sub,idx)),ninp)
                            => match p.unbed_sort(&srt) {
                                Err(e) => PResult::EmbedError(e),
                                Ok(SortKind::Int)
                                    => PResult::Done((Function::AbsInt,
                                                      vec![sub],vec![idx],false),
                                                     ninp),
                                Ok(SortKind::Real)
                                    => PResult::Done((Function::AbsReal,
                                                      vec![sub],vec![idx],false),
                                                     ninp),
                                Ok(_) => PResult::SyntaxError
                                    (ParseError::ExpectedNumeric(srt))
                            },
                        PResult::Incomplete => PResult::Incomplete,
                        PResult::EmbedError(e) => PResult::EmbedError(e),
                        PResult::SyntaxError(e) => PResult::SyntaxError(e)
                    }
                }
            },
            b"not" => {
                pos.col+=off;
                PResult::Done((Function::Not,vec![],vec![],false),
                              &input[off..])
            },
            b"and" | b"or" | b"xor" | b"=>" => match p.embed_sort(SortKind::Bool) {
                Err(e) => PResult::EmbedError(e),
                Ok(srt) => {
                    pos.col+=off;
                    let mut args = Vec::new();
                    let mut indices = Vec::new();
                    let mut narg = 0;
                    let mut input1 = &input[off..];
                    loop {
                        match rec(input1,pos,p,narg,indir,Some(&srt)) {
                            PResult::Done(None,ninp) => {
                                input1 = ninp;
                                break
                            },
                            PResult::Done(Some((_,sub,idx)),ninp) => {
                                args.push(sub);
                                indices.push(idx);
                                narg+=1;
                                input1=ninp;
                            },
                            PResult::Incomplete => return PResult::Incomplete,
                            PResult::EmbedError(e)
                                => return PResult::EmbedError(e),
                            PResult::SyntaxError(e)
                                => return PResult::SyntaxError(e)
                        }
                    }
                    let op = match &input[0..off] {
                        b"and" => Function::And(narg),
                        b"or" => Function::Or(narg),
                        b"xor" => Function::XOr(narg),
                        b"=>" => Function::Implies(narg),
                        _ => unreachable!()
                    };
                    PResult::Done((op,args,indices,true),input1)
                }
            },
            b"to-real" => {
                pos.col+=off;
                PResult::Done((Function::ToReal,vec![],vec![],false),
                              &input[off..])
            },
            b"to-int" => {
                pos.col+=off;
                PResult::Done((Function::ToInt,vec![],vec![],false),
                              &input[off..])
            },
            b"ite" => {
                pos.col+=off;
                match hint {
                    Some(srt) => PResult::Done((Function::ITE(srt.clone()),
                                                vec![],vec![],false),
                                               &input[off..]),
                    None => match p.embed_sort(SortKind::Bool) {
                        Err(e) => PResult::EmbedError(e),
                        Ok(tp_b) => match rec(&input[off..],pos,p,0,indir,Some(&tp_b)) {
                            PResult::Done(None,_)
                                => PResult::SyntaxError
                                (ParseError::WrongNumberOfArgs(0,3,false)),
                            PResult::Incomplete => PResult::Incomplete,
                            PResult::EmbedError(e) => PResult::EmbedError(e),
                            PResult::SyntaxError(e) => PResult::SyntaxError(e),
                            PResult::Done(Some((_,cond,cidx)),input1)
                                => match rec(input1,pos,p,1,indir,None) {
                                    PResult::Done(None,_)
                                        => PResult::SyntaxError
                                        (ParseError::WrongNumberOfArgs(0,3,false)),
                                    PResult::Incomplete => PResult::Incomplete,
                                    PResult::EmbedError(e) => PResult::EmbedError(e),
                                    PResult::SyntaxError(e) => PResult::SyntaxError(e),
                                    PResult::Done(Some((srt,lhs,lidx)),input2)
                                        => PResult::Done
                                        ((Function::ITE(srt),vec![cond,lhs],vec![cidx,lidx],false),
                                         input2)
                                }
                        }
                    }
                }
            },
            b"bvule" | b"bvult" | b"bvuge" | b"bvugt" |
            b"bvsle" | b"bvslt" | b"bvsge" | b"bvsgt" |
            b"bvadd" | b"bvsub" | b"bvmul" |
            b"bvurem" | b"bvsrem" | b"bvudiv" | b"bvsdiv" |
            b"bvshl" | b"bvlshr" | b"bvashr" |
            b"bvxor" | b"bvand" | b"bvor" |
            b"bvnot" | b"bvneg" => {
                pos.col+=off;
                let op = match &input[3..off] {
                    b"uge" => BVOp::Ord(false,OrdOp::Ge),
                    b"ugt" => BVOp::Ord(false,OrdOp::Gt),
                    b"ule" => BVOp::Ord(false,OrdOp::Le),
                    b"ult" => BVOp::Ord(false,OrdOp::Lt),
                    b"sge" => BVOp::Ord(true,OrdOp::Ge),
                    b"sgt" => BVOp::Ord(true,OrdOp::Gt),
                    b"sle" => BVOp::Ord(true,OrdOp::Le),
                    b"slt" => BVOp::Ord(true,OrdOp::Lt),
                    b"add" => BVOp::Arith(ArithOp::Add),
                    b"sub" => BVOp::Arith(ArithOp::Sub),
                    b"mul" => BVOp::Arith(ArithOp::Mult),
                    b"urem" => BVOp::Rem(false),
                    b"srem" => BVOp::Rem(true),
                    b"udiv" => BVOp::Div(false),
                    b"sdiv" => BVOp::Div(true),
                    b"shl" => BVOp::SHL,
                    b"lshr" => BVOp::LSHR,
                    b"ashr" => BVOp::ASHR,
                    b"xor" => BVOp::XOr,
                    b"and" => BVOp::And,
                    b"or" => BVOp::Or,
                    b"not" => BVOp::Not,
                    b"neg" => BVOp::Neg,
                    _ => unreachable!()
                };
                let arity = match &input[2..off] {
                    b"not" | b"neg" => 1,
                    _ => 2
                };
                let is_ord = match op {
                    BVOp::Ord(_,_) => true,
                    _ => false
                };
                let sz = if is_ord {
                    match hint {
                        None => None,
                        Some(srt) => match p.unbed_sort(srt) {
                            Err(e) => return PResult::EmbedError(e),
                            Ok(SortKind::BitVec(sz)) => Some(sz),
                            Ok(_) => return PResult::SyntaxError
                                (ParseError::ExpectedBitVec(srt.clone()))
                        }
                    }
                } else { None };

                let (nsz,args,indices,input1) = match sz {
                    Some(s) => (s,vec![],vec![],&input[off..]),
                    None => match rec(&input[off..],pos,p,0,indir,None) {
                        PResult::Done(None,_)
                            => return PResult::SyntaxError
                            (ParseError::WrongNumberOfArgs(0,arity,false)),
                        PResult::Done(Some((srt,sub,idx)),ninp)
                            => match p.unbed_sort(&srt) {
                                Err(e) => return PResult::EmbedError(e),
                                Ok(SortKind::BitVec(sz))
                                    => (sz,vec![sub],vec![idx],ninp),
                                Ok(_) => return PResult::SyntaxError
                                    (ParseError::ExpectedBitVec(srt))
                            },
                        PResult::Incomplete => return PResult::Incomplete,
                        PResult::EmbedError(e) => return PResult::EmbedError(e),
                        PResult::SyntaxError(e) => return PResult::SyntaxError(e)
                    }
                };
                PResult::Done((Function::BV(nsz,op),args,indices,false),input1)
            },
            _ => match p.parse_fun(&input[0..off]) {
                Ok(fun) => {
                    pos.col+=off;
                    PResult::Done((Function::Fun(fun),vec![],vec![],false),
                                  &input[off..])
                },
                Err(e) => PResult::EmbedError(e)
            }
        }
    } else if input[0]==b'(' {
        // parametric function
        pos.col+=1;
        let input1 = eat_ws(&input[1..],pos);
        if input1.len()==0 {
            return PResult::Incomplete
        }
        if input1[0]==b'_' {
            pos.col+=1;
            let input2 = eat_ws(&input1[1..],pos);
            if input2.len()==0 {
                return PResult::Incomplete
            }
            if !is_sym_char(input2[0]) {
                return PResult::SyntaxError(ParseError::ExpectedId)
            }
            let mut off=1;
            while off<input2.len() {
                if !is_sym_char(input2[off]) { break }
                off+=1;
            }
            match &input2[0..off] {
                b"map" => {
                    pos.col+=off;
                    let input3 = eat_ws(&input2[off..],pos);
                    match parse_function(input3,pos,p,None,indir+1,rec) {
                        PResult::Done((fun,mut subs,mut indices,all),input4) => {
                            let mut input5 = input4;
                            //Identify the index type
                            if subs.len()==0 {
                                debug_assert!(!all);
                                match rec(&input5,pos,p,0,indir+1,None) {
                                    PResult::Done(None,_) => {
                                        let arity = match fun.arity(p) {
                                            Err(e) => return PResult::EmbedError(e),
                                            Ok(n) => n
                                        };
                                        return PResult::SyntaxError(ParseError::WrongNumberOfArgs(0,arity,false))
                                    },
                                    PResult::Done(Some((_,sub,ind)),input6) => {
                                        subs.push(sub);
                                        indices.push(ind);
                                        input5 = input6;
                                    },
                                    PResult::Incomplete => return PResult::Incomplete,
                                    PResult::EmbedError(e) => return PResult::EmbedError(e),
                                    PResult::SyntaxError(e) => return PResult::SyntaxError(e)
                                }
                            }
                            let idx = indices[0][0].clone();
                            PResult::Done((Function::Map(Box::new(fun),idx),subs,indices,all),input5)
                        },
                        PResult::Incomplete => PResult::Incomplete,
                        PResult::EmbedError(e) => PResult::EmbedError(e),
                        PResult::SyntaxError(e) => PResult::SyntaxError(e)
                    }
                },
                _ => PResult::SyntaxError(ParseError::ExpectedParFun)
            }
        } else if input1[0]==b'a' {
            if input1.len() < 3 {
                return PResult::Incomplete
            }
            if input1[1]!=b's' || (input1[2]!=b' ' && input1[2]!=b'\t' && input1[2]!=b'\n') {
                return PResult::SyntaxError(ParseError::ExpectedAs)
            }
            pos.col+=2;
            let input2 = eat_ws(&input1[2..],pos);
            if input2.len() < 6 {
                return PResult::Incomplete
            }
            if input2[0..5]!=b"const"[..] || (input2[5]!=b' ' && input2[5]!=b'\t' && input2[5]!=b'\n') {
                return PResult::SyntaxError(ParseError::ExpectedConst)
            }
            pos.col+=5;
            let input3 = eat_ws(&input2[5..],pos);
            match parse_sort(input3,pos,p) {
                PResult::Incomplete => PResult::Incomplete,
                PResult::EmbedError(e) => PResult::EmbedError(e),
                PResult::SyntaxError(e) => PResult::SyntaxError(e),
                PResult::Done(srt,input4) => {
                    match p.unbed_sort(&srt) {
                        Err(e) => PResult::EmbedError(e),
                        Ok(SortKind::Array(idx,el)) => {
                            let input5 = eat_ws(input4,pos);
                            if input5.len()==0 {
                                return PResult::Incomplete
                            }
                            if input5[0]!=b')' {
                                return PResult::SyntaxError(ParseError::ExpectedClosePar)
                            }
                            PResult::Done((Function::ConstArray(idx,el),vec![],vec![],false),&input5[1..])
                        },
                        Ok(_) => PResult::SyntaxError(ParseError::ExpectedArraySort(srt))
                    }
                }
            }
        } else {
            unimplemented!()
        }
    } else {
        unimplemented!()
    }
}

fn parse_sort<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P) -> PResult<'inp,P::Sort,P> {
    if input.len()<3 {
        return PResult::Incomplete
    }
    if &input[0..3]==b"Int" {
        pos.col+=3;
        match p.embed_sort(SortKind::Int) {
            Err(e) => return PResult::EmbedError(e),
            Ok(tp) => return PResult::Done(tp,&input[3..])
        }
    }
    if input.len()<4 {
        return PResult::Incomplete
    }
    if &input[0..4]==b"Bool" {
        pos.col+=4;
        match p.embed_sort(SortKind::Bool) {
            Err(e) => return PResult::EmbedError(e),
            Ok(tp) => return PResult::Done(tp,&input[4..])
        }
    }
    if &input[0..4]==b"Real" {
        pos.col+=4;
        match p.embed_sort(SortKind::Real) {
            Err(e) => return PResult::EmbedError(e),
            Ok(tp) => return PResult::Done(tp,&input[4..])
        }
    }
    if input[0]==b'(' {
        pos.col+=1;
        let input1 = eat_ws(&input[1..],pos);
        if input1.len()==0 {
            return PResult::Incomplete
        }
        if input1[0]==b'_' {
            let input2 = eat_ws(&input1[1..],pos);
            if input2.len() < 6 {
                return PResult::Incomplete
            }
            if &input2[0..6] != b"BitVec" {
                return PResult::SyntaxError(ParseError::ExpectedLitBitVec)
            }
            pos.col+=6;
            let input3 = eat_ws(&input2[6..],pos);
            let mut off = 0;
            loop {
                if off>=input3.len() {
                    return PResult::Incomplete
                }
                if !(input3[off] as char).is_digit(10) {
                    break
                }
                off+=1;
            }
            let bw = match str::from_utf8(&input3[0..off]) {
                Err(_) => panic!("Internal error: Cannot parse {:?} to &str",&input3[0..off]),
                Ok(sz) => match FromStr::from_str(sz) {
                    Err(_) => panic!("Internal error: Cannot parse {:?} to usize",sz),
                    Ok(rsz) => rsz
                }
            };
            pos.col+=off;
            let input4 = eat_ws(&input3[off..],pos);
            if input4.len()==0 {
                return PResult::Incomplete
            }
            if input4[0]!=b')' {
                return PResult::SyntaxError(ParseError::ExpectedClosePar)
            }
            pos.col+=1;
            match p.embed_sort(SortKind::BitVec(bw)) {
                Err(e) => return PResult::EmbedError(e),
                Ok(tp) => return PResult::Done(tp,&input4[1..])
            }
        }
        if input1.len() < 5 {
            return PResult::Incomplete
        }
        if input1[0..5]==b"Array"[..] {
            pos.col+=5;
            let input2 = eat_ws(&input1[5..],pos);
            match parse_sort(input2,pos,p) {
                PResult::Incomplete => return PResult::Incomplete,
                PResult::EmbedError(e) => return PResult::EmbedError(e),
                PResult::SyntaxError(e) => return PResult::SyntaxError(e),
                PResult::Done(tp,input3) => {
                    let mut indices = Vec::new();
                    let mut last = tp;
                    let mut input4 = eat_ws(&input3,pos);
                    loop {
                        if input4.len()==0 {
                            return PResult::Incomplete
                        }
                        if input4[0]==b')' {
                            pos.col+=1;
                            input4 = &input4[1..];
                            break;
                        }
                        match parse_sort(input4,pos,p) {
                            PResult::Done(tp,ninp) => {
                                indices.push(last);
                                last = tp;
                                input4 = eat_ws(ninp,pos);
                            },
                            PResult::Incomplete => return PResult::Incomplete,
                            PResult::EmbedError(e) => return PResult::EmbedError(e),
                            PResult::SyntaxError(e) => return PResult::SyntaxError(e)
                        }
                    }
                    match p.embed_sort(SortKind::Array(indices,last)) {
                        Err(e) => return PResult::EmbedError(e),
                        Ok(tp) => return PResult::Done(tp,input4)
                    }
                }
            }
        }
    }
    return PResult::SyntaxError(ParseError::ExpectedSort)
}

fn parse_value<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P, hint: Option<&P::Sort>)
                                -> PResult<'inp,Value,P> {
    if input.len()==0 {
        return PResult::Incomplete
    }
    if (input[0] as char).is_digit(10) {
        // Num constant parsing
        pos.col+=1;
        let mut off = 1;
        loop {
            if !(input[off] as char).is_digit(10) {
                break
            }
            off+=1;
            if off >= input.len() { break }
        }
        match BigInt::parse_bytes(&input[0..off],10) {
            None => panic!("Internal error: Cannot parse {:?} to BigInt",&input[0..off]),
            Some(v) => match hint {
                Some(srt) => match p.unbed_sort(srt) {
                    Err(e) => PResult::EmbedError(e),
                    Ok(SortKind::Int) => {
                        pos.col+=off;
                        PResult::Done(Value::Int(v),&input[off..])
                    },
                    Ok(SortKind::Real) => {
                        pos.col+=off;
                        PResult::Done(Value::Real(Ratio::from(v)),&input[off..])
                    },
                    Ok(SortKind::BitVec(sz)) => {
                        pos.col+=off;
                        PResult::Done(Value::BitVec(sz,v),&input[off..])
                    },
                    Ok(_) => PResult::SyntaxError(ParseError::NumberNotOfSort(v,(*srt).clone()))
                },
                None => {
                    pos.col+=off;
                    PResult::Done(Value::Int(v),&input[off..])
                }
            }
        }
    } else if input[0]==b'#' {
        pos.col+=1;
        if input.len() < 2 { return PResult::Incomplete }
        match input[1] {
            b'x' => {
                pos.col+=1;
                let mut off = 2;
                while off < input.len() {
                    if !(input[off] as char).is_digit(16) { break; }
                    off+=1;
                }
                match BigInt::parse_bytes(&input[2..off],16) {
                    None => panic!("Internal error: Cannot parse {:?} to BigInt",&input[2..off]),
                    Some(v) => {
                        pos.col+=off-2;
                        PResult::Done(Value::BitVec((off-2)*4,v),&input[off..])
                    }
                }
            },
            b'b' => {
                pos.col+=1;
                let mut off = 2;
                while off < input.len() {
                    if input[off]!=b'0' &&
                        input[off]!=b'1' { break }
                    off+=1;
                }
                match BigInt::parse_bytes(&input[2..off],2) {
                    None => panic!("Internal error: Cannot parse {:?} to BigInt",&input[2..off]),
                    Some(v) => {
                        pos.col+=off-2;
                        PResult::Done(Value::BitVec((off-2),v),&input[off..])
                    }
                }
            },
            c => PResult::SyntaxError(ParseError::InvalidNumberFormat(c))
        }
    } else if (input.len()==4 ||
               (input.len()>4 && !is_sym_char(input[4]))) && &input[0..4]==&b"true"[..] {
        pos.col+=4;
        PResult::Done(Value::Bool(true),&input[4..])
    } else if (input.len()==5 ||
               (input.len()>5 && !is_sym_char(input[5]))) && &input[0..5]==&b"false"[..] {
        pos.col+=4;
        PResult::Done(Value::Bool(false),&input[5..])
    } else if input[0]==b'(' {
        pos.col+=1;
        let input1 = eat_ws(&input[1..],pos);
        if input1.len()<1 {
            return PResult::Incomplete
        }
        if input1[0]!=b'_' {
            return PResult::SyntaxError(ParseError::ExpectedUnderscore)
        }
        pos.col+=1;
        let input2 = eat_ws(&input1[1..],pos);
        if input2.len()<3 {
            return PResult::Incomplete
        }
        if input2[0]!=b'b' || input2[1]!=b'v' {
            return PResult::SyntaxError(ParseError::ExpectedBV)
        }
        pos.col+=2;
        let mut off = 2;
        while off < input2.len() {
            if !(input2[off] as char).is_digit(10) { break }
            off+=1;
        }
        if off==2 {
            return PResult::Incomplete
        }
        match BigInt::parse_bytes(&input2[2..off],10) {
            None => panic!("Internal error: Cannot parse {:?} to BigInt",&input2[2..off]),
            Some(v) => {
                pos.col+=off;
                let input3 = eat_ws(&input2[off..],pos);
                off=0;
                while off<input3.len() {
                    if !(input3[off] as char).is_digit(10) { break }
                    off+=1;
                }
                if off==0 {
                    return PResult::Incomplete
                }
                match str::from_utf8(&input3[0..off]) {
                    Err(_) => panic!("Internal error: Cannot parse {:?} into &str",&input3[0..off]),
                    Ok(sz) => match FromStr::from_str(sz) {
                        Err(_) => panic!("Internal error: Cannot parse {:?} into usize",sz),
                        Ok(rsz) => {
                            pos.col+=off;
                            let input4 = eat_ws(&input3[off..],pos);
                            if input4.len()==0 {
                                return PResult::Incomplete
                            }
                            if input4[0]==b')' {
                                pos.col+=1;
                                PResult::Done(Value::BitVec(rsz,v),
                                              &input4[1..])
                            } else {
                                PResult::SyntaxError(ParseError::ExpectedClosePar)
                            }
                        }
                    }
                }
            }
        }
    } else {
        PResult::SyntaxError(ParseError::ExpectedValue)
    }
}

pub fn parse_info_response_name<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P)
                                                 -> PResult<'inp,String,P> {
    parse_info_response(b"name",input,pos,p)
}

pub fn parse_info_response_version<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P)
                                                    -> PResult<'inp,String,P> {
    parse_info_response(b"version",input,pos,p)
}


fn parse_info_response<'inp,P : Parser>(info: &'static[u8],input: &'inp[u8],pos: &mut Pos,_: &mut P)
                                        -> PResult<'inp,String,P> {
    if input.len()==0 {
        return PResult::Incomplete
    }
    if input[0]!=b'(' {
        return PResult::SyntaxError(ParseError::ExpectedOpenPar)
    }
    pos.col+=1;
    let input1 = eat_ws(&input[1..],pos);
    if input1.len()<info.len()+1 {
        return PResult::Incomplete
    }
    if &input1[1..info.len()+1]!=info {
        return PResult::SyntaxError(ParseError::ExpectedLiteral(info))
    }
    pos.col+=1+info.len();
    let input2 = eat_ws(&input1[info.len()+1..],pos);
    if input2.len()<2 {
        return PResult::Incomplete
    }
    if input2[0]!=b'"' {
        return PResult::SyntaxError(ParseError::ExpectedQuote)
    }
    let mut off=1;
    // FIXME: Handle escaped chars
    loop {
        if input2.len() <= off {
            return PResult::Incomplete
        }
        if input2[off]==b'\\' {
            off+=1;
            if input2.len()<=off {
                return PResult::Incomplete
            }
        } else if input2[off]==b'"' {
            break
        }
        off+=1;
    }
    let resp = match str::from_utf8(&input2[1..off]) {
        Err(_) => return PResult::SyntaxError(ParseError::InvalidUTF8),
        Ok(r) => r
    };
    pos.col+=off+1;
    let input3 = eat_ws(&input2[off+1..],pos);
    if input3.len()==0 {
        return PResult::Incomplete
    }
    if input3[0]!=b')' {
        return PResult::SyntaxError(ParseError::ExpectedClosePar)
    }
    pos.col+=1;
    return PResult::Done(String::from(resp),&input3[1..])
}

pub fn parse_checksat_result<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,_: &mut P)
                                              -> PResult<'inp,CheckSatResult,P> {
    if input.len() < 3 {
        return PResult::Incomplete
    }
    if &input[0..3]==b"sat" {
        pos.col+=3;
        return PResult::Done(CheckSatResult::Sat,&input[3..])
    }
    if input.len() < 5 {
        return PResult::Incomplete
    }
    if &input[0..5]==b"unsat" {
        pos.col+=5;
        return PResult::Done(CheckSatResult::Unsat,&input[5..])
    }
    if input.len() < 7 {
        return PResult::Incomplete
    }
    if &input[0..7]==b"unknown" {
        pos.col+=7;
        return PResult::Done(CheckSatResult::Unknown,&input[7..])
    }
    return PResult::SyntaxError(ParseError::ExpectedCheckSatResult)
}

pub fn parse_get_value_result<'inp,P : Parser>(input: &'inp[u8],pos: &mut Pos,p: &mut P,hint: &P::Sort)
                                               -> PResult<'inp,Value,P> {
    if input.len()==0 {
        return PResult::Incomplete
    }
    if input[0]!=b'(' {
        return PResult::SyntaxError(ParseError::ExpectedOpenPar)
    }
    pos.col+=1;
    let input1=eat_ws(&input[1..],pos);
    if input1.len()==0 {
        return PResult::Incomplete
    }
    if input1[0]!=b'(' {
        return PResult::SyntaxError(ParseError::ExpectedOpenPar)
    }
    pos.col+=1;
    let input2 = eat_ws(&input1[1..],pos);
    let (_,input3) = match parse_expr(input2,pos,p,Some(hint)) {
        PResult::Done(e,ninp) => (e,ninp),
        PResult::Incomplete => return PResult::Incomplete,
        PResult::SyntaxError(e) => return PResult::SyntaxError(e),
        PResult::EmbedError(e) => return PResult::EmbedError(e)
    };
    let input4 = eat_ws(input3,pos);
    let (val,input5) = match parse_value(input4,pos,p,Some(hint)) {
        PResult::Done(res,ninp) => (res,ninp),
        err => return err
    };
    let input6 = eat_ws(input5,pos);
    if input6.len()==0 {
        return PResult::Incomplete
    }
    if input6[0]!=b')' {
        return PResult::SyntaxError(ParseError::ExpectedClosePar)
    }
    pos.col+=1;
    let input7 = eat_ws(input6,pos);
    if input7[0]!=b')' {
        return PResult::SyntaxError(ParseError::ExpectedClosePar)
    }
    pos.col+=1;
    PResult::Done(val,&input7[1..])
}

#[cfg(test)]
fn test_parser_() -> Result<(),()> {
    let mut simp = Simple::new();

    let e1 = simp.embed(Expr::Const(Value::Int(BigInt::from(123))))?;
    let mut pos = Pos { col: 0, line: 0 };

    assert_eq!(parse_expr(b"123",&mut pos,&mut simp,None),
               PResult::Done(e1,&b""[..]));

    let e2 = simp.embed(Expr::Const(Value::BitVec(32,BigInt::from(36232))))?;
    assert_eq!(parse_expr(b"#x00008D88",&mut pos,&mut simp,None),
               PResult::Done(e2.clone(),&b""[..]));
    assert_eq!(parse_expr(b"( _  bv36232 32  )",&mut pos,&mut simp,None),
               PResult::Done(e2.clone(),&b""[..]));
    let bv32 = simp.tp_bitvec(32)?;
    let e3 = simp.embed(Expr::App(Function::Distinct(bv32,2),
                                  vec![e2.clone(),e2.clone()]))?;
    assert_eq!(parse_expr(b"(distinct (_ bv36232 32) #x00008D88)",&mut pos,&mut simp,None),
               PResult::Done(e3.clone(),&b""[..]));
    let tbool = simp.tp_bool()?;
    let tint = simp.tp_int()?;
    let e4 = simp.embed(Expr::Const(Value::Int(BigInt::from(5))))?;
    let e5 = simp.embed(Expr::App(Function::ConstArray(vec![tbool.clone()],tint),
                                  vec![e4]))?;
    let e6 = simp.embed(Expr::App(Function::Map(Box::new(Function::ArithInt(ArithOp::Add,2)),
                                                vec![tbool]),
                                  vec![e5.clone(),e5]))?;

    assert_eq!(parse_expr(b"((_ map +) ((as const (Array Bool Int)) 5) ((as const (Array Bool Int)) 5))",
                          &mut pos,&mut simp,None),
               PResult::Done(e6.clone(),&b""[..]));
    Ok(())
}

#[test]
fn test_parser() {
    test_parser_();
}
