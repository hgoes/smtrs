extern crate num_bigint;
extern crate num_rational;
extern crate num_traits;

pub mod embed;
pub mod parser;
pub mod composite;
pub mod domain;
pub mod unique;
pub mod types;
pub mod expr;
pub mod backend;
pub mod lazy;
pub mod simplify;
#[cfg(test)]
mod test;
