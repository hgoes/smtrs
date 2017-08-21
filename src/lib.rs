extern crate num_bigint;
extern crate num_rational;

pub mod embed;
pub mod parser;
pub mod composite;
pub mod domain;
pub mod unique;
pub mod types;
pub mod expr;
pub mod backend;
pub mod lazy;
#[cfg(test)]
mod test;
