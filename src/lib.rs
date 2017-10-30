// #![feature(placement_in_syntax)]
// #![feature(const_fn)]
#![feature(rc_downcast)]
extern crate fixedbitset;
#[macro_use] extern crate serde_state as serde;
#[macro_use] extern crate serde_derive_state;

extern crate vec_map;

pub mod ocaml;
pub mod hopcroft;
