// #![feature(placement_in_syntax)]
// #![feature(const_fn)]
#![feature(rc_downcast)]
#![feature(try_from)]
#![feature(try_trait)]
#![feature(nonzero)]
#![feature(never_type)]
#![feature(drain_filter)]
extern crate fixedbitset;
#[macro_use] extern crate serde_state as serde;
#[macro_use] extern crate serde_derive_state;

extern crate core;
extern crate vec_map;
extern crate typed_arena;

#[macro_use]
extern crate bitflags;

pub mod ocaml;
pub mod coq;
pub mod hopcroft;
