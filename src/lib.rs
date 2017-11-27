// #![feature(placement_in_syntax)]
#![feature(const_fn)]
#![feature(rc_downcast)]
#![feature(try_from)]
#![feature(try_trait)]
#![feature(nonzero)]
#![feature(never_type)]
#![feature(drain_filter)]
#![feature(generic_param_attrs)]
extern crate fixedbitset;
#[macro_use] extern crate serde_state as serde;
#[macro_use] extern crate serde_derive_state;

extern crate core;
extern crate cuckoo;
extern crate lazy_init;
extern crate movecell;
// extern crate rayon;
extern crate smallvec;
extern crate take_mut;
extern crate typed_arena;
extern crate vec_map;

#[macro_use]
extern crate bitflags;

pub mod ocaml;
pub mod coq;
pub mod hopcroft;
pub mod util;
