extern crate kravanenn;
extern crate serde;

use std::fs::File;
use std::io;
use std::io::{Write, Seek, SeekFrom};
use std::str::FromStr;
use kravanenn::*;
use kravanenn::ocaml::values::{Opaques, LibSum, Any, UnivOpaques, Lib};
use kravanenn::coq::checker::checker::{LoadPath};

fn main () {
  let args : Vec<String> = std::env::args().collect();
  let lp = LoadPath::new();
  kravanenn::coq::checker::checker::check(&lp, args.as_ref());
}
