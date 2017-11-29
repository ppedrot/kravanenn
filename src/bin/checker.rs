extern crate kravanenn;
extern crate serde;

use std::fs::File;
use std::io;
use std::io::{Write, Seek, SeekFrom};
use std::str::FromStr;
use kravanenn::*;
use kravanenn::ocaml::values::{Opaques, LibSum, Any, UnivOpaques, Lib};

fn main () {
  let args : Vec<String> = std::env::args().collect();
  kravanenn::coq::checker::checker::check(args.as_ref());
}
