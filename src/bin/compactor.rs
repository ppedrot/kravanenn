extern crate kravanenn;

use std::fs::File;
use std::io;
use std::io::{Write};
use std::str::FromStr;
use kravanenn::*;
use kravanenn::ocaml::marshal::{Header};

fn main () {
  let args : Vec<String> = std::env::args().collect();
  match args.len() {
    3 => (),
    _ => { println!("Usage: compact FILE OUTPUT"); return; },
  }
  println!("Reading file {}...", args[1]);
  let mut file = match File::open(&args[1]) {
    Err (e) => {
      println!("Fatal error: {}", e);
      return ();
    },
    Ok (f) => f,
  };
  let segments = ocaml::marshal::read_file_summary(&mut file).unwrap();
  println!("Found {} segments.", segments.len());
}
