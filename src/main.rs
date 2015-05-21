extern crate kravanenn;

use std::fs::File;
use kravanenn::*;

fn main () {
  let args : Vec<String> = std::env::args().collect();
  if args.len() == 2 {
    println!("Reading file {}...", args[1]);
    let mut file = match File::open(&args[1]) {
      Err (e) => {
        println!("Fatal error: {}", e);
        return ();
      },
      Ok (f) => f,
    };
    let mem = ocaml::marshal::read_file(&mut file);
    println!("{:?}", mem);
  } else {
    panic!("Invalid argument");
  }
}
