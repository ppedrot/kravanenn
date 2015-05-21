extern crate kravanenn;

use kravanenn::*;

fn main () {
  let args : Vec<String> = std::env::args().collect();
  if args.len() == 2 {
    println!("Reading file {}...", args[1]);
    let mem = ocaml::marshal::read_file(&args[1]);
    println!("{:?}", mem);
  } else {
    panic!("Invalid argument");
  }
}
