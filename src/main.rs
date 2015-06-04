extern crate kravanenn;

use std::fs::File;
use std::io;
use std::io::{Write};
use std::str::FromStr;
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
    let segments = match ocaml::marshal::read_file(&mut file) {
      Err (e) => {
        println!("Fatal error: {}", e);
        return ();
      },
      Ok (s) => s,
    };
    println!("Found {} segments. Choose the one to visit.", segments.len());
    let mut n : usize = 0;
    for segment in segments.iter() {
      let (ref header, _) = *segment;
      println!("{}: {}w", n, header.size64);
      n = n + 1;
    };
    let mut buf = String::new();
    let mut n : usize;
    loop {
      print!("# ");
      let _ = io::stdout().flush();
      let () = buf.clear();
      let () = match io::stdin().read_line(&mut buf) {
        Ok (0) => return (),
        Ok (..) => (),
        Err (..) => return (),
      };
      // Remove the EOL
      let _ = buf.pop();
      match usize::from_str(&mut buf) {
        Ok (i) if i < segments.len() => { n = i; break; },
        _ => (),
      };
      println!("No such segment.");
    };
    println!("Reading segment n°{}...", n);
    let (_, ref obj) = segments[n];
    let ocaml::marshal::Memory(ref mem) = obj.memory;
    ocaml::votour::visit_object(&obj.entry, mem, &ocaml::values::Value::Any);
  } else {
    panic!("Invalid argument");
  }
}
