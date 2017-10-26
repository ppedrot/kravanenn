extern crate kravanenn;

use std::fs::File;
use std::io;
use std::io::{Write, Seek, SeekFrom};
use std::str::FromStr;
use kravanenn::*;
use kravanenn::ocaml::marshal::{Header};

macro_rules! try_fatal {
    ($e:expr) => {
      {
        match $e {
          Err (e) => {
            println!("Fatal error: {}", e);
            return ();
          },
          Ok (ans) => ans,
        }
      }
  };
}

fn main () {
  let args : Vec<String> = std::env::args().collect();
  if args.len() != 2 { panic!("Invalid argument"); };
  println!("Reading file {}...", args[1]);
  let mut file = match File::open(&args[1]) {
    Err (e) => {
      println!("Fatal error: {}", e);
      return ();
    },
    Ok (f) => f,
  };
  let segments = ocaml::marshal::read_file_summary(&mut file).unwrap();
  println!("Found {} segments. Choose the one to visit.", segments.len());
  let mut n : usize = 0;
  for header in segments.iter() {
    println!("{}: {}w", n, header.size64);
    n = n + 1;
  };
   let mut buf = String::new();
   let mut n : usize;
   let n;
   let segment;
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
     if let Ok(n_) = usize::from_str(&mut buf) {
         if let Some(obj) = segments.get(n_) {
            n = n_;
            segment = obj;
            break
        }
     }
     println!("No such segment.");
   }
   println!("Reading segment n°{}...", n);
   let _ = try_fatal!(file.seek(SeekFrom::Start(4)));
   for _ in 0..n {
        ocaml::marshal::read_segment(&mut file).unwrap();
   }
   let (_, ref obj) = try_fatal!(ocaml::marshal::read_segment(&mut file));
   let ocaml::marshal::Memory(ref mem) = obj.memory;
   ocaml::votour::visit_object(&obj.entry, mem, &ocaml::values::Value::Any);
}
