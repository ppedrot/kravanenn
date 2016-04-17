extern crate kravanenn;

use std::fs::File;
use std::io::{Seek, SeekFrom};
use kravanenn::ocaml::marshal;

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
  match args.len() {
    3 => (),
    _ => { println!("Usage: compact FILE OUTPUT"); return; },
  }
  println!("Reading file {}...", args[1]);
  let mut file = try_fatal!(File::open(&args[1]));
  let segments = try_fatal!(marshal::read_file_summary(&mut file));
  println!("Found {} segments.", segments.len());
  // Back to the first segment, skipping the magic number
  let _ = try_fatal!(file.seek(SeekFrom::Start(4)));
  for i in 0..segments.len() {
    println!("Reading segment {}", i);
    let seg = try_fatal!(marshal::read_segment(&mut file));
  }
}
