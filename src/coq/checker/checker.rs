extern crate serde;

use std::fs::File;
use std::io;
use std::io::{Write, Seek, SeekFrom};
use std::str::FromStr;
use ocaml::values::{Opaques, LibSum, Any, UnivOpaques, Lib};

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

pub struct Error;

fn load_file(f : &str) -> Result <(), Error> {
//   println!("Reading file {}...", args[1]);
//   let mut file = match File::open(&args[1]) {
//     Err (e) => {
//       println!("Fatal error: {}", e);
//       return ();
//     },
//     Ok (f) => f,
//   };
//   let () = try_fatal!(ocaml::marshal::read_magic(&mut file));
//   // First segment: object file summary
//   let (_, ref obj) = try_fatal!(ocaml::marshal::read_segment(&mut file));
//   let mut seed = ocaml::de::Seed::new(&obj.memory);
//   let sd : LibSum = try_fatal!(ocaml::de::from_obj_state(obj, &mut seed));
//   // Second segment: library itself
//   let (_, ref obj) = try_fatal!(ocaml::marshal::read_segment(&mut file));
//   let mut seed = ocaml::de::Seed::new(&obj.memory);
//   let md : Lib = try_fatal!(ocaml::de::from_obj_state(obj, &mut seed));
//   // Third, fourth and fifth segments don't matter for checker
//   let () = try_fatal!(ocaml::marshal::skip_segment(&mut file));
//   let () = try_fatal!(ocaml::marshal::skip_segment(&mut file));
//   let () = try_fatal!(ocaml::marshal::skip_segment(&mut file));
//   // Sixth segment: opaque table
//   let mut seed = ocaml::de::Seed::new(&obj.memory);
//   let table : Opaques = try_fatal!(ocaml::de::from_obj_state(obj, &mut seed));
//   
  unimplemented!("yay");
}

pub fn check (files : &[String]) -> Result<(), Error> {
  Ok(())
}
