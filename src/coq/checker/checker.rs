extern crate serde;

use std::str;
use std::rc::Rc;
use std::sync::Arc;
use std::collections::{HashMap};
use std::collections::hash_map::{Entry};
use std::fs::File;
use std::io;
use std::io::{Write, Seek, SeekFrom};
use std::str::FromStr;
use std::path::{PathBuf, Path};
use ocaml::values::{Opaques, LibSum, Any, UnivOpaques, Lib, Id, Dp, List};
use ocaml::de::{ORef, Str};

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

pub struct LoadPath {
  f_map : HashMap<PathBuf, Dp>,
  r_map : HashMap<Dp, Vec<PathBuf>>,
}

fn split_dirpath(dp : &Dp) -> (&Id, &Dp) {
  // Dirpaths are ordered by decreasing order of generality, so the first node
  // of a module path is necessarily the name of the module.
  match dp {
    &List::Nil => panic!("Invalid library name"),
    &List::Cons(ORef(ref r1)) => {
      let (ref md, ref lib) = **r1;
      (md, lib)
    },
  }
}

fn is_in_path(lib : &Dp, path : &Dp) -> bool {
  let (_, mut lib) = split_dirpath(lib);
  let mut path = path;
  loop {
    match (lib, path) {
      (&List::Nil, &List::Nil) => return true,
      (&List::Cons(ORef(ref r1)), &List::Cons(ORef(ref r2))) => {
        let (ref id1, ref nlib) = **r1;
        let (ref id2, ref npath) = **r2;
        if id1 == id2 { lib = nlib; path = npath }
        else { return false }
      },
      (_, _) => return false,
    }
  }
}

impl LoadPath {

  pub fn new() -> Self {
    LoadPath {
      f_map : HashMap::new (),
      r_map : HashMap::new (),
    }
  }

  pub fn add(&mut self, s : PathBuf, dp : Dp) -> io::Result<()> {
    let s = try!(s.canonicalize());
    match self.f_map.insert(s.clone(), dp.clone()) {
      None => (),
      Some(_) => (), // TODO: warning
    };
    match self.r_map.entry(dp) {
      Entry::Occupied(ref mut e) => e.get_mut().push(s),
      Entry::Vacant(e) => { let _ = e.insert(vec!(s)); } ,
    };
    Ok(())
  }

  // Associate a logical path to some physical path.
  fn locate_physical(&self, s : &Path) -> Option<Dp> {
    let path = match s.parent() {
      None => return None,
      Some(s) => s,
    };
    let name = match s.file_stem() {
      None => return None,
      Some(n) =>
        match n.to_str() {
          None => return None,
          Some(n) => n,
        },
    };
    let lp = match self.f_map.get(path) {
      None => return None,
      Some(lp) => lp,
    };
    let name = Str(Arc::new(String::from(name.clone()).into_bytes()));
    Some(List::Cons(ORef(Arc::new((name, lp.clone())))))
  }

  // Associate a physical vo file to a logical path
  fn locate_logical(&self, dp : &Dp) -> Option<PathBuf> {
    let def = [];
    let (md, path) = split_dirpath(dp);
    // TODO: use UTF8 strings as identifiers
    let mut md = String::from_utf8((**md).clone()).unwrap();
    md.push_str(".vo");
    let md = Path::new(&md);
    let dirs = match self.r_map.get(path) {
      None => def.as_ref(),
      Some(v) => v.as_ref(),
    };
    for dir in dirs {
      let mut f = dir.clone();
      // No need to canonicalize, dir should already be in canonical form.
      f.push(Path::new(md));
      if f.is_file() { return Some(f); }
    }
    None
  }

}

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

pub fn check (paths : &LoadPath, files : &[String]) -> Result<(), Error> {
  Ok(())
}
