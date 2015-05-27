use ocaml::marshal::*;

fn object_size(obj : &Obj) -> u64 {
  match *obj {
    Obj::Block (_, ref args) => {
      1 + args.len() as u64
    },
    Obj::String (ref s) => {
      let len = s.len() as u64;
      1 + len / 8
    },
  }
}

fn compute_size(mem : &Memory) -> Box<[u64]> {
  let Memory(ref mem) = *mem;
  let len = mem.len();
  let mut ans = Vec::with_capacity(len);
  for i in 0..len {
    ans.push(0);
  };
  ans.into_boxed_slice()
}
