use ocaml::marshal::*;

fn loop_size(mem : &[Obj], ans : &mut[u64], off : usize) -> u64 {
  let mut size = ans[off];
  if size > 0 { return size; };
  match mem[off] {
    Obj::Block (_, ref args) => {
      let len = args.len();
      size = size + 1 + len as u64;
      for _ in 0..len {
        match args[len] {
          Field::Ref (off) => {
            size = size + loop_size(mem, ans, off);
          },
          Field::Int (..) => (),
          Field::Abs (..) => (),
          Field::Atm (..) => (),
        }
      }
    },
    Obj::String (ref s) => {
      let len = s.len() as u64;
      size = size + 1 + len / 8;
    },
  }
  ans[off] = size;
  return size;
}

fn compute_size(mem : &[Obj]) -> Box<[u64]> {
  let len = mem.len();
  let mut ans = Vec::with_capacity(len);
  for _ in 0..len {
    ans.push(0);
  };
  let mut ans = ans.into_boxed_slice();
  let _ = loop_size(mem, &mut ans, 0);
  ans
}
