use ocaml::marshal::*;

fn compute_size(mem : &Memory) -> Box<[u64]> {
  let Memory(ref mem) = *mem;
  let mut ans = Vec::with_capacity(mem.len());
  ans.into_boxed_slice()
}
