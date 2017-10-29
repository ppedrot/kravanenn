use hopcroft::hopcroft::{Automaton, Transition, StateT};
use hopcroft::partition::{Partition};
use ocaml::marshal::{ObjRepr, Obj, Field, Memory};

#[derive (Clone, PartialEq, PartialOrd, Eq, Ord)]
enum Label {
  Tag (u8), // self tag
  Int (i64), // integer
  Atm (usize, u8), // index, tag
  Fld (usize), // pointer to another block
  Str (Box<[u8]>), // string
}

fn push(trs : &mut Vec<Transition<Label>>, lbl : Label, src : usize, dst : usize) {
  let t = Transition::new(lbl, src, dst);
  trs.push(t)
}

fn to_automaton(obj : &ObjRepr) -> Automaton<Label> {
  let len = obj.memory.len();
  // Heuristic size
  let mut trs = Vec::with_capacity(len);
  for (ptr, obj) in obj.memory.iter().enumerate() {
    match *obj {
      Obj::Block(tag, ref data) => {
        push(&mut trs, Label::Tag(tag), ptr, ptr);
        for (i, field) in data.iter().enumerate() {
          match *field {
            Field::Int(n) => push(&mut trs, Label::Int(n), ptr, ptr),
            Field::Ref(p) => push(&mut trs, Label::Fld(i), ptr, p),
            Field::Atm(tag) => push(&mut trs, Label::Atm(i, tag), ptr, ptr),
            Field::Abs(_) => unimplemented!(),
          }
        }
      },
      Obj::String(ref s) => {
        let s = s as &Box<[u8]>;
        let lbl = Label::Str(s.clone());
        push(&mut trs, lbl, ptr, ptr)
      },
    }
  }
  Automaton { states : len, transitions : trs.into_boxed_slice(), }
}

fn quotient(obj : &ObjRepr, partition : &Partition<StateT>) -> ObjRepr {
  let mem = Vec::with_capacity(partition.len());
  // Fill the memory in two passes, to ensure we get the pointers right
  // First construct the structures.
  for _p in partition.into_iter() {
  // TODO: implement memory translation
  }
  let entry = match obj.entry {
    Field::Int(n) => Field::Int(n),
    Field::Ref(p) => Field::Ref(partition.partition(p).to_usize()),
    Field::Atm(tag) => Field::Atm(tag),
    Field::Abs(addr) => Field::Abs(addr),
  };
  ObjRepr { entry : entry, memory : Memory(mem.into_boxed_slice()) }
}

pub fn reduce(obj : &ObjRepr) -> ObjRepr {
  let mut automaton = to_automaton(obj);
  let ref partition = automaton.reduce();
  quotient(obj, partition)
}
