use ocaml::marshal::*;
use std::io;
use std::str::FromStr;
use std::io::{Read, Write};
use std::fmt::{Display, Error, Formatter};

pub fn peek<T>(v : &Vec<T>) -> &T {
  &v[v.len() - 1]
}

fn prompt(){
  let _ = io::stdout().write("# ".as_ref());
  let _ = io::stdout().flush();
}

fn loop_size(mem : &[Obj], seen : &mut[bool], cb : &mut (FnMut(usize, usize) -> ()), off : usize) -> usize {
  if seen[off] { return 0; };
  seen[off] = true;
  let mut size = 0;
  match mem[off] {
    Obj::Block (_, ref args) => {
      let len = args.len();
      size = size + 1 + len;
      for i in 0..len {
        match args[i] {
          Field::Ref (off) => {
            size = size + loop_size(mem, seen, cb, off);
          },
          Field::Int (..) => (),
          Field::Abs (..) => (),
          Field::Atm (..) => (),
        }
      }
    },
    Obj::String (ref s) => {
      let len = s.bytes().count();
      size = size + 2 + len / 8;
    },
  }
  cb(off, size);
  return size;
}

fn compute_size(mem : &[Obj]) -> Box<[usize]> {
  let len = mem.len();
  let mut ans = Vec::with_capacity(len);
  let mut seen = Vec::with_capacity(len);
  for _ in 0..len {
    ans.push(0);
    seen.push(false);
  };
  let mut ans = ans.into_boxed_slice();
  {
    let mut cb = |off, size| { ans[off] = size };
    if len != 0 { let _ = loop_size(mem, &mut seen, &mut cb, 0); };
  }
  ans
}

pub struct State<'a> {
  pointer : Vec<&'a Field>,
  memory : &'a [Obj],
  buffer : String,
  objsize : Box<[usize]>,
}

fn get_children<'a, 'b>(field : &'a Field, memory : &'b [Obj]) -> Option<&'b [Field]>{
  match *field {
    Field::Ref (p) => {
      match memory[p] {
        Obj::String(..) => None,
        Obj::Block(_, ref block) => Some (block),
      }
    },
    _ => None,
  }
}

fn get_size(field : &Field, objsize : &[usize]) -> usize {
  match *field {
    Field::Ref(p) => objsize[p],
    _ => 0,
  }
}

#[derive(Copy, Clone, Debug)]
pub struct Closure<'a> (pub &'a Field, pub &'a [Obj]);

impl <'a> Display for Closure<'a> {
  fn fmt(&self, fmt : &mut Formatter) -> Result<(), Error> {
    let Closure(field, memory) = *self;
    match *field {
      Field::Int (n) => {
        write!(fmt, "[int={}]", n)
      },
      Field::Ref (p) => {
        match memory.get(p) {
          Some(obj) => obj.fmt(fmt),
          None => write!(fmt, "<invalid ptr={}>", p)
        }
      },
      Field::Abs (ptr) => {
        write!(fmt, "[abs=0x{:x}]", ptr)
      },
      Field::Atm (tag) => {
        write!(fmt, "[tag={}]", tag)
      },
    }
  }
}

fn display_stack(state : &State){
  let field = *peek(&state.pointer);
  let memory = state.memory;
  let size = get_size (field, state.objsize.as_ref());
  // println!("{:?}", CONSTR);
  println!("{} (size {}w)", Closure(field, memory), size);
  match get_children(field, memory) {
    None => (),
    Some (block) => {
      println!("-------------");
      let mut n = 0;
      for i in block.iter() {
        let size = get_size (i, state.objsize.as_ref());
        println!("  {}: {} (size {}w)", n, Closure(i, memory), size);
        n = n + 1;
      };
      println!("-------------");
    }
  }
}

enum Command {
  Up,
  Down(usize),
}

fn read_command(buf : &str) -> Option<Command> {
  match usize::from_str(buf) {
    Ok(n) => Some(Command::Down(n)),
    Err(..) => {
      if buf == "u" { Some(Command::Up) }
      else { None }
    },
  }
}

fn perform_up(state : &mut State) {
  // We have reached the root
  if state.pointer.len() == 1 {
    println!("Topmost object reached.");
  }
  else {
    let _ = state.pointer.pop();
  }
}

fn perform_down(state : &mut State, n : usize) {
  let block = match **peek(&state.pointer) {
    Field::Ref (p) => {
      match state.memory[p] {
        Obj::String(..) => {
          println!("No such children.");
          return
        },
        Obj::Block(_, ref block) => { block },
      }
    },
    _ => {
      println!("No such children.");
      return
    },
  };
  if n < block.len() {
    let ptr = &block[n];
    state.pointer.push(ptr);
  } else {
    println!("No such children.");
    return
  }
}

fn perform_stack(state : &mut State) -> bool {
  prompt();
  let () = state.buffer.clear();
  let _ = match io::stdin().read_line(&mut state.buffer) {
    Ok (0) => return false,
    Ok (..) => (),
    Err (..) => return true,
  };
  // Remove EOL if possible
  let _ = state.buffer.pop();
  match read_command(&state.buffer) {
    None => (),
    Some(Command::Up) => perform_up(state),
    Some(Command::Down(n)) => perform_down(state, n),
  };
  true
}

fn visit_stack(state : &mut State){
  loop {
    display_stack(state);
    if !perform_stack(state) { return };
  }
}

pub fn visit_object<'a>(ptr : &'a Field, mem : &'a [Obj]) {
  let size = compute_size(mem);
  let ptrs = vec!(ptr);
  let buf = String::new();
  let mut state = State {
    memory : mem,
    pointer : ptrs,
    buffer : buf,
    objsize : size,
  };
  visit_stack(&mut state)
}
