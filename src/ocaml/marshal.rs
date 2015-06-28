use std;
use std::io::prelude::*;
use std::io::{Result, Error, ErrorKind};
use std::ops::Deref;
use std::fmt::{Display, LowerHex, Formatter};
use std::{char};

static MARSHAL_MAGIC : u32 = 0x8495a6be;

#[allow(dead_code)]
enum Tag {
  TagInt8,
  TagInt16,
  TagInt32,
  TagInt64,
  TagShared8,
  TagShared16,
  TagShared32,
  TagDoubleArray32Little,
  TagBlock32,
  TagString8,
  TagString32,
  TagDoubleBig,
  TagDoubleLittle,
  TagDoubleArray8Big,
  TagDoubleArray8Little,
  TagDoubleArray32Big,
  TagCodePointer,
  TagInfixPointer,
  TagCustom,
  TagBlock64,
}

static PREFIX_SMALL_BLOCK : u8 = 0x80;
static PREFIX_SMALL_INT : u8 = 0x40;
static PREFIX_SMALL_STRING : u8 = 0x20;
static MAX_TAG : u8 = 0x13;

pub struct RawString (Box<[u8]>);

impl Deref for RawString {
  type Target = [u8];
  fn deref(&self) -> &[u8] {
    let RawString(ref s) = *self;
    s.as_ref()
  }
}

impl Display for RawString {
  fn fmt(&self, fmt : &mut Formatter) -> std::result::Result<(), std::fmt::Error> {
    let RawString(ref s) = *self;
    for i in s.as_ref() {
      match char::from_u32(*i as u32) {
        None => { try!(LowerHex::fmt(i, fmt)) },
        Some(ref c) => { try!(Display::fmt(c, fmt)) },
      };
    };
    Ok(())
  }
}

enum Object {
  Int (i64),
  Block (u8, usize),
  String (RawString),
  Pointer (usize),
  Code (u32),
}

pub enum Field {
  Int (i64),
  Ref (usize),
  Abs (u64),
  Atm (u8),
}

pub enum Obj {
  Block (u8, Box<[Field]>),
  String (RawString),
}

#[allow(dead_code)]
pub struct Header {
  pub magic : u32,
  pub length : usize,
  pub objects : usize,
  pub size32 : usize,
  pub size64 : usize,
}

pub struct Memory (pub Box<[Obj]>);

fn tag_of_int (i : u8) -> Tag {
  if MAX_TAG < i { panic!("Unknown tag {}", i); };
  unsafe {
    return std::mem::transmute::<u8, Tag>(i);
  }
}

trait Add<T> {
  fn add(&mut self, x : T);
}

impl <T> Add<T> for Vec<T> {
  fn add(&mut self, x : T) {
    assert!(self.len() < self.capacity());
    self.push(x);
  }
}

macro_rules! ERROR_TRUNCATED {
    () => {
      {
        let err = Error::new(ErrorKind::InvalidInput, "Truncated object");
        return Err(err)
      }
  };
}

fn parse_u8<T : Read>(file : &mut T) -> Result<u8> {
  let ref mut buf = [0; 1];
  let n = try!(file.read(buf));
  if n == 0 { ERROR_TRUNCATED!() };
  Ok(buf[0])
}

fn parse_bytes<T : Read>(file : &mut T, buf : &mut [u8], len : usize) -> Result<()> {
  let mut i : usize = 0;
  while i < len {
    let buf = &mut buf[i..len];
    let size = try!(file.read(buf));
    i = i + size;
  }
  Ok (())
}

fn parse_string<T : Read>(file : &mut T, len : usize) -> Result<RawString> {
  let mut buf : Vec<u8> = std::vec::Vec::with_capacity(len);
  let mut i = 0;
  // Initialize the answer
  while i < len {
    buf.push(0);
    i = i + 1;
  };
  let () = try!(parse_bytes(file, &mut buf, len));
  Ok (RawString(buf.into_boxed_slice()))
}

fn parse_u16<T : Read>(file : &mut T) -> Result<u16> {
  let mut buf = [0; 2];
  try!(parse_bytes(file, &mut buf, 2));
  Ok (unsafe { std::mem::transmute::<[u8; 2], u16>(buf).swap_bytes() })
}

fn parse_u32<T : Read>(file : &mut T) -> Result<u32> {
  let mut buf = [0; 4];
  try!(parse_bytes(file, &mut buf, 4));
  Ok (unsafe { std::mem::transmute::<[u8; 4], u32>(buf).swap_bytes() })
}

fn parse_u64<T : Read>(file : &mut T) -> Result<u64> {
  let mut buf = [0; 8];
  try!(parse_bytes(file, &mut buf, 8));
  Ok (unsafe { std::mem::transmute::<[u8; 8], u64>(buf).swap_bytes() })
}

pub fn parse_header<T : Read>(file: &mut T) -> Result<Header> {
  let magic = try!(parse_u32(file));
  assert_eq!(magic, MARSHAL_MAGIC);
  let length = try!(parse_u32(file)) as usize;
  let objects = try!(parse_u32(file)) as usize;
  let size32 = try!(parse_u32(file)) as usize;
  let size64 = try!(parse_u32(file)) as usize;
  let header = Header {
    magic : magic,
    length : length,
    objects : objects,
    size32 : size32,
    size64 : size64,
  };
  Ok (header)
}

macro_rules! INT {
    ($e:expr) => {
      {
        let i = try!($e);
        Ok (Some (Object::Int (i as i64)))
      }
  };
}

macro_rules! PTR {
    ($e:expr) => {
      {
        let i = try!($e);
        Ok (Some (Object::Pointer (i as usize)))
      }
  };
}

macro_rules! STR {
    ($file:expr, $len:expr) => {
      {
        let string = try!(parse_string($file, $len));
        Ok (Some (Object::String (string)))
      }
  };
}

fn parse_object<T : Read>(file : &mut T) -> Result<Option<Object>> {
  match file.bytes().next() {
    None => Ok (None),
    Some (Ok (data)) =>
      if PREFIX_SMALL_BLOCK <= data {
        let tag = data & 0x0F;
        let len = ((data >> 4) & 0x07) as usize;
        Ok (Some (Object::Block(tag, len)))
      } else if PREFIX_SMALL_INT <= data {
        let n = (data & 0x3F) as i64;
        Ok (Some (Object::Int (n)))
      } else if PREFIX_SMALL_STRING <= data {
        let len = (data & 0x1F) as usize;
        STR!(file, len)
      } else {
        match tag_of_int(data) {
          Tag::TagInt8 => INT!(parse_u8(file)),
          Tag::TagInt16 => INT!(parse_u16(file)),
          Tag::TagInt32 => INT!(parse_u32(file)),
          Tag::TagInt64 => INT!(parse_u64(file)),
          Tag::TagShared8 => PTR!(parse_u8(file)),
          Tag::TagShared16 => PTR!(parse_u16(file)),
          Tag::TagShared32 => PTR!(parse_u32(file)),
//           Tag::TagDoubleArray32Little =>,
          Tag::TagBlock32 => {
            let obj = try!(parse_u32(file));
            Ok (Some (Object::Block((obj & 0xFF) as u8, (obj >> 10) as usize)))
          },
          Tag::TagString8 => {
            let len = try!(parse_u8(file)) as usize;
            STR!(file, len)
          },
          Tag::TagString32 => {
            let len = try!(parse_u32(file)) as usize;
            STR!(file, len)
          },
//           Tag::TagDoubleBig =>,
//           Tag::TagDoubleLittle =>,
//           Tag::TagDoubleArray8Big =>,
//           Tag::TagDoubleArray8Little =>,
//           Tag::TagDoubleArray32Big =>,
          Tag::TagCodePointer => {
            let addr = try!(parse_u32(file));
            let buf = &mut [0; 16];
            let () = try!(parse_bytes(file, buf, 16));
            Ok (Some (Object::Code(addr)))
          },
//           Tag::TagInfixPointer =>,
//           Tag::TagCustom =>,
//           Tag::TagBlock64 =>,
        _ => panic!("Code {} not handled", data),
      }
    },
    Some (Err (e)) => Err (e),
  }
}

struct BackPointer {
  object : Vec<Field>,
  offset : usize,
}

// Return true if there is nothing more to read
fn rebuild_stack(stack : &mut Vec<BackPointer>, mem : &mut[Obj]) -> bool {
  let mut len = stack.len();
  loop {
    // We hit the root node
    if len == 1 { return true; }
    // Otherwise, check if the top object is full
    else {
      let is_full = {
        let top = &stack[len - 1];
        top.object.capacity() == top.object.len()
      };
      if is_full {
        let top = stack.pop().unwrap();
        len = len - 1;
        let off = top.offset;
        let tag = match mem[off] {
          Obj::Block(tag, _) => tag,
          _ => panic!("Bad object"),
        };
        mem[off] = Obj::Block(tag, top.object.into_boxed_slice());
      } else { return false; }
    }
  }
}

pub struct ObjRepr {
  pub entry : Field,
  pub memory : Memory,
}

pub fn read_object<T : Read>(f : &mut T) -> Result<(Header, ObjRepr)>{
  let header = try!(parse_header(f));
  let mut mem = Vec::with_capacity(header.objects);
  let mut stack = Vec::with_capacity(1 + header.objects);
  let mut cur : usize = 0;
//   println!("Reading data.");
  {
    // Dummy initial block
    let dummy = Vec::with_capacity(1);
    let root = BackPointer { object : dummy, offset : 0 };
    stack.push(root);
  }
  loop {
//     println!("{:?}", stack);
    // Retrieve the header of the object
    let obj = try!(parse_object(f));
    let obj = match obj {
      None => { ERROR_TRUNCATED!() },
      Some (obj) => obj,
    };
    //
    let field = match obj {
      Object::Block(tag, 0) => Field::Atm(tag),
      Object::Block(..) => Field::Ref(cur),
      Object::String(..) => Field::Ref(cur),
      Object::Pointer(p) => Field::Ref(cur - p),
      Object::Code(p) => Field::Abs(p as u64),
      Object::Int(n) => Field::Int(n),
    };
    {
      let len = stack.len();
      let top = &mut stack[len - 1];
      top.object.add(field);
    }
    // Store the object in the memory or in the stack if non-scalar
    match obj {
      Object::Block (tag, len) if len > 0 => {
        let obj = Vec::with_capacity(len);
        // This vector is a placeholder
        let blk = Obj::Block(tag, Box::default());
        let bp = BackPointer { object : obj, offset : cur };
        stack.push(bp);
        mem.add(blk);
        cur = cur + 1;
      },
      Object::String(s) => {
        mem.add(Obj::String(s));
        cur = cur + 1;
      },
      _ => (),
    }
    // Clean filled up blocks
    let finished = rebuild_stack(&mut stack, &mut mem);
    if finished { break; };
  }
//   println!("Done.");
  let mut entry = stack.pop().unwrap();
  let entry = entry.object.pop().unwrap();
  let memory = Memory(mem.into_boxed_slice());
  let ans : ObjRepr = ObjRepr { entry : entry, memory : memory };
  Ok((header, ans))
}

pub fn read_segment<T : Read>(f : &mut T) -> Result<(Header, ObjRepr)>{
  // Offset
  let _ = try!(parse_u32(f));
  // Payload
  let mem = try!(read_object(f));
  // Digest
  let buf = &mut [0; 16];
  let _ = try!(parse_bytes(f, buf, 16));
  Ok(mem)
}

pub fn read_file<T : Read>(f : &mut T) -> Result<Box<[(Header, ObjRepr)]>>{
  let mut ans = Vec::new();
  // Magic number
  let _ = try!(parse_u32(f));
  let mut i = 5;
  while 0 < i {
    let segment = try!(read_segment(f));
    ans.push(segment);
    i = i - 1;
  }
  Ok(ans.into_boxed_slice())
}
