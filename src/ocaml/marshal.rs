use std;
use std::io::prelude::*;
use std::io::{Result, Error, ErrorKind};
use std::fs::File;

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

enum Object {
  Int (i64),
  Block (u8, usize),
  String (Vec<u8>),
  Pointer (u64),
  Code (u32),
}

#[derive (Clone, Debug)]
enum Field {
  Int (i64),
  Ref (usize),
  Abs (u64),
}

#[derive (Debug)]
enum Obj {
  Block (u8, Vec<Field>),
  String (Vec<u8>),
}

#[allow(dead_code)]
pub struct Header {
  magic : u32,
  length : usize,
  objects : usize,
  size32 : usize,
  size64 : usize,
}

#[derive (Debug)]
pub struct Memory (Vec<Obj>);

fn tag_of_int (i : u8) -> Tag {
  if MAX_TAG < i { panic!("Unknown tag {}", i); };
  unsafe {
    return std::mem::transmute::<u8, Tag>(i);
  }
}

fn parse_byte(file : &mut File) -> Result<u8> {
  match file.bytes().next() {
    None =>
      {
        let err = Error::new(ErrorKind::InvalidInput, "Truncated object");
        Err(err)
      }
    Some (Ok (byte)) => Ok (byte),
    Some (Err (e)) => Err (e),
  }
}

fn parse_bytes(file : &mut File, buf : &mut [u8], len : usize) -> Result<()> {
  let mut i : usize = 0;
  while i < len {
    let byte = try!(parse_byte(file));
    buf[i] = byte;
    i = i + 1;
  }
  Ok (())
}

fn parse_string(file : &mut File, len : usize) -> Result<Vec<u8>> {
  let mut buf : Vec<u8> = std::vec::Vec::with_capacity(len);
  let mut i = 0;
  // Initialize the answer
  while i < len {
    buf.push(0);
    i = i + 1;
  };
  let () = try!(parse_bytes(file, &mut buf, len));
  Ok (buf)
}

fn parse_u16(file : &mut File) -> Result<u16> {
  let mut buf = [0; 2];
  buf[1] = try!(parse_byte(file));
  buf[0] = try!(parse_byte(file));
  Ok (unsafe { std::mem::transmute::<[u8; 2], u16>(buf) })
}

fn parse_u32(file : &mut File) -> Result<u32> {
  let mut buf = [0; 4];
  buf[3] = try!(parse_byte(file));
  buf[2] = try!(parse_byte(file));
  buf[1] = try!(parse_byte(file));
  buf[0] = try!(parse_byte(file));
  Ok (unsafe { std::mem::transmute::<[u8; 4], u32>(buf) })
}

fn parse_u64(file : &mut File) -> Result<u64> {
  let mut buf = [0; 8];
  buf[7] = try!(parse_byte(file));
  buf[6] = try!(parse_byte(file));
  buf[5] = try!(parse_byte(file));
  buf[4] = try!(parse_byte(file));
  buf[3] = try!(parse_byte(file));
  buf[2] = try!(parse_byte(file));
  buf[1] = try!(parse_byte(file));
  buf[0] = try!(parse_byte(file));
  Ok (unsafe { std::mem::transmute::<[u8; 8], u64>(buf) })
}

pub fn parse_header(file: &mut File) -> Result<Header> {
  let magic = try!(parse_u32(file));
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
        Ok (Some (Object::Pointer (i as u64)))
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

fn parse_object (file : &mut File) -> Result<Option<Object>> {
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
          Tag::TagInt8 => INT!(parse_byte(file)),
          Tag::TagInt16 => INT!(parse_u16(file)),
          Tag::TagInt32 => INT!(parse_u32(file)),
          Tag::TagInt64 => INT!(parse_u64(file)),
          Tag::TagShared8 => PTR!(parse_byte(file)),
          Tag::TagShared16 => PTR!(parse_u16(file)),
          Tag::TagShared32 => PTR!(parse_u32(file)),
//           Tag::TagDoubleArray32Little =>,
          Tag::TagBlock32 => {
            let obj = try!(parse_u32(file));
            Ok (Some (Object::Block((obj & 0xFF) as u8, (obj >> 8) as usize)))
          },
          Tag::TagString8 => {
            let len = try!(parse_byte(file)) as usize;
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

fn print_header(h : &Header) {
  println!("Magic {}", h.magic);
  println!("Length {}", h.length);
  println!("Objects {}", h.objects);
  println!("Size32 {}", h.size32);
  println!("Size64 {}", h.size64);
}

fn print_object(obj : Object) {
  match obj {
    Object::Int (i) => println!("INT {}", i),
    Object::Block (tag, len) => println!("BLOCK {}::{}", tag, len),
    Object::String (..) => println!("STRING"),
    Object::Pointer (p) => println!("POINTER {:x}", p),
    Object::Code (p) => println!("CODE {:x}", p),
  }
}

#[derive (Debug)]
struct BackPointer {
  object : Vec<Field>,
  offset : usize,
}

fn rebuild_stack(stack : &mut Vec<BackPointer>, mem : &mut[Obj]) {
  let mut len = stack.len();
  loop {
    // We hit the root node
    if len == 1 { return; }
    // Otherwise, check if the top object is full
    else {
      let is_full = {
        let top = &stack[len - 1];
        top.object.capacity() == top.object.len()
      };
      if is_full {
//         println!("Popping");
        let top = match stack.pop() {
          None => panic!("Bad object"),
          Some (top) => top
        };
        len = len - 1;
        let off = top.offset;
        let tag = match mem[off] {
          Obj::Block(tag, _) => tag,
          _ => panic!("Bad object"),
        };
        mem[off] = Obj::Block(tag, top.object);
      } else { return; }
    }
  }
}

#[derive (Debug)]
pub struct ObjRepr {
  entry : Field,
  memory : Memory,
}

pub fn read_object (f : &mut File) -> Result<ObjRepr>{
  let header = try!(parse_header(f));
//   print_header(&header);
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
  while cur < header.objects {
//     println!("{:?}", stack);
    // Retrieve the header of the object
    let obj = try!(parse_object(f));
    let obj = match obj {
      None => {
        let err = Error::new(ErrorKind::InvalidInput, "Truncated object");
        return Err(err);
      },
      Some (obj) => obj,
    };
    //
    let field = match obj {
      Object::Block (..) | Object::String(..) => Field::Ref(cur),
      Object::Pointer(p) => Field::Abs(p as u64),
      Object::Code(p) => Field::Abs(p as u64),
      Object::Int(n) => Field::Int(n),
    };
    {
      let len = stack.len();
      let top = &mut stack[len - 1];
      top.object.push(field);
    }
    // Store the object in the memory or in the stack if non-scalar
    match obj {
      Object::Block (tag, len) => {
        let obj = Vec::with_capacity(len);
        // This vector is a placeholder
        let blk = Obj::Block(tag, Vec::new());
        let bp = BackPointer { object : obj, offset : cur };
        stack.push(bp);
        mem.push(blk);
        cur = cur + 1;
      },
      Object::String(s) => {
        mem.push(Obj::String(s));
        cur = cur + 1;
      },
      _ => (),
    }
    // Clean filled up blocks
    rebuild_stack(&mut stack, &mut mem);
  }
//   println!("Done.");
  let entry = match stack.pop() {
    None => panic!("Bad object"),
    Some (obj) => obj,
  };
  let entry = entry.object[0].clone();
  let ans : ObjRepr = ObjRepr { entry : entry, memory : Memory(mem) };
  Ok(ans)
}

pub fn read_segment (f : &mut File) -> Result<ObjRepr>{
  // Offset
  let _ = try!(parse_u32(f));
  // Payload
  let mem = try!(read_object(f));
  // Digest
  let buf = &mut [0; 16];
  let _ = try!(parse_bytes(f, buf, 16));
  Ok(mem)
}

pub fn read_file (f : &mut File) -> Result<Vec<ObjRepr>>{
  let mut ans = Vec::new();
  // Magic number
  let n = try!(parse_u32(f));
  loop {
    let segment = try!(read_segment(f));
    ans.push(segment);
  }
  Ok(ans)
}
