extern crate byteorder;

use std;
use std::io::prelude::*;
use std::io::{Result, Error, ErrorKind};
use std::ops::Deref;
use std::fmt::{Display, LowerHex, Formatter};
use std::{char};
use self::byteorder::{ReadBytesExt, BigEndian};

use fixedbitset::{FixedBitSet};

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

#[derive(Debug)]
pub struct RawString (pub Box<[u8]>);

impl Deref for RawString {
  type Target = Box<[u8]>;
  fn deref(&self) -> &Box<[u8]> {
    let RawString(ref s) = *self;
    s
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

#[derive(Debug)]
enum Object {
  Int (i64),
  Block (u8, usize),
  String (RawString),
  Pointer (usize),
  Code (u32),
}

impl Display for Obj {
  fn fmt(&self, fmt : &mut Formatter) -> ::std::result::Result<(), std::fmt::Error> {
      match *self {
          Obj::String(ref s) => write!(fmt, "[str=\"{}\"]", s),
          Obj::Block(tag, ref p) => write!(fmt, "[tag={}, fields.len={}]", tag, p.len()),
      }
  }
}

#[derive(Copy,Clone,Debug)]
pub enum Field {
  Int (i64),
  Ref (usize),
  Abs (u64),
  Atm (u8),
}

#[derive(Debug)]
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

impl Deref for Memory {
  type Target = Box<[Obj]>;
  fn deref(&self) -> &Box<[Obj]> {
    let Memory(ref s) = *self;
    s
  }
}

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

fn parse_u8<T : Read>(file : &mut T) -> Result<u8> {
  file.read_u8()
}

fn parse_bytes<T : Read>(file : &mut T, buf : &mut [u8]) -> Result<bool> {
  let len = buf.len();
  let mut i : usize = 0;
  while i < len {
    let buf = &mut buf[i..len];
    let size = try!(file.read(buf));
    if size == 0 && i == 0 { return Ok(false) };
    if size == 0 {
      let err = Error::new(ErrorKind::InvalidInput, "Truncated object");
      return Err(err);
    };
    i = i + size;
  }
  Ok (true)
}

fn parse_string<T : Read>(file : &mut T, len : usize) -> Result<RawString> {
  let mut buf : Vec<u8> = std::vec::Vec::with_capacity(len);
  unsafe { buf.set_len(len) };
  let () = try!(file.read_exact(&mut buf));
  Ok (RawString(buf.into_boxed_slice()))
}

fn parse_u16<T : Read>(file : &mut T) -> Result<u16> {
  file.read_u16::<BigEndian>()
}

fn parse_u32<T : Read>(file : &mut T) -> Result<u32> {
  file.read_u32::<BigEndian>()
}

fn parse_u64<T : Read>(file : &mut T) -> Result<u64> {
  file.read_u64::<BigEndian>()
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
        Ok (Object::Int (i as i64))
      }
  };
}

macro_rules! PTR {
    ($e:expr) => {
      {
        let i = try!($e);
        Ok (Object::Pointer (i as usize))
      }
  };
}

macro_rules! STR {
    ($file:expr, $len:expr) => {
      {
        let string = try!(parse_string($file, $len));
        Ok (Object::String (string))
      }
  };
}

fn parse_object<T : Read>(file : &mut T) -> Result<Object> {
  let data = try!(file.read_u8());
  if PREFIX_SMALL_BLOCK <= data {
    let tag = data & 0x0F;
    let len = ((data >> 4) & 0x07) as usize;
    Ok (Object::Block(tag, len))
  } else if PREFIX_SMALL_INT <= data {
    let n = (data & 0x3F) as i64;
    Ok (Object::Int (n))
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
        // println!("{:x} = obj, {:x} = tag", obj, obj & 0xFF);
        Ok (Object::Block((obj & 0xFF) as u8, (obj >> 10) as usize))
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
        let () = try!(file.read_exact(buf));
        Ok (Object::Code(addr))
      },
//           Tag::TagInfixPointer =>,
//           Tag::TagCustom =>,
//           Tag::TagBlock64 =>,
    _ => panic!("Code {} not handled", data),
  } }
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
  let mut bits = FixedBitSet::with_capacity(1 + header.objects);
  let mut cur : usize = 0;
  let mut total = 0;
  let mut share = 0;
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
      if let Field::Ref(p) = field {
          total += 1;
          if bits.put(p) {
              share += 1;
          }
      }
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
  println!("Memory sharing in effect: share={:?} / total={:?}", share, total);
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
  let _ = try!(f.read_exact(buf));
  Ok(mem)
}

fn read_segment_header<T : Read + Seek>(f : &mut T) -> Result<Option<Header>>{
  // Offset
  let mut buf = [0; 4];
  let read = try!(parse_bytes(f, &mut buf));
  if !read { return Ok(None); };
  let pos = try!(buf.as_ref().read_u32::<BigEndian>());
  // Ignore the digest
  let pos = pos + 16;
  // Payload + Digest
  let header = try!(parse_header(f));
  let _ = try!(f.seek(std::io::SeekFrom::Start(pos as u64)));
  Ok(Some(header))
}

pub fn read_file_summary<T : Read + Seek>(f : &mut T) -> Result<Box<[Header]>>{
  // Magic number
  let _ = try!(parse_u32(f));
  // Segments
  let mut segments = Vec::new();
  loop {
    let hd = try!(read_segment_header(f));
    match hd {
      None => { break; }
      Some (hd) => { segments.push(hd); }
    }
  };
  Ok(segments.into_boxed_slice())
}
