use ocaml::marshal::{Obj, Field, RawString, ObjRepr};
use ocaml::votour::{Closure};
use std::error::{self, Error as StdError};
use std::fmt;
use std::rc::Rc;

use serde;
use vec_map::{VecMap};
use std::any::Any;
use serde::de::{Error as DeError, IntoDeserializer};

#[derive(Debug)]
pub struct ORef<T>(pub Rc<T>);

#[derive(Debug)]
pub struct Array<T>(pub Rc<Vec<T>>);

#[derive(Debug)]
pub struct Str(pub Rc<Vec<u8>>);

#[derive(Debug)]
pub enum Error<'a> {
    /// Returned if the deserializer attempts to deserialize a bool that was
    /// not encoded as either a 1 or a 0
    InvalidBoolEncoding(u32),
    /// Returned if the deserializer attempts to deserialize a byte string that is not in the correct
    /// format.
    InvalidByteBufEncoding(&'a Obj),
    /// Returned if the deserializer attempts to deserialize an int that is not in the correct format.
    InvalidIntEncoding(Closure<'a>),
    /// Returned if the deserializer attempts to deserialize a block that is not in the correct format.
    InvalidBlockEncoding(&'a Obj),
    /// Returned if the deserializer attempts to deserialize a ref that is not in the correct
    /// format.
    InvalidObjEncoding(Closure<'a>),
    /// Returned if the deserializer attempts to deserialize an enum variant from a block when it
    /// is has a constant constructor.
    InvalidVariantEncoding(Closure<'a>),
    /// Returned if the deserializer attempts to deserialize the tag of an enum that is
    /// not in the expected ranges
    InvalidTagEncoding(u8),
    /// Serde has a deserialize_any method that lets the format hint to the
    /// object which route to take in deserializing.
    DeserializeAnyNotSupported,
    /// Returned if the deserializer attempts to deserialize a block with an unexpected length.
    LengthMismatch(&'a [Field], usize),
    /// A custom error message from Serde.
    Custom(String),
}

impl<'a> error::Error for Error<'a> {
    fn description(&self) -> &str {
        match *self {
            Error::InvalidBoolEncoding(_) => "invalid u8 while decoding bool",
            Error::InvalidIntEncoding(_) => "invalid field while decoding int",
            Error::InvalidVariantEncoding(_) => "invalid field while decoding variant",
            Error::InvalidObjEncoding(_) => "invalid field while decoding object",
            Error::InvalidBlockEncoding(_) => "invalid object while decoding block",
            Error::InvalidByteBufEncoding(_) => "invalid object while decoding byte buffer",
            Error::InvalidTagEncoding(_) => "tag for enum is not valid",
            Error::DeserializeAnyNotSupported => {
                "OCaml doesn't support serde::Deserializer::deserialize_any"
            }
            Error::LengthMismatch(_, _) => "length mismatch while decoding block",
            Error::Custom(ref msg) => msg,

        }
    }

    fn cause(&self) -> Option<&error::Error> {
        match *self {
            Error::InvalidBoolEncoding(_) => None,
            Error::InvalidIntEncoding(_) => None,
            Error::InvalidVariantEncoding(_) => None,
            Error::InvalidObjEncoding(_) => None,
            Error::InvalidBlockEncoding(_) => None,
            Error::InvalidByteBufEncoding(_) => None,
            Error::InvalidTagEncoding(_) => None,
            Error::DeserializeAnyNotSupported => None,
            Error::LengthMismatch(_, _) => None,
            Error::Custom(_) => None,
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::InvalidIntEncoding(c) => {
                write!(fmt, "{}, expected int, found {}", self.description(), c)
            }
            Error::InvalidBlockEncoding(o) => {
                write!(fmt, "{}, expected block, found {}", self.description(), o)
            }
            Error::InvalidByteBufEncoding(o) => {
                write!(fmt, "{}, expected byte buffer, found {}", self.description(), o)
            }
            Error::InvalidVariantEncoding(c) => {
                write!(fmt, "{}, expected constant variant, found {}", self.description(), c)
            }
            Error::InvalidObjEncoding(c) => {
                write!(fmt, "{}, expected object, found {}", self.description(), c)
            }
            Error::LengthMismatch(fs, l) => {
                write!(fmt, "{}, expected block with length {}, found {}", self.description(), l, fs.len())
            }
            Error::InvalidBoolEncoding(b) => {
                write!(fmt, "{}, expected 0 or 1, found {}", self.description(), b)
            }
            Error::InvalidTagEncoding(tag) => {
                write!(fmt, "{}, expected valid tag, found {}", self.description(), tag)
            }
            Error::DeserializeAnyNotSupported => {
                write!(
                    fmt,
                    "OCaml does not support the serde::Deserializer::deserialize_any method"
                )
            }
            Error::Custom(ref s) => s.fmt(fmt),
        }
    }
}

impl<'a> serde::de::Error for Error<'a> {
    fn custom<T: fmt::Display>(desc: T) -> Error<'a> {
        Error::Custom(desc.to_string()).into()
    }
}

pub type Deserializer<'a> = Closure<'a>;

impl<'a> Deserializer<'a> {
    fn obj(self) -> Result<&'a Obj, Error<'a>> {
        match self.0 {
            Field::Ref(p) => self.1.get(p).ok_or(Error::InvalidObjEncoding(self)),
            _ => Err(Error::InvalidObjEncoding(self))
        }
    }

    fn block(self) -> Result<(u8, &'a [Field]), Error<'a>> {
        match self.0 {
            Field::Ref(_) => self.obj()?.block(),
            Field::Atm(tag) => {
                const EMPTY_FIELDS : &'static [Field] = &[];
                Ok((tag, EMPTY_FIELDS))
            },
            _ => Err(Error::InvalidObjEncoding(self))
        }
    }
}

impl<'a> Obj {
    fn block(&'a self) -> Result<(u8, &[Field]), Error<'a>> {
        match *self {
            Obj::Block(tag, ref block) => Ok((tag, block)),
            _ => Err(Error::InvalidBlockEncoding(self))
        }
    }

    fn bytes(&'a self) -> Result<&RawString, Error<'a>> {
        match *self {
            Obj::String(ref s) => Ok(s),
            _ => Err(Error::InvalidByteBufEncoding(self))
        }
    }
}


macro_rules! impl_nums {
    ($ty:ty, $dser_method:ident, $visitor_method:ident, $reader_method:ident) => {
        #[inline]
        fn $dser_method<V>(self, visitor: V) -> Result<V::Value, Error<'a>>
            where V: serde::de::Visitor<'de>,
        {
            match self.0 {
                Field::Int (i) => visitor.$visitor_method(i as $ty),
                _ => Err(Error::InvalidIntEncoding(self))
            }
        }
    }
}

struct Access<'a, I> {
    iter: I,
    memory: &'a [Obj],
}

impl<'de, 'a, I> serde::de::SeqAccess<'de> for Access<'a, I>
        where I: Iterator<Item=&'a Field> {
    type Error = Error<'a>;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Error<'a>>
    where
        T: serde::de::DeserializeSeed<'de>,
    {
        /* println!("remaining: {:?}", self.iter.size_hint())*/;
        match self.iter.next() {
            Some(&field) => serde::de::DeserializeSeed::deserialize(seed, Closure(field, self.memory)).map(Some),
            None => {
                /* println!("Done!")*/;
                Ok(None)
            },
        }
    }

    fn size_hint(&self) -> Option<usize> {
        self.iter.size_hint().1
    }
}

impl<'de, 'a> serde::Deserializer<'de> for Deserializer<'a>
{
    type Error = Error<'a>;

    #[inline]
    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        Err(Error::DeserializeAnyNotSupported)
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        let value: u32 = serde::de::Deserialize::deserialize(self)?;
        match value {
            1 => visitor.visit_bool(true),
            0 => visitor.visit_bool(false),
            value => Err(Error::InvalidBoolEncoding(value).into()),
        }
    }

    impl_nums!(u16, deserialize_u16, visit_u16, read_u16);
    impl_nums!(u32, deserialize_u32, visit_u32, read_u32);
    impl_nums!(u64, deserialize_u64, visit_u64, read_u64);
    impl_nums!(i16, deserialize_i16, visit_i16, read_i16);
    impl_nums!(i32, deserialize_i32, visit_i32, read_i32);
    impl_nums!(i64, deserialize_i64, visit_i64, read_i64);
    impl_nums!(f32, deserialize_f32, visit_f32, read_f32);
    impl_nums!(f64, deserialize_f64, visit_f64, read_f64);

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_bytes(self.obj()?.bytes()?)
    }

    fn deserialize_enum<V>(
        self,
        _enum: &'static str,
        variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        /* println!("Deserializing enum: {}", self)*/;
        /* println!("enum={}, variants={:?}", _enum, variants)*/;
        struct Enum<'a> {
            tag: u32,
            de: Deserializer<'a>,
        };

        impl<'de, 'a> serde::de::EnumAccess<'de> for Enum<'a>
        {
            type Error = Error<'a>;
            type Variant = Self;

            fn variant_seed<S>(self, seed: S) -> Result<(S::Value, Self::Variant), Error<'a>>
                where S: serde::de::DeserializeSeed<'de>,
            {
                /* println!("Deserializing variant seed: tag={}, closure={}", self.tag, self.de)*/;
                let tag = self.tag;
                let variant = tag.into_deserializer();
                seed.deserialize(variant).map(|v| (v, self))
            }
        }

        impl<'de, 'a> serde::de::VariantAccess<'de> for Enum<'a>
        {
            type Error = Error<'a>;

            // deserialize_enum already handles non-tuple variants.
            fn unit_variant(self) -> Result<(), Error<'a>> {
                /* println!("Deserializing unit variant: {}", self.de)*/;
                Err(Error::InvalidVariantEncoding(self.de))
            }

            fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Error<'a>>
                where T: serde::de::DeserializeSeed<'de>,
            {
                /* println!("Deserializing newtype variant seed: {}", self.de)*/;
                let block = self.de.obj()?.block()?.1;
                let mut iter = block.iter();
                let field = iter.next().ok_or(Error::LengthMismatch(block, 1))?;
                match iter.next() {
                    None => serde::de::DeserializeSeed::deserialize(seed, Closure(*field, self.de.1)),
                    _ => Err(Error::LengthMismatch(block, 1)),
                }
            }

            fn tuple_variant<V>(self,
                              len: usize,
                              visitor: V) -> Result<V::Value, Error<'a>>
                where V: serde::de::Visitor<'de>,
            {
                /* println!("Deserializing tuple variant: {}", self.de)*/;
                serde::de::Deserializer::deserialize_tuple(self.de, len, visitor)
            }

            fn struct_variant<V>(self,
                               fields: &'static [&'static str],
                               visitor: V) -> Result<V::Value, Error<'a>>
                where V: serde::de::Visitor<'de>,
            {
                /* println!("Deserializing struct variant: {}", self.de)*/;
                serde::de::Deserializer::deserialize_tuple(self.de, fields.len(), visitor)
            }
        }

        let res = match self.0 {
            Field::Int(n) => {
                // This is a unit variant, which means it goes first.
                // FIXME: Assert that n is actually a u32 before downcasting.
                // That, or fix Value to know about the difference between
                // u32s and other ints.
                visitor.visit_enum((n as u32).into_deserializer())
            },
            Field::Ref(_) => {
                let tag = self.obj()?.block()?.0;
                // This is a tuple variant, which means that we reverse the order compared
                // to the real OCaml and wrap back from the end of the variant list.
                // FIXME: Either check to make sure u32 is reasonable, or check here to make sure
                //the length is in bounds of u32 (actually the bounds of 0 to 1<<31 - 1).
                /* println!("{:?}", tag)*/;
                let tag = (variants.len() as u32).checked_sub(1).and_then( |v| v.checked_sub(tag as u32)).ok_or(Error::InvalidTagEncoding(tag))?;
                visitor.visit_enum(Enum { tag: tag, de: self })
            },
            _ => Err(Error::InvalidVariantEncoding(self))
        };
        if res.is_ok() { /* println!("Done deserializing enum={:?} variants={:?}: {}", _enum, variants, self)*/ };
        res
    }

    fn deserialize_tuple<V>(self, len: usize, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        /* println!("Deserializing tuple: {}", self)*/;
        let block = self.obj()?.block()?.1;
        if block.len() != len {
            Err(Error::LengthMismatch(block, len))
        } else {
            let res = visitor.visit_seq(Access { iter: block.iter(), memory: self.1 });
            if res.is_ok() { /* println!("Done deserializing tuple: {}", self)*/ };
            res
        }
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        let res = match self.0 {
            Field::Int(0) => visitor.visit_none(),
            Field::Ref(_) => match self.obj()?.block()? {
                (0, block) => {
                    let mut iter = block.iter();
                    let field = iter.next().ok_or(Error::LengthMismatch(block, 1))?;
                    match iter.next() {
                        None => visitor.visit_some(Closure(*field, self.1)),
                        _ => Err(Error::LengthMismatch(block, 1)),
                    }
                },
                (tag, _) => Err(Error::InvalidTagEncoding(tag))
            },
            _ => Err(Error::InvalidVariantEncoding(self))
        };
        if res.is_ok() { /* println!("Done deserializing enum={:?} variants={:?}: {}", _enum, variants, self)*/ };
        res
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        /* println!("Deserializing seq: {}", self)*/;
        let block = self.block()?.1;
        let res = visitor.visit_seq(Access { iter: block.iter(), memory: self.1 });
        if res.is_ok() { /* println!("Done deserializing seq: {}", self)*/ };
        res
    }

    fn deserialize_struct<V>(
        self,
        _name: &str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        /* println!("Deserializing struct name={:?} fields={:?}: {}", _name, fields, self)*/;
        let res = self.deserialize_tuple(fields.len(), visitor);
        if res.is_ok() { /* println!("Done deserializing struct name={:?} fields={:?}: {}", _name, fields, self)*/ };
        res
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        let message = "OCaml does not support Deserializer::deserialize_identifier";
        match self.0 {
            Field::Ref(p) => visitor.visit_i64(p as i64),
            Field::Atm(tag) => visitor.visit_i64(-(tag as i64) - 1),
            Field::Int(i) => visitor.visit_i64(-i - 257), // FIXME: checked arithmetic
            _ => Err(Error::custom(message)),
        }
    }

    fn deserialize_newtype_struct<V>(self, _name: &str, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        /* println!("Deserializing newtype struct name={:?}: {}", _name, self)*/;
        let res = self.deserialize_tuple(1, visitor);
        if res.is_ok() { /* println!("Done deserializing newtype struct name={:?}: {}", _name, self)*/ };
        res
    }

    fn deserialize_unit_struct<V>(self, _name: &'static str, visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        len: usize,
        visitor: V,
    ) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        /* println!("Deserializing tuple struct name={:?}: {}", _name, self)*/;
        let res = self.deserialize_tuple(len, visitor);
        if res.is_ok() { /* println!("Done deserializing tuple struct name={:?}: {}", _name, self)*/ };
        res
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        let message = "OCaml does not support Deserializer::deserialize_ignored_any";
        Err(Error::custom(message))
    }

    forward_to_deserialize_any! {
        u8 i8 char str string
        unit map byte_buf
    }
}

struct IdentVisitor;

impl<'de> serde::de::Visitor<'de> for IdentVisitor {
    type Value = isize;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("OCaml String")
    }

    fn visit_i64<E>(self, v: i64) -> Result<Self::Value, E>
        where E: serde::de::Error
    {
        Ok(v as isize)
    }
}

pub struct Seed<'s> {
    /// A mapping from object pointers (block numbers) to dynamically typed values.  It is an error
    /// for two references to the same block to have different types, so once a value is set in the
    /// VecMap it should not change, and we also know its length up front; however, neither
    /// property seems to make it worth using something other than a VecMap.
    rust_memory: VecMap<Rc<Any>>,
    /// OCaml's memory, represented as an array of blocks.  Should have the same length as the
    /// VecMap.
    ocaml_memory: &'s [Obj],
}

impl<'s> Seed<'s> {
    pub fn new(ocaml_memory: &'s [Obj]) -> Self {
        Seed {
            rust_memory: VecMap::with_capacity(ocaml_memory.len()),
            ocaml_memory: ocaml_memory,
        }
    }
}

impl<'de, 's, T> serde::de::DeserializeState<'de, Seed<'s>> for ORef<T>
    where T: 'static,
          T: serde::de::DeserializeState<'de, Seed<'s>>,
{
    fn deserialize_state<'seed, D>(seed: &'seed mut Seed<'s>, deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        let p = deserializer.deserialize_identifier(IdentVisitor)?;
        // Okay: we have the ptr, atm, or tag number... (fixme: make this work properly).
        if let Some(o) = if p >= 0 { seed.rust_memory.remove(p as usize) } else { None } {
            // Occupied entries have been visited before, so we just need to confirm that we have
            // the same time now that we did last time.
            return match o.downcast::<T>() {
                Ok(a) => {
                    seed.rust_memory.insert(p as usize, a.clone());
                    Ok(ORef(a))
                },
                Err(_) => {
                    /* println!("Error with typeid {:?}", ::std::any::TypeId::of::<T>());
                    println!("{:?}", seed.rust_memory); */
                    Err(D::Error::custom(Error::Custom("Type mismatch".into())))
                },
            }
        }
        // Vacant entries have not yet been visited, so we need to visit this one and allocate
        // an entry.
        let deserializer = Closure(if p >= 0 { Field::Ref(p as usize) }
                                   else if p >= -256 { Field::Atm(-(p + 1) as u8) }
                                   else { Field::Int(-(p + 257) as i64) }, seed.ocaml_memory);
        // Note that if we had a cycle, this strategy will not necessarily terminate...
        // cycle detection would require keeping some sort of placeholder in the entry (of
        // the wrong type) to make sure we panicked if we came to it a second time.
        let res: T = serde::de::DeserializeState::deserialize_state(&mut *seed, deserializer).map_err(D::Error::custom)?;
        let res: Rc<T> = Rc::from(res);
        let res_: Rc<T> = res.clone();
        let res = if p >= 0 && seed.rust_memory.insert(p as usize, res_).is_some() {
            Err(D::Error::custom::<String>("The memory location was somehow mapped to a type before we finished deserializing its contents".into()))
        } else {
            /* println!("ORef {:?} TypeId {:?}", p, ::std::any::TypeId::of::<T>()); */
            Ok(ORef(res))
        };
        // if res.is_ok() { /* println!("Done deserializing seq: {}", self)*/ };
        res
    }
}

impl<'de, 's> serde::de::DeserializeState<'de, Seed<'s>> for Str
{
    fn deserialize_state<'seed, D>(seed: &'seed mut Seed<'s>, deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        /* println!("SRef"); */
        let p = deserializer.deserialize_identifier(IdentVisitor)?;
        /* println!("SRef {:?}", p); */
        // Okay: we have the ptr, atm, or tag number... (fixme: make this work properly).
        if let Some(o) = if p >= 0 { seed.rust_memory.remove(p as usize) } else { None } {
            // Occupied entries have been visited before, so we just need to confirm that we have
            // the same time now that we did last time.
            return match o.downcast::<Vec<u8>>() {
                Ok(a) => {
                    seed.rust_memory.insert(p as usize, a.clone());
                    Ok(Str(a))
                },
                Err(_) => {
                    /* println!("Error with typeid {:?}", ::std::any::TypeId::of::<Vec<u8>>()); */
                    /* println!("{:?}", seed.rust_memory); */
                    Err(D::Error::custom(Error::Custom("Type mismatch".into())))
                },
            }
        }
        // Vacant entries have not yet been visited, so we need to visit this one and allocate
        // an entry.
        struct RawStringVisitor;

        impl<'de> serde::de::Visitor<'de> for RawStringVisitor {
            type Value = Vec<u8>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("OCaml String")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
                where E: serde::de::Error
            {
                Ok(v.to_vec())
            }
        }

        let deserializer = Closure(if p >= 0 { Field::Ref(p as usize) }
                                   else if p >= -256 { Field::Atm(-(p + 1) as u8) }
                                   else { Field::Int(-(p + 257) as i64) }, seed.ocaml_memory);
        // Note that if we had a cycle, this strategy will not necessarily terminate...
        // cycle detection would require keeping some sort of placeholder in the entry (of
        // the wrong type) to make sure we panicked if we came to it a second time.
        let res: Vec<u8> = serde::de::Deserializer::deserialize_bytes(deserializer, RawStringVisitor).map_err(D::Error::custom)?;
        let res: Rc<Vec<u8>> = Rc::from(res);
        let res_ = res.clone();
        let res = if p >= 0 && seed.rust_memory.insert(p as usize, res_).is_some() {
            Err(D::Error::custom::<String>("The memory location was somehow mapped to a type before we finished deserializing its contents".into()))
        } else {
            /* println!("SRef {:?} TypeId {:?}", p, ::std::any::TypeId::of::<Vec<u8>>()); */
            Ok(Str(res))
        };
        // if res.is_ok() { /* println!("Done deserializing seq: {}", self)*/ };
        res
    }
}

impl<'s, 'de, T> serde::de::DeserializeState<'de, Seed<'s>> for Array<T>
    where T: 'static,
          T: serde::de::DeserializeState<'de, Seed<'s>>,
          // Seed<'s>: serde::de::DeserializeSeed<'de>,
{
    fn deserialize_state<'seed, D>(seed: &'seed mut Seed<'s>, deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        /* println!("ARef"); */
        let p = deserializer.deserialize_identifier(IdentVisitor)?;
        /* println!("ARef {:?}", p); */
        // Okay: we have the ptr, atm, or tag number... (fixme: make this work properly).
        if let Some(o) = if p >= 0 { seed.rust_memory.remove(p as usize) } else { None } {
            // Occupied entries have been visited before, so we just need to confirm that we have
            // the same time now that we did last time.
            return match o.downcast::<Vec<T>>() {
                Ok(a) => {
                    seed.rust_memory.insert(p as usize, a.clone());
                    Ok(Array(a))
                },
                Err(_) => {
                    /* println!("Error with typeid {:?}", ::std::any::TypeId::of::<T>());
                    println!("{:?}", seed.rust_memory); */
                    Err(D::Error::custom(Error::Custom("Type mismatch".into())))
                },
            }
        }
        // Vacant entries have not yet been visited, so we need to visit this one and allocate
        // an entry.
        let deserializer = Closure(if p >= 0 { Field::Ref(p as usize) }
                                   else if p >= -256 { Field::Atm(-(p + 1) as u8) }
                                   else { Field::Int(-(p + 257) as i64) }, seed.ocaml_memory);
        // Note that if we had a cycle, this strategy will not necessarily terminate...
        // cycle detection would require keeping some sort of placeholder in the entry (of
        // the wrong type) to make sure we panicked if we came to it a second time.
        let res: Vec<T> = serde::de::DeserializeState::deserialize_state(&mut *seed, deserializer).map_err(D::Error::custom)?;
        let res: Rc<Vec<T>> = Rc::from(res);
        let res_ = res.clone();
        // Insert the vector slice with the deserialized sequence, suitably cast, into the vacant entry.
        // Note that if we had a cycle, this strategy will not necessarily terminate...
        // cycle detection would require keeping some sort of placeholder in the entry (of
        // the wrong type) to make sure we panicked if we came to it a second time.
        // We unwrap() here because it shouldn't be possible for this memory slot to have
        // been filled by someone else yet (since they would've had to iterate through the
        // same sequence of elements).
        let res = if p >= 0 && seed.rust_memory.insert(p as usize, res_).is_some() {
            Err(D::Error::custom::<String>("The memory location was somehow mapped to a type before we finished deserializing its contents".into()))
        } else {
            /* println!("ARef {:?} TypeId {:?}", p, ::std::any::TypeId::of::<T>()); */
            Ok(Array(res))
        };
        // if res.is_ok() { /* println!("Done deserializing seq: {}", self)*/ };
        res
    }
}

pub fn from_obj_state<'a, 'de, 'seed, S, T>(obj: &'a ObjRepr, seed: &'seed mut S) -> Result<T, Error<'a>>
    where T: serde::de::DeserializeState<'de, S>, T: 'static,
{
    let ObjRepr { entry, ref memory} = *obj;
    let deserializer = Closure(entry, &*memory);
    T::deserialize_state(seed, deserializer)
}
