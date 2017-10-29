use ocaml::marshal::{Obj, Field, RawString, ObjRepr};
use ocaml::votour::{Closure};
use std::error::{self, Error as StdError};
use std::fmt;

use serde;
use serde::de::{Error as DeError, IntoDeserializer};

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
        match *self.0 {
            Field::Ref(p) => self.1.get(p).ok_or(Error::InvalidObjEncoding(self)),
            _ => Err(Error::InvalidObjEncoding(self))
        }
    }

    fn block(self) -> Result<(u8, &'a [Field]), Error<'a>> {
        match *self.0 {
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
            match *self.0 {
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
            Some(field) => serde::de::DeserializeSeed::deserialize(seed, Closure(field, self.memory)).map(Some),
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
                    None => serde::de::DeserializeSeed::deserialize(seed, Closure(field, self.de.1)),
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

        let res = match *self.0 {
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
        let res = match *self.0 {
            Field::Int(0) => visitor.visit_none(),
            Field::Ref(_) => match self.obj()?.block()? {
                (0, block) => {
                    let mut iter = block.iter();
                    let field = iter.next().ok_or(Error::LengthMismatch(block, 1))?;
                    match iter.next() {
                        None => visitor.visit_some(Closure(field, self.1)),
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

    fn deserialize_identifier<V>(self, _visitor: V) -> Result<V::Value, Error<'a>>
    where
        V: serde::de::Visitor<'de>,
    {
        let message = "OCaml does not support Deserializer::deserialize_identifier";
        Err(Error::custom(message))
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

impl<'de> serde::de::Deserialize<'de> for RawString {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: serde::de::Deserializer<'de>
    {
        struct RawStringVisitor;

        impl<'de> serde::de::Visitor<'de> for RawStringVisitor {
            type Value = RawString;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("OCaml String")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
                where E: serde::de::Error
            {
                Ok(RawString(v.to_vec().into_boxed_slice()))
            }
        }

        deserializer.deserialize_bytes(RawStringVisitor)
    }
}


pub fn from_obj<'a, T>(obj: &'a ObjRepr) -> Result<T, Error<'a>>
    where T: serde::de::Deserialize<'a>
{
    let ObjRepr { ref entry, ref memory} = *obj;
    let deserializer = Closure(entry, &*memory);
    T::deserialize(deserializer)
}
