#![no_std]
#![allow(non_camel_case_types)]

use core::{num::{NonZeroU8, NonZeroU16, NonZeroU32, NonZeroU64}, mem::{align_of, size_of, transmute}, slice, u8, u16, u32, u64, convert::identity};

/// A data structure that can be serialized to a sequence of bytes.
pub trait Serialize<T: Serialized> {
    fn serialize(&self) -> T;
}

/// A data structure which has been serialized to a sequence of bytes.
///
/// Safety:
/// Any type implementing this trait must have an alignment of one and no invalid values.
pub unsafe trait Serialized: Sized + Clone + Copy + 'static {
    type Deserialized: Serialize<Self>;

    fn deserialize(&self) -> Self::Deserialized;
}

mod sealed {
    pub trait Sealed {}
    impl Sealed for u8 {}
    impl Sealed for u16 {}
    impl Sealed for u32 {}
    impl Sealed for u64 {}
}

/// A type which can be used as the length of a slice.
pub trait SliceLen: sealed::Sealed {
    fn as_usize(self) -> usize;
}
impl SliceLen for u8 {
    fn as_usize(self) -> usize { self as usize }
}
impl SliceLen for u16 {
    fn as_usize(self) -> usize { self as usize }
}
impl SliceLen for u32 {
    fn as_usize(self) -> usize { self as usize }
}

/// Attempts to read the serialized type from the start of the given byte slice.
///
/// Returns both the serialized value and the remainder of the byte slice, or `None` if the slice
/// was not large enough.
#[inline]
pub fn try_read<T: Serialized>(bytes: &[u8]) -> Option<(&T, &[u8])> {
    assert_eq!(align_of::<T>(), 1);
    let len = size_of::<T>();
    let head = bytes.get(..len)?;
    let tail = &bytes[len..];
    Some((unsafe { &*(head.as_ptr() as *const _) }, tail))
}

/// Attempts to read the given number of items from the start of the given byte slice.
///
/// Returns both the slice of items and the remainder of the byte slice, or `None` if the slice was
/// not large enough.
#[inline]
pub fn try_read_slice<T: Serialized>(bytes: &[u8], count: usize) -> Option<(&[T], &[u8])> {
    assert_eq!(align_of::<T>(), 1);
    let len = count * size_of::<T>();
    let head = bytes.get(..len)?;
    let tail = &bytes[len..];
    Some((unsafe { slice::from_raw_parts(head.as_ptr() as *const _, count) }, tail))
}

#[inline]
pub fn as_bytes<T: Serialized>(item: &T) -> &[u8] {
    unsafe { slice::from_raw_parts(item as *const _  as *const u8, size_of::<T>()) }
}

impl Serialize<u8> for u8 {
    #[inline]
    fn serialize(&self) -> u8 {
        *self
    }
}
unsafe impl Serialized for u8 {
    type Deserialized = Self;
    #[inline]
    fn deserialize(&self) -> Self::Deserialized {
        *self
    }
}

impl Serialize<i8> for i8 {
    #[inline]
    fn serialize(&self) -> i8 {
        *self
    }
}
unsafe impl Serialized for i8 {
    type Deserialized = Self;
    #[inline]
    fn deserialize(&self) -> Self::Deserialized {
        *self
    }
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Bool(u8);
impl Serialize<Bool> for bool {
    #[inline]
    fn serialize(&self) -> Bool {
        Bool(u8::from(*self))
    }
}
unsafe impl Serialized for Bool {
    type Deserialized = bool;
    #[inline]
    fn deserialize(&self) -> Self::Deserialized {
        self.0 != 0
    }
}

macro_rules! int {
    ($t:ty => $name:ident with $to_bytes:ident $from_bytes:ident) => {
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct $name([u8; size_of::<$t>()]);
        impl Serialize<$name> for $t {
            #[inline]
            fn serialize(&self) -> $name {
                $name(self.$to_bytes())
            }
        }
        unsafe impl Serialized for $name {
            type Deserialized = $t;
            #[inline]
            fn deserialize(&self) -> Self::Deserialized {
                <$t>::$from_bytes(self.0)
            }
        }
    };

    ($t:ty => $le:ident $be:ident) => {
        int!($t => $le with to_le_bytes from_le_bytes);
        int!($t => $be with to_be_bytes from_be_bytes);
    };
}

int!(i16 => I16Le I16Be);
int!(i32 => I32Le I32Be);
int!(i64 => I64Le I64Be);

int!(u16 => U16Le U16Be);
int!(u32 => U32Le U32Be);
int!(u64 => U64Le U64Be);

macro_rules! float {
    ($t:ty => $name:ident with $int:ty) => {
        #[derive(Clone, Copy)]
        #[repr(transparent)]
        pub struct $name($int);
        impl Serialize<$name> for $t {
            #[inline]
            fn serialize(&self) -> $name {
                let x: <$int as Serialized>::Deserialized = unsafe { transmute(*self) };
                $name(x.serialize())
            }
        }
        unsafe impl Serialized for $name {
            type Deserialized = $t;
            #[inline]
            fn deserialize(&self) -> Self::Deserialized {
                unsafe { transmute(self.0.deserialize()) }
            }
        }
    };
}

float!(f32 => F32Le with U32Le);
float!(f32 => F32Be with U32Be);
float!(f64 => F64Le with U64Le);
float!(f64 => F64Be with U64Be);

macro_rules! array {
    ($size:literal; $($access:literal)*) => {
        unsafe impl<T: Serialized> Serialized for [T; $size] {
            type Deserialized = [<T as Serialized>::Deserialized; $size];
            #[inline]
            fn deserialize(&self) -> Self::Deserialized {
                [$(self[$access].deserialize(),)*]
            }
        }
        impl<U: Serialized, T: Serialize<U>> Serialize<[U; $size]> for [T; $size] {
            #[inline]
            fn serialize(&self) -> [U; $size] {
                [$(self[$access].serialize(),)*]
            }
        }
    };
}

array!(0;);
array!(1; 0);
array!(2; 0 1);
array!(3; 0 1 2);
array!(4; 0 1 2 3);
array!(5; 0 1 2 3 4);
array!(6; 0 1 2 3 4 5);
array!(7; 0 1 2 3 4 5 6);
array!(8; 0 1 2 3 4 5 6 7);
array!(9; 0 1 2 3 4 5 6 7 8);
array!(10; 0 1 2 3 4 5 6 7 8 9);
array!(11; 0 1 2 3 4 5 6 7 8 9 10);
array!(12; 0 1 2 3 4 5 6 7 8 9 10 11);
array!(13; 0 1 2 3 4 5 6 7 8 9 10 11 12);
array!(14; 0 1 2 3 4 5 6 7 8 9 10 11 12 13);
array!(15; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14);
array!(16; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15);
array!(32; 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31);

macro_rules! non_zero_option {
    ($t:ty => $name:ident with $base:ty) => {
        #[repr(transparent)]
        #[derive(Clone, Copy)]
        pub struct $name($base);
        impl Serialize<$name> for Option<$t> {
            #[inline]
            fn serialize(&self) -> $name {
                $name(self.map_or(0, <$t>::get).serialize())
            }
        }
        impl Serialize<$name> for $t {
            #[inline]
            fn serialize(&self) -> $name {
                $name(self.get().serialize())
            }
        }
        impl Serialize<$name> for <$base as Serialized>::Deserialized {
            #[inline]
            fn serialize(&self) -> $name {
                $name(self.serialize())
            }
        }
        unsafe impl Serialized for $name {
            type Deserialized = Option<$t>;
            #[inline]
            fn deserialize(&self) -> Self::Deserialized {
                <$t>::new(self.0.deserialize())
            }
        }
    };
}

non_zero_option!(NonZeroU8 => OptNonZeroU8 with u8);
non_zero_option!(NonZeroU16 => OptNonZeroU16Le with U16Le);
non_zero_option!(NonZeroU16 => OptNonZeroU16Be with U16Be);
non_zero_option!(NonZeroU32 => OptNonZeroU32Le with U32Le);
non_zero_option!(NonZeroU32 => OptNonZeroU32Be with U32Be);
non_zero_option!(NonZeroU64 => OptNonZeroU64Le with U64Le);
non_zero_option!(NonZeroU64 => OptNonZeroU64Be with U64Be);

macro_rules! non_max_option {
    ($t:ty => $name:ident with $base:ty) => {
        #[repr(transparent)]
        #[derive(Clone, Copy)]
        pub struct $name($base);
        impl Serialize<$name> for Option<$t> {
            fn serialize(&self) -> $name {
                $name(self.unwrap_or(<$t>::max_value()).serialize())
            }
        }
        impl Serialize<$name> for $t {
            fn serialize(&self) -> $name {
                $name(self.serialize())
            }
        }
        unsafe impl Serialized for $name {
            type Deserialized = Option<$t>;
            fn deserialize(&self) -> Self::Deserialized {
                let x = self.0.deserialize();
                if x == <$t>::max_value() { None } else { Some(x) }
            }
        }
    }
}

non_max_option!(u8 => OptNonMaxU8 with u8);
non_max_option!(u16 => OptNonMaxU16Le with U16Le);
non_max_option!(u16 => OptNonMaxU16Be with U16Be);
non_max_option!(u32 => OptNonMaxU32Le with U32Le);
non_max_option!(u32 => OptNonMaxU32Be with U32Be);
non_max_option!(u64 => OptNonMaxU64Le with U64Le);
non_max_option!(u64 => OptNonMaxU64Be with U64Be);

#[macro_export]
macro_rules! serializable {
    ($(#[$attr:meta])* $v:vis struct $se_name:ident ($de_name:ident) {
        $($(#[$fattr:meta])* $fv:vis $fname:ident: $fty:ty),* $(,)?
    }) => {
        $(#[$attr])*
        #[repr(C)]
        #[derive(Clone, Copy)]
        $v struct $se_name {
            $($(#[$fattr])* $fv $fname: $fty),*
        }

        $(#[$attr])*
        #[derive(Clone, Copy)]
        $v struct $de_name {
            $($(#[$fattr])* $fv $fname: <$fty as $crate::Serialized>::Deserialized),*
        }

        impl $crate::Serialize<$se_name> for $de_name {
            fn serialize(&self) -> $se_name {
                $se_name {
                    $($fname: <<$fty as $crate::Serialized>::Deserialized as $crate::Serialize<$fty>>::serialize(&self.$fname)),*
                }
            }
        }

        unsafe impl $crate::Serialized for $se_name {
            type Deserialized = $de_name;

            fn deserialize(&self) -> Self::Deserialized {
                $de_name {
                    $($fname: <$fty as $crate::Serialized>::deserialize(&self.$fname)),*
                }
            }
        }
    };
}

#[cfg(test)]
mod test {
    use super::*;
    use core::mem::size_of;

    #[test]
    fn serialize_deserialize() {
        serializable!{
            struct SerialTest(Test) {
                pub foo: u8,
                bar: U32Le,
                baz: [Bool; 5],
            }
        }

        let x = Test {
            foo: 0,
            bar: 0,
            baz: [false, false, false, false, false],
        };

        let y: SerialTest = x.serialize();
        let bytes = as_bytes(&y);
        assert_eq!(bytes, &[0; size_of::<SerialTest>()]);

        let mut y = y;
        y.foo = 15.serialize();
        y.bar = 23456.serialize();
        y.baz = [true, false, true, true, false].serialize();

        let z = y.deserialize();
        assert_eq!(z.foo, 15);
        assert_eq!(z.bar, 23456);
        assert_eq!(z.baz, [true, false, true, true, false]);
    }

    #[test]
    fn single_from_slice() {
        serializable!{
            struct SerialTest(Test) {
                foo: U32Be,
                bar: [Bool; 2],
                baz: U32Le,
            }
        }

        let data = [0, 0, 0, 1, 1, 0, 2, 0, 0, 0,];
        let (x, _) = try_read::<SerialTest>(&data).unwrap();

        assert_eq!(x.foo.deserialize(), 1);
        assert_eq!(x.bar.deserialize(), [true, false]);
        assert_eq!(x.baz.deserialize(), 2);
    }
}
