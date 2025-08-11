// VTOCK-TODO: how to do defs without breaking compilation
use core::clone::Clone;
use core::marker::Copy;
use core::ops::{Add, AddAssign};
use core::prelude::rust_2021::derive;
pub use tock_registers::debug;
pub use tock_registers::fields::TryFromValue;
use tock_registers::fields::{Field, FieldValue};
use tock_registers::LocalRegisterCopy;
pub use tock_registers::RegisterLongName;

flux_rs::defs! {
    fn bv32(x:int) -> bitvec<32> { bv_int_to_bv32(x) }
}
#[flux_rs::opaque]
#[flux_rs::refined_by(mask: bitvec<32>, shift: bitvec<32>)]
pub struct FieldU32<R: RegisterLongName> {
    inner: Field<u32, R>,
}

#[allow(dead_code)]
impl<R: RegisterLongName> FieldU32<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(mask: u32, shift: usize) -> Self[bv32(mask), bv32(shift)])]
    pub const fn new(mask: u32, shift: usize) -> Self {
        Self {
            inner: Field::new(mask, shift),
        }
    }

    /*
        mask: mask << shift,
        value: (value & mask) << shift,
    */
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(&Self[@mask, @shift], value: u32) -> FieldValueU32<R>[bv_shl(mask, shift), bv_shl(bv_and(bv32(value), mask), shift)])]
    pub fn val(&self, value: u32) -> FieldValueU32<R> {
        FieldValueU32 {
            inner: FieldValue::<u32, R>::new(self.inner.mask, self.inner.shift, value),
        }
    }

    #[flux_rs::trusted(reason = "flux wrappers")]
    pub fn into_inner(self) -> Field<u32, R> {
        self.inner
    }
}

#[derive(Copy, Clone)]
#[flux_rs::opaque]
#[flux_rs::refined_by(mask: bitvec<32>, value: bitvec<32>)]
pub struct FieldValueU32<R: RegisterLongName> {
    inner: FieldValue<u32, R>,
}

impl<R: RegisterLongName> FieldValueU32<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    // mask << shift, value << shift
    #[flux_rs::sig(fn(u32[@mask], usize[@shift], u32[@value]) -> Self[bv_shl(bv32(mask), bv32(shift)), bv_shl(bv32(value), bv32(shift))])]
    pub const fn new(mask: u32, shift: usize, value: u32) -> Self {
        FieldValueU32 {
            inner: FieldValue::<u32, R>::new(mask, shift, value),
        }
    }

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    // (val & (mask << shift)) >> shift
    #[flux_rs::sig(fn(&Self[@mask, @val], FieldU32<R>[@_mask2, @shift]) -> u32[bv_bv32_to_int(bv_lshr(bv_and(val, bv_shl(mask, shift)), shift))])]
    pub fn read(&self, field: FieldU32<R>) -> u32 {
        field.inner.read(self.inner.value)
    }

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(self: &Self[@mask, @_value]) -> u32[bv_bv32_to_int(mask)])]
    pub fn mask(&self) -> u32 {
        self.inner.mask
    }

    #[flux_rs::trusted(reason = "flux wrappers")]
    pub fn into_inner(self) -> FieldValue<u32, R> {
        self.inner
    }

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(self: &Self[@_mask, @value]) -> u32[bv_bv32_to_int(value)])]
    pub fn value(&self) -> u32 {
        self.inner.value
    }
}

#[allow(dead_code)]
impl<R: RegisterLongName> Add for FieldValueU32<R> {
    type Output = Self;

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(Self[@mask0, @value0], Self[@mask1, @value1]) -> FieldValueU32<R>[bv_or(mask0, mask1), bv_or(value0, value1)])]
    fn add(self, rhs: Self) -> Self {
        FieldValueU32 {
            inner: FieldValue::<u32, R>::new(
                self.inner.mask | rhs.inner.mask,
                0,
                self.inner.value | rhs.inner.value,
            ),
        }
    }
}

impl<R: RegisterLongName> AddAssign for FieldValueU32<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(self: &strg Self[@mask0, @value0], Self[@mask1, @value1]) ensures self: Self[bv_or(mask0, mask1), bv_or(value0, value1)])]
    fn add_assign(&mut self, other: Self) {
        self.inner += other.inner;
    }
}

// FieldU8

#[flux_rs::opaque]
#[flux_rs::refined_by(mask: bitvec<32>, shift: bitvec<32>)]
// mask should really be a u8 - so we need to constrain it
#[flux_rs::invariant(mask <= bv_int_to_bv32(u8::MAX))]
pub struct FieldU8<R: RegisterLongName> {
    inner: Field<u8, R>,
}

#[allow(dead_code)]
impl<R: RegisterLongName> FieldU8<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(mask: u8, shift: usize) -> Self[bv32(mask), bv32(shift)])]
    pub const fn new(mask: u8, shift: usize) -> Self {
        Self {
            inner: Field::new(mask, shift),
        }
    }

    /*
        mask: mask << shift,
        value: (value & mask) << shift,
    */
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(&Self[@mask, @shift], value: u8) -> FieldValueU8<R>[bv_shl(mask, shift), bv_shl(bv_and(bv32(value), mask), shift)])]
    pub fn val(&self, value: u8) -> FieldValueU8<R> {
        FieldValueU8 {
            inner: FieldValue::<u8, R>::new(self.inner.mask, self.inner.shift, value),
        }
    }

    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn (&Self[@mask, @shift], u8[@value]) -> bool[bv_int_to_bv32(value) & (mask << shift) != 0])]
    pub fn is_set(&self, value: u8) -> bool {
        self.inner.is_set(value)
    }

    #[flux_rs::trusted(reason = "flux wrappers")]
    pub fn into_inner(self) -> Field<u8, R> {
        self.inner
    }

    #[flux_rs::trusted(reason = "flux wrappers")]
    pub fn read_as_enum<E: TryFromValue<u8, EnumType = E>>(self, val: u8) -> Option<E> {
        E::try_from_value(self.inner.read(val))
    }
}
#[derive(Copy, Clone)]
#[flux_rs::opaque]
#[flux_rs::refined_by(mask: bitvec<32>, value: bitvec<32>)]
#[flux_rs::invariant(mask <= bv_int_to_bv32(u8::MAX) && value <= bv_int_to_bv32(u8::MAX))]
pub struct FieldValueU8<R: RegisterLongName> {
    inner: FieldValue<u8, R>,
}

impl<R: RegisterLongName> FieldValueU8<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    // mask << shift, value << shift
    #[flux_rs::sig(fn(u8[@mask], usize[@shift], u8[@value]) -> Self[bv_shl(bv32(mask), bv32(shift)), bv_shl(bv32(value), bv32(shift))])]
    pub const fn new(mask: u8, shift: usize, value: u8) -> Self {
        FieldValueU8 {
            inner: FieldValue::<u8, R>::new(mask, shift, value),
        }
    }

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    // (val & (mask << shift)) >> shift
    #[flux_rs::sig(fn(&Self[@mask, @val], FieldU8<R>[@_mask2, @shift]) -> u8[bv_bv32_to_int(bv_lshr(bv_and(val, bv_shl(mask, shift)), shift))])]
    pub fn read(&self, field: FieldU8<R>) -> u8 {
        field.inner.read(self.inner.value)
    }

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(self: &Self[@mask, @_value]) -> u8[bv_bv32_to_int(mask)])]
    pub fn mask(&self) -> u8 {
        self.inner.mask
    }

    #[flux_rs::trusted(reason = "flux wrappers")]
    pub fn into_inner(self) -> FieldValue<u8, R> {
        self.inner
    }

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(self: &Self[@_mask, @value]) -> u8[bv_bv32_to_int(value)])]
    pub fn value(&self) -> u8 {
        self.inner.value
    }
}

#[allow(dead_code)]
impl<R: RegisterLongName> Add for FieldValueU8<R> {
    type Output = Self;

    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(Self[@mask0, @value0], Self[@mask1, @value1]) -> FieldValueU8<R>[bv_or(mask0, mask1), bv_or(value0, value1)])]
    fn add(self, rhs: Self) -> Self {
        FieldValueU8 {
            inner: FieldValue::<u8, R>::new(
                self.inner.mask | rhs.inner.mask,
                0,
                self.inner.value | rhs.inner.value,
            ),
        }
    }
}

impl<R: RegisterLongName> AddAssign for FieldValueU8<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn(self: &strg Self[@mask0, @value0], Self[@mask1, @value1]) ensures self: Self[bv_or(mask0, mask1), bv_or(value0, value1)])]
    fn add_assign(&mut self, other: Self) {
        self.inner += other.inner;
    }
}
// Macros for declaring named bitfields

/// Define register types and fields.
#[macro_export]
macro_rules! register_bitfields_u32 {
    {
        $valtype:ident, $( $(#[$inner:meta])* $vis:vis $reg:ident $fields:tt ),* $(,)?
    } => {
        $(
            #[allow(non_snake_case)]
            $(#[$inner])*
            $vis mod $reg {
                // Visibility note: This is left always `pub` as it is not
                // meaningful to restrict access to the `Register` element of
                // the register module if the module itself is in scope
                //
                // (if you can access $reg, you can access $reg::Register)
                #[derive(Clone, Copy)]
                pub struct Register;
                impl $crate::RegisterLongName for Register {}

                use $crate::{FieldU32, FieldValueU32};
                use $crate::TryFromValue;

                $crate::register_bitmasks_u32!( $valtype, $reg, Register, $fields );
            }
        )*
    }
}

#[macro_export]
macro_rules! bitmask {
    ($numbits:expr) => {
        (1 << ($numbits - 1)) + ((1 << ($numbits - 1)) - 1)
    };
}

/// Helper macro for defining register fields.
#[macro_export]
macro_rules! register_bitmasks_u32 {
    {
        // BITFIELD_NAME OFFSET(x)
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident OFFSET($offset:expr)),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u32!($valtype, $reg_desc, $(#[$inner])* $field, $offset, 1, []); )*
        $crate::register_bitmasks_u32!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        // BITFIELD_NAME OFFSET
        // All fields are 1 bit
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident $offset:expr ),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u32!($valtype, $reg_desc, $(#[$inner])* $field, $offset, 1, []); )*
        $crate::register_bitmasks_u32!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        // BITFIELD_NAME OFFSET(x) NUMBITS(y)
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident OFFSET($offset:expr) NUMBITS($numbits:expr) ),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u32!($valtype, $reg_desc, $(#[$inner])* $field, $offset, $numbits, []); )*
        $crate::register_bitmasks_u32!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        // BITFIELD_NAME OFFSET(x) NUMBITS(y) []
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident OFFSET($offset:expr) NUMBITS($numbits:expr)
               $values:tt ),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u32!($valtype, $reg_desc, $(#[$inner])* $field, $offset, $numbits,
                              $values); )*
        $crate::register_bitmasks_u32!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        $valtype:ident, $reg_desc:ident, $(#[$outer:meta])* $field:ident,
                    $offset:expr, $numbits:expr,
                    [$( $(#[$inner:meta])* $valname:ident = $value:expr ),+ $(,)?]
    } => { // this match arm is duplicated below with an allowance for 0 elements in the valname -> value array,
        // to seperately support the case of zero-variant enums not supporting non-default
        // representations.

        pub use $field::$field;

        #[allow(non_snake_case)]
        #[allow(unused)]
        $(#[$outer])*
        pub mod $field {
            #[allow(unused_imports)]
            use $crate::{FieldValueU32, TryFromValue, FieldU32};
            use super::$reg_desc;

            pub const MASK: u32 = $crate::bitmask!($numbits);
            pub const OFFSET: usize = $offset;

            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            #[flux_rs::sig(fn() -> FieldU32<$reg_desc>[bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)])]
            pub const fn $field() -> FieldU32<$reg_desc> {
                FieldU32::<$reg_desc>::new(MASK, OFFSET)
            }


            $(
            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            $(#[$inner])*
            mod $valname {
                use $crate::{FieldValueU32, TryFromValue};
                use super::$reg_desc;

                const MASK: u32 = $crate::bitmask!($numbits);
                const OFFSET: usize = $offset;
                const VALUE: u32 = $value;

                #[flux_rs::sig(fn() -> FieldValueU32<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(VALUE), bv_int_to_bv32(OFFSET))])]
                pub const fn $valname() -> FieldValueU32<$reg_desc> {
                FieldValueU32::<$reg_desc>::new(MASK, OFFSET, $value)
                }
            }
            pub use $valname::$valname;
            )*

            #[flux_rs::sig(fn() -> FieldValueU32<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET))])]
            pub const fn SET() -> FieldValueU32<$reg_desc> {
                FieldValueU32::<$reg_desc>::new(MASK, OFFSET, MASK)
            }

            #[flux_rs::sig(fn() -> FieldValueU32<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(0), bv_int_to_bv32(OFFSET))])]
            pub const fn CLEAR() -> FieldValueU32<$reg_desc> {
                FieldValueU32::<$reg_desc>::new(MASK, OFFSET, 0)
            }

            #[allow(dead_code)]
            #[allow(non_camel_case_types)]
            #[derive(Copy, Clone, Debug, Eq, PartialEq)]
            #[repr($valtype)] // so that values larger than isize::MAX can be stored
            $(#[$outer])*
            pub enum Value {
                $(
                    $(#[$inner])*
                    $valname = $value,
                )*
            }

            impl TryFromValue<$valtype> for Value {
                type EnumType = Value;

                fn try_from_value(v: $valtype) -> Option<Self::EnumType> {
                    match v {
                        $(
                            $(#[$inner])*
                            x if x == Value::$valname as $valtype => Some(Value::$valname),
                        )*

                        _ => Option::None
                    }
                }
            }

            impl From<Value> for FieldValueU32<$reg_desc> {
                fn from(v: Value) -> Self {
                    Self::new($crate::bitmask!($numbits), $offset, v as $valtype)
                }
            }
        }
    };
    {
        $valtype:ident, $reg_desc:ident, $(#[$outer:meta])* $field:ident,
                    $offset:expr, $numbits:expr,
                    []
    } => { //same pattern as previous match arm, for 0 elements in array. Removes code associated with array.

        pub use $field::$field;

        #[allow(non_snake_case)]
        #[allow(unused)]
        $(#[$outer])*
        pub mod $field {
            #[allow(unused_imports)]
            use $crate::{FieldValueU32, TryFromValue, FieldU32};
            use super::$reg_desc;

            const MASK: u32 = $crate::bitmask!($numbits);
            const OFFSET: usize = $offset;

            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            #[flux_rs::sig(fn() -> FieldU32<$reg_desc>[bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)])]
            pub const fn $field() -> FieldU32<$reg_desc> {
                FieldU32::<$reg_desc>::new(MASK, OFFSET)
            }


            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            #[flux_rs::sig(fn() -> FieldValueU32<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET))])]
            pub const fn SET() -> FieldValueU32<$reg_desc> {
                FieldValueU32::<$reg_desc>::new(MASK, OFFSET, MASK)
            }


            #[flux_rs::sig(fn() -> FieldValueU32<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(0), bv_int_to_bv32(OFFSET))])]
            pub const fn CLEAR() -> FieldValueU32<$reg_desc> {
                FieldValueU32::<$reg_desc>::new(MASK, OFFSET, 0)
            }

            #[allow(dead_code)]
            #[allow(non_camel_case_types)]
            #[derive(Debug)]
            $(#[$outer])*
            pub enum Value {}

            impl TryFromValue<$valtype> for Value {
                type EnumType = Value;

                fn try_from_value(_v: $valtype) -> Option<Self::EnumType> {
                    Option::None
                }
            }
        }
    };

    // Implement the `RegisterDebugInfo` trait for the register. Refer to its
    // documentation for more information on the individual types and fields.
    (
        // final implementation of the macro
        @debug $valtype:ident, $reg_mod:ident, $reg_desc:ident, [$($field:ident),*]
    ) => {};

}

// PMP macros

#[macro_export]
macro_rules! register_bitfields_u8 {
    {
        $valtype:ident, $( $(#[$inner:meta])* $vis:vis $reg:ident $fields:tt ),* $(,)?
    } => {
        $(
            #[allow(non_snake_case)]
            $(#[$inner])*
            $vis mod $reg {
                // Visibility note: This is left always `pub` as it is not
                // meaningful to restrict access to the `Register` element of
                // the register module if the module itself is in scope
                //
                // (if you can access $reg, you can access $reg::Register)
                #[derive(Clone, Copy)]
                pub struct Register;
                impl $crate::RegisterLongName for Register {}

                use $crate::{FieldU8, FieldValueU8};

                $crate::register_bitmasks_u8!( $valtype, $reg, Register, $fields );
            }
        )*
    }
}

#[macro_export]
macro_rules! register_bitmasks_u8 {
    {
        // BITFIELD_NAME OFFSET(x)
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident OFFSET($offset:expr)),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u8!($valtype, $reg_desc, $(#[$inner])* $field, $offset, 1, []); )*
        $crate::register_bitmasks_u8!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        // BITFIELD_NAME OFFSET
        // All fields are 1 bit
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident $offset:expr ),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u8!($valtype, $reg_desc, $(#[$inner])* $field, $offset, 1, []); )*
        $crate::register_bitmasks_u8!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        // BITFIELD_NAME OFFSET(x) NUMBITS(y)
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident OFFSET($offset:expr) NUMBITS($numbits:expr) ),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u8!($valtype, $reg_desc, $(#[$inner])* $field, $offset, $numbits, []); )*
        $crate::register_bitmasks_u8!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        // BITFIELD_NAME OFFSET(x) NUMBITS(y) []
        $(#[$outer:meta])*
        $valtype:ident, $reg_mod:ident, $reg_desc:ident, [
            $( $(#[$inner:meta])* $field:ident OFFSET($offset:expr) NUMBITS($numbits:expr)
               $values:tt ),+ $(,)?
        ]
    } => {
        $(#[$outer])*
        $( $crate::register_bitmasks_u8!($valtype, $reg_desc, $(#[$inner])* $field, $offset, $numbits,
                              $values); )*
        $crate::register_bitmasks_u8!(@debug $valtype, $reg_mod, $reg_desc, [$($field),*]);
    };

    {
        $valtype:ident, $reg_desc:ident, $(#[$outer:meta])* $field:ident,
                    $offset:expr, $numbits:expr,
                    [$( $(#[$inner:meta])* $valname:ident = $value:expr ),+ $(,)?]
    } => { // this match arm is duplicated below with an allowance for 0 elements in the valname -> value array,
        // to seperately support the case of zero-variant enums not supporting non-default
        // representations.

        pub use $field::$field;

        #[allow(non_snake_case)]
        #[allow(unused)]
        $(#[$outer])*
        pub mod $field {
            #[allow(unused_imports)]
            use $crate::{FieldValueU8, TryFromValue, FieldU8};
            use super::$reg_desc;

            pub const MASK: u8 = $crate::bitmask!($numbits);
            pub const OFFSET: usize = $offset;

            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            #[flux_rs::sig(fn() -> FieldU8<$reg_desc>[bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)])]
            pub const fn $field() -> FieldU8<$reg_desc> {
                FieldU8::<$reg_desc>::new(MASK, OFFSET)
            }


            $(
            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            $(#[$inner])*
            mod $valname {
                use $crate::{FieldValueU8, TryFromValue};
                use super::$reg_desc;

                const MASK: u8 = $crate::bitmask!($numbits);
                const OFFSET: usize = $offset;
                const VALUE: u8 = $value;

                #[flux_rs::sig(fn() -> FieldValueU8<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(VALUE), bv_int_to_bv32(OFFSET))])]
                pub const fn $valname() -> FieldValueU8<$reg_desc> {
                FieldValueU8::<$reg_desc>::new(MASK, OFFSET, $value)
                }
            }
            pub use $valname::$valname;
            )*

            #[flux_rs::sig(fn() -> FieldValueU8<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET))])]
            pub const fn SET() -> FieldValueU8<$reg_desc> {
                FieldValueU8::<$reg_desc>::new(MASK, OFFSET, MASK)
            }

            #[flux_rs::sig(fn() -> FieldValueU8<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(0), bv_int_to_bv32(OFFSET))])]
            pub const fn CLEAR() -> FieldValueU8<$reg_desc> {
                FieldValueU8::<$reg_desc>::new(MASK, OFFSET, 0)
            }

            #[allow(dead_code)]
            #[allow(non_camel_case_types)]
            #[derive(Copy, Clone, Debug, Eq, PartialEq)]
            #[repr($valtype)] // so that values larger than isize::MAX can be stored
            $(#[$outer])*
            pub enum Value {
                $(
                    $(#[$inner])*
                    $valname = $value,
                )*
            }

            impl TryFromValue<$valtype> for Value {
                type EnumType = Value;

                fn try_from_value(v: $valtype) -> Option<Self::EnumType> {
                    match v {
                        $(
                            $(#[$inner])*
                            x if x == Value::$valname as $valtype => Some(Value::$valname),
                        )*

                        _ => Option::None
                    }
                }
            }

            impl From<Value> for FieldValueU8<$reg_desc> {
                fn from(v: Value) -> Self {
                    Self::new($crate::bitmask!($numbits), $offset, v as $valtype)
                }
            }
        }
    };
    {
        $valtype:ident, $reg_desc:ident, $(#[$outer:meta])* $field:ident,
                    $offset:expr, $numbits:expr,
                    []
    } => { //same pattern as previous match arm, for 0 elements in array. Removes code associated with array.

        pub use $field::$field;

        #[allow(non_snake_case)]
        #[allow(unused)]
        $(#[$outer])*
        pub mod $field {
            #[allow(unused_imports)]
            use $crate::{FieldValueU8, TryFromValue, FieldU8};
            use super::$reg_desc;

            const MASK: u8 = $crate::bitmask!($numbits);
            const OFFSET: usize = $offset;

            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            #[flux_rs::sig(fn() -> FieldU8<$reg_desc>[bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)])]
            pub const fn $field() -> FieldU8<$reg_desc> {
                FieldU8::<$reg_desc>::new(MASK, OFFSET)
            }


            #[allow(non_upper_case_globals)]
            #[allow(unused)]
            #[flux_rs::sig(fn() -> FieldValueU8<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET))])]
            pub const fn SET() -> FieldValueU8<$reg_desc> {
                FieldValueU8::<$reg_desc>::new(MASK, OFFSET, MASK)
            }


            #[flux_rs::sig(fn() -> FieldValueU8<$reg_desc>[bv_shl(bv_int_to_bv32(MASK), bv_int_to_bv32(OFFSET)), bv_shl(bv_int_to_bv32(0), bv_int_to_bv32(OFFSET))])]
            pub const fn CLEAR() -> FieldValueU8<$reg_desc> {
                FieldValueU8::<$reg_desc>::new(MASK, OFFSET, 0)
            }

            #[allow(dead_code)]
            #[allow(non_camel_case_types)]
            #[derive(Debug)]
            $(#[$outer])*
            pub enum Value {}

            impl TryFromValue<$valtype> for Value {
                type EnumType = Value;

                fn try_from_value(_v: $valtype) -> Option<Self::EnumType> {
                    Option::None
                }
            }
        }
    };

    // Implement the `RegisterDebugInfo` trait for the register. Refer to its
    // documentation for more information on the individual types and fields.
    (
        // final implementation of the macro
        @debug $valtype:ident, $reg_mod:ident, $reg_desc:ident, [$($field:ident),*]
    ) => {};

}

#[derive(Copy, Clone)]
#[flux_rs::opaque]
#[flux_rs::refined_by(val: bitvec<32>)]
#[flux_rs::invariant(val <= bv_int_to_bv32(u8::MAX))]
pub struct LocalRegisterCopyU8<R: RegisterLongName = ()> {
    inner: LocalRegisterCopy<u8, R>,
}

impl<R: RegisterLongName> LocalRegisterCopyU8<R> {
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn (value: u8) -> Self[bv_int_to_bv32(value)])]
    pub const fn new(value: u8) -> Self {
        LocalRegisterCopyU8 {
            inner: LocalRegisterCopy::new(value),
        }
    }

    /// Get the raw register value
    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn (&Self[@inner]) -> u8[bv_bv32_to_int(inner.val)])]
    pub fn get(&self) -> u8 {
        self.inner.value
    }

    /// Set the raw register value
    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn (self: &strg Self[@inner], value: u8) ensures self: Self { s: s.val == bv_int_to_bv32(value) })]
    pub fn set(&mut self, value: u8) {
        self.inner.value = value;
    }

    /// Read the value of the given field
    #[inline]
    #[flux_rs::trusted(reason = "flux wrappers")]
    #[flux_rs::sig(fn (&Self[@value], FieldU8<R>[@mask, @shift]) -> u8[bv_bv32_to_int((value & (mask << shift)) >> shift)])]
    // (val & (self.mask << self.shift)) >> self.shift
    pub fn read(&self, field: FieldU8<R>) -> u8 {
        field.inner.read(self.get())
    }

    #[inline]
    pub fn read_as_enum<E: TryFromValue<u8, EnumType = E>>(&self, field: FieldU8<R>) -> Option<E> {
        field.read_as_enum(self.get())
    }

    /// Check if one or more bits in a field are set
    #[inline]
    #[flux_rs::sig(fn (&Self[@value], FieldU8<R>[@mask, @shift]) -> bool[value & (mask << shift) != 0])]
    pub fn is_set(&self, field: FieldU8<R>) -> bool {
        field.is_set(self.get())
    }

    // /// Check if any bits corresponding to the mask in the passed `FieldValue` are set.
    // #[inline]
    // pub fn any_matching_bits_set(&self, field: FieldValue<T, R>) -> bool {
    //     field.any_matching_bits_set(self.get())
    // }

    // /// Check if all specified parts of a field match
    // #[inline]
    // pub fn matches_all(&self, field: FieldValue<T, R>) -> bool {
    //     field.matches_all(self.get())
    // }

    // /// Check if any of the passed parts of a field exactly match the contained
    // /// value. This allows for matching on unset bits, or matching on specific values
    // /// in multi-bit fields.
    // #[inline]
    // pub fn matches_any(&self, fields: &[FieldValue<T, R>]) -> bool {
    //     fields
    //         .iter()
    //         .any(|field| self.get() & field.mask() == field.value)
    // }

    // /// Do a bitwise AND operation of the stored value and the passed in value
    // /// and return a new LocalRegisterCopy.
    // #[inline]
    // pub fn bitand(&self, rhs: T) -> LocalRegisterCopy<T, R> {
    //     LocalRegisterCopy::new(self.value & rhs)
    // }

    // #[inline]
    // pub fn debug(&self) -> crate::debug::RegisterDebugValue<T, R>
    // where
    //     R: crate::debug::RegisterDebugInfo<T>,
    // {
    //     crate::debug::RegisterDebugValue {
    //         data: self.get(),
    //         _reg: core::marker::PhantomData,
    //     }
    // }
}
