//! The unsigned `bitint` types [`U1`] through [`U128`].

use core::cmp::Ordering;
use core::fmt::{self, Display, Formatter};
use core::hash::{Hash, Hasher};
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Rem, RemAssign, Sub, SubAssign,
};
use core::str::FromStr;

use assume::assume;
use num_traits::{Num, One, Zero};
use paste::paste;
use seq_macro::seq;

use crate::{ParseBitintError, RangeError, UBitint};

macro_rules! define_ubitint_type {
    ($a:literal..$b:literal: $primitive:ident; $flag:tt) => {
        seq!(N in $a..$b { define_ubitint_type!(N: $primitive; $flag); });
    };
    ($bits:literal: $primitive:ident; $flag:tt) => {
        paste! {
            define_ubitint_type!(@define [<U $bits>] $primitive $bits $flag);
        }
    };
    (@define $self:ident $primitive:ident $bits:literal $flag:tt) => {
        #[derive(Clone, Copy, Debug)]
        #[doc = define_ubitint_type!(@type_doc $bits $primitive $flag)]
        #[repr(transparent)]
        pub struct $self($primitive);

        impl $self {
            /// The bit width of this type.
            ///
            /// See also: [`UBitint::BITS`]
            pub const BITS: u32 = $bits;

            /// The bit mask for the bits that may be set in values of this
            /// type.
            ///
            /// See also: [`UBitint::MASK`]
            pub const MASK: $primitive = match (1 as $primitive).checked_shl($bits) {
                Some(x) => x.wrapping_sub(1),
                None => $primitive::MAX,
            };

            /// The smallest value of this type.
            ///
            /// See also: [`UBitint::MIN`]
            pub const MIN: Self = Self::new_masked(0);

            /// The largest value of this type.
            ///
            /// See also: [`UBitint::MAX`]
            pub const MAX: Self = Self::new_masked($primitive::MAX);

            /// The value `0` represented in this type.
            ///
            /// See also: [`UBitint::ZERO`], [`num_traits::Zero`]
            pub const ZERO: Self = Self::new_masked(0);

            /// The value `1` represented in this type.
            ///
            /// See also: [`UBitint::ONE`], [`num_traits::One`]
            pub const ONE: Self = Self::new_masked(1);

            /// Creates a `bitint` from a primitive value if it is in range for
            /// this type, as determined by [`is_in_range`](Self::is_in_range).
            ///
            /// This method is a `const` variant of [`UBitint::new`].
            #[inline(always)]
            #[must_use]
            pub const fn new(value: $primitive) -> Option<Self> {
                if Self::is_in_range(value) {
                    Some(Self(value))
                } else {
                    None
                }
            }

            /// Creates a `bitint` by masking off the upper bits of a primitive
            /// value.
            ///
            /// This conversion is lossless if the value is in range for this
            /// type, as determined by [`is_in_range`](Self::is_in_range).
            ///
            /// This method is a `const` variant of [`UBitint::new_masked`].
            #[inline(always)]
            #[must_use]
            pub const fn new_masked(value: $primitive) -> Self {
                Self(value & Self::MASK)
            }

            /// Creates a `bitint` from a primitive value without checking
            /// whether it is in range for this type.
            ///
            /// # Safety
            ///
            /// The value must be in range for this type, as determined by
            /// [`is_in_range`](Self::is_in_range).
            ///
            /// This method is a `const` variant of [`UBitint::new_unchecked`].
            #[inline(always)]
            #[must_use]
            pub const unsafe fn new_unchecked(value: $primitive) -> Self {
                assume!(unsafe: Self::is_in_range(value));
                Self(value)
            }

            define_ubitint_type!(@from_primitive $primitive $flag);

            /// Converts the value to a primitive type.
            ///
            /// The result is in range for this type, as determined by
            /// [`is_in_range`](Self::is_in_range).
            #[inline(always)]
            #[must_use]
            pub const fn to_primitive(self) -> $primitive {
                assume!(unsafe: Self::is_in_range(self.0));
                self.0
            }

            /// Checks whether a primitive value is in range for this type.
            ///
            /// There are a few equivalent ways to express this check.
            ///
            /// - The unused most significant bits are clear: `(value &
            ///   !Self::MASK) == 0`
            /// - The value is between [`MIN`](Self::MIN) and
            ///   [`MAX`](Self::MAX), inclusive: `value >=
            ///   Self::MIN.as_primitive() && value <= Self::MAX.as_primitive()`
            ///
            /// This method is a `const` variant of [`UBitint::is_in_range`].
            #[allow(clippy::bad_bit_mask)] // For primitive widths.
            #[inline(always)]
            #[must_use]
            pub const fn is_in_range(value: $primitive) -> bool {
                value & !Self::MASK == 0
            }

            define_ubitint_type!(@checked_op_method checked_add "addition" "+" "overflow occurred");
            define_ubitint_type!(@unchecked_op_method unchecked_add "addition" "+");
            define_ubitint_type!(@checked_op_method checked_sub "subtraction" "-" "overflow occurred");
            define_ubitint_type!(@unchecked_op_method unchecked_sub "subtraction" "-");
            define_ubitint_type!(@checked_op_method checked_mul "multiplication" "*" "overflow occurred");
            define_ubitint_type!(@unchecked_op_method unchecked_mul "multiplication" "*");
            define_ubitint_type!(@checked_op_method checked_div "division" "/" "`rhs == 0`");
            define_ubitint_type!(@checked_op_method checked_rem "remainder" "%" "`rhs == 0`");
            define_ubitint_type!(@wrapping_op_method wrapping_add "addition" "+");
            define_ubitint_type!(@wrapping_op_method wrapping_sub "subtraction" "-");
            define_ubitint_type!(@wrapping_op_method wrapping_mul "multiplication" "*");
        }

        impl crate::sealed::Sealed for $self {}

        impl UBitint for $self {
            type Primitive = $primitive;

            const BITS: u32 = Self::BITS;
            const MASK: $primitive = Self::MASK;
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
            const ZERO: Self = Self::ZERO;
            const ONE: Self = Self::ONE;

            #[inline(always)]
            fn new(value: $primitive) -> Option<Self> {
                Self::new(value)
            }

            #[inline(always)]
            fn new_masked(value: $primitive) -> Self {
                Self::new_masked(value)
            }

            #[inline(always)]
            unsafe fn new_unchecked(value: $primitive) -> Self {
                Self::new_unchecked(value)
            }

            #[inline(always)]
            fn is_in_range(value: $primitive) -> bool {
                Self::is_in_range(value)
            }
        }

        impl Zero for $self {
            #[inline(always)]
            fn zero() -> Self {
                Self::ZERO
            }

            #[inline(always)]
            fn is_zero(&self) -> bool {
                *self == Self::ZERO
            }
        }

        impl One for $self {
            #[inline(always)]
            fn one() -> Self {
                Self::ONE
            }

            #[inline(always)]
            fn is_one(&self) -> bool {
                *self == Self::ONE
            }
        }

        impl FromStr for $self {
            type Err = ParseBitintError;

            fn from_str(s: &str) -> Result<Self, ParseBitintError> {
                Self::new($primitive::from_str(s)?)
                    .ok_or_else(|| RangeError(()).into())
            }
        }

        impl Num for $self {
            type FromStrRadixErr = ParseBitintError;

            fn from_str_radix(
                str: &str,
                radix: u32
            ) -> Result<Self, ParseBitintError> {
                Self::new($primitive::from_str_radix(str, radix)?)
                    .ok_or_else(|| RangeError(()).into())
            }
        }

        impl Display for $self {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                write!(f, "{}", self.to_primitive())
            }
        }

        impl From<$self> for $primitive {
            #[inline(always)]
            fn from(value: $self) -> Self {
                value.to_primitive()
            }
        }

        impl PartialEq for $self {
            #[inline(always)]
            fn eq(&self, other: &Self) -> bool {
                self.to_primitive() == other.to_primitive()
            }
        }

        impl Eq for $self {}

        impl Hash for $self {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.to_primitive().hash(state);
            }
        }

        impl PartialOrd for $self {
            #[inline(always)]
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }

            // As of Rust 1.71, leveraging the default function impls can result
            // in poor codegen. (Rather than compare the primitive, it computes
            // the Ordering discriminant and compares with that instead.)

            #[inline(always)]
            fn lt(&self, other: &Self) -> bool {
                self.to_primitive() < other.to_primitive()
            }

            #[inline(always)]
            fn le(&self, other: &Self) -> bool {
                self.to_primitive() <= other.to_primitive()
            }

            #[inline(always)]
            fn gt(&self, other: &Self) -> bool {
                self.to_primitive() > other.to_primitive()
            }

            #[inline(always)]
            fn ge(&self, other: &Self) -> bool {
                self.to_primitive() >= other.to_primitive()
            }
        }

        impl Ord for $self {
            #[inline(always)]
            fn cmp(&self, other: &Self) -> Ordering {
                self.to_primitive().cmp(&other.to_primitive())
            }
        }

        impl Not for $self {
            type Output = Self;

            #[inline(always)]
            fn not(self) -> Self {
                self ^ Self::MAX
            }
        }

        define_ubitint_type!(@impl_from $self $primitive $flag);
        define_ubitint_type!(@impl_op $self $primitive Add::add);
        define_ubitint_type!(@impl_op $self $primitive Div::div);
        define_ubitint_type!(@impl_op $self $primitive Mul::mul);
        define_ubitint_type!(@impl_op $self $primitive Rem::rem);
        define_ubitint_type!(@impl_op $self $primitive Sub::sub);
        define_ubitint_type!(@impl_bit_op $self $primitive BitAnd::bitand);
        define_ubitint_type!(@impl_bit_op $self $primitive BitOr::bitor);
        define_ubitint_type!(@impl_bit_op $self $primitive BitXor::bitxor);
        define_ubitint_type!(@impl_op_assign $self Add::add);
        define_ubitint_type!(@impl_op_assign $self Div::div);
        define_ubitint_type!(@impl_op_assign $self Mul::mul);
        define_ubitint_type!(@impl_op_assign $self Rem::rem);
        define_ubitint_type!(@impl_op_assign $self Sub::sub);
        define_ubitint_type!(@impl_op_assign $self BitAnd::bitand);
        define_ubitint_type!(@impl_op_assign $self BitOr::bitor);
        define_ubitint_type!(@impl_op_assign $self BitXor::bitxor);
        define_ubitint_type!(@impl_num_trait $self CheckedAdd::checked_add Option<Self>);
        define_ubitint_type!(@impl_num_trait $self CheckedSub::checked_sub Option<Self>);
        define_ubitint_type!(@impl_num_trait $self CheckedMul::checked_mul Option<Self>);
        define_ubitint_type!(@impl_num_trait $self CheckedDiv::checked_div Option<Self>);
        define_ubitint_type!(@impl_num_trait $self CheckedRem::checked_rem Option<Self>);
        define_ubitint_type!(@impl_num_trait $self WrappingAdd::wrapping_add Self);
        define_ubitint_type!(@impl_num_trait $self WrappingSub::wrapping_sub Self);
        define_ubitint_type!(@impl_num_trait $self WrappingMul::wrapping_mul Self);
    };
    (@type_doc $bits:literal $primitive:ident upper_bits_clear) => {
        concat!(
            "The ", stringify!($bits), "-bit unsigned `bitint` type.",
            "\n\n",
            "# Layout",
            "\n\n",
            "This type is `#[repr(transparent)]` to [`", stringify!($primitive), "`], but imposes ",
            "additional invariants.",
            "\n\n",
            "# Invariants",
            "\n\n",
            "The value is represented in the least significant bits of a [`",
            stringify!($primitive),
            "`]. The unused most significant bits are always clear.",
        )
    };
    (@type_doc $bits:literal $primitive:ident any_bit_pattern) => {
        concat!(
            "The ", stringify!($bits), "-bit unsigned `bitint` type.",
            "\n\n",
            "# Layout",
            "\n\n",
            "This type is `#[repr(transparent)]` to [`", stringify!($primitive), "`].",
        )
    };
    (@from_primitive $primitive:ident any_bit_pattern) => {
        /// Creates a `bitint` from a primitive value.
        ///
        /// This method is only provided for the `bitint` types that do not
        /// impose additional invariants: [`U8`], [`U16`], [`U32`], [`U64`], and
        /// [`U128`].
        #[inline(always)]
        #[must_use]
        pub const fn from_primitive(value: $primitive) -> Self {
            Self(value)
        }
    };
    (@from_primitive $primitive:ident upper_bits_clear) => {};
    (@checked_op_method $method:ident $desc:literal $op:literal $none_case:literal) => {
        #[doc = concat!(
            "Checked integer ", $desc, ". Computes `self ", $op, " rhs`, returning `None` if ",
            $none_case, ".",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn $method(self, rhs: Self) -> Option<Self> {
            match self.to_primitive().$method(rhs.to_primitive()) {
                Some(x) => Self::new(x),
                None => None,
            }
        }
    };
    (@wrapping_op_method $method:ident $desc:literal $op:literal) => {
        #[doc = concat!(
            "Wrapping (modular) ", $desc, ". Computes `self ", $op, " rhs`, wrapping around at ",
            "the boundary of the type.",
        )]
        #[inline(always)]
        #[must_use]
        pub const fn $method(self, rhs: Self) -> Self {
            Self::new_masked(self.to_primitive().$method(rhs.to_primitive()))
        }
    };
    (@unchecked_op_method $method:ident $desc:literal $op:literal) => {
        #[cfg(feature = "unchecked_math")]
        #[cfg_attr(feature = "_nightly", doc(cfg(unchecked_math)))]
        #[doc = concat!(
            "Unchecked integer ", $desc, ". Computes `self ", $op, " rhs`, assuming overflow ",
            "cannot occur.",
            "\n\n",
            "# Safety",
            "\n\n",
            "The result must be in range for this type, as determined by ",
            "[`is_in_range`](Self::is_in_range).",
        )]
        #[inline(always)]
        pub const unsafe fn $method(self, rhs: Self) -> Self {
            Self::new_unchecked(self.to_primitive().$method(rhs.to_primitive()))
        }
    };
    (@impl_from $self:ident $primitive:ident any_bit_pattern) => {
        impl From<$primitive> for $self {
            #[inline(always)]
            fn from(value: $primitive) -> Self {
                Self(value)
            }
        }
    };
    (@impl_from $self:ident $primitive:ident upper_bits_clear) => {
        impl TryFrom<$primitive> for $self {
            type Error = RangeError;

            #[inline(always)]
            fn try_from(value: $primitive) -> Result<Self, RangeError> {
                Self::new(value).ok_or(RangeError(()))
            }
        }
    };
    (@impl_op $self:ident $primitive:ident $trait:ident::$method:ident) => {
        impl $trait for $self {
            type Output = Self;

            #[inline(always)]
            fn $method(self, rhs: Self) -> Self {
                let result = $trait::$method(self.to_primitive(), rhs.to_primitive());
                // Perform a sentinel operation with overflow behavior that
                // depends on the build configuration:
                // - With overflow-checks enabled, this panics on overflow. Even
                //   though the result is unused, the optimizer should retain
                //   its side effects.
                // - With overflow-checks disabled, this wraps on overflow. The
                //   result is unused and there are no side effects, so it is
                //   likely to be optimized out entirely.
                let _ = result + ($primitive::MAX - Self::MAX.to_primitive());
                // We must either wrap or panic here. The unchecked constructor
                // is unsafe so calling it would be unsound.
                Self::new_masked(result)
            }
        }
    };
    (@impl_bit_op $self:ident $primitive:ident $trait:ident::$method:ident) => {
        impl $trait for $self {
            type Output = Self;

            #[inline(always)]
            fn $method(self, rhs: Self) -> Self {
                let result = $trait::$method(self.to_primitive(), rhs.to_primitive());

                // SAFETY: The unused upper bits are clear in both operands, so
                // they will be clear in the result. This holds for BitAnd,
                // BitOr, and BitXor.
                unsafe { Self::new_unchecked(result) }
            }
        }
    };
    (@impl_num_trait $self:ident $trait:ident::$method:ident $return:ty) => {
        impl num_traits::$trait for $self {
            #[inline(always)]
            fn $method(&self, v: &Self) -> $return {
                (*self).$method(*v)
            }
        }
    };
    (@impl_op_assign $self:ident $trait:ident::$method:ident) => {
        paste! {
            impl [<$trait Assign>] for $self {
                #[inline(always)]
                fn [<$method _assign>](&mut self, rhs: Self) {
                    *self = $trait::$method(*self, rhs);
                }
            }
        }
    };
}

define_ubitint_type!(1..8: u8; upper_bits_clear);
define_ubitint_type!(8: u8; any_bit_pattern);
define_ubitint_type!(9..16: u16; upper_bits_clear);
define_ubitint_type!(16: u16; any_bit_pattern);
define_ubitint_type!(17..32: u32; upper_bits_clear);
define_ubitint_type!(32: u32; any_bit_pattern);
define_ubitint_type!(33..64: u64; upper_bits_clear);
define_ubitint_type!(64: u64; any_bit_pattern);
define_ubitint_type!(65..128: u128; upper_bits_clear);
define_ubitint_type!(128: u128; any_bit_pattern);

impl From<bool> for U1 {
    #[inline(always)]
    fn from(value: bool) -> Self {
        // SAFETY: `bool` and `U1` have the same size (1), alignment (1), and
        // valid bit patterns (0u8 and 1u8).
        unsafe { core::mem::transmute(value) }
    }
}

impl From<U1> for bool {
    #[inline(always)]
    fn from(value: U1) -> Self {
        // SAFETY: `bool` and `U1` have the same size (1), alignment (1), and
        // valid bit patterns (0u8 and 1u8).
        unsafe { core::mem::transmute(value) }
    }
}

/// A type-level function returning a [`UBitint`].
pub trait FnUBitint {
    /// The resulting type.
    type Type: UBitint;
}

/// Maps each bit width to its corresponding [`UBitint`] type.
pub enum UBitintForWidth<const WIDTH: usize> {}

macro_rules! impl_ubitint_for_width {
    ($width:literal) => {
        paste! {
            impl FnUBitint for UBitintForWidth<$width> {
                type Type = [<U $width>];
            }
        }
    };
}
seq!(N in 1..=128 { impl_ubitint_for_width!(N); });
