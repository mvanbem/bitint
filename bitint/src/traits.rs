use core::fmt::{Debug, Display};
use core::hash::Hash;
use core::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

use num_traits::{Num, NumAssignOps};

use crate::sealed::Sealed;

/// Unsigned `bitint` types.
///
/// There is one type implementing `UBitint` for each bit width from 1 to 128
/// inclusive.
pub trait UBitint:
    Copy
    + Debug
    + Display
    + Hash
    + Eq
    + Ord
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + TryFrom<Self::Primitive>
    + Into<Self::Primitive>
    + Num
    + NumAssignOps
    + Sized
    + Sealed
{
    /// The primitive type that this type wraps.
    type Primitive: From<Self> + TryInto<Self>;

    /// The bit width of this type.
    const BITS: u32;
    /// The bit mask for the bits that may be set in values of this type.
    const MASK: Self::Primitive;

    /// The smallest value of this type.
    const MIN: Self;
    /// The largest value of this type.
    const MAX: Self;

    /// The value `0` represented in this type.
    const ZERO: Self;
    /// The value `1` represented in this type.
    const ONE: Self;

    /// Creates an unsigned `bitint` value from a primitive value if it is in
    /// range for this type, as determined by
    /// [`is_in_range`](Self::is_in_range).
    #[must_use]
    fn new(value: Self::Primitive) -> Option<Self>;

    /// Creates an unsigned `bitint` value by masking off the upper bits of a
    /// primitive value.
    ///
    /// This conversion is lossless if the value is in range for this type, as
    /// determined by [`is_in_range`](Self::is_in_range).
    #[must_use]
    fn new_masked(value: Self::Primitive) -> Self;

    /// Creates an unsigned `bitint` value from a primitive value without
    /// checking whether it is in range for this type.
    ///
    /// This is a zero-cost conversion.
    ///
    /// # Safety
    ///
    /// The value must be in range for this type, as determined by
    /// [`is_in_range`](Self::is_in_range).
    #[must_use]
    unsafe fn new_unchecked(value: Self::Primitive) -> Self;

    /// Checks whether a primitive value is in range for this type.
    ///
    /// There are a few equivalent ways to express this check.
    ///
    /// - The unused most significant bits are clear: `(value & !Self::MASK) ==
    ///   0`
    /// - The value is between [`MIN`](Self::MIN) and [`MAX`](Self::MAX),
    ///   inclusive: `value >= Self::MIN.as_primitive() && value <=
    ///   Self::MAX.as_primitive()`
    ///
    #[must_use]
    fn is_in_range(value: Self::Primitive) -> bool;
}
