//! Integer types that have a logical size measured in bits.
//!
//! This crate provides the [`UBitint`] trait and 128 types named
//! [`U1`](crate::U1) through [`U128`](crate::U128) that implement it. Each type
//! wraps the smallest primitive unsigned integer type that can contain it. The
//! types that are not the same width as their primitive type impose a validity
//! constraint---the value is represented in the least significant bits and the
//! upper bits are always clear.
//!
//! # Demo
//!
//! ```
//! // Recommended, but not required.
//! use bitint::prelude::*;
//!
//! // Use the bitint! macro to write a bitint literal. Underscores are
//! // permitted anywhere in a Rust literal and are encouraged for readability.
//! let seven = bitint!(7_U12);
//!
//! // Use the #[bitint_literals] attribute macro to write bitint literals
//! // anywhere inside an item. Here the item is a function, but it can also be
//! // useful on an impl block or inline module.
//! # demo();
//! #[bitint_literals]
//! fn demo() {
//!     let five = 5_U12;
//!
//!     // Arithmetic ops accept Self or the primitive type and panic or wrap
//!     // just like primitive arithmetic ops.
//!     assert_eq!(five + five, 10_U12);
//!     assert_eq!(five - 1_U12, 4_U12);
//!     assert_eq!(five * 2_U12, 10_U12);
//!     assert_eq!(five / 3_U12, 1_U12);
//!     assert_eq!(five % 3_U12, 2_U12);
//!     // If built with overflow-checks = true, this would panic.
//!     // If built with overflow-checks = false, this would wrap.
//!     // five + U12::MAX
//!
//!     // Checked arithmetic ops.
//!     assert_eq!(five.checked_add(10_U12), Some(15_U12));
//!     assert_eq!(five.checked_add(4095_U12), None);
//!
//!     // Wrapping arithmetic ops.
//!     assert_eq!(five.wrapping_add(10_U12), 15_U12);
//!     assert_eq!(five.wrapping_add(4095_U12), 4_U12);
//!
//!     // Zero-(extra)-cost unchecked arithmetic ops.
//!     #[cfg(feature = "unchecked_math")]
//!     {
//!         // SAFETY: 15 is in range for U12.
//!         assert_eq!(unsafe { five.unchecked_add(10_U12) }, 15_U12);
//!         // This would violate the safety condition and cause undefined
//!         // behavior.
//!         // unsafe { five.unchecked_add(4095_U12) }
//!     }
//!
//!     // Zero-cost conversion to a primitive type.
//!     assert_eq!(five.to_primitive(), 5);
//!
//!     // Checked constructor.
//!     assert_eq!(U12::new(5), Some(five));
//!     assert_eq!(U12::new(4096), None);
//!
//!     // Masking constructor.
//!     assert_eq!(U12::new_masked(5), five);
//!     assert_eq!(U12::new_masked(13 * 4096 + 5), five);
//!
//!     // Zero-cost unsafe constructor.
//!     // SAFETY: 5 is in range for U12.
//!     assert_eq!(unsafe { U12::new_unchecked(5) }, five);
//!     // This would violate the safety condition and cause undefined behavior.
//!     // unsafe { U12::new_unchecked(65536) }
//!
//!     // Zero-cost safe constructor, only for bitints that are the same width
//!     // as a primitive type.
//!     assert_eq!(U16::from_primitive(1234), 1234_U16);
//!
//!     // String conversions.
//!     assert_eq!(format!("{five}"), "5");
//!     assert_eq!(five.to_string(), "5");
//!     assert_eq!("5".parse::<U12>().unwrap(), 5_U12);
//! };
//! ```
//!
//! # Crate features
//!
//! * **unchecked_math** - Enables the `unchecked_*` methods on unsigned
//!   `bitint` types. Requires a nightly Rust compiler.
//!
#![cfg_attr(not(test), no_std)]
#![cfg_attr(
    feature = "unchecked_math",
    feature(unchecked_math),
    feature(const_inherent_unchecked_arith)
)]
#![cfg_attr(feature = "_nightly", feature(doc_cfg))]
#![deny(missing_docs)]
#![deny(rustdoc::broken_intra_doc_links)]

use core::fmt::{self, Display, Formatter};
use core::num::ParseIntError;

pub mod prelude;
mod traits;
mod types;

// For macro access via `$crate`.
#[doc(hidden)]
pub mod __private {
    pub use bitint_macros::bitint;
}

mod sealed {
    pub trait Sealed {}
}

pub use types::*;

/// The error type returned when a [`TryFrom`] conversion to a `bitint` fails.
#[derive(Debug)]
pub struct RangeError(pub(crate) ());

impl Display for RangeError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "value out of range for bitint type")
    }
}

/// The error type returned when parsing a string to a `bitint` fails.
#[derive(Debug)]
#[non_exhaustive]
pub enum ParseBitintError {
    /// Parsing failed because parsing to the primitive type failed.
    Parse(ParseIntError),
    /// Parsing failed because the primitive value was out of range.
    Range(RangeError),
}

impl Display for ParseBitintError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::Parse(e) => write!(f, "{e}"),
            Self::Range(e) => write!(f, "{e}"),
        }
    }
}

impl From<ParseIntError> for ParseBitintError {
    fn from(value: ParseIntError) -> Self {
        Self::Parse(value)
    }
}

impl From<RangeError> for ParseBitintError {
    fn from(value: RangeError) -> Self {
        Self::Range(value)
    }
}

pub use traits::*;

/// Constructs a `bitint` literal.
///
/// A `bitint` literal is an integer literal with a suffix consisting of `'U'`
/// followed by an integer, which must be at least one and at most 128.
///
/// This macro accepts one `bitint` literal which is checked against the
/// corresponding [`UBitint`] type's range and replaced with either a call to a
/// non-panicking const constructor or a compile error.
///
/// # Examples
///
/// ```
/// # use bitint::prelude::*;
/// // The suffix `U3` corresponds to the type `U3`. Underscores are permitted
/// // anywhere in a Rust literal and are encouraged for readability.
/// let x = bitint!(6_U3);
/// assert_eq!(x.to_primitive(), 6);
///```
///
/// ```compile_fail
/// # use bitint::prelude::*;
/// // This value is out of range for `U16`.
/// bitint!(65536_U16);
/// ```
#[macro_export]
macro_rules! bitint {
    ($($tt:tt)*) => {
        $crate::__private::bitint! { ($crate, $($tt)*) }
    };
}

/// Rewrites `bitint` literals in the item it is attached to.
///
/// A `bitint` literal is an integer literal with a suffix consisting of `'U'`
/// followed by an integer, which must be at least one and at most 128.
///
/// `bitint` literals are checked against the corresponding [`UBitint`] type's
/// range and replaced with either a call to a non-panicking const constructor
/// or a compile error. All other tokens are preserved.
///
/// # Examples
///
/// ```
/// # use bitint::prelude::*;
/// #[bitint_literals]
/// fn example() {
///     // The suffix `U3` corresponds to the type `U3`. Underscores are
///     // permitted anywhere in a Rust literal and are encouraged for
///     // readability.
///     let x = 6_U3;
///     assert_eq!(x.to_primitive(), 6);
/// }
/// ```
///
/// ```compile_fail
/// # use bitint::prelude::*;
/// #[bitint_literals]
/// fn example() {
///     // This value is out of range for `U16`.
///     let x = 65536_U16;
/// }
/// ```
pub use bitint_macros::bitint_literals;
