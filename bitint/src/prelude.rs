//! Convenience re-exports.

use paste::paste;
use seq_macro::seq;

#[doc(no_inline)]
pub use crate::{bitint, bitint_literals, PrimitiveSizedBitint, UBitint};

seq!(N in 1..=128 {
    paste! {
        #[doc(no_inline)]
        pub use crate::[<U N>];
    }
});
