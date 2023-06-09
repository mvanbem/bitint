# bitint

[![crates.io][crates-badge]][crates-url]
[![docs.rs][docs-badge]][docs-url]
[![CI Status][ci-badge]][ci-url]

[crates-badge]: https://img.shields.io/crates/v/bitint
[crates-url]: https://crates.io/crates/bitint
[docs-badge]: https://img.shields.io/docsrs/bitint
[docs-url]: https://docs.rs/bitint
[ci-badge]: https://img.shields.io/github/actions/workflow/status/mvanbem/bitint/ci.yml?branch=main&label=CI&logo=github
[ci-url]: https://github.com/mvanbem/bitint/actions?query=workflow%3ACI+branch%3Amain

A bit-integer library for Rust. `bitint`s are like primitive integer types, but
their logical width is measured in bits.

This crate provides the `UBitint` trait and 128 types named `U1` through `U128`
that implement it. Each type wraps the smallest primitive unsigned integer type
that can contain it. The types that are not the same width as their primitive
type impose a validity constraint---the value is represented in the least
significant bits and the upper bits are always clear.

## Demo

```rust
// Recommended, but not required.
use bitint::prelude::*;

// Use the bitint! macro to write a bitint literal. Underscores are permitted
// anywhere in a Rust literal and are encouraged for readability.
let seven = bitint!(7_U12);

// Use the #[bitint_literals] attribute macro to write bitint literals anywhere
// inside an item. Here the item is a function, but it can also be useful on an
// impl block or inline module.
# demo();
#[bitint_literals]
fn demo() {
    let five = 5_U12;

    // Arithmetic ops accept Self or the primitive type and panic or wrap just
    // like primitive arithmetic ops.
    assert_eq!(five + five, 10_U12);
    assert_eq!(five - 1_U12, 4_U12);
    assert_eq!(five * 2_U12, 10_U12);
    assert_eq!(five / 3_U12, 1_U12);
    assert_eq!(five % 3_U12, 2_U12);
    // If built with overflow-checks = true, this would panic.
    // If built with overflow-checks = false, this would wrap.
    // five + U12::MAX

    // Checked arithmetic ops.
    assert_eq!(five.checked_add(10_U12), Some(15_U12));
    assert_eq!(five.checked_add(4095_U12), None);

    // Wrapping arithmetic ops.
    assert_eq!(five.wrapping_add(10_U12), 15_U12);
    assert_eq!(five.wrapping_add(4095_U12), 4_U12);

    // Zero-(extra)-cost unchecked arithmetic ops.
    #[cfg(feature = "unchecked_math")]
    {
        // SAFETY: 15 is in range for U12.
        assert_eq!(unsafe { five.unchecked_add(10_U12) }, 15_U12);
        // This would violate the safety condition and cause undefined behavior.
        // unsafe { five.unchecked_add(4095_U12) }
    }

    // Zero-cost conversion to a primitive type.
    assert_eq!(five.to_primitive(), 5);

    // Checked constructor.
    assert_eq!(U12::new(5), Some(five));
    assert_eq!(U12::new(4096), None);

    // Masking constructor.
    assert_eq!(U12::new_masked(5), five);
    assert_eq!(U12::new_masked(13 * 4096 + 5), five);

    // Zero-cost unsafe constructor.
    // SAFETY: 5 is in range for U12.
    assert_eq!(unsafe { U12::new_unchecked(5) }, five);
    // This would violate the safety condition and cause undefined behavior.
    // unsafe { U12::new_unchecked(65536) }

    // Zero-cost safe constructor, only for bitints that are the same width as a
    // primitive type.
    assert_eq!(U16::from_primitive(1234), 1234_U16);

    // String conversions.
    assert_eq!(format!("{five}"), "5");
    assert_eq!(five.to_string(), "5");
    assert_eq!("5".parse::<U12>().unwrap(), 5_U12);
};
```

## Crate features

* **unchecked_math** - Enables the `unchecked_*` methods on unsigned `bitint`
  types. Requires a nightly Rust compiler.
