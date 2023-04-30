//! `bitint` tests for profiles with `overflow-checks = true`.
//!
//! `bitint` operators work in two stages. First, they convert both operands to
//! the primitive type (an infallible, zero-cost operation) and perform the
//! operation in the primitive type. Then they convert the result back to the
//! `bitint` type.
//!
//! In order to present primitive-like behavior, both of these stages should
//! panic on overflow when overflow checks are enabled.
#![allow(arithmetic_overflow)]
#![cfg(test)]

use std::panic::catch_unwind;

use bitint::prelude::*;

#[test]
fn test_profile() {
    if let Ok(_) = catch_unwind(|| 255u8 + 1u8) {
        panic!("this crate expects to be tested with overflow-checks enabled");
    }
}

// NOTE: bitint addition cannot overflow in the primitive op.

#[bitint_literals]
#[test]
#[should_panic]
fn test_bitint_add_overflow_in_conversion_panics() {
    let _ = 127_U7 + 1_U7;
}

#[bitint_literals]
#[test]
#[should_panic]
fn test_bitint_sub_overflow_in_primitive_op_panics() {
    let _ = 0_U7 - 1_U7;
}

// NOTE: bitint subtraction cannot overflow in the conversion back to bitint.

#[bitint_literals]
#[test]
#[should_panic]
fn test_bitint_mul_overflow_in_primitive_op_panics() {
    let _ = 127_U7 * 127_U7;
}

#[bitint_literals]
#[test]
#[should_panic]
fn test_bitint_mul_overflow_in_conversion_panics() {
    let _ = 127_U7 * 2_U7;
}
