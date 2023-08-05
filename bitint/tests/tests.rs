use std::cmp::Ordering;

use bitint::prelude::*;

#[bitint_literals]
#[test]
fn test_debug() {
    assert_eq!(format!("{:?}", 1_U1), "U1(1)");
    assert_eq!(format!("{:?}", 1234_U12), "U12(1234)");
    assert_eq!(format!("{:?}", 65535_U16), "U16(65535)");
}

#[bitint_literals]
#[test]
fn test_display() {
    assert_eq!(format!("{}", 1_U1), "1");
    assert_eq!(format!("{}", 1234_U12), "1234");
    assert_eq!(format!("{}", 65535_U16), "65535");
}

#[bitint_literals]
#[test]
fn test_bit_cmp() {
    assert_eq!(0b0100_U4.cmp(&0b0101_U4), Ordering::Less);
    assert_eq!(0b1011_U4.cmp(&0b1011_U4), Ordering::Equal);
    assert_eq!(0b1111_U4.cmp(&0b1110_U4), Ordering::Greater);
    assert!(0b0010100_U7 < 0b1010100_U7);
    assert!(0b0010111_U7 <= 0b0010111_U7);
    assert!(0b1111111_U7 == 0b1111111_U7);
    assert!(0b1011101_U7 >= 0b1011101_U7);
    assert!(0b1010001_U7 > 0b1010000_U7);
}

#[bitint_literals]
#[test]
fn test_bit_ops() {
    assert_eq!(0b1000_U4, 0b1010_U4 & 0b1100_U4);
    assert_eq!(0b1110_U4, 0b1010_U4 | 0b1100_U4);
    assert_eq!(0b0110_U4, 0b1010_U4 ^ 0b1100_U4);
    assert_eq!(0b00110101_U8, !0b11001010_U8);
    assert_eq!(0b00011100110101_U14, !0b11100011001010_U14);
}

#[bitint_literals]
#[test]
fn test_bit_assign_ops() {
    assert_eq!(0b1000_U4, {
        let mut x = 0b1010_U4;
        x &= 0b1100_U4;
        x
    });
    assert_eq!(0b1110_U4, {
        let mut x = 0b1010_U4;
        x |= 0b1100_U4;
        x
    });
    assert_eq!(0b0110_U4, {
        let mut x = 0b1010_U4;
        x ^= 0b1100_U4;
        x
    });
}

mod hostile_environment {
    mod bitint {}
    mod core {}

    const _: ::bitint::U5 = ::bitint::bitint!(1_U5);

    #[allow(unused)]
    #[::bitint::bitint_literals]
    fn example() {
        let _ = 1_U5;
    }
}

#[test]
#[cfg_attr(not(feature = "_trybuild_tests"), ignore)]
fn trybuild_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests_error/*.rs");
}
