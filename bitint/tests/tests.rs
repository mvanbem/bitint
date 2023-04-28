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
fn test_bit_ops() {
    assert_eq!(0b1000_U4, 0b1010_U4 & 0b1100);
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
        x &= 0b1100;
        x
    });
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

#[test]
fn trybuild_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests_error/*.rs");
}
