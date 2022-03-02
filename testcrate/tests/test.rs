use u64_array_bigints::{u256, Uint, U256};

#[test]
fn serialization_test() {
    let v123 = U256::from_dec_or_hex_str("123").unwrap();
    assert_eq!(v123.resize_to_u128(), 123);
    let v123e60 = U256::from_dec_or_hex_str(
        "123000000000000000000000000000000000000000000000000000000000000",
    )
    .unwrap();
    assert_eq!(
        v123.checked_mul(U256::checked_exp10(60).unwrap()).unwrap(),
        v123e60
    );
    assert_eq!(
        U256::from_dec_or_hex_str(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
        )
        .unwrap(),
        U256::max_value()
    );
    let max = U256::from_dec_or_hex_str(
        "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    )
    .unwrap();
    assert_eq!(max, U256::max_value());

    assert_eq!(U256::zero().to_hex_string(), "0x0");
    assert_eq!(U256::from_u32(0x1234u32).to_hex_string(), "0x1234");
    assert_eq!(
        U256::from_dec_or_hex_str(
            "0x1234ffffffffffffffffffffffffffffffffffffffffffffffffffffffff5678",
        )
        .unwrap()
        .to_hex_string(),
        "0x1234ffffffffffffffffffffffffffffffffffffffffffffffffffffffff5678"
    );

    assert_eq!(
        max.to_dec_string(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
}

#[test]
fn le_be_test() {
    assert_eq!(
        u256!(0x1234ffffffffffffffffffffffffffffffffffffffffffffffffffffffff5678).to_u8_array_be(),
        u256!(0x7856ffffffffffffffffffffffffffffffffffffffffffffffffffffffff3412).to_u8_array()
    );
    assert_eq!(
        U256::from_bytes_be(&[0xffu8; 32]).unwrap(),
        U256::max_value()
    );
    assert!(U256::from_bytes_be(&[0u8; 33]).is_none());
}

#[test]
fn to_hex_string() {
    assert_eq!(&U256::zero().to_hex_string(), "0x0");
    assert_eq!(&U256::from_u64_array([1, 0, 0, 0]).to_hex_string(), "0x1");
    assert_eq!(&U256::from_u64_array([0xa, 0, 0, 0]).to_hex_string(), "0xa");
    assert_eq!(
        &U256::from_u64_array([0xabcdef0, 9, 0, 0]).to_hex_string(),
        "0x9000000000abcdef0"
    );
    assert_eq!(
        &U256::from_u64_array([0, 0, 1, 0]).to_hex_string(),
        "0x100000000000000000000000000000000"
    );
    assert_eq!(
        &U256::from_u64_array([
            0x0123456789abcedf,
            0xfdecba9876543210,
            0x0f1e2d3c4b5a6978,
            0x13375ca1ab1e1337
        ])
        .to_hex_string(),
        "0x13375ca1ab1e13370f1e2d3c4b5a6978fdecba98765432100123456789abcedf"
    );
}

#[test]
fn format() {
    let x = u256!(0x0123456789abcedffdecba98765432100f1e2d3c4b5a697813375ca1ab1e1337);
    assert_eq!(
        format!("{}", x),
        "514631507721406819000807973055347587171986281168858714843337847970547503927"
    );
    assert_eq!(
        format!("{:x}", x),
        "123456789abcedffdecba98765432100f1e2d3c4b5a697813375ca1ab1e1337"
    );
    assert_eq!(
        format!("{:#x}", x),
        "0x123456789abcedffdecba98765432100f1e2d3c4b5a697813375ca1ab1e1337"
    );
}

#[test]
fn restricted() {
    assert_eq!(
        U256::from_dec_or_hex_str_restricted(&U256::max_value().to_hex_string()).unwrap(),
        U256::max_value()
    );
    assert_eq!(
        U256::from_dec_or_hex_str_restricted(&U256::max_value().to_dec_string()).unwrap(),
        U256::max_value()
    );
    assert!(U256::from_dec_or_hex_str_restricted("0x1_2").is_err());
    assert!(U256::from_dec_or_hex_str_restricted(
        "0115792089237316195423570985008687907853269984665640564039457584007913129639935"
    )
    .is_err());
}

#[cfg(not(miri))]
#[test]
fn all_byte_combos() {
    let mut s = [b'0'; 64];
    for i in 0..64 {
        for b in 0..=255u8 {
            s[s.len() - 1 - i] = b;
            match b {
                b'0'..=b'9' => {
                    if U256::from_hex_str_fast(&s).unwrap()
                        != U256::from_u8(b - b'0').wrapping_shl(i * 4)
                    {
                        dbg!(
                            &s,
                            b,
                            U256::from_u8(b - b'0').wrapping_shl(i * 4).to_hex_string(),
                            U256::from_hex_str_fast(&s).unwrap().to_hex_string()
                        );
                    }
                    assert!(
                        U256::from_hex_str_fast(&s).unwrap()
                            == U256::from_u8(b - b'0').wrapping_shl(i * 4)
                    );
                }
                b'a'..=b'f' => {
                    assert!(
                        U256::from_hex_str_fast(&s).unwrap()
                            == U256::from_u8(b - b'a' + 10).wrapping_shl(i * 4)
                    );
                }
                _ => {
                    assert!(U256::from_hex_str_fast(&s).is_err());
                }
            }
            match b {
                b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' | b'_' => {
                    assert!(U256::from_bytes_radix(&s, 16).is_ok());
                }
                _ => {
                    assert!(U256::from_bytes_radix(&s, 16).is_err());
                }
            }
            // set back
            s[s.len() - 1 - i] = b'0';
        }
    }
}

#[test]
#[should_panic]
fn len_0() {
    let _ = Uint::<0>::from_u64_array([]);
}
