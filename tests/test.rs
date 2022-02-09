use u64_array_bigints::{Uint, U256};

#[test]
fn to_hex_string() {
    assert_eq!(&U256::zero().to_hex_string(), "0x0");
    assert_eq!(&U256(Uint([1, 0, 0, 0])).to_hex_string(), "0x1");
    assert_eq!(&U256(Uint([0xa, 0, 0, 0])).to_hex_string(), "0xa");
    assert_eq!(
        &U256(Uint([0xabcdef0, 9, 0, 0])).to_hex_string(),
        "0x9000000000abcdef0"
    );
    assert_eq!(
        &U256(Uint([0, 0, 1, 0])).to_hex_string(),
        "0x100000000000000000000000000000000"
    );
    assert_eq!(
        &U256(Uint([
            0x0123456789abcedf,
            0xfdecba9876543210,
            0x0f1e2d3c4b5a6978,
            0x13375ca1ab1e1337
        ]))
        .to_hex_string(),
        "0x13375ca1ab1e13370f1e2d3c4b5a6978fdecba98765432100123456789abcedf"
    );
}

/*
#[test]
fn serialization_test() {
    let v123 = U256::from_dec_or_hex_str("123").unwrap();
    assert_eq!(v123.low_u128(), 123);
    let v123e60 = U256::from_dec_or_hex_str(
        "123000000000000000000000000000000000000000000000000000000000000",
    )
    .unwrap();
    assert_eq!(v123.checked_mul(U256::exp10(60)).unwrap(), v123e60);
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
    assert_eq!(U256::from(0x1234u32).to_hex_string(), "0x1234");
    assert_eq!(
        U256::from_dec_or_hex_str(
            "0x1234ffffffffffffffffffffffffffffffffffffffffffffffffffffffff5678",
        )
        .unwrap()
        .to_hex_string(),
        "0x1234ffffffffffffffffffffffffffffffffffffffffffffffffffffffff5678"
    );

    assert_eq!(
        max.to_string(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
}

#[test]
fn le_be_test() {
    assert_eq!(
        U256::from_dec_or_hex_str(
            "0x1234ffffffffffffffffffffffffffffffffffffffffffffffffffffffff5678",
        )
        .unwrap()
        .to_u8_array_be(),
        U256::from_dec_or_hex_str(
            "0x7856ffffffffffffffffffffffffffffffffffffffffffffffffffffffff3412",
        )
        .unwrap()
        .to_u8_array()
    );
    assert_eq!(
        U256::from_bytes_be(&[0xffu8; 32]).unwrap(),
        U256::max_value()
    );
    assert!(U256::from_bytes_be(&[0u8; 33]).is_none());
}
*/
