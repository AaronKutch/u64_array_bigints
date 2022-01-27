use u64_array_bigints::U256;

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

    assert_eq!(
        max.to_string(),
        "115792089237316195423570985008687907853269984665640564039457584007913129639935"
    );
}
