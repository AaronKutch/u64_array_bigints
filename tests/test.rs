#![cfg(not(feature = "use_parity_uint"))]

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
