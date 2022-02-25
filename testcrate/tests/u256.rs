use awint::{bw, inlawi, Bits, ExtAwi, InlAwi};
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
use testcrate::*;
use u64_array_bigints::{u256, U256};

#[test]
fn specific() {
    assert!(U256::from_bytes(&[0; 33]).is_none());
    assert!(U256::from_bytes_be(&[0; 33]).is_none());
    assert!(
        u256!(0x80000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000)
            .shl1()
            .is_none()
    );
    assert!(u256!(0).checked_shl(256).is_none());
    assert!(u256!(0).checked_shr(256).is_none());
    assert!(u256!(0).divide(u256!(0)).is_none());
    assert!(u256!(0).checked_short_divide(0).is_none());
}

// fuzz U256 specific stuff
fn identities_inner(x0: U256, x1: U256, y0: &Bits, y2: &mut Bits) {
    assert_eq!(x0.resize_to_bool(), y0.to_bool());
    assert_eq!(x0.resize_to_u8(), y0.to_u8());
    assert_eq!(x0.resize_to_u16(), y0.to_u16());
    assert_eq!(x0.resize_to_u32(), y0.to_u32());
    assert_eq!(x0.resize_to_u64(), y0.to_u64());
    assert_eq!(x0.resize_to_u128(), y0.to_u128());
    assert_eq!(
        x0.try_resize_to_bool().is_none(),
        inlawi!(0u1).zero_resize_assign(y0)
    );
    assert_eq!(
        x0.try_resize_to_u8().is_none(),
        inlawi!(0u8).zero_resize_assign(y0)
    );
    assert_eq!(
        x0.try_resize_to_u16().is_none(),
        inlawi!(0u16).zero_resize_assign(y0)
    );
    assert_eq!(
        x0.try_resize_to_u32().is_none(),
        inlawi!(0u32).zero_resize_assign(y0)
    );
    assert_eq!(
        x0.try_resize_to_u64().is_none(),
        inlawi!(0u64).zero_resize_assign(y0)
    );
    assert_eq!(
        x0.try_resize_to_u128().is_none(),
        inlawi!(0u128).zero_resize_assign(y0)
    );
    y2.bool_assign(y0.to_bool());
    assert_eq_awint_u256(y2, U256::from_bool(y0.to_bool()));
    y2.u8_assign(y0.to_u8());
    assert_eq_awint_u256(y2, U256::from_u8(y0.to_u8()));
    y2.u16_assign(y0.to_u16());
    assert_eq_awint_u256(y2, U256::from_u16(y0.to_u16()));
    y2.u32_assign(y0.to_u32());
    assert_eq_awint_u256(y2, U256::from_u32(y0.to_u32()));
    y2.u64_assign(y0.to_u64());
    assert_eq_awint_u256(y2, U256::from_u64(y0.to_u64()));
    y2.u128_assign(y0.to_u128());
    assert_eq_awint_u256(y2, U256::from_u128(y0.to_u128()));

    assert_eq!(U256::from_u8_array(x0.to_u8_array()), x0);
    assert_eq!(U256::from_u16_array(x0.to_u16_array()), x0);
    assert_eq!(U256::from_u32_array(x0.to_u32_array()), x0);
    assert_eq!(U256::from_u64_array(x0.to_u64_array()), x0);
    assert_eq!(U256::from_u128_array(x0.to_u128_array()), x0);

    assert_eq!(U256::from_u8_array_be(x0.to_u8_array_be()), x0);

    let mut tmp = x0;
    tmp.as_u8_slice_mut().copy_from_slice(&x1.to_u8_array());
    assert_eq!(tmp, x1);

    assert_eq!(
        U256::from_bytes(&x0.to_u8_array()[..(32 - (x0.lz() / 8))]).unwrap(),
        x0
    );

    assert_eq!(
        U256::from_bytes_be(&x0.to_u8_array_be()[(x0.lz() / 8)..]).unwrap(),
        x0
    );

    let mut s = "0x".to_owned();
    s += &ExtAwi::bits_to_string_radix(y0, false, 16, false, 1).unwrap();
    assert_eq!(s, x0.to_hex_string());
    assert_eq!(U256::from_bytes_radix(&s.as_bytes()[2..], 16).unwrap(), x0);
    assert_eq!(U256::from_dec_or_hex_str(&s).unwrap(), x0);

    let s = ExtAwi::bits_to_string_radix(y0, false, 10, false, 1).unwrap();
    assert_eq!(s, x0.to_dec_string());
    assert_eq!(U256::from_dec_or_hex_str(&s).unwrap(), x0);
}

#[test]
fn fuzz_u256() {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let iw = 4usize * 64;
    let mut x0 = U256::zero();
    let mut x1 = U256::zero();
    let mut y0 = ExtAwi::zero(bw(iw));
    let mut y1 = y0.clone();
    let mut y2 = y0.clone();

    // edge case fuzzing
    #[cfg(not(miri))]
    {
        let fl = fuzz_lengths(iw);
        edge_cases_u256!(fl, x0, {
            edge_cases_u256!(fl, x1, {
                u256_to_awint(&mut y0, x0);
                u256_to_awint(&mut y1, x1);
                identities_inner(x0, x1, &y0, &mut y2);
            })
        });
    }

    // random fuzzing
    for _ in 0..N {
        fuzz_step_u256(&mut rng, &mut x0);
        fuzz_step_u256(&mut rng, &mut x1);
        u256_to_awint(&mut y0, x0);
        u256_to_awint(&mut y1, x1);
        identities_inner(x0, x1, &y0, &mut y2);
    }
}