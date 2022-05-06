use std::{assert, num::NonZeroUsize};

use awint::{bw, Bits, ExtAwi};
use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use testcrate::*;
use u64_array_bigints::Uint;

// See `testcrate` in https://github.com/AaronKutch/awint to see the strategy used here

fn one_run<const LEN: usize>() {
    let iw = NonZeroUsize::new(Uint::<LEN>::bw()).unwrap();
    assert_eq_awint(&ExtAwi::zero(iw), Uint::<LEN>::zero());
    assert_eq_awint(&ExtAwi::umax(iw), Uint::<LEN>::max_value());
    assert_eq_awint(&ExtAwi::uone(iw), Uint::<LEN>::one());
}

#[allow(clippy::too_many_arguments)]
fn identities_inner<const LEN: usize>(
    rng: &mut Xoshiro128StarStar,
    x0: Uint<LEN>,
    x1: Uint<LEN>,
    y0: &Bits,
    y1: &Bits,
    y2: &mut Bits,
    y3: &mut Bits,
    dw: &mut Bits,
) {
    let iw = Uint::<LEN>::bw();
    let s0 = (rng.next_u32() as usize) % iw;
    let digit0 = rng.next_u64();
    let digit1 = rng.next_u64();

    assert_eq!(x0.is_zero(), y0.is_zero());
    assert_eq!(x0.lsb(), y0.lsb());
    assert_eq!(x0.msb(), y0.msb());
    assert_eq!(x0.lz(), y0.lz());
    assert_eq!(x0.tz(), y0.tz());
    assert_eq!(x0.count_ones(), y0.count_ones());

    assert_eq!(x0.const_eq(&x1), y0.const_eq(y1).unwrap());
    assert_eq!(x0.const_lt(&x1), y0.ult(y1).unwrap());
    assert_eq!(x0.const_le(&x1), y0.ule(y1).unwrap());
    assert_eq!(x0.const_gt(&x1), y0.ugt(y1).unwrap());
    assert_eq!(x0.const_ge(&x1), y0.uge(y1).unwrap());

    y2.copy_assign(y0).unwrap();
    y2.not_assign();
    assert_eq_awint(y2, x0.const_not());

    y2.copy_assign(y0).unwrap();
    y2.or_assign(y1).unwrap();
    assert_eq_awint(y2, x0.const_or(x1));

    y2.copy_assign(y0).unwrap();
    y2.and_assign(y1).unwrap();
    assert_eq_awint(y2, x0.const_and(x1));

    y2.copy_assign(y0).unwrap();
    y2.xor_assign(y1).unwrap();
    assert_eq_awint(y2, x0.const_xor(x1));

    y2.copy_assign(y0).unwrap();
    y2.add_assign(y1).unwrap();
    assert_eq_awint(y2, x0.wrapping_add(x1));

    let o = y2.cin_sum_assign(false, y0, y1).unwrap();
    if let Some(tmp) = x0.checked_add(x1) {
        assert!(!o.0);
        assert_eq_awint(y2, tmp);
    } else {
        assert!(o.0);
    }

    y3.copy_assign(y1).unwrap();
    y3.neg_assign(true);
    y2.cin_sum_assign(false, y0, y3).unwrap();
    if let Some(tmp) = x0.checked_sub(x1) {
        assert!(y0.uge(y1).unwrap());
        assert_eq_awint(y2, tmp);
    } else {
        assert!(y0.ult(y1).unwrap());
    }

    y2.copy_assign(y0).unwrap();
    y2.shl_assign(s0).unwrap();
    assert_eq_awint(y2, x0.checked_shl(s0).unwrap());

    y2.copy_assign(y0).unwrap();
    y2.lshr_assign(s0).unwrap();
    assert_eq_awint(y2, x0.checked_shr(s0).unwrap());

    y2.copy_assign(y0).unwrap();
    y2.rotl_assign(s0).unwrap();
    assert_eq_awint(y2, x0.checked_rotl(s0).unwrap());

    #[cfg(target_pointer_width = "64")]
    {
        y2.copy_assign(y0).unwrap();
        let cout0 = y2.short_cin_mul(digit0 as usize, digit1 as usize);
        let (res, cout1) = x0.overflowing_short_cin_mul(digit0, digit1);
        assert_eq!(cout0 as u64, cout1);
        assert_eq_awint(y2, res);

        y2.copy_assign(y0).unwrap();
        let o0 = y2.short_mul_add_assign(y1, digit0 as usize).unwrap();
        let (res, o1) = x0.overflowing_short_mul_add(x1, digit0);
        assert_eq!(o0, o1);
        assert_eq_awint(y2, res);

        if digit0 != 0 {
            y2.copy_assign(y0).unwrap();
            let rem0 = y2.short_udivide_inplace_assign(digit0 as usize).unwrap();
            let (res, rem1) = x0.checked_short_divide(digit0).unwrap();
            assert_eq!(rem0 as u64, rem1);
            assert_eq_awint(y2, res);
        }
    }
    // `awint`'s `short_` stuff was made for usize::BITS adjusting algorithms or
    // for stuff that fits in a `u16`
    #[cfg(not(target_pointer_width = "64"))]
    {
        y2.copy_assign(y0).unwrap();
        let cout0 = y2.short_cin_mul(digit0 as u8 as usize, digit1 as u8 as usize);
        let (res, cout1) = x0.overflowing_short_cin_mul(digit0 as u8 as u64, digit1 as u8 as u64);
        assert_eq!(cout0 as u8, cout1 as u8);
        assert_eq_awint(y2, res);

        y2.copy_assign(y0).unwrap();
        let o0 = y2.short_mul_add_assign(y1, digit0 as u8 as usize).unwrap();
        let (res, o1) = x0.overflowing_short_mul_add(x1, digit0 as u8 as u64);
        assert_eq!(o0, o1);
        assert_eq_awint(y2, res);

        if (digit0 as u8) != 0 {
            y2.copy_assign(y0).unwrap();
            let rem0 = y2
                .short_udivide_inplace_assign(digit0 as u8 as usize)
                .unwrap();
            let (res, rem1) = x0.checked_short_divide(digit0 as u8 as u64).unwrap();
            assert_eq!(rem0 as u8, rem1 as u8);
            assert_eq_awint(y2, res);
        }
    }

    y2.copy_assign(y0).unwrap();
    y2.mul_assign(y1, y3).unwrap();
    assert_eq_awint(y2, x0.wrapping_mul(x1));

    dw.zero_assign();
    dw.arb_umul_add_assign(y0, y1);
    let o = y2.zero_resize_assign(dw);
    if let Some(tmp) = x0.checked_mul(x1) {
        assert_eq_awint(y2, tmp);
        assert!(!o);
    } else {
        assert!(o);
    }

    if x1.is_zero() {
        assert!(Bits::udivide(y2, y3, y0, y1).is_none());
        assert!(x0.divide(x1).is_none());
    } else {
        Bits::udivide(y2, y3, y0, y1).unwrap();
        let (quo, rem) = x0.divide(x1).unwrap();
        assert_eq_awint(y2, quo);
        assert_eq_awint(y3, rem);
    }
}

fn fuzz<const LEN: usize>(iters: u32, seed: u64) {
    one_run::<LEN>();
    let mut rng = Xoshiro128StarStar::seed_from_u64(seed);
    let iw = LEN * 64;
    let mut x0 = Uint::<LEN>::zero();
    let mut x1 = Uint::<LEN>::zero();
    let mut y0 = ExtAwi::zero(bw(iw));
    let mut y1 = y0.clone();
    let mut y2 = y0.clone();
    let mut y3 = y0.clone();
    let mut dw = ExtAwi::zero(bw(iw.checked_mul(2).unwrap()));

    // edge case fuzzing
    #[cfg(not(miri))]
    {
        let fl = fuzz_lengths(iw);
        edge_cases!(fl, x0, {
            edge_cases!(fl, x1, {
                uint_to_awint(&mut y0, x0);
                uint_to_awint(&mut y1, x1);
                identities_inner(&mut rng, x0, x1, &y0, &y1, &mut y2, &mut y3, &mut dw);
            })
        });
    }

    // random fuzzing
    for _ in 0..iters {
        fuzz_step(&mut rng, &mut x0);
        fuzz_step(&mut rng, &mut x1);
        uint_to_awint(&mut y0, x0);
        uint_to_awint(&mut y1, x1);
        identities_inner(&mut rng, x0, x1, &y0, &y1, &mut y2, &mut y3, &mut dw);
    }
}

#[test]
fn fuzz_1() {
    fuzz::<1>(N, 0);
}

#[test]
fn fuzz_2() {
    fuzz::<2>(N, 0);
}

#[test]
fn fuzz_3() {
    fuzz::<3>(N, 0);
}

#[test]
fn fuzz_4() {
    fuzz::<4>(N, 0);
}

#[test]
fn fuzz_8() {
    fuzz::<8>(N, 0);
}

#[test]
#[cfg(not(miri))]
fn fuzz_33() {
    fuzz::<33>(N, 0);
}
