use awint::{bw, Bits, ExtAwi};
use rand::SeedableRng;
// See `testcrate` in https://github.com/AaronKutch/awint to see the strategy
use rand_xoshiro::{rand_core::RngCore, Xoshiro128StarStar};
use u64_array_bigints::Uint;

const N: u32 = if cfg!(miri) {
    32
} else if cfg!(debug_assertions) {
    10_000
} else {
    1_000_000
};

/// Panics if `usize::BITS != 64` or `awint.bw() != Uint::<LEN>::bw()`
fn uint_to_awint<const LEN: usize>(awint: &mut Bits, uint: Uint<LEN>) {
    if usize::BITS != 64 {
        // this could be fixed if the need arises
        panic!("testing only supported on 64 bit architectures");
    }
    if awint.bw() != Uint::<LEN>::bw() {
        panic!("bitwidth mismatch");
    }
    // should optimize ok
    let mut x: [usize; LEN] = [0; LEN];
    for i in 0..LEN {
        x[i] = uint.0[i] as usize;
    }
    awint.as_mut_slice().copy_from_slice(&x);
}

/*
/// Panics if `usize::BITS != 64` or `awint.bw() != Uint::<LEN>::bw()`
fn awint_to_uint<const LEN: usize>(awint: &Bits) -> Uint<LEN> {
    if usize::BITS != 64 {
        // this could be fixed if the need arises
        panic!("testing only supported on 64 bit architectures");
    }
    if awint.bw() != Uint::<LEN>::bw() {
        panic!("bitwidth mismatch");
    }
    let mut x: [usize; LEN] = [0; LEN];
    x.copy_from_slice(&awint.as_slice());
    let mut res = Uint::zero();
    for i in 0..LEN {
        res.0[i] = x[i] as u64;
    }
    res
}
*/

/// Panics if the bitwidths or bitvalues of `awint` do not equal that of `uint`
#[track_caller]
fn assert_eq_awint<const LEN: usize>(awint: &Bits, uint: Uint<LEN>) {
    if usize::BITS != 64 {
        // this could be fixed if the need arises
        panic!("testing only supported on 64 bit architectures");
    }
    if awint.bw() != Uint::<LEN>::bw() {
        panic!("bitwidth mismatch");
    }
    for i in 0..LEN {
        if (awint.as_slice()[i] as u64) != uint.0[i] {
            panic!("awint {:?} is not equal to uint {:?}", awint, uint);
        }
    }
}

/*
// for debugging
fn check_eq_awint<const LEN: usize>(awint: &Bits, uint: Uint<LEN>) -> bool {
    if usize::BITS != 64 {
        // this could be fixed if the need arises
        panic!("testing only supported on 64 bit architectures");
    }
    if awint.bw() != Uint::<LEN>::bw() {
        panic!("bitwidth mismatch");
    }
    for i in 0..LEN {
        if (awint.as_slice()[i] as u64) != uint.0[i] {
            return false
        }
    }
    true
}
*/

fn identities_inner<const LEN: usize>(
    rng: &mut Xoshiro128StarStar,
    x0: Uint<LEN>,
    x1: Uint<LEN>,
    y0: &Bits,
    y1: &Bits,
    y2: &mut Bits,
    y3: &mut Bits,
) {
    let iw = Uint::<LEN>::bw();
    let s0 = (rng.next_u32() as usize) % iw;
    let digit0 = rng.next_u64();
    let digit1 = rng.next_u64();

    assert_eq!(x0.lsb(), y0.lsb());
    assert_eq!(x0.msb(), y0.msb());
    assert_eq!(x0.lz(), y0.lz());
    assert_eq!(x0.tz(), y0.tz());
    assert_eq!(x0.count_ones(), y0.count_ones());

    // TODO fill in remaining

    y2.copy_assign(y0).unwrap();
    y2.xor_assign(y1).unwrap();
    assert_eq_awint(y2, x0 ^ x1);

    y2.copy_assign(y0).unwrap();
    y2.add_assign(y1).unwrap();
    assert_eq_awint(y2, x0.wrapping_add(x1));

    y2.copy_assign(y0).unwrap();
    y2.shl_assign(s0).unwrap();
    assert_eq_awint(y2, x0.checked_shl(s0).unwrap());

    y2.copy_assign(y0).unwrap();
    y2.lshr_assign(s0).unwrap();
    assert_eq_awint(y2, x0.checked_shr(s0).unwrap());

    y2.copy_assign(y0).unwrap();
    y2.rotl_assign(s0).unwrap();
    assert_eq_awint(y2, x0.checked_rotl(s0).unwrap());

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

    y2.copy_assign(y0).unwrap();
    y2.mul_assign(y1, y3).unwrap();
    assert_eq_awint(y2, x0.wrapping_mul(x1));

    if digit0 != 0 {
        y2.copy_assign(y0).unwrap();
        let rem0 = y2.short_udivide_inplace_assign(digit0 as usize).unwrap();
        let (res, rem1) = x0.checked_short_divide(digit0).unwrap();
        assert_eq!(rem0 as u64, rem1);
        assert_eq_awint(y2, res);
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

fn fuzz_step<const LEN: usize>(rng: &mut Xoshiro128StarStar, x: &mut Uint<LEN>) {
    let r0 = (rng.next_u32() as usize) % Uint::<LEN>::bw();
    let r1 = (rng.next_u32() as usize) % Uint::<LEN>::bw();
    let tmp = Uint::max_value()
        .checked_shl(r0)
        .unwrap()
        .checked_rotl(r1)
        .unwrap();
    match rng.next_u32() % 4 {
        0 => *x |= tmp,
        1 => *x &= tmp,
        _ => *x ^= tmp,
    }
}

fn fuzz_lengths(bw: usize) -> Vec<usize> {
    if bw < 4 {
        return (0..bw).collect()
    }
    let mut v = vec![0, 1];
    let mut x = 8;
    while x < (bw / 2) {
        v.push(x - 1);
        v.push(x);
        x *= 2;
    }
    while x < (bw - 2) {
        v.push(x - 1);
        v.push(x);
        x = x + (x / 2);
    }
    // crucial for `imin` cases
    v.push(bw - 2);
    v.push(bw - 1);
    v
}

macro_rules! edge_cases {
    ($fuzz_lengths:ident, $x:ident, $inner:block) => {
        for i0 in 0..$fuzz_lengths.len() {
            $x = Uint::max_value().checked_shr($fuzz_lengths[i0]).unwrap();
            for i1 in i0..$fuzz_lengths.len() {
                $x &= Uint::<LEN>::max_value()
                    .checked_shl($fuzz_lengths[i1 - i0])
                    .unwrap();
                $inner
            }
        }
    };
}

fn fuzz<const LEN: usize>(iters: u32, seed: u64) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(seed);
    let iw = LEN * 64;
    let mut x0 = Uint::zero();
    let mut x1 = Uint::zero();
    let mut y0 = ExtAwi::zero(bw(iw));
    let mut y1 = y0.clone();
    let mut y2 = y0.clone();
    let mut y3 = y0.clone();

    // edge case fuzzing
    let fl = fuzz_lengths(iw);
    edge_cases!(fl, x0, {
        edge_cases!(fl, x1, {
            uint_to_awint(&mut y0, x0);
            uint_to_awint(&mut y1, x1);
            identities_inner(&mut rng, x0, x1, &y0, &y1, &mut y2, &mut y3);
        })
    });

    // random fuzzing
    for _ in 0..iters {
        fuzz_step(&mut rng, &mut x0);
        fuzz_step(&mut rng, &mut x1);
        uint_to_awint(&mut y0, x0);
        uint_to_awint(&mut y1, x1);
        identities_inner(&mut rng, x0, x1, &y0, &y1, &mut y2, &mut y3);
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
