#![allow(clippy::needless_range_loop)]

use awint::Bits;
use rand_xoshiro::{rand_core::RngCore, Xoshiro128StarStar};
use u64_array_bigints::{Uint, U256};

pub const N: u32 = if cfg!(miri) {
    32
} else if cfg!(debug_assertions) {
    10_000
} else {
    1_000_000
};

/// Panics if `usize::BITS != 64` or `awint.bw() != Uint::<LEN>::bw()`
pub fn uint_to_awint<const LEN: usize>(awint: &mut Bits, uint: Uint<LEN>) {
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

/// Panics if `usize::BITS != 64` or `awint.bw() != Uint::<LEN>::bw()`
pub fn u256_to_awint(awint: &mut Bits, uint: U256) {
    if usize::BITS != 64 {
        // this could be fixed if the need arises
        panic!("testing only supported on 64 bit architectures");
    }
    if awint.bw() != 256 {
        panic!("bitwidth mismatch");
    }
    // should optimize ok
    let mut x: [usize; 4] = [0; 4];
    for i in 0..4 {
        x[i] = uint.to_u64_array()[i] as usize;
    }
    awint.as_mut_slice().copy_from_slice(&x);
}

/*
/// Panics if `usize::BITS != 64` or `awint.bw() != Uint::<LEN>::bw()`
pub fn awint_to_uint<const LEN: usize>(awint: &Bits) -> Uint<LEN> {
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
pub fn assert_eq_awint<const LEN: usize>(awint: &Bits, uint: Uint<LEN>) {
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

/// Panics if the bitwidths or bitvalues of `awint` do not equal that of `uint`
#[track_caller]
pub fn assert_eq_awint_u256(awint: &Bits, uint: U256) {
    if usize::BITS != 64 {
        // this could be fixed if the need arises
        panic!("testing only supported on 64 bit architectures");
    }
    if awint.bw() != 256 {
        panic!("bitwidth mismatch");
    }
    for i in 0..4 {
        if (awint.as_slice()[i] as u64) != uint.to_u64_array()[i] {
            panic!("awint {:?} is not equal to uint {:?}", awint, uint);
        }
    }
}

/*
// for debugging
pub fn check_eq_awint<const LEN: usize>(awint: &Bits, uint: Uint<LEN>) -> bool {
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

pub fn fuzz_step<const LEN: usize>(rng: &mut Xoshiro128StarStar, x: &mut Uint<LEN>) {
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

pub fn fuzz_step_u256(rng: &mut Xoshiro128StarStar, x: &mut U256) {
    let r0 = (rng.next_u32() as usize) % 256;
    let r1 = (rng.next_u32() as usize) % 256;
    let tmp = U256::max_value()
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

pub fn fuzz_lengths(bw: usize) -> Vec<usize> {
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

#[macro_export]
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

#[macro_export]
macro_rules! edge_cases_u256 {
    ($fuzz_lengths:ident, $x:ident, $inner:block) => {
        for i0 in 0..$fuzz_lengths.len() {
            $x = U256::max_value().checked_shr($fuzz_lengths[i0]).unwrap();
            for i1 in i0..$fuzz_lengths.len() {
                $x &= U256::max_value()
                    .checked_shl($fuzz_lengths[i1 - i0])
                    .unwrap();
                $inner
            }
        }
    };
}
