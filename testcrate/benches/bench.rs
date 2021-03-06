#![feature(test)]

extern crate test;
use rand_xoshiro::{
    rand_core::{RngCore, SeedableRng},
    Xoshiro128StarStar,
};
use test::{black_box, Bencher};
use u64_array_bigints::U256;

#[bench]
fn format_std(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    bencher.iter(|| {
        // this might not be representative because of the number of string ops
        // happening in `format`
        black_box(format!(
            "{:x?}",
            black_box(U256::rand_using(black_box(&mut rng)))
        ))
    })
}

#[bench]
fn format_itoa(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let x = [
        rng.next_u64(),
        rng.next_u64(),
        rng.next_u64(),
        rng.next_u64(),
    ];
    bencher.iter(|| {
        let mut buf = itoa::Buffer::new();
        let mut sum = 0;
        for i in 0..4 {
            sum += black_box(buf.format(black_box(x)[i])).len();
        }
        sum
    })
}

#[bench]
fn format_fast(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let x = U256::rand_using(&mut rng);
    bencher.iter(|| {
        let mut buf = [0u64; 8];
        black_box(black_box(x).to_hex_string_buffer(&mut buf));
        buf
    })
}

#[bench]
fn parse_hex_fast(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let s = U256::rand_using(&mut rng).to_hex_string();
    bencher.iter(|| U256::from_hex_str_fast(black_box(&s.as_bytes()[2..])))
}

#[bench]
fn parse_dec(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let s = U256::rand_using(black_box(&mut rng)).to_dec_string();
    bencher.iter(|| U256::from_dec_or_hex_str(black_box(&s)))
}

#[bench]
fn parse_u64_hex_std(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    let s = U256::rand_using(black_box(&mut rng))
        .wrapping_shr(192)
        .to_hex_string();
    bencher.iter(|| u64::from_str_radix(black_box(&s[2..]), 16).unwrap())
}
