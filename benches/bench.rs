#![feature(test)]

extern crate test;
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
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
fn format_fast(bencher: &mut Bencher) {
    let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    bencher.iter(|| black_box(U256::rand_using(black_box(&mut rng))).to_hex_string())
}
