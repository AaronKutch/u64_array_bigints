#![feature(test)]

extern crate test;
use rand::prelude::*;
use test::{black_box, Bencher};
use u64_array_bigints::{Uint, U256};

fn rand_u256() -> U256 {
    U256(Uint([random(), random(), random(), random()]))
}

#[bench]
fn format_std(bencher: &mut Bencher) {
    bencher.iter(|| {
        // this might not be representative because of the number of string ops
        // happening in `format`
        black_box(format!("{:x?}", black_box(rand_u256())))
    })
}

#[bench]
fn format_fast(bencher: &mut Bencher) {
    bencher.iter(|| black_box(black_box(rand_u256()).to_hex_string()))
}
