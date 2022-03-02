# u64_array_bigints

This crate supplies a fixed width `Uint` type and a `U256` type.

This crate is basically a specialized version of [awint](https://crates.io/crates/awint) made for
https://github.com/onomyprotocol/cosmos-gravity-bridge.

## feature flags

The `rand_support` and `serde_support` feature flags are turned on by default.
The crate is `no_std` by default.

If the `use_parity_uint` feature flag is on, the `uint` crate is used for most function
implementations of `U256`.
