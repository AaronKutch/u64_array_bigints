# u64_array_bigints

This crate supplies a fixed width `Uint` type and a `U256` type.

## feature flags

The `rand_support` and `serde_support` feature flags are turned on by default.
The crate is `no_std` by default.

If the `use_parity_uint` feature flag is on, the `uint` crate is used for most function
implementations of `U256`.
