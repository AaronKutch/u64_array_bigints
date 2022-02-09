# u64_array_bigints

This crate currently just supplies a special purpose integer `U256` type.

It is planned for this crate to be coded without the `uint` dependency and to have more general
bigints based on `u64` arrays.

## feature flags

The `serde_support` feature flag is turned on by default.
The crate is `no_std` by default.

The `use_parity_uint` feature flag is turned on by default, turning it off uses new implementations.
