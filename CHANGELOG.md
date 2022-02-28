# Changelog

## [0.2.1] - 2022-2-28
### Fixes
- Fixed formatting impls to use `pad_integral`. The non-alternate form of `LowerHex` (the one
  involving the "{:x}" format string) now does not include the leading "0x". Only the alternate
  "{:#x}" format should include the leading "0x".

## [0.2.0] - 2022-2-25
### Fixes
- Casting is now correct on big endian systems

### Changes
- `U256` now uses an in-crate implementation by default

### Additions
- The `u256` macro for quick construction of decimal or hexadecimal `U256` values. Two crates were
  added so that the macro could be reexported by `u64_array_bigints`, so that everything can be
  accessed from one crate.
