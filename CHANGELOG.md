# Changelog

## [0.3.2] - TODO
### Fixes
- Fixed that `msb` and functions depending on it were broken on non-64-bit architectures

### Changes
- The `Deserialize` impl of `U256` now also tries to parse the input as a `u64`, allowing more cases
  of `serde_json` deserialization to work
- Changed the `Debug` and `Display` impls for `U256` to display a decimal string

### Crate
- Version bump of bytemuck to 1.10

## [0.3.1] - 2022-03-02
### Fixes
- Fixed that string deserialization would not catch some overflow cases
- Fixed incorrect documentation

## [0.3.0] - 2022-03-01
### Fixes
- Fixed deserialization bug where chars that shouldn't be accepted were sometimes accepted when the
  radix was above 10

### Changes
- Deserialization uses `from_dec_or_hex_str_restricted`

### Additions
- added `from_dec_or_hex_str_restricted`

## [0.2.1] - 2022-02-28
### Fixes
- Fixed formatting impls to use `pad_integral`. The non-alternate form of `LowerHex` (the one
  involving the "{:x}" format string) now does not include the leading "0x". Only the alternate
  "{:#x}" format should include the leading "0x".

## [0.2.0] - 2022-02-25
### Fixes
- Casting is now correct on big endian systems

### Changes
- `U256` now uses an in-crate implementation by default

### Additions
- The `u256` macro for quick construction of decimal or hexadecimal `U256` values. Two crates were
  added so that the macro could be reexported by `u64_array_bigints`, so that everything can be
  accessed from one crate.
