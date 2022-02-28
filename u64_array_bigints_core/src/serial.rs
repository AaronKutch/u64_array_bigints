#![allow(clippy::manual_range_contains)]

use alloc::{borrow::ToOwned, string::String, vec, vec::Vec};
use core::fmt::{self, Display};

#[cfg(feature = "serde_support")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

use crate::{const_for, utils::BITS, U256};

#[derive(Debug, Clone)]
pub enum FromStrRadixErr {
    InvalidRadix,
    InvalidChar,
    Overflow,
}

impl Display for FromStrRadixErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

use FromStrRadixErr::*;

// more adaptations from `awint`

/// Runs all pre serialization checks except for `Overflow` checks
const fn verify_for_bytes_assign(src: &[u8], radix: u8) -> Result<(), FromStrRadixErr> {
    if radix < 2 || radix > 36 {
        return Err(InvalidRadix)
    }
    const_for!(i in {0..src.len()} {
        let b = src[i];
        if b == b'_' {
            continue;
        }
        let in_decimal_range = b'0' <= b && b < b'0'.wrapping_add(radix);
        let in_lower_range = (radix > 10)
            && (b'a' <= b)
            && (b < b'a'.wrapping_add(radix).wrapping_sub(10));
        let in_upper_range = (radix > 10)
            && (b'A' <= b)
            && (b < b'A'.wrapping_add(radix).wrapping_sub(10));
        if radix <= 10 {
            if !in_decimal_range {
                return Err(InvalidChar)
            }
        } else if !(in_decimal_range || in_lower_range || in_upper_range) {
            return Err(InvalidChar)
        }
    });
    Ok(())
}

impl U256 {
    pub const fn from_bytes_radix(src: &[u8], radix: u8) -> Result<Self, FromStrRadixErr> {
        if let Err(e) = verify_for_bytes_assign(src, radix) {
            return Err(e)
        }
        // the accumulator
        let mut pad0 = Self::zero();
        // contains the radix exponential
        #[cfg(feature = "use_parity_uint")]
        let mut pad1 = Self([1, 0, 0, 0]);
        #[cfg(not(feature = "use_parity_uint"))]
        let mut pad1 = Self::one();
        const_for!(i in {0..src.len()}.rev() {
            let b = src[i];
            if b == b'_' {
                continue;
            }
            let char_digit = if radix <= 10 || b <= b'9' {
                b.wrapping_sub(b'0')
            } else if b <= b'Z' {
                b.wrapping_sub(b'A').wrapping_add(10)
            } else {
                b.wrapping_sub(b'a').wrapping_add(10)
            } as u64;
            // pad0 += pad1 * char_digit
            let tmp = pad0.overflowing_short_mul_add(pad1, char_digit);
            pad0 = tmp.0;
            let o0 = tmp.1;
            if o0 {
                return Err(Overflow)
            }
            let tmp = pad1.overflowing_short_cin_mul(0, radix as u64);
            pad1 = tmp.0;
            let o1 = tmp.1;
            if o1 != 0 {
                const_for!(i in {0..i} {
                    match src[i] {
                        b'_' | b'0' => (),
                        _ => return Err(Overflow)
                    }
                });
                break
            }
        });
        Ok(pad0)
    }

    #[cfg(not(feature = "use_parity_uint"))]
    pub const fn from_str_radix(src: &str, radix: u8) -> Result<Self, FromStrRadixErr> {
        Self::from_bytes_radix(src.as_bytes(), radix)
    }

    /// Uses radix 16 if `src` has a leading `0x`, otherwise uses radix 10
    ///
    /// The `uint` implementation of `FromStr` is unsuitable because it is
    /// hexadecimal only (intentional by their developers because they did not
    /// make the mistake of using decimal in message passing implementations and
    /// do not have wasteful "0x" prefixes), this function will switch between
    /// hexadecimal and decimal depending on if there is a "0x" prefix.
    pub fn from_dec_or_hex_str(src: &str) -> Result<Self, FromStrRadixErr> {
        let src = src.as_bytes();
        if src.len() <= 2 {
            Self::from_bytes_radix(src, 10)
        } else if (src[0] == b'0') && (src[1] == b'x') {
            Self::from_bytes_radix(&src[2..], 16)
        } else {
            Self::from_bytes_radix(src, 10)
        }
    }

    /// This function is intended for formatting intermediates that use stack
    /// buffers.
    ///
    /// Assigns a hex representation of `self` to `buf[index..]` (cast as a byte
    /// array with `bytemuck`) and returns the `index`. No prefix or minimum
    /// "0" are set (returns 64 if `self.is_zero()`). Also, bytes in
    /// `buf[..index]` may be set arbitrarily. Only
    /// b'0'-b'9' and b'a'-b'f' can be output to `buf[index..]`.
    pub fn to_hex_string_buffer(self, buf: &mut [u64; 8]) -> usize {
        if self.is_zero() {
            return 64
        }
        let swar = |x: u64| -> u64 {
            // Using SWAR techniques to process one u32 at a time.
            // First, scatter and reverse `x` evenly into groups of 4 bits.
            // 0x0000_0000_abcd_efgh
            // 0xefgh_0000_abcd_0000
            // 0x00gh_00ef_00cd_00ab
            // 0x0h0g_0f0e_0d0c_0b0a
            let mut x0: u64 = x & 0xffff;
            let mut x1: u64 = x & 0xffff_0000;
            let mut x: u64 = (x0 << 48) | x1;
            x0 = x & 0x00ff_0000_00ff_0000;
            x1 = x & 0xff00_0000_ff00_0000;
            x = x0 | (x1 >> 24);
            x0 = x & 0x000f_000f_000f_000f;
            x1 = x & 0x00f0_00f0_00f0_00f0;
            x = (x0 << 8) | (x1 >> 4);

            // because ASCII does not have letters immediately following numbers, we need to
            // differentiate between them to be able to add different offsets.

            // the two's complement of `10u4 == 0b1010u4` is `0b0110u4 == 0x6u4`.
            // get the carries, if there is a carry the 4 bits were above '9'
            let c = (x.wrapping_add(0x0606_0606_0606_0606) & 0x1010_1010_1010_1010) >> 4;

            // conditionally offset to b'a' or b'0'
            let offsets = c.wrapping_mul(0x57) | (c ^ 0x0101_0101_0101_0101).wrapping_mul(0x30);

            x.wrapping_add(offsets)
        };

        let mut char_len = 0;
        for j in (0..4).rev() {
            // find first nonzero leading digit
            #[cfg(feature = "use_parity_uint")]
            let y = self.0[j];
            #[cfg(not(feature = "use_parity_uint"))]
            let y = self.0 .0[j];
            if y != 0 {
                let sig_bits = BITS
                    .wrapping_sub(y.leading_zeros() as usize)
                    .wrapping_add(BITS.wrapping_mul(j));
                // the nibble with the msb and all less significant nibbles count
                char_len = (sig_bits >> 2).wrapping_add(((sig_bits & 0b11) != 0) as usize);
                for i in 0..=j {
                    #[cfg(feature = "use_parity_uint")]
                    let x = self.0[i];
                    #[cfg(not(feature = "use_parity_uint"))]
                    let x = self.0 .0[i];
                    let lo = x as u32 as u64;
                    let hi = (x >> 32) as u32 as u64;
                    // reverse at the chunk level. The `from_le` fixes big endian architectures.
                    buf[buf.len() - 1 - (i << 1)] = u64::from_le(swar(lo));
                    buf[buf.len() - 2 - (i << 1)] = u64::from_le(swar(hi));
                }
                break
            }
        }
        64 - char_len
    }

    /// Returns a hexadecimal string representation of `self`, including a "0x"
    /// prefix. If `self.is_zero()`, this returns "0x0"
    pub fn to_hex_string(self) -> String {
        let mut buf = [0u64; 8];
        let index = self.to_hex_string_buffer(&mut buf);
        if index == 64 {
            return "0x0".to_owned()
        }
        let byte_buf: [u8; 64] = bytemuck::try_cast(buf).unwrap();
        // the +2 makes room for the prefix
        let char_len = (64 - index) + 2;
        let mut s: Vec<u8> = alloc::vec![0; char_len];
        s[0] = b'0';
        s[1] = b'x';
        s[2..].copy_from_slice(&byte_buf[index..]);
        #[cfg(all(debug_assertions, not(miri)))]
        {
            String::from_utf8(s).unwrap()
        }
        #[cfg(any(not(debug_assertions), miri))]
        {
            // Safety: `to_hex_string_buffer` only set `buf[index..]` to b'0'-b'9' and
            // b'a'-b'f', and the prefix adds b'x'.
            unsafe { String::from_utf8_unchecked(s) }
        }
    }

    /// Prefixes not included. Note: if `self.is_zero`, the `Vec` is empty.
    ///
    /// Returns `None` if the `radix` is not valid
    pub fn to_bytes_radix(self, radix: u8, upper: bool) -> Option<Vec<u8>> {
        if radix < 2 || radix > 36 {
            return None
        }
        let mut pad = self;
        let mut dst = vec![];
        loop {
            if pad.is_zero() {
                dst[..].reverse();
                return Some(dst)
            }
            // cannot result in panic or infinite loop because of bounds on `radix`
            let tmp = pad.checked_short_divide(radix as u64).unwrap();
            pad = tmp.0;
            let rem = tmp.1 as u8;
            if rem < 10 {
                dst.push(b'0'.wrapping_add(rem));
            } else if upper {
                dst.push(b'A'.wrapping_add(rem).wrapping_sub(10));
            } else {
                dst.push(b'a'.wrapping_add(rem).wrapping_sub(10));
            }
        }
    }

    pub fn to_dec_string(self) -> String {
        if self.is_zero() {
            return "0".to_owned()
        }
        // Safety: `to_bytes_radix(10, false)` can only output b'0'-b'9'
        unsafe { String::from_utf8_unchecked(self.to_bytes_radix(10, false).unwrap()) }
    }

    /// Returns `10^exp`, or `None` if overflow occurs
    pub const fn checked_exp10(exp: usize) -> Option<Self> {
        #[cfg(feature = "use_parity_uint")]
        let mut res = Self([1, 0, 0, 0]);
        #[cfg(not(feature = "use_parity_uint"))]
        let mut res = Self::one();
        const_for!(i in {0..exp} {
            let tmp = res.overflowing_short_cin_mul(0, 10);
            if tmp.1 != 0 {
                return None
            }
            res = tmp.0;
        });
        Some(res)
    }
}

/*impl FromStr for U256 {
    type Err = FromStrRadixErr;

    /// Uses `from_dec_or_hex_str`
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_dec_or_hex_str(s)
    }
}*/

/*impl ToString for U256 {
    /// Uses `to_hex_string`
    fn to_string(&self) -> String {
        self.to_hex_string()
    }
}*/

#[cfg(not(feature = "use_parity_uint"))]
impl fmt::LowerHex for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buf = [0u64; 8];
        let index = self.to_hex_string_buffer(&mut buf);
        let byte_buf: [u8; 64] = bytemuck::try_cast(buf).unwrap();
        if index == 64 {
            return f.pad_integral(true, "0x", "0")
        }
        #[cfg(all(debug_assertions, not(miri)))]
        {
            f.pad_integral(
                true,
                "0x",
                core::str::from_utf8(&byte_buf[index..]).unwrap(),
            )
        }
        #[cfg(any(not(debug_assertions), miri))]
        {
            // Safety: `to_hex_string_buffer` only set `byte_buf[index..]` to b'0'-b'9' and
            // b'a'-b'f'
            unsafe {
                f.pad_integral(
                    true,
                    "0x",
                    core::str::from_utf8_unchecked(&byte_buf[index..]),
                )
            }
        }
    }
}

#[cfg(not(feature = "use_parity_uint"))]
impl fmt::Display for U256 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad_integral(true, "", &self.to_dec_string())
    }
}

#[cfg(feature = "serde_support")]
impl Serialize for U256 {
    /// Includes a "0x" prefix.
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_hex_string())
    }
}

#[cfg(feature = "serde_support")]
impl<'de> Deserialize<'de> for U256 {
    /// Uses `from_dec_or_hex_str`.
    fn deserialize<D>(deserializer: D) -> Result<U256, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Create U256 given the sliced data, and radix
        U256::from_dec_or_hex_str(&String::deserialize(deserializer)?)
            .map_err(serde::de::Error::custom)
    }
}
