use alloc::{
    borrow::ToOwned,
    string::{String, ToString},
    vec::Vec,
};
use core::{
    fmt::{self, Display},
    str::FromStr,
};

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
    pub fn from_bytes_radix(src: &[u8], radix: u8) -> Result<Self, FromStrRadixErr> {
        if let Err(e) = verify_for_bytes_assign(src, radix) {
            return Err(e)
        }
        // the accumulator
        let mut pad0 = Self::zero();
        // contains the radix exponential
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

    pub fn from_str_radix(src: &str, radix: u8) -> Result<Self, FromStrRadixErr> {
        Self::from_bytes_radix(src.as_bytes(), radix)
    }

    /// Uses radix 16 if `src` has a leading `0x`, otherwise uses radix 10
    pub fn from_dec_or_hex_str(src: &str) -> Result<Self, FromStrRadixErr> {
        let src = src.as_bytes();
        if src.len() < 2 {
            Self::from_bytes_radix(src, 10)
        } else if (src[0] == b'0') && (src[1] == b'1') {
            Self::from_bytes_radix(&src[2..], 16)
        } else {
            Self::from_bytes_radix(src, 10)
        }
    }

    pub fn to_hex_string(self) -> String {
        if self.is_zero() {
            return "0x0".to_owned()
        }
        let swar = |x: u64| -> u64 {
            // Using SWAR techniques to process one u32 at a time.
            // First, scatter and reverse `x` evenly nto groups of 4 bits.
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

        // need room for 256/4 bytes
        let mut s_chunks = [0u64; 8];
        let mut char_len = 0;
        for j in (0..4).rev() {
            // find first nonzero leading digit
            let y = self.0 .0[j];
            if y != 0 {
                let sig_bits = BITS
                    .wrapping_sub(y.leading_zeros() as usize)
                    .wrapping_add(BITS.wrapping_mul(j));
                // the nibble with the msb and all less significant nibbles count
                char_len = (sig_bits >> 2).wrapping_add(((sig_bits & 0b11) != 0) as usize);
                for i in 0..=j {
                    let x = self.0 .0[i];
                    let lo = x as u32 as u64;
                    let hi = (x >> 32) as u32 as u64;
                    // reverse at the chunk level
                    s_chunks[s_chunks.len() - 1 - (i << 1)] = swar(lo);
                    s_chunks[s_chunks.len() - 2 - (i << 1)] = swar(hi);
                }
                break
            }
        }
        let s_bytes_le: [u8; 8 * 8] = bytemuck::try_cast(s_chunks).unwrap();
        // the +2 is for the extra leading "0x"
        let mut s: Vec<u8> = alloc::vec![0; char_len + 2];
        s[0] = b'0';
        s[1] = b'x';
        s[2..].copy_from_slice(&s_bytes_le[(s_bytes_le.len() - char_len)..]);
        #[cfg(all(debug_assertions, not(miri)))]
        {
            String::from_utf8(s).unwrap()
        }
        #[cfg(any(not(debug_assertions), miri))]
        {
            // Safety: the algorithm above can only output b'0'-b'9', b'a'-b'f', and b'x',
            // and we have tested all nibble combinations
            unsafe { String::from_utf8_unchecked(s) }
        }
    }
}

impl FromStr for U256 {
    type Err = FromStrRadixErr;

    /// Uses `from_dec_or_hex_str`
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_dec_or_hex_str(s)
    }
}

impl ToString for U256 {
    /// Uses `to_hex_string`
    fn to_string(&self) -> String {
        self.to_hex_string()
    }
}

#[cfg(feature = "serde_support")]
impl Serialize for U256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

#[cfg(feature = "serde_support")]
impl<'de> Deserialize<'de> for U256 {
    fn deserialize<D>(deserializer: D) -> Result<U256, D::Error>
    where
        D: Deserializer<'de>,
    {
        // Create U256 given the sliced data, and radix
        U256::from_dec_or_hex_str(&String::deserialize(deserializer)?)
            .map_err(serde::de::Error::custom)
    }
}
