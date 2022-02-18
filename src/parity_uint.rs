#[allow(clippy::all)]
mod clippy_guard {
    uint::construct_uint! {
        pub struct U256(4);
    }
}
use alloc::{borrow::ToOwned, string::String, vec::Vec};

pub use clippy_guard::U256;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
pub use uint::FromStrRadixErr;

// the unwraps here will not panic if $n is correct
macro_rules! to_from_array {
    ($($to_fn:ident $from_fn:ident $uX:ident $n:expr);*;) => {
        $(
            pub fn $to_fn(self) -> [$uX; $n] {
                bytemuck::try_cast(self.0).unwrap()
            }

            pub fn $from_fn(x: [$uX; $n]) -> Self {
                Self(bytemuck::try_cast(x).unwrap())
            }
        )*
    };
}

impl U256 {
    to_from_array!(
        to_u8_array from_u8_array u8 32;
        to_u16_array from_u16_array u16 16;
        to_u32_array from_u32_array u32 8;
        to_u64_array from_u64_array u64 4;
        to_u128_array from_u128_array u128 2;
    );

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
            let y = self.0[j];
            if y != 0 {
                let sig_bits = 64usize
                    .wrapping_sub(y.leading_zeros() as usize)
                    .wrapping_add(64usize.wrapping_mul(j));
                // the nibble with the msb and all less significant nibbles count
                char_len = (sig_bits >> 2).wrapping_add(((sig_bits & 0b11) != 0) as usize);
                for i in 0..=j {
                    let x = self.0[i];
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

    /// The `uint` implementation of `FromStr` is unsuitable because it is
    /// hexadecimal only (intentional by their developers because they did not
    /// make the mistake of using decimal in message passing implementations and
    /// do not have wasteful "0x" prefixes), this function will switch between
    /// hexadecimal and decimal depending on if there is a "0x" prefix.
    pub fn from_dec_or_hex_str(s: &str) -> Result<U256, FromStrRadixErr> {
        if let Some(val) = s.strip_prefix("0x") {
            Ok(U256::from_str_radix(val, 16)?)
        } else {
            Ok(U256::from_str_radix(s, 10)?)
        }
    }

    pub fn as_u8_slice_mut(&mut self) -> &mut [u8; 32] {
        // this will not panic because `[u8; 32]` is the right size
        bytemuck::try_cast_mut(&mut self.0).unwrap()
    }

    /// # Errors
    ///
    /// If the number of bytes is greater than the number of bytes in `Self`
    pub fn from_bytes_be(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > 32 {
            return None
        }
        let mut a = [0u8; 32];
        a[(32 - bytes.len())..].copy_from_slice(bytes);
        a.reverse();
        Some(U256::from_u8_array(a))
    }

    pub fn to_u8_array_be(self) -> [u8; 32] {
        let mut a = self.to_u8_array();
        a.reverse();
        a
    }

    #[must_use]
    pub fn wrapping_add(self, other: U256) -> U256 {
        self.overflowing_add(other).0
    }

    #[must_use]
    pub fn wrapping_sub(self, other: U256) -> U256 {
        self.overflowing_sub(other).0
    }

    #[must_use]
    pub fn wrapping_mul(self, other: U256) -> U256 {
        self.overflowing_mul(other).0
    }

    pub fn checked_div_rem(self, other: U256) -> Option<(U256, U256)> {
        if other.is_zero() {
            None
        } else {
            Some(self.div_mod(other))
        }
    }

    /// Randomly-assigns `self` using a `rand_core::RngCore` random number
    /// generator
    ///
    /// ```
    /// // Example using the `rand_xoshiro` crate.
    /// use rand_xoshiro::{rand_core::SeedableRng, Xoshiro128StarStar};
    /// use u64_array_bigints::U256;
    ///
    /// let mut rng = Xoshiro128StarStar::seed_from_u64(0);
    ///
    /// assert_eq!(
    ///     U256::rand_using(&mut rng),
    ///     U256::from_u64_array([
    ///         0x9a089d75dec9045d,
    ///         0xc3e16405ab77d362,
    ///         0x60dea0565c95a8da,
    ///         0xa4290614c25a5140,
    ///     ])
    /// );
    /// ```
    #[cfg(feature = "rand_support")]
    pub fn rand_using<R>(rng: &mut R) -> Self
    where
        R: rand_core::RngCore,
    {
        let mut res = Self::zero();
        for i in 0..res.0.len() {
            res.0[i] = rng.next_u64();
        }
        res
    }
}

impl Serialize for U256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_hex_string())
    }
}

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
