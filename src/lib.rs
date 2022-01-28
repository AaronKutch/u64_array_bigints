#![no_std]

extern crate alloc;
use alloc::{
    borrow::ToOwned,
    format,
    string::{String, ToString},
};

use serde::{Deserialize, Deserializer, Serialize, Serializer};
pub use uint::FromStrRadixErr;

// Currently, this uses the `uint` crate which handles almost everything the way
// we want. TODO when we replace it we can fix clippy and the `FromStr` impl.
// Perhaps we should enforce all hexadecimal in upstream crates so we can remove
// warts.

#[allow(clippy::all)]
mod clippy_guard {
    uint::construct_uint! {
        pub struct U256(4);
    }
}

pub use clippy_guard::U256;

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
        let mut s = "0x".to_owned();
        let mut latch = false;
        for i in (0..self.0.len()).rev() {
            if self.0[i] != 0 {
                // delay until we see a nonzero digit, otherwise we will print an extra leading
                // zero for every digit
                latch = true;
            }
            if latch {
                s += &format!("{:x}", self.0[i]);
            }
        }
        s
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
}

impl Serialize for U256 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&self.to_string())
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
