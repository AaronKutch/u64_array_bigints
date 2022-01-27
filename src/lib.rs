#![no_std]

extern crate alloc;
use alloc::string::{String, ToString};

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

impl U256 {
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
