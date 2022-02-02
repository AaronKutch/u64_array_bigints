use alloc::string::String;

use crate::Uint;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct U256(pub Uint<4>);

impl U256 {
    pub const fn zero() -> Self {
        Self(Uint::zero())
    }

    pub const fn one() -> Self {
        Self(Uint::one())
    }
}

// the unwraps here will not panic if $n is correct
macro_rules! to_from_array {
    ($($to_fn:ident $from_fn:ident $uX:ident $n:expr);*;) => {
        $(
            pub fn $to_fn(self) -> [$uX; $n] {
                bytemuck::try_cast(self.0.0).unwrap()
            }

            pub fn $from_fn(x: [$uX; $n]) -> Self {
                Self(Uint(bytemuck::try_cast(x).unwrap()))
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

    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }

    pub fn to_hex_string(self) -> String {
        self.0.to_hex_string()
    }

    /// The `uint` implementation of `FromStr` is unsuitable because it is
    /// hexadecimal only (intentional by their developers because they did not
    /// make the mistake of using decimal in message passing implementations and
    /// do not have wasteful "0x" prefixes), this function will switch between
    /// hexadecimal and decimal depending on if there is a "0x" prefix.
    /*pub fn from_dec_or_hex_str(s: &str) -> Result<U256, FromStrRadixErr> {
        if let Some(val) = s.strip_prefix("0x") {
            Ok(U256::from_str_radix(val, 16)?)
        } else {
            Ok(U256::from_str_radix(s, 10)?)
        }
    }*/

    pub fn as_u8_slice_mut(&mut self) -> &mut [u8; 32] {
        // this will not panic because `[u8; 32]` is the right size
        bytemuck::try_cast_mut(&mut self.0 .0).unwrap()
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

    pub const fn overflowing_add(self, other: Self) -> (Self, bool) {
        let tmp = self.0.overflowing_add(other.0);
        (Self(tmp.0), tmp.1)
    }

    pub const fn overflowing_sub(self, other: Self) -> (Self, bool) {
        let tmp = self.0.overflowing_sub(other.0);
        (Self(tmp.0), tmp.1)
    }

    pub const fn overflowing_mul(self, other: Self) -> (Self, bool) {
        let tmp = self.0.overflowing_mul(other.0);
        (Self(tmp.0), tmp.1)
    }

    #[must_use]
    pub const fn wrapping_add(self, other: Self) -> Self {
        Self(self.0.wrapping_add(other.0))
    }

    #[must_use]
    pub const fn wrapping_sub(self, other: Self) -> Self {
        Self(self.0.wrapping_sub(other.0))
    }

    #[must_use]
    pub const fn wrapping_mul(self, other: Self) -> Self {
        Self(self.0.wrapping_mul(other.0))
    }

    // can't use `map` because of `const`

    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        match self.0.checked_add(rhs.0) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        match self.0.checked_sub(rhs.0) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        match self.0.checked_mul(rhs.0) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }
}

/*impl Serialize for U256 {
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
}*/
