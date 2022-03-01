use core::ops::{BitAndAssign, BitOrAssign, BitXorAssign};

// `serial.rs` is shared with this implementation, functions that could not be
// shared are reimplemented here
use crate::{
    const_for,
    utils::{dd_division, widen_add, widen_mul_add},
};

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
            pub fn $from_fn(mut x: [$uX; $n]) -> Self {
                const_for!(i in {0..x.len()} {
                    // on little endian this is a no-op, on big endian this fixes the endianness
                    x[i] = $uX::from_le(x[i]);
                });
                let mut res = Self(bytemuck::try_cast(x).unwrap());
                const_for!(i in {0..res.0.len()} {
                    // I don't care to think about perf on bigendian, I only care about correctness
                    res.0[i] = u64::from_le(res.0[i]);
                });
                res
            }

            pub fn $to_fn(self) -> [$uX; $n] {
                let mut tmp = self;
                const_for!(i in {0..tmp.0.len()} {
                    tmp.0[i] = u64::from_le(self.0[i]);
                });
                let mut x: [$uX; $n] = bytemuck::try_cast(tmp.0).unwrap();
                const_for!(i in {0..x.len()} {
                    x[i] = $uX::from_le(x[i]);
                });
                x
            }
        )*
    };
}

macro_rules! to_from_primitive {
    ($($to_fn:ident $from_fn:ident $uX:ident);*;) => {
        $(
            pub const fn $from_fn(x: $uX) -> Self {
                let mut res = Self::zero();
                res.0[0] = x as u64;
                res
            }

            pub const fn $to_fn(self) -> $uX {
                self.0[0] as $uX
            }
        )*
    };
}

macro_rules! try_resize {
    ($($try_resize_fn:ident $resize_fn:ident $uX:ident $n:expr);*;) => {
        $(
            pub fn $try_resize_fn(self) -> Option<$uX> {
                if self.sig_bits() > $n {
                    None
                } else {
                    Some(self.$resize_fn())
                }
            }
        )*
    };
}

impl U256 {
    to_from_array!(
        to_u8_array from_u8_array u8 32;
        to_u16_array from_u16_array u16 16;
        to_u32_array from_u32_array u32 8;
        to_u128_array from_u128_array u128 2;
    );

    to_from_primitive!(
        resize_to_u8 from_u8 u8;
        resize_to_u16 from_u16 u16;
        resize_to_u32 from_u32 u32;
        resize_to_u64 from_u64 u64;
    );

    try_resize!(
        try_resize_to_bool resize_to_bool bool 1;
        try_resize_to_u8 resize_to_u8 u8 8;
        try_resize_to_u16 resize_to_u16 u16 16;
        try_resize_to_u32 resize_to_u32 u32 32;
        try_resize_to_u64 resize_to_u64 u64 64;
        try_resize_to_u128 resize_to_u128 u128 128;
    );

    // Do this separate because we can do it `const`. Const transmute is not stable
    // yet, so even if we went away from `bytemuck` we could not fix it performantly

    pub const fn from_u64_array(x: [u64; 4]) -> Self {
        Self(x)
    }

    pub const fn to_u64_array(self) -> [u64; 4] {
        self.0
    }

    pub const fn from_bool(x: bool) -> Self {
        let mut res = Self::zero();
        res.0[0] = x as u64;
        res
    }

    pub const fn resize_to_bool(self) -> bool {
        (self.0[0] & 1) != 0
    }

    pub const fn from_u128(x: u128) -> Self {
        let mut res = Self::zero();
        res.0[0] = x as u64;
        res.0[1] = (x >> 64) as u64;
        res
    }

    pub const fn resize_to_u128(self) -> u128 {
        (self.0[0] as u128) | ((self.0[1] as u128) << 64)
    }

    pub fn as_u8_slice_mut(&mut self) -> &mut [u8; 32] {
        // this will not panic because `[u8; 32]` is the right size
        bytemuck::try_cast_mut(&mut self.0).unwrap()
    }

    /// # Errors
    ///
    /// If the number of bytes is greater than the number of bytes in `Self`
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > 32 {
            return None
        }
        let mut a = [0u8; 32];
        a[..bytes.len()].copy_from_slice(bytes);
        Some(U256::from_u8_array(a))
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

    pub fn from_u8_array_be(mut x: [u8; 32]) -> Self {
        x.reverse();
        Self::from_u8_array(x)
    }

    pub fn to_u8_array_be(self) -> [u8; 32] {
        let mut a = self.to_u8_array();
        a.reverse();
        a
    }

    /// Significant bits
    pub fn sig_bits(self) -> usize {
        self.bits()
    }

    pub fn lz(&self) -> usize {
        self.leading_zeros() as usize
    }

    #[must_use]
    pub const fn const_or(self, other: U256) -> U256 {
        let mut res = U256::zero();
        const_for!(i in {0usize..4} {
            res.0[i] = self.0[i] | other.0[i];
        });
        res
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

    #[must_use]
    pub const fn wrapping_shl(self, s: usize) -> U256 {
        if s >= 256 {
            panic!("shifted left by >= 256")
        }
        if s == 0 {
            return self
        }
        let mut res = Self::zero();
        // digits to shift by
        let digits = s / 64;
        const_for!(i in {0..(4usize - digits)} {
            res.0[i + digits] = self.0[i];
        });
        // bits to shift by (modulo digit size)
        let bits = s % 64;
        if bits != 0 {
            const_for!(i in {1usize..4}.rev() {
                res.0[i] = (res.0[i - 1] >> (64 - bits))
                    | (res.0[i] << bits);
            });
            res.0[0] <<= bits;
        }
        res
    }

    #[must_use]
    pub fn wrapping_shr(self, s: usize) -> U256 {
        if s >= 256 {
            panic!("shifted right by >= 256")
        } else {
            self >> s
        }
    }

    pub fn checked_shl(self, s: usize) -> Option<U256> {
        if s >= 256 {
            None
        } else {
            Some(self << s)
        }
    }

    pub fn checked_shr(self, s: usize) -> Option<U256> {
        if s >= 256 {
            None
        } else {
            Some(self >> s)
        }
    }

    pub fn checked_rotl(self, s: usize) -> Option<U256> {
        if s >= 256 {
            None
        } else if s == 0 {
            Some(self)
        } else {
            Some(self.wrapping_shl(s) | self.wrapping_shr(256 - s))
        }
    }

    pub fn divide(self, other: U256) -> Option<(U256, U256)> {
        if other.is_zero() {
            None
        } else {
            Some(self.div_mod(other))
        }
    }

    /// Shift left by 1. Returns `None` if overflow results
    #[must_use]
    pub fn shl1(self) -> Option<Self> {
        if self.bits() > 255 {
            return None
        }
        Some(self << 1)
    }

    /// Shift right by 1
    #[must_use]
    pub fn shr1(self) -> Self {
        self >> 1
    }

    /// Returns a tuple of `cin + (self * rhs)` and the overflow. The
    /// intermediates are effectively zero extended.
    pub const fn overflowing_short_cin_mul(self, cin: u64, rhs: u64) -> (Self, u64) {
        let mut res = Self::zero();
        let mut carry = cin;
        const_for!(i in {0usize..4} {
            let tmp = widen_mul_add(self.0[i], rhs, carry);
            res.0[i] = tmp.0;
            carry = tmp.1;
        });
        (res, carry)
    }

    /// Returns `self + (lhs * rhs)` and if overflow occured. The
    /// intermediates are effectively zero extended.
    pub const fn overflowing_short_mul_add(self, lhs: Self, rhs: u64) -> (Self, bool) {
        let mut mul_carry = 0;
        let mut add_carry = 0;
        let mut res = Self::zero();
        const_for!(i in {0usize..4} {
            let tmp0 = widen_mul_add(lhs.0[i], rhs, mul_carry);
            mul_carry = tmp0.1;
            let tmp1 = widen_add(self.0[i], tmp0.0, add_carry);
            add_carry = tmp1.1;
            res.0[i] = tmp1.0;
        });
        (res, (mul_carry != 0) || (add_carry != 0))
    }

    /// Returns a tuple of the quotient and remainder of `self` divided by
    /// `div`. `div` is zero extended. Returns `None` if `div == 0`.
    pub const fn checked_short_divide(self, div: u64) -> Option<(Self, u64)> {
        if div == 0 {
            return None
        }
        let mut res = Self::zero();
        let mut rem = 0;
        const_for!(i in {0..4}.rev() {
            let y = self.0[i];
            // the panic here is avoided by the early return
            let tmp = dd_division((y, rem), (div, 0));
            rem = tmp.1.0;
            res.0[i] = tmp.0.0;
        });
        Some((res, rem))
    }

    /// Quickly ORs `rhs` into `self` at bit position `shl`
    #[must_use]
    pub const fn u64_or(self, rhs: u64, shl: usize) -> Self {
        if shl >= 256 {
            return self
        }
        let mut res = self;
        let bits = shl % 64;
        let digits = shl / 64;
        if bits == 0 {
            res.0[digits] |= rhs;
        } else {
            res.0[digits] |= rhs << bits;
            if (digits + 1) < 4 {
                res.0[digits + 1] |= rhs >> (64 - bits);
            }
        }
        res
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

impl BitOrAssign for U256 {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

impl BitAndAssign for U256 {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl BitXorAssign for U256 {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = *self ^ rhs;
    }
}
