use crate::{const_for, Uint};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct U256(pub Uint<4>);

// note: u128 has to be handled separately because of endianness changes
//
// the unwraps here will not panic if $n is correct
macro_rules! to_from_array {
    ($($to_fn:ident $from_fn:ident $uX:ident $n:expr);*;) => {
        $(
            pub fn $from_fn(mut x: [$uX; $n]) -> Self {
                const_for!(i in {0..x.len()} {
                    // on little endian this is a no-op, on big endian this fixes the endianness
                    x[i] = $uX::from_le(x[i]);
                });
                let mut res = Self(Uint(bytemuck::try_cast(x).unwrap()));
                const_for!(i in {0..res.0.0.len()} {
                    // I don't care to think about perf on bigendian, I only care about correctness
                    res.0.0[i] = u64::from_le(res.0.0[i]);
                });
                res
            }

            pub fn $to_fn(self) -> [$uX; $n] {
                let mut tmp = self;
                const_for!(i in {0..tmp.0.0.len()} {
                    tmp.0.0[i] = u64::from_le(self.0.0[i]);
                });
                let mut x: [$uX; $n] = bytemuck::try_cast(tmp.0.0).unwrap();
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
                res.0.0[0] = x as u64;
                res
            }

            pub const fn $to_fn(self) -> $uX {
                self.0.0[0] as $uX
            }
        )*
    };
}

macro_rules! try_resize {
    ($($try_resize_fn:ident $resize_fn:ident $uX:ident $n:expr);*;) => {
        $(
            pub const fn $try_resize_fn(self) -> Option<$uX> {
                if self.lz() > (256 - $n) {
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
        Self(Uint(x))
    }

    pub const fn to_u64_array(self) -> [u64; 4] {
        self.0 .0
    }

    pub const fn from_bool(x: bool) -> Self {
        let mut res = Self::zero();
        res.0 .0[0] = x as u64;
        res
    }

    pub const fn resize_to_bool(self) -> bool {
        (self.0 .0[0] & 1) != 0
    }

    pub const fn from_u128(x: u128) -> Self {
        let mut res = Self::zero();
        res.0 .0[0] = x as u64;
        res.0 .0[1] = (x >> 64) as u64;
        res
    }

    pub const fn resize_to_u128(self) -> u128 {
        (self.0 .0[0] as u128) | ((self.0 .0[1] as u128) << 64)
    }

    pub const fn zero() -> Self {
        Self(Uint::zero())
    }

    pub const fn one() -> Self {
        Self(Uint::one())
    }

    pub const fn max_value() -> Self {
        Self(Uint::max_value())
    }

    pub fn is_zero(self) -> bool {
        self.0.is_zero()
    }

    /// Significant bits
    pub fn sig_bits(self) -> usize {
        256usize.wrapping_sub(self.lz())
    }

    /// This gives a straight byte slice view into `self`, be aware that it
    /// changes on big endian systems
    pub fn as_u8_slice_mut(&mut self) -> &mut [u8; 32] {
        // this will not panic because `[u8; 32]` is the right size
        bytemuck::try_cast_mut(&mut self.0 .0).unwrap()
    }

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

    pub const fn checked_shl(self, s: usize) -> Option<Self> {
        match self.0.checked_shl(s) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    pub const fn checked_shr(self, s: usize) -> Option<Self> {
        match self.0.checked_shr(s) {
            Some(x) => Some(Self(x)),
            None => None,
        }
    }

    /// Shift left by 1
    #[must_use]
    pub const fn shl1(self) -> Self {
        match self.checked_shl(1) {
            Some(x) => x,
            None => unreachable!(),
        }
    }

    /// Shift right by 1
    #[must_use]
    pub const fn shr1(self) -> Self {
        match self.checked_shr(1) {
            Some(x) => x,
            None => unreachable!(),
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
        Self(Uint::rand_using(rng))
    }
}

/// These are forwarded from `Uint<4>`
impl U256 {
    pub const fn bw() -> usize {
        Uint::<4>::bw()
    }

    pub const fn lsb(&self) -> bool {
        self.0.lsb()
    }

    pub const fn msb(&self) -> bool {
        self.0.msb()
    }

    pub const fn lz(&self) -> usize {
        self.0.lz()
    }

    pub const fn tz(&self) -> usize {
        self.0.tz()
    }

    pub const fn count_ones(&self) -> usize {
        self.0.count_ones()
    }

    pub const fn const_eq(&self, rhs: &Self) -> bool {
        self.0.const_eq(&rhs.0)
    }

    pub const fn const_lt(&self, rhs: &Self) -> bool {
        self.0.const_lt(&rhs.0)
    }

    pub const fn const_le(&self, rhs: &Self) -> bool {
        self.0.const_le(&rhs.0)
    }

    pub const fn const_gt(&self, rhs: &Self) -> bool {
        self.0.const_gt(&rhs.0)
    }

    pub const fn const_ge(&self, rhs: &Self) -> bool {
        self.0.const_eq(&rhs.0)
    }

    pub const fn overflowing_short_cin_mul(self, cin: u64, rhs: u64) -> (Self, u64) {
        let tmp = self.0.overflowing_short_cin_mul(cin, rhs);
        (Self(tmp.0), tmp.1)
    }

    pub const fn overflowing_short_mul_add(self, lhs: Self, rhs: u64) -> (Self, bool) {
        let tmp = self.0.overflowing_short_mul_add(lhs.0, rhs);
        (Self(tmp.0), tmp.1)
    }

    pub const fn overflowing_mul_add(self, lhs: Self, rhs: Self) -> (Self, bool) {
        let tmp = self.0.overflowing_mul_add(lhs.0, rhs.0);
        (Self(tmp.0), tmp.1)
    }

    pub const fn checked_short_divide(self, div: u64) -> Option<(Self, u64)> {
        match self.0.checked_short_divide(div) {
            Some((x, o)) => Some((Self(x), o)),
            None => None,
        }
    }

    pub const fn panicking_short_divide(self, div: u64) -> (Self, u64) {
        let tmp = self.0.panicking_short_divide(div);
        (Self(tmp.0), tmp.1)
    }

    pub const fn divide(self, div: Self) -> Option<(Self, Self)> {
        match self.0.divide(div.0) {
            Some((x, y)) => Some((Self(x), Self(y))),
            None => None,
        }
    }
}

impl Default for U256 {
    fn default() -> Self {
        Self::zero()
    }
}
