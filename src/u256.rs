use crate::Uint;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct U256(pub Uint<4>);

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

    pub const fn resize_to_u64(&self) -> u64 {
        self.0.resize_to_u64()
    }

    pub const fn from_u64(x: u64) -> Self {
        Self(Uint::from_u64(x))
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