use core::{
    cmp::Ordering,
    ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not},
};

use crate::Uint;

impl<const LEN: usize> PartialOrd for Uint<LEN> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const LEN: usize> Ord for Uint<LEN> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.const_lt(other) {
            Ordering::Less
        } else if self == other {
            Ordering::Equal
        } else {
            Ordering::Greater
        }
    }
}

impl<const LEN: usize> Not for Uint<LEN> {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.const_not()
    }
}

impl<const LEN: usize> BitOr for Uint<LEN> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.const_or(rhs)
    }
}

impl<const LEN: usize> BitAnd for Uint<LEN> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.const_and(rhs)
    }
}

impl<const LEN: usize> BitXor for Uint<LEN> {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.const_xor(rhs)
    }
}

impl<const LEN: usize> BitOrAssign for Uint<LEN> {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.const_or(rhs);
    }
}

impl<const LEN: usize> BitAndAssign for Uint<LEN> {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = self.const_and(rhs);
    }
}

impl<const LEN: usize> BitXorAssign for Uint<LEN> {
    fn bitxor_assign(&mut self, rhs: Self) {
        *self = self.const_xor(rhs);
    }
}
