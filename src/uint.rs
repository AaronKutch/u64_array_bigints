use crate::utils::{dd_division, digits_u, extra_u, widen_add, widen_mul_add, BITS};

/// A basic for loop for const contexts
macro_rules! const_for {
    ($i:ident in $range:block $b:block) => {
        let mut $i: usize = $range.start.wrapping_sub(1);
        loop {
            // the increment must happen before `$b` so that `continue`s still cause it
            $i = $i.wrapping_add(1);
            if $i >= $range.end {
                break
            }
            $b;
        }
    };
    ($i:ident in $range:block.rev() $b:block) => {
        let mut $i: usize = $range.end;
        loop {
            if $i <= $range.start {
                break
            }
            $i = $i.wrapping_sub(1);
            $b;
        }
    };
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Uint<const LEN: usize>(pub [u64; LEN]);

// N.B. much of this code is taken from the `awint` crate, see it for better docs.

// N.B. inspection with `cargo-asm` shows the compiler is smart enough to remove
// bounds checks, no unsafe needed

/// These functions directly correspond to the Rust standard unsigned integers.
impl<const LEN: usize> Uint<LEN> {
    pub const fn zero() -> Self {
        // can't use `const_assert` because of E0401, but is trivially eliminated by
        // compiler
        assert!(LEN > 0);
        // the array should automatically prevent this, but just to be explicit
        assert!(LEN < (isize::MAX as usize));
        // this guarantees that functions related to the bitwidth cannot have problems
        let (tmp, o) = LEN.overflowing_mul(BITS);
        assert!(!o);
        assert!(tmp < (isize::MAX as usize));
        Self([0; LEN])
    }

    pub const fn max() -> Self {
        assert!(LEN > 0);
        assert!(LEN < (isize::MAX as usize));
        Self([u64::MAX; LEN])
    }

    pub const fn one() -> Self {
        let mut this = Self::zero();
        this.0[0] = 1;
        this
    }

    pub const fn is_zero(self) -> bool {
        const_for!(i in {0..LEN} {
            if self.0[i] != 0 {
                return false
            }
        });
        true
    }

    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let mut res = Self::zero();
        let mut carry = 0;
        const_for!(i in {0..LEN} {
            let tmp = widen_add(self.0[i], rhs.0[i], carry);
            res.0[i] = tmp.0;
            carry = tmp.1;
        });
        (res, carry != 0)
    }

    #[must_use]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        self.overflowing_add(rhs).0
    }

    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let tmp = self.overflowing_add(rhs);
        if tmp.1 {
            None
        } else {
            Some(tmp.0)
        }
    }

    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        // 2's complement by carrying in 1 and inverting `rhs`
        let mut res = Self::zero();
        let mut carry = 1;
        const_for!(i in {0..LEN} {
            let tmp = widen_add(self.0[i], !rhs.0[i], carry);
            res.0[i] = tmp.0;
            carry = tmp.1;
        });
        (res, carry == 0)
    }

    #[must_use]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        self.overflowing_sub(rhs).0
    }

    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        let tmp = self.overflowing_sub(rhs);
        if tmp.1 {
            None
        } else {
            Some(tmp.0)
        }
    }

    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        Self::zero().overflowing_mul_add(self, rhs)
    }

    #[must_use]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        self.overflowing_mul(rhs).0
    }

    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        let tmp = self.overflowing_mul(rhs);
        if tmp.1 {
            None
        } else {
            Some(tmp.0)
        }
    }
}

/// special functions
impl<const LEN: usize> Uint<LEN> {
    /// Returns the bitwidth of `Self`
    pub const fn bw() -> usize {
        // Note: this cannot overflow because of the guard in the creation functions
        LEN.wrapping_mul(BITS)
    }

    /// Returns the least significant bit
    #[inline]
    pub const fn lsb(&self) -> bool {
        (self.0[0] & 1) != 0
    }

    /// Returns the most significant bit
    #[inline]
    pub const fn msb(&self) -> bool {
        (self.0[LEN - 1] as isize) < 0
    }

    /// Returns the number of leading zero bits
    pub const fn lz(&self) -> usize {
        const_for!(i in {0..LEN}.rev() {
            let x = self.0[i];
            if x != 0 {
                return ((LEN - 1 - i) * BITS) + (x.leading_zeros() as usize);
            }
        });
        LEN * BITS
    }

    /// Returns the number of trailing zero bits
    pub const fn tz(&self) -> usize {
        const_for!(i in {0..LEN} {
            let x = self.0[i];
            if x != 0 {
                return (i * BITS) + (x.trailing_zeros() as usize);
            }
        });
        LEN * BITS
    }

    /// Returns the number of set ones
    pub const fn count_ones(&self) -> usize {
        let mut ones = 0;
        const_for!(i in {0..LEN} {
            let x = self.0[i];
            ones += x.count_ones() as usize;
        });
        ones
    }

    /// Equality comparison
    pub const fn const_eq(&self, rhs: &Self) -> bool {
        const_for!(i in {0..LEN}.rev() {
            let x = self.0[i];
            let y = rhs.0[i];
            if x != y {
                return false
            }
            // else it is indeterminant and the next digit has to be checked
        });
        true
    }

    /// Less-than comparison
    pub const fn const_lt(&self, rhs: &Self) -> bool {
        const_for!(i in {0..LEN}.rev() {
            let x = self.0[i];
            let y = rhs.0[i];
            if x < y {
                return true
            } else if x != y {
                return false
            }
            // else it is indeterminant and the next digit has to be checked
        });
        false
    }

    /// Less-or-equal comparison
    pub const fn const_le(&self, rhs: &Self) -> bool {
        self.const_eq(rhs) || rhs.const_lt(self)
    }

    /// Greater-than comparison
    pub const fn const_gt(&self, rhs: &Self) -> bool {
        rhs.const_lt(self)
    }

    /// Greater-or-equal comparison
    pub const fn const_ge(&self, rhs: &Self) -> bool {
        self.const_eq(rhs) || rhs.const_lt(self)
    }

    pub const fn resize_to_u64(&self) -> u64 {
        self.0[0]
    }

    pub const fn from_u64(x: u64) -> Self {
        let mut res = Self::zero();
        res.0[0] = x;
        res
    }

    /// Returns `self` incremented starting from `digit`
    pub(crate) const fn inc_starting_from_digit(self, digit: usize) -> Self {
        let mut res = Self::zero();
        const_for!(i in {digit..LEN} {
            match self.0[i].overflowing_add(1) {
                (v, false) => {
                    res.0[i] = v;
                    break
                }
                (v, true) => {
                    res.0[i] = v;
                }
            }
        });
        res
    }

    /// Returns a tuple of `cin + (self * rhs)` and the overflow. The
    /// intermediates are effectively zero extended.
    pub const fn overflowing_short_cin_mul(self, cin: u64, rhs: u64) -> (Self, u64) {
        let mut res = Self::zero();
        let mut carry = cin;
        const_for!(i in {0..LEN} {
            let tmp = widen_mul_add(self.0[i], rhs, carry);
            res.0[i] = tmp.0;
            carry = tmp.1;
        });
        (res, carry)
    }

    /// Returns a tuple of `self + (lhs * rhs)` and if overflow occured.
    pub const fn overflowing_mul_add(self, lhs: Self, rhs: Self) -> (Self, bool) {
        let mut res = self;
        let mut o = false;
        const_for!(lhs_i in {0..LEN} {
            // carry from the short multiplication
            let mut carry0 = 0;
            let mut carry1 = 0;
            const_for!(rhs_i in {0..(LEN - lhs_i)} {
                let tmp0 =
                    widen_mul_add(lhs.0[lhs_i], rhs.0[rhs_i], carry0);
                carry0 = tmp0.1;
                let tmp1 = widen_add(res.0[lhs_i + rhs_i], tmp0.0, carry1);
                carry1 = tmp1.1;
                res.0[lhs_i + rhs_i] = tmp1.0;
            });
            o |= carry0 != 0;
            o |= carry1 != 0;
        });
        (res, o)
    }

    /// Returns a tuple of the quotient and remainder of `self` divided by
    /// `div`. `div` is zero extended. Returns `None` if `div == 0`.
    pub const fn checked_short_divide(self, div: u64) -> Option<(Self, u64)> {
        if div == 0 {
            return None
        }
        let mut res = Self::zero();
        let mut rem = 0;
        const_for!(i in {0..LEN}.rev() {
            let y = self.0[i];
            // the panic here is avoided by the early return
            let tmp = dd_division((y, rem), (div, 0));
            rem = tmp.1.0;
            res.0[i] = tmp.0.0;
        });
        Some((res, rem))
    }

    /// because `unwrap` is not `const` on stable, this exists for
    /// `checked_short_divide(..).unwrap()`
    pub const fn panicking_short_divide(self, div: u64) -> (Self, u64) {
        if div == 0 {
            panic!("division by zero")
        }
        let mut res = Self::zero();
        let mut rem = 0;
        const_for!(i in {0..LEN}.rev() {
            let y = self.0[i];
            // the panic here is avoided by the early return
            let tmp = dd_division((y, rem), (div, 0));
            rem = tmp.1.0;
            res.0[i] = tmp.0.0;
        });
        (res, rem)
    }

    // see the `awint` crate for what this all does

    /// Gets one `u64` digit from `self` starting at the bit index `start`.
    /// Bits that extend beyond `Self::bw()` are zeroed.
    pub const fn get_digit(&self, start: usize) -> u64 {
        let digits = digits_u(start);
        let bits = extra_u(start);
        let mut tmp = 0;
        if digits < LEN {
            tmp = self.0[digits] >> bits;
            if bits != 0 && ((digits + 1) < LEN) {
                tmp |= self.0[digits + 1] << (BITS - bits);
            }
        }
        tmp
    }

    /// Gets two `u64` digits from `self` starting at the bit index `start`,
    /// and returns them in little endian order. Bits that extend beyond
    /// `Self::bw()` are zeroed.
    pub(crate) const fn get_double_digit(&self, start: usize) -> (u64, u64) {
        let digits = digits_u(start);
        let bits = extra_u(start);
        let mut first = 0;
        let mut second = 0;
        if digits < LEN {
            first = self.0[digits] >> bits;
            if (digits + 1) < LEN {
                let mid = self.0[digits + 1];
                if bits == 0 {
                    second = mid;
                } else {
                    first |= mid << (BITS - bits);
                    second = mid >> bits;
                    if (digits + 2) < LEN {
                        second |= self.0[digits + 2] << (BITS - bits);
                    }
                };
            }
        }
        (first, second)
    }

    pub(crate) const fn two_possibility_algorithm(duo: Self, div: Self) -> (Self, Self) {
        debug_assert!(div.lz() > duo.lz());
        debug_assert!((div.lz() - duo.lz()) < BITS);
        debug_assert!((Self::bw() - duo.lz()) >= (BITS * 2));
        let i = Self::bw() - duo.lz() - (BITS * 2);
        let duo_sig_dd = duo.get_double_digit(i);
        let div_sig_dd = div.get_double_digit(i);
        // Because `lz_diff < BITS`, the quotient will fit in one `usize`
        let mut small_quo = dd_division(duo_sig_dd, div_sig_dd).0 .0;
        let tmp = div.overflowing_short_cin_mul(0, small_quo);
        let mut tmp_rem = tmp.0;
        let uof = tmp.1;
        tmp_rem = duo.wrapping_sub(tmp_rem);
        if (uof != 0) || tmp_rem.msb() {
            tmp_rem = tmp_rem.wrapping_add(div);
            small_quo -= 1;
        }
        (Self::from_u64(small_quo), tmp_rem)
    }

    /// Divides `duo` by `div` and returns a tuple of the quotient to and
    /// remainder. Returns `None` if `div.is_zero()`.
    pub const fn divide(duo: Self, div: Self) -> Option<(Self, Self)> {
        if div.is_zero() {
            return None
        }

        let bw = Self::bw();

        let mut duo_lz = duo.lz();
        let div_lz = div.lz();

        // quotient is 0 or 1 branch
        if div_lz <= duo_lz {
            if duo.const_ge(&div) {
                return Some((Self::one(), duo.wrapping_sub(div)))
            } else {
                return Some((Self::zero(), duo))
            }
        }

        // small division branch
        if (bw - duo_lz) <= BITS {
            return Some((
                Self::from_u64(duo.0[0].wrapping_div(div.0[0])),
                Self::from_u64(duo.0[0].wrapping_rem(div.0[0])),
            ))
        }

        // double digit division branch
        if (bw - duo_lz) <= BITS * 2 {
            // LEN > 1 cases cannot reach here so this can be done
            let tmp = dd_division(
                (duo.resize_to_u64(), duo.0[1]),
                (div.resize_to_u64(), div.0[1]),
            );
            // using `usize_assign` to make sure other digits are zeroed
            let mut quo = Self::from_u64(tmp.0 .0);
            quo.0[1] = tmp.0 .1;
            let mut rem = Self::from_u64(tmp.1 .0);
            rem.0[1] = tmp.1 .1;
            return Some((quo, rem))
        }

        // short division branch
        if bw - div_lz <= BITS {
            let (quo, rem) = duo.panicking_short_divide(div.resize_to_u64());
            return Some((quo, Self::from_u64(rem)))
        }

        // Two possibility division algorithm branch
        let lz_diff = div_lz - duo_lz;
        if lz_diff < BITS {
            return Some(Self::two_possibility_algorithm(duo, div))
        }

        let div_extra = bw - div_lz - BITS;
        let div_sig_d = div.get_digit(div_extra);
        let div_sig_d_add1 = widen_add(div_sig_d, 1, 0);
        let mut quo = Self::zero();
        // using `rem` as `duo`
        let mut rem = duo;
        loop {
            let duo_extra = bw - duo_lz - (BITS * 2) + 1;
            // using `<` instead of `<=` because of the change to `duo_extra`
            if div_extra < duo_extra {
                // Undersubtracting long division step

                // `get_dd_unchecked` will not work, e.x. bw = 192 and duo_lz = 0, it will
                // attempt to access an imaginary zero bit beyond the bitwidth
                let duo_sig_dd = {
                    let digits = digits_u(duo_extra);
                    let bits = extra_u(duo_extra);
                    if bits == 0 {
                        (rem.0[digits], rem.0[digits + 1])
                    } else {
                        let mid = rem.0[digits + 1];
                        let last = if digits + 2 == LEN {
                            0
                        } else {
                            rem.0[digits + 2]
                        };
                        (
                            (rem.0[digits] >> bits) | (mid << (BITS - bits)),
                            (mid >> bits) | (last << (BITS - bits)),
                        )
                    }
                };
                let quo_part = dd_division(duo_sig_dd, div_sig_d_add1).0 .0;
                let extra_shl = duo_extra - div_extra;
                let shl_bits = extra_u(extra_shl);
                let shl_digits = digits_u(extra_shl);

                // Addition of `quo_part << extra_shl` to the quotient.
                let (carry, next) = {
                    if shl_bits == 0 {
                        let tmp = widen_add(quo.0[shl_digits], quo_part, 0);
                        quo.0[shl_digits] = tmp.0;
                        (tmp.1 != 0, shl_digits + 1)
                    } else {
                        let tmp0 = widen_add(quo.0[shl_digits], quo_part << shl_bits, 0);
                        quo.0[shl_digits] = tmp0.0;
                        let tmp1 =
                            widen_add(quo.0[shl_digits + 1], quo_part >> (BITS - shl_bits), tmp0.1);
                        quo.0[shl_digits + 1] = tmp1.0;
                        (tmp1.1 != 0, shl_digits + 2)
                    }
                };
                if carry {
                    quo = quo.inc_starting_from_digit(next)
                }

                // Subtraction of `(div * quo_part) << extra_shl` from duo.

                let mut wrap_carry = 0;
                let mut mul_carry = 0;
                let mut add_carry = 1;
                if shl_bits == 0 {
                    const_for!(i in {shl_digits..LEN} {
                        let tmp1 = widen_mul_add(
                            div.0[i - shl_digits],
                            quo_part,
                            mul_carry
                        );
                        mul_carry = tmp1.1;
                        let tmp2 = widen_add(!tmp1.0, rem.0[i], add_carry);
                        add_carry = tmp2.1;
                        rem.0[i] = tmp2.0;
                    });
                } else {
                    const_for!(i in {shl_digits..LEN} {
                        let tmp0 = wrap_carry | (div.0[i - shl_digits] << shl_bits);
                        wrap_carry = div.0[i - shl_digits] >> (BITS - shl_bits);
                        let tmp1 = widen_mul_add(tmp0, quo_part, mul_carry);
                        mul_carry = tmp1.1;
                        let tmp2 = widen_add(!tmp1.0, rem.0[i], add_carry);
                        add_carry = tmp2.1;
                        rem.0[i] = tmp2.0;
                    });
                }
            } else {
                // Two possibility algorithm
                let i = bw - duo_lz - (BITS * 2);
                let duo_sig_dd = rem.get_double_digit(i);
                let div_sig_dd = div.get_double_digit(i);
                let mut small_quo = dd_division(duo_sig_dd, div_sig_dd).0 .0;
                let mut mul_carry = 0;
                let mut add_carry = 1;
                const_for!(i in {0..LEN} {
                    let tmp0 = widen_mul_add(div.0[i], small_quo, mul_carry);
                    mul_carry = tmp0.1;
                    let tmp1 = widen_add(!tmp0.0, rem.0[i], add_carry);
                    add_carry = tmp1.1;
                    rem.0[i] = tmp1.0;
                });
                if rem.msb() {
                    rem = rem.wrapping_add(div);
                    small_quo -= 1;
                }
                // add `quo_add` to `quo`
                let tmp = widen_add(quo.resize_to_u64(), small_quo, 0);
                quo.0[0] = tmp.0;
                if tmp.1 != 0 {
                    quo = quo.inc_starting_from_digit(1);
                }
                return Some((quo, rem))
            }

            duo_lz = rem.lz();

            if div_lz <= duo_lz {
                // quotient can have 0 or 1 added to it
                if div_lz == duo_lz && div.const_le(&rem) {
                    quo.inc_starting_from_digit(0);
                    rem = rem.wrapping_sub(div);
                }
                return Some((quo, rem))
            }

            if (bw - duo_lz) <= (BITS * 2) {
                let tmp = dd_division(
                    (rem.resize_to_u64(), rem.0[1]),
                    (div.resize_to_u64(), div.0[1]),
                );
                let tmp0 = widen_add(quo.resize_to_u64(), tmp.0 .0, 0);

                quo.0[0] = tmp0.0;
                quo = quo.inc_starting_from_digit(1);
                rem = Self::from_u64(tmp.1 .0);
                rem.0[1] = tmp.1 .1;
                return Some((quo, rem))
            }
        }
    }
}
