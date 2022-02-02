pub const BITS: usize = 64;

/// Returns the number of extra bits given `bw`
#[inline]
pub const fn extra_u(bw: usize) -> usize {
    bw & (BITS - 1)
}

/// Returns the number of _whole_ digits (not including a digit with unused
/// bits) given `bw`
#[inline]
pub const fn digits_u(bw: usize) -> usize {
    bw.wrapping_shr(BITS.trailing_zeros())
}

/// Computes x + y + z and returns the widened result as a tuple.
#[inline]
pub const fn widen_add(x: u64, y: u64, z: u64) -> (u64, u64) {
    let (sum, carry0) = x.overflowing_add(y);
    let (sum, carry1) = sum.overflowing_add(z);
    (sum, (carry0 as u64) + (carry1 as u64))
}

/// Computes (x * y) + z. This cannot overflow, because it returns the value
/// widened into a tuple, where the first element is the least significant part
/// of the integer and the second is the most significant.
#[inline]
pub const fn widen_mul_add(x: u64, y: u64, z: u64) -> (u64, u64) {
    let tmp = (x as u128).wrapping_mul(y as u128).wrapping_add(z as u128);
    (tmp as u64, tmp.wrapping_shr(64) as u64)
}

/// Divides `duo` by `div` and returns the quotient and remainder.
///
/// # Panics
///
/// If `div == 0`, this function will panic.
#[inline]
pub const fn dd_division(duo: (u64, u64), div: (u64, u64)) -> ((u64, u64), (u64, u64)) {
    let duo = duo.0 as u128 | ((duo.1 as u128) << 64);
    let div = div.0 as u128 | ((div.1 as u128) << 64);
    let tmp0 = duo.wrapping_div(div);
    let tmp1 = duo.wrapping_rem(div);
    (
        (tmp0 as u64, (tmp0 >> 64) as u64),
        (tmp1 as u64, (tmp1 >> 64) as u64),
    )
}

/// A basic for loop for const contexts
#[doc(hidden)]
#[macro_export]
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
