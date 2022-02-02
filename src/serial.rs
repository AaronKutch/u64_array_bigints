use alloc::{borrow::ToOwned, format, string::String};

use crate::Uint;

pub struct FromStrRadixErr;

impl<const LEN: usize> Uint<LEN> {
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
}
