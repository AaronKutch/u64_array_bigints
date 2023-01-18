//! Note: this is all reexported from the main `u64_array_bigints` crate

extern crate alloc;
use alloc::{format, string::ToString};

extern crate proc_macro;
use proc_macro::TokenStream;
use u64_array_bigints_core::U256;

/// Converts what is entered into it into a &str, which is entered into
/// `U256::from_dec_or_hex_str`, the result of which is unwrapped at compile
/// time to produce a const `U256`.
#[proc_macro]
pub fn u256(input: TokenStream) -> TokenStream {
    let input = input.to_string();
    match U256::from_dec_or_hex_str(&input) {
        Ok(x) => {
            // `from_u64_array` is const.
            // we use `u64_array_bigints` because that is what most users will be using
            format!(
                "u64_array_bigints::U256::from_u64_array({:?})",
                x.to_u64_array()
            )
            .parse()
            .unwrap()
        }
        Err(e) => {
            panic!("Invalid U256 string representation: {e:?} for \"{input}\".");
        }
    }
}
