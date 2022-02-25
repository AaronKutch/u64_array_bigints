#![no_std]

extern crate alloc;
mod serial;
mod std_ops;
mod uint;
mod utils;
pub use serial::FromStrRadixErr;

pub use crate::uint::Uint;

#[cfg(not(feature = "use_parity_uint"))]
mod u256;
#[cfg(not(feature = "use_parity_uint"))]
pub use u256::U256;
#[cfg(feature = "use_parity_uint")]
mod parity_uint;
#[cfg(feature = "use_parity_uint")]
pub use parity_uint::*;
