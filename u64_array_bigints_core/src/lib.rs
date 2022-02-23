#![no_std]

extern crate alloc;
mod serial;
#[cfg(not(feature = "use_parity_uint"))]
mod std_ops;
#[cfg(not(feature = "use_parity_uint"))]
mod u256;
#[cfg(not(feature = "use_parity_uint"))]
mod uint;
mod utils;
pub use serial::FromStrRadixErr;
#[cfg(not(feature = "use_parity_uint"))]
pub use u256::U256;
#[cfg(not(feature = "use_parity_uint"))]
pub use uint::Uint;

#[cfg(feature = "use_parity_uint")]
mod parity_uint;
#[cfg(feature = "use_parity_uint")]
pub use parity_uint::*;
