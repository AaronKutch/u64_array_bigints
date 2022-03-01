// `u64_array_bigints` was not designed for smaller architecture compatibility
// like how `awint` was, but we need correctness at least

macro_rules! usize_conversion {
    (
        $from_fn:ident,
        $to_fn:ident,
        $from_primitive:ident,
        $resize_to_fn:ident,
        $try_resize_to_fn:ident,
        $uX:ident,
        $n:expr
    ) => {
        impl crate::U256 {
            pub fn from_usize_array(x: [usize; $n]) -> Self {
                Self::$from_fn(bytemuck::try_cast(x).unwrap())
            }

            pub fn to_usize_array(self) -> [usize; $n] {
                bytemuck::try_cast(self.$to_fn()).unwrap()
            }

            pub const fn from_usize(x: usize) -> Self {
                Self::$from_primitive(x as $uX)
            }

            pub const fn resize_to_usize(self) -> usize {
                self.$resize_to_fn() as usize
            }

            pub fn try_resize_to_usize(self) -> Option<usize> {
                match self.$try_resize_to_fn() {
                    Some(x) => Some(x as usize),
                    None => None,
                }
            }
        }
    };
}

#[cfg(target_pointer_width = "16")]
usize_conversion!(
    from_u16_array,
    to_u16_array,
    from_u16,
    resize_to_u16,
    try_resize_to_u16,
    u16,
    16
);

#[cfg(target_pointer_width = "32")]
usize_conversion!(
    from_u32_array,
    to_u32_array,
    from_u32,
    resize_to_u32,
    try_resize_to_u32,
    u32,
    8
);

#[cfg(target_pointer_width = "64")]
usize_conversion!(
    from_u64_array,
    to_u64_array,
    from_u64,
    resize_to_u64,
    try_resize_to_u64,
    u64,
    4
);

#[cfg(target_pointer_width = "128")]
usize_conversion!(
    from_u128_array,
    to_u128_array,
    from_u128,
    resize_to_u128,
    try_resize_to_u128,
    u128,
    2
);
