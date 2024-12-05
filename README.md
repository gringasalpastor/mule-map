
# `MuleMap<🫏,🗺>`
`MuleMap` is a hybrid between a `HashMap` and a lookup table. Use `MuleMap` when the majority of your map accesses use keys that are near a fixed point `n` (by default we optimize for keys near 0). `MuleMap` tries to match as much as possible the same API as the standard `HashMap` (with a few minor differences) - making it a drop in replacement. 

## Example



## Limitations

 - Only supports keys that are primitive integer types (`u8`, `u16`, `u32`, `u64`, `u128`, ~~`usize`~~, `i8`, `i16`, `i32`, `i64`, `i128`, and ~~`isize`~~). Non-primitive keys could be added if demand is seen, otherwise not likely.
 - Does not support automatically converting enum's with primitive representations. Will be added in the future. 
 - Currently the type of a const generic can't depend on another generic type argument, so `TABLE_MIN_VALUE` and `TABLE_MAX_VALUE` can't use the same type as the key. Because of this, I am using `i128`, but that means we can't represent values near `u128::MAX`. Hopefully having frequent keys near `u128::MAX` is extremely rare.



