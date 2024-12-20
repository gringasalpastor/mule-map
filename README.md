<p align="center">
<img src="https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/mule-with-map.png" width="200" height="200"
style="border-radius:50%" />
</p>

# `MuleMap<🫏,🗺>`
[![ci](https://github.com/gringasalpastor/mule-map/actions/workflows/ci.yml/badge.svg)](https://github.com/gringasalpastor/mule-map/actions/workflows/ci.yml)
[![](https://docs.rs/mule-map/badge.svg)](https://docs.rs/mule-map)
[![Version](https://img.shields.io/crates/v/mule-map.svg?style=flat-square)](https://crates.io/crates/mule-map)



`MuleMap` is a hybrid between a `HashMap` and a lookup table. Use `MuleMap` when the majority of your map accesses use keys that are near a fixed point `n` (by default we assume keys near 0). `MuleMap` tries to match the API of the standard library `HashMap`, when possible. 

## Example


```rust
use MuleMap;

type Hash = fnv_rs::FnvBuildHasher;  // Use whatever hash function you prefer
let mut mule_map = MuleMap::<u32, usize, Hash>::new();

assert_eq!(mule_map.get(5), None);
let entry = mule_map.entry(5);
entry.or_insert(10);
assert_eq!(mule_map.get(5), Some(&10));
```

## Limitations

 - Only supports keys that are primitive integer types (`u8`, `u16`, `u32`, `u64`, `u128`, ~~`usize`~~, `i8`, `i16`, `i32`, `i64`, `i128`, and ~~`isize`~~). Non-primitive keys could be added if demand is seen, otherwise not likely.
 - Does not support automatically converting enum's with primitive representations. Likely to be added in the future. 
 - Currently the type of a const generic can't depend on another generic type argument, so `TABLE_MIN_VALUE` and `TABLE_MAX_VALUE` can't use the same type as the key. Because of this, I am using `i128`, but that means we can't represent values near `u128::MAX`. Hopefully having frequent keys near `u128::MAX` is extremely rare.
 - Currently requires `std`, but if there is demand it would not be hard to make `no_std`.

## Benchmarks

![violin](https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/violin.svg)
![lines](https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/lines.svg)

## License

Licensed under either of:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or https://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)

at your option.
