<p align="center">
<img src="https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/mule-with-map.png" width="200" height="200"
style="border-radius:50%" />
</p>

# `MuleMap<🫏,🗺>`
[![ci](https://github.com/gringasalpastor/mule-map/actions/workflows/ci.yml/badge.svg)](https://github.com/gringasalpastor/mule-map/actions/workflows/ci.yml)
[![](https://docs.rs/mule-map/badge.svg)](https://docs.rs/mule-map)
[![Version](https://img.shields.io/crates/v/mule-map.svg?style=flat-square)](https://crates.io/crates/mule-map)

`MuleMap` is a hybrid between a `HashMap` and a lookup table. It improves performance for frequently accessed keys in a known range. If a key (integer) is in the user specified range, then its value will be stored directly in the lookup table. Benchmarks (using random selection) start to show speed improvements when about 50% of the key accesses are in the lookup table. Performance is almost identical to `HashMap` with less than 50%. `MuleMap` tries to match the API of the standard library `HashMap` - making it a drop-in replacement for `HashMap`.

## Example


```rust
use mule_map::MuleMap;
use std::num::NonZero;
type Hash = fnv_rs::FnvBuildHasher;  // Use whatever hash function you prefer

// Using Entry API
let mut mule_map = MuleMap::<u32, usize, Hash>::new();
assert_eq!(mule_map.get(5), None);
let entry = mule_map.entry(5);
entry.or_insert(10);
assert_eq!(mule_map.get(5), Some(&10));

// Using NonZero and bump
let mut mule_map_non_zero = MuleMap::<u32, NonZero<i32>, Hash>::default();

mule_map_non_zero.bump_non_zero(10);
mule_map_non_zero.bump_non_zero(10);
mule_map_non_zero.bump_non_zero(999_999);
mule_map_non_zero.bump_non_zero(999_999);

assert_eq!(mule_map_non_zero.get(10), NonZero::<i32>::new(2).as_ref());
assert_eq!(mule_map_non_zero.get(999_999),NonZero::<i32>::new(2).as_ref());
```

## Highlights

 - All primitive integer types are supported for keys (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i32`, `i64`, `i128`, and `isize`).
 - All corresponding `NonZero<T>` types are supported for keys.
 - `NonZero<T>` key types take advantage of the niche optimizations (guaranteed by the rust compiler) by being stored as an `Option<NonZero<T>>`. This is used by `bump_non_zero()` to directly cast `Option<NonZero<T>>` to it's underlying integer type (using bytemuck - **no unsafe code**) and directly incrementing its value. See [benchmarks](#benchmarks) for details. 
 - *NOTE*: Currently the type of a const generic can't depend on another generic type argument, so `TABLE_MIN_VALUE` can't use the same type as the key. Because of this, I am using `i128`, but that means we can't represent values near `u128::MAX`. Hopefully having frequent keys near `u128::MAX` is extremely rare.
 - No unsafe code used in safe APIs.

## <a name="benchmarks"></a> Benchmarks

### Benchmark Setup

- Takes 2 random uniform distributions of small and large keys, and counts the frequency of all of the keys. 
- `MuleMap` stores the small keys (near 0) in its lookup table.
- The benchmarks are run with and without shuffling the 2 random distributions of keys. 
  - If you expect your lookup table keys to appear in clumps, than the "No Shuffle" graph is more representative of your use case. 
  - If you don't expect runs of small keys (random order), than the graph with the keys shuffled is more representative of your use case.
- "Input" is the percentage of small keys using the lookup table vs large keys that use the `HashMap`.
- Benchmarks were run on a `MacBook` Pro 15-inch, Mid 2015 - 2.8 GHz Quad-Core Intel Core i7 (Sonoma). Both `MuleMap` `HashMap` are using `fnv_rs::FnvBuildHasher`. I tried other hash functions like [GxHash](https://github.com/ogxd/gxhash?tab=readme-ov-file#throughput), but they were slower (likely because my older CPU has slower AES/SSE2 instructions than more modern CPUs).

### Types of Maps Compared

- **Hand Rolled** - Simple loop with an `if` block that switches between a `HashMap` and indexing into a lookup table. This is the baseline to show that `MuleMap` is a zero cost abstraction.
- **`HashMap`** - Uses `HashMap<u32, usize, fnv_rs::FnvBuildHasher>`
- **`MuleMap`** -  Uses `MuleMap<u32, usize, fnv_rs::FnvBuildHasher>`
- **`MuleMap (NonZero)`** -  Uses `MuleMap<u32, NonZero<usize>, fnv_rs::FnvBuildHasher>`. This take advantage of the niche optimizations by directly casting `Option<NonZero<usize>>` to `usize` using bytemuck (**no unsafe code**)

![violin](https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/lines-freq-count-no-shuffle.png)
![lines](https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/lines-freq-count.png)

## License

Licensed under either of:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or [https://www.apache.org/licenses/LICENSE-2.0](https://www.apache.org/licenses/LICENSE-2.0))
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or [https://opensource.org/licenses/MIT](https://opensource.org/licenses/MIT))

at your option.
