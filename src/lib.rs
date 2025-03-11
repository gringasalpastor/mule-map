//! <p align="center">
//!  <img
//!   src="https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/mule-with-map.png"
//!   width="200"
//!   height="200"
//!   style="border-radius:50%" />
//! </p>
//!
//! [`MuleMap`] is a hybrid between a [`HashMap`](std::collections::HashMap) and a lookup table. If a key is between  [`TABLE_MIN_VALUE`](MuleMap)
//! and [`TABLE_MAX_VALUE`](MuleMap), then the value will be stored directly in the lookup table (keys must be integers)
//! at `table[key - TABLE_MIN_VALUE]`, instead of the slower [`HashMap`](std::collections::HashMap). Benchmarks start to show speed improvements
//! starting when  ~50% of the key accesses are in the lookup table. Performance is almost identical to [`HashMap`](std::collections::HashMap) when
//! less than 50%  [`MuleMap`] tries to match the API of the standard library `HashMap` when possible.
//!
//! ## Example
//!
//! ```rust
//! use mule_map::MuleMap;
//!
//! type Hash = fnv_rs::FnvBuildHasher;  // Use whatever hash function you prefer
//! let mut mule_map = MuleMap::<u32, usize, Hash>::new();
//!
//! assert_eq!(mule_map.get(5), None);
//! let entry = mule_map.entry(5);
//! entry.or_insert(10);
//! assert_eq!(mule_map.get(5), Some(&10));
//! ```
//!
//! ## Limitations
//!
//!  - Only supports keys that are primitive integer types ([`u8`], [`u16`], [`u32`], [`u64`], [`u128`], ~~[`usize`]~~,
//!     [`i8`], [`i16`], [`i32`], [`i64`], [`i128`], and ~~[`isize`]~~).
//!  - Does not currently support automatically converting enum's with primitive representations.
//!  - Currently the type of a const generic can't depend on another generic type argument, so [`TABLE_MIN_VALUE`](MuleMap) and
//!     [`TABLE_MAX_VALUE`](MuleMap) can't use the same type as the key. Because of this, I am using [`i128`], but that means
//!     we can't represent values near [`u128::MAX`]. Hopefully having frequent keys near [`u128::MAX`] is extremely rare.
//!  - Currently requires `std`
//!
//! ## Benchmarks
//!
//! ![violin](https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/violin.svg)
//! ![lines](https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/lines.svg)

pub use crate::mule_map::entry::*;
pub use crate::mule_map::*;
// pub use crate::mule_map2::entry::*;
pub use crate::mule_map2::*;

mod mule_map;
mod mule_map2;
