//! <p align="center">
//!  <img
//!   src="https://raw.githubusercontent.com/gringasalpastor/mule-map/refs/heads/master/assets/mule-with-map.png"
//!   width="200"
//!   height="200"
//!   style="border-radius:50%" />
//! </p>
//!
//! [`MuleMap`] is a hybrid between a [`HashMap`] and a lookup table. If a key is between  [`TABLE_MIN_VALUE`](MuleMap)
//! and [`TABLE_MAX_VALUE`](MuleMap), then the value will be stored directly in the lookup table (keys must be integers)
//! at `table[key - TABLE_MIN_VALUE]`, instead of the slower [`HashMap`]. Benchmarks start to show speed improvements
//! starting when  ~50% of the key accesses are in the lookup table. Performance is almost identical to [`HashMap`] when
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

pub use crate::entry::private::{
    Entry, OccupiedEntry, OccupiedHashMapEntry, OccupiedVecEntry, VacantEntry, VacantHashMapEntry,
    VacantVecEntry,
};

use num_traits::AsPrimitive;
use num_traits::PrimInt;
use sealed::sealed;
use std::collections::HashMap;
use std::fmt::Debug;

/// Pass this as the generic argument to [`MuleMap`]'s `ZERO_IS_SENTINEL`  to treat 0 as a sentinel and enable various
/// additional optimizations. See: [`MuleMap`] for more details.
///
/// # Example
///
/// ```
/// let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, {ZERO_SENTINEL}>::new();
/// ```
pub const ZERO_SENTINEL: bool = true;

/// Pass this as the generic argument to [`MuleMap`]'s `ZERO_IS_SENTINEL`  to **not** treat 0 as a sentinel and **not**
/// enable various additional optimizations. See: [`MuleMap`] for more details. Note, this is the default.  
///
/// # Example
///
///```
/// let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, {NOT_ZERO_SENTINEL}>::new();
/// ```
pub const NOT_ZERO_SENTINEL: bool = false;

mod entry;

/// [`MuleMap`] is a hybrid between a [`HashMap`] and a lookup table. [`MuleMap`] tries to match the API of the standard
/// library [`HashMap`] when possible.
///
/// # Differences between [`HashMap`] and [`MuleMap`]
///
/// - **The key, `K`, must be an integer type.** - The key is directly mapped to the index in the lookup, so it must be
///     an integer.
/// - **The key, `K`, is passed by value** - Because it is a primitive integer type.
/// - **The hash builder, `S`,  does not have a default** - You must specify your hash builder. The assumption being
///     that if you need better performance you will likely also want to use a custom hash function.
/// - **`const ZERO_IS_SENTINEL: bool`** - If set to [`ZERO_SENTINEL`], then the lookup table will use 0 as a sentinel
///     which enables various additional optimizations. **NOTE:** debug mode will try to detect (if possible) if a value was
///     set to 0 and panic. Do not set values to 0 hoping to remove it, use the remove APIs. By default this is set to [`NOT_ZERO_SENTINEL`]
/// - **`TABLE_MIN_VALUE` and `TABLE_MAX_VALUE`** -  If a key is between `TABLE_MIN_VALUE` and `TABLE_MAX_VALUE`, then
///     the value will be stored directly in the lookup table at  `table[key - TABLE_MIN_VALUE]`, instead of the `HashMap`.
///     **NOTE:** Currently the type of a const generic can’t depend on another generic type argument, so `TABLE_MIN_VALUE`
///     and `TABLE_MAX_VALUE` can’t use the same type as the key. Because of this, I am using [`i128`], but that means we can’t
///     represent values near [`u128::MAX`]. Hopefully having frequent keys near [`u128::MAX`] is extremely rare.
///
/// # Performance
///
/// Benchmarks start to show speed improvements starting when  ~50% of the key accesses are in the lookup table. Performance
/// stayed almost identical to [`HashMap`] when less than 50%. Every use case is unique, and I expect users to do their own tests.
///
/// ## Example
///
/// ```
/// type Hash = fnv_rs::FnvBuildHasher;  /// Use whatever hash function you prefer
/// let mut mule_map = MuleMap::<u32, usize, Hash>::new();
///
/// assert_eq!(mule_map.get(5), None);
/// mule_map.entry(5).or_insert(10);
/// assert_eq!(mule_map.get(5), Some(&10));
/// ```
#[derive(Debug)]
pub struct MuleMap<
    K,
    V,
    S,
    const ZERO_IS_SENTINEL: bool = NOT_ZERO_SENTINEL,
    const TABLE_MIN_VALUE: i128 = 0,
    const TABLE_MAX_VALUE: i128 = { u8::MAX as i128 },
> {
    table: Vec<V>,
    occupied_map: Vec<bool>,
    hash_map: HashMap<K, V, S>,
}

impl<
        K,
        V,
        S,
        const ZERO_IS_SENTINEL: bool,
        const TABLE_MIN_VALUE: i128,
        const TABLE_MAX_VALUE: i128,
    > Default for MuleMap<K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
    V: Clone + PartialEq + Default,
    i128: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    /// Creates an empty `MuleMap`
    fn default() -> Self {
        Self::new()
    }
}

impl<
        K,
        V,
        S,
        const ZERO_IS_SENTINEL: bool,
        const TABLE_MIN_VALUE: i128,
        const TABLE_MAX_VALUE: i128,
    > MuleMap<K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
    V: Clone + PartialEq + Default,
    i128: AsPrimitive<K>,
{
    const STATIC_ASSERT_MAX_GREATER_OR_EQ_MIN: () = assert!(TABLE_MAX_VALUE >= TABLE_MIN_VALUE);

    #[inline]
    #[must_use]
    fn use_lookup_table(key: K) -> bool {
        // `TABLE_MAX_VALUE` and `TABLE_MIN_VALUE` must fit into a key type, K
        // Hopfully in the future they can have type K
        key <= TABLE_MAX_VALUE.as_() && key >= TABLE_MIN_VALUE.as_()
    }

    /// Creates an empty [`MuleMap`].
    ///
    /// The hash map is initially created with a capacity of 0, but space will be allocated for the the lookup table
    /// based on `TABLE_MIN_VALUE` and `TABLE_MAX_VALUE`.
    ///
    /// # Example
    /// ```
    /// let mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// ```
    /// # Panics
    /// - if `TABLE_MAX_VALUE - TABLE_MIN_VALUE + 1` doesn't fit in a `usize`
    /// - if Lookup table size exceeds [`i32::MAX`]
    /// - if `TABLE_MIN_VALUE` or `TABLE_MIN_VALUE` can't fit into the the key type, `K`
    ///
    /// Analogous to [`HashMap::new`]
    #[must_use]
    #[inline]
    pub fn new() -> Self
    where
        <K as TryFrom<i128>>::Error: Debug,
    {
        #[allow(clippy::let_unit_value)]
        let () = Self::STATIC_ASSERT_MAX_GREATER_OR_EQ_MIN;
        // NOTE: Can't make this a static assert yet because of try_from
        assert!(usize::try_from(TABLE_MAX_VALUE - TABLE_MIN_VALUE + 1).is_ok());

        // Hard limit, way beyond practical lookup table size
        assert!(TABLE_MAX_VALUE - TABLE_MIN_VALUE < i128::from(i32::MAX));
        <i128 as TryInto<K>>::try_into(TABLE_MAX_VALUE)
            .expect("TABLE_MAX_VALUE should fit into key type, K");
        <i128 as TryInto<K>>::try_into(TABLE_MIN_VALUE)
            .expect("TABLE_MIN_VALUE should fit into key type, K");

        #[allow(clippy::cast_sign_loss)] // Lookup table size can't exceed `usize`
        let table_size: usize = (TABLE_MAX_VALUE - TABLE_MIN_VALUE + 1) as usize;
        let occupied_map_size: usize = if ZERO_IS_SENTINEL == ZERO_SENTINEL {
            1
        } else {
            table_size
        };

        MuleMap::<K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE> {
            table: vec![V::default(); table_size],
            occupied_map: vec![false; occupied_map_size],
            hash_map: HashMap::default(),
        }
    }

    /// Gets the given key’s corresponding entry in the map for in-place manipulation.
    ///
    /// Analogous to [`HashMap::entry`]
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, ZERO_IS_SENTINEL> {
        if Self::use_lookup_table(key) {
            let key_index = key.key_index();

            if ZERO_IS_SENTINEL == ZERO_SENTINEL {
                if self.table[key_index] == V::default() {
                    Entry::<K, V, ZERO_IS_SENTINEL>::Vacant(VacantEntry::Vec(VacantVecEntry {
                        value: &mut self.table[key_index],
                        occupied: &mut self.occupied_map[0],
                        key,
                    }))
                } else {
                    Entry::<K, V, ZERO_IS_SENTINEL>::Occupied(OccupiedEntry::Vec(
                        OccupiedVecEntry {
                            value: &mut self.table[key_index],
                            occupied: &mut self.occupied_map[0],
                            key,
                        },
                    ))
                }
            } else {
                #[allow(clippy::collapsible_else_if)]
                if self.occupied_map[key_index] {
                    Entry::<K, V, ZERO_IS_SENTINEL>::Occupied(OccupiedEntry::Vec(
                        OccupiedVecEntry {
                            value: &mut self.table[key_index],
                            occupied: &mut self.occupied_map[key_index],
                            key,
                        },
                    ))
                } else {
                    Entry::<K, V, ZERO_IS_SENTINEL>::Vacant(VacantEntry::Vec(VacantVecEntry {
                        value: &mut self.table[key_index],
                        occupied: &mut self.occupied_map[key_index],
                        key,
                    }))
                }
            }
        } else {
            match self.hash_map.entry(key) {
                std::collections::hash_map::Entry::Occupied(base) => {
                    Entry::<K, V, ZERO_IS_SENTINEL>::Occupied(OccupiedEntry::HashMap(
                        OccupiedHashMapEntry { base },
                    ))
                }
                std::collections::hash_map::Entry::Vacant(base) => {
                    Entry::<K, V, ZERO_IS_SENTINEL>::Vacant(VacantEntry::HashMap(
                        VacantHashMapEntry { base },
                    ))
                }
            }
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Analogous to [`HashMap::get`]
    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        if Self::use_lookup_table(key) {
            let key_index = key.key_index();

            #[allow(clippy::collapsible_else_if)]
            if ZERO_IS_SENTINEL == ZERO_SENTINEL {
                if self.table[key_index] == V::default() {
                    None
                } else {
                    Some(&self.table[key_index])
                }
            } else {
                if self.occupied_map[key_index] {
                    Some(&self.table[key_index])
                } else {
                    None
                }
            }
        } else {
            let result = self.hash_map.get(&key);
            debug_assert!(!(ZERO_IS_SENTINEL && result.is_some_and(|x| *x == V::default())));
            result
        }
    }

    /// ???
    #[inline]
    pub fn bump(&mut self, key: K)
    where
        V: std::ops::AddAssign<V> + num_traits::One,
    {
        if Self::use_lookup_table(key) {
            let key_index = key.key_index();
            if ZERO_IS_SENTINEL == ZERO_SENTINEL {
                self.table[key_index] += V::one();
            } else {
                self.occupied_map[key_index] = true;
                self.table[key_index] += V::one();
            }
        } else {
            self.hash_map
                .entry(key)
                .and_modify(|counter| *counter += V::one())
                .or_insert(V::one());
        }
    }

    /// ???
    #[inline]
    pub fn modify_or_insert<F>(&mut self, key: K, f: F, default: V)
    where
        F: FnOnce(&mut V),
    {
        if Self::use_lookup_table(key) {
            let key_index = key.key_index();
            if ZERO_IS_SENTINEL == ZERO_SENTINEL {
                if self.table[key_index] == Default::default() {
                    self.table[key_index] = default;
                } else {
                    f(&mut self.table[key_index]);
                }
            } else {
                if self.occupied_map[key_index] {
                    f(&mut self.table[key_index]);
                } else {
                    self.table[key_index] = default;
                }
                self.occupied_map[key_index] = true;
            }
        } else {
            self.hash_map.entry(key).and_modify(f).or_insert(default);
        }
    }
}

#[sealed]
#[doc(hidden)]
pub trait KeyIndex<K, const TABLE_MIN_VALUE: i128> {
    fn key_index(&self) -> usize;
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u8, TABLE_MIN_VALUE> for u8 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types becasue key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u8) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u16, TABLE_MIN_VALUE> for u16 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types becasue key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u16) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u32, TABLE_MIN_VALUE> for u32 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types becasue key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u64, TABLE_MIN_VALUE> for u64 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types becasue key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u64) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u128, TABLE_MIN_VALUE> for u128 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types becasue key >= TABLE_MIN_VALUE
        // NOTE: i128 can't represent u128::MAX, but it's value will still fit in u128
        (*self - TABLE_MIN_VALUE as u128) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i8, TABLE_MIN_VALUE> for i8 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: Promotion to i16 _needed_ for subtractions because difference could exceed i8::MAX
        (i16::from(*self) - TABLE_MIN_VALUE as i16) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i16, TABLE_MIN_VALUE> for i16 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: Promotion to i32 _needed_ for subtractions because difference could exceed i16::MAX
        (i32::from(*self) - TABLE_MIN_VALUE as i32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i32, TABLE_MIN_VALUE> for i32 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in i32
        (*self - TABLE_MIN_VALUE as i32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i64, TABLE_MIN_VALUE> for i64 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in i64
        (*self - TABLE_MIN_VALUE as i64) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i128, TABLE_MIN_VALUE> for i128 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size (difference) will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in i128
        (*self - TABLE_MIN_VALUE) as usize
    }
}

/// `TABLE_MIN_VALUE` > `TABLE_MAX_VALUE`
/// ```compile_fail
/// use mule_map::*;
/// let mut mule_map_bad = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher,{ ZERO_SENTINEL }, 1, 0>::new();
///
/// ```
fn _doc_test() {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, { ZERO_SENTINEL }>::new();

        assert_eq!(mule_map.get(5), None);
        let entry = mule_map.entry(5);
        entry.or_insert(10);
        assert_eq!(mule_map.get(5), Some(&10));
    }
}
