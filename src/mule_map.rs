use entry::{
    Entry, OccupiedEntry, OccupiedHashMapEntry, OccupiedVecEntry, VacantEntry, VacantHashMapEntry,
    VacantVecEntry,
};
use key_index::KeyIndex;
use num_traits::AsPrimitive;
use num_traits::PrimInt;
use sealed::sealed;
use std::collections::HashMap;
use std::fmt::Debug;
use std::num::NonZero;

pub(crate) mod entry;
mod iterators;
mod key_index;

#[sealed]
#[doc(hidden)]
pub trait NonZeroInt {
    type UnderlyingType;
    const ONE: Self;
    #[inline]
    fn checked_add(self, other: Self::UnderlyingType) -> Option<Self>
    where
        Self::UnderlyingType: bytemuck::Pod,
        Self::UnderlyingType: std::ops::AddAssign<Self::UnderlyingType>,
        Self: bytemuck::PodInOption,
        Self::UnderlyingType: PrimInt,
    {
        let mut result = Some(self);
        let x = bytemuck::cast_mut::<Option<Self>, Self::UnderlyingType>(&mut result);
        *x += other;
        result
    }
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI128 {
    const ONE: std::num::NonZeroI128 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = i128;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI16 {
    const ONE: std::num::NonZeroI16 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = i16;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI32 {
    const ONE: std::num::NonZeroI32 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = i32;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI64 {
    const ONE: std::num::NonZeroI64 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = i64;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI8 {
    const ONE: std::num::NonZeroI8 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = i8;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroIsize {
    const ONE: std::num::NonZeroIsize = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = isize;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU128 {
    const ONE: std::num::NonZeroU128 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = u128;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU16 {
    const ONE: std::num::NonZeroU16 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = u16;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU32 {
    const ONE: std::num::NonZeroU32 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = u32;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU64 {
    const ONE: std::num::NonZeroU64 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = u64;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU8 {
    const ONE: std::num::NonZeroU8 = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = u8;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroUsize {
    const ONE: std::num::NonZeroUsize = const { NonZero::new(1).expect("1 is not 0") };
    type UnderlyingType = usize;
}

/// [`MuleMap`] is a hybrid between a [`HashMap`] and a lookup table. It improves performance for frequently accessed
/// keys in a known range. If a key (integer) is in the user specified range, then its value will be stored directly in
/// the lookup table.
///
/// # Differences between [`HashMap`] and [`MuleMap`]
///
/// - **The key, `K`, must be an integer type.** - The key is directly mapped to the index in the lookup, so it must be
///     an integer.
/// - **The key, `K`, is passed by value** - Because it is a primitive integer type.
/// - **The hash builder, `S`,  does not have a default** - You must specify your hash builder. The assumption being
///     that if you need better performance you will likely also want to use a custom hash function.
/// - **`TABLE_MIN_VALUE` and `TABLE_SIZE`** -  If a key is between `TABLE_MIN_VALUE` and `TABLE_MIN_VALUE +
///     TABLE_SIZE`, then the value will be stored directly in the lookup table, instead of using the `HashMap`.
///     **NOTE:** Currently the type of a const generic can’t depend on another generic type argument, so
///     `TABLE_MIN_VALUE` can’t use the same type as the key. Because of this, We are using [`i128`], but that means we
///     can’t represent values near [`u128::MAX`]. Hopefully having frequent keys near [`u128::MAX`] is extremely rare.
///
/// # Performance
///
/// Benchmarks (using random selection) start to show speed improvements when about 50% of the key accesses are in the
/// lookup table. Performance is almost identical to `HashMap` with less than 50%.
///
/// ## Example
///
/// ```
/// use mule_map::MuleMap;
/// use std::num::NonZero;
/// type Hash = fnv_rs::FnvBuildHasher;  // Use whatever hash function you prefer
///
/// // Using Entry API
/// let mut mule_map = MuleMap::<u32, usize, Hash>::new();
/// assert_eq!(mule_map.get(5), None);
/// let entry = mule_map.entry(5);
/// entry.or_insert(10);
/// assert_eq!(mule_map.get(5), Some(&10));
///
/// // Using NonZero and bump
/// let mut mule_map_non_zero = MuleMap::<u32, NonZero<i32>, Hash>::default();
///
/// mule_map_non_zero.bump_non_zero(10);
/// mule_map_non_zero.bump_non_zero(10);
/// mule_map_non_zero.bump_non_zero(999_999);
/// mule_map_non_zero.bump_non_zero(999_999);
///
// assert_eq!(mule_map_non_zero.get(10), NonZero::<i32>::new(2).as_ref());
// assert_eq!(mule_map_non_zero.get(999_999),NonZero::<i32>::new(2).as_ref());
/// ```
#[derive(Debug)]
pub struct MuleMap<
    K,
    V,
    S,
    const TABLE_MIN_VALUE: i128 = 0,
    const TABLE_SIZE: usize = { u8::MAX as usize },
> {
    hash_map: HashMap<K, V, S>,
    table: [Option<V>; TABLE_SIZE],
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Default
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    /// Creates an empty [`MuleMap`].
    ///
    /// # Example
    /// ```
    /// let mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::default();
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::default`]
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    // Hard limit, way beyond practical lookup table size. This makes it easier to calculate the key index
    const STATIC_ASSERT_LIMIT_SIZE_TO_I32_MAX: () =
        assert!((TABLE_SIZE as u128) < i32::MAX as u128);

    #[inline]
    #[must_use]
    fn use_lookup_table(key: K) -> bool {
        // NOTE: TABLE_MIN_VALUE + TABLE_SIZE and TABLE_MIN_VALUE must fit into a key type, K
        key < (TABLE_MIN_VALUE.as_() + TABLE_SIZE.as_()) && key >= TABLE_MIN_VALUE.as_()
    }

    /// Creates an empty [`MuleMap`].
    ///
    /// # Example
    /// ```
    /// let mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::new`]
    #[must_use]
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity_and_hasher(0, S::default())
    }

    /// Creates an empty [`MuleMap`] with at least the provided capacity.
    ///
    /// # Example
    /// ```
    /// let mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::with_capacity(100);
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::with_capacity`]
    #[must_use]
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, S::default())
    }

    /// Creates an empty [`MuleMap`] using `hash_builder`.
    ///
    /// # Example
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::with_hasher(Hash::default());
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::with_hasher`]
    #[must_use]
    #[inline]
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates an empty [`MuleMap`] with at least the provided capacity and using `hash_builder`.
    ///
    /// # Example
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::with_capacity_and_hasher(100, Hash::default());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if
    ///  - `TABLE_MIN_VALUE` or `TABLE_MIN_VALUE + TABLE_SIZE` doesn't fit into key type, `K`.
    ///
    /// Analogous to [`HashMap::with_capacity_and_hasher`]
    #[must_use]
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        let () = Self::STATIC_ASSERT_LIMIT_SIZE_TO_I32_MAX;

        <i128 as TryInto<K>>::try_into(TABLE_MIN_VALUE + TABLE_SIZE as i128)
            .expect("TABLE_MIN_VALUE + TABLE_SIZE should fit into key type, K");
        <i128 as TryInto<K>>::try_into(TABLE_MIN_VALUE)
            .expect("TABLE_MIN_VALUE should fit into key type, K");

        MuleMap::<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE> {
            hash_map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            table: [None; TABLE_SIZE],
        }
    }

    /// Returns capacity of the underlying hash map.
    ///
    /// See [`HashMap::capacity`]
    #[must_use]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.hash_map.capacity()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory for reuse.
    ///
    /// See [`HashMap::clear`]
    pub fn clear(&mut self) {
        self.hash_map.clear();
        self.table.fill(None);
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// Analogous to [`HashMap::contains_key`]
    #[must_use]
    #[inline]
    pub fn contains_key(&self, key: K) -> bool {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].is_some()
        } else {
            self.hash_map.contains_key(&key)
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// Analogous to [`HashMap::get`]
    #[must_use]
    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].as_ref()
        } else {
            let result = self.hash_map.get(&key);
            result
        }
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// Analogous to [`HashMap::get_key_value`]
    pub fn get_key_value(&self, key: K) -> Option<(K, &V)> {
        let result = None;
        result.zip(self.get(key))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// Analogous to [`HashMap::get_mut`]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].as_mut()
        } else {
            self.hash_map.get_mut(&key)
        }
    }

    /// Returns a reference to the map’s [`BuildHasher`].
    ///
    /// Analogous to [`HashMap::hasher`]
    pub fn hasher(&self) -> &S {
        self.hash_map.hasher()
    }

    /// Inserts a key-value pair into the map. If the map did not have this key present, None is returned. If the map
    /// did have this key present, the value is updated, and the old value is returned.
    ///
    /// Analogous to [`HashMap::insert`]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].replace(value)
        } else {
            self.hash_map.insert(key, value)
        }
    }

    /// Returns true if the map contains no elements. Checks both the lookup table and the hashmap. Note, there is no
    /// tracking in the lookup table - in the worst case, we have to check all elements of the lookup table.
    ///
    ///  Analogous to [`HashMap::is_empty`]
    pub fn is_empty(&self) -> bool {
        self.hash_map.is_empty() && !self.table.iter().any(|&x| x.is_some())
    }

    /// Modify the values at location `key` by calling `f` on its value. If no value present, create a new value set to
    /// `default`.
    #[inline]
    pub fn modify_or_insert<F>(&mut self, key: K, f: F, default: V)
    where
        F: FnOnce(&mut V),
    {
        if Self::use_lookup_table(key) {
            let value = &mut self.table[key.key_index()];
            match value {
                Some(x) => f(x),
                None => *value = Some(default),
            }
        } else {
            self.hash_map.entry(key).and_modify(f).or_insert(default);
        }
    }

    /// Adds 1 to the value stored at location `key`. If the value is not present, the value 1 will be set at that
    /// location.
    ///
    /// *NOTE:* This method can only be called with values that implement `AddAssign`, like primitives. For `NonZero<T>`
    /// values use [`bump_non_zero`] - It uses the niche optimization for better performance.
    ///
    /// # Panics
    ///
    /// May panics if adding 1 results in overflow.
    #[inline]
    pub fn bump_int(&mut self, key: K)
    where
        V: std::ops::AddAssign<V> + num_traits::One + num_traits::Zero,
    {
        if Self::use_lookup_table(key) {
            *self.table[key.key_index()].get_or_insert(V::zero()) += V::one();
        } else {
            self.hash_map
                .entry(key)
                .and_modify(|counter| *counter += V::one())
                .or_insert(V::one());
        }
    }

    /// Adds 1 to the value stored at location `key`. If the value is not present, the value 1 will be set at that
    /// location. Uses the niche optimization for better performance with `Option<NonZero<T>>`.
    ///
    /// *NOTE:* This method can only be called with `NonZero<T>` values. For primitive values use [`bump_int`].
    ///
    /// # Panics
    ///
    /// Panics if adding 1 results in overflow.
    #[inline]
    pub fn bump_non_zero(&mut self, key: K)
    where
        V: NonZeroInt + bytemuck::PodInOption,
        <V as NonZeroInt>::UnderlyingType: std::ops::AddAssign<V::UnderlyingType>,
        <V as NonZeroInt>::UnderlyingType: bytemuck::Pod + PrimInt,
    {
        use num_traits::One;

        if Self::use_lookup_table(key) {
            *bytemuck::cast_mut::<Option<V>, V::UnderlyingType>(
                &mut self.table[key.key_index()],
            ) += V::UnderlyingType::one();
        } else {
            self.hash_map
                .entry(key)
                .and_modify(|counter| {
                    *counter = counter
                        .checked_add(V::UnderlyingType::one())
                        .expect("Addition should not overflow");
                })
                .or_insert(V::ONE);
        }
    }

    /// Gets the given key’s corresponding entry in the map for in-place manipulation.
    ///
    /// Analogous to [`HashMap::entry`]
    #[must_use]
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        if Self::use_lookup_table(key) {
            let value: &mut Option<V> = &mut self.table[key.key_index()];
            match value {
                Some(_) => {
                    Entry::<K, V>::Occupied(OccupiedEntry::Vec(OccupiedVecEntry { value, key }))
                }
                None => Entry::<K, V>::Vacant(VacantEntry::Vec(VacantVecEntry { value, key })),
            }
        } else {
            match self.hash_map.entry(key) {
                std::collections::hash_map::Entry::Occupied(base) => {
                    Entry::<K, V>::Occupied(OccupiedEntry::HashMap(OccupiedHashMapEntry { base }))
                }
                std::collections::hash_map::Entry::Vacant(base) => {
                    Entry::<K, V>::Vacant(VacantEntry::HashMap(VacantHashMapEntry { base }))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut mule_map_int = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
        mule_map_int.bump_int(10);
        mule_map_int.bump_int(10);
        assert_eq!(mule_map_int.get(10), Some(&2));

        let mut mule_map_non_zero = MuleMap::<u32, NonZero<i32>, fnv_rs::FnvBuildHasher>::default();

        mule_map_non_zero.bump_non_zero(10);
        mule_map_non_zero.bump_non_zero(10);
        assert_eq!(mule_map_non_zero.get(10), NonZero::<i32>::new(2).as_ref());
        mule_map_non_zero.bump_non_zero(999_999);
        mule_map_non_zero.bump_non_zero(999_999);
        assert_eq!(
            mule_map_non_zero.get(999_999),
            NonZero::<i32>::new(2).as_ref()
        );

        let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();

        mule_map.modify_or_insert(100, |x| *x += 10, 1);
        assert_eq!(mule_map.get(100), Some(&1));

        mule_map.modify_or_insert(100, |x| *x += 10, 1);
        assert_eq!(mule_map.get(100), Some(&11));
    }
}
