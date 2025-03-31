use entry::{
    Entry, OccupiedEntry, OccupiedHashMapEntry, OccupiedVecEntry, VacantEntry, VacantHashMapEntry,
    VacantVecEntry,
};
use key::Key;
use key::PrimInt;
use sealed::sealed;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::BuildHasher;
use std::num::NonZero;
use std::ops::AddAssign;

pub(crate) mod entry;
pub(crate) mod iterators;
mod key;

#[sealed]
#[doc(hidden)]
pub trait NonZeroInt {
    type UnderlyingType;
    const ONE: Self;
    #[inline]
    fn checked_add(self, other: Self::UnderlyingType) -> Option<Self>
    where
        Self::UnderlyingType: bytemuck::Pod,
        Self::UnderlyingType: AddAssign<Self::UnderlyingType>,
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
/// ## Differences between [`HashMap`] and [`MuleMap`]
///
/// - **The key, `K`, must be an integer type.** - The key is directly mapped to the index in the lookup, so it must be
///     an integer.
/// - **The key, `K`, is passed by value** - Because it is a primitive integer type.
/// - **The hash builder, `S`,  does not have a default** - You must specify your hash builder. The assumption being
///     that if you need better performance you will likely also want to use a custom hash function.
/// - **`TABLE_MIN_VALUE` and `TABLE_SIZE`** -  If a key is between `TABLE_MIN_VALUE` and `TABLE_MIN_VALUE +
///     TABLE_SIZE` (exclusive), then the value will be stored directly in the lookup table, instead of using the `HashMap`.
///     **NOTE:** Currently the type of a const generic can’t depend on another generic type argument, so
///     `TABLE_MIN_VALUE` can’t use the same type as the key. Because of this, We are using [`i128`], but that means we
///     can’t represent values near [`u128::MAX`]. Hopefully having frequent keys near [`u128::MAX`] is extremely rare.
///
/// ## Performance
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
/// assert_eq!(mule_map_non_zero.get(10), NonZero::<i32>::new(2).as_ref());
/// assert_eq!(mule_map_non_zero.get(999_999),NonZero::<i32>::new(2).as_ref());
/// ```
#[derive(Debug, Clone)]
pub struct MuleMap<
    K,
    V,
    S,
    const TABLE_MIN_VALUE: i128 = 0,
    const TABLE_SIZE: usize = { u8::MAX as usize + 1 },
> {
    hash_map: HashMap<K, V, S>,
    table: [Option<V>; TABLE_SIZE],
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Default
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: Default + BuildHasher,
    <K as TryFrom<i128>>::Error: Debug,
{
    /// Creates an empty [`MuleMap`].
    ///
    /// # Example
    ///
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, Hash>::default();
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::default`]
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> PartialEq
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    V: PartialEq,
    S: BuildHasher,
{
    /// Tests for `self` and `other` values to be equal, and is used by `==`.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map1 = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map1.bump_int(10);
    /// mule_map1.bump_int(11);
    /// mule_map1.bump_int(999_999);
    /// mule_map1.bump_int(999_999);
    ///
    /// let mut mule_map2 = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map2.bump_int(10);
    /// mule_map2.bump_int(11);
    /// mule_map2.bump_int(999_999);
    /// mule_map2.bump_int(999_999);
    ///
    /// assert!(mule_map1 ==  mule_map2)
    /// ```
    fn eq(&self, other: &MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>) -> bool {
        self.hash_map == other.hash_map && self.table == other.table
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Eq
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    V: Eq,
    S: BuildHasher,
{
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::ops::Index<K>
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    /// assert_eq!(mule_map[10], 1);
    /// assert_eq!(mule_map[999_999], 1);
    /// assert!(test_utils::catch_unwind_silent(|| mule_map[123]).is_err());
    ///
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `MuleMap`.
    #[inline]
    fn index(&self, key: K) -> &V {
        self.get(key).expect("No entry found for key")
    }
}

impl<'a, K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Extend<(K, &'a V)>
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: Default + BuildHasher,
    V: Copy,
{
    /// Extends a collection with the contents of an iterator.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.extend([(0, &10), (999_999, &3)].into_iter());
    ///
    /// let mut mule_map2 = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map2.insert(0, 10);
    /// mule_map2.insert(999_999, 3);
    /// assert_eq!(mule_map, mule_map2);
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (K, &'a V)>>(&mut self, iter: T) {
        for (key, val) in iter {
            self.insert(key, *val);
        }
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Extend<(K, V)>
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    /// Extends a collection with the contents of an iterator.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.extend([(0, 10), (999_999, 3)].into_iter());
    ///
    /// let mut mule_map2 = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map2.insert(0, 10);
    /// mule_map2.insert(999_999, 3);
    /// assert_eq!(mule_map, mule_map2);
    /// ```
    #[inline]
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (key, val) in iter {
            self.insert(key, val);
        }
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize, const N: usize>
    From<[(K, V); N]> for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher + Default,
    <K as TryFrom<i128>>::Error: Debug,
{
    /// Converts a `[(K, V); N]` into a `MuleMap<K, V>`.
    ///
    /// If any entries in the array have equal keys,
    /// all but one of the corresponding values will be dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(3,4);
    ///
    /// let map1 = MuleMap::<_, _, fnv_rs::FnvBuildHasher>::from([(1, 2), (3, 4)]);
    /// let map2: MuleMap<_, _, fnv_rs::FnvBuildHasher> = [(1, 2), (3, 4)].into();
    ///
    /// assert_eq!(map1, mule_map);
    /// assert_eq!(map2, mule_map);
    /// ```
    fn from(arr: [(K, V); N]) -> Self {
        let mut map = Self::default();
        for (key, val) in arr {
            map.insert(key, val);
        }
        map
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> FromIterator<(K, V)>
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher + Default,
    <K as TryFrom<i128>>::Error: Debug,
{
    /// Constructs a `MuleMap<K, V>` from an iterator of key-value pairs.
    ///
    /// If the iterator produces any pairs with equal keys,
    /// all but one of the corresponding values will be dropped.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(3,4);
    ///
    /// let map1 = MuleMap::<_, _, fnv_rs::FnvBuildHasher>::from_iter([(1, 2), (3, 4)].into_iter());
    ///
    /// assert_eq!(map1, mule_map);
    /// ```
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::default();
        map.extend(iter);
        map
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    // Hard limit, way beyond practical lookup table size. This makes it easier to calculate the key index
    const STATIC_ASSERT_LIMIT_SIZE_TO_I32_MAX: () =
        assert!((TABLE_SIZE as u128) <= i32::MAX as u128 + 1);

    // NOTE: using `saturating_sub` to allow for when `TABLE_SIZE == 0`
    const STATIC_ASSERT_SIZE_FITS_I128: () = assert!(
        TABLE_MIN_VALUE
            .checked_add(const { TABLE_SIZE.saturating_sub(1) as i128 })
            .is_some()
    );

    const STATIC_ASSERT_ISIZE_FITS_I32: () = assert!(isize::MAX as u128 >= i32::MAX as u128);

    #[inline]
    #[must_use]
    pub(crate) fn use_lookup_table(key: K) -> bool {
        if const { TABLE_SIZE == 0 } {
            return false;
        }

        let promoted_sum = K::add_promoted(
            K::i128_as_promoted(TABLE_MIN_VALUE),
            K::usize_as_promoted(const { TABLE_SIZE.saturating_sub(1) }),
        );

        // NOTE: `TABLE_MIN_VALUE + TABLE_SIZE - 1` and TABLE_MIN_VALUE must fit into a key type, K (with correct
        // promotion during add for signed ints)
        key <= promoted_sum && key >= K::i128_as_k(TABLE_MIN_VALUE)
    }

    #[inline]
    pub(crate) fn check_bounds()
    where
        <K as TryFrom<i128>>::Error: Debug,
    {
        let () = Self::STATIC_ASSERT_LIMIT_SIZE_TO_I32_MAX;
        let () = Self::STATIC_ASSERT_SIZE_FITS_I128;
        let () = Self::STATIC_ASSERT_ISIZE_FITS_I32;

        // NOTE: using `saturating_sub` to allow for when `TABLE_SIZE == 0`
        // `TABLE_MIN_VALUE + TABLE_SIZE - 1` must fit in i128, because of `STATIC_ASSERT_SIZE_FITS_I128`
        <i128 as TryInto<K>>::try_into(
            TABLE_MIN_VALUE + const { TABLE_SIZE.saturating_sub(1) } as i128,
        )
        .unwrap_or_else(|_| {
            panic!(
                "TABLE_MIN_VALUE ({TABLE_MIN_VALUE:?}) + TABLE_SIZE ({TABLE_SIZE:?}) should fit into key type, K"
            )
        });

        <i128 as TryInto<K>>::try_into(TABLE_MIN_VALUE)
            .expect("TABLE_MIN_VALUE should fit into key type, K");
    }

    /// Creates an empty [`MuleMap`].
    ///
    /// # Example
    ///
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, Hash>::new();
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::new`]
    #[must_use]
    #[inline]
    pub fn new() -> Self
    where
        S: Default,
        <K as TryFrom<i128>>::Error: Debug,
    {
        Self::with_capacity_and_hasher(0, S::default())
    }

    /// Creates an empty [`MuleMap`] with at least the provided capacity.
    ///
    /// # Example
    ///
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, Hash>::with_capacity(100);
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::with_capacity`]
    #[must_use]
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self
    where
        S: Default,
        <K as TryFrom<i128>>::Error: Debug,
    {
        Self::with_capacity_and_hasher(capacity, S::default())
    }

    /// Creates an empty [`MuleMap`] using `hash_builder`.
    ///
    /// # Example
    ///
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, Hash>::with_hasher(Hash::default());
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// See: [`MuleMap::with_capacity_and_hasher`]
    ///
    /// Analogous to [`HashMap::with_hasher`]
    #[must_use]
    #[inline]
    pub fn with_hasher(hash_builder: S) -> Self
    where
        <K as TryFrom<i128>>::Error: Debug,
    {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

    /// Creates an empty [`MuleMap`] with at least the provided capacity and using `hash_builder`.
    ///
    /// # Example
    ///
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, Hash>::with_capacity_and_hasher(100, Hash::default());
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if
    ///  - `TABLE_MIN_VALUE` or `TABLE_MIN_VALUE + TABLE_SIZE - 1` doesn't fit into key type, `K`.
    ///
    /// Analogous to [`HashMap::with_capacity_and_hasher`]
    #[must_use]
    #[inline]
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self
    where
        <K as TryFrom<i128>>::Error: Debug,
    {
        Self::check_bounds();

        MuleMap::<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE> {
            hash_map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            table: [const { None }; TABLE_SIZE],
        }
    }

    /// Returns capacity of the underlying hash map.
    ///
    /// # Example
    ///
    /// ```
    /// type Hash = fnv_rs::FnvBuildHasher;
    /// let mule_map = mule_map::MuleMap::<u32, usize, Hash>::with_capacity(100);
    /// assert!(mule_map.capacity() >= 100);
    /// ```
    ///
    /// See [`HashMap::capacity`]
    #[must_use]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.hash_map.capacity()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory for reuse.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(999_999,4);
    /// mule_map.clear();
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// See [`HashMap::clear`]
    #[inline]
    pub fn clear(&mut self) {
        self.hash_map.clear();
        self.table = [const { None }; TABLE_SIZE];
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(999_999,4);
    /// assert!(mule_map.contains_key(999_999));
    /// assert!(mule_map.contains_key(1));
    /// assert!(!mule_map.contains_key(2));
    /// assert!(!mule_map.contains_key(999_998));
    /// ```
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
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.get(999_999), Some(&4));
    /// assert_eq!(mule_map.get(1), Some(&2));
    /// assert_eq!(mule_map.get(2), None);
    /// assert_eq!(mule_map.get(999_998), None);
    /// ```
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
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.get_key_value(999_999), Some((999_999, &4)));
    /// assert_eq!(mule_map.get_key_value(1), Some((1,&2)));
    /// assert_eq!(mule_map.get_key_value(2), None);
    /// assert_eq!(mule_map.get_key_value(999_998), None);
    /// ```
    ///
    /// Analogous to [`HashMap::get_key_value`]
    #[must_use]
    #[inline]
    pub fn get_key_value(&self, key: K) -> Option<(K, &V)> {
        let result = Some(key);
        result.zip(self.get(key))
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.get_mut(999_999), Some(&mut 4));
    /// assert_eq!(mule_map.get_mut(1), Some(&mut 2));
    /// assert_eq!(mule_map.get_mut(2), None);
    /// assert_eq!(mule_map.get_mut(999_998), None);
    /// ```
    ///
    /// Analogous to [`HashMap::get_mut`]
    #[must_use]
    #[inline]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].as_mut()
        } else {
            self.hash_map.get_mut(&key)
        }
    }

    /// Returns a reference to the map’s [`BuildHasher`].
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// assert_eq!(&fnv_rs::FnvBuildHasher::default(), mule_map.hasher());
    /// ```
    ///
    /// Analogous to [`HashMap::hasher`]
    #[must_use]
    #[inline]
    pub fn hasher(&self) -> &S {
        self.hash_map.hasher()
    }

    /// Inserts a key-value pair into the map. If the map did not have this key present, None is returned. If the map
    /// did have this key present, the value is updated, and the old value is returned.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.get_key_value(999_999), Some((999_999, &4)));
    /// assert_eq!(mule_map.get_key_value(1), Some((1,&2)));
    /// assert_eq!(mule_map.get_key_value(2), None);
    /// assert_eq!(mule_map.get_key_value(999_998), None);
    /// ```
    ///
    /// Analogous to [`HashMap::insert`]
    #[inline]
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
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// assert!(mule_map.is_empty());
    /// mule_map.insert(1,2);
    /// assert!(!mule_map.is_empty());
    /// mule_map.clear();
    /// assert!(mule_map.is_empty());
    /// mule_map.insert(999_999,4);
    /// assert!(!mule_map.is_empty());
    /// mule_map.clear();
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    ///  Analogous to [`HashMap::is_empty`]
    #[must_use]
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.hash_map.is_empty() && !self.table.iter().any(Option::is_some)
    }

    /// Returns the number of elements in the map. Checks both the lookup table and the hashmap. Note, there is no
    /// tracking in the lookup table, so this will scan the whole table.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// assert_eq!(mule_map.len(), 0);
    /// mule_map.insert(1,2);
    /// assert_eq!(mule_map.len(), 1);
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.len(), 2);
    /// mule_map.clear();
    /// assert_eq!(mule_map.len(), 0);
    /// ```
    ///
    ///  Analogous to [`HashMap::len`]
    #[must_use]
    #[inline]
    pub fn len(&self) -> usize {
        self.hash_map.len() + self.table.iter().filter(|&x| x.is_some()).count()
    }

    /// Removes a key from the map, returning the value at the key if the key was previously in the map.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// assert_eq!(mule_map.remove(0), None);
    /// assert!(!mule_map.is_empty());
    /// assert_eq!(mule_map.remove(1), Some(2));
    /// assert!(mule_map.is_empty());
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.remove(999_999), Some(4));
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    ///  Analogous to [`HashMap::remove`]
    #[inline]
    pub fn remove(&mut self, key: K) -> Option<V> {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].take()
        } else {
            self.hash_map.remove(&key)
        }
    }

    /// Removes a key from the map, returning the stored key and value if the key was previously in the map.
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.insert(1,2);
    /// assert_eq!(mule_map.remove_entry(0), None);
    /// assert!(!mule_map.is_empty());
    /// assert_eq!(mule_map.remove_entry(1), Some((1, 2)));
    /// assert!(mule_map.is_empty());
    /// mule_map.insert(999_999,4);
    /// assert_eq!(mule_map.remove_entry(999_999), Some((999_999,4)));
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    ///  Analogous to [`HashMap::remove_entry`]
    #[inline]
    pub fn remove_entry(&mut self, key: K) -> Option<(K, V)> {
        if Self::use_lookup_table(key) {
            let result = Some(key);
            result.zip(self.table[key.key_index()].take())
        } else {
            self.hash_map.remove_entry(&key)
        }
    }

    /// Calls `reserve` on the underlying [`HashMap`]
    ///
    /// # Example
    ///
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.reserve(100);
    /// ```
    ///
    ///  Analogous to [`HashMap::reserve`]
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.hash_map.reserve(additional);
    }

    /// Calls `shrink_to` on the underlying [`HashMap`]
    ///
    /// # Example
    ///
    /// ```
    /// let mut map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::with_capacity(100);
    /// map.insert(999_999, 2);
    /// map.insert(999_998, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// ```
    ///
    ///  Analogous to [`HashMap::shrink_to`]
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.hash_map.shrink_to(min_capacity);
    }

    /// Calls `shrink_to_fit` on the underlying [`HashMap`]
    ///
    /// # Example
    ///
    /// ```
    /// let mut map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::with_capacity(100);
    /// map.insert(999_999, 2);
    /// map.insert(999_998, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    ///
    ///  Analogous to [`HashMap::shrink_to_fit`]
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.hash_map.shrink_to_fit();
    }

    /// Calls `try_reserve` on the underlying [`HashMap`]
    ///
    ///
    /// # Example
    ///
    /// ```
    /// let mut map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::new();
    /// map.try_reserve(10).expect("Should have space to allocate 10 elements");
    /// ```
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    ///  Analogous to [`HashMap::try_reserve`]
    #[inline]
    pub fn try_reserve(
        &mut self,
        additional: usize,
    ) -> Result<(), std::collections::TryReserveError> {
        self.hash_map.try_reserve(additional)
    }

    /// Modify the values at location `key` by calling `f` on its value. If no value present, create a new value set to
    /// `default`.
    ///
    /// # Example
    ///
    /// ```
    /// let mut map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::new();
    /// map.modify_or_insert(10, |x| *x += 1, 100);
    /// assert!(map.get(10) == Some(&100));
    /// map.modify_or_insert(10, |x| *x += 1, 100);
    /// assert!(map.get(10) == Some(&101));
    /// map.modify_or_insert(999_999, |x| *x += 1, 100);
    /// assert!(map.get(999_999) == Some(&100));
    /// map.modify_or_insert(999_999, |x| *x += 1, 100);
    /// assert!(map.get(999_999) == Some(&101));
    /// ```
    ///
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
    /// values use [`MuleMap::bump_non_zero`] - It uses the niche optimization for better performance.
    ///
    /// # Example
    ///
    /// ```
    /// let mut map = mule_map::MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::new();
    /// map.bump_int(10);
    /// assert!(map.get(10) == Some(&1));
    /// map.bump_int(10);
    /// assert!(map.get(10) == Some(&2));
    /// map.bump_int(999_999);
    /// assert!(map.get(999_999) == Some(&1));
    /// map.bump_int(999_999);
    /// assert!(map.get(999_999) == Some(&2));
    /// ```
    ///
    /// # Panics
    ///
    /// May panics if adding 1 results in overflow.
    #[inline]
    pub fn bump_int(&mut self, key: K)
    where
        V: AddAssign<V> + num_traits::One + num_traits::Zero,
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
    /// *NOTE:* This method can only be called with `NonZero<T>` values. For primitive values use [`MuleMap::bump_int`].
    ///
    /// # Example
    ///
    /// ```
    /// use std::num::NonZero;
    /// let mut map = mule_map::MuleMap::<u32, NonZero<i32>, fnv_rs::FnvBuildHasher>::new();
    /// map.bump_non_zero(10);
    ///
    /// assert!(map.get(10) == Some(&const { NonZero::new(1).expect("1 is not 0") }));
    /// map.bump_non_zero(10);
    /// assert!(map.get(10) == Some(&const { NonZero::new(2).expect("2 is not 0") }));
    /// map.bump_non_zero(999_999);
    /// assert!(map.get(999_999) == Some(&const { NonZero::new(1).expect("1 is not 0") }));
    /// map.bump_non_zero(999_999);
    /// assert!(map.get(999_999) == Some(&const { NonZero::new(2).expect("2 is not 0") }));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if adding 1 results in overflow.
    #[inline]
    pub fn bump_non_zero(&mut self, key: K)
    where
        V: NonZeroInt + bytemuck::PodInOption,
        <V as NonZeroInt>::UnderlyingType: AddAssign<V::UnderlyingType>,
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
    /// # Example
    ///
    /// ```
    /// let mut map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// map.entry(5).or_insert(3);
    /// assert!(map.get(5) == Some(&3));
    /// map.entry(5).and_modify(|e| *e += 1).or_insert(1);
    /// assert!(map.get(5) == Some(&4));
    /// ```
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
    fn use_lookup_table() {
        type DefaultRange = MuleMap<i32, i32, fnv_rs::FnvBuildHasher, 0, { u8::MAX as usize + 1 }>;
        type NegRange = MuleMap<i32, i32, fnv_rs::FnvBuildHasher, -100, { u8::MAX as usize + 1 }>;
        type ZeroSize = MuleMap<i32, i32, fnv_rs::FnvBuildHasher, 0, { u8::MIN as usize }>;

        assert!(DefaultRange::use_lookup_table(0));
        assert!(!DefaultRange::use_lookup_table(-1));
        assert!(DefaultRange::use_lookup_table(255));
        assert!(!DefaultRange::use_lookup_table(256));

        assert!(NegRange::use_lookup_table(-100));
        assert!(!NegRange::use_lookup_table(-101));
        assert!(NegRange::use_lookup_table(155));
        assert!(!NegRange::use_lookup_table(156));

        assert!(!ZeroSize::use_lookup_table(0));
        assert!(!ZeroSize::use_lookup_table(1));
    }
    #[test]
    fn check_table_range() {
        type BadRange = MuleMap<u8, i32, fnv_rs::FnvBuildHasher, 0, { u8::MAX as usize + 2 }>;
        type BadRange2 = MuleMap<u8, i32, fnv_rs::FnvBuildHasher, -1, { u8::MAX as usize }>;
        type OkRange = MuleMap<u8, i32, fnv_rs::FnvBuildHasher, 0, { u8::MAX as usize + 1 }>;
        type OkRange2 = MuleMap<u8, i32, fnv_rs::FnvBuildHasher, 1, { u8::MAX as usize }>;
        type ZeroSize = MuleMap<u8, i32, fnv_rs::FnvBuildHasher, 0, { u8::MIN as usize }>;

        assert!(test_utils::catch_unwind_silent(BadRange::new).is_err());
        assert!(test_utils::catch_unwind_silent(BadRange2::new).is_err());
        assert!(test_utils::catch_unwind_silent(OkRange::new).is_ok());
        assert!(test_utils::catch_unwind_silent(OkRange2::new).is_ok());
        assert!(test_utils::catch_unwind_silent(ZeroSize::new).is_ok());
    }
}
