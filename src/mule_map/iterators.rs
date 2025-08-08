use crate::MuleMap;
use crate::mule_map::Key;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::BuildHasher;
use std::iter::Enumerate;
use std::iter::FilterMap;

#[must_use]
#[inline]
fn key_from_index<K, const TABLE_MIN_VALUE: i128>(index: usize) -> K
where
    K: Key<TABLE_MIN_VALUE>,
{
    K::add_promoted(
        K::i128_as_promoted(TABLE_MIN_VALUE),
        K::usize_as_promoted(index),
    )
}

// MuleMapIter

type IterLeftSide<'a, K, V> =
    std::iter::Map<std::collections::hash_map::Iter<'a, K, V>, fn((&'a K, &'a V)) -> (K, &'a V)>;

type IterRightSide<'a, K, V> = FilterMap<
    Enumerate<std::slice::Iter<'a, Option<V>>>,
    fn((usize, &'a Option<V>)) -> Option<(K, &'a V)>,
>;

#[inline]
#[must_use]
fn map_fn<'a, K, V>((key, val): (&'a K, &'a V)) -> (K, &'a V)
where
    K: Copy,
{
    (*key, val)
}

#[inline]
#[must_use]
fn filter_map_fn<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &Option<V>),
) -> Option<(K, &V)>
where
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.as_ref())
}

/// An iterator over the entries of a [`MuleMap`].
#[derive(Debug, Clone)]
pub struct Iter<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<IterLeftSide<'a, K, V>, IterRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    Iter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: &'a HashMap<K, V, S>,
        table: &'a [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        type MapFn<'a, K, V> = fn((&'a K, &'a V)) -> (K, &'a V);
        type FilterMapFn<'a, K, V> = fn((usize, &Option<V>)) -> Option<(K, &V)>;

        let left_iter: std::iter::Map<_, MapFn<'a, K, V>> = hash_map
            .iter()
            .map(map_fn as fn((&'a K, &'a V)) -> (K, &'a V));
        let right_iter: FilterMap<_, FilterMapFn<'a, K, V>> = table.iter().enumerate().filter_map(
            filter_map_fn::<K, V, TABLE_MIN_VALUE> as fn((usize, &Option<V>)) -> Option<(K, &V)>,
        );

        Iter {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for Iter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, &'a V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for Iter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// MuleMapIterMut

type IterMutLeftSide<'a, K, V> = std::iter::Map<
    std::collections::hash_map::IterMut<'a, K, V>,
    fn((&'a K, &'a mut V)) -> (K, &'a mut V),
>;

type IterMutRightSide<'a, K, V> = FilterMap<
    Enumerate<std::slice::IterMut<'a, Option<V>>>,
    fn((usize, &'a mut Option<V>)) -> Option<(K, &'a mut V)>,
>;

#[inline]
#[must_use]
fn map_fn_mut<'a, K, V>((key, val): (&'a K, &'a mut V)) -> (K, &'a mut V)
where
    K: Copy,
{
    (*key, val)
}

#[inline]
#[must_use]
fn filter_map_fn_mut<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &mut Option<V>),
) -> Option<(K, &mut V)>
where
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.as_mut())
}

/// A mutable iterator over the entries of a [`MuleMap`].
#[derive(Debug)]
pub struct IterMut<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<IterMutLeftSide<'a, K, V>, IterMutRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    IterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: &'a mut HashMap<K, V, S>,
        table: &'a mut [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        type MapFn<'a, K, V> = fn((&'a K, &'a mut V)) -> (K, &'a mut V);
        type FilterMapFn<'a, K, V> = fn((usize, &mut Option<V>)) -> Option<(K, &mut V)>;

        let left_iter: std::iter::Map<_, MapFn<'a, K, V>> = hash_map
            .iter_mut()
            .map(map_fn_mut as fn((&'a K, &'a mut V)) -> (K, &'a mut V));
        let right_iter: FilterMap<_, FilterMapFn<'a, K, V>> =
            table.iter_mut().enumerate().filter_map(
                filter_map_fn_mut::<K, V, TABLE_MIN_VALUE>
                    as fn((usize, &mut Option<V>)) -> Option<(K, &mut V)>,
            );

        IterMut {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for IterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for IterMut<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// MuleMapIntoIter

type IntoIterRightSide<K, V, const TABLE_SIZE: usize> = FilterMap<
    Enumerate<std::array::IntoIter<Option<V>, TABLE_SIZE>>,
    fn((usize, Option<V>)) -> Option<(K, V)>,
>;

#[inline]
#[must_use]
fn filter_map_fn_into<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, Option<V>),
) -> Option<(K, V)>
where
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value)
}

/// An owning iterator over the entries of a [`MuleMap`].
#[derive(Debug)]
pub struct IntoIter<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<
        std::collections::hash_map::IntoIter<K, V>,
        IntoIterRightSide<K, V, TABLE_SIZE>,
    >,
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    IntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
    #[inline]
    fn from_hash_map_and_table<S>(
        hash_map: HashMap<K, V, S>,
        table: [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        type FilterMapFn<K, V> = fn((usize, Option<V>)) -> Option<(K, V)>;

        let left_iter: std::collections::hash_map::IntoIter<K, V> = hash_map.into_iter();
        let right_iter: FilterMap<_, FilterMapFn<K, V>> = table.into_iter().enumerate().filter_map(
            filter_map_fn_into::<K, V, TABLE_MIN_VALUE> as fn((usize, Option<V>)) -> Option<(K, V)>,
        );

        IntoIter {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for IntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for IntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// Drain

type DrainIterRightSide<'a, K, V, const TABLE_SIZE: usize> = FilterMap<
    Enumerate<std::slice::IterMut<'a, Option<V>>>,
    fn((usize, &mut Option<V>)) -> Option<(K, V)>,
>;

#[inline]
#[must_use]
fn filter_map_fn_drain<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &mut Option<V>),
) -> Option<(K, V)>
where
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.take())
}

/// An draining iterator over the entries of a [`MuleMap`].
#[derive(Debug)]
pub struct DrainIter<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<
        std::collections::hash_map::Drain<'a, K, V>,
        DrainIterRightSide<'a, K, V, TABLE_SIZE>,
    >,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    DrainIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: &'a mut HashMap<K, V, S>,
        table: &'a mut [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        type FilterMapFn<K, V> = fn((usize, &mut Option<V>)) -> Option<(K, V)>;

        let left_iter = hash_map.drain();

        let right_iter: FilterMap<_, FilterMapFn<K, V>> = table.iter_mut().enumerate().filter_map(
            filter_map_fn_drain::<K, V, TABLE_MIN_VALUE>
                as fn((usize, &mut Option<V>)) -> Option<(K, V)>,
        );
        Self {
            // Note: Can't hold a `&mut` to both table and iter in `MuleMapDrainIter`, but we need to be sure to consume
            // all of the elements so that the original `MuleMap` is empty after dropped. We could have used an owned
            // table, but that would have made an extra copy. This could be made more efficient using unsafe.
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Drop
    for DrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    #[inline]
    fn drop(&mut self) {
        for _ in &mut self.iter {}
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for DrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for DrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// Keys

type KeysLeftSide<'a, K, V> =
    std::iter::Map<std::collections::hash_map::Keys<'a, K, V>, fn(&'a K) -> K>;

type KeysRightSide<'a, K, V> =
    FilterMap<Enumerate<std::slice::Iter<'a, Option<V>>>, fn((usize, &'a Option<V>)) -> Option<K>>;

#[inline]
#[must_use]
fn map_fn_keys<K>(key: &K) -> K
where
    K: Copy,
{
    *key
}

#[inline]
#[must_use]
fn filter_map_fn_keys<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &Option<V>),
) -> Option<K>
where
    K: Key<TABLE_MIN_VALUE>,
{
    value
        .as_ref()
        .map(|_| key_from_index::<K, TABLE_MIN_VALUE>(index))
}

/// An iterator over the keys of a [`MuleMap`].
#[derive(Debug, Clone)]
pub struct Keys<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<KeysLeftSide<'a, K, V>, KeysRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    Keys<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: &'a HashMap<K, V, S>,
        table: &'a [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        type MapFn<'a, K> = fn(&'a K) -> K;
        type FilterMapFn<'a, K, V> = fn((usize, &Option<V>)) -> Option<K>;

        let left_iter: std::iter::Map<_, MapFn<'a, K>> =
            hash_map.keys().map(map_fn_keys as fn(&'a K) -> K);
        let right_iter: FilterMap<_, FilterMapFn<'a, K, V>> = table.iter().enumerate().filter_map(
            filter_map_fn_keys::<K, V, TABLE_MIN_VALUE> as fn((usize, &Option<V>)) -> Option<K>,
        );

        Keys {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for Keys<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for Keys<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// IntoKeys

/// An owning iterator over the keys of a [`MuleMap`].
#[derive(Debug)]
pub struct IntoKeys<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<std::collections::hash_map::IntoKeys<K, V>, std::vec::IntoIter<K>>,
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    IntoKeys<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: HashMap<K, V, S>,
        table: &[Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        let left_iter = hash_map.into_keys();

        let table_keys: Vec<K> = table
            .iter()
            .enumerate()
            .filter_map(
                filter_map_fn_keys::<K, V, TABLE_MIN_VALUE> as fn((usize, &Option<V>)) -> Option<K>,
            )
            .collect();

        IntoKeys {
            iter: left_iter.chain(table_keys),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for IntoKeys<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = K;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for IntoKeys<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// Values

type ValuesRightSide<'a, V> =
    FilterMap<std::slice::Iter<'a, Option<V>>, fn(&Option<V>) -> Option<&V>>;

#[inline]
#[must_use]
#[allow(clippy::ref_option)]
fn filter_map_fn_values<V, const TABLE_MIN_VALUE: i128>(value: &Option<V>) -> Option<&V> {
    value.as_ref()
}

/// An iterator over the values of a [`MuleMap`].
#[derive(Debug, Clone)]
pub struct Values<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<std::collections::hash_map::Values<'a, K, V>, ValuesRightSide<'a, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    Values<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: &'a HashMap<K, V, S>,
        table: &'a [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        let left_iter = hash_map.values();
        let right_iter = table
            .iter()
            .filter_map(filter_map_fn_values::<V, TABLE_MIN_VALUE> as fn(&Option<V>) -> Option<&V>);

        Values {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for Values<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for Values<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// ValuesMut

type ValuesMutRightSide<'a, V> =
    FilterMap<std::slice::IterMut<'a, Option<V>>, fn(&mut Option<V>) -> Option<&mut V>>;

#[inline]
#[must_use]
fn filter_map_fn_values_mut<V, const TABLE_MIN_VALUE: i128>(
    value: &mut Option<V>,
) -> Option<&mut V>
where
{
    value.as_mut()
}

/// A mutable iterator over the values of a [`MuleMap`].
#[derive(Debug)]
pub struct ValuesMut<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<
        std::collections::hash_map::ValuesMut<'a, K, V>,
        ValuesMutRightSide<'a, V>,
    >,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    ValuesMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: &'a mut HashMap<K, V, S>,
        table: &'a mut [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        let left_iter = hash_map.values_mut();
        let right_iter = table.iter_mut().filter_map(
            filter_map_fn_values_mut::<V, TABLE_MIN_VALUE> as fn(&mut Option<V>) -> Option<&mut V>,
        );

        ValuesMut {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for ValuesMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = &'a mut V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for ValuesMut<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// IntoValues

type IntoValuesRightSide<V, const TABLE_SIZE: usize> =
    FilterMap<std::array::IntoIter<Option<V>, TABLE_SIZE>, fn(Option<V>) -> Option<V>>;

#[inline]
#[must_use]
fn filter_map_fn_into_values<V, const TABLE_MIN_VALUE: i128>(value: Option<V>) -> Option<V>
where
{
    value
}

/// An owning iterator over the values of a [`MuleMap`].
#[derive(Debug)]
pub struct IntoValues<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<
        std::collections::hash_map::IntoValues<K, V>,
        IntoValuesRightSide<V, TABLE_SIZE>,
    >,
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    IntoValues<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    #[inline]
    #[must_use]
    fn from_hash_map_and_table<S>(
        hash_map: HashMap<K, V, S>,
        table: [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: BuildHasher,
    {
        let left_iter = hash_map.into_values();
        let right_iter = table.into_iter().filter_map(
            filter_map_fn_into_values::<V, TABLE_MIN_VALUE> as fn(Option<V>) -> Option<V>,
        );

        IntoValues {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for IntoValues<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = V;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> std::iter::FusedIterator
    for IntoValues<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
}

// MuleMap

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    /// An iterator visiting all key-value pairs in arbitrary order. The iterator element type is `(K, &'a V)`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for (key, value) in mule_map.iter()
    /// {
    ///     assert!((key == 10 && *value == 2) || (key == 999_999 && *value == 1));
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    /// Analogous to [`HashMap::iter`]
    #[inline]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        Iter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    /// A mutable iterator visiting all key-value pairs in arbitrary order. The iterator element type is `(K, &'a mut V)`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for (key, value) in mule_map.iter_mut()
    /// {
    ///     *value *= 2;
    ///     assert!((key == 10 && *value == 4) || (key == 999_999 && *value == 2));
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    /// Analogous to [`HashMap::iter_mut`]
    #[inline]
    #[must_use]
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IterMut::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the allocated memory for reuse. If the
    /// returned iterator is dropped before being fully consumed, it drops the remaining key-value pairs. The returned
    /// iterator keeps a mutable borrow on the map to optimize its implementation.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// for (key, value)  in mule_map.drain().take(1) {
    ///     assert!((key == 10 && value == 2) || (key == 999_999 && value == 1));
    /// }
    /// assert!(mule_map.is_empty());
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    /// Analogous to [`HashMap::drain`]
    #[inline]
    #[must_use]
    pub fn drain(&mut self) -> DrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        DrainIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    /// An iterator visiting all keys in arbitrary order. The iterator element type is `K`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for key in mule_map.keys()
    /// {
    ///     assert!(key == 10 || key == 999_999);
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    /// Analogous to [`HashMap::keys`]
    #[inline]
    #[must_use]
    pub fn keys(&self) -> Keys<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        Keys::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    /// Creates a consuming iterator visiting all the keys in arbitrary order. The map cannot be used after calling
    /// this. The iterator element type is `K`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for key in mule_map.into_keys()
    /// {
    ///     assert!(key == 10 || key == 999_999);
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    /// Analogous to [`HashMap::into_keys`]
    #[inline]
    #[must_use]
    pub fn into_keys(self) -> IntoKeys<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IntoKeys::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            self.hash_map,
            &self.table,
        )
    }

    /// Creates an iterator visiting all the values in arbitrary order. The iterator element type is `&'a V`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for val in mule_map.values()
    /// {
    ///     assert!(*val == 1 || *val == 2);
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    /// Analogous to [`HashMap::values`]
    #[inline]
    #[must_use]
    pub fn values(&self) -> Values<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        Values::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    /// Creates an iterator visiting all the values in arbitrary order. The iterator element type is `&'a mut V`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for val in mule_map.values_mut()
    /// {
    ///     *val *= 2;
    ///     assert!(*val == 2 || *val == 4);
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    ///  Analogous to [`HashMap::values_mut`]
    #[inline]
    #[must_use]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        ValuesMut::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    /// Creates an iterator consuming all the values in arbitrary order. The map cannot be used after calling this. The
    /// iterator element type is `V`.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// let mut count = 0;
    /// for val in mule_map.into_values()
    /// {
    ///     assert!(val == 1 || val == 2);
    ///     count += 1;
    /// }
    /// assert_eq!(count, 2);
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    ///  Analogous to [`HashMap::into_values`]
    #[inline]
    #[must_use]
    pub fn into_values(self) -> IntoValues<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IntoValues::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            self.hash_map,
            self.table,
        )
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs (k, v) for which f(&k, &mut v) returns false. The elements are visited in
    /// unsorted (and unspecified) order.
    ///
    /// # Example
    ///
    /// ```
    /// use mule_map::MuleMap;
    ///
    /// let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(10);
    /// mule_map.bump_int(999_999);
    ///
    /// mule_map.retain(|&k, _| k % 2 == 0);
    /// assert_eq!(mule_map.len(), 1);
    /// assert_eq!(mule_map.get(10), Some(&2));
    /// ```
    ///
    /// # Performance
    /// O(capacity of the [`HashMap`]) + O(`TABLE_SIZE` of the lookup table). Currently all `TABLE_SIZE` elements of the
    /// lookup table will be visited.
    ///
    ///  Analogous to [`HashMap::retain`]
    #[inline]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        for (index, value) in self.table.iter_mut().enumerate() {
            if let Some(x) = value
                && !f(&key_from_index::<K, TABLE_MIN_VALUE>(index), x)
            {
                *value = None;
            }
        }

        self.hash_map.retain(f);
    }
}

// IntoIterator
impl<'a, K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for &'a MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    type Item = (K, &'a V);
    type IntoIter = Iter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>;

    #[inline]
    fn into_iter(self) -> Iter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        self.iter()
    }
}

impl<'a, K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for &'a mut MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    type Item = (K, &'a mut V);
    type IntoIter = IterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>;

    #[inline]
    fn into_iter(self) -> IterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        self.iter_mut()
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
    S: BuildHasher,
{
    type Item = (K, V);
    type IntoIter = IntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IntoIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            self.hash_map,
            self.table,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_key_from_index() {
        macro_rules! check_key_from_index_small {
            (type=$prim_type:ty) => {
                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MIN as i128 }>(0),
                    <$prim_type>::MIN
                );

                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MIN as i128 }>(
                        (1 << (<$prim_type>::BITS + 1)) - 1
                    ),
                    <$prim_type>::MAX
                );

                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MAX as i128 }>(0),
                    <$prim_type>::MAX
                );

                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MAX as i128 / 2 }>(0),
                    <$prim_type>::MAX / 2
                );

                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MAX as i128 / 2 }>(
                        (<$prim_type>::MAX / 2) as usize + 1
                    ),
                    <$prim_type>::MAX
                );
            };
        }

        check_key_from_index_small!(type=u8);
        check_key_from_index_small!(type=u16);
        check_key_from_index_small!(type=i8);
        check_key_from_index_small!(type=i16);

        macro_rules! check_key_from_index_large {
            (type=$prim_type:ty) => {
                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MIN as i128 }>(0),
                    <$prim_type>::MIN
                );

                assert_eq!(
                    key_from_index::<$prim_type, { <$prim_type>::MIN as i128 }>(i32::MAX as usize),
                    (<$prim_type>::MIN as i128 + i32::MAX as i128) as $prim_type
                );

                {
                    const fn largest_table_min() -> i128 {
                        if (<$prim_type>::BITS == 128) {
                            return i128::MAX;
                        }
                        <$prim_type>::MAX as i128
                    }

                    assert_eq!(
                        key_from_index::<$prim_type, { largest_table_min() }>(0),
                        largest_table_min() as $prim_type
                    );

                    assert_eq!(
                        key_from_index::<$prim_type, { largest_table_min() - (i32::MAX as i128) }>(
                            0
                        ),
                        (largest_table_min() - (i32::MAX as i128)) as $prim_type
                    );

                    assert_eq!(
                        key_from_index::<$prim_type, { largest_table_min() - (i32::MAX as i128) }>(
                            i32::MAX as usize
                        ),
                        largest_table_min() as $prim_type
                    );
                }
            };
        }

        #[allow(clippy::cast_lossless)]
        #[allow(clippy::cast_possible_wrap)]
        #[allow(clippy::cast_possible_truncation)]
        #[allow(clippy::cast_sign_loss)]
        {
            check_key_from_index_large!(type=u32);
            check_key_from_index_large!(type=u64);
            check_key_from_index_large!(type=u128);
            check_key_from_index_large!(type=usize);

            check_key_from_index_large!(type=i32);
            check_key_from_index_large!(type=i64);
            check_key_from_index_large!(type=i128);
            check_key_from_index_large!(type=isize);
        }
    }
}
