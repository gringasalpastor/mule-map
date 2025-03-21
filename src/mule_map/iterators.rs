use crate::MuleMap;
use crate::mule_map::KeyIndex;
use num_traits::AsPrimitive;
use num_traits::PrimInt;
use std::collections::HashMap;
use std::fmt::Debug;

#[inline]
fn key_from_index<K, const TABLE_MIN_VALUE: i128>(index: usize) -> K
where
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
{
    TABLE_MIN_VALUE.as_() + index.as_()
}

// MuleMapIter

type IterLeftSide<'a, K, V> =
    std::iter::Map<std::collections::hash_map::Iter<'a, K, V>, fn((&'a K, &'a V)) -> (K, &'a V)>;

type IterRightSide<'a, K, V> = std::iter::FilterMap<
    std::iter::Enumerate<std::slice::Iter<'a, Option<V>>>,
    fn((usize, &'a Option<V>)) -> Option<(K, &'a V)>,
>;

#[inline]
fn map_fn<'a, K, V>((key, val): (&'a K, &'a V)) -> (K, &'a V)
where
    K: Copy,
{
    (*key, val)
}

#[inline]
fn filter_map_fn<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &Option<V>),
) -> Option<(K, &V)>
where
    usize: AsPrimitive<K>,
    i128: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.as_ref())
}

pub struct MuleMapIter<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<IterLeftSide<'a, K, V>, IterRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMapIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    usize: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
    i128: AsPrimitive<K>,
{
    fn from_hash_map_and_table<S>(
        hash_map: &'a HashMap<K, V, S>,
        table: &'a [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: std::hash::BuildHasher,
    {
        type MapFn<'a, K, V> = fn((&'a K, &'a V)) -> (K, &'a V);
        type FilterMapFn<'a, K, V> = fn((usize, &Option<V>)) -> Option<(K, &V)>;

        let left_iter: std::iter::Map<_, MapFn<'a, K, V>> = hash_map
            .iter()
            .map(map_fn as fn((&'a K, &'a V)) -> (K, &'a V));
        let right_iter: std::iter::FilterMap<_, FilterMapFn<'a, K, V>> =
            table.iter().enumerate().filter_map(
                filter_map_fn::<K, V, TABLE_MIN_VALUE>
                    as fn((usize, &Option<V>)) -> Option<(K, &V)>,
            );

        MuleMapIter {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for MuleMapIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

// MuleMapIterMut

type IterMutLeftSide<'a, K, V> = std::iter::Map<
    std::collections::hash_map::IterMut<'a, K, V>,
    fn((&'a K, &'a mut V)) -> (K, &'a mut V),
>;

type IterMutRightSide<'a, K, V> = std::iter::FilterMap<
    std::iter::Enumerate<std::slice::IterMut<'a, Option<V>>>,
    fn((usize, &'a mut Option<V>)) -> Option<(K, &'a mut V)>,
>;

#[inline]
fn map_fn_mut<'a, K, V>((key, val): (&'a K, &'a mut V)) -> (K, &'a mut V)
where
    K: Copy,
{
    (*key, val)
}

#[inline]
fn filter_map_fn_mut<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &mut Option<V>),
) -> Option<(K, &mut V)>
where
    usize: AsPrimitive<K>,
    i128: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.as_mut())
}

pub struct MuleMapIterMut<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<IterMutLeftSide<'a, K, V>, IterMutRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMapIterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    usize: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
    i128: AsPrimitive<K>,
{
    fn from_hash_map_and_table<S>(
        hash_map: &'a mut HashMap<K, V, S>,
        table: &'a mut [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: std::hash::BuildHasher,
    {
        type MapFn<'a, K, V> = fn((&'a K, &'a mut V)) -> (K, &'a mut V);
        type FilterMapFn<'a, K, V> = fn((usize, &mut Option<V>)) -> Option<(K, &mut V)>;

        let left_iter: std::iter::Map<_, MapFn<'a, K, V>> = hash_map
            .iter_mut()
            .map(map_fn_mut as fn((&'a K, &'a mut V)) -> (K, &'a mut V));
        let right_iter: std::iter::FilterMap<_, FilterMapFn<'a, K, V>> =
            table.iter_mut().enumerate().filter_map(
                filter_map_fn_mut::<K, V, TABLE_MIN_VALUE>
                    as fn((usize, &mut Option<V>)) -> Option<(K, &mut V)>,
            );

        MuleMapIterMut {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for MuleMapIterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, &'a mut V);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

// MuleMapIntoIter

type IntoIterRightSide<K, V, const TABLE_SIZE: usize> = std::iter::FilterMap<
    std::iter::Enumerate<std::array::IntoIter<Option<V>, TABLE_SIZE>>,
    fn((usize, Option<V>)) -> Option<(K, V)>,
>;

#[inline]
fn filter_map_fn_into<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, Option<V>),
) -> Option<(K, V)>
where
    usize: AsPrimitive<K>,
    i128: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value)
}

pub struct MuleMapIntoIter<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<
        std::collections::hash_map::IntoIter<K, V>,
        IntoIterRightSide<K, V, TABLE_SIZE>,
    >,
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMapIntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    usize: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
    i128: AsPrimitive<K>,
{
    fn from_hash_map_and_table<S>(
        hash_map: HashMap<K, V, S>,
        table: [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: std::hash::BuildHasher,
    {
        type FilterMapFn<K, V> = fn((usize, Option<V>)) -> Option<(K, V)>;

        let left_iter: std::collections::hash_map::IntoIter<K, V> = hash_map.into_iter();
        let right_iter: std::iter::FilterMap<_, FilterMapFn<K, V>> =
            table.into_iter().enumerate().filter_map(
                filter_map_fn_into::<K, V, TABLE_MIN_VALUE>
                    as fn((usize, Option<V>)) -> Option<(K, V)>,
            );

        MuleMapIntoIter {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for MuleMapIntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

// Drain

type DrainIterRightSide<'a, K, V, const TABLE_SIZE: usize> = std::iter::FilterMap<
    std::iter::Enumerate<std::slice::IterMut<'a, Option<V>>>,
    fn((usize, &mut Option<V>)) -> Option<(K, V)>,
>;

#[inline]
fn filter_map_fn_drain<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &mut Option<V>),
) -> Option<(K, V)>
where
    usize: AsPrimitive<K>,
    i128: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.take())
}

pub struct MuleMapDrainIter<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<
        std::collections::hash_map::Drain<'a, K, V>,
        DrainIterRightSide<'a, K, V, TABLE_SIZE>,
    >,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMapDrainIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    usize: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
    i128: AsPrimitive<K>,
{
    fn from_hash_map_and_table<S>(
        hash_map: &'a mut HashMap<K, V, S>,
        table: &'a mut [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: std::hash::BuildHasher,
    {
        type FilterMapFn<K, V> = fn((usize, &mut Option<V>)) -> Option<(K, V)>;

        let left_iter = hash_map.drain();

        let right_iter: std::iter::FilterMap<_, FilterMapFn<K, V>> =
            table.iter_mut().enumerate().filter_map(
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
    for MuleMapDrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    fn drop(&mut self) {
        for _ in &mut self.iter {}
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for MuleMapDrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, V);
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

// Keys

type KeysLeftSide<'a, K, V> =
    std::iter::Map<std::collections::hash_map::Keys<'a, K, V>, fn(&'a K) -> K>;

type KeysRightSide<'a, K, V> = std::iter::FilterMap<
    std::iter::Enumerate<std::slice::Iter<'a, Option<V>>>,
    fn((usize, &'a Option<V>)) -> Option<K>,
>;

#[inline]
fn map_fn_keys<K>(key: &K) -> K
where
    K: Copy,
{
    *key
}

#[inline]
fn filter_map_fn_keys<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &Option<V>),
) -> Option<K>
where
    usize: AsPrimitive<K>,
    i128: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
{
    value
        .as_ref()
        .map(|_| key_from_index::<K, TABLE_MIN_VALUE>(index))
}

pub struct MuleMapKeys<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<KeysLeftSide<'a, K, V>, KeysRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMapKeys<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    usize: AsPrimitive<K>,
    K: Copy + std::ops::Add<Output = K> + 'static,
    i128: AsPrimitive<K>,
{
    fn from_hash_map_and_table<S>(
        hash_map: &'a HashMap<K, V, S>,
        table: &'a [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: std::hash::BuildHasher,
    {
        type MapFn<'a, K> = fn(&'a K) -> K;
        type FilterMapFn<'a, K, V> = fn((usize, &Option<V>)) -> Option<K>;

        let left_iter: std::iter::Map<_, MapFn<'a, K>> =
            hash_map.keys().map(map_fn_keys as fn(&'a K) -> K);
        let right_iter: std::iter::FilterMap<_, FilterMapFn<'a, K, V>> =
            table.iter().enumerate().filter_map(
                filter_map_fn_keys::<K, V, TABLE_MIN_VALUE> as fn((usize, &Option<V>)) -> Option<K>,
            );

        MuleMapKeys {
            iter: left_iter.chain(right_iter),
        }
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for MuleMapKeys<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

// MuleMap

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    #[inline]
    pub fn iter(&self) -> MuleMapIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        MuleMapIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    #[inline]
    pub fn iter_mut(&mut self) -> MuleMapIterMut<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        MuleMapIterMut::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    #[inline]
    pub fn drain(&mut self) -> MuleMapDrainIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        MuleMapDrainIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    #[inline]
    pub fn keys(&self) -> MuleMapKeys<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        MuleMapKeys::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }
}

// IntoIterator
impl<'a, K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for &'a MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    type Item = (K, &'a V);
    type IntoIter = MuleMapIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>;

    #[inline]
    fn into_iter(self) -> MuleMapIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        self.iter()
    }
}

impl<'a, K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for &'a mut MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    type Item = (K, &'a mut V);
    type IntoIter = MuleMapIterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>;

    #[inline]
    fn into_iter(self) -> MuleMapIterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        self.iter_mut()
    }
}

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    type Item = (K, V);
    type IntoIter = MuleMapIntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE>;

    #[inline]
    fn into_iter(self) -> MuleMapIntoIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        MuleMapIntoIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            self.hash_map,
            self.table,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_iter() {
        let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
        mule_map.bump_int(10);
        mule_map.bump_int(10);
        mule_map.bump_int(999_999);
        let mut iter = mule_map.iter();

        assert_eq!(iter.next(), Some((999_999, &1)));
        assert_eq!(iter.next(), Some((10, &2)));

        for _ in &mule_map {}
        for _ in &mut mule_map {}
        for _ in mule_map {}

        let mut mule_map2 = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
        mule_map2.bump_int(10);
        mule_map2.bump_int(11);
        mule_map2.bump_int(999_998);
        mule_map2.bump_int(999_999);

        for _ in mule_map2.drain().take(1) {}
        assert_eq!(mule_map2.len(), 0);

        //keys
        let mut mule_map_keys = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();
        mule_map_keys.bump_int(10);
        mule_map_keys.bump_int(11);
        mule_map_keys.bump_int(999_998);
        mule_map_keys.bump_int(999_999);
        for k in mule_map_keys.keys() {
            assert!([10, 11, 999_999, 999_998].contains(&k));
        }
    }
}
