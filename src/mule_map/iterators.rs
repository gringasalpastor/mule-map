use crate::MuleMap;
use crate::mule_map::Key;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::BuildHasher;
use std::iter::Enumerate;
use std::iter::FilterMap;

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
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.as_ref())
}

#[derive(Debug, Clone)]
pub struct Iter<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<IterLeftSide<'a, K, V>, IterRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    Iter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
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
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.as_mut())
}

#[derive(Debug)]
pub struct IterMut<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<IterMutLeftSide<'a, K, V>, IterMutRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    IterMut<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
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
fn filter_map_fn_into<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, Option<V>),
) -> Option<(K, V)>
where
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value)
}

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
fn filter_map_fn_drain<K, V, const TABLE_MIN_VALUE: i128>(
    (index, value): (usize, &mut Option<V>),
) -> Option<(K, V)>
where
    K: Key<TABLE_MIN_VALUE>,
{
    Some(key_from_index::<K, TABLE_MIN_VALUE>(index)).zip(value.take())
}

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
    fn drop(&mut self) {
        for _ in &mut self.iter {}
    }
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> Iterator
    for DrainIter<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
    type Item = (K, V);
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
    K: Key<TABLE_MIN_VALUE>,
{
    value
        .as_ref()
        .map(|_| key_from_index::<K, TABLE_MIN_VALUE>(index))
}

#[derive(Debug, Clone)]
pub struct Keys<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<KeysLeftSide<'a, K, V>, KeysRightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    Keys<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
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

#[derive(Debug)]
pub struct IntoKeys<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<std::collections::hash_map::IntoKeys<K, V>, std::vec::IntoIter<K>>,
}

impl<K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    IntoKeys<K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: Key<TABLE_MIN_VALUE>,
{
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
#[allow(clippy::ref_option)]
fn filter_map_fn_values<V, const TABLE_MIN_VALUE: i128>(value: &Option<V>) -> Option<&V> {
    value.as_ref()
}

#[derive(Debug, Clone)]
pub struct Values<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<std::collections::hash_map::Values<'a, K, V>, ValuesRightSide<'a, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    Values<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
{
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
fn filter_map_fn_values_mut<V, const TABLE_MIN_VALUE: i128>(
    value: &mut Option<V>,
) -> Option<&mut V>
where
{
    value.as_mut()
}

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
fn filter_map_fn_into_values<V, const TABLE_MIN_VALUE: i128>(value: Option<V>) -> Option<V>
where
{
    value
}

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
    #[inline]
    pub fn iter(&self) -> Iter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        Iter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IterMut::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    #[inline]
    pub fn drain(&mut self) -> DrainIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        DrainIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    #[inline]
    pub fn keys(&self) -> Keys<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        Keys::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    #[inline]
    pub fn into_keys(self) -> IntoKeys<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IntoKeys::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            self.hash_map,
            &self.table,
        )
    }

    #[inline]
    pub fn values(&self) -> Values<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        Values::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }

    #[inline]
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        ValuesMut::<'_, K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &mut self.hash_map,
            &mut self.table,
        )
    }

    #[inline]
    pub fn into_values(self) -> IntoValues<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        IntoValues::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            self.hash_map,
            self.table,
        )
    }

    /// Retains only the elements specified by the predicate.
    ///
    ///  Analogous to [`HashMap::retain`]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        for (index, value) in self.table.iter_mut().enumerate() {
            if let Some(x) = value {
                if !f(&key_from_index::<K, TABLE_MIN_VALUE>(index), x) {
                    *value = None;
                }
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
