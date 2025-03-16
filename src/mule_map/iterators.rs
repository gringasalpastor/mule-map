use crate::MuleMap;
use crate::mule_map::KeyIndex;
use num_traits::AsPrimitive;
use num_traits::PrimInt;
use std::collections::HashMap;
use std::fmt::Debug;

fn map_fn<'a, K, V>((k, v): (&'a K, &'a V)) -> (K, &'a V)
where
    K: Clone,
{
    (k.clone(), v)
}

#[allow(clippy::ref_option)]
fn filter_map_fn<K, V>(value: &Option<V>) -> Option<(K, &V)>
where
    K: num_traits::One,
{
    Some(K::one()).zip(value.as_ref())
}

type LeftSide<'a, K, V> =
    std::iter::Map<std::collections::hash_map::Iter<'a, K, V>, fn((&'a K, &'a V)) -> (K, &'a V)>;

type RightSide<'a, K, V> =
    std::iter::FilterMap<std::slice::Iter<'a, Option<V>>, fn(&'a Option<V>) -> Option<(K, &'a V)>>;
pub struct MuleMapIter<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> {
    iter: std::iter::Chain<LeftSide<'a, K, V>, RightSide<'a, K, V>>,
}

impl<'a, K, V, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMapIter<'a, K, V, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: num_traits::One + std::clone::Clone,
{
    fn from_hash_map_and_table<S>(
        hash_map: &'a HashMap<K, V, S>,
        table: &'a [Option<V>; TABLE_SIZE],
    ) -> Self
    where
        S: Default + std::hash::BuildHasher,
    {
        type MapFn<'a, K, V> = fn((&'a K, &'a V)) -> (K, &'a V);
        type FilterMap<'a, K, V> = fn(&Option<V>) -> Option<(K, &V)>;

        let h: std::iter::Map<_, MapFn<'a, K, V>> = hash_map
            .iter()
            .map(map_fn as fn((&'a K, &'a V)) -> (K, &'a V));
        let x: std::iter::FilterMap<_, FilterMap<'a, K, V>> = table
            .iter()
            .filter_map(filter_map_fn as fn(&Option<V>) -> Option<(K, &V)>);

        MuleMapIter { iter: h.chain(x) }
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
    #[inline]
    pub fn iter(&self) -> MuleMapIter<K, V, TABLE_MIN_VALUE, TABLE_SIZE> {
        MuleMapIter::<K, V, TABLE_MIN_VALUE, TABLE_SIZE>::from_hash_map_and_table(
            &self.hash_map,
            &self.table,
        )
    }
}

impl<'a, K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize> IntoIterator
    for &'a MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
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
        assert_eq!(iter.next(), Some((1, &2)));
    }
}
