use crate::MuleMap;
use crate::mule_map::key_index::KeyIndex;

use num_traits::AsPrimitive;
use num_traits::PrimInt;
use std::fmt::Debug;

impl<K, V, S, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>
    MuleMap<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
    V: Clone + PartialEq + Default,
    i128: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    fn _iter(&self) -> impl Iterator<Item = V> + '_
    where
        usize: AsPrimitive<K>,
    {
        self.hash_map.values().cloned().chain(
            self.table
                .iter()
                .filter_map(|value| value.as_ref())
                .cloned(),
        )
    }
}
