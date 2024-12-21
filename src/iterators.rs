use crate::KeyIndex;
use crate::MuleMap;
use num_traits::AsPrimitive;
use num_traits::PrimInt;
use std::fmt::Debug;

struct Iter {}

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
    <K as TryFrom<i128>>::Error: Debug,
{
    fn iter(
        &self,
    ) -> impl Iterator<Item = K> + use<'_, K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE>
    where
        usize: AsPrimitive<K>,
    {
        self.hash_map.keys().map(|&key| key).chain(
            self.occupied_map
                .iter()
                .enumerate()
                .filter_map(|(index, occupied)| if *occupied { Some(index.as_()) } else { None }),
        )
    }
}

// pub fn keys(
//     &self,
// ) -> impl Iterator<Item = K> + use<'_, K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE>
// where
//     usize: AsPrimitive<K>,
// {
//     if !ZERO_IS_SENTINEL {
//         self.hash_map.keys()
//     } else {
//         // NOTE: !!!! need to convert index back to key
//         self.hash_map.keys().map(|&key| key).chain(
//             self.occupied_map
//                 .iter()
//                 .enumerate()
//                 .filter_map(
//                     |(index, occupied)| if *occupied { Some(index.as_()) } else { None },
//                 ),
//         )
//     }

//     // if !ZERO_IS_SENTINEL{
//     // self.hash_map.keys().map(|&key| key).chain(
//     //     self.occupied_map
//     //         .iter()
//     //         .enumerate()
//     //         .filter(|(index, occupied): (usize, bool)| occupied)
//     //         .map(|(index, occupied): (usize, bool)| index),
//     // )
//     //}
// }
