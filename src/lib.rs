use crate::entry::{
    Entry, OccupiedEntry, OccupiedHashMapEntry, OccupiedVecEntry, VacantEntry, VacantHashMapEntry,
    VacantVecEntry,
};

use num_traits::AsPrimitive;
use num_traits::PrimInt;
use paste::paste;
use sealed::sealed;
use std::collections::HashMap;

pub const ZERO_SENTINEL: bool = true;
pub const NOT_ZERO_SENTINEL: bool = false;

mod entry;

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
    validity_map: Vec<bool>,
    hash_map: HashMap<K, V, S>,
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
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + AsPrimitive<i128>, /*+ std::convert::TryFrom<i128>*/
    S: std::default::Default + std::hash::BuildHasher,
    V: std::clone::Clone + std::cmp::PartialEq + Default + num_traits::ConstZero,
{
    const STATIC_ASSERT_MAX_GREATER_OR_EQ_MIN: () = assert!(TABLE_MAX_VALUE >= TABLE_MIN_VALUE);

    pub fn new() -> Self {
        let _ = Self::STATIC_ASSERT_MAX_GREATER_OR_EQ_MIN;
        // NOTE: Can't make this a static assert yet because of try_from
        assert!(usize::try_from(TABLE_MAX_VALUE - TABLE_MIN_VALUE + 1).is_ok());
        assert!(TABLE_MAX_VALUE <= <K as AsPrimitive<i128>>::as_(K::max_value()));
        assert!(TABLE_MIN_VALUE >= <K as AsPrimitive<i128>>::as_(K::min_value()));

        let table_size: usize = (TABLE_MAX_VALUE - TABLE_MIN_VALUE + 1) as usize;

        MuleMap::<K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE> {
            table: vec![V::default(); table_size],
            validity_map: vec![false; table_size],
            hash_map: Default::default(),
        }
    }

    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, ZERO_IS_SENTINEL> {
        // if key <= K::from(TABLE_MAX_VALUE).expect("REASON")
        //     && key >= K::from(TABLE_MIN_VALUE).expect("REASON")

        if <K as AsPrimitive<i128>>::as_(key) <= TABLE_MAX_VALUE
            && <K as AsPrimitive<i128>>::as_(key) >= TABLE_MIN_VALUE
        {
            let key_index = key.key_index();

            match ZERO_IS_SENTINEL {
                ZERO_SENTINEL => match self.table[key_index] == V::default() {
                    true => {
                        Entry::<K, V, ZERO_IS_SENTINEL>::Vacant(VacantEntry::Vec(VacantVecEntry {
                            value: &mut self.table[key_index],
                            validity: &mut self.validity_map[key_index],
                            key: key,
                        }))
                    }
                    false => Entry::<K, V, ZERO_IS_SENTINEL>::Occupied(OccupiedEntry::Vec(
                        OccupiedVecEntry {
                            value: &mut self.table[key_index],
                            validity: &mut self.validity_map[key_index],
                            key: key,
                        },
                    )),
                },
                NOT_ZERO_SENTINEL => match self.validity_map[key_index] {
                    true => Entry::<K, V, ZERO_IS_SENTINEL>::Occupied(OccupiedEntry::Vec(
                        OccupiedVecEntry {
                            value: &mut self.table[key_index],
                            validity: &mut self.validity_map[key_index],
                            key: key,
                        },
                    )),

                    false => {
                        Entry::<K, V, ZERO_IS_SENTINEL>::Vacant(VacantEntry::Vec(VacantVecEntry {
                            value: &mut self.table[key_index],
                            validity: &mut self.validity_map[key_index],
                            key: key,
                        }))
                    }
                },
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

    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        if key <= K::from(TABLE_MAX_VALUE).expect("REASON")
            && key >= K::from(TABLE_MIN_VALUE).expect("REASON")
        {
            let key_index = key.key_index();
            match ZERO_IS_SENTINEL {
                ZERO_SENTINEL => {
                    if self.table[key_index] == V::default() {
                        return None;
                    } else {
                        return Some(&self.table[key_index]);
                    }
                }
                NOT_ZERO_SENTINEL => match self.validity_map[key_index] {
                    true => {
                        return Some(&self.table[key_index]);
                    }
                    false => {
                        return None;
                    }
                },
            }
        } else {
            return self.hash_map.get(&key);
        }
    }

    #[inline]
    pub fn bump(&mut self, key: K)
    where
        V: std::ops::AddAssign<V> + num_traits::One,
        K: AsPrimitive<i128> + AsPrimitive<usize> + AsPrimitive<K>,
    {
        if <K as AsPrimitive<i128>>::as_(key) <= TABLE_MAX_VALUE
            && <K as AsPrimitive<i128>>::as_(key) >= TABLE_MIN_VALUE
        {
            let key_index = key.key_index();
            match ZERO_IS_SENTINEL {
                ZERO_SENTINEL => {
                    self.table[key_index] += V::one();
                }
                NOT_ZERO_SENTINEL => {
                    self.validity_map[key_index] = true;
                    self.table[key_index] += V::one();
                }
            }
        } else {
            self.hash_map
                .entry(key)
                .and_modify(|counter| *counter += V::one())
                .or_insert(V::one());
        }
    }

    #[inline]
    pub fn modify_or_insert<F>(&mut self, key: K, f: F, default: V)
    where
        F: FnOnce(&mut V),
        K: AsPrimitive<i128> + AsPrimitive<usize> + AsPrimitive<K>,
    {
        if <K as AsPrimitive<i128>>::as_(key) <= TABLE_MAX_VALUE
            && <K as AsPrimitive<i128>>::as_(key) >= TABLE_MIN_VALUE
        {
            let key_index = key.key_index();
            match ZERO_IS_SENTINEL {
                ZERO_SENTINEL => {
                    if self.table[key_index] == Default::default() {
                        self.table[key_index] = default;
                    } else {
                        f(&mut self.table[key_index])
                    }
                }
                NOT_ZERO_SENTINEL => {
                    if self.validity_map[key_index] {
                        f(&mut self.table[key_index])
                    } else {
                        self.table[key_index] = default;
                    }
                    self.validity_map[key_index] = true;
                }
            }
        } else {
            self.hash_map.entry(key).and_modify(f).or_insert(default);
        }
    }
}

#[sealed]
pub trait KeyIndex<K, const TABLE_MIN_VALUE: i128> {
    fn key_index(&self) -> usize;
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u8, TABLE_MIN_VALUE> for u8 {
    fn key_index(&self) -> usize {
        (*self - TABLE_MIN_VALUE as u8) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u16, TABLE_MIN_VALUE> for u16 {
    fn key_index(&self) -> usize {
        (*self - TABLE_MIN_VALUE as u16) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u32, TABLE_MIN_VALUE> for u32 {
    fn key_index(&self) -> usize {
        (*self - TABLE_MIN_VALUE as u32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<u64, TABLE_MIN_VALUE> for u64 {
    fn key_index(&self) -> usize {
        (*self - TABLE_MIN_VALUE as u64) as usize
    }
}

// #[sealed]
// impl<const TABLE_MIN_VALUE: i128> KeyIndex<u128, TABLE_MIN_VALUE> for u128 {
//     fn key_index(&self) -> usize {
//         // NOTE: ...
//         (*self - TABLE_MIN_VALUE as u128) as usize
//     }
// }

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i8, TABLE_MIN_VALUE> for i8 {
    fn key_index(&self) -> usize {
        (*self as i16 - TABLE_MIN_VALUE as i16) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i16, TABLE_MIN_VALUE> for i16 {
    fn key_index(&self) -> usize {
        (*self as i32 - TABLE_MIN_VALUE as i32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i32, TABLE_MIN_VALUE> for i32 {
    fn key_index(&self) -> usize {
        // table size will not exceed limits of i32, no need to promote
        (*self - TABLE_MIN_VALUE as i32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> KeyIndex<i64, TABLE_MIN_VALUE> for i64 {
    fn key_index(&self) -> usize {
        // table size will not exceed limits of i64, no need to promote
        (*self - TABLE_MIN_VALUE as i64) as usize
    }
}

// #[sealed]
// impl<const TABLE_MIN_VALUE: i128> KeyIndex<i128, TABLE_MIN_VALUE> for i128 {
//     fn key_index(&self) -> usize {
//         // table size will not exceed limits of i128, no need to promote
//         (*self - TABLE_MIN_VALUE) as usize
//     }
// }

// MuleMap<K, V, S, ZERO_IS_SENTINEL, TABLE_MIN_VALUE, TABLE_MAX_VALUE>

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        // fails to compile min > max
        // let mut mule_map_bad = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, 1, 0>::new(&0);
        let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, { ZERO_SENTINEL }>::new();

        assert_eq!(mule_map.get(5), None);
        let entry = mule_map.entry(5);
        entry.or_insert(10);
        assert_eq!(mule_map.get(5), Some(&10));

        // let _sbla = newb!(u32);
        // let _mule_map = MuleMapU32::<usize, fnv_rs::FnvBuildHasher, { ZERO_SENTINEL }, 0, 1>::new();
    }
}
