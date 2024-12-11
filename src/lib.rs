pub use crate::entry::private::{
    Entry, OccupiedEntry, OccupiedHashMapEntry, OccupiedVecEntry, VacantEntry, VacantHashMapEntry,
    VacantVecEntry,
};

use num_traits::AsPrimitive;
use num_traits::PrimInt;
use sealed::sealed;
use std::collections::HashMap;
use std::fmt::Debug;

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

    /// # Panics
    ///  ...
    #[must_use]
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
            .expect("TABLE_MAX_VALUE should fit into key type, K");

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
        // fails to compile min > max
        // let mut mule_map_bad = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, 1, 0>::new(&0);
        let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, { ZERO_SENTINEL }>::new();

        assert_eq!(mule_map.get(5), None);
        let entry = mule_map.entry(5);
        entry.or_insert(10);
        assert_eq!(mule_map.get(5), Some(&10));
    }
}
