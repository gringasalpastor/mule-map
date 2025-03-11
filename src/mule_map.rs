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

    #[must_use]
    #[inline]
    pub fn new() -> Self {
        Self::with_capacity_and_hasher(0, S::default())
    }

    #[must_use]
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, S::default())
    }

    #[must_use]
    #[inline]
    pub fn with_hasher(hash_builder: S) -> Self {
        Self::with_capacity_and_hasher(0, hash_builder)
    }

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

    #[must_use]
    #[inline]
    pub fn capacity(&self) -> usize {
        self.hash_map.capacity()
    }

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

    #[must_use]
    #[inline]
    pub fn contains_key(&self, key: K) -> bool {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].is_some()
        } else {
            self.hash_map.contains_key(&key)
        }
    }

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

    #[inline]
    pub fn bump_int(&mut self, key: K)
    where
        V: std::ops::AddAssign<V> + num_traits::One + num_traits::Zero + PrimInt,
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

    /// ????
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

    #[must_use]
    #[inline]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        if Self::use_lookup_table(key) {
            let value: &mut Option<V> = &mut self.table[key.key_index()];
            match value {
                Some(_) => Entry::<K, V>::Occupied(OccupiedEntry::Vec(OccupiedVecEntry {
                    value: value,
                    key,
                })),
                None => {
                    Entry::<K, V>::Vacant(VacantEntry::Vec(VacantVecEntry { value: value, key }))
                }
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
        mule_map_non_zero.bump_non_zero(999999);
        mule_map_non_zero.bump_non_zero(999999);
        assert_eq!(
            mule_map_non_zero.get(999999),
            NonZero::<i32>::new(2).as_ref()
        );

        let mut mule_map = MuleMap::<u32, i32, fnv_rs::FnvBuildHasher>::default();

        mule_map.modify_or_insert(100, |x| *x += 10, 1);
        assert_eq!(mule_map.get(100), Some(&1));

        mule_map.modify_or_insert(100, |x| *x += 10, 1);
        assert_eq!(mule_map.get(100), Some(&11));
    }
}
