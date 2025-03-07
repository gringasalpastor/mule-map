use key_index::KeyIndex;
use num_traits::AsPrimitive;
use num_traits::PrimInt;
use sealed::sealed;
use std::collections::HashMap;
use std::fmt::Debug;
use std::num::NonZero;

mod key_index;

#[sealed]
#[doc(hidden)]
pub trait NonZeroInt {
    type UnderlayingType;
    const ONE: Self;
    #[inline]
    fn checked_add(self, other: Self::UnderlayingType) -> Option<Self>
    where
        Self::UnderlayingType: bytemuck::Pod,
        Self::UnderlayingType: std::ops::AddAssign<Self::UnderlayingType>,
        Self: bytemuck::PodInOption,
        Self::UnderlayingType: PrimInt,
    {
        let mut result = Some(self);
        let x = bytemuck::cast_mut::<Option<Self>, Self::UnderlayingType>(&mut result);
        *x += other;
        result
    }
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI128 {
    const ONE: std::num::NonZeroI128 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = i128;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI16 {
    const ONE: std::num::NonZeroI16 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = i16;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI32 {
    const ONE: std::num::NonZeroI32 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = i32;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI64 {
    const ONE: std::num::NonZeroI64 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = i64;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroI8 {
    const ONE: std::num::NonZeroI8 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = i8;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroIsize {
    const ONE: std::num::NonZeroIsize = const { NonZero::new(1).unwrap() };
    type UnderlayingType = isize;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU128 {
    const ONE: std::num::NonZeroU128 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = u128;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU16 {
    const ONE: std::num::NonZeroU16 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = u16;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU32 {
    const ONE: std::num::NonZeroU32 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = u32;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU64 {
    const ONE: std::num::NonZeroU64 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = u64;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroU8 {
    const ONE: std::num::NonZeroU8 = const { NonZero::new(1).unwrap() };
    type UnderlayingType = u8;
}

#[sealed]
impl NonZeroInt for std::num::NonZeroUsize {
    const ONE: std::num::NonZeroUsize = const { NonZero::new(1).unwrap() };
    type UnderlayingType = usize;
}

#[derive(Debug)]
pub struct MuleMap2<
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
    for MuleMap2<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
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
    MuleMap2<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE>
where
    K: PrimInt + Eq + std::hash::Hash + KeyIndex<K, TABLE_MIN_VALUE> + TryFrom<i128> + 'static,
    S: Default + std::hash::BuildHasher,
    V: PartialEq + Copy,
    i128: AsPrimitive<K>,
    usize: AsPrimitive<K>,
    <K as TryFrom<i128>>::Error: Debug,
{
    // const STATIC_ASSERT_MAX_GREATER_OR_EQ_ONE: () = assert!(TABLE_SIZE >= TABLE_MIN_VALUE);

    #[inline]
    #[must_use]
    fn use_lookup_table(key: K) -> bool {
        // `TABLE_SIZE` and `TABLE_MIN_VALUE` must fit into a key type, K
        // Hopfully in the future they can have type K
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
        MuleMap2::<K, V, S, TABLE_MIN_VALUE, TABLE_SIZE> {
            hash_map: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            table: [None; TABLE_SIZE],
        }
    }

    pub fn capacity(&self) -> usize {
        self.hash_map.capacity()
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
        <V as NonZeroInt>::UnderlayingType: std::ops::AddAssign<V::UnderlayingType>,
        <V as NonZeroInt>::UnderlayingType: bytemuck::Pod + PrimInt,
    {
        use num_traits::One;

        if Self::use_lookup_table(key) {
            *bytemuck::cast_mut::<Option<V>, V::UnderlayingType>(
                &mut self.table[key.key_index()],
            ) += V::UnderlayingType::one();
        } else {
            self.hash_map
                .entry(key)
                .and_modify(|counter| {
                    *counter = counter
                        .checked_add(V::UnderlayingType::one())
                        .expect("Addition should not overflow");
                })
                .or_insert(V::ONE);
        }
    }

    #[inline]
    pub fn get(&self, key: K) -> Option<&V> {
        if Self::use_lookup_table(key) {
            self.table[key.key_index()].as_ref()
        } else {
            let result = self.hash_map.get(&key);
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut mule_map_int = MuleMap2::<u32, i32, fnv_rs::FnvBuildHasher>::default();
        mule_map_int.bump_int(10);
        mule_map_int.bump_int(10);
        assert_eq!(mule_map_int.get(10), Some(&2));

        let mut mule_map_non_zero =
            MuleMap2::<u32, NonZero<i32>, fnv_rs::FnvBuildHasher>::default();

        mule_map_non_zero.bump_non_zero(10);
        mule_map_non_zero.bump_non_zero(10);
        assert_eq!(mule_map_non_zero.get(10), NonZero::<i32>::new(2).as_ref());
        mule_map_non_zero.bump_non_zero(999999);
        mule_map_non_zero.bump_non_zero(999999);
        assert_eq!(
            mule_map_non_zero.get(999999),
            NonZero::<i32>::new(2).as_ref()
        );
    }
}
