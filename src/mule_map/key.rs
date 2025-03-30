use sealed::sealed;

#[sealed]
pub trait PrimInt: num_traits::PrimInt {
    type PromotedType; // Used to avoid overflow during addition

    fn add_i218_usize_promoted(left: i128, right: usize) -> Self;
    fn i128_as_k(val: i128) -> Self;
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType;
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType;
    fn promoted_as_k(val: Self::PromotedType) -> Self;
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType;
}

#[sealed]
impl PrimInt for u8 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for u16 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for u32 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for u64 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for u128 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for i8 {
    type PromotedType = i16;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for i16 {
    type PromotedType = i32;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for i32 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for i64 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for i128 {
    type PromotedType = Self;

    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for usize {
    type PromotedType = Self;

    #[inline]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

#[sealed]
impl PrimInt for isize {
    type PromotedType = Self;

    #[inline]
    fn add_i218_usize_promoted(left: i128, right: usize) -> Self {
        (left as Self::PromotedType + right as Self::PromotedType) as Self
    }

    #[inline]
    fn i128_as_k(val: i128) -> Self {
        val as Self
    }

    #[inline]
    fn i128_as_k_promoted(val: i128) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn usize_as_k_promoted(val: usize) -> Self::PromotedType {
        val as Self::PromotedType
    }

    #[inline]
    fn promoted_as_k(val: Self::PromotedType) -> Self {
        val as Self
    }

    #[inline]
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self::PromotedType {
        x + y
    }
}

// use super::key_index::KeyIndex;
use std::fmt::Debug;
use std::hash::Hash;

#[sealed]
pub trait Key<const TABLE_MIN_VALUE: i128>:
    PrimInt + Eq + Hash + TryFrom<i128> + Debug + 'static
{
    fn key_index(&self) -> usize;
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for u8 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types because key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u8) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for u16 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types because key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u16) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for u32 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types because key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for u64 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types because key >= TABLE_MIN_VALUE
        (*self - TABLE_MIN_VALUE as u64) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for u128 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types because key >= TABLE_MIN_VALUE
        // NOTE: i128 can't represent u128::MAX, but it's value will still fit in u128
        (*self - TABLE_MIN_VALUE as u128) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for i8 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: Promotion to i16 _needed_ for subtractions because difference could exceed i8::MAX
        (i16::from(*self) - TABLE_MIN_VALUE as i16) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for i16 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: Promotion to i32 _needed_ for subtractions because difference could exceed i16::MAX
        (i32::from(*self) - TABLE_MIN_VALUE as i32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for i32 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in i32
        (*self - TABLE_MIN_VALUE as i32) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for i64 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in i64
        (*self - TABLE_MIN_VALUE as i64) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for i128 {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in i128
        (*self - TABLE_MIN_VALUE) as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for usize {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions of unsigned types because key >= TABLE_MIN_VALUE
        *self - TABLE_MIN_VALUE as usize
    }
}

#[sealed]
impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for isize {
    #[allow(clippy::cast_possible_truncation)]
    #[allow(clippy::cast_sign_loss)]
    fn key_index(&self) -> usize {
        // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
        // NOTE: No promotion needed for subtractions because difference will be at most i32::MAX - fits in isize see
        // `STATIC_ASSERT_ISIZE_FITS_I32`
        (*self - TABLE_MIN_VALUE as isize) as usize
    }
}

#[cfg(test)]
mod tests {
    use crate::MuleMap;
    use crate::mule_map::key::Key;
    use std::fmt::Debug;

    fn test_index<K, const TABLE_MIN_VALUE: i128, const TABLE_SIZE: usize>(key: K) -> usize
    where
        K: Key<TABLE_MIN_VALUE>,
        <K as TryFrom<i128>>::Error: Debug,
    {
        type Hash = fnv_rs::FnvBuildHasher;
        MuleMap::<K, u8, Hash, TABLE_MIN_VALUE, TABLE_SIZE>::check_bounds();
        assert!(MuleMap::<K, u8, Hash, TABLE_MIN_VALUE, TABLE_SIZE>::use_lookup_table(key));
        key.key_index()
    }

    const MAX_U8_SIZE: usize = u8::MAX as usize + 1;

    #[test]
    fn check_table_range_unsigned() {
        const MAX_U16_SIZE: usize = u16::MAX as usize + 1;
        const MAX_SIZE: usize = i32::MAX as usize + 1; // i32::MAX is largest allowed
        const MAX_INDEX: usize = i32::MAX as usize;
        const MAX_INDEX_U32: u32 = i32::MAX as u32; // Help clippy see there is no overflow

        // u8
        assert_eq!(test_index::<u8, 0, MAX_U8_SIZE>(u8::MIN), 0);
        assert_eq!(test_index::<u8, 0, MAX_U8_SIZE>(u8::MAX), MAX_U8_SIZE - 1);
        assert_eq!(test_index::<u8, 100, { MAX_U8_SIZE - 100 }>(100), 0);
        assert_eq!(test_index::<u8, 100, { MAX_U8_SIZE - 100 }>(255), 155);

        // u16
        assert_eq!(test_index::<u16, 0, MAX_U16_SIZE>(u16::MIN), 0);
        assert_eq!(
            test_index::<u16, 0, MAX_U16_SIZE>(u16::MAX),
            MAX_U16_SIZE - 1
        );
        assert_eq!(test_index::<u16, 100, { MAX_U16_SIZE - 100 }>(100), 0);
        assert_eq!(
            test_index::<u16, 100, { MAX_U16_SIZE - 100 }>(u16::MAX),
            MAX_U16_SIZE - 100 - 1
        );

        // u32
        assert_eq!(test_index::<u32, 0, MAX_SIZE>(u32::MIN), 0);
        assert_eq!(test_index::<u32, 0, MAX_SIZE>(i32::MAX as u32), MAX_INDEX);
        assert_eq!(
            test_index::<u32, { (u32::MAX - MAX_INDEX_U32) as i128 }, MAX_SIZE>(
                u32::MAX - MAX_INDEX_U32
            ),
            0
        );
        assert_eq!(
            test_index::<u32, { (u32::MAX - MAX_INDEX_U32) as i128 }, MAX_SIZE>(u32::MAX),
            MAX_INDEX
        );

        // u64
        assert_eq!(test_index::<u64, 0, MAX_SIZE>(u64::MIN), 0);
        assert_eq!(test_index::<u64, 0, MAX_SIZE>(i32::MAX as u64), MAX_INDEX);
        assert_eq!(
            test_index::<u64, { (u64::MAX - MAX_INDEX as u64) as i128 }, MAX_SIZE>(
                u64::MAX - MAX_INDEX as u64
            ),
            0
        );
        assert_eq!(
            test_index::<u64, { (u64::MAX - MAX_INDEX as u64) as i128 }, MAX_SIZE>(u64::MAX),
            MAX_INDEX
        );

        // u128
        assert_eq!(test_index::<u128, 0, MAX_SIZE>(u128::MIN), 0);
        assert_eq!(test_index::<u128, 0, MAX_SIZE>(i32::MAX as u128), MAX_INDEX);
        assert_eq!(
            test_index::<u128, { i128::MAX - MAX_INDEX as i128 }, MAX_SIZE>(
                i128::MAX as u128 - MAX_INDEX as u128
            ),
            0
        );
        assert_eq!(
            test_index::<u128, { i128::MAX - MAX_INDEX as i128 }, MAX_SIZE>(i128::MAX as u128),
            MAX_INDEX
        );
    }

    #[test]
    fn check_table_range_signed() {
        // i8
        assert_eq!(
            test_index::<i8, { i8::MIN as i128 }, MAX_U8_SIZE>(i8::MIN),
            0
        );
    }
}
