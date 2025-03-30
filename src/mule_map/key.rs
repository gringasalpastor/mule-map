use sealed::sealed;
use std::fmt::Debug;
use std::hash::Hash;

#[sealed]
pub trait PrimInt: num_traits::PrimInt {
    type PromotedType; // Used to avoid overflow during addition

    fn as_promoted(val: Self) -> Self::PromotedType;
    fn i128_as_k(val: i128) -> Self;
    fn i128_as_promoted(val: i128) -> Self::PromotedType;
    fn usize_as_promoted(val: usize) -> Self::PromotedType;
    fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self;
}

macro_rules! impl_prim_int {
    (type=$prim_type:ty, promoted_type=$promoted_type:ty) => {
        #[sealed]
        impl PrimInt for $prim_type {
            type PromotedType = $promoted_type;

            // NOTE: This could almost use `Self::PromotedType::from(val)` if not for isize -> i64, which is also
            // lossless because i64 is the largest type isize can be.
            #[inline]
            #[allow(clippy::cast_lossless)]
            fn as_promoted(val: Self) -> Self::PromotedType {
                val as Self::PromotedType
            }

            // NOTE: `TABLE_MIN_VALUE` fits into `K`.  See [`mule_map::MuleMap::check_bounds`].
            //
            // CAUTION: Don't use with other values that might truncate
            #[inline]
            #[allow(clippy::cast_possible_truncation)]
            #[allow(clippy::cast_sign_loss)]
            fn i128_as_k(val: i128) -> Self {
                val as Self
            }

            // NOTE: `TABLE_MIN_VALUE` fits into `K`. So they it also fits into `Self::PromotedType`.  See
            // [`mule_map::MuleMap::check_bounds`]
            //
            // CAUTION: Don't use with other values that might truncate
            #[inline]
            #[allow(clippy::cast_possible_truncation)]
            #[allow(clippy::cast_sign_loss)]
            fn i128_as_promoted(val: i128) -> Self::PromotedType {
                val as Self::PromotedType
            }

            // NOTE: `TABLE_SIZE.saturating_sub(1)` fits into `K`. So it also fits into `Self::PromotedType`.  See
            // [`mule_map::MuleMap::check_bounds`]
            //
            // CAUTION: Don't use with other values that might truncate
            #[inline]
            #[allow(clippy::cast_possible_truncation)]
            #[allow(clippy::cast_possible_wrap)]
            fn usize_as_promoted(val: usize) -> Self::PromotedType {
                val as Self::PromotedType
            }

            // NOTE: To be used with 2 values where their sum fits into K. For example, `TABLE_MIN_VALUE + TABLE_SIZE -
            // 1` or `TABLE_MIN_VALUE + key_index`. Promotion is needed for cases like i8::MIN + 255, since 255 does not
            // fit in i8
            //
            // CAUTION: Don't use with other values that might truncate
            #[inline]
            #[allow(clippy::cast_possible_truncation)]
            fn add_promoted(x: Self::PromotedType, y: Self::PromotedType) -> Self {
                (x + y) as Self
            }
        }
    };
}

// NOTE: unsigned ints don't need promotion during addition
impl_prim_int!(type=u8, promoted_type=Self);
impl_prim_int!(type=u16, promoted_type=Self);
impl_prim_int!(type=u32, promoted_type=Self);
impl_prim_int!(type=u64, promoted_type=Self);
impl_prim_int!(type=u128, promoted_type=Self);
impl_prim_int!(type=usize, promoted_type=Self);

// NOTE: Promotion is needed for cases like `i8::MIN + 255`, since 255 does not fit in i8
impl_prim_int!(type=i8, promoted_type=i16);
impl_prim_int!(type=i16, promoted_type=i32);
// No promotion needed, `i32::MIN + i32::MAX-1` will not truncate. TABLE_SIZE is at most `i32::MAX + 1`, see
// [`STATIC_ASSERT_LIMIT_SIZE_TO_I32_MAX`]
impl_prim_int!(type=i32, promoted_type=Self);
impl_prim_int!(type=i64, promoted_type=Self);
impl_prim_int!(type=i128, promoted_type=Self);

// isize can be i16, i132, or i64. Using i64 since it work for all cases
impl_prim_int!(type=isize, promoted_type=i64);

#[sealed]
pub trait Key<const TABLE_MIN_VALUE: i128>:
    PrimInt + Eq + Hash + TryFrom<i128> + Debug + 'static
{
    fn key_index(&self) -> usize;
}

macro_rules! impl_key {
    ($prim_type:ty) => {
        #[sealed]
        impl<const TABLE_MIN_VALUE: i128> Key<TABLE_MIN_VALUE> for $prim_type {
            #[allow(clippy::cast_possible_truncation)]
            #[allow(clippy::cast_sign_loss)]
            #[inline]
            fn key_index(&self) -> usize {
                // NOTE: Table size will not exceed i32::MAX so cast to usize will not truncate
                // NOTE: No promotion happens for subtractions of unsigned types because `key >= TABLE_MIN_VALUE``
                // NOTE: Promotion _needed_ for {i8, i16, isize} because the difference could exceed $prim_type::MAX
                (<$prim_type>::as_promoted(*self) - <$prim_type>::i128_as_promoted(TABLE_MIN_VALUE))
                    as usize
            }
        }
    };
}

impl_key!(u8);
impl_key!(u16);
impl_key!(u32);
impl_key!(u64);
impl_key!(u128);
impl_key!(usize);
impl_key!(i8);
impl_key!(i16);
impl_key!(i32);
impl_key!(i64);
impl_key!(i128);
impl_key!(isize);

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
