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
        MuleMap::<K, (), Hash, TABLE_MIN_VALUE, TABLE_SIZE>::check_bounds();

        eprintln!(
            "\ntest_index::<{:?}, {TABLE_MIN_VALUE:?}, {TABLE_SIZE:?}>({key:?})\n",
            std::any::type_name::<K>()
        );

        assert!(MuleMap::<K, (), Hash, TABLE_MIN_VALUE, TABLE_SIZE>::use_lookup_table(key));
        key.key_index()
    }

    const MAX_U8_SIZE: usize = u8::MAX as usize + 1;
    const MAX_U16_SIZE: usize = u16::MAX as usize + 1;
    const MAX_SIZE: usize = (i32::MAX as usize) + 1; // i32::MAX is largest allowed
    const MAX_INDEX: usize = i32::MAX as usize;

    #[test]
    fn check_table_range_unsigned() {
        macro_rules! check_key_range_from_0 {
            (type=$prim_type:ty, max_size=$max_size:expr) => {
                assert_eq!(test_index::<$prim_type, 0, $max_size>(<$prim_type>::MIN), 0);
                assert_eq!(
                    test_index::<$prim_type, 0, $max_size>(
                        <$prim_type>::try_from($max_size - 1).expect("")
                    ),
                    $max_size - 1
                );
            };
        }

        check_key_range_from_0!(type=u8, max_size=MAX_U8_SIZE); // (TABLE_MIN_VALUE=0, TABLE_SIZE=256)
        check_key_range_from_0!(type=u16, max_size=MAX_U16_SIZE); // (TABLE_MIN_VALUE=0, TABLE_SIZE=65536)
        check_key_range_from_0!(type=u32, max_size=MAX_SIZE ); // (TABLE_MIN_VALUE=0, TABLE_SIZE=2147483648)
        check_key_range_from_0!(type=u64, max_size=MAX_SIZE ); // (TABLE_MIN_VALUE=0, TABLE_SIZE=2147483648)
        check_key_range_from_0!(type=u128, max_size=MAX_SIZE ); // (TABLE_MIN_VALUE=0, TABLE_SIZE=2147483648)
        check_key_range_from_0!(type=usize, max_size=MAX_SIZE ); // (TABLE_MIN_VALUE=0, TABLE_SIZE=2147483648)

        macro_rules! check_key_range_from_upper {
            (type=$prim_type:ty, max_size=$max_size:expr, table_min_value=$table_min_value:expr) => {
                assert_eq!(
                    test_index::<
                        $prim_type,
                        { $table_min_value },
                        {
                            ((<$prim_type>::MAX as i128 + 1)
                                .checked_sub($table_min_value)
                                .expect("table_min_value < $prim_type>::MAX") as usize)
                        },
                    >(
                        <$prim_type>::try_from($table_min_value)
                            .expect("table_min_value fits in $prim_type")
                    ),
                    0
                );
                assert_eq!(
                    test_index::<
                        $prim_type,
                        { $table_min_value },
                        { (<$prim_type>::MAX as i128 + 1 - $table_min_value) as usize },
                    >(<$prim_type>::MAX),
                    (<$prim_type>::MAX as i128 - $table_min_value) as usize
                );
            };
        }
        #[allow(clippy::cast_sign_loss)]
        #[allow(clippy::cast_lossless)]
        {
            check_key_range_from_upper!(type=u8, max_size=MAX_U8_SIZE, table_min_value= 100); // (TABLE_MIN_VALUE=100, TABLE_SIZE=156)
            check_key_range_from_upper!(type=u16, max_size=MAX_U16_SIZE, table_min_value= 100); // (TABLE_MIN_VALUE=100, TABLE_SIZE=65436)
            check_key_range_from_upper!(type=u32, max_size=MAX_SIZE, table_min_value= u32::MAX as i128 - (MAX_SIZE - 1)  as i128); // (TABLE_MIN_VALUE=2147483648, TABLE_SIZE=2147483648)
            check_key_range_from_upper!(type=u64, max_size=MAX_SIZE, table_min_value= u64::MAX as i128 - (MAX_SIZE - 1)  as i128); // (TABLE_MIN_VALUE=18446744071562067968, TABLE_SIZE=2147483648)
            check_key_range_from_upper!(type=usize, max_size=MAX_SIZE, table_min_value= usize::MAX as i128 - (MAX_SIZE - 1)  as i128); // (TABLE_MIN_VALUE=18446744071562067968, TABLE_SIZE=2147483648)
        }

        // Test u128 separately because TABLE_MIN_VALUE is at most i128::MAX, and we can't use use it's upper range
        // (TABLE_MIN_VALUE=170141183460469231731687303713736622080, TABLE_SIZE=2147483648)
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
        // // i8
        // assert_eq!(
        //     test_index::<i8, { i8::MIN as i128 }, MAX_U8_SIZE>(i8::MIN),
        //     0
        // );
    }
}
