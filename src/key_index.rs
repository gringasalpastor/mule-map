use sealed::sealed;

#[sealed]
#[doc(hidden)]
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
