use sealed::sealed;

#[sealed]
pub trait PrimInt: num_traits::PrimInt {
    type PromotedType; // Used for addition to avoid overflow
}

#[sealed]
impl PrimInt for u8 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for u16 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for u32 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for u64 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for u128 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for i8 {
    type PromotedType = i16;
}

#[sealed]
impl PrimInt for i16 {
    type PromotedType = i32;
}

#[sealed]
impl PrimInt for i32 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for i64 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for i128 {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for usize {
    type PromotedType = Self;
}

#[sealed]
impl PrimInt for isize {
    type PromotedType = Self;
}

use super::key_index::KeyIndex;
use std::fmt::Debug;
use std::hash::Hash;

pub trait Key<const TABLE_MIN_VALUE: i128>:
    PrimInt + Eq + Hash + TryFrom<i128> + KeyIndex<TABLE_MIN_VALUE> + Debug + 'static
{
}

impl<
    T: PrimInt + Eq + Hash + TryFrom<i128> + KeyIndex<TABLE_MIN_VALUE> + Debug + 'static,
    const TABLE_MIN_VALUE: i128,
> Key<TABLE_MIN_VALUE> for T
{
}
