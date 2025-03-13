use Entry::{Occupied, Vacant};
use num_traits::PrimInt;

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This enum is constructed from the entry method on [`crate::MuleMap`].
///
/// Analogous to [`std::collections::hash_map::Entry`]
pub enum Entry<'a, K: 'a, V: 'a> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

pub enum OccupiedEntry<'a, K: 'a, V: 'a> {
    HashMap(OccupiedHashMapEntry<'a, K, V>),
    Vec(OccupiedVecEntry<'a, K, V>),
}

pub enum VacantEntry<'a, K: 'a, V: 'a> {
    HashMap(VacantHashMapEntry<'a, K, V>),
    Vec(VacantVecEntry<'a, K, V>),
}

#[doc(hidden)]
pub struct OccupiedHashMapEntry<'a, K: 'a, V: 'a> {
    pub(crate) base: std::collections::hash_map::OccupiedEntry<'a, K, V>,
}

#[doc(hidden)]
pub struct OccupiedVecEntry<'a, K: 'a, V: 'a> {
    pub(crate) value: &'a mut Option<V>,
    pub(crate) key: K,
}

#[doc(hidden)]
pub struct VacantHashMapEntry<'a, K: 'a, V: 'a> {
    pub(crate) base: std::collections::hash_map::VacantEntry<'a, K, V>,
}

#[doc(hidden)]
pub struct VacantVecEntry<'a, K: 'a, V: 'a> {
    pub(crate) value: &'a mut Option<V>,
    pub(crate) key: K,
}

impl<'a, K, V> Entry<'a, K, V>
where
    K: PrimInt,
    V: PartialEq,
{
    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable reference to the
    /// value in the entry.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(3);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::Entry::or_insert`]
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty, and returns a
    /// mutable reference to the value in the entry.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert_with(|| 1 + 1);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::Entry::or_insert_with`]
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting, if empty, the result of the default function.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert_with_key(|key| key as usize + 1);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::Entry::or_insert_with_key`]
    #[inline]
    pub fn or_insert_with_key<F: FnOnce(K) -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => {
                let value = default(entry.key());
                entry.insert(value)
            }
        }
    }

    /// Returns this entry’s key.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// assert_eq!(mule_map.entry(5).key(), 5);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::Entry::key`]
    #[inline]
    pub fn key(&self) -> K {
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the map.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).and_modify(|e| *e += 1).or_insert(1);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::Entry::and_modify`]
    #[inline]
    #[allow(clippy::return_self_not_must_use)]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Occupied(mut entry) => {
                f(entry.get_mut());
                Occupied(entry)
            }
            Vacant(entry) => Vacant(entry),
        }
    }

    /// Sets the value of the entry, and returns an [`OccupiedEntry`].
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// let entry = mule_map.entry(5).insert_entry(10);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::Entry::insert_entry`]
    #[inline]
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            Vacant(entry) => entry.insert_entry(value),
        }
    }
}

impl<'a, K, V> OccupiedEntry<'a, K, V>
where
    K: PrimInt,
    V: PartialEq,
{
    /// Returns this entry’s key.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// assert_eq!(mule_map.entry(5).key(), 5);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::key`]
    #[inline]
    pub fn key(&self) -> K {
        match self {
            OccupiedEntry::HashMap(entry) => *entry.base.key(),
            OccupiedEntry::Vec(entry) => entry.key(),
        }
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// if let mule_map::Entry::Occupied(o) = mule_map.entry(5) {
    ///    o.remove_entry();
    /// }
    ///
    /// assert_eq!(mule_map.contains_key(5), false);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::remove_entry`]
    #[inline]
    pub fn remove_entry(self) -> (K, V)
    where
        V: Clone,
    {
        match self {
            OccupiedEntry::HashMap(entry) => entry.base.remove_entry(),
            OccupiedEntry::Vec(entry) => entry.remove_entry(),
        }
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// if let mule_map::Entry::Occupied(o) = mule_map.entry(5) {
    ///    assert_eq!(o.get(), &12);
    /// }
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::get`]
    #[inline]
    pub fn get(&self) -> &V {
        match self {
            OccupiedEntry::HashMap(entry) => entry.base.get(),
            OccupiedEntry::Vec(entry) => entry.get(),
        }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the [`OccupiedEntry`] which may outlive the destruction of the [`Entry`] value, see [`OccupiedEntry::into_mut`].
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// if let mule_map::Entry::Occupied(mut o) = mule_map.entry(5) {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(o.get(), &22);
    ///     *o.get_mut() += 2;
    /// }
    /// assert_eq!(mule_map.get(5), Some(&24));
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::get_mut`]
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        match self {
            OccupiedEntry::HashMap(entry) => entry.base.get_mut(),
            OccupiedEntry::Vec(entry) => entry.get_mut(),
        }
    }

    /// Converts the [`OccupiedEntry`] into a mutable reference to the value in the entry with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the [`OccupiedEntry`], see [`OccupiedEntry::get_mut`].
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// if let mule_map::Entry::Occupied(mut o) = mule_map.entry(5) {
    ///     *o.into_mut() += 10;
    /// }
    /// assert_eq!(mule_map.get(5), Some(&22));
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::into_mut`]
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        match self {
            OccupiedEntry::HashMap(entry) => {
                let result = entry.base.into_mut();
                result
            }
            OccupiedEntry::Vec(entry) => entry.into_mut(),
        }
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// if let mule_map::Entry::Occupied(mut o) = mule_map.entry(5) {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    /// assert_eq!(mule_map.get(5), Some(&15));
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::insert`]
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        match self {
            OccupiedEntry::HashMap(entry) => entry.base.insert(value),
            OccupiedEntry::Vec(entry) => entry.insert(value),
        }
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// mule_map.entry(5).or_insert(12);
    /// if let mule_map::Entry::Occupied(mut o) = mule_map.entry(5) {
    ///     assert_eq!(o.remove(), 12);
    /// }
    /// assert_eq!(mule_map.contains_key(5), false);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::OccupiedEntry::remove`]
    #[inline]
    pub fn remove(self) -> V
    where
        V: Clone,
    {
        match self {
            OccupiedEntry::HashMap(entry) => entry.base.remove(),
            OccupiedEntry::Vec(entry) => entry.remove(),
        }
    }
}

impl<'a, K, V> OccupiedVecEntry<'a, K, V>
where
    K: PrimInt,
{
    #[inline]
    pub(crate) fn key(&self) -> K {
        self.key
    }
    #[inline]
    pub(crate) fn remove_entry(self) -> (K, V) {
        (
            self.key,
            self.value.take().expect("Value should be occupied."),
        )
    }
    #[inline]
    pub(crate) fn get(&self) -> &V {
        self.value.as_ref().expect("Value should be occupied.")
    }
    #[inline]
    pub(crate) fn get_mut(&mut self) -> &mut V {
        self.value.as_mut().expect("Value should be occupied.")
    }
    #[inline]
    pub(crate) fn into_mut(self) -> &'a mut V {
        self.value.as_mut().expect("Value should be occupied.")
    }
    #[inline]
    pub(crate) fn insert(&mut self, value: V) -> V {
        let mut value = value;
        std::mem::swap(&mut value, self.get_mut());
        value
    }
    #[inline]
    pub(crate) fn remove(self) -> V {
        self.value.take().expect("Value should be occupied.")
    }
}

impl<'a, K, V> VacantEntry<'a, K, V>
where
    K: PrimInt,
{
    /// Returns this entry’s key.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// assert_eq!(mule_map.entry(5).key(), 5);
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::VacantEntry::key`]
    #[inline]
    pub fn key(&self) -> K {
        match self {
            VacantEntry::HashMap(entry) => *entry.base.key(),
            VacantEntry::Vec(entry) => entry.key(),
        }
    }

    /// Sets the value of the entry with the VacantEntry’s key, and returns a mutable reference to it.
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// if let mule_map::Entry::Vacant(o) = mule_map.entry(5) {
    ///     o.insert(37);
    /// }
    /// assert_eq!(mule_map.get(5), Some(&37));
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::VacantEntry::insert`]
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        match self {
            VacantEntry::HashMap(entry) => entry.base.insert(value),
            VacantEntry::Vec(entry) => entry.insert(value),
        }
    }

    /// Sets the value of the entry with the VacantEntry’s key, and returns an [`OccupiedEntry`].
    ///
    /// # Example
    /// ```
    /// let mut mule_map = mule_map::MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
    /// if let mule_map::Entry::Vacant(o) = mule_map.entry(5) {
    ///     o.insert_entry(37);
    /// }
    /// assert_eq!(mule_map.get(5), Some(&37));
    /// ```
    ///
    /// Analogous to [`std::collections::hash_map::VacantEntry::insert_entry`]
    #[inline]
    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        match self {
            VacantEntry::HashMap(entry) => OccupiedEntry::HashMap(OccupiedHashMapEntry {
                base: entry.base.insert_entry(value),
            }),
            VacantEntry::Vec(entry) => entry.insert_entry(value),
        }
    }
}

impl<'a, K, V> VacantVecEntry<'a, K, V>
where
    K: PrimInt,
{
    #[inline]
    pub(crate) fn key(&self) -> K {
        self.key
    }

    #[inline]
    pub(crate) fn insert(self, value: V) -> &'a mut V {
        self.value.insert(value)
    }

    #[inline]
    pub(crate) fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
        _ = self.value.insert(value);

        OccupiedEntry::Vec(OccupiedVecEntry {
            value: self.value,
            key: self.key,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::MuleMap;

    #[test]
    fn test_entry() {
        let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher>::new();
        assert_eq!(mule_map.entry(5).and_modify(|e| *e += 1).or_insert(1), &1);
        assert_eq!(mule_map.entry(5).and_modify(|e| *e += 1).or_insert(1), &2);
    }
}
