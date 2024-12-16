use crate::Entry::{Occupied, Vacant};
use num_traits::PrimInt;

pub enum Entry<'a, K: 'a, V: 'a, const ZERO_IS_SENTINEL: bool> {
    Occupied(OccupiedEntry<'a, K, V, ZERO_IS_SENTINEL>),
    Vacant(VacantEntry<'a, K, V, ZERO_IS_SENTINEL>),
}

pub enum OccupiedEntry<'a, K: 'a, V: 'a, const ZERO_IS_SENTINEL: bool> {
    HashMap(OccupiedHashMapEntry<'a, K, V>),
    Vec(OccupiedVecEntry<'a, K, V, ZERO_IS_SENTINEL>),
}

pub enum VacantEntry<'a, K: 'a, V: 'a, const ZERO_IS_SENTINEL: bool> {
    HashMap(VacantHashMapEntry<'a, K, V>),
    Vec(VacantVecEntry<'a, K, V, ZERO_IS_SENTINEL>),
}

pub struct OccupiedHashMapEntry<'a, K: 'a, V: 'a> {
    pub(crate) base: std::collections::hash_map::OccupiedEntry<'a, K, V>,
}

pub struct OccupiedVecEntry<'a, K: 'a, V: 'a, const ZERO_IS_SENTINEL: bool> {
    pub(crate) value: &'a mut V,
    pub(crate) validity: &'a mut bool,
    pub(crate) key: K,
}

pub struct VacantHashMapEntry<'a, K: 'a, V: 'a> {
    pub(crate) base: std::collections::hash_map::VacantEntry<'a, K, V>,
}

pub struct VacantVecEntry<'a, K: 'a, V: 'a, const ZERO_IS_SENTINEL: bool> {
    pub(crate) value: &'a mut V,
    pub(crate) validity: &'a mut bool,
    pub(crate) key: K,
}

impl<'a, K, V, const ZERO_IS_SENTINEL: bool> Entry<'a, K, V, ZERO_IS_SENTINEL>
where
    K: PrimInt,
    V: std::default::Default,
{
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }
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
    #[inline]
    pub fn key(&self) -> K {
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }
    #[inline]
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

    //Not till rust 1.83.0
    // pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
    //     match self {
    //         Occupied(mut entry) => {
    //             entry.insert(value);
    //             entry
    //         }
    //         Vacant(entry) => entry.insert_entry(value),
    //     }
    // }
}

impl<'a, K, V, const ZERO_IS_SENTINEL: bool> OccupiedEntry<'a, K, V, ZERO_IS_SENTINEL>
where
    K: PrimInt,
    V: std::default::Default,
{
    #[inline]
    pub fn key(&self) -> K {
        match self {
            OccupiedEntry::HashMap(ref entry) => *entry.base.key(),
            OccupiedEntry::Vec(ref entry) => entry.key(),
        }
    }
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
    #[inline]
    pub fn get(&self) -> &V {
        match self {
            OccupiedEntry::HashMap(ref entry) => entry.base.get(),
            OccupiedEntry::Vec(ref entry) => entry.get(),
        }
    }
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        match self {
            OccupiedEntry::HashMap(ref mut entry) => entry.base.get_mut(),
            OccupiedEntry::Vec(ref mut entry) => entry.get_mut(),
        }
    }
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        match self {
            OccupiedEntry::HashMap(entry) => entry.base.into_mut(),
            OccupiedEntry::Vec(entry) => entry.into_mut(),
        }
    }
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        match self {
            OccupiedEntry::HashMap(ref mut entry) => entry.base.insert(value),
            OccupiedEntry::Vec(ref mut entry) => entry.insert(value),
        }
    }
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

impl<'a, K, V, const ZERO_IS_SENTINEL: bool> OccupiedVecEntry<'a, K, V, ZERO_IS_SENTINEL>
where
    K: PrimInt,
    V: std::default::Default,
{
    #[inline]
    pub fn key(&self) -> K {
        self.key
    }
    #[inline]
    pub fn remove_entry(self) -> (K, V)
    where
        V: Clone,
    {
        if ZERO_IS_SENTINEL {
            *self.value = Default::default();
            (self.key, self.value.clone())
        } else {
            *self.validity = false;
            (self.key, self.value.clone())
        }
    }
    #[inline]
    pub fn get(&self) -> &V {
        self.value
    }
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.value
    }
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.value
    }
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        let mut value = value;
        std::mem::swap(&mut value, self.get_mut());
        value
    }
    #[inline]
    pub fn remove(self) -> V
    where
        V: Clone,
    {
        if ZERO_IS_SENTINEL {
            let value = self.value.clone();
            *self.value = Default::default();
            value
        } else {
            *self.validity = false;
            self.value.clone()
        }
    }
}

impl<'a, K, V, const ZERO_IS_SENTINEL: bool> VacantEntry<'a, K, V, ZERO_IS_SENTINEL>
where
    K: PrimInt,
{
    #[inline]
    pub fn key(&self) -> K {
        match self {
            VacantEntry::HashMap(ref entry) => *entry.base.key(),
            VacantEntry::Vec(ref entry) => entry.key(),
        }
    }
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        match self {
            VacantEntry::HashMap(entry) => entry.base.insert(value),
            VacantEntry::Vec(entry) => entry.insert(value),
        }
    }

    //Not till rust 1.83.0
    // pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
    //     match self {
    //         VacantEntry::HashMap(entry) => entry::OccupiedEntry {
    //             base: entry.base.insert_entry(value),
    //         },
    //         VacantEntry::Vec(entry) => entry.insert_entry(value),
    //     }
    // }
}

impl<'a, K, V, const ZERO_IS_SENTINEL: bool> VacantVecEntry<'a, K, V, ZERO_IS_SENTINEL>
where
    K: PrimInt,
{
    #[inline]
    pub fn key(&self) -> K {
        self.key
    }
    #[inline]
    pub fn insert(self, value: V) -> &'a mut V {
        if ZERO_IS_SENTINEL {
            *self.value = value;
            self.value
        } else {
            *self.validity = true;
            *self.value = value;
            self.value
        }
    }

    //Not till rust 1.83.0
    // pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, K, V> {
    //     *self.value = value;
    //     OccupiedVecEntry {
    //         value: &mut self.value,
    //         key: self.key,
    //         sentinel_value: &self.sentinel_value,
    //     }
    // }
}

#[cfg(test)]
mod tests {
    // use crate::MuleMap;
    use crate::{MuleMap, ZERO_SENTINEL};

    #[test]
    fn it_works() {
        let mut mule_map = MuleMap::<u32, usize, fnv_rs::FnvBuildHasher, { ZERO_SENTINEL }>::new();

        let entry = mule_map.entry(5);

        entry.and_modify(|e| *e += 1).or_insert(42);
        // println!("{:?}", mule_map.get(&5));
    }
}
