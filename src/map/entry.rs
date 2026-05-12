//! Code for inserting elements and the entry pattern.

use crate::{
    table::{EmptyMut, NoNodeMut, PresentMut},
    Prefix,
};

/// A mutable view into a single entry in a map, which may either be vacant or occupied.
pub enum Entry<'a, P, T> {
    /// The entry is not present in the tree.
    Vacant(VacantEntry<'a, P, T>),
    /// The entry is already present in the tree.
    Occupied(OccupiedEntry<'a, P, T>),
}

/// A mutable view into a missing entry. The information within this structure describes a path
/// towards that missing node, and how to insert it.
pub struct VacantEntry<'a, P, T> {
    loc: Result<EmptyMut<'a, T>, NoNodeMut<'a, T>>,
    count: &'a mut usize,
    prefix: P,
}

impl<'a, P, T> VacantEntry<'a, P, T> {
    pub(super) fn empty(loc: EmptyMut<'a, T>, count: &'a mut usize, prefix: P) -> Self {
        Self {
            loc: Ok(loc),
            count,
            prefix,
        }
    }
    pub(super) fn no_node(loc: NoNodeMut<'a, T>, count: &'a mut usize, prefix: P) -> Self {
        Self {
            loc: Err(loc),
            count,
            prefix,
        }
    }
}

/// A mutable view into an occupied entry. An occupied entry represents a node that is already
/// present on the tree.
pub struct OccupiedEntry<'a, P, T> {
    loc: PresentMut<'a, T>,
    count: &'a mut usize,
    prefix: P,
}

impl<'a, P, T> OccupiedEntry<'a, P, T>
where
    P: Prefix,
{
    pub(super) fn new(loc: PresentMut<'a, T>, count: &'a mut usize, prefix: P) -> Self {
        let prefix = P::from_repr_len(prefix.mask(), prefix.prefix_len());
        Self { loc, count, prefix }
    }
}

impl<P: Prefix, T> Entry<'_, P, T> {
    /// Get the value if it exists
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).get(), Some(&1));
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).get(), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get(&self) -> Option<&T> {
        match self {
            Entry::Vacant(_) => None,
            Entry::Occupied(e) => Some(e.get()),
        }
    }

    /// Get the value if it exists
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// pm.entry("192.168.1.0/24".parse()?).get_mut().map(|x| *x += 1);
    /// pm.entry("192.168.2.0/24".parse()?).get_mut().map(|x| *x += 1);
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&2));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_mut(&mut self) -> Option<&mut T> {
        match self {
            Entry::Vacant(_) => None,
            Entry::Occupied(e) => {
                // Safety: internal_idx points to an initialized cell (see OccupiedEntry::new)
                Some(e.get_mut())
            }
        }
    }

    /// get the key of the current entry
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).key(), &"192.168.1.0/24".parse()?);
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).key(), &"192.168.2.0/24".parse()?);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn key(&self) -> &P {
        match self {
            Entry::Vacant(e) => &e.prefix,
            Entry::Occupied(e) => e.key(),
        }
    }
}

impl<'a, P, T> Entry<'a, P, T>
where
    P: Prefix,
{
    /// Replace the current entry, and return the entry that was stored before.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits masked out by the prefix length are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    ///
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).insert(10), Some(1));
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).insert(20), None);
    ///
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&10));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), Some(&20));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// Host bits from the `entry` argument are not preserved:
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.entry("192.168.1.2/24".parse()?).insert(2);
    /// assert_eq!(
    ///     pm.get_key_value(&"192.168.1.0/24".parse()?),
    ///     Some(("192.168.1.0/24".parse()?, &2))
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn insert(self, v: T) -> Option<T> {
        match self {
            Entry::Vacant(e) => {
                e._insert(v);
                None
            }
            Entry::Occupied(e) => Some(e.insert(v)),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns a mutable
    /// reference to the value in the entry.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    ///
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).or_insert(10), &1);
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).or_insert(20), &20);
    ///
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&1));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), Some(&20));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// Host bits from an existing matching prefix are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.entry("192.168.1.2/24".parse()?).or_insert(2);
    /// assert_eq!(
    ///     pm.get_key_value(&"192.168.1.0/24".parse()?),
    ///     Some(("192.168.1.0/24".parse()?, &1))
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn or_insert(self, default: T) -> &'a mut T {
        match self {
            Entry::Vacant(e) => e._insert(default).1,
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    ///
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).or_insert_with(|| 10), &1);
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).or_insert_with(|| 20), &20);
    ///
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&1));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), Some(&20));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// Host bits from an existing matching prefix are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.entry("192.168.1.2/24".parse()?).or_insert_with(|| 2);
    /// assert_eq!(
    ///     pm.get_key_value(&"192.168.1.0/24".parse()?),
    ///     Some(("192.168.1.0/24".parse()?, &1))
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn or_insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        match self {
            Entry::Vacant(e) => e._insert(default()).1,
            Entry::Occupied(e) => e.into_mut(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts into the
    /// map.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).and_modify(|x| *x += 1).get(), Some(&2));
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).and_modify(|x| *x += 1).get(), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// Host bits from an existing matching prefix are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.entry("192.168.1.2/24".parse()?).and_modify(|x| *x += 1);
    /// assert_eq!(
    ///     pm.get_key_value(&"192.168.1.0/24".parse()?),
    ///     Some(("192.168.1.0/24".parse()?, &2))
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[inline(always)]
    pub fn and_modify<F: FnOnce(&mut T)>(self, f: F) -> Self {
        match self {
            Entry::Vacant(e) => Entry::Vacant(e),
            Entry::Occupied(mut e) => {
                f(e.get_mut());
                Entry::Occupied(e)
            }
        }
    }
}

impl<'a, P, T> Entry<'a, P, T>
where
    P: Prefix,
    T: Default,
{
    /// Ensures a value is in the entry by inserting the default value if empty, and returns a
    /// mutable reference to the value in the entry.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    ///
    /// assert_eq!(pm.entry("192.168.1.0/24".parse()?).or_default(), &1);
    /// assert_eq!(pm.entry("192.168.2.0/24".parse()?).or_default(), &0);
    ///
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&1));
    /// assert_eq!(pm.get(&"192.168.2.0/24".parse()?), Some(&0));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    ///
    /// Host bits from an existing matching prefix are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.1/24".parse()?, 1);
    /// pm.entry("192.168.1.2/24".parse()?).or_default();
    /// assert_eq!(
    ///     pm.get_key_value(&"192.168.1.0/24".parse()?),
    ///     Some(("192.168.1.0/24".parse()?, &1))
    /// );
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    #[allow(clippy::unwrap_or_default)]
    #[inline(always)]
    pub fn or_default(self) -> &'a mut T {
        self.or_insert_with(Default::default)
    }
}

impl<'a, P, T> VacantEntry<'a, P, T>
where
    P: Prefix,
{
    fn _insert(self, v: T) -> (P, &'a mut T) {
        let Self { loc, count, prefix } = self;
        *count += 1;
        let r = match loc {
            Ok(empty_mut) => empty_mut.insert(v),
            Err(no_node_mut) => {
                no_node_mut.insert_path_and_data(prefix.repr(), prefix.prefix_len() as u32, v)
            }
        };
        let computed_prefix = r.prefix(prefix.repr());
        let val_ref = r.get_mut();
        (computed_prefix, val_ref)
    }
}

impl<P: Prefix, T> OccupiedEntry<'_, P, T> {
    /// Gets a reference to the key in the entry. This is the key that is currently stored, and not
    /// the key that was used in the insert.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// match pm.entry("192.168.1.1/24".parse()?) {
    ///     Entry::Occupied(e) => assert_eq!(e.key(), &"192.168.1.0/24".parse()?),
    ///     Entry::Vacant(_) => unreachable!(),
    /// }
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn key(&self) -> &P {
        &self.prefix
    }

    /// Gets a reference to the value in the entry.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Occupied(e) => assert_eq!(e.get(), &1),
    ///     Entry::Vacant(_) => unreachable!(),
    /// }
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get(&self) -> &T {
        self.loc.get()
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// Prefixes are not stored verbatim. They are reconstructed from the trie position, so host
    /// bits masked out by the prefix length are not preserved.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Occupied(mut e) => *e.get_mut() += 1,
    ///     Entry::Vacant(_) => unreachable!(),
    /// }
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&2));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn get_mut(&mut self) -> &mut T {
        self.loc.as_mut()
    }

    /// Insert a new value into the entry, returning the old value.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, _> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Occupied(mut e) => assert_eq!(e.insert(10), 1),
    ///     Entry::Vacant(_) => unreachable!(),
    /// }
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&10));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert(self, v: T) -> T {
        self.loc.replace(v)
    }

    /// Remove the current value and return it. Empty trie nodes may be left in place (the same
    /// effect as `PrefixMap::remove_keep_tree`).
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, i32> = PrefixMap::new();
    /// pm.insert("192.168.1.0/24".parse()?, 1);
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Occupied(mut e) => assert_eq!(e.remove(), 1),
    ///     Entry::Vacant(_) => unreachable!(),
    /// }
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), None);
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn remove(self) -> T {
        *self.count -= 1;
        self.loc.take()
    }
}

impl<'a, P, T> OccupiedEntry<'a, P, T> {
    /// Converts this occupied entry into a mutable reference to the stored value.
    pub fn into_mut(self) -> &'a mut T {
        self.loc.get_mut()
    }
}

impl<P, T> VacantEntry<'_, P, T> {
    /// Gets a reference to the key in the entry.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, i32> = PrefixMap::new();
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Vacant(e) => assert_eq!(e.key(), &"192.168.1.0/24".parse()?),
    ///     Entry::Occupied(_) => unreachable!(),
    /// }
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn key(&self) -> &P {
        &self.prefix
    }
}

impl<'a, P, T> VacantEntry<'a, P, T>
where
    P: Prefix,
{
    /// Get a mutable reference to the value. If the value is yet empty, set it to the given default
    /// value.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, i32> = PrefixMap::new();
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Vacant(mut e) => assert_eq!(e.insert(10), &10),
    ///     Entry::Occupied(_) => unreachable!(),
    /// }
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&10));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert(self, default: T) -> &'a mut T {
        self._insert(default).1
    }

    /// Get a mutable reference to the value. If the value is yet empty, set it to the return value
    /// from the given function.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, i32> = PrefixMap::new();
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Vacant(mut e) => assert_eq!(e.insert_with(|| 10), &10),
    ///     Entry::Occupied(_) => unreachable!(),
    /// }
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&10));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn insert_with<F: FnOnce() -> T>(self, default: F) -> &'a mut T {
        self._insert(default()).1
    }
}

impl<'a, P, T> VacantEntry<'a, P, T>
where
    P: Prefix,
    T: Default,
{
    /// Get a mutable reference to the value. If the value is yet empty, set it to the default value
    /// using `Default::default()`.
    ///
    /// ```
    /// # use prefix_trie::*;
    /// use prefix_trie::map::Entry;
    /// # #[cfg(feature = "ipnet")]
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut pm: PrefixMap<ipnet::Ipv4Net, i32> = PrefixMap::new();
    /// match pm.entry("192.168.1.0/24".parse()?) {
    ///     Entry::Vacant(e) => assert_eq!(e.default(), &0),
    ///     Entry::Occupied(_) => unreachable!(),
    /// }
    /// assert_eq!(pm.get(&"192.168.1.0/24".parse()?), Some(&0));
    /// # Ok(())
    /// # }
    /// # #[cfg(not(feature = "ipnet"))]
    /// # fn main() {}
    /// ```
    pub fn default(self) -> &'a mut T {
        self._insert(Default::default()).1
    }
}
