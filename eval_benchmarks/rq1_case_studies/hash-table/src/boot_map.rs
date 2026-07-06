use crate::svec::SVec as Vec;

#[derive(Clone, Copy)]
struct Fraction {
    dividend: usize,
    divisor: usize,
}

pub struct HashMap<T, K = usize> {
    /// The current number of entries in the table
    num_entries: usize,
    /// The max load factor, expressed as a fraction
    max_load_factor: Fraction,
    /// The max load factor applied to the current table length:
    /// gives the threshold at which to resize the table.
    max_load: usize,
    /// [true] if we can't increase the size anymore.
    saturated: bool,
    /// The table itself
    slots: Vec<Option<(K, T)>>,
}

pub type Hash = usize;

/// A hash function for the keys.
pub fn hash_key<K: Copy + Into<usize>>(k: &K) -> Hash {
    (*k).into()
}

impl<T, K> HashMap<T, K>
where
    K: Copy + Eq + Into<usize>,
{
    /// Allocate a vector of slots of a given size.
    fn allocate_slots(mut slots: Vec<Option<(K, T)>>, mut n: usize) -> Vec<Option<(K, T)>> {
        while n > 0 {
            slots.push(None);
            n -= 1;
        }
        slots
    }

    /// Create a new table, with a given capacity
    fn new_with_capacity(capacity: usize, max_load_factor: Fraction) -> Self {
        let slots = HashMap::allocate_slots(Vec::new(), capacity);
        HashMap {
            num_entries: 0,
            max_load_factor,
            max_load: (capacity * max_load_factor.dividend) / max_load_factor.divisor,
            saturated: false,
            slots,
        }
    }

    pub fn new() -> Self {
        // For now we create a table with 32 slots and a max load factor of 4/5
        HashMap::new_with_capacity(
            32,
            Fraction {
                dividend: 4,
                divisor: 5,
            },
        )
    }

    pub fn clear(&mut self) {
        self.num_entries = 0;
        let slots = &mut self.slots;
        let mut i = 0;
        while i < slots.len() {
            slots.set(i, None);
            i += 1;
        }
    }

    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Auxiliary function to insert in the hashmap without triggering a resize
    fn insert_no_resize(&mut self, key: K, value: T) {
        let hash = hash_key(&key);
        let len = self.slots.len();
        let mut i = hash % len;
        let mut n = 0;
        loop {
            let slot = &mut self.slots[i];
            match slot {
                None => {
                    *slot = Some((key, value));
                    self.num_entries += 1;
                    return;
                }
                Some((ckey, cvalue)) => {
                    if *ckey == key {
                        *cvalue = value;
                        return;
                    }
                }
            }
            n += 1;
            if n == len {
                self.saturated = true;
                return;
            }
            i = if i + 1 == len { 0 } else { i + 1 };
        }
    }

    /// Insertion function.
    /// May trigger a resize of the hash table.
    pub fn insert(&mut self, key: K, value: T) {
        // Insert
        self.insert_no_resize(key, value);
        // Resize if necessary and if we're not saturated
        if self.len() > self.max_load && !self.saturated {
            self.try_resize()
        }
    }

    /// The resize function, called if we need to resize the table after
    /// an insertion.
    fn try_resize(&mut self) {
        let max_usize = usize::MAX;
        let capacity = self.slots.len();
        // Checking that there won't be overflows by using the fact that, if m > 0:
        // n * m <= p <==> n <= p / m
        let n1 = max_usize / 2;
        if capacity <= n1 / self.max_load_factor.dividend {
            // Create a new table with a higher capacity
            let mut ntable = HashMap::new_with_capacity(capacity * 2, self.max_load_factor);

            // Move the elements to the new table
            HashMap::move_elements(&mut ntable, &mut self.slots);

            // Replace the current table with the new table
            self.slots = ntable.slots;
            self.max_load = ntable.max_load;
            self.saturated = false;
        } else {
            self.saturated = true;
        }
    }

    /// Auxiliary function called by [try_resize] to move all the elements
    /// from the table to a new table
    fn move_elements<'a>(ntable: &'a mut HashMap<T, K>, slots: &'a mut Vec<Option<(K, T)>>) {
        let mut i = 0;
        while i < slots.len() {
            if let Some((k, v)) = std::mem::replace(&mut slots[i], None) {
                ntable.insert_no_resize(k, v);
            }
            i += 1;
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    pub fn contains_key(&self, key: &K) -> bool {
        self.find_slot(key).is_some()
    }

    fn find_slot(&self, key: &K) -> Option<usize> {
        let hash = hash_key(key);
        let len = self.slots.len();
        let mut i = hash % len;
        let mut n = 0;
        loop {
            match &self.slots[i] {
                None => return None,
                Some((ckey, _)) => {
                    if *ckey == *key {
                        return Some(i);
                    }
                }
            }
            n += 1;
            if n == len {
                return None;
            }
            i = if i + 1 == len { 0 } else { i + 1 };
        }
    }

    /// We don't support borrows inside of enumerations for now, so we
    /// can't return an option...
    /// TODO: add support for that
    pub fn get<'a, 'k>(&'a self, key: &'k K) -> Option<&'a T> {
        let slot = self.find_slot(key)?;
        match &self.slots[slot] {
            None => None,
            Some((_, v)) => Some(v),
        }
    }

    // /// Same remark as for [get].
    // pub fn get_mut<'a, 'k>(&'a mut self, key: &'k K) -> Option<&'a mut T> {
    //     let hash = hash_key(key);
    //     let len = self.slots.len();
    //     let mut i = hash % len;
    //     let mut n = 0;
    //     loop {
    //         match &mut self.slots[i] {
    //             None => return None,
    //             Some((ckey, cvalue)) => {
    //                 if *ckey == *key {
    //                     return Some(cvalue);
    //                 }
    //             }
    //         }
    //         n += 1;
    //         if n == len {
    //             return None;
    //         }
    //         i = if i + 1 == len { 0 } else { i + 1 };
    //     }
    // }

    /// Same remark as for [get].
    pub fn remove(&mut self, key: &K) -> Option<T> {
        let hash = hash_key(key);
        let len = self.slots.len();
        let mut i = hash % len;
        let mut n = 0;
        loop {
            match &self.slots[i] {
                None => return None,
                Some((ckey, _)) if *ckey == *key => break,
                _ => {}
            }
            n += 1;
            if n == len {
                return None;
            }
            i = if i + 1 == len { 0 } else { i + 1 };
        }

        let removed = std::mem::replace(&mut self.slots[i], None);
        let (_, value) = removed?;
        self.num_entries -= 1;

        // Reinsert the following cluster to preserve probe chains.
        let mut j = if i + 1 == len { 0 } else { i + 1 };
        loop {
            let entry = std::mem::replace(&mut self.slots[j], None);
            match entry {
                None => break,
                Some((k, v)) => {
                    self.num_entries -= 1;
                    self.insert_no_resize(k, v);
                }
            }
            j = if j + 1 == len { 0 } else { j + 1 };
        }

        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::HashMap;

    #[test]
    fn insert_get_contains_and_len() {
        let mut map = HashMap::<i32>::new();
        assert_eq!(map.len(), 0);
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        assert_eq!(map.len(), 3);
        assert!(map.contains_key(&1));
        assert!(map.contains_key(&2));
        assert!(!map.contains_key(&4));
        assert_eq!(*map.get(&1).unwrap(), 10);
        assert_eq!(*map.get(&2).unwrap(), 20);
        assert_eq!(map.get(&4), None);
    }

    #[test]
    fn insert_updates_existing_key() {
        let mut map = HashMap::<i32>::new();
        map.insert(5, 50);
        assert_eq!(map.len(), 1);
        map.insert(5, 55);
        assert_eq!(map.len(), 1);
        assert_eq!(*map.get(&5).unwrap(), 55);
    }

    #[test]
    // fn get_mut_updates_value() {
    //     let mut map = HashMap::<i32>::new();
    //     map.insert(7, 70);
    //     if let Some(v) = map.get_mut(&7) {
    //         *v = 77;
    //     }
    //     assert_eq!(*map.get(&7).unwrap(), 77);
    // }

    #[test]
    fn linear_probing_handles_collisions_and_wraps() {
        let mut map = HashMap::<i32>::new();
        // Capacity is 32; these keys all hash to index 0.
        map.insert(0, 1);
        map.insert(32, 2);
        map.insert(64, 3);
        assert_eq!(*map.get(&0).unwrap(), 1);
        assert_eq!(*map.get(&32).unwrap(), 2);
        assert_eq!(*map.get(&64).unwrap(), 3);
    }

    #[test]
    fn remove_preserves_probe_chain() {
        let mut map = HashMap::<i32>::new();
        map.insert(0, 1);
        map.insert(32, 2);
        map.insert(64, 3);
        assert_eq!(map.len(), 3);
        assert_eq!(map.remove(&32), Some(2));
        assert_eq!(map.len(), 2);
        assert_eq!(*map.get(&0).unwrap(), 1);
        assert_eq!(*map.get(&64).unwrap(), 3);
        assert_eq!(map.get(&32), None);
    }

    #[test]
    fn clear_resets_table() {
        let mut map = HashMap::<i32>::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.clear();
        assert_eq!(map.len(), 0);
        assert!(!map.contains_key(&1));
        assert_eq!(map.get(&1), None);
    }

    #[test]
    fn resize_keeps_elements() {
        let mut map = HashMap::<i32>::new();
        let mut i = 0;
        while i < 40 {
            map.insert(i, (i as i32) * 10);
            i += 1;
        }
        assert_eq!(map.len(), 40);
        let mut j = 0;
        while j < 40 {
            assert_eq!(*map.get(&j).unwrap(), (j as i32) * 10);
            j += 1;
        }
    }
}
