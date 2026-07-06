
use flux_rs::proven_externally;

use crate::alist::{AList, Assoc};
use crate::svec::SVec as Vec;

extern crate flux_core;

pub type Key = usize; // TODO: make this generic
pub type Hash = usize;

flux_rs::defs! {
    fn empty_between<T>(s: Vec<AList<T, int>>, l: int, r: int) -> bool;
    fn unique_keys<T>(s: Vec<AList<T, int>>) -> bool;
    fn keys_distributed_by_hash<T>(s: Vec<AList<T, int>>) -> bool;
    fn total_len<T>(s: Vec<AList<T, int>>) -> int;
    fn empties<T>(n : int) -> Vec<AList<T, int>>;
    fn absorb_bucket<T>(s: Vec<AList<T, int>>, b: AList<T, int>) -> Vec<AList<T,int>>;
    fn absorb_buckets<T>(s: Vec<AList<T, int>>, b: Vec<AList<T, int>>) -> Vec<AList<T,int>>;
    fn disjoint_with_list<T>(s: Vec<AList<T, int>>, l: AList<T, int>) -> bool;
    fn disjoint<T>(s1: Vec<AList<T, int>>, s2: Vec<AList<T, int>>) -> bool;

    fn hash(k: int) -> int {
        k
    }

    fn key_matches<T>(m: HashMap<T>, k: int, v: T) -> bool {
        aseq_key_matches(get(m.slots, hash(k) % len(m.slots)), k, v)
    }

    fn contains_key<T>(m: HashMap<T>, k: int) -> bool {
        aseq_contains_key(get(m.slots, hash(k) % len(m.slots)), k)
    }

    fn insert_or_replace<T>(m: Vec<AList<T, int>>, k: int, v: T) -> Vec<AList<T, int>> {
        let bucket_idx = hash(k) % len(m);
        let bucket = get(m, bucket_idx);
        let had_key = aseq_contains_key(bucket, k);
        set(
            m, 
            bucket_idx, 
            if had_key {
                aseq_set(bucket, k, v)
            } else {
                aseq_cons(k, v, bucket)
            }
        )
    }

    fn insert_or_replace_try_resize<T>(m: HashMap<T>, k: int, v: T) -> Vec<AList<T, int>> {
        let before_resize = insert_or_replace(m.slots, k, v);
        if total_len(before_resize) > m.max_load && !m.saturated && len(before_resize) <= (usize::MAX / 2) / m.max_load_factor.dividend {
            absorb_buckets(empties(2 * len(before_resize)), before_resize)
        }
        else {
            before_resize
        }
    }
}

/// A hash function for the keys.
/// Rk.: we use shared references because we anticipate on the generic
/// hash map version.
#[flux_rs::spec(fn(&Key[@k]) -> Hash[hash(k)])]
pub fn hash_key(k: &Key) -> Hash {
    // Do nothing for now, we might want to implement something smarter
    // in the future, or to call an external function (which will be
    // abstract): we don't need to reason about the hash function.
    *k
}

#[derive(Clone, Copy)]
#[flux_rs::refined_by(dividend: int, divisor: int)]
#[flux_rs::invariant(dividend != 0)]
#[flux_rs::invariant(divisor != 0)]
struct Fraction {
    #[flux_rs::field(usize[dividend])]
    dividend: usize,
    #[flux_rs::field(usize[divisor])]
    divisor: usize,
}

/// A hash map from [u64] to values
#[flux_rs::refined_by(
    num_entries: int, 
    max_load_factor: Fraction, 
    max_load: int, 
    saturated: bool, 
    slots: Vec<AList<T, int>>
)]
#[flux_rs::invariant(len(slots) > 0)]
#[flux_rs::invariant(unique_keys(slots))]
#[flux_rs::invariant(keys_distributed_by_hash(slots))]
#[flux_rs::invariant(num_entries == total_len(slots))]
#[flux_rs::invariant(max_load_factor.dividend < max_load_factor.divisor)]
#[flux_rs::invariant(len(slots) * max_load_factor.dividend >= max_load_factor.divisor)]
#[flux_rs::invariant(max_load == (len(slots) * max_load_factor.dividend) / max_load_factor.divisor)]
pub struct HashMap<T> {
    /// The current number of entries in the table
    #[flux_rs::field(usize[num_entries])]
    num_entries: usize,
    /// The max load factor, expressed as a fraction
    #[flux_rs::field(Fraction[max_load_factor])]
    max_load_factor: Fraction,
    /// The max load factor applied to the current table length:
    /// gives the threshold at which to resize the table.
    #[flux_rs::field(usize[max_load])]
    max_load: usize,
    /// [true] if we can't increase the size anymore.
    #[flux_rs::field(bool[saturated])]
    saturated: bool,
    /// The table itself
    #[flux_rs::field(Vec<AList<T>>[slots])]
    slots: Vec<AList<T>>,
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(capacity: usize { capacity > 0 && capacity * max_load_factor.dividend >= max_load_factor.divisor }, 
        max_load_factor: Fraction { max_load_factor.dividend < max_load_factor.divisor }, Key[@k]) -> HashMap<usize>[#res]
    ensures !contains_key(res, k),
            res == HashMap {
                num_entries: 0,
                max_load_factor: max_load_factor,
                max_load: (capacity * max_load_factor.dividend) / max_load_factor.divisor,
                saturated: false,
                slots: empties(capacity)
            }
)]
fn thm_new_with_capacity(capacity: usize, max_load_factor: Fraction, _k: Key) -> HashMap<usize> {
    HashMap::new_with_capacity(capacity, max_load_factor)
}

#[flux_rs::spec(fn(Key[@k]) -> HashMap<usize>[#res]
    ensures !contains_key(res, k)    
)]
fn thm_new(k: Key) -> HashMap<usize> {
    thm_new_with_capacity(32, Fraction { dividend: 4, divisor: 5 }, k);
    HashMap::new()
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(Key[@k], T[@val], AList<T>[@ls]) -> (AList<T>[#new_ls], bool[#ins])
    requires aseq_unique_keys(ls)
    ensures  aseq_key_matches(new_ls, k, val),
             aseq_keys_unchanged_except_k(ls, new_ls, k),
             aseq_len(new_ls) == aseq_len(ls) + if aseq_contains_key(ls, k) { 0 } else { 1 },
             aseq_unique_keys(new_ls)
)]
fn thm_insert_in_list<T>(key: Key, value: T, ls: AList<T>) -> (AList<T>, bool) {
    HashMap::insert_in_list(key, value, ls)
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(ntable: &mut HashMap<T>[@hm], AList<T>[@ls], Key[@k], T[@v])
    requires disjoint_with_list(hm.slots, ls),
             aseq_unique_keys(ls),
    ensures ntable: HashMap<T>[#new_hm],
            key_matches(new_hm, k, v) => key_matches(hm, k, v) || aseq_key_matches(ls, k, v),
            key_matches(hm, k, v) => key_matches(new_hm, k, v),
            aseq_key_matches(ls, k, v) => key_matches(new_hm, k, v),
            new_hm.num_entries == hm.num_entries + aseq_len(ls)

)]
fn thm_move_elements_from_list<T>(ntable: &mut HashMap<T>, mut ls: AList<T>, _k: Key, _v: T) {
    HashMap::move_elements_from_list(ntable, ls);
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(ntable: &mut HashMap<T>[@hm], slots: &mut Vec<AList<T>>[@s], Key[@k], T[@v])
    requires disjoint(hm.slots, s),
             unique_keys(s),
             keys_distributed_by_hash(s),
    ensures ntable: HashMap<T>[#new_hm],
            slots: Vec<AList<T>>[#new_s],
            key_matches(new_hm, k, v) => key_matches(hm, k, v) || aseq_key_matches(get(s, (k % len(s))), k, v),
            key_matches(hm, k, v) => key_matches(new_hm, k, v),
            aseq_key_matches(get(s, (k % len(s))), k, v) => key_matches(new_hm, k, v),
            new_hm.num_entries == hm.num_entries + total_len(s)

)]
fn thm_move_elements<'a, T>(ntable: &'a mut HashMap<T>, slots: &'a mut Vec<AList<T>>, _k: Key, _v: T) {
    HashMap::move_elements(ntable, slots);
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(m: &mut HashMap<T>[@hm], Key[@k], T[@v])
    ensures m : HashMap<T>[#nhm],
            nhm.max_load_factor == hm.max_load_factor,
            len(nhm.slots) == len(hm.slots),
            key_matches(nhm, k, v),
            nhm.num_entries == hm.num_entries + if contains_key(hm, k) { 0 } else { 1 }
)]
fn thm_insert_no_resize<T>(m: &mut HashMap<T>, k: Key, v: T) {
    m.insert_no_resize(k, v);
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(ntable: &mut HashMap<T>[@hm], Key[@k], T[@v], Key[@k2], T[@v2])
    requires k2 != k,
    ensures ntable: HashMap<T>[#new_hm],
            key_matches(new_hm, k, v),
            key_matches(hm, k2, v2) <=> key_matches(new_hm, k2, v2),
            new_hm.num_entries == hm.num_entries + if contains_key(hm, k) { 0 } else { 1 }
)]
fn thm_insert<T>(ntable: &mut HashMap<T>, key: Key, value: T, _key: Key, _value: T) {
    ntable.insert(key, value);
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(&Key[@k], AList<T>[@ls]) -> (AList<T>[#new_ls], Option<T>[#is_some])
    requires aseq_unique_keys(ls)
    ensures !aseq_contains_key(new_ls, k),
            aseq_keys_unchanged_except_k(ls, new_ls, k),
            aseq_len(new_ls) == aseq_len(ls) - if is_some { 1 } else { 0 }

)]
fn thm_remove_from_list<T>(key: &Key, ls: AList<T>) -> (AList<T>, Option<T>) {
    HashMap::remove_from_list(key, ls)
}

#[flux_rs::proven_externally]
#[flux_rs::spec(fn(m: &mut HashMap<T>[@hm], &Key[@k]) -> Option<T{v : contains_key(hm, k) => key_matches(hm, k, v) }>[#is_some]
    ensures m : HashMap<T>[#nhm],
            is_some == contains_key(hm, k),
            !contains_key(nhm, k),
            nhm.num_entries == hm.num_entries - if is_some { 1 } else { 0 }
)]
fn thm_remove<T>(m: &mut HashMap<T>, k: &Key) -> Option<T> {
    m.remove(k)
}

impl<T> HashMap<T> {
    /// Allocate a vector of slots of a given size.
    /// We would need a loop, but can't use loops for now...
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(Vec<AList<T>>[empty()], usize[@n]) -> Vec<AList<T>>[empties(n)])]
    fn allocate_slots(mut slots: Vec<AList<T>>, mut n: usize) -> Vec<AList<T>> {
        while n > 0 {
            slots.push(AList::Nil);
            n -= 1;
        }
        slots
    }

    /// Create a new table, with a given capacity
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(
        capacity: usize { capacity > 0 && capacity * max_load_factor.dividend >= max_load_factor.divisor }, 
        max_load_factor: Fraction { max_load_factor.dividend < max_load_factor.divisor }
    ) -> Self[HashMap {
        num_entries: 0,
        max_load_factor: max_load_factor,
        max_load: (capacity * max_load_factor.dividend) / max_load_factor.divisor,
        saturated: false,
        slots: empties(capacity)
    }])]
    fn new_with_capacity(capacity: usize, max_load_factor: Fraction) -> Self {
        // TODO: better to use `Vec::with_capacity(capacity)` instead
        // of `Vec::new()`
        let slots = HashMap::allocate_slots(Vec::new(), capacity);
        HashMap {
            num_entries: 0,
            max_load_factor,
            max_load: (capacity * max_load_factor.dividend) / max_load_factor.divisor,
            saturated: false,
            slots,
        }
    }

    #[flux_rs::spec(fn() -> Self[HashMap {
        num_entries: 0,
        max_load_factor: Fraction { dividend: 4, divisor: 5 },
        max_load: (32 * 4) / 5,
        saturated: false,
        slots: empties(32)
    }])]
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

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(s: &mut Self[@slf])
        ensures s : Self[HashMap {
            num_entries: 0,
            max_load_factor: slf.max_load_factor,
            max_load: slf.max_load,
            saturated: slf.saturated,
            slots: empties(len(slf.slots))
        }]
    )]
    pub fn clear(&mut self) {
        self.num_entries = 0;
        let mut i = 0;
        while i < self.slots.len() {
            self.slots.set(i, AList::Nil);
            i += 1;
        }
    }

    #[flux_rs::spec(fn(&Self[@slf]) -> usize[slf.num_entries])]
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Insert in a list.
    /// Return `true` if we inserted an element, `false` if we simply updated
    /// a value.
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(Key[@key], value: T[@val], AList<T>[@ls]) -> (AList<T>[#ls_res], bool[#inserted])
        ensures inserted  == !aseq_contains_key(ls, key),
                inserted  => ls_res == aseq_cons(key, val, ls),
                !inserted => ls_res == aseq_set(ls, key, val)
    )]
    fn insert_in_list(key: Key, value: T, ls: AList<T>) -> (AList<T>, bool) {
        let (lst, kv) = ls.replace_if_present(key, value);
        if let Some((k, v)) = kv {
            (AList::Cons(k, v, Box::new(lst)), true)
        } else {
            (lst, false)
        }
    }

    /// Auxiliary function to insert in the hashmap without triggering a resize
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(s: &mut Self[@slf], Key[@key], T[@value])
        ensures s : Self[#new_slf],
                new_slf.max_load == slf.max_load,
                new_slf.max_load_factor == slf.max_load_factor,
                new_slf.saturated == slf.saturated,
                new_slf.num_entries == slf.num_entries + if aseq_contains_key(get(slf.slots, hash(key) % len(slf.slots)), key) { 0 } else { 1 },
                new_slf.slots == insert_or_replace(slf.slots, key, value)
    )]
    fn insert_no_resize(&mut self, key: Key, value: T) {
        let hash = hash_key(&key);
        let hash_mod = hash % self.slots.len();
        // We may want to use slots[...] instead of get_mut...
        let ls = self.slots.take(hash_mod, AList::Nil);
        let (new_ls, inserted) = HashMap::insert_in_list(key, value, ls);
        self.slots.set(hash_mod, new_ls);
        if inserted {
            self.num_entries += 1;
        }
    }

    /// Insertion function.
    /// May trigger a resize of the hash table.
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(s: &mut Self[@slf], Key[@key], T[@val])
        ensures s : Self[#new_slf],
                new_slf.max_load_factor == slf.max_load_factor,
                new_slf.slots == insert_or_replace_try_resize(slf, key, val)
    )]
    pub fn insert(&mut self, key: Key, value: T) {
        // Insert
        self.insert_no_resize(key, value);
        // Resize if necessary and if we're not saturated
        if self.len() > self.max_load && !self.saturated {
            self.try_resize()
        }
    }

    /// The resize function, called if we need to resize the table after
    /// an insertion.
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(s: &mut Self[@slf])
        ensures s : Self[#new_slf],
                new_slf.num_entries == slf.num_entries && new_slf.max_load_factor == slf.max_load_factor,
                (len(slf.slots) <= (usize::MAX / 2) / slf.max_load_factor.dividend) => (
                    new_slf.slots == absorb_buckets(empties(2 * len(slf.slots)), slf.slots)
                ),
                (len(slf.slots)  > (usize::MAX / 2) / slf.max_load_factor.dividend) => (
                    new_slf.max_load == slf.max_load && new_slf.slots == slf.slots &&
                    new_slf.saturated == true
                )
    )]
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
        } else {
            self.saturated = true;
        }
    }

    /// Auxiliary function called by [try_resize] to move all the elements
    /// from the table to a new table
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(ntable: &mut HashMap<T>[@t], slots: &mut Vec<AList<T>>[@s])
        ensures ntable: HashMap<T>[#new_t],
                new_t.max_load == t.max_load,
                new_t.max_load_factor == t.max_load_factor,
                new_t.saturated == t.saturated,
                new_t.slots == absorb_buckets(t.slots, s),
                slots: Vec<AList<T>>[empties(len(s))],

    )]
    fn move_elements<'a>(ntable: &'a mut HashMap<T>, slots: &'a mut Vec<AList<T>>) {
        let mut i = 0;
        while i < slots.len() {
            // Move the elements out of the slot i
            let ls = slots.take(i, AList::Nil);
            // Move all those elements to the new table
            HashMap::move_elements_from_list(ntable, ls);
            // Do the same for slot i+1
            i += 1;
        }
    }

    /// Auxiliary function.
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(ntable: &mut HashMap<T>[@t], AList<T>[@ls])
        ensures ntable: HashMap<T>[#new_t],
                new_t.max_load == t.max_load,
                new_t.max_load_factor == t.max_load_factor,
                new_t.saturated == t.saturated,
                new_t.num_entries >= t.num_entries,
                new_t.num_entries <= t.num_entries + aseq_len(ls),
                new_t.slots == absorb_bucket(t.slots, ls)
    )]
    fn move_elements_from_list(ntable: &mut HashMap<T>, mut ls: AList<T>) {
        // As long as there are elements in the list, move them
        loop {
            match ls {
                AList::Nil => return, // We're done
                AList::Cons(k, v, tl) => {
                    // Insert the element in the new table
                    ntable.insert_no_resize(k, v);
                    // Move the elements out of the tail
                    ls = *tl;
                }
            }
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    #[flux_rs::spec(fn(&Self[@slf], &Key[@key]) -> bool[contains_key(slf, key)])]
    pub fn contains_key(&self, key: &Key) -> bool {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::contains_key_in_list(key, self.slots.get(hash_mod))
    }

    /// Returns `true` if the list contains a value for the specified key.
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(&Key[@k], &AList<T, Key>[@l]) -> bool[aseq_contains_key(l, k)])]
    pub fn contains_key_in_list(key: &Key, mut ls: &AList<T>) -> bool {
        loop {
            match ls {
                AList::Nil => return false,
                AList::Cons(ckey, _, tl) => {
                    if *ckey == *key {
                        return true;
                    } else {
                        ls = tl;
                    }
                }
            }
        }
    }

    /// We don't support borrows inside of enumerations for now, so we
    /// can't return an option...
    /// TODO: add support for that
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(&Key[@key], &AList<T>[@ls]) -> Option<&T{v : aseq_contains_key(ls, key) => aseq_key_matches(ls, key, v)}>[aseq_contains_key(ls, key)])]
    fn get_in_list<'a, 'k>(key: &'k Key, mut ls: &'a AList<T>) -> Option<&'a T> {
        while let AList::Cons(ckey, cvalue, tl) = ls {
            if *ckey == *key {
                return Some(cvalue);
            } else {
                ls = tl;
            }
        }
        None
    }

    #[flux_rs::spec(fn(&Self[@slf], &Key[@key]) -> Option<&T{v : contains_key(slf, key) => key_matches(slf, key, v)}>[contains_key(slf, key)])]
    pub fn get<'a, 'k>(&'a self, key: &'k Key) -> Option<&'a T> {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();
        HashMap::get_in_list(key, self.slots.get(hash_mod))
    }

    // /// Same remark as for [get].
    // pub fn get_mut<'a, 'k>(&'a mut self, key: &'k Key) -> Option<&'a mut T> {
    //     let hash = hash_key(key);
    //     let hash_mod = hash % self.slots.len();
    //     let ptr = self.slots.as_mut_ptr();
    //     unsafe {
    //         let mut ls = &mut *ptr.add(hash_mod);
    //         while let AList::Cons(ckey, cvalue, tl) = ls {
    //             if *ckey == *key {
    //                 return Some(cvalue);
    //             } else {
    //                 ls = tl;
    //             }
    //         }
    //     }
    //     None
    // }

    /// Remove an element from the list.
    /// Return the removed element.
    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(&Key[@k], AList<T>[@ls]) -> (AList<T>[#ls_res], Option<T{v : aseq_contains_key(ls, k) => aseq_key_matches(ls, k, v)}>[#is_some])
        ensures is_some  == aseq_contains_key(ls, k),
                is_some  => ls_res == aseq_remove_key(ls, k),
                !is_some => ls_res == ls
    )]
    fn remove_from_list(key: &Key, mut ls: AList<T>) -> (AList<T>, Option<T>) {
        match ls {
            AList::Nil => (AList::Nil, None),
            AList::Cons(ckey, cval, tl) => {
                if ckey == *key {
                    (*tl, Some(cval))
                } else {
                    let (rest, removed) = HashMap::remove_from_list(key, *tl);
                    (AList::Cons(ckey, cval, Box::new(rest)), removed)
                }
            }
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(s: &mut Self[@slf], &Key[@key]) -> Option<T{v : contains_key(slf, key) => key_matches(slf, key, v)}>[#is_some]
        ensures s : Self[#new_slf],
                is_some == aseq_contains_key(get(slf.slots, key % len(slf.slots)), key),
                new_slf.num_entries == slf.num_entries - if is_some { 1 } else { 0 },
                new_slf.max_load == slf.max_load,
                new_slf.max_load_factor == slf.max_load_factor,
                new_slf.saturated == slf.saturated,
                new_slf.slots == 
                    if is_some {
                        set(slf.slots, key % len(slf.slots), aseq_remove_key(get(slf.slots, key % len(slf.slots)), key))
                    } else {
                        slf.slots
                    }
    )]
    pub fn remove(&mut self, key: &Key) -> Option<T> {
        let hash = hash_key(key);
        let hash_mod = hash % self.slots.len();

        let ls = self.slots.take(hash_mod, AList::Nil);
        let (new_ls, x) = HashMap::remove_from_list(key, ls);
        self.slots.set(hash_mod, new_ls);
        match x {
            Option::None => Option::None,
            Option::Some(x) => {
                self.num_entries -= 1;
                Option::Some(x)
            }
        }
    }
}
