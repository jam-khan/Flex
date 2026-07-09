use std::ops::{Index, IndexMut};

flux_rs::defs! {
    opaque sort OVec<T>;
    fn empty<T>() -> OVec<T>;
    fn len<T>(vec: OVec<T>) -> int;
    fn get<T>(vec: OVec<T>, idx: int) -> T;
    fn push<T>(vec: OVec<T>, e: T) -> OVec<T>;
    fn set<T>(vec: OVec<T>, idx: int, val: T) -> OVec<T>;
    fn pop<T>(vec: OVec<T>) -> OVec<T>;
}

#[flux_rs::opaque]
#[flux_rs::refined_by(v: OVec<T>)]
pub struct SVec<T> {
    inner: Vec<T>
}

#[flux_rs::trusted]
impl<T> SVec<T> {

    #[flux_rs::spec(fn() -> Self[empty()])]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[flux_rs::spec(fn(&Self[@slf]) -> usize[len(slf)])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[flux_rs::spec(fn(&Self[@slf], pos: usize { pos < len(slf) }) -> &T[get(slf, pos)])]
    pub fn get(&self, pos: usize) -> &T {
        &self.inner[pos]
    }

    #[flux_rs::spec(fn(s: &mut Self[@slf], pos: usize { pos < len(slf) }) -> &mut T[get(slf, pos)])]
    pub fn get_mut(&mut self, pos: usize) -> &mut T {
        &mut self.inner[pos]
    }

    #[flux_rs::spec(fn(s: &mut Self[@slf], e: T) ensures s : Self[push(slf, e)])]
    pub fn push(&mut self, e: T) {
        self.inner.push(e);
    }

    #[flux_rs::spec(fn(s: &mut Self[@slf], pos: usize{ pos < len(slf) }, e: T) 
        ensures s : Self[set(slf, pos, e)]
    )]
    pub fn set(&mut self, pos: usize, e: T) {
        self.inner[pos] = e;
    }

    #[flux_rs::spec(fn(s: &mut Self[@slf]) -> T[get(slf, len(slf) - 1)] requires len(slf) > 0 ensures s : Self[pop(slf)])]
    pub fn pop(&mut self) -> T {
        self.inner.pop().unwrap()
    }

    #[flux_rs::spec(fn(s: &mut Self[@slf], pos: usize { pos < len(slf) }, r: T[@rv]) -> T[get(slf, pos)]
        ensures s : Self[set(slf, pos, rv)]
    )]
    pub fn take(&mut self, pos: usize, r: T) -> T {
        std::mem::replace(self.get_mut(pos), r)
    }
}
