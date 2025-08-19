use core::slice::{Iter, IterMut};

#[flux_rs::opaque]
#[flux_rs::refined_by(m: Map<int, T>)]
pub struct RArray<T: Copy> {
    arr: [T; 8],
}
impl<T: Copy> RArray<T> {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn (arr: [T; 8]) -> Self)]
    pub const fn new(arr: [T; 8]) -> Self {
        Self { arr }
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (&Self[@arr], { usize[@idx] | idx < 8 }) -> T[map_select(arr, idx)])]
    pub fn get(&self, idx: usize) -> T {
        self.arr[idx]
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (self: &strg Self[@arr], { usize[@idx] | idx < 8 }, item: T) ensures self: Self[map_store(arr, idx, item)])]
    pub fn set(&mut self, idx: usize, item: T) {
        self.arr[idx] = item;
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (&Self) -> usize[8])]
    pub fn len(&self) -> usize {
        self.arr.len()
    }

    #[flux_rs::trusted]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        self.arr.iter_mut()
    }

    #[flux_rs::trusted]
    pub fn iter(&self) -> Iter<'_, T> {
        self.arr.iter()
    }
}
