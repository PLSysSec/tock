use core::ops::{Index, IndexMut};

flux_rs::defs! {
    opaque sort Slc<T>;
    fn len<T>(s: Slc<T>) -> int;
    fn set<T>(s: Slc<T>, pos: int, val: T) -> Slc<T>;
    fn get<T>(s: Slc<T>, pos: int) -> T;
    fn push<T>(s: Slc<T>, val: T) -> Slc<T>;
    fn pop_front<T>(s: Slc<T>) -> Slc<T>;
    fn append<T>(s1: Slc<T>, s2: Slc<T>) -> Slc<T>;
    fn subslice<T>(s: Slc<T>, l: int, r: int) -> Slc<T>;
}

#[derive(Clone, Copy)]
#[flux_rs::opaque]
#[flux_rs::refined_by(elems: Slc<T>)]
pub struct SSlice<'a, T> {
    inner: &'a [T]
}

impl<'a, T> SSlice<'a, T> {
    #[flux_rs::trusted]
    #[flux_rs::spec(fn(&Self[@slf], start: usize { start < len(slf) }, end: usize { start <= end && end < len(slf) })
        -> SSlice<T>[subslice(slf, start, end)]
    )]
    pub fn sub_slice(&'a self, start: usize, end: usize) -> SSlice<'a, T> {
        let sub = &self.inner[start..end];
        SSlice { inner: sub }
    }
}

#[flux_rs::opaque]
#[flux_rs::refined_by(elems: Slc<T>)]
pub struct MutSSlice<'a, T> {
    inner: &'a mut [T],
}

#[flux_rs::trusted]
impl<'a, T> MutSSlice<'a, T> {
    #[flux_rs::spec(fn(inner: &mut [T][@l]) -> Self{ v : len(v) == l}
    )]
    pub fn new(inner: &'a mut [T]) -> Self {
        MutSSlice { inner }
    }

    #[flux_rs::spec(fn(&Self[@slf]) -> usize[len(slf)])]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[flux_rs::spec(fn(&Self[@slf], pos: usize{ pos < len(slf) })
        -> (SSlice<T>[subslice(slf, 0, pos)], SSlice<T>[subslice(slf, pos, len(slf) - 1)])
    )]
    pub fn split_at(&'a self, pos: usize) -> (SSlice<'a, T>, SSlice<'a, T>) {
        let (left, right) = self.inner.split_at(pos);
        (SSlice { inner: left }, SSlice { inner: right })
    }

    #[flux_rs::spec(fn(self: &Self[@slf], start: usize { start < len(slf) }, end: usize { start <= end && end < len(slf) })
        -> SSlice<T>[subslice(slf, start, end)]
    )]
    pub fn sub_slice(&'a self, start: usize, end: usize) -> SSlice<'a, T> {
        let sub = &self.inner[start..end];
        SSlice { inner: sub }
    }

    #[flux_rs::spec(fn(self: &mut Self[@slf], pos: usize{ pos < len(slf) }, T[@val])
        ensures self: Self[set(slf, pos, val)]
    )]
    pub fn set(&mut self, pos: usize, val: T) {
        self.inner[pos] = val;
    }

    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        self.inner
    }
}

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::assoc(
    fn in_bounds(self: Self, idx: Idx) -> bool {
        true
    }
    fn output(self: Self, idx: Idx, output: Self::Output) -> bool {
        true
    }
)]
trait Index<Idx> {
    #[flux_rs::spec(fn(self: &Self[@v], index: Idx { <Self as Index<Idx>>::in_bounds(v, index) }) 
        -> &Self::Output{ o : <Self as Index<Idx>>::output(v, index, o) })]
    fn index(&self, index: Idx) -> &Self::Output;
}

#[flux_rs::trusted]
#[flux_rs::assoc(
    fn in_bounds(self: Self, idx: int) -> bool {
        idx < len(self)
    }

    fn output(self: Self, idx: int, output: T) -> bool {
        output == get(self, idx)
    }
)]
impl<'a, T> Index<usize> for MutSSlice<'a, T> {
    type Output = T;
    #[flux_rs::trusted_impl]
    #[flux_rs::spec(fn(self: &Self[@v], index: usize { Self::in_bounds(v, index) }) 
        -> &Self::Output{ o : Self::output(v, index, o) })]
    fn index(&self, index: usize) -> &Self::Output {
        &self.inner[index]
    }
}

#[flux_rs::trusted]
impl<'a, T> IndexMut<usize> for MutSSlice<'a, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.inner[index]
    }
}
