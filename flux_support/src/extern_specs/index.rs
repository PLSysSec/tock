#![allow(unused)]
use std::ops::Range;
use std::ops::RangeFrom;
use std::ops::RangeTo;
use std::slice::SliceIndex;

#[flux_rs::extern_spec(std::ops)]
#[flux_rs::assoc(fn index(old: Self, idx: Idx, new: Self::Output) -> bool)]
trait Index<Idx> {
    #[flux_rs::sig(fn(&Self[@old], Idx[@idx]) -> &Self::Output{v: <Self as Index<Idx>>::index(old, idx, v) })]
    fn index(&self, index: Idx) -> &Self::Output;
}

#[flux_rs::extern_spec(std::ops)]
#[flux_rs::assoc(fn index(old: Self, idx: Idx, new: Self::Output) -> bool)]
trait IndexMut<Idx> {
    #[flux_rs::sig(fn(&mut Self[@old], Idx[@idx]) -> &mut Self::Output{v: <Self as Index<Idx>>::index(old, idx, v) })]
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}

#[flux_rs::extern_spec(std::slice)]
#[flux::generics(Self as base, T as base)]
#[flux::assoc(fn in_bounds(idx: Self, v: T) -> bool)]
#[flux::assoc(fn index(old: T, idx: Self, new: Self::Output) -> bool)]
trait SliceIndex<T>
where
    T: ?Sized,
{
}

#[flux_rs::extern_spec(std::ops)]
#[flux_rs::assoc(fn index(old: Self, idx: I, new: <I as SliceIndex<[T]>>::Output) -> bool { <I as SliceIndex<[T]>>::index(old, idx, new)  })]
#[generics(I as base)]
impl<T, I: SliceIndex<[T]>> Index<I> for [T] {
    #[flux::sig(fn (&[T][@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> &<I as SliceIndex<[T]>>::Output{ new: <I as SliceIndex<[T]>>::index(len, idx, new) })]
    fn index(&self, index: I) -> &<I as SliceIndex<[T]>>::Output;
}

#[flux_rs::extern_spec(std::ops)]
#[flux_rs::generics(I as base)]
impl<T, I: SliceIndex<[T]>> IndexMut<I> for [T] {
    #[flux::sig(fn (&mut [T][@len], {I[@idx] | <I as SliceIndex<[T]>>::in_bounds(idx, len)}) -> _)]
    fn index_mut(&mut self, idx: I) -> &mut <I as SliceIndex<[T]>>::Output;
}

#[flux_rs::extern_spec(std::slice)]
#[flux::assoc(fn in_bounds(idx: Range<int>, len: int) -> bool { idx.start >= 0 && idx.start <= idx.end && idx.end <= len } )]
impl<T> SliceIndex<[T]> for Range<usize> {
    #[flux_rs::sig(fn(Range<usize>[@start, @end], &[T][@len]) -> Option<&[T][end - start]>[start >= 0 && start <= end && end <= len])]
    fn get(self, slice: &[T]) -> Option<&[T]>;

    #[flux_rs::sig(fn(Range<usize>[@start, @end], &mut [T][@len]) -> Option<&mut [T][end - start]>[start >= 0 && start <= end && end <= len])]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]>;

    #[flux_rs::sig(fn(Range<usize>[@start, @end], &[T][@len]) -> &[T][end - start])]
    fn index(self, slice: &[T]) -> &[T];

    #[flux_rs::sig(fn(Range<usize>[@start, @end], &mut [T][@len]) -> &mut [T][end - start])]
    fn index_mut(self, slice: &mut [T]) -> &mut [T];
}

#[flux_rs::extern_spec(std::slice)]
#[flux::assoc(fn in_bounds(idx: RangeTo<int>, len: int) -> bool { idx.end >= 0 && idx.end <= len } )]
impl<T> SliceIndex<[T]> for RangeTo<usize> {
    #[flux_rs::sig(fn(RangeTo<usize>[@end], &[T][@len]) -> Option<&[T][end]>[end >= 0 && end <= len])]
    fn get(self, slice: &[T]) -> Option<&[T]>;

    #[flux_rs::sig(fn(RangeTo<usize>[@end], &mut [T][@len]) -> Option<&mut [T][end]>[end >= 0 && end <= len])]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]>;

    #[flux_rs::sig(fn(RangeTo<usize>[@end], &[T][@len]) -> &[T][end])]
    fn index(self, slice: &[T]) -> &[T];

    #[flux_rs::sig(fn(RangeTo<usize>[@end], &mut [T][@len]) -> &mut [T][end])]
    fn index_mut(self, slice: &mut [T]) -> &mut [T];
}

#[flux_rs::extern_spec(std::slice)]
#[flux::assoc(fn in_bounds(idx: RangeFrom<int>, len: int) -> bool { idx.start >= 0 && idx.start < len } )]
impl<T> SliceIndex<[T]> for RangeFrom<usize> {
    #[flux_rs::sig(fn(RangeFrom<usize>[@start], &[T][@len]) -> Option<&[T][len - start]>[start >= 0 && start < len])]
    fn get(self, slice: &[T]) -> Option<&[T]>;

    #[flux_rs::sig(fn(RangeFrom<usize>[@start], &mut [T][@len]) -> Option<&mut [T][len - start]>[start >= 0 && start < len])]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]>;

    #[flux_rs::sig(fn(RangeFrom<usize>[@start], &[T][@len]) -> &[T][len - start])]
    fn index(self, slice: &[T]) -> &[T];

    #[flux_rs::sig(fn(RangeFrom<usize>[@start], &mut [T][@len]) -> &mut [T][len - start])]
    fn index_mut(self, slice: &mut [T]) -> &mut [T];
}

#[flux_rs::extern_spec(std::slice)]
#[flux::assoc(fn in_bounds(idx: int, len: int) -> bool { idx >= 0 && idx < len } )]
impl<T> SliceIndex<[T]> for usize {
    #[flux_rs::sig(fn(usize[@idx], &[T][@len]) -> Option<&T>[idx >= 0 && idx < len])]
    fn get(self, slice: &[T]) -> Option<&T>;

    #[flux_rs::sig(fn(usize[@idx], &mut [T][@len]) -> Option<&mut T>[idx >= 0 && idx < len])]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut T>;

    #[flux_rs::sig(fn(usize[@idx], &[T][@len]) -> &T)]
    fn index(self, slice: &[T]) -> &T;

    #[flux_rs::sig(fn(usize[@idx], &mut [T][@len]) -> &mut T)]
    fn index_mut(self, slice: &mut [T]) -> &mut T;
}
