#![allow(unused)]
use core::ops::{Range, RangeBounds};

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::refined_by(start: Idx, end: Idx)]
struct Range<Idx> {
    #[field(Idx[start])]
    start: Idx,
    #[field(Idx[end])]
    end: Idx,
}


#[flux_rs::extern_spec(core::ops)]
#[generics(Self as base)]
trait RangeBounds<T> {
    #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
    fn start_bound(&self) -> Bound<&T>;
    #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
    fn end_bound(&self) -> Bound<&T>;
}


#[flux_rs::extern_spec(core::ops)]
#[generics(T as base)]
impl<T> RangeBounds<T> for Range<T> {
    #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
    fn start_bound(&self) -> Bound<&T>;
    #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
    fn end_bound(&self) -> Bound<&T>;
}
