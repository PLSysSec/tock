#![allow(unused)]
use core::ops::{Range, RangeBounds, RangeFrom, RangeTo};

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::refined_by(start: Idx, end: Idx)]
struct Range<Idx> {
    #[field(Idx[start])]
    start: Idx,
    #[field(Idx[end])]
    end: Idx,
}

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::refined_by(end: Idx)]
struct RangeTo<Idx> {
    #[field(Idx[end])]
    end: Idx,
}

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::refined_by(start: Idx)]
struct RangeFrom<Idx> {
    #[field(Idx[start])]
    start: Idx,
}

#[flux_rs::extern_spec(core::ops)]
#[generics(Self as base, T as base)]
#[flux_rs::assoc(fn start(r: Self) -> T)]
#[flux_rs::assoc(fn end(r: Self) -> T)]
trait RangeBounds<T> {
    #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
    fn start_bound(&self) -> Bound<&T>;
    #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
    fn end_bound(&self) -> Bound<&T>;
}

// #[flux_rs::extern_spec(core::ops)]
// #[generics(T as base)]
// #[flux_rs::assoc(fn start(r: Range<T>) -> T { r.start })]
// #[flux_rs::assoc(fn end(r: Range<T>) -> T { r.end })]
// impl<T> RangeBounds<T> for Range<T> {
//     // Included
//     #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
//     fn start_bound(&self) -> Bound<&T>;
// 
//     // Excluded
//     #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[false, false])]
//     fn end_bound(&self) -> Bound<&T>;
// }

// #[flux_rs::extern_spec(core::ops)]
// #[generics(T as base)]
// #[flux_rs::assoc(fn start(r: Range<T>) -> T { 0 })]
// #[flux_rs::assoc(fn end(r: Range<T>) -> T { r.end })]
// impl<T> RangeBounds<T> for RangeTo<T> {
// 
//     // Unbounded
//     #[flux_rs::sig(fn(&RangeTo<T>[@r]) -> Bound<&T>[false, true])]
//     fn start_bound(&self) -> Bound<&T>;
// 
//     // Excluded
//     #[flux_rs::sig(fn(&RangeTo<T>[@r]) -> Bound<&T>[false, false])]
//     fn end_bound(&self) -> Bound<&T>;
// }
// 
// #[flux_rs::extern_spec(core::ops)]
// #[generics(T as base)]
// impl<T> RangeBounds<T> for RangeFrom<T> {
//     
//     // Included 
//     #[flux_rs::sig(fn(&RangeFrom<T>[@r]) -> Bound<&T>[true, false])]
//     fn start_bound(&self) -> Bound<&T>;
// 
//     // Unbounded
//     #[flux_rs::sig(fn(&RangeFrom<T>[@r]) -> Bound<&T>[false, true])]
//     fn end_bound(&self) -> Bound<&T>;
// }
