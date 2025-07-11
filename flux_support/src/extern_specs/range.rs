#![allow(unused)]

use core::ops::Bound;
use core::ops::{Range, RangeBounds};

#[flux_rs::extern_spec]
#[flux_rs::refined_by(included: bool, unbounded: bool)]
enum Bound<T> {
    #[variant((T) -> Bound<T>[true, false])]
    Included(T),
    #[variant((T) -> Bound<T>[false, false])]
    Excluded(T),
    // NOTE:
    // `included` refinement is
    // true because an unbounded value
    // will always be included
    #[variant(Bound<T>[true, true])]
    Unbounded,
}

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::refined_by(start: Idx, end: Idx)]
struct Range<Idx> {
    #[field(Idx[start])]
    start: Idx,
    #[field(Idx[end])]
    end: Idx,
}

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::assoc(fn start(self: Self) -> T)]
#[flux_rs::assoc(fn end(self: Self) -> T)]
trait RangeBounds<T> {
    #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
    fn start_bound(&self) -> Bound<&T>;

    #[flux_rs::sig(fn(&Self) -> Bound<&T>)]
    fn end_bound(&self) -> Bound<&T>;

    fn contains<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>;
    // {
    //     (match self.start_bound() {
    //         Included(start) => start <= item,
    //         Excluded(start) => start < item,
    //         Unbounded => true,
    //     }) && (match self.end_bound() {
    //         Included(end) => item <= end,
    //         Excluded(end) => item < end,
    //         Unbounded => true,
    //     })
    // }
}

#[flux_rs::extern_spec(core::ops)]
#[flux_rs::assoc(fn start(self: Range<T>) -> T { self.end })]
#[flux_rs::assoc(fn end(self: Range<T>) -> T { self.end })]
impl<T> RangeBounds<T> for Range<T> {
    #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
    fn start_bound(&self) -> Bound<&T>;
    #[flux_rs::sig(fn(&Range<T>[@r]) -> Bound<&T>[true, false])]
    fn end_bound(&self) -> Bound<&T>;
}
