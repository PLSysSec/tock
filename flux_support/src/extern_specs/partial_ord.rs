#![allow(unused)]

use core::cmp::PartialOrd;

#[flux_rs::extern_spec(core::cmp)]
#[flux_rs::assoc(fn lt(this: Self, other: Rhs) -> bool { true })]
#[flux_rs::assoc(fn le(this: Self, other: Rhs) -> bool { true })]
trait PartialOrd<Rhs: ?Sized = Self> {
    #[flux_rs::sig(fn (&Self[@l], &Rhs[@r]) -> bool[<Self as PartialOrd>::lt(l, r)])]
    fn lt(&self, other: &Rhs) -> bool;

    #[flux_rs::sig(fn (&Self[@l], &Rhs[@r]) -> bool[<Self as PartialOrd>::le(l, r)])]
    fn le(&self, other: &Rhs) -> bool;
}
