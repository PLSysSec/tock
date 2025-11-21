#![allow(unused)]

use core::cmp::PartialOrd;

#[flux_rs::extern_spec(core::cmp)]
trait Ord {
    #[flux_rs::no_panic]
    fn min(self, other: Self) -> Self
    where
        Self: Sized;
}

#[flux_rs::extern_spec(core::cmp)]
trait PartialOrd<Rhs: ?Sized = Self>: PartialEq<Rhs> {
    #[flux_rs::no_panic]
    fn lt(&self, other: &Rhs) -> bool;
    fn le(&self, other: &Rhs) -> bool;
}


#[flux_rs::extern_spec(core::cmp)]
trait PartialEq<Rhs: ?Sized = Self> {
    #[flux_rs::no_panic]
    fn eq(&self, other: &Rhs) -> bool;
}