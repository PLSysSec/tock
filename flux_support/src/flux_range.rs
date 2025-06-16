use core::clone::Clone;
use core::cmp::Eq;
use core::cmp::PartialEq;
use core::fmt::Debug;
use core::marker::Copy;
use core::prelude::rust_2021::derive;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[flux_rs::refined_by(start: int, end: int)]
pub struct FluxRange {
    #[field(usize[start])]
    pub start: usize,
    #[field(usize[end])]
    pub end: usize,
}

impl FluxRange {
    #[flux_rs::sig(fn (&Self[@r]) -> bool[r.start >= r.end])]
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    #[flux_rs::sig(fn (&Self[@r], &usize[@item]) -> bool[r.start <= item && item < r.end])]
    pub fn contains(&self, item: &usize) -> bool {
        self.start <= *item && *item < self.end
    }
}
