#![allow(unused)]
use std::iter::Step;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::refined_by(idx: int, inner: I)]
struct Enumerate<I>;

#[flux_rs::extern_spec(std::iter)]
#[flux_rs::generics(Self as base)]
#[flux_rs::assoc(fn done(self: Self) -> bool  )]
#[flux_rs::assoc(fn step(self: Self, other: Self) -> bool )]
trait Iterator {
    #[flux_rs::sig(fn(self: &strg Self[@curr_s]) -> Option<Self::Item>[!<Self as Iterator>::done(curr_s)] ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<Self::Item>;

    #[flux_rs::sig(fn(Self[@s]) -> Enumerate<Self>[0, s])]
    fn enumerate(self) -> Enumerate<Self>
    where
        Self: Sized;
}

#[flux_rs::extern_spec(core::ops)]
#[generics(A as base)]
#[flux_rs::assoc(fn done(r: Range<A>) -> bool { r.start == r.end } )]
#[flux_rs::assoc(fn step(self: Range<A>, other: Range<A>) -> bool { <A as Step>::can_step_forward(self.start, 1) => other.start == <A as Step>::step_forward(self.start, 1) } )]
impl<A: Step> Iterator for Range<A> {
    #[flux_rs::sig(
        fn(self: &strg Range<A>[@old_range]) -> Option<A>[old_range.start < old_range.end]
            ensures self: Range<A>{r: <A as Step>::can_step_forward(old_range.start, 1) => r.start == <A as Step>::step_forward(old_range.start, 1) }
    )]
    fn next(&mut self) -> Option<A>;
}
