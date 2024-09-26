#[allow(unused)]
use std::ops::Bound;

#[flux_rs::extern_spec]
#[generics(T as base)]
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
