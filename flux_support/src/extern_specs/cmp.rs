#[flux_rs::extern_spec(core::cmp)]
#[flux_rs::no_panic]
fn min<T: Ord>(v1: T, v2: T) -> T;

#[flux_rs::extern_spec(core::cmp)]
#[flux_rs::no_panic]
fn max<T: Ord>(v1: T, v2: T) -> T;