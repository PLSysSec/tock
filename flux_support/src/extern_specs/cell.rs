use core::cell::Cell;

#[flux_rs::extern_spec(core::cell)]
struct Cell<T: ?Sized>;

#[flux_rs::extern_spec(core::cell)]
impl<T: Copy> Cell<T> {
    #[flux_rs::no_panic]
    fn get(&self) -> T;
}

#[flux_rs::extern_spec(core::cell)]
impl<T> Cell<T> {
    #[flux_rs::no_panic]
    fn new(value: T) -> Cell<T>;

    #[flux_rs::no_panic]
    fn set(&self, value: T);

    #[flux_rs::no_panic]
    fn replace(&self, val: T) -> T;
}

#[flux_rs::extern_spec(core::cell)]
impl<T: Default> Cell<T> {
    #[flux_rs::no_panic]
    fn take(&self) -> T;
}