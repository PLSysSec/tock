#[flux_rs::extern_spec(core::convert)]
trait From<T>: Sized {
    #[flux_rs::no_panic]
    fn from(value: T) -> Self;
}

#[flux_rs::extern_spec(core::convert)]
trait Into<T>: Sized {
    #[flux_rs::no_panic]
    fn into(self) -> T;
}


#[flux_rs::extern_spec(core::convert)]
impl<T, U: From<T>> Into<U> for T {
    #[flux_rs::no_panic]
    fn into(self) -> U;
}