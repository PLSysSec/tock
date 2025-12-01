#[flux_rs::extern_spec]
#[flux_rs::refined_by(b: bool)]
enum Option<T> {
    #[variant(Option<T>[false])]
    None,
    #[variant({T} -> Option<T>[true])]
    Some(T),
}

#[flux_rs::extern_spec]
impl<T> Option<T> {
    #[sig(fn(&Option<T>[@b]) -> bool[b])]
    #[flux_rs::no_panic]
    const fn is_some(&self) -> bool;

    #[sig(fn(&Option<T>[@b]) -> bool[!b])]
    #[flux_rs::no_panic]
    const fn is_none(&self) -> bool;

    #[flux_rs::no_panic]
    fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U;


    #[flux_rs::no_panic]
    fn map<U, F>(self, op: F) -> Option<U>
    where
        F: FnOnce(T) -> U;

    #[flux_rs::no_panic]
    fn inspect<F>(self, op: F) -> Self
    where
        F: FnOnce(&T);

    #[flux_rs::no_panic]
    fn unwrap_or_default(self) -> T
    where
        T: Default;

    #[flux_rs::no_panic]
    fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        // Andrew note: why does this not match up with source?
        D: FnOnce() -> U,
        F: FnOnce(T) -> U;

    #[flux_rs::no_panic]
    fn ok_or<E>(self, err: E) -> Result<T, E>;
}
