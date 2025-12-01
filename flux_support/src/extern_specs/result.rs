#[flux_rs::extern_spec]
#[flux_rs::refined_by(b: bool)]
enum Result<T, E> {
    #[variant({T} -> Result<T, E>[true])]
    Ok(T),
    #[variant({E} -> Result<T, E>[false])]
    Err(E),
}

#[flux_rs::extern_spec]
impl<T, E> Result<T, E> {
    #[sig(fn(&Result<T,E>[@b]) -> bool[b])]
    const fn is_ok(&self) -> bool;

    #[flux_rs::no_panic]
    #[sig(fn(&Result<T,E>[@b]) -> bool[!b])]
    const fn is_err(&self) -> bool;
}

#[flux_rs::extern_spec(core::ops)]
impl<T, E> Try for Result<T, E> {
    #[flux_rs::no_panic]
    fn branch(self) -> ControlFlow<<Result<T, E> as core::ops::Try>::Residual, <Result<T, E> as core::ops::Try>::Output>;
}

#[flux_rs::extern_spec(core::ops)]
impl<T, E, F: From<E>> FromResidual<Result<core::convert::Infallible, E>> for Result<T, F> {
    #[flux_rs::no_panic]
    fn from_residual(residual: Result<core::convert::Infallible, E>) -> Self;
}