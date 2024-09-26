#[flux_rs::extern_spec(std::iter)]
#[generics(Self as base)]
trait IntoIterator {
    #[flux_rs::sig(fn(self: Self) -> Self::IntoIter)]
    fn into_iter(self) -> Self::IntoIter
    where
        Self: Sized;
}

#[flux_rs::extern_spec(core::ops)]
#[generics(I as base)]
impl<I: Iterator> IntoIterator for I {
    #[flux_rs::sig(fn(self: I) -> I)]
    fn into_iter(self) -> I;
}
