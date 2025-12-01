use core::marker::PointeeSized;

#[flux_rs::extern_spec(core::ptr)]
impl<T: Sized> NonNull<T> {
    #[flux_rs::no_panic]
    fn as_ptr(self) -> *mut T;

    #[flux_rs::no_panic]
    fn cast<U>(self) -> NonNull<U>;
}

#[flux_rs::extern_spec(core::ptr)]
#[flux_rs::no_panic]
fn null_mut<T: PointeeSized + Thin>() -> *mut T;

