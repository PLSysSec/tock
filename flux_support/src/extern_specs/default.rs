#[flux_rs::extern_spec(core::default)]
trait Default {
    #[flux_rs::no_panic]
    fn default() -> Self;
}