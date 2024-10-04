#[flux_rs::extern_spec]
impl str {
    #[flux_rs::sig(fn(&str[@s]) -> usize[str_len(s)])]
    fn len(s: &str) -> usize;

    #[flux_rs::sig(fn(&str[@s]) -> &[u8][str_len(s)])]
    fn as_bytes(s: &str) -> &[u8];
}
