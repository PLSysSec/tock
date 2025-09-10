// Need to tell Flux what slice.len() does
#[flux_rs::extern_spec]
impl<T> [T] {
    #[flux_rs::sig(fn(&[T][@len]) -> usize[len])]
    fn len(v: &[T]) -> usize;
}

// Need to tell Flux what an Option<T> is
// Here, we refine Option<T> with a bool, denoting whether it is Some or None
#[flux_rs::extern_spec]
#[flux_rs::refined_by(b: bool)]
enum Option<T> {
    #[variant(Option<T>[false])]
    None,
    #[variant({T} -> Option<T>[true])]
    Some(T),
}

#[flux::specs {
    mod collections {
        mod ring_buffer {
            // Specify well-formedness for RingBuffer<T>
            #[refined_by(ring_len: int, hd: int, tl: int)]
            struct RingBuffer<T> {
                ring: {&mut [T][ring_len] | ring_len > 1},
                head: {usize[hd] | hd < ring_len},
                tail: {usize[tl] | tl < ring_len},
            }

            impl RingBuffer<T> {
                // Every time RingBuffer::new() is called, 
                // Flux will ensure the slice passed in has length > 1.
                fn new({&mut [T][@ring_len] | ring_len > 1}) -> RingBuffer<T>[ring_len, 0, 0];
            }
        }

        mod queue {
            impl Queue<T> for collections::ring_buffer::RingBuffer<T> {
                fn enqueue(self: &mut RingBuffer<T>, val: T) -> bool 
                    ensures self: RingBuffer<T>;

                fn push(self: &mut RingBuffer<T>, val: T) -> Option<T>
                    ensures self: RingBuffer<T>;

                fn dequeue(self: &mut RingBuffer<T>) -> Option<T>
                    ensures self: RingBuffer<T>;

                fn remove_first_matching<F>(self: &mut RingBuffer<T>, _) -> Option<T> 
                    ensures self: RingBuffer<T>;

                fn retain<F>(self: &mut RingBuffer<T>, _) 
                    ensures self: RingBuffer<T>;

                fn empty(self: &mut RingBuffer<T>[@old]) 
                    ensures self: RingBuffer<T>[old.ring_len, 0, 0];
            }
        }

        mod list {
            impl Iterator for collections::list::ListIterator<T> {
                fn next(self: &mut ListIterator<T>) -> Option<&T> 
                    ensures self: ListIterator<T>;
            }
        }
    }
}]
const _: () = ();