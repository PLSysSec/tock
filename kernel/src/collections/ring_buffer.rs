// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Implementation of a ring buffer.

use crate::collections::queue;
use crate::collections::sslice::{MutSSlice, SSlice};

#[flux_rs::refined_by(ring: Slc<T>, hd: int, tl: int)]
#[flux_rs::invariant(len(ring) > 1)]
#[flux_rs::invariant(0 <= hd && hd < len(ring))]
#[flux_rs::invariant(0 <= tl && tl < len(ring))]
pub struct RingBuffer<'a, T: 'a> {
    #[field({MutSSlice<T>[ring] | len(ring) > 1})]
    ring: MutSSlice<'a, T>,
    #[field({usize[hd] | hd < len(ring)})]
    head: usize,
    #[field({usize[tl] | tl < len(ring)})]
    tail: usize,
}

flux_rs::defs! {
    fn ring_len<T>(rb: RingBuffer<T>) -> int {
        len(rb.ring)
    }
    fn next_index(x:int, rlen: int) -> int { (x + 1) % rlen }
    fn empty<T>(rb: RingBuffer<T>) -> bool { rb.hd == rb.tl }
    fn full<T>(rb: RingBuffer<T>) -> bool { rb.hd == next_index(rb.tl, ring_len(rb)) }
    fn next_hd<T>(rb: RingBuffer<T>) -> int { next_index(rb.hd, ring_len(rb)) }
    fn next_tl<T>(rb: RingBuffer<T>) -> int { next_index(rb.tl, ring_len(rb)) }

    fn rb_push<T>(old: RingBuffer<T>, val: T) -> RingBuffer<T> {
        RingBuffer {
            hd: if full(old) { next_hd(old) } else { old.hd },
            tl: next_tl(old),
            ring: set(old.ring, old.tl, val),
        }
    }

    fn rb_enqueue<T>(old: RingBuffer<T>, val: T) -> RingBuffer<T> {
        if !full(old) {
            rb_push(old, val)
        } else {
            old
        }
    }

    fn rb_dequeue<T>(old: RingBuffer<T>) -> RingBuffer<T> {
        if !empty(old) {
            RingBuffer {
                hd : next_hd(old),
                tl : old.tl,
                ring : old.ring
            }
        } else {
            old
        }
    }

    fn rb_len<T>(rb: RingBuffer<T>) -> int {
        if rb.tl > rb.hd {
            rb.tl - rb.hd
        } else if rb.tl < rb.hd {
            ring_len(rb) - rb.hd + rb.tl
        } else {
            0
        }
    }

    fn rb_matches_lqueue<T>(rb: RingBuffer<T>, vq: SSlice<T>) -> bool {
        vq == if rb.hd > rb.tl {
            append(subslice(rb.ring, rb.hd, len(rb.ring)), subslice(rb.ring, 0, rb.tl))
        } else {
            subslice(rb.ring, rb.hd, rb.tl)
        }
    }
}

impl<'a, T: Copy> RingBuffer<'a, T> {
    #[flux_rs::proven_externally]
    #[flux_rs::sig(fn({&mut [T][@rl] | rl > 1}) -> RingBuffer<T>{ rb : ring_len(rb) == rl && rb.hd == 0 && rb.tl == 0 })]
    pub fn new(ring: &'a mut [T]) -> RingBuffer<'a, T> {
        RingBuffer {
            head: 0,
            tail: 0,
            ring: MutSSlice::new(ring),
        }
    }

    /// Returns the number of elements that can be enqueued until the ring buffer is full.
    pub fn available_len(&self) -> usize {
        // The maximum capacity of the queue is ring.len - 1, because head == tail for the empty
        // queue.
        self.ring.len().saturating_sub(1 + queue::Queue::len(self))
    }

    /// Returns up to 2 slices that together form the contents of the ring buffer.
    ///
    /// Returns:
    /// - `(None, None)` if the buffer is empty.
    /// - `(Some(slice), None)` if the head is before the tail (therefore all the contents is
    /// contiguous).
    /// - `(Some(left), Some(right))` if the head is after the tail. In that case, the logical
    /// contents of the buffer is `[left, right].concat()` (although physically the "left" slice is
    /// stored after the "right" slice).
    pub fn as_slices(&self) -> (Option<&[T]>, Option<&[T]>) {
        if self.head < self.tail {
            (Some(&self.ring.as_slice()[self.head..self.tail]), None)
        } else if self.head > self.tail {
            let (left, right) = self.ring.as_slice().split_at(self.head);
            (
                Some(right),
                if self.tail == 0 {
                    None
                } else {
                    Some(&left[..self.tail])
                },
            )
        } else {
            (None, None)
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(&Self[@slf]) ->
        (
            Option<SSlice<T>{ v : 
                slf.hd < slf.tl => v == subslice(slf.ring, slf.hd, slf.tl) &&
                slf.hd > slf.tl => v == subslice(slf.ring, slf.hd, len(v))
            }>, 
            Option<SSlice<T>{ v : slf.hd > slf.tl => v == subslice(slf.ring, 0, slf.tl) }>
        )
    )]
    pub fn as_sslices(&'a self) -> (Option<SSlice<'a, T>>, Option<SSlice<'a, T>>) {
        if self.head < self.tail {
            return (Some(self.ring.sub_slice(self.head,self.tail)), None)
        }
        if self.head > self.tail {
            let (_, right) = self.ring.split_at(self.head);
            return (
                Some(right),
                if self.tail == 0 {
                    None
                } else {
                    Some(self.ring.sub_slice(0, self.tail))
                },
            )
        } 
        (None, None)
    }
}

impl<T: Copy> queue::Queue<T> for RingBuffer<'_, T> {
    #[flux_rs::sig(fn(&RingBuffer<T>[@rb]) -> bool[!empty(rb)]) ]
    fn has_elements(&self) -> bool {
        self.head != self.tail
    }

    #[flux_rs::sig(fn(&RingBuffer<T>[@rb]) -> bool[full(rb)]) ]
    fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    #[flux_rs::sig(fn(&RingBuffer<T>[@rb]) -> usize[rb_len(rb)])]
    fn len(&self) -> usize {
        if self.tail > self.head {
            self.tail - self.head
        } else if self.tail < self.head {
            (self.ring.len() - self.head) + self.tail
        } else {
            // head equals tail, length is zero
            0
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>[@old], T[@val]) -> bool[#success]
            ensures self: RingBuffer<T>[#nrb],
                    success == !full(old),
                    nrb == rb_enqueue(old, val)
    )]
    fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            // Incrementing tail will overwrite head
            false
        } else {
            self.ring.set(self.tail, val);
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(
        fn(self: &strg Self[@old], T[@val]) -> Option<T[get(old.ring, old.hd)]>[#res] 
            ensures 
                self: Self[#new],
                res == full(old),
                new == rb_push(old, val),
    )]
    fn push(&mut self, val: T) -> Option<T> {
        let result = if self.is_full() {
            let val = self.ring[self.head];
            self.head = (self.head + 1) % self.ring.len();
            Some(val)
        } else {
            None
        };

        self.ring.set(self.tail, val);
        self.tail = (self.tail + 1) % self.ring.len();
        result
    }

    #[flux_rs::proven_externally]
    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>[@old]) -> Option<T[get(old.ring, old.hd)]>[!empty(old)]
            ensures self: Self[rb_dequeue(old)]
    )]
    fn dequeue(&mut self) -> Option<T> {
        if self.has_elements() {
            let val = self.ring[self.head];
            self.head = (self.head + 1) % self.ring.len();
            Some(val)
        } else {
            None
        }
    }

    /// Removes the first element for which the provided closure returns `true`.
    ///
    /// This walks the ring buffer and, upon finding a matching element, removes
    /// it. It then shifts all subsequent elements forward (filling the hole
    /// created by removing the element).
    ///
    /// If an element was removed, this function returns it as `Some(elem)`.
    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &strg Self, _) -> Option<_> ensures self: Self
    )]
    fn remove_first_matching<F>(&mut self, f: F) -> Option<T>
    where
        F: Fn(&T) -> bool,
    {
        let len = self.ring.len();
        let mut slot = self.head;
        while slot != self.tail {
            if f(&self.ring[slot]) {
                // This is the desired element, remove it and return it
                let val = self.ring[slot];

                let mut next_slot = (slot + 1) % len;
                // Move everything past this element forward in the ring
                while next_slot != self.tail {
                    self.ring.set(slot, self.ring[next_slot]);
                    slot = next_slot;
                    next_slot = (next_slot + 1) % len;
                }
                self.tail = slot;
                return Some(val);
            }
            slot = (slot + 1) % len;
        }
        None
    }

    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>[@old]) ensures self: RingBuffer<T>[old.ring, 0, 0]
    )]
    fn empty(&mut self) {
        self.head = 0;
        self.tail = 0;
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &strg RingBuffer<T>, _) ensures self: RingBuffer<T>
    )]
    fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let len = self.ring.len();
        // Index over the elements before the retain operation.
        let mut src = self.head;
        // Index over the retained elements.
        let mut dst = self.head;

        while src != self.tail {
            if f(&self.ring[src]) {
                // When the predicate is true, move the current element to the
                // destination if needed, and increment the destination index.
                if src != dst {
                    self.ring.set(dst, self.ring[src]);
                }
                dst = (dst + 1) % len;
            }
            src = (src + 1) % len;
        }

        self.tail = dst;
    }
}

mod vec_queue {

    use crate::collections::ring_buffer::RingBuffer;
    use crate::collections::queue::Queue;

    #[flux_rs::opaque]
    #[flux_rs::refined_by(elems: Slc<T>)]
    struct LQueue<T> {
        inner: T
    }

    #[flux_rs::trusted]
    impl<T> LQueue<T> {

        #[flux_rs::spec(fn(self: &mut Self[@slf], T[@elem])
            ensures self: Self[push(slf, elem)]
        )]
        fn push_back(&mut self, elem: T) {}

        #[flux_rs::spec(fn(self: &mut Self[@slf])
            ensures self: Self[pop_front(slf)]
        )]
        fn pop_front(&mut self) {}
    }

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(r: &mut RingBuffer<T>[@rb], v: &mut LQueue<T>[@vq], T[@e], T[e]) -> bool[#res]
        requires rb_matches_lqueue(rb, vq),
        ensures  r: RingBuffer<T>[#nrb],
                 v: LQueue<T>[#nvq],
                 res => rb_matches_lqueue(nrb, nvq)
    )]
    fn push_correct<T: Copy>(r: &mut RingBuffer<'_, T>, v: &mut LQueue<T>, e1: T, e2: T) -> bool {
        v.push_back(e1);
        r.enqueue(e2)
    }

    #[flux_rs::proven_externally]
    #[flux_rs::spec(fn(r: &mut RingBuffer<T>[@rb], v: &mut LQueue<T>[@vq])
        requires rb_matches_lqueue(rb, vq),
                 !empty(rb), len(vq) > 0
        ensures r: RingBuffer<T>[#nrb],
                v: LQueue<T>[#nvq],
                rb_matches_lqueue(nrb, nvq)
    )]
    fn pop_correct<T: Copy>(r: &mut RingBuffer<'_, T>, v: &mut LQueue<T>) {
        v.pop_front();
        r.dequeue();
    }
}