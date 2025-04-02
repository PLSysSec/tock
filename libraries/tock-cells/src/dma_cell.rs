// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Tock specific `DmaCell` to hold buffers owned by DMA.
//! 
//! Example Usage:
//! ```rust
//! use tock_cells::dma_cell::DmaCell;
//! 
//! #[repr(C)]
//! PeripheralRegisters {
//!   txd_ptr: ReadWrite<u32, Pointer::Register>
//! } 
//!
//! struct Peripheral {
//!   tx_buf: DmaCell<'static, [u8]>
//!   registers: StaticRef<PeripheralRegisters>
//! }
//!
//! impl Peripheral {
//!   fn transmit(buf: &'static mut [u8]) {
//!     // begin dma; place buffer into `DmaCell`
//!     // and set dma register with address.
//!     self.registers.txd_ptr.write(self.tx_buf.place(buf) as u32);
//!   }
//! }
use crate::optional_cell::OptionalCell;

/////////////////////////////////////////////////////////////////////
// TODO (vtock): One thing we are not considering with this is the 
// length field with DMA, but I think we can fairly easily add this.
/////////////////////////////////////////////////////////////////////

/// A shared reference to a mutable reference to be use with 
/// DMA. 
/// 
/// While DMA is in progress, a buffer given to DMA must be 
/// viewed as mutable and other references to it must not be used.
/// `DmaCell` allows you to safely contain a mutable reference
/// to a buffer that is currently being used by DMA, and ensures
/// that others may not access this buffer. 
/// 
/// A user of the `DmaCell` places a buffer that is to be owned by 
/// DMA into the `DmaCell`. Upon completion of a DMA operation, the 
/// user can call `completed()` to retrieve the buffer from DMA.
pub struct DmaCell<'a, T> {
    val: OptionalCell<&'a mut T>,
}

impl<'a, T> DmaCell<'a, T> {
    const EMPTY: Self = Self {
        val: OptionalCell::empty(),
    };

    pub const fn empty() -> DmaCell<'a, T> {
        Self::EMPTY
    }

    /// Retrieve the buffer from the `DmaCell` upon completion 
    /// of DMA. 
    /// 
    /// Upon completion of a DMA operation, we can safely
    /// retreive the buffer from the `DmaCell`. This function
    /// is marked `unsafe` as we must be sure that the DMA operation
    /// is completed before calling it. If the DMA is still in progress,
    /// it is unsafe to access the buffer as the DMA engine in practice
    /// maintains ownership of this buffer and may still be writing to it.
    pub unsafe fn completed(&self) -> Option<&'a mut T> {
        self.val.take()
    }

    // TODO: Make width of return value generic (instead of u32)

    /// Places a new buffer into the `DmaCell`.
    /// 
    /// Intended to be called when a buffer is handed to DMA.
    /// Upon successfully placing buffer (i.e. DMA is not currently
    /// in use), returns a 
    pub fn place(&self, val: &'a mut T) -> Option<*const T> {
        if self.val.is_some() {
            // If the cell is already holding a value, we can't replace it
            // because DMA is still in progress.
            None
        } else {
            // get ptr value from buffer
            let res = Some(val as *const T);
            self.val.set(val);
            res
        }
    }
}
