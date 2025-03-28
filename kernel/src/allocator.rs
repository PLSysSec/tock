use core::{cmp, fmt::Display, ptr::NonNull};

use flux_support::{max_ptr, max_usize, FluxPtrU8, FluxPtrU8Mut};

use crate::{
    platform::mpu::{self, RegionDescriptor},
    process::Error, utilities::math,
};

pub(crate) enum AllocateAppMemoryError {
    HeapError,
    FlashError,
}

#[derive(Clone, Copy)]
#[flux_rs::refined_by(
    memory_start: int,
    memory_size: int,
    app_break: int, 
    high_water_mark: int, 
    kernel_break: int, 
    flash_start: int, 
    flash_size: int
)]
#[flux_rs::invariant(flash_start + flash_size < memory_start)]
#[flux_rs::invariant(app_break >= high_water_mark)]
#[flux_rs::invariant(app_break <= kernel_break)]
#[flux_rs::invariant(high_water_mark >= memory_start)]
pub(crate) struct AppBreaks {
    #[field(FluxPtrU8[memory_start])]
    memory_start: FluxPtrU8,
    #[field(usize[memory_size])]
    memory_size: usize,
    #[field(FluxPtrU8[app_break])]
    app_break: FluxPtrU8,
    #[field(FluxPtrU8[high_water_mark])]
    high_water_mark: FluxPtrU8,
    #[field(FluxPtrU8[kernel_break])]
    kernel_break: FluxPtrU8,
    #[field(FluxPtrU8[flash_start])]
    flash_start: FluxPtrU8,
    #[field(usize[flash_size])]
    flash_size: usize,
}

impl AppBreaks {
    pub(crate) fn memory_start(&self) -> FluxPtrU8 {
        self.memory_start
    }
    pub(crate) fn memory_size(&self) -> usize {
        self.memory_size
    }
    pub(crate) fn app_break(&self) -> FluxPtrU8 {
        self.app_break
    }
    pub(crate) fn high_water_mark(&self) -> FluxPtrU8 {
        self.high_water_mark
    }
    pub(crate) fn kernel_break(&self) -> FluxPtrU8 {
        self.high_water_mark()
    }
    pub(crate) fn process_ram_size(&self) -> usize {
        self.app_break.as_usize() - self.memory_start.as_usize()
    }
    fn in_app_ram_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> bool {
        end >= start && start >= self.memory_start && end <= self.app_break
    }
    fn in_app_flash_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> bool {
        end >= start
            && start >= self.flash_start
            && end <= self.flash_start.wrapping_add(self.flash_size)
    }
}

const RAM_REGION_NUMBER: usize = 0;
const FLASH_REGION_NUMBER: usize = 1;

pub(crate) struct AppMemoryAllocator<M: mpu::MPU> {
    pub breaks: Option<AppBreaks>,
    pub regions: [M::Region; 8], // IDK why this is 8 but that's what is in the kernel - definitely cheating for IPC lol
}

impl<M: mpu::MPU> Display for AppMemoryAllocator<M> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "\r\n MPU")?;
        for region in self.regions.iter() {
            write!(f, "{}", region)?;
        }
        write!(f, "\r\n")
    }
}

impl<M: mpu::MPU> AppMemoryAllocator<M> {
    #[flux_rs::trusted]
    pub(crate) fn new() -> Self {
        let regions = core::array::from_fn(|i| <M as mpu::MPU>::Region::default(i));
        Self {
            breaks: None,
            regions,
        }
    }

    #[flux_rs::trusted]
    pub(crate) fn reset(&mut self) {
        for (i, r) in self.regions.iter_mut().enumerate() {
            *r = <M as mpu::MPU>::Region::default(i)
        }
    }

    pub(crate) fn kernel_break(&self) -> Option<FluxPtrU8> {
        Some(self.breaks?.kernel_break())
    }

    pub(crate) fn app_break(&self) -> Option<FluxPtrU8> {
        Some(self.breaks?.app_break())
    }

    pub(crate) fn in_app_ram_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> Option<bool> {
        Some(self.breaks?.in_app_ram_memory(start, end))
    }

    #[flux_rs::trusted]
    pub(crate) fn add_shared_readonly_buffer(
        &mut self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<(), ()> {
        let breaks = &mut self.breaks.ok_or(())?;
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        if breaks.in_app_ram_memory(buf_start_addr, buf_end_addr) {
            // TODO: Check for buffer aliasing here
            // Valid buffer, we need to adjust the app's watermark
            // note: `in_app_owned_memory` ensures this offset does not wrap
            let new_water_mark = max_ptr(breaks.high_water_mark, buf_end_addr);
            breaks.high_water_mark = new_water_mark;
            Ok(())
        } else if breaks.in_app_flash_memory(buf_start_addr, buf_end_addr) {
            Ok(())
        } else {
            Err(())
        }
    }

    #[flux_rs::trusted]
    pub(crate) fn add_shared_readwrite_buffer(
        &mut self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<(), ()> {
        let breaks = &mut self.breaks.ok_or(())?;
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        if breaks.in_app_ram_memory(buf_start_addr, buf_end_addr) {
            // TODO: Check for buffer aliasing here
            // Valid buffer, we need to adjust the app's watermark
            // note: `in_app_owned_memory` ensures this offset does not wrap
            let new_water_mark = max_ptr(breaks.high_water_mark, buf_end_addr);
            breaks.high_water_mark = new_water_mark;
            Ok(())
        } else {
            Err(())
        }
    }

    pub(crate) fn allocate_in_grant_region(
        &mut self,
        size: usize,
        align: usize,
    ) -> Option<NonNull<u8>> {
        // First, compute the candidate new pointer. Note that at this point
        // we have not yet checked whether there is space for this
        // allocation or that it meets alignment requirements.
        let breaks = &mut self.breaks?;
        let new_break_unaligned = breaks.kernel_break.wrapping_sub(size);

        // Our minimum alignment requirement is two bytes, so that the
        // lowest bit of the address will always be zero and we can use it
        // as a flag. It doesn't hurt to increase the alignment (except for
        // potentially a wasted byte) so we make sure `align` is at least
        // two.
        let align = max_usize(align, 2);

        // The alignment must be a power of two, 2^a. The expression
        // `!(align - 1)` then returns a mask with leading ones, followed by
        // `a` trailing zeros.
        let alignment_mask = !(align - 1);
        let new_break = FluxPtrU8::from(new_break_unaligned.as_usize() & alignment_mask);

        // Verify there is space for this allocation
        if new_break < breaks.app_break {
            None
            // Verify it didn't wrap around
        } else if new_break > breaks.kernel_break {
            None
            // Verify this is compatible with the MPU.
        } else {
            // Allocation is valid.
            // The app break is precisely the end of the process
            // accessible memory so we don't need to ask the MPU
            // anything

            // We always allocate down, so we must lower the
            // kernel_memory_break.
            breaks.kernel_break = new_break;

            // We need `grant_ptr` as a mutable pointer.
            let grant_ptr = new_break;

            // ### Safety
            //
            // Here we are guaranteeing that `grant_ptr` is not null. We can
            // ensure this because we just created `grant_ptr` based on the
            // process's allocated memory, and we know it cannot be null.
            unsafe { Some(NonNull::new_unchecked(grant_ptr.unsafe_as_ptr())) }
        }
    }

    // pub(crate) fn remove_memory_region(
    //     &mut self,
    //     _region: <M as mpu::MPU>::Region,
    // ) -> Result<(), ()> {
    //     todo!()
    // }

    pub(crate) fn configure_mpu(&mut self, mpu: &mut M) {
        mpu.configure_mpu(&self.regions);
    }

    fn next_available_ipc_idx(&self) -> Option<usize> {
        for (i, region) in self.regions.iter().enumerate() {
            if i != FLASH_REGION_NUMBER && i != RAM_REGION_NUMBER && !region.is_set() {
                return Some(i);
            }
        }
        None
    }

    fn any_overlaps(&self, region: &<M as mpu::MPU>::Region) -> bool {
        for existing_region in self.regions.iter() {
            if region.overlaps(existing_region) {
                return true;
            }
        }
        return false;
    }

    #[flux_rs::trusted]
    pub(crate) fn allocate_ipc_region(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: mpu::Permissions,
        mpu: &M,
    ) -> Result<mpu::Region, ()> {
        let region_idx = self.next_available_ipc_idx().ok_or(())?;
        let region = mpu
            .new_region(
                region_idx + 2, // Adds two because the first two are reserved for app flash and ram
                unallocated_memory_start,
                unallocated_memory_size,
                min_region_size,
                permissions,
            )
            .ok_or(())?;

        // make sure new region doesn't overlap
        if self.any_overlaps(&region) {
            return Err(())
        }

        self.regions[region_idx] = region;
        let start = region.accessible_start().ok_or(())?;
        let size = region.accessible_size().ok_or(())?;
        Ok(mpu::Region::new(start, size))
    }

    fn add_flash_region(
        &mut self,
        flash_start: FluxPtrU8,
        flash_size: usize,
        mpu: &M,
    ) -> Result<(), ()> {
        let region = mpu
            .new_region(
                FLASH_REGION_NUMBER,
                flash_start,
                flash_size,
                flash_size,
                mpu::Permissions::ReadExecuteOnly,
            )
            .ok_or(())?;

        // make sure new region doesn't overlap
        if self.any_overlaps(&region) {
            return Err(())
        }

        self.regions[FLASH_REGION_NUMBER] = region;
        Ok(())
    }

    #[flux_rs::trusted]
    pub(crate) fn allocate_app_memory(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8Mut,
        flash_size: usize,
        mpu: &M,
    ) -> Result<AppBreaks, AllocateAppMemoryError> {

        let flash_region = self.regions[FLASH_REGION_NUMBER];
        let ram_region = self.regions[RAM_REGION_NUMBER];

        if flash_region.is_set() || ram_region.is_set() {
            // Don't reallocate a process that is already set up
            return Err(AllocateAppMemoryError::HeapError)
        }

        self.add_flash_region(flash_start, flash_size, mpu)
            .map_err(|_| AllocateAppMemoryError::FlashError)?;

        let ideal_region_size = cmp::min(
            min_memory_size,
            initial_app_memory_size 
        );
        let region = mpu
            .new_region(
                RAM_REGION_NUMBER,
                unallocated_memory_start,
                unallocated_memory_size,
                ideal_region_size,
                mpu::Permissions::ReadWriteOnly,
            )
            .ok_or(AllocateAppMemoryError::HeapError)?;

        let memory_start = region
            .accessible_start()
            .ok_or(AllocateAppMemoryError::HeapError)?;
        let app_memory_size = region.accessible_size().ok_or(AllocateAppMemoryError::HeapError)?;
        let app_break = memory_start.wrapping_add(app_memory_size);

        // compute the total block size: 
        // make it a power of two to add some space between the app and the kernel regions of memory
        let total_block_size = math::closest_power_of_two_usize(app_memory_size + initial_kernel_memory_size);

        // make sure we can actually fit everything into te RAM pool
        if memory_start.wrapping_add(total_block_size) > unallocated_memory_start.wrapping_add(unallocated_memory_size) {
            // We don't have enough memory left in the RAM pool to 
            // give this process memory
            return Err(AllocateAppMemoryError::HeapError)
        }

        // make sure new region doesn't overlap
        if self.any_overlaps(&region) {
            return Err(AllocateAppMemoryError::HeapError)
        }

        self.regions[RAM_REGION_NUMBER] = region;
        let kernel_break = memory_start
            .wrapping_add(total_block_size)
            .wrapping_sub(initial_kernel_memory_size);
        let high_water_mark = memory_start;
        let breaks = AppBreaks {
            memory_start,
            memory_size: total_block_size,
            app_break,
            high_water_mark,
            kernel_break,
            flash_start,
            flash_size,
        };
        self.breaks = Some(breaks);
        Ok(breaks)
    }

    #[flux_rs::trusted]
    pub(crate) fn update_app_memory(
        &mut self,
        new_app_break: FluxPtrU8Mut,
        mpu: &M,
    ) -> Result<AppBreaks, Error> {
        let current_breaks = &mut self.breaks.ok_or(Error::KernelError)?;
        let memory_start = current_breaks.memory_start;
        let total_size = current_breaks.memory_size;
        let memory_end = memory_start.wrapping_add(total_size);
        let high_water_mark = current_breaks.high_water_mark;
        let kernel_break = current_breaks.kernel_break;
        if new_app_break.as_usize() > kernel_break.as_usize()
            || new_app_break.as_usize() <= memory_start.as_usize()
            || new_app_break.as_usize() > memory_end.as_usize()
            || new_app_break.as_usize() < high_water_mark.as_usize()
        {
            return Err(Error::AddressOutOfBounds);
        }
        let new_region_size = new_app_break.wrapping_sub(memory_start.as_usize());
        let new_region = mpu
            .new_region(
                RAM_REGION_NUMBER,
                memory_start,
                total_size,
                new_region_size.as_usize(),
                mpu::Permissions::ReadWriteOnly,
            )
            .ok_or(Error::OutOfMemory)?;
        let new_app_break = new_region
            .accessible_start()
            .ok_or(Error::KernelError)?
            .as_usize()
            + new_region.accessible_size().ok_or(Error::KernelError)?;
        if new_app_break > kernel_break.as_usize() {
            return Err(Error::OutOfMemory);
        }
        current_breaks.app_break = FluxPtrU8::from(new_app_break);
        self.regions[RAM_REGION_NUMBER] = new_region;
        Ok(*current_breaks)
    }
}
