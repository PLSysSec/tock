use core::{cmp, fmt::Display, ptr::NonNull};

use flux_support::{max_ptr, max_usize, FluxPtrU8, FluxPtrU8Mut};

use crate::{
    platform::mpu::{self, RegionDescriptor},
    process::{Error, ProcessCustomGrantIdentifier},
    utilities::math,
};

pub(crate) enum AllocateAppMemoryError {
    HeapError,
    FlashError,
}

#[derive(Clone, Copy)]
pub(crate) struct AppBreaks {
    memory_start: FluxPtrU8,
    memory_size: usize,
    app_break: FluxPtrU8,
    high_water_mark: FluxPtrU8,
    kernel_break: FluxPtrU8,
    flash_start: FluxPtrU8,
    flash_size: usize,
}

impl AppBreaks {
    pub(crate) fn flash_start(&self) -> FluxPtrU8 {
        self.flash_start
    }
    pub(crate) fn flash_size(&self) -> usize {
        self.flash_size
    }
    pub(crate) fn memory_start(&self) -> FluxPtrU8 {
        self.memory_start
    }
    pub(crate) fn memory_size(&self) -> usize {
        self.memory_size
    }
    pub(crate) fn app_break(&self) -> FluxPtrU8 {
        self.app_break
    }
}

const RAM_REGION_NUMBER: usize = 0;
const FLASH_REGION_NUMBER: usize = 1;

pub(crate) struct AppMemoryAllocator<R: RegionDescriptor + Display + Copy> {
    pub breaks: AppBreaks,
    pub regions: [R; 8],
}

impl<R: RegionDescriptor + Display + Copy> Display for AppMemoryAllocator<R> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "\r\n MPU")?;
        for region in self.regions.iter() {
            write!(f, "{}", region)?;
        }
        write!(f, "\r\n")
    }
}

impl<R: RegionDescriptor + Display + Copy> AppMemoryAllocator<R> {
    pub(crate) fn flash_start(&self) -> FluxPtrU8 {
        self.breaks.flash_start
    }

    pub(crate) fn flash_end(&self) -> FluxPtrU8 {
        self.breaks.flash_start.wrapping_add(self.breaks.flash_size)
    }

    pub(crate) fn memory_start(&self) -> FluxPtrU8 {
        self.breaks.memory_start
    }

    pub(crate) fn memory_size(&self) -> usize {
        self.breaks.memory_size
    }

    pub(crate) fn memory_end(&self) -> FluxPtrU8 {
        self.breaks
            .memory_start
            .wrapping_add(self.breaks.memory_size)
    }

    pub(crate) fn app_break(&self) -> FluxPtrU8 {
        self.breaks.app_break
    }

    pub(crate) fn kernel_break(&self) -> FluxPtrU8 {
        self.breaks.kernel_break
    }

    fn new_regions() -> [R; 8] {
        core::array::from_fn(|i| R::default(i))
    }

    pub(crate) fn reset(&mut self) {
        for (i, r) in self.regions.iter_mut().enumerate() {
            *r = R::default(i)
        }
    }

    pub(crate) fn in_app_ram_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> bool {
        end >= start && start >= self.breaks.memory_start && end <= self.breaks.app_break
    }

    pub(crate) fn in_app_flash_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> bool {
        end >= start
            && start >= self.breaks.flash_start
            && end <= self.breaks.flash_start.wrapping_add(self.breaks.flash_size)
    }

    pub(crate) fn add_shared_readonly_buffer(
        &mut self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<(), ()> {
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        if self.in_app_ram_memory(buf_start_addr, buf_end_addr) {
            // TODO: Check for buffer aliasing here
            // Valid buffer, we need to adjust the app's watermark
            // note: `in_app_owned_memory` ensures this offset does not wrap
            let new_water_mark = max_ptr(self.breaks.high_water_mark, buf_end_addr);
            self.breaks.high_water_mark = new_water_mark;
            Ok(())
        } else if self.in_app_flash_memory(buf_start_addr, buf_end_addr) {
            Ok(())
        } else {
            Err(())
        }
    }

    pub(crate) fn add_shared_readwrite_buffer(
        &mut self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<(), ()> {
        // let breaks = &mut self.breaks.ok_or(())?;
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        if self.in_app_ram_memory(buf_start_addr, buf_end_addr) {
            // TODO: Check for buffer aliasing here
            // Valid buffer, we need to adjust the app's watermark
            // note: `in_app_owned_memory` ensures this offset does not wrap
            let new_water_mark = max_ptr(self.breaks.high_water_mark, buf_end_addr);
            self.breaks.high_water_mark = new_water_mark;
            Ok(())
        } else {
            Err(())
        }
    }

    pub(crate) fn allocate_custom_grant(
        &mut self,
        size: usize,
        align: usize,
    ) -> Result<(ProcessCustomGrantIdentifier, NonNull<u8>), ()> {
        let ptr = self
            .allocate_in_grant_region_internal(size, align)
            .ok_or(())?;
        let custom_grant_address = ptr.as_usize();
        let process_memory_end = self.memory_end().as_usize();

        Ok((
            ProcessCustomGrantIdentifier {
                offset: process_memory_end - custom_grant_address,
            },
            ptr.into(),
        ))
    }

    pub(crate) fn allocate_in_grant_region_internal(
        &mut self,
        size: usize,
        align: usize,
    ) -> Option<FluxPtrU8> {
        // First, compute the candidate new pointer. Note that at this point
        // we have not yet checked whether there is space for this
        // allocation or that it meets alignment requirements.
        let new_break_unaligned = self.kernel_break().wrapping_sub(size).as_usize();

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
        let new_break = FluxPtrU8::from(new_break_unaligned & alignment_mask);

        // Verify there is space for this allocation
        if new_break < self.app_break() || new_break > self.kernel_break() {
            None
        } else {
            // Allocation is valid.
            // The app break is precisely the end of the process
            // accessible memory so we don't need to ask the MPU
            // anything

            // We always allocate down, so we must lower the
            // kernel_memory_break.
            self.set_kernel_break(new_break);

            // ### Safety
            //
            // Here we are guaranteeing that `grant_ptr` is not null. We can
            // ensure this because we just created `grant_ptr` based on the
            // process's allocated memory, and we know it cannot be null.
            Some(new_break)
        }
    }

    fn set_kernel_break(&mut self, new_break: FluxPtrU8) {
        self.breaks.kernel_break = new_break;
    }

    fn next_available_ipc_idx(&self) -> Option<usize> {
        for i in 0..8 {
            let region = self.regions[i];
            if i != FLASH_REGION_NUMBER && i != RAM_REGION_NUMBER && !region.is_set() {
                return Some(i);
            }
        }
        None
    }

    fn any_overlaps(&self, region: &R) -> bool {
        for ex_region in self.regions.iter() {
            if ex_region.overlaps(region) {
                return true;
            }
        }
        return false;
    }

    pub(crate) fn allocate_ipc_region<M: mpu::MPU<Region = R>>(
        &mut self,
        start: FluxPtrU8,
        size: usize,
        permissions: mpu::Permissions,
    ) -> Result<mpu::Region, ()> {
        let buf_start = start.as_usize();
        let buf_end = buf_start + size;
        let memory_start = self.breaks.memory_start();
        let memory_size = self.breaks.memory_size();
        if buf_start < memory_start.as_usize() + memory_size && memory_start.as_usize() < buf_end {
            return Err(());
        }

        let region_idx = self.next_available_ipc_idx().ok_or(())?;
        let region = M::create_exact_region(region_idx, start, size, permissions).ok_or(())?;

        // make sure new region doesn't overlap
        if self.any_overlaps(&region) {
            return Err(());
        }

        self.regions[region_idx] = region;
        let start = region.accessible_start().ok_or(())?;
        let size = region.accessible_size().ok_or(())?;
        Ok(mpu::Region::new(start, size))
    }

    pub(crate) fn allocate_app_memory<M: mpu::MPU<Region = R>>(
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8,
        flash_size: usize,
    ) -> Result<Self, AllocateAppMemoryError> {
        let mut app_regions = Self::new_regions();

        // add flash
        let flash_region = M::create_exact_region(
            FLASH_REGION_NUMBER,
            flash_start,
            flash_size,
            mpu::Permissions::ReadExecuteOnly,
        )
        .ok_or(AllocateAppMemoryError::FlashError)?;
        app_regions[FLASH_REGION_NUMBER] = flash_region;

        let ideal_region_size = cmp::max(min_memory_size, initial_app_memory_size);
        let ram_region = M::create_bounded_region(
            RAM_REGION_NUMBER,
            unallocated_memory_start,
            unallocated_memory_size,
            ideal_region_size,
            mpu::Permissions::ReadWriteOnly,
        )
        .ok_or(AllocateAppMemoryError::HeapError)?;

        let memory_start = ram_region
            .accessible_start()
            .ok_or(AllocateAppMemoryError::HeapError)?;

        let app_memory_size = ram_region
            .accessible_size()
            .ok_or(AllocateAppMemoryError::HeapError)?;
        let app_break = memory_start.wrapping_add(app_memory_size);

        // compute the total block size:
        // make it a power of two to add some space between the app and the kernel regions of memory
        let total_block_size =
            math::closest_power_of_two_usize(app_memory_size + initial_kernel_memory_size);

        // make sure we can actually fit everything into te RAM pool
        if memory_start.wrapping_add(total_block_size)
            > unallocated_memory_start.wrapping_add(unallocated_memory_size)
        {
            // We don't have enough memory left in the RAM pool to
            // give this process memory
            return Err(AllocateAppMemoryError::HeapError);
        }

        app_regions[RAM_REGION_NUMBER] = ram_region;
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

        Ok(Self {
            breaks,
            regions: app_regions,
        })
    }

    pub(crate) fn update_app_memory<M: mpu::MPU<Region = R>>(
        &mut self,
        new_app_break: FluxPtrU8Mut,
    ) -> Result<(), Error> {
        let memory_start = self.breaks.memory_start();
        let high_water_mark = self.breaks.high_water_mark;
        let kernel_break = self.kernel_break();
        if new_app_break.as_usize() > kernel_break.as_usize() {
            return Err(Error::OutOfMemory);
        }
        if new_app_break.as_usize() <= memory_start.as_usize()
            || new_app_break.as_usize() > kernel_break.as_usize()
            || new_app_break.as_usize() < high_water_mark.as_usize()
        {
            return Err(Error::AddressOutOfBounds);
        }
        let new_region_size = new_app_break.as_usize() - memory_start.as_usize();
        let new_region = M::update_region(
            memory_start,
            memory_start.as_usize() + self.breaks.memory_size(),
            new_region_size,
            RAM_REGION_NUMBER,
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
        self.breaks.app_break = FluxPtrU8::from(new_app_break);
        self.regions[RAM_REGION_NUMBER] = new_region;
        Ok(())
    }

    pub(crate) fn configure_mpu<M: mpu::MPU<Region = R>>(&self, mpu: &M) {
        mpu.configure_mpu(&self.regions);
    }
}
