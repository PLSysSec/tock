use core::{fmt::Display, ptr::NonNull};

use flux_support::capability::*;
use flux_support::{max_ptr, max_usize, FluxPtrU8, FluxPtrU8Mut, RArray};

use crate::{
    platform::mpu::{self, RegionDescriptor},
    process::{Error, ProcessCustomGrantIdentifier},
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
#[flux_rs::invariant(memory_start + memory_size <= u32::MAX)]
#[flux_rs::invariant(kernel_break < memory_start + memory_size)]
#[flux_rs::invariant(flash_start + flash_size < memory_start)]
#[flux_rs::invariant(app_break >= high_water_mark)]
#[flux_rs::invariant(app_break <= kernel_break)]
#[flux_rs::invariant(high_water_mark >= memory_start)]
pub(crate) struct AppBreaks {
    #[field(FluxPtrU8[memory_start])]
    pub memory_start: FluxPtrU8,
    #[field(usize[memory_size])]
    pub memory_size: usize,
    #[field(FluxPtrU8[app_break])]
    pub app_break: FluxPtrU8,
    #[field(FluxPtrU8[high_water_mark])]
    pub high_water_mark: FluxPtrU8,
    #[field(FluxPtrU8[kernel_break])]
    pub kernel_break: FluxPtrU8,
    #[field(FluxPtrU8[flash_start])]
    pub flash_start: FluxPtrU8,
    #[field(usize[flash_size])]
    pub flash_size: usize,
}

const RAM_REGION_NUMBER: usize = 0;
const FLASH_REGION_NUMBER: usize = 1;

#[flux_rs::refined_by(
    regions: Map<int, R>,
    breaks: AppBreaks
)]
#[flux_rs::invariant(
    // flash can access
    <R as RegionDescriptor>::region_can_access(map_select(regions, FLASH_REGION_NUMBER), breaks.flash_start, breaks.flash_start + breaks.flash_size, mpu::Permissions { r: true, w: false, x: true }) &&
    <R as RegionDescriptor>::region_cant_access_at_all(map_select(regions, FLASH_REGION_NUMBER), 0, breaks.flash_start - 1) &&
    <R as RegionDescriptor>::region_cant_access_at_all(map_select(regions, FLASH_REGION_NUMBER), breaks.flash_start + breaks.flash_size + 1, u32::MAX) &&
    // ram can access
    <R as RegionDescriptor>::region_can_access(map_select(regions, RAM_REGION_NUMBER), breaks.memory_start, breaks.app_break, mpu::Permissions { r: true, w: true, x: false }) &&
    <R as RegionDescriptor>::region_cant_access_at_all(map_select(regions, RAM_REGION_NUMBER), 0, breaks.memory_start - 1) &&
    <R as RegionDescriptor>::region_cant_access_at_all(map_select(regions, RAM_REGION_NUMBER), breaks.app_break + 1, u32::MAX) &&
    // no IPC region overlaps from the start to the end of memory
    <R as RegionDescriptor>::no_region_overlaps_app_block(regions, breaks.high_water_mark, breaks.memory_start + breaks.memory_size)
)]
pub(crate) struct AppMemoryAllocator<R: RegionDescriptor + Display + Copy> {
    #[field(AppBreaks[breaks])]
    pub breaks: AppBreaks,
    #[field(RArray<R>[regions])]
    pub regions: RArray<R>,
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
    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8[b.breaks.flash_start])]
    pub(crate) fn flash_start(&self) -> FluxPtrU8 {
        self.breaks.flash_start
    }

    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8[b.breaks.flash_start + b.breaks.flash_size])]
    pub(crate) fn flash_end(&self) -> FluxPtrU8 {
        self.breaks.flash_start.wrapping_add(self.breaks.flash_size)
    }

    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8[b.breaks.memory_start])]
    pub(crate) fn memory_start(&self) -> FluxPtrU8 {
        self.breaks.memory_start
    }

    #[flux_rs::sig(fn (&Self[@b]) -> usize[b.breaks.memory_size])]
    pub(crate) fn memory_size(&self) -> usize {
        self.breaks.memory_size
    }

    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8[b.breaks.memory_start + b.breaks.memory_size])]
    pub(crate) fn memory_end(&self) -> FluxPtrU8 {
        self.breaks
            .memory_start
            .wrapping_add(self.breaks.memory_size)
    }

    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8[b.breaks.app_break])]
    pub(crate) fn app_break(&self) -> FluxPtrU8 {
        self.breaks.app_break
    }

    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8{p: p == b.breaks.kernel_break && p < b.breaks.memory_start + b.breaks.memory_size })]
    pub(crate) fn kernel_break(&self) -> FluxPtrU8 {
        self.breaks.kernel_break
    }

    #[flux_rs::sig(fn (&Self[@b], start: FluxPtrU8, end: FluxPtrU8) -> bool[end >= start && start >= b.breaks.memory_start && end <= b.breaks.app_break])]
    pub(crate) fn in_app_ram_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> bool {
        end >= start && start >= self.breaks.memory_start && end <= self.breaks.app_break
    }

    #[flux_rs::sig(fn (&Self[@b], start: FluxPtrU8, end: FluxPtrU8) -> bool[end >= start && start >= b.breaks.flash_start && end <= b.breaks.flash_start + b.breaks.flash_size])]
    pub(crate) fn in_app_flash_memory(&self, start: FluxPtrU8, end: FluxPtrU8) -> bool {
        end >= start
            && start >= self.breaks.flash_start
            && end <= self.breaks.flash_start.wrapping_add(self.breaks.flash_size)
    }

    #[flux_rs::sig(fn () -> RArray<R>{regions:
        forall i in 0..8 {
            let r = map_select(regions, i);
            !<R as RegionDescriptor>::is_set(r)
        }
    })]
    fn new_regions() -> RArray<R> {
        let regions = [R::default(0); 8];
        let mut regions = RArray::new(regions);

        regions.set(0, R::default(0));
        regions.set(1, R::default(1));
        regions.set(2, R::default(2));
        regions.set(3, R::default(3));
        regions.set(4, R::default(4));
        regions.set(5, R::default(5));
        regions.set(6, R::default(6));
        regions.set(7, R::default(7));

        regions
    }

    #[flux_rs::sig(fn (self: &strg Self, _, _) -> Result<(), ()> ensures self: Self)]
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
            flux_support::assert(new_water_mark >= self.breaks.high_water_mark);
            flux_support::assert(new_water_mark <= self.memory_end());
            self.breaks.high_water_mark = new_water_mark;
            Ok(())
        } else if self.in_app_flash_memory(buf_start_addr, buf_end_addr) {
            Ok(())
        } else {
            Err(())
        }
    }

    #[flux_rs::sig(fn (self: &strg Self, _, _) -> Result<(), ()> ensures self: Self)]
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

    #[flux_rs::sig(fn (self: &strg Self, _, _) -> Result<_, _> ensures self: Self)]
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

    #[flux_rs::sig(
        fn (self: &strg Self[@old_bc], usize, usize) -> Option<{p. FluxPtrU8[p] | p < bc.breaks.memory_start + bc.breaks.memory_size}>[#opt]
            ensures self: Self[#bc],
            (opt => bc.breaks.kernel_break >= bc.breaks.app_break) &&
            (!opt => bc == old_bc)
    )]
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

    #[flux_rs::sig(
        fn (
            self: &strg Self[@old_app],
            { FluxPtrU8[@new_break] | new_break >= old_app.breaks.app_break && new_break < old_app.breaks.memory_start + old_app.breaks.memory_size }
        ) ensures self: Self[{breaks: AppBreaks { kernel_break: new_break, ..old_app.breaks }, ..old_app}]
    )]
    fn set_kernel_break(&mut self, new_break: FluxPtrU8) {
        self.breaks.kernel_break = new_break;
    }

    #[flux_rs::sig(fn (&Self) -> Option<{idx. usize[idx] | idx > 1 && idx < 8}>)]
    #[flux_rs::trusted(
        reason = "invariant might not hold (when place is folded) - there's no mutation"
    )]
    fn next_available_ipc_idx(&self) -> Option<usize> {
        let mut i = 0;
        while i < self.regions.len() {
            let region = self.regions.get(i);
            if i != FLASH_REGION_NUMBER && i != RAM_REGION_NUMBER && !region.is_set() {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    #[flux_rs::sig(fn (&Self[@app], &R[@region]) -> bool[exists i in 0..8 {
        <R as RegionDescriptor>::overlaps(region, map_select(app.regions, i))
    }])]
    fn any_overlaps(&self, region: &R) -> bool {
        region.overlaps(&self.regions.get(0))
            || region.overlaps(&self.regions.get(1))
            || region.overlaps(&self.regions.get(2))
            || region.overlaps(&self.regions.get(3))
            || region.overlaps(&self.regions.get(4))
            || region.overlaps(&self.regions.get(5))
            || region.overlaps(&self.regions.get(6))
            || region.overlaps(&self.regions.get(7))
    }

    #[flux_rs::sig(fn () -> usize[10])]
    fn test() -> usize {
        let mut n0 = 0;
        n0 += 1;
        n0 += 2;
        n0 += 3;
        n0 += 4;
        n0
    }

    #[flux_rs::sig(fn (&Self[@app], &R[@region]) -> bool[
            <R as RegionDescriptor>::region_overlaps_app_block(region, app.breaks.memory_start, app.breaks.memory_start + app.breaks.memory_size)
        ]
    )]
    fn overlaps_app_block(&self, region: &R) -> bool {
        let (start, end) = match (R::start(region), R::size(region)) {
            (Some(start), Some(size)) => {
                let start_us = start.as_usize();
                (start_us, start_us + size)
            }
            _ => return false,
        };

        let _ = Self::test();
        let mem_end = self.memory_end().as_usize();
        let mem_start = self.breaks.memory_start.as_usize();
        end >= start
            && ((start >= mem_start && end <= mem_end) || (end >= mem_start && end <= mem_end))
    }

    #[flux_rs::sig(fn (self: &strg Self, start: FluxPtrU8, size: usize{valid_size(start + size)}, _) -> Result<_, _> ensures self: Self)]
    pub(crate) fn allocate_ipc_region(
        &mut self,
        start: FluxPtrU8,
        size: usize,
        permissions: mpu::Permissions,
    ) -> Result<mpu::Region, ()> {
        let buf_start = start.as_usize();
        let buf_end = buf_start + size;
        let memory_start = self.memory_start();
        let memory_size = self.memory_size();
        if buf_start < memory_start.as_usize() + memory_size && memory_start.as_usize() < buf_end {
            return Err(());
        }

        let region_idx = self.next_available_ipc_idx().ok_or(())?;
        let region = R::create_exact_region(region_idx, start, size, permissions).ok_or(())?;

        // make sure new region doesn't overlap
        if self.any_overlaps(&region) || self.overlaps_app_block(&region) {
            return Err(());
        }

        self.regions.set(region_idx, region);
        let start = region.start().ok_or(())?;
        let size = region.size().ok_or(())?;
        Ok(mpu::Region::new(start, size))
    }

    #[flux_rs::sig(
        fn (
            flash_start: FluxPtrU8,
            flash_size: usize{valid_size(flash_start + flash_size)}
        ) -> Result<{r. R[r] |
            <R as RegionDescriptor>::is_set(r) &&
            <R as RegionDescriptor>::rnum(r) == FLASH_REGION_NUMBER &&
            <R as RegionDescriptor>::start(r) == flash_start &&
            <R as RegionDescriptor>::size(r) == flash_size &&
            <R as RegionDescriptor>::perms(r) == mpu::Permissions { r: true, x: true, w: false }
        }, ()>
    )]
    fn get_flash_region(flash_start: FluxPtrU8, flash_size: usize) -> Result<R, ()> {
        R::create_exact_region(
            FLASH_REGION_NUMBER,
            flash_start,
            flash_size,
            mpu::Permissions::ReadExecuteOnly,
        )
        .ok_or(())
    }

    #[flux_rs::sig(
        fn (
            mem_start: FluxPtrU8,
            mem_size: usize{valid_size(mem_start + mem_size)},
            min_size: usize,
            app_mem_size: usize
        ) -> Result<{r. R[r] |
            <R as RegionDescriptor>::is_set(r) &&
            <R as RegionDescriptor>::rnum(r) == RAM_REGION_NUMBER &&
            <R as RegionDescriptor>::start(r) >= mem_start  &&
            <R as RegionDescriptor>::size(r) >= min_size &&
            <R as RegionDescriptor>::size(r) >= app_mem_size &&
            <R as RegionDescriptor>::start(r) + <R as RegionDescriptor>::size(r) >= <R as RegionDescriptor>::start(r) + min_size &&
            <R as RegionDescriptor>::perms(r) == mpu::Permissions { r: true, w: true, x: false }
         }, ()>
    )]
    fn get_ram_region(
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
    ) -> Result<R, ()> {
        // set our stack, data, and heap up
        let ideal_region_size = flux_support::max_usize(min_memory_size, initial_app_memory_size);
        R::create_bounded_region(
            RAM_REGION_NUMBER,
            unallocated_memory_start,
            unallocated_memory_size,
            ideal_region_size,
            mpu::Permissions::ReadWriteOnly,
        )
        .ok_or(())
    }

    #[flux_rs::trusted(reason = "flux wrappers/debugging")]
    #[flux_rs::sig(fn (x: usize, y: usize) -> usize[x + y] requires valid_size(x + y))]
    fn fake_add(x: usize, y: usize) -> usize {
        x + y
    }

    #[flux::opts(check_overflow = "strict")]
    #[flux_rs::sig(
        fn (
            ram_region: R,
            unallocated_memory_start: FluxPtrU8,
            unallocated_memory_size: usize,
            initial_kernel_memory_size: usize,
            flash_start: FluxPtrU8,
            flash_size: usize,
        ) -> Result<{b. AppBreaks[b] |
                b.memory_start == <R as RegionDescriptor>::start(ram_region) &&
                b.app_break == <R as RegionDescriptor>::start(ram_region) + <R as RegionDescriptor>::size(ram_region) &&
                b.flash_start == flash_start &&
                b.flash_size == flash_size &&
                b.memory_start >= unallocated_memory_start &&
                valid_size(b.memory_start + b.memory_size) &&
                b.memory_start > 0 &&
                b.memory_size >= initial_kernel_memory_size
            }, ()>
            requires
                <R as RegionDescriptor>::start(ram_region) >= unallocated_memory_start &&
                valid_size(unallocated_memory_start + unallocated_memory_size) &&
                unallocated_memory_start > 0 &&
                initial_kernel_memory_size > 0 &&
                flash_start + flash_size < unallocated_memory_start &&
                valid_size(<R as RegionDescriptor>::size(ram_region) + initial_kernel_memory_size)
    )]
    fn get_app_breaks(
        ram_region: R,
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8,
        flash_size: usize,
    ) -> Result<AppBreaks, ()> {
        let memory_start = ram_region.start().ok_or(())?;
        let app_memory_size = ram_region.size().ok_or(())?;
        let app_break = memory_start.as_usize() + app_memory_size;

        // compute the total block size:
        let total_block_size = app_memory_size + initial_kernel_memory_size;

        let block_end = memory_start.as_usize() + total_block_size;

        // make sure we can actually fit everything into te RAM pool
        if block_end > unallocated_memory_start.as_usize() + unallocated_memory_size {
            // We don't have enough memory left in the RAM pool to
            // give this process memory
            return Err(());
        }
        // compute breaks
        let high_water_mark = memory_start;
        let kernel_break = block_end - initial_kernel_memory_size;
        Ok(AppBreaks {
            memory_start,
            memory_size: total_block_size,
            app_break: FluxPtrU8::from(app_break),
            high_water_mark,
            kernel_break: FluxPtrU8::from(kernel_break),
            flash_start,
            flash_size,
        })
    }

    #[flux_rs::sig(
        fn (
            mem_start: FluxPtrU8,
            mem_size: usize,
            min_mem_size: usize,
            app_mem_size: usize,
            kernel_mem_size: usize,
            flash_start: FluxPtrU8,
            flash_size: usize,
        ) -> Result<{app. Self[app] |
                let regions = app.regions;
                let breaks = app.breaks;
                app.breaks.memory_start >= mem_start &&
                valid_size(app.breaks.memory_start + app.breaks.memory_size) &&
                app.breaks.memory_start > 0 &&
                app.breaks.memory_size >= kernel_mem_size
            }, AllocateAppMemoryError>
        requires valid_size(mem_start + mem_size) && flash_start + flash_size < mem_start && kernel_mem_size > 0
    )]
    pub(crate) fn allocate_app_memory(
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8,
        flash_size: usize,
    ) -> Result<Self, AllocateAppMemoryError> {
        if unallocated_memory_start.as_usize() + unallocated_memory_size > u32::MAX as usize {
            // VTOCK TODO: this isn't possible because usize IS u32 on tock archs but Flux doesn't know that
            // We should be able to fix that
            return Err(AllocateAppMemoryError::HeapError);
        }

        let mut app_regions = Self::new_regions();

        // ask MPU for a region covering flash
        let flash_region = Self::get_flash_region(flash_start, flash_size)
            .map_err(|_| AllocateAppMemoryError::FlashError)?;

        app_regions.set(FLASH_REGION_NUMBER, flash_region);

        // ask MPU for a region covering RAM
        let ram_region = Self::get_ram_region(
            unallocated_memory_start,
            unallocated_memory_size,
            min_memory_size,
            initial_app_memory_size,
        )
        .map_err(|_| AllocateAppMemoryError::HeapError)?;

        // For some reason flux needs this to prove our pre and post conditions
        flux_rs::assert(flash_start.as_usize() + flash_size < unallocated_memory_start.as_usize());
        // flux wants this to cough up the invariant
        // ram_region.start() + ram_region.size() <=u32::MAX,
        // which combines with initial_app_memory_size <= ram_region.size()
        // to check get_app_breaks
        let _ = ram_region.size();

        // Get the app breaks using the RAM region
        let breaks = Self::get_app_breaks(
            ram_region,
            unallocated_memory_start,
            unallocated_memory_size,
            initial_kernel_memory_size,
            flash_start,
            flash_size,
        )
        .map_err(|_| AllocateAppMemoryError::HeapError)?;

        // Set the RAM region
        app_regions.set(RAM_REGION_NUMBER, ram_region);

        Ok(Self {
            breaks,
            regions: app_regions,
        })
    }

    #[flux_rs::sig(fn (&R[@r], FluxPtrU8[@mem_start], usize[@mem_end])
        requires
            <R as RegionDescriptor>::region_can_access(r, mem_start, mem_end, mpu::Permissions { r: true, w: true, x: false }) &&
            <R as RegionDescriptor>::region_cant_access_at_all(r, 0, mem_start - 1) &&
            <R as RegionDescriptor>::region_cant_access_at_all(r, mem_end + 1, u32::MAX)
    )]
    fn check_pred(region: &R, mem_start: FluxPtrU8, mem_end: usize) {}

    #[flux_rs::sig(fn (self: &strg Self, new_app_break: FluxPtrU8Mut) -> Result<(), Error> ensures self: Self)]
    pub(crate) fn update_app_memory(&mut self, new_app_break: FluxPtrU8Mut) -> Result<(), Error> {
        let memory_start = self.breaks.memory_start; // self.memory_start();
        let high_water_mark = self.breaks.high_water_mark;
        let kernel_break = self.breaks.kernel_break; // self.kernel_break();
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
        let new_region = R::update_region(
            memory_start,
            memory_start.as_usize() + self.memory_size(),
            new_region_size,
            RAM_REGION_NUMBER,
            mpu::Permissions::ReadWriteOnly,
        )
        .ok_or(Error::OutOfMemory)?;

        let new_app_break = new_region.start().ok_or(Error::KernelError)?.as_usize()
            + new_region.size().ok_or(Error::KernelError)?;

        if new_app_break > kernel_break.as_usize() {
            return Err(Error::OutOfMemory);
        }
        self.breaks.app_break = FluxPtrU8::from(new_app_break);
        self.regions.set(RAM_REGION_NUMBER, new_region);

        let new_region = self.regions.get(RAM_REGION_NUMBER);
        let mem_start = self.breaks.memory_start;
        let mem_end = self.breaks.app_break.as_usize();

        Self::check_pred(&new_region, mem_start, mem_end);

        Ok(())
    }

    pub(crate) fn configure_mpu<M: mpu::MPU<Region = R>>(
        &self,
        mpu: &M,
    ) -> MpuConfiguredCapability {
        mpu.configure_mpu(&self.regions);
        MpuConfiguredCapability::new(self.memory_start(), self.app_break())
    }

    pub(crate) unsafe fn set_byte(&self, mut addr: FluxPtrU8Mut, value: u8) -> bool {
        let end = addr.wrapping_add(1);
        if self.in_app_ram_memory(addr, end) {
            // We verify that this will only write process-accessible memory,
            // but this can still be undefined behavior if something else holds
            // a reference to this memory.
            *addr = value;
            true
        } else {
            false
        }
    }
}
