use core::{cell::Cell, fmt::Display, ptr::NonNull};
use flux_support::capability::*;
use flux_support::{max_ptr, max_usize, FluxPtrU8, FluxPtrU8Mut, Pair, RArray};

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
#[flux_rs::invariant(kernel_break <= memory_start + memory_size)]
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

const MAX_RAM_REGION_NUMBER: usize = 1;
const FLASH_REGION_NUMBER: usize = 2;

#[flux_rs::refined_by(
    regions: Map<int, R>,
    breaks: AppBreaks
)]
#[flux_rs::invariant(
    // flash can access
    R::region_can_access_exactly(map_select(regions, FLASH_REGION_NUMBER), breaks.flash_start, breaks.flash_start + breaks.flash_size, mpu::Permissions { r: true, w: false, x: true }) &&
    !R::overlaps(map_select(regions, FLASH_REGION_NUMBER), 0, breaks.flash_start) &&
    !R::overlaps(map_select(regions, FLASH_REGION_NUMBER), breaks.flash_start + breaks.flash_size, u32::MAX) &&
    // ram can access
    R::regions_can_access_exactly(
        map_select(regions, MAX_RAM_REGION_NUMBER - 1),
        map_select(regions, MAX_RAM_REGION_NUMBER),
        breaks.memory_start, breaks.app_break, mpu::Permissions { r: true, w: true, x: false }
    )
    &&
    !R::overlaps(map_select(regions, MAX_RAM_REGION_NUMBER - 1), 0, breaks.memory_start) &&
    !R::overlaps(map_select(regions, MAX_RAM_REGION_NUMBER - 1), breaks.app_break, u32::MAX) &&
    !R::overlaps(map_select(regions, MAX_RAM_REGION_NUMBER), 0, breaks.memory_start) &&
    !R::overlaps(map_select(regions, MAX_RAM_REGION_NUMBER), breaks.app_break, u32::MAX)
    &&
    // no IPC region overlaps from the start to the end of memory
    R::no_region_overlaps_app_block(regions, breaks.memory_start, breaks.memory_start + breaks.memory_size)
)]
pub(crate) struct AppMemoryAllocator<R: RegionDescriptor + Display + Copy> {
    #[field(AppBreaks[breaks])]
    pub breaks: AppBreaks,
    #[field(RArray<R>[regions])]
    pub regions: RArray<R>,
    is_dirty: Cell<bool>,
    id: usize,
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

    #[flux_rs::sig(fn (&Self[@b]) -> FluxPtrU8{p: p == b.breaks.kernel_break && p <= b.breaks.memory_start + b.breaks.memory_size })]
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
            !R::is_set(r)
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

    #[flux_rs::sig(fn (self: &strg Self, buf_start_addr: FluxPtrU8Mut, size: usize) -> Result<{() | valid_size(buf_start_addr + size)}, ()> ensures self: Self)]
    pub(crate) fn add_shared_readwrite_buffer(
        &mut self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<(), ()> {
        // let breaks = &mut self.breaks.ok_or(())?;
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        if buf_start_addr.in_bounds(size) && self.in_app_ram_memory(buf_start_addr, buf_end_addr) {
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
        if new_break < self.app_break() || new_break >= self.kernel_break() {
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

    #[flux_rs::sig(fn (&Self) -> Option<{idx. usize[idx] | idx > 2 && idx < 8}>)]
    fn next_available_ipc_idx(&self) -> Option<usize> {
        let mut i = FLASH_REGION_NUMBER + 1;
        let n = self.regions.len();
        while i < n {
            let region = self.regions.get(i);
            if !region.is_set() {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    #[flux_rs::sig(fn (&Self[@app], &R[@region]) -> bool[
        R::is_set(region) &&
        exists i in 0..8 {
            R::overlaps(
                map_select(app.regions, i),
                R::start(region),
                R::start(region) + R::size(region),
            )
        }
    ])]
    fn any_overlaps(&self, region: &R) -> bool {
        let (start, end) = match (region.start(), region.size()) {
            (Some(start), Some(size)) => (start.as_usize(), start.as_usize() + size),
            _ => return false,
        };
        self.regions.get(0).overlaps(start, end)
            || self.regions.get(1).overlaps(start, end)
            || self.regions.get(2).overlaps(start, end)
            || self.regions.get(3).overlaps(start, end)
            || self.regions.get(4).overlaps(start, end)
            || self.regions.get(5).overlaps(start, end)
            || self.regions.get(6).overlaps(start, end)
            || self.regions.get(7).overlaps(start, end)
    }

    #[flux_rs::sig(fn (&Self[@app], &R[@region]) -> bool[
            R::overlaps(region, app.breaks.memory_start, app.breaks.memory_start + app.breaks.memory_size)
        ]
    )]
    fn overlaps_app_block(&self, region: &R) -> bool {
        let mem_start = self.breaks.memory_start.as_usize();
        let mem_end = mem_start + self.breaks.memory_size;
        region.overlaps(mem_start, mem_end)
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
        self.is_dirty.set(true);
        let start = region.start().ok_or(())?;
        let size = region.size().ok_or(())?;
        Ok(mpu::Region::new(start, size))
    }

    #[flux_rs::sig(
        fn (
            flash_start: FluxPtrU8,
            flash_size: usize{valid_size(flash_start + flash_size)}
        ) -> Result<R { r:
            R::is_set(r) &&
            flash_start == R::start(r) &&
            flash_start + flash_size == R::start(r) + R::size(r) &&
            R::perms(r) == mpu::Permissions { r: true, x: true, w: false }
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
        ) -> Result<Pair<R, R>{p:
            R::start(p.fst) >= mem_start &&
            ((!R::is_set(p.snd)) =>
                R::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    R::start(p.fst),
                    R::start(p.fst) + R::size(p.fst),
                    mpu::Permissions { r: true, w: true, x: false }
                )
            ) &&
            (R::is_set(p.snd) =>
                R::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    R::start(p.fst),
                    R::start(p.fst) + R::size(p.fst) + R::size(p.snd),
                    mpu::Permissions { r: true, w: true, x: false }
                )
            )
        }, ()>
    )]
    fn get_ram_regions(
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
    ) -> Result<Pair<R, R>, ()> {
        // set our stack, data, and heap up
        let ideal_region_size = flux_support::max_usize(min_memory_size, initial_app_memory_size);
        R::allocate_regions(
            MAX_RAM_REGION_NUMBER,
            unallocated_memory_start,
            unallocated_memory_size,
            ideal_region_size,
            mpu::Permissions::ReadWriteOnly,
        )
        .ok_or(())
    }

    #[flux_rs::opts(check_overflow = "strict")]
    #[flux_rs::sig(
        fn (
            ram_regions: Pair<R, R>,
            unallocated_memory_start: FluxPtrU8,
            unallocated_memory_size: usize,
            initial_kernel_memory_size: usize,
            flash_start: FluxPtrU8,
            flash_size: usize,
        ) -> Result<{b. AppBreaks[b] |
                b.memory_start == R::start(ram_regions.fst) &&
                ((!R::is_set(ram_regions.snd)) => (
                    b.app_break == R::start(ram_regions.fst) + R::size(ram_regions.fst)
                )) &&
                (R::is_set(ram_regions.snd) => (
                    b.app_break == R::start(ram_regions.fst)
                        + R::size(ram_regions.fst)
                            + R::size(ram_regions.snd)
                )) &&
                b.flash_start == flash_start &&
                b.flash_size == flash_size &&
                b.memory_start >= unallocated_memory_start &&
                valid_size(b.memory_start + b.memory_size) &&
                b.memory_start > 0 &&
                b.memory_size >= initial_kernel_memory_size
            }, ()>
            requires
                valid_size(R::size(ram_regions.fst) + initial_kernel_memory_size) &&
                R::is_set(ram_regions.fst) &&
                R::start(ram_regions.fst) >= unallocated_memory_start &&
                unallocated_memory_start + unallocated_memory_size <= u32::MAX &&
                unallocated_memory_start > 0 &&
                initial_kernel_memory_size > 0 &&
                flash_start + flash_size < unallocated_memory_start
    )]
    fn get_app_breaks(
        ram_regions: Pair<R, R>,
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8,
        flash_size: usize,
    ) -> Result<AppBreaks, ()> {
        let memory_start = ram_regions.fst.start().ok_or(())?;
        let snd_region_size = match ram_regions.snd.size() {
            Some(s) => s,
            None => 0,
        };
        let app_memory_size = ram_regions.fst.size().ok_or(())? + snd_region_size;
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
            id: usize,
            mem_start: FluxPtrU8,
            mem_size: usize,
            min_mem_size: usize,
            app_mem_size: usize,
            initial_kernel_memory_size: usize{valid_size(initial_kernel_memory_size) && initial_kernel_memory_size > 0},
            flash_start: FluxPtrU8,
            flash_size: usize,
        ) -> Result<Self { app:
                let regions = app.regions;
                let breaks = app.breaks;
                app.breaks.memory_start >= mem_start &&
                valid_size(app.breaks.memory_start + app.breaks.memory_size) &&
                app.breaks.memory_start > 0 &&
                app.breaks.memory_size >= initial_kernel_memory_size
            }, AllocateAppMemoryError>
        requires valid_size(mem_start + mem_size) && flash_start + flash_size < mem_start
    )]
    pub(crate) fn allocate_app_memory(
        id: usize,
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

        flash_region.lemma_region_can_access_exactly_implies_no_overlap(
            flash_start,
            flash_start.wrapping_add(flash_size),
            mpu::Permissions::ReadExecuteOnly,
        );

        // set the flash region
        app_regions.set(FLASH_REGION_NUMBER, flash_region);

        // ask MPU for a region covering RAM
        let ram_regions = match Self::get_ram_regions(
            unallocated_memory_start,
            unallocated_memory_size,
            min_memory_size,
            initial_app_memory_size,
        ) {
            Ok(r) => r,
            Err(_) => return Err(AllocateAppMemoryError::HeapError),
        };
        // .map_err(|_| AllocateAppMemoryError::HeapError)?;

        // For some reason flux needs this to prove our pre and post conditions
        flux_rs::assert(flash_start.as_usize() + flash_size < unallocated_memory_start.as_usize());

        let Some(ram0_size) = ram_regions.fst.size() else {
            return Err(AllocateAppMemoryError::HeapError);
        };
        if ram0_size > (u32::MAX as usize) - initial_kernel_memory_size {
            return Err(AllocateAppMemoryError::HeapError);
        }

        // Get the app breaks using the RAM region
        let breaks = Self::get_app_breaks(
            ram_regions,
            unallocated_memory_start,
            unallocated_memory_size,
            initial_kernel_memory_size,
            flash_start,
            flash_size,
        )
        .map_err(|_| AllocateAppMemoryError::HeapError)?;

        R::lemma_regions_can_access_exactly_implies_no_overlap(
            &ram_regions.fst,
            &ram_regions.snd,
            breaks.memory_start,
            breaks.app_break,
            mpu::Permissions::ReadWriteOnly,
        );
        let memory_end = breaks.memory_start.wrapping_add(breaks.memory_size);
        app_regions
            .get(FLASH_REGION_NUMBER)
            .lemma_region_can_access_flash_implies_no_app_block_overlaps(
                breaks.flash_start,
                breaks.flash_start.wrapping_add(breaks.flash_size),
                breaks.memory_start,
                memory_end,
            );
        app_regions
            .get(3)
            .lemma_region_not_set_implies_no_overlap(breaks.memory_start, memory_end);
        app_regions
            .get(4)
            .lemma_region_not_set_implies_no_overlap(breaks.memory_start, memory_end);
        app_regions
            .get(5)
            .lemma_region_not_set_implies_no_overlap(breaks.memory_start, memory_end);
        app_regions
            .get(6)
            .lemma_region_not_set_implies_no_overlap(breaks.memory_start, memory_end);
        app_regions
            .get(7)
            .lemma_region_not_set_implies_no_overlap(breaks.memory_start, memory_end);

        // Set the RAM region
        app_regions.set(MAX_RAM_REGION_NUMBER - 1, ram_regions.fst);
        app_regions.set(MAX_RAM_REGION_NUMBER, ram_regions.snd);

        // TODO: need a lemma to establish that flash_region won't overlap with app block
        Ok(Self {
            breaks,
            regions: app_regions,
            is_dirty: Cell::new(true),
            id,
        })
    }

    #[flux_rs::sig(fn (self: &strg Self, new_app_break: FluxPtrU8Mut) -> Result<FluxPtrU8, Error> ensures self: Self)]
    pub(crate) fn update_app_memory(
        &mut self,
        new_app_break: FluxPtrU8Mut,
    ) -> Result<FluxPtrU8, Error> {
        let memory_start = self.breaks.memory_start;
        let high_water_mark = self.breaks.high_water_mark;
        let kernel_break = self.breaks.kernel_break;
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
        let new_regions = R::update_regions(
            memory_start,
            self.memory_size(),
            new_region_size,
            MAX_RAM_REGION_NUMBER,
            mpu::Permissions::ReadWriteOnly,
        )
        .ok_or(Error::OutOfMemory)?;

        let snd_region_size = match new_regions.snd.size() {
            Some(s) => s,
            None => 0,
        };
        let app_memory_size = new_regions.fst.size().ok_or(Error::KernelError)? + snd_region_size;
        let new_app_break = memory_start.as_usize() + app_memory_size;

        if new_app_break > kernel_break.as_usize() {
            return Err(Error::OutOfMemory);
        }

        let old_break = self.breaks.app_break;
        self.breaks.app_break = FluxPtrU8::from(new_app_break);

        R::lemma_regions_can_access_exactly_implies_no_overlap(
            &new_regions.fst,
            &new_regions.snd,
            self.breaks.memory_start,
            self.breaks.app_break,
            mpu::Permissions::ReadWriteOnly,
        );

        let mem_end = self
            .breaks
            .memory_start
            .wrapping_add(self.breaks.memory_size);
        new_regions
            .fst
            .lemma_no_overlap_le_addr_implies_no_overlap_addr(self.breaks.app_break, mem_end);
        new_regions
            .snd
            .lemma_no_overlap_le_addr_implies_no_overlap_addr(self.breaks.app_break, mem_end);

        self.regions.set(MAX_RAM_REGION_NUMBER - 1, new_regions.fst);
        self.regions.set(MAX_RAM_REGION_NUMBER, new_regions.snd);
        self.is_dirty.set(true);

        flux_rs::assert(self.breaks.app_break >= self.breaks.high_water_mark);
        Ok(old_break)
    }

    pub(crate) fn configure_mpu<M: mpu::MPU<Region = R>>(
        &self,
        mpu: &M,
    ) -> MpuConfiguredCapability {
        mpu.configure_mpu(&self.regions, self.id, self.is_dirty.get());
        self.is_dirty.set(false);
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
