use core::{cmp, fmt::Display};

use flux_support::{FluxPtrU8, FluxPtrU8Mut};

#[derive(Copy, Clone, Debug)]
#[flux_rs::refined_by(r: bool, w: bool, x: bool)]
pub enum BlockPermissions {
    #[flux::variant(BlockPermissions[true, true, true])]
    ReadWriteExecute,
    #[flux::variant(BlockPermissions[true, true, false])]
    ReadWriteOnly,
    #[flux::variant(BlockPermissions[true, false, true])]
    ReadExecuteOnly,
    #[flux::variant(BlockPermissions[true, false, false])]
    ReadOnly,
    #[flux::variant(BlockPermissions[false, false, true])]
    ExecuteOnly,
}

#[flux_rs::refined_by(memory_start: int, app_break: int)]
pub struct AllocatedAppBreaks {
    #[field(FluxPtrU8[memory_start])]
    pub memory_start: FluxPtrU8,
    #[field(FluxPtrU8[app_break])]
    pub app_break: FluxPtrU8,
}

impl AllocatedAppBreaks {
    #[flux_rs::sig(fn (FluxPtrU8[@memory_start], FluxPtrU8[@app_break]) -> AllocatedAppBreaks[memory_start, app_break])]
    pub fn new(memory_start: FluxPtrU8, app_break: FluxPtrU8) -> Self {
        Self {
            memory_start,
            app_break,
        }
    }
}

pub enum AllocateAppMemoryError {
    HeapError,
    FlashError,
    ProcessUnitializedError,
}

#[flux_rs::refined_by(memory_start: int, app_break: int, memory_size: int)]
pub struct AllocatedAppBreaksAndSize {
    #[field(AllocatedAppBreaks[memory_start, app_break])]
    pub breaks: AllocatedAppBreaks,
    #[field(usize[memory_size])]
    pub memory_size: usize,
}

impl AllocatedAppBreaksAndSize {
    #[flux_rs::sig(fn (FluxPtrU8[@memory_start], FluxPtrU8[@app_break], memory_size: usize) -> AllocatedAppBreaksAndSize[memory_start, app_break, memory_size])]
    pub fn new(memory_start: FluxPtrU8, app_break: FluxPtrU8, memory_size: usize) -> Self {
        Self {
            breaks: AllocatedAppBreaks::new(memory_start, app_break),
            memory_size,
        }
    }
}

pub struct AppAccessibleRegion<T: DescribeRegion> {
    pub region: T,
    pub permissions: BlockPermissions,
}

pub struct AppAccessibleMemory<M: MPUVerified> {
    pub(crate) regions: [Option<AppAccessibleRegion<M::Region>>; MPUVerified::NUM_REGIONS],
    pub(crate) app_heap_idx: Option<usize>,
    pub(crate) app_flash_idx: Option<usize>,
    pub(crate) mpu: M,
}

impl<M: MPUVerified> AppAccessibleMemory<M> {
    pub fn next_available_idx(&self) -> Option<usize> {
        for (i, region) in self.regions.iter().enumerate() {
            if region.is_none() {
                return Some(i);
            }
        }
        None
    }

    pub fn new(mpu: M) -> Self {
        Self {
            regions: [const { None }; NUM_REGIONS],
            app_heap_idx: None,
            app_flash_idx: None,
            mpu,
        }
    }

    pub fn reset(&mut self) {
        for b in self.regions.iter_mut() {
            *b = None;
        }
        self.app_heap_idx = None;
        self.app_flash_idx = None;
    }

    pub fn remove_memory_region(&mut self, region: <M as MPUVerified>::Region) -> Result<(), ()> {
        todo!()
    }

    pub fn allocate_ipc_region(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: crate::platform::allocator::BlockPermissions,
    ) -> Result<(), ()> {
        let region_idx = self.next_available_idx().ok_or(())?;
        let region = self
            .mpu
            .new_region(
                unallocated_memory_start,
                unallocated_memory_size,
                min_region_size,
            )
            .ok_or(())?;
        self.regions[region_idx] = Some(crate::platform::allocator::AppAccessibleRegion {
            region,
            permissions,
        });
        Ok(())
    }

    fn add_flash_region(&mut self, flash_start: FluxPtrU8, flash_size: usize) -> Result<(), ()> {
        let app_flash_idx = self.next_available_idx().ok_or(())?;
        let region = self
            .mpu
            .new_region(flash_start, flash_size, flash_size)
            .ok_or(())?;
        self.regions[app_flash_idx] = Some(AppAccessibleRegion {
            region,
            permissions: BlockPermissions::ReadExecuteOnly,
        });
        self.app_flash_idx = Some(app_flash_idx);
        Ok(())
    }

    fn add_heap_region(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
    ) -> Result<(), ()> {
        let region_size = cmp::min(
            min_memory_size,
            initial_app_memory_size + initial_kernel_memory_size,
        );
        let mut region = self
            .mpu
            .new_region(
                unallocated_memory_start,
                unallocated_memory_size,
                region_size,
            )
            .ok_or(())?;
        let region_start = region.accessible_start();
        let app_break = region_start.as_usize() + region.accessible_size();

        let mut total_size = region.region_size();
        let kernel_break = region_start.as_usize() + total_size - initial_kernel_memory_size;
        if app_break > kernel_break {
            total_size *= 2;
            region = self
                .mpu
                .new_region(
                    unallocated_memory_start,
                    unallocated_memory_size,
                    total_size,
                )
                .ok_or(())?;
        }
        let app_heap_idx = self
            .next_available_idx()
            .ok_or(AllocateAppMemoryError::HeapError)?;
        self.regions[app_heap_idx] = Some(AppAccessibleRegion {
            region,
            permissions: BlockPermissions::ReadWriteOnly,
        });
        self.app_heap_idx = Some(app_heap_idx);
        Ok(())
    }

    pub fn allocate_app_memory(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8Mut,
        flash_size: usize,
    ) -> Result<(), crate::platform::allocator::AllocateAppMemoryError> {
        self.add_flash_region(flash_start, flash_size)
            .map_err(AllocateAppMemoryError::FlashError)?;
        self.add_heap_region(
            unallocated_memory_start,
            unallocated_memory_size,
            min_memory_size,
            initial_app_memory_size,
            initial_kernel_memory_size,
        )
        .map_err(AllocateAppMemoryError::HeapError)
    }

    pub fn update_app_memory(
        &mut self,
        app_memory_break: FluxPtrU8Mut,
        kernel_memory_break: FluxPtrU8Mut,
    ) -> Result<(), ()> {
        let idx = self.app_heap_idx.ok_or(())?;
        let current_region = self.regions[idx].as_ref().ok_or(())?;
        let memory_start = current_region.region.accessible_start();
        let total_size = current_region.region.region_size();
        let memory_end = memory_start.as_usize() + total_size;
        if app_memory_break.as_usize() > kernel_memory_break.as_usize()
            || app_memory_break.as_usize() <= memory_start.as_usize()
            || app_memory_break.as_usize() > memory_end
        {
            return Err(());
        }
        let new_region_size = app_memory_break.as_usize() - memory_start.as_usize();
        // TODO: Make sure that this preserves the region size we ask for
        let new_region = self
            .mpu
            .new_region(memory_start, total_size, new_region_size)
            .ok_or(())?;
        let new_app_break = new_region.accessible_start().as_usize() + new_region.accessible_size();
        if new_app_break > kernel_memory_break.as_usize() {
            return Err(());
        }
        self.regions[idx] = Some(crate::platform::allocator::AppAccessibleRegion {
            region: new_region,
            permissions: BlockPermissions::ReadWriteOnly,
        });
        Ok(())
    }
}

pub(crate) trait DescribeRegion {
    fn accessible_start(&self) -> FluxPtrU8;
    fn region_start(&self) -> FluxPtrU8;
    fn accessible_size(&self) -> usize;
    fn region_size(&self) -> usize;
}

pub(crate) trait MPUVerified {
    /// MPU-specific state that defines a particular configuration for the MPU.
    /// That is, this should contain all of the required state such that the
    /// implementation can be passed an object of this type and it should be
    /// able to correctly and entirely configure the MPU.
    ///
    /// This state will be held on a per-process basis as a way to cache all of
    /// the process settings. When the kernel switches to a new process it will
    /// use the `MpuConfig` for that process to quickly configure the MPU.
    ///
    /// It is `Default` so we can create empty state when the process is
    /// created, and `Display` so that the `panic!()` output can display the
    /// current state to help with debugging.
    // type MpuConfig: Display;
    type Region: DescribeRegion;
    const NUM_REGIONS: usize;

    /// Enables the MPU for userspace apps.
    ///
    /// This function must enable the permission restrictions on the various
    /// regions protected by the MPU.
    // #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{r: <Self as MPU>::enabled(r)})]
    fn enable_app_mpu(&mut self);

    /// Disables the MPU for userspace apps.
    ///
    /// This function must disable any access control that was previously setup
    /// for an app if it will interfere with the kernel.
    /// This will be called before the kernel starts to execute as on some
    /// platforms the MPU rules apply to privileged code as well, and therefore
    /// some of the MPU configuration must be disabled for the kernel to effectively
    /// manage processes.
    fn disable_app_mpu(&mut self);

    /// Returns the maximum number of regions supported by the MPU.
    fn number_total_regions(&self) -> usize;

    fn new_region(
        &self,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
    ) -> Option<Self::Region>;

    /// Configures the MPU with the provided region configuration.
    ///
    /// An implementation must ensure that all memory locations not covered by
    /// an allocated region are inaccessible in user mode and accessible in
    /// supervisor mode.
    ///
    /// # Arguments
    ///
    /// - `config`: MPU region configuration
    fn configure_mpu(&mut self, config: &Self::Region);
}
