use core::fmt::Display;

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

pub struct AppAccessibleMemory<T: DescribeRegion, const NUM_REGIONS: usize> {
    pub(crate) regions: [Option<AppAccessibleRegion<T>>; NUM_REGIONS],
    pub(crate) app_region_idx: Option<usize>,
}

impl<T: DescribeRegion, const NUM_REGIONS: usize> AppAccessibleMemory<T, NUM_REGIONS> {
    pub fn next_available_idx(&self) -> Option<usize> {
        for (i, region) in self.regions.iter().enumerate() {
            if region.is_none() {
                return Some(i);
            }
        }
        None
    }

    pub fn reset(&mut self) {
        for b in self.regions.iter_mut() {
            *b = None;
        }
        self.app_region_idx = None;
    }
}

pub(crate) trait ProcessMemoryAllocator<M: MPUVerified, const NUM_REGIONS: usize> {
    fn new(&self) -> AppAccessibleMemory<<M as MPUVerified>::T, NUM_REGIONS>;

    fn reset(&mut self);

    fn allocate_new_block(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: BlockPermissions,
    ) -> Result<(), ()>;

    fn remove_memory_region(&mut self, region: <M as MPUVerified>::T) -> Result<(), ()>;

    fn allocate_app_memory(
        &self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        flash_start: FluxPtrU8Mut,
        flash_size: usize,
    ) -> Result<AppAccessibleRegion<<M as MPUVerified>::T>, AllocateAppMemoryError>;

    fn update_app_memory(
        &mut self,
        app_memory_break: FluxPtrU8Mut,
        kernel_memory_break: FluxPtrU8Mut,
    ) -> Result<(), ()>;
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
    type T: DescribeRegion;
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
    ) -> Option<Self::T>;

    /// Configures the MPU with the provided region configuration.
    ///
    /// An implementation must ensure that all memory locations not covered by
    /// an allocated region are inaccessible in user mode and accessible in
    /// supervisor mode.
    ///
    /// # Arguments
    ///
    /// - `config`: MPU region configuration
    fn configure_mpu(&mut self, config: &Self::T);
}
