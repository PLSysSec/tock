use core::{cmp, fmt::Display};

use flux_support::{FluxPtrU8, FluxPtrU8Mut};

use crate::{
    platform::mpu::{self, RegionDescriptor},
    process::Error,
};

#[derive(Copy, Clone, Debug)]
#[flux_rs::refined_by(r: bool, w: bool, x: bool)]
pub enum RegionPermissions {
    #[flux::variant(RegionPermissions[true, true, true])]
    ReadWriteExecute,
    #[flux::variant(RegionPermissions[true, true, false])]
    ReadWriteOnly,
    #[flux::variant(RegionPermissions[true, false, true])]
    ReadExecuteOnly,
    #[flux::variant(RegionPermissions[true, false, false])]
    ReadOnly,
    #[flux::variant(RegionPermissions[false, false, true])]
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

pub struct AppAccessibleMemory<M: mpu::MPU, const NUM_IPC_REGIONS: usize> {
    pub ipc_regions: [M::Region; NUM_IPC_REGIONS],
    pub mpu: M,
    pub app_ram_region: M::Region,
    pub app_flash_region: M::Region,
}

impl<M: mpu::MPU, const NUM_IPC_REGIONS: usize> Display
    for AppAccessibleMemory<M, NUM_IPC_REGIONS>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "\r\n MPU")?;
        write!(f, "{}", self.app_ram_region);
        write!(f, "{}", self.app_flash_region);
        for region in self.ipc_regions.iter() {
            write!(f, "{}", region);
        }
        write!(f, "\r\n")
    }
}

impl<M: mpu::MPU, const NUM_REGIONS: usize> AppAccessibleMemory<M, NUM_REGIONS> {
    pub fn mem_start(&self) -> Option<FluxPtrU8> {
        self.app_ram_region.accessible_start()
    }

    pub fn app_break(&self) -> Option<FluxPtrU8> {
        Some(
            self.mem_start()?
                .wrapping_add(self.app_ram_region.accessible_size()?),
        )
    }

    pub fn next_available_ipc_idx(&self) -> Option<usize> {
        for (i, region) in self.ipc_regions.iter().enumerate() {
            if !region.is_set() {
                return Some(i);
            }
        }
        None
    }

    pub fn new(mpu: M) -> Self {
        Self {
            ipc_regions: [<M as mpu::MPU>::Region::default(); NUM_REGIONS],
            app_ram_region: <M as mpu::MPU>::Region::default(),
            app_flash_region: <M as mpu::MPU>::Region::default(),
            mpu,
        }
    }

    pub fn reset(&mut self) {
        for b in self.ipc_regions.iter_mut() {
            *b = <M as mpu::MPU>::Region::default();
        }
        self.app_ram_region = <M as mpu::MPU>::Region::default();
        self.app_flash_region = <M as mpu::MPU>::Region::default();
    }

    pub fn remove_memory_region(&mut self, _region: <M as mpu::MPU>::Region) -> Result<(), ()> {
        todo!()
    }

    pub fn configure_mpu(&mut self) {
        // configure app regions
        self.mpu.configure_mpu_region(&self.app_flash_region);
        self.mpu.configure_mpu_region(&self.app_ram_region);
        // configure IPC regions
        for ipc_region in self.ipc_regions.iter() {
            self.mpu.configure_mpu_region(ipc_region);
        }
    }

    pub fn allocate_ipc_region(
        &mut self,
        unallocated_memory_start: FluxPtrU8Mut,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: RegionPermissions,
    ) -> Result<(), ()> {
        let region_idx = self.next_available_ipc_idx().ok_or(())?;
        let region = self
            .mpu
            .new_region(
                unallocated_memory_start,
                unallocated_memory_size,
                min_region_size,
                permissions,
            )
            .ok_or(())?;
        self.ipc_regions[region_idx] = region;
        Ok(())
    }

    fn add_flash_region(&mut self, flash_start: FluxPtrU8, flash_size: usize) -> Result<(), ()> {
        let region = self
            .mpu
            .new_region(
                flash_start,
                flash_size,
                flash_size,
                RegionPermissions::ReadExecuteOnly,
            )
            .ok_or(())?;

        self.app_flash_region = region;
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
        // TODO: There is a way better way to allocate this region
        // For example, we definitely don't need to cover the
        // entire process memory block
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
                RegionPermissions::ReadWriteOnly,
            )
            .ok_or(())?;
        let region_start = region.accessible_start().ok_or(())?;
        let app_break = region_start.as_usize() + region.accessible_size().ok_or(())?;

        let mut total_size = region.region_size().ok_or(())?;
        let kernel_break = region_start.as_usize() + total_size - initial_kernel_memory_size;
        if app_break > kernel_break {
            total_size *= 2;
            region = self
                .mpu
                .new_region(
                    unallocated_memory_start,
                    unallocated_memory_size,
                    total_size,
                    RegionPermissions::ReadWriteOnly,
                )
                .ok_or(())?;
        }
        self.app_ram_region = region;
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
    ) -> Result<(), AllocateAppMemoryError> {
        self.add_flash_region(flash_start, flash_size)
            .map_err(|_| AllocateAppMemoryError::FlashError)?;
        self.add_heap_region(
            unallocated_memory_start,
            unallocated_memory_size,
            min_memory_size,
            initial_app_memory_size,
            initial_kernel_memory_size,
        )
        .map_err(|_| AllocateAppMemoryError::HeapError)
    }

    pub fn update_app_memory(
        &mut self,
        app_memory_break: FluxPtrU8Mut,
        kernel_memory_break: FluxPtrU8Mut,
    ) -> Result<(), Error> {
        let current_region = self.app_ram_region;
        let memory_start = current_region
            .accessible_start()
            .ok_or(Error::KernelError)?;
        let total_size = current_region.region_size().ok_or(Error::KernelError)?;
        let memory_end = memory_start.as_usize() + total_size;
        if app_memory_break.as_usize() > kernel_memory_break.as_usize()
            || app_memory_break.as_usize() <= memory_start.as_usize()
            || app_memory_break.as_usize() > memory_end
        {
            return Err(Error::AddressOutOfBounds);
        }
        let new_region_size = app_memory_break.as_usize() - memory_start.as_usize();
        // TODO: Make sure that this preserves the region size we ask for
        let new_region = self
            .mpu
            .new_region(
                memory_start,
                total_size,
                new_region_size,
                RegionPermissions::ReadWriteOnly,
            )
            .ok_or(Error::OutOfMemory)?;
        let new_app_break = new_region
            .accessible_start()
            .ok_or(Error::KernelError)?
            .as_usize()
            + new_region.accessible_size().ok_or(Error::KernelError)?;
        if new_app_break > kernel_memory_break.as_usize() {
            return Err(Error::OutOfMemory);
        }
        self.app_ram_region = new_region;
        Ok(())
    }
}
