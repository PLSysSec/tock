// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Interface for configuring the Memory Protection Unit.

use core::fmt::{self, Display};
#[allow(clippy::wildcard_imports)]
use flux_support::*;

use crate::allocator::RegionPermissions;

/// Null type for the default type of the `MpuConfig` type in an implementation
/// of the `MPU` trait. This custom type allows us to implement `Display` with
/// an empty implementation to meet the constraint on `type MpuConfig`.
#[derive(Clone, Copy)]
pub struct MpuRegionDefault {
    start: Option<FluxPtrU8>,
    size: Option<usize>,
}

impl Display for MpuRegionDefault {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

impl Default for MpuRegionDefault {
    fn default() -> Self {
        Self {
            start: None,
            size: None,
        }
    }
}

pub trait RegionDescriptor {
    fn accessible_start(&self) -> Option<FluxPtrU8>;
    fn region_start(&self) -> Option<FluxPtrU8>;
    fn accessible_size(&self) -> Option<usize>;
    fn region_size(&self) -> Option<usize>;
    fn is_set(&self) -> bool;
}

impl RegionDescriptor for MpuRegionDefault {
    fn accessible_start(&self) -> Option<FluxPtrU8> {
        self.start
    }
    fn region_start(&self) -> Option<FluxPtrU8> {
        self.start
    }
    fn accessible_size(&self) -> Option<usize> {
        self.size
    }
    fn region_size(&self) -> Option<usize> {
        self.size
    }
    fn is_set(&self) -> bool {
        self.start.is_some()
    }
}

// #[flux_rs::assoc(fn enabled(self: Self) -> bool {false} )]
// #[flux_rs::assoc(fn configured_for(self: Self, config: Self::MpuConfig) -> bool)]
// #[flux_rs::assoc(fn config_can_access_flash(c: Self::MpuConfig, fstart: int, fend: int) -> bool)]
// #[flux_rs::assoc(fn config_can_access_heap(c: Self::MpuConfig, hstart: int, hend: int) -> bool)]
// #[flux_rs::assoc(fn config_cant_access_at_all(c: Self::MpuConfig, start: int, end: int) -> bool)]

/// The generic trait that particular memory protection unit implementations
/// need to implement.
///
/// This trait is implements generic MPU functionality that is common across different
/// MPU implementations.
pub trait MPU {
    /// MPU-specific state that defines a region for the MPU.
    /// That is, this should contain all of the required state such that the
    /// implementation can be passed an array of of this type and it should be
    /// able to correctly and entirely configure the MPU.
    ///
    /// This state will be held on a per-process basis as a way to cache all of
    /// the process settings. When the kernel switches to a new process it will
    /// use the `MpuConfig` for that process to quickly configure the MPU.
    ///
    /// It is `Default` so we can create empty state when the process is
    /// created, and `Display` so that the `panic!()` output can display the
    /// current state to help with debugging.
    type Region: RegionDescriptor + Default + Display + Copy;
    ///
    /// Defines the number of regions associated with the particular MPU.
    /// Note that this is architecture dependent.
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
    fn number_total_regions(&self) -> usize {
        Self::NUM_REGIONS
    }

    ///
    /// Deals with the alignment, size, and other constraints of the specific
    /// MPU to create a new region.
    ///
    /// Returns None if the MPU cannot allocate a region with the passed
    /// constraints
    fn new_region(
        &self,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: RegionPermissions,
    ) -> Option<Self::Region>;

    /// Configures the MPU with the provided region configuration.
    ///
    /// An implementation must ensure that all memory locations not covered by
    /// an allocated region are inaccessible in user mode and accessible in
    /// supervisor mode.
    ///
    /// # Arguments
    ///
    /// - `region`: MPU region to be configured
    fn configure_mpu_region(&mut self, region: &Self::Region);
}

// /// Implement default MPU trait for unit.
impl MPU for () {
    type Region = MpuRegionDefault;
    const NUM_REGIONS: usize = 0;

    fn enable_app_mpu(&mut self) {}

    fn disable_app_mpu(&mut self) {}

    fn number_total_regions(&self) -> usize {
        Self::NUM_REGIONS
    }

    fn configure_mpu_region(&mut self, _config: &Self::Region) {}

    fn new_region(
        &self,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        _permissions: RegionPermissions,
    ) -> Option<Self::Region> {
        if region_size <= available_size {
            Some(MpuRegionDefault {
                start: Some(available_start),
                size: Some(region_size),
            })
        } else {
            None
        }
    }
}
