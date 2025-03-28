use super::mpu;
use kernel::platform::allocator::MPUVerified;

pub struct CortexRegion {
    accessible_start: FluxPtrU8,
    accessible_size: usize,
    region_start: FluxPtrU8,
    region_size: usize,
    subregions: Option<(usize, usize)>,
}

impl DescribeRegion for CortexRegion {
    fn accessible_start(&self) -> FluxPtrU8 {
        self.accessible_start
    }
    fn region_start(&self) -> FluxPtrU8 {
        self.region_start
    }
    fn accesible_size(&self) -> usize {
        self.accessible_size
    }
    fn region_size(&self) -> usize {
        self.region_size
    }
}

impl MPUVerified for mpu::MPU {
    type MpuConfig = mpu::CortexMConfig;

    fn enable_app_mpu(&mut self) {
        self.registers.ctrl.write(
            Control::ENABLE::SET() + Control::HFNMIENA::CLEAR() + Control::PRIVDEFENA::SET(),
        );
    }

    fn disable_app_mpu(&mut self) {
        self.registers.ctrl.write(Control::ENABLE::CLEAR());
    }

    fn number_total_regions(&self) -> usize {
        self.registers.mpu_type.read(Type::DREGION()) as usize
    }

    fn gimme_a_region(
        &self,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
    ) -> Option<CortexRegion> {
        let mut start = available_start.as_usize();
        let mut size = region_size;

        // Region start always has to align to minimum region size bytes
        if start % MIN_REGION_SIZE != 0 {
            start += MIN_REGION_SIZE - (start % MIN_REGION_SIZE);
        }

        // Regions must be at least minimum region size bytes
        if size < MIN_REGION_SIZE {
            size = MIN_REGION_SIZE;
        }

        // Physical MPU region (might be larger than logical region if some subregions are disabled)
        let mut region_start = start;
        let mut region_size = size;
        let mut subregions = None;
        // We can only create an MPU region if the size is a power of two and it divides
        // the start address. If this is not the case, the first thing we try to do to
        // cover the memory region is to use a larger MPU region and expose certain subregions.
        if size.count_ones() > 1 || start % size != 0 {
            // Which (power-of-two) subregion size would align with the start
            // address?
            //
            // We find this by taking smallest binary substring of the start
            // address with exactly one bit:
            //
            //      1 << (start.trailing_zeros())
            let subregion_size = {
                let tz = start.trailing_zeros();
                if tz < 32 {
                    // Find the largest power of two that divides `start`
                    // 1_usize << tz
                    power_of_two(tz)
                } else {
                    // This case means `start` is 0.

                    // VTOCK Bug?
                    // This is interesting. We are able to prove the case this way
                    // assert(size <= (u32::MAX / 2 + 1) as usize);
                    //
                    // but casting the usize to u32 does not work:
                    // assert(size as u32 <= u32::MAX / 2 + 1);
                    // if size as u32 > u32::MAX / 2 + 1 {
                    //     return None
                    // }
                    let mut ceil = math::closest_power_of_two_usize(size);
                    if ceil < 256 {
                        ceil = 256
                    }
                    ceil / 8
                }
            };

            // Once we have a subregion size, we get a region size by
            // multiplying it by the number of subregions per region.
            let underlying_region_size = subregion_size * 8;

            // Finally, we calculate the region base by finding the nearest
            // address below `start` that aligns with the region size.
            let underlying_region_start = start - (start % underlying_region_size);

            // If `size` doesn't align to the subregion size, extend it.
            if size % subregion_size != 0 {
                size += subregion_size - (size % subregion_size);
            }

            let end = start + size;
            let underlying_region_end = underlying_region_start + underlying_region_size;

            // To use subregions, the region must be at least 256 bytes. Also, we need
            // the amount of left over space in the region after `start` to be at least as
            // large as the memory region we want to cover.
            if subregion_size >= 32 && underlying_region_end >= end {
                // The index of the first subregion to activate is the number of
                // regions between `region_start` (MPU) and `start` (memory).
                let min_subregion = (start - underlying_region_start) / subregion_size;

                // The index of the last subregion to activate is the number of
                // regions that fit in `len`, plus the `min_subregion`, minus one
                // (because subregions are zero-indexed).
                let max_subregion = min_subregion + size / subregion_size - 1;

                region_start = underlying_region_start;
                region_size = underlying_region_size;
                subregions = Some((min_subregion, max_subregion));
            } else {
                // In this case, we can't use subregions to solve the alignment
                // problem. Instead, we round up `size` to a power of two and
                // shift `start` up in memory to make it align with `size`.

                // VTOCK Bug - this can overflow and there is no check like the one below
                if size > (u32::MAX / 2 + 1) as usize {
                    return None;
                }
                size = math::closest_power_of_two_usize(size);
                start += size - (start % size);

                region_start = start;
                region_size = size;
            }
        }

        // Check that our logical region fits in memory.
        if start + size > (available_start.as_usize()) + available_size {
            return None;
        }

        if region_size > u32::MAX as usize {
            return None;
        }

        Some(CortexRegion {
            accessible_start: start,
            accessible_size: size,
            region_start,
            region_size,
            subregions,
        })
    }

    fn configure_mpu(&mut self, config: &CortexMConfig) {
        // If the hardware is already configured for this app and the app's MPU
        // configuration has not changed, then skip the hardware update.
        // if !self.hardware_is_configured_for.contains(&config.id()) || config.is_dirty() {
        // Set MPU regions
        self.commit_region(config.get_region(0));
        self.commit_region(config.get_region(1));
        self.commit_region(config.get_region(2));
        self.commit_region(config.get_region(3));
        self.commit_region(config.get_region(4));
        self.commit_region(config.get_region(5));
        self.commit_region(config.get_region(6));
        self.commit_region(config.get_region(7));
        // for region in config.regions_iter() {
        //     self.commit_region(region);
        // }
        // self.hardware_is_configured_for.set(config.id());
        // config.set_dirty(false);
        // }
    }
}
