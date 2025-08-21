// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Tock default Process implementation.
//!
//! `ProcessStandard` is an implementation for a userspace process running on
//! the Tock kernel.

use core::cell::Cell;
use core::cmp;
use core::fmt::Write;
use core::num::NonZeroU32;
use core::ptr::NonNull;
use core::{mem, str};
use flux_support::capability::*;
#[allow(clippy::wildcard_imports)]
use flux_support::*;

use crate::allocator::{self, AppMemoryAllocator};
use crate::collections::queue::Queue;
use crate::collections::ring_buffer::RingBuffer;
use crate::config;
use crate::debug;
use crate::errorcode::ErrorCode;
use crate::kernel::Kernel;
use crate::platform::chip::Chip;
use crate::platform::mpu;
use crate::process::BinaryVersion;
use crate::process::ProcessBinary;
use crate::process::{Error, FunctionCall, FunctionCallSource, Process, Task};
use crate::process::{FaultAction, ProcessCustomGrantIdentifier, ProcessId};
use crate::process::{ProcessAddresses, ProcessSizes, ShortId};
use crate::process::{State, StoppedState};
use crate::process_checker::AcceptedCredential;
use crate::process_loading::ProcessLoadError;
use crate::process_policies::ProcessFaultPolicy;
use crate::processbuffer::{ReadOnlyProcessBuffer, ReadWriteProcessBuffer};
use crate::storage_permissions;
use crate::syscall::{self, Syscall, SyscallReturn, UserspaceKernelBoundary};
use crate::upcall::UpcallId;
use crate::utilities::cells::{MapCell, NumericCellExt, OptionalCell};

use tock_tbf::types::CommandPermissions;

/// State for helping with debugging apps.
///
/// These pointers and counters are not strictly required for kernel operation,
/// but provide helpful information when an app crashes.
struct ProcessStandardDebug {
    /// If this process was compiled for fixed addresses, save the address
    /// it must be at in flash. This is useful for debugging and saves having
    /// to re-parse the entire TBF header.
    fixed_address_flash: Option<u32>,

    /// If this process was compiled for fixed addresses, save the address
    /// it must be at in RAM. This is useful for debugging and saves having
    /// to re-parse the entire TBF header.
    fixed_address_ram: Option<u32>,

    /// Where the process has started its heap in RAM.
    app_heap_start_pointer: Option<FluxPtrU8Mut>,

    /// Where the start of the stack is for the process. If the kernel does the
    /// PIC setup for this app then we know this, otherwise we need the app to
    /// tell us where it put its stack.
    app_stack_start_pointer: Option<FluxPtrU8Mut>,

    /// How low have we ever seen the stack pointer.
    app_stack_min_pointer: Option<FluxPtrU8Mut>,

    /// How many syscalls have occurred since the process started.
    syscall_count: usize,

    /// What was the most recent syscall.
    last_syscall: Option<Syscall>,

    /// How many upcalls were dropped because the queue was insufficiently
    /// long.
    dropped_upcall_count: usize,

    /// How many times this process has been paused because it exceeded its
    /// timeslice.
    timeslice_expiration_count: usize,
}

/// Entry that is stored in the grant pointer table at the top of process
/// memory.
///
/// One copy of this entry struct is stored per grant region defined in the
/// kernel. This type allows the core kernel to lookup a grant based on the
/// driver_num associated with the grant, and also holds the pointer to the
/// memory allocated for the particular grant.
#[repr(C)]
struct GrantPointerEntry {
    /// The syscall driver number associated with the allocated grant.
    ///
    /// This defaults to 0 if the grant has not been allocated. Note, however,
    /// that 0 is a valid driver_num, and therefore cannot be used to check if a
    /// grant is allocated or not.
    driver_num: usize,

    /// The start of the memory location where the grant has been allocated, or
    /// null if the grant has not been allocated.
    grant_ptr: FluxPtrU8Mut,
}
/// A type for userspace processes in Tock.
pub struct ProcessStandard<'a, C: 'static + Chip> {
    /// Identifier of this process and the index of the process in the process
    /// table.
    process_id: Cell<ProcessId>,

    /// An application ShortId, generated from process loading and
    /// checking, which denotes the security identity of this process.
    app_id: ShortId,

    /// Pointer to the main Kernel struct.
    kernel: &'static Kernel,

    /// Pointer to the struct that defines the actual chip the kernel is running
    /// on. This is used because processes have subtle hardware-based
    /// differences. Specifically, the actual syscall interface and how
    /// processes are switched to is architecture-specific, and how memory must
    /// be allocated for memory protection units is also hardware-specific.
    chip: &'static C,

    /// Application memory layout:
    ///
    /// ```text
    ///     ╒════════ ← memory_start + memory_len
    ///  ╔═ │ Grant Pointers
    ///  ║  │ ──────
    ///     │ Process Control Block
    ///  D  │ ──────
    ///  Y  │ Grant Regions
    ///  N  │
    ///  A  │   ↓
    ///  M  │ ──────  ← kernel_memory_break
    ///  I  │
    ///  C  │ ──────  ← app_break               ═╗
    ///     │                                    ║
    ///  ║  │   ↑                                  A
    ///  ║  │  Heap                              P C
    ///  ╠═ │ ──────  ← app_heap_start           R C
    ///     │  Data                              O E
    ///  F  │ ──────  ← data_start_pointer       C S
    ///  I  │ Stack                              E S
    ///  X  │   ↓                                S I
    ///  E  │                                    S B
    ///  D  │ ──────  ← current_stack_pointer      L
    ///     │                                    ║ E
    ///  ╚═ ╘════════ ← memory_start            ═╝
    /// ```
    ///
    /// The start of process memory. We store this as a pointer and length and
    /// not a slice due to Rust aliasing rules. If we were to store a slice,
    /// then any time another slice to the same memory or an ProcessBuffer is
    /// used in the kernel would be undefined behavior.
    // breaks and corresponding configuration
    // refinement says that these are the same
    // breaks_and_config: MapCell<BreaksAndMPUConfig<C>>,
    app_memory_allocator: MapCell<AppMemoryAllocator<<<C as Chip>::MPU as mpu::MPU>::Region>>,

    /// Reference to the slice of `GrantPointerEntry`s stored in the process's
    /// memory reserved for the kernel. These driver numbers are zero and
    /// pointers are null if the grant region has not been allocated. When the
    /// grant region is allocated these pointers are updated to point to the
    /// allocated memory and the driver number is set to match the driver that
    /// owns the grant. No other reference to these pointers exists in the Tock
    /// kernel.
    grant_pointers: MapCell<&'static mut [GrantPointerEntry]>,

    /// The footers of the process binary (may be zero-sized), which are metadata
    /// about the process not covered by integrity. Used, among other things, to
    /// store signatures.
    footers: &'static [u8],

    /// Collection of pointers to the TBF header in flash.
    header: tock_tbf::types::TbfHeader,

    /// Credential that was approved for this process, or `None` if the
    /// credential was permitted to run without an accepted credential.
    credential: Option<AcceptedCredential>,

    /// State saved on behalf of the process each time the app switches to the
    /// kernel.
    stored_state:
        MapCell<<<C as Chip>::UserspaceKernelBoundary as UserspaceKernelBoundary>::StoredState>,

    /// The current state of the app. The scheduler uses this to determine
    /// whether it can schedule this app to execute.
    ///
    /// The `state` is used both for bookkeeping for the scheduler as well as
    /// for enabling control by other parts of the system. The scheduler keeps
    /// track of if a process is ready to run or not by switching between the
    /// `Running` and `Yielded` states. The system can control the process by
    /// switching it to a "stopped" state to prevent the scheduler from
    /// scheduling it.
    state: Cell<State>,

    /// How to respond if this process faults.
    fault_policy: &'a dyn ProcessFaultPolicy,

    /// Essentially a list of upcalls that want to call functions in the
    /// process.
    tasks: MapCell<RingBuffer<'a, Task>>,

    /// Count of how many times this process has entered the fault condition and
    /// been restarted. This is used by some `ProcessRestartPolicy`s to
    /// determine if the process should be restarted or not.
    restart_count: Cell<usize>,

    /// The completion code set by the process when it last exited, restarted,
    /// or was terminated. If the process is has never terminated, then the
    /// `OptionalCell` will be empty (i.e. `None`). If the process has exited,
    /// restarted, or terminated, the `OptionalCell` will contain an optional 32
    /// bit value. The option will be `None` if the process crashed or was
    /// stopped by the kernel and there is no provided completion code. If the
    /// process called the exit syscall then the provided completion code will
    /// be stored as `Some(completion code)`.
    completion_code: OptionalCell<Option<u32>>,

    /// Values kept so that we can print useful debug messages when apps fault.
    debug: MapCell<ProcessStandardDebug>,
}

impl<C: Chip> Process for ProcessStandard<'_, C> {
    fn processid(&self) -> ProcessId {
        self.process_id.get()
    }

    fn short_app_id(&self) -> ShortId {
        self.app_id
    }

    fn binary_version(&self) -> Option<BinaryVersion> {
        let version = self.header.get_binary_version();
        match NonZeroU32::new(version) {
            Some(version_nonzero) => Some(BinaryVersion::new(version_nonzero)),
            None => None,
        }
    }

    fn get_credential(&self) -> Option<AcceptedCredential> {
        self.credential
    }

    fn enqueue_task(&self, task: Task) -> Result<(), ErrorCode> {
        // If this app is in a `Fault` state then we shouldn't schedule
        // any work for it.
        if !self.is_running() {
            return Err(ErrorCode::NODEVICE);
        }

        let ret = self.tasks.map_or(Err(ErrorCode::FAIL), |tasks| {
            match tasks.enqueue(task) {
                true => {
                    // The task has been successfully enqueued.
                    Ok(())
                }
                false => {
                    // The task could not be enqueued as there is
                    // insufficient space in the ring buffer.
                    Err(ErrorCode::NOMEM)
                }
            }
        });

        if ret.is_err() {
            // On any error we were unable to enqueue the task. Record the
            // error, but importantly do _not_ increment kernel work.
            self.debug.map(|debug| {
                debug.dropped_upcall_count += 1;
            });
        }

        ret
    }

    fn ready(&self) -> bool {
        self.tasks.map_or(false, |ring_buf| ring_buf.has_elements())
            || self.state.get() == State::Running
    }

    fn remove_pending_upcalls(&self, upcall_id: UpcallId) {
        self.tasks.map(|tasks| {
            let count_before = tasks.len();
            // VTOCK-TODO: prove tasks.retain() reduces number of tasks
            tasks.retain(|task| match task {
                // Remove only tasks that are function calls with an id equal
                // to `upcall_id`.
                Task::FunctionCall(function_call) => match function_call.source {
                    FunctionCallSource::Kernel => true,
                    FunctionCallSource::Driver(id) => id != upcall_id,
                },
                _ => true,
            });
            if config::CONFIG.trace_syscalls {
                let count_after = tasks.len();
                // assume(count_before >= count_after); // requires refined ringbuffer
                debug!(
                    "[{:?}] remove_pending_upcalls[{:#x}:{}] = {} upcall(s) removed",
                    self.processid(),
                    upcall_id.driver_num,
                    upcall_id.subscribe_num,
                    count_before - count_after,
                );
            }
        });
    }

    fn is_running(&self) -> bool {
        match self.state.get() {
            State::Running | State::Yielded | State::YieldedFor(_) | State::Stopped(_) => true,
            _ => false,
        }
    }

    fn get_state(&self) -> State {
        self.state.get()
    }

    fn set_yielded_state(&self) {
        if self.state.get() == State::Running {
            self.state.set(State::Yielded);
        }
    }

    fn set_yielded_for_state(&self, upcall_id: UpcallId) {
        if self.state.get() == State::Running {
            self.state.set(State::YieldedFor(upcall_id));
        }
    }

    fn stop(&self) {
        match self.state.get() {
            State::Running => self.state.set(State::Stopped(StoppedState::Running)),
            State::Yielded => self.state.set(State::Stopped(StoppedState::Yielded)),
            State::YieldedFor(upcall_id) => self
                .state
                .set(State::Stopped(StoppedState::YieldedFor(upcall_id))),
            State::Stopped(_stopped_state) => {
                // Already stopped, nothing to do.
            }
            State::Faulted | State::Terminated => {
                // Stop has no meaning on a inactive process.
            }
        }
    }

    fn resume(&self) {
        match self.state.get() {
            State::Stopped(stopped_state) => match stopped_state {
                StoppedState::Running => self.state.set(State::Running),
                StoppedState::Yielded => self.state.set(State::Yielded),
                StoppedState::YieldedFor(upcall_id) => self.state.set(State::YieldedFor(upcall_id)),
            },
            _ => {} // Do nothing
        }
    }

    fn set_fault_state(&self) {
        // Use the per-process fault policy to determine what action the kernel
        // should take since the process faulted.
        let action = self.fault_policy.action(self);
        match action {
            FaultAction::Panic => {
                // process faulted. Panic and print status
                self.state.set(State::Faulted);
                panic!("Process {} had a fault", self.get_process_name());
            }
            FaultAction::Restart => {
                self.try_restart(None);
            }
            FaultAction::Stop => {
                // This looks a lot like restart, except we just leave the app
                // how it faulted and mark it as `Faulted`. By clearing
                // all of the app's todo work it will not be scheduled, and
                // clearing all of the grant regions will cause capsules to drop
                // this app as well.
                self.terminate(None);
                self.state.set(State::Faulted);
            }
        }
    }

    fn start(&self, _cap: &dyn crate::capabilities::ProcessStartCapability) {
        // `start()` can only be called on a terminated process.
        if self.get_state() != State::Terminated {
            return;
        }

        // Reset to start the process.
        if let Ok(()) = self.reset() {
            self.state.set(State::Yielded);
        }
    }

    fn try_restart(&self, completion_code: Option<u32>) {
        // `try_restart()` cannot be called if the process is terminated. Only
        // `start()` can start a terminated process.
        if self.get_state() == State::Terminated {
            return;
        }

        // Terminate the process, freeing its state and removing any
        // pending tasks from the scheduler's queue.
        self.terminate(completion_code);

        // If there is a kernel policy that controls restarts, it should be
        // implemented here. For now, always restart.
        if let Ok(()) = self.reset() {
            self.state.set(State::Yielded);
        }

        // Decide what to do with res later. E.g., if we can't restart
        // want to reclaim the process resources.
    }

    fn terminate(&self, completion_code: Option<u32>) {
        // A process can be terminated if it is running or in the `Faulted`
        // state. Otherwise, you cannot terminate it and this method return
        // early.
        //
        // The kernel can terminate in the `Faulted` state to return the process
        // to a state in which it can run again (e.g., reset it).
        if !self.is_running() && self.get_state() != State::Faulted {
            return;
        }

        // And remove those tasks
        self.tasks.map(|tasks| {
            tasks.empty();
        });

        // Clear any grant regions this app has setup with any capsules.
        unsafe {
            self.grant_ptrs_reset();
        }

        // Save the completion code.
        self.completion_code.set(completion_code);

        // Mark the app as stopped so the scheduler won't try to run it.
        self.state.set(State::Terminated);
    }

    fn get_restart_count(&self) -> usize {
        self.restart_count.get()
    }

    fn has_tasks(&self) -> bool {
        self.tasks.map_or(false, |tasks| tasks.has_elements())
    }

    fn dequeue_task(&self) -> Option<Task> {
        self.tasks.map_or(None, |tasks| tasks.dequeue())
    }

    fn remove_upcall(&self, upcall_id: UpcallId) -> Option<Task> {
        self.tasks.map_or(None, |tasks| {
            tasks.remove_first_matching(|task| match task {
                Task::FunctionCall(fc) => match fc.source {
                    FunctionCallSource::Driver(upid) => upid == upcall_id,
                    _ => false,
                },
                Task::ReturnValue(rv) => rv.upcall_id == upcall_id,
                Task::IPC(_) => false,
            })
        })
    }

    fn pending_tasks(&self) -> usize {
        self.tasks.map_or(0, |tasks| tasks.len())
    }

    fn get_command_permissions(&self, driver_num: usize, offset: usize) -> CommandPermissions {
        self.header.get_command_permissions(driver_num, offset)
    }

    fn get_storage_permissions(&self) -> Option<storage_permissions::StoragePermissions> {
        let (read_count, read_ids) = self.header.get_storage_read_ids().unwrap_or((0, [0; 8]));

        let (modify_count, modify_ids) =
            self.header.get_storage_modify_ids().unwrap_or((0, [0; 8]));

        let write_id = self.header.get_storage_write_id();

        Some(storage_permissions::StoragePermissions::new(
            read_count,
            read_ids,
            modify_count,
            modify_ids,
            write_id,
        ))
    }

    fn number_writeable_flash_regions(&self) -> usize {
        self.header.number_writeable_flash_regions()
    }

    fn get_writeable_flash_region(&self, region_index: usize) -> (u32, u32) {
        self.header.get_writeable_flash_region(region_index)
    }

    fn update_stack_start_pointer(&self, stack_pointer: FluxPtrU8Mut) {
        self.app_memory_allocator.map(|am| {
            if stack_pointer >= am.memory_start() && stack_pointer < am.memory_end() {
                self.debug.map(|debug| {
                    debug.app_stack_start_pointer = Some(stack_pointer);

                    // We also reset the minimum stack pointer because whatever
                    // value we had could be entirely wrong by now.
                    debug.app_stack_min_pointer = Some(stack_pointer);
                });
            }
        });
    }

    fn update_heap_start_pointer(&self, heap_pointer: FluxPtrU8Mut) {
        self.app_memory_allocator.map(|am| {
            if heap_pointer >= am.memory_start() && heap_pointer < am.memory_end() {
                self.debug.map(|debug| {
                    debug.app_heap_start_pointer = Some(heap_pointer);
                });
            }
        });
    }

    fn setup_mpu(&self) -> MpuConfiguredCapability {
        let dwt = self.chip.dwt();
        dwt.reset();
        dwt.start();
        self.app_memory_allocator
            .map_or(Err(()), |am| Ok(am.configure_mpu(self.chip.mpu())))
            .expect("Fatal kernel bug in setting up MPU - cannot branch to process as it would be unsafe")
        dwt.stop();
        let count = dwt.count();
        crate::debug!("[EVAL] setup_mpu {}", count);
    }

    #[flux_rs::sig(fn (_, start: FluxPtrU8, size: usize{valid_size(start+size)}) -> _)]
    fn add_mpu_region(&self, start: FluxPtrU8, size: usize) -> Option<mpu::Region> {
        self.app_memory_allocator.and_then(|am| {
            am.allocate_ipc_region(start, size, mpu::Permissions::ReadWriteOnly)
                .ok()
        })
    }

    fn sbrk(&self, increment: isize) -> Result<FluxPtrU8Mut, Error> {
        // Do not modify an inactive process.
        if !self.is_running() {
            return Err(Error::InactiveApp);
        }
        let app_break = self.app_memory_break().map_err(|_| Error::KernelError)?;
        let new_break = app_break.wrapping_offset(increment);
        self.brk(new_break)
    }

    fn brk(&self, new_break: FluxPtrU8Mut) -> Result<FluxPtrU8Mut, Error> {
        let dwt = self.chip.dwt();
        dwt.reset();
        dwt.start();
        // Do not modify an inactive process.
        if !self.is_running() {
            return Err(Error::InactiveApp);
        }

        let res = self.app_memory_allocator
            .map_or(Err(Error::KernelError), |am| {
                am.update_app_memory(new_break)?;
                // VTOCK Note:
                // The natural thing here seems to be to expose the actual
                // end of the heap to the process. However, doing this crashes
                // apps as they seem to use the value returned here to immediately
                // read/write to memory.
                Ok(new_break)
            });
        dwt.stop();
        let count = dwt.count();
        crate::debug!("[EVAL] brk {:?}", count);
        res
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    fn build_readwrite_process_buffer(
        &self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<ReadWriteProcessBuffer, ErrorCode> {
        let dwt = self.chip.dwt();
        dwt.reset();
        dwt.start();
        if !self.is_running() {
            // Do not operate on an inactive process
            return Err(ErrorCode::FAIL);
        }

        // A process is allowed to pass any pointer if the buffer length is 0,
        // as to revoke kernel access to a memory region without granting access
        // to another one
        if size == 0 {
            // Clippy complains that we're dereferencing a pointer in a public
            // and safe function here. While we are not dereferencing the
            // pointer here, we pass it along to an unsafe function, which is as
            // dangerous (as it is likely to be dereferenced down the line).
            //
            // Relevant discussion:
            // https://github.com/rust-lang/rust-clippy/issues/3045
            //
            // It should be fine to ignore the lint here, as a buffer of length
            // 0 will never allow dereferencing any memory in a safe manner.
            //
            // ### Safety
            //
            // We specify a zero-length buffer, so the implementation of
            // `ReadWriteProcessBuffer` will handle any safety issues.
            // Therefore, we can encapsulate the unsafe.
            Ok(unsafe { ReadWriteProcessBuffer::new(buf_start_addr, 0, self.processid()) })
        } else {
            let process_buffer = self.app_memory_allocator.map(|app_mem| {
                if let Ok(_) = app_mem.add_shared_readwrite_buffer(buf_start_addr, size) {
                    Ok(unsafe {
                        ReadWriteProcessBuffer::new(buf_start_addr, size, self.processid())
                    })
                } else {
                    Err(ErrorCode::INVAL)
                }
            });

            // Clippy complains that we're dereferencing a pointer in a public
            // and safe function here. While we are not dereferencing the
            // pointer here, we pass it along to an unsafe function, which is as
            // dangerous (as it is likely to be dereferenced down the line).
            //
            // Relevant discussion:
            // https://github.com/rust-lang/rust-clippy/issues/3045
            //
            // It should be fine to ignore the lint here, as long as we make
            // sure that we're pointing towards userspace memory (verified using
            // `in_app_owned_memory`) and respect alignment and other
            // constraints of the Rust references created by
            // `ReadWriteProcessBuffer`.
            //
            // ### Safety
            //
            // We encapsulate the unsafe here on the condition in the TODO
            // above, as we must ensure that this `ReadWriteProcessBuffer` will
            // be the only reference to this memory.
            let res = match process_buffer {
                Some(Ok(process_buffer)) => return Ok(process_buffer),
                _ => return Err(ErrorCode::INVAL),
            };
            dwt.stop();
            let count = dwt.count();
            crate::debug!("[EVAL] build_readwrite_process_buffer {:?}", count);
            res
        }
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    fn build_readonly_process_buffer(
        &self,
        buf_start_addr: FluxPtrU8Mut,
        size: usize,
    ) -> Result<ReadOnlyProcessBuffer, ErrorCode> {
        let dwt = self.chip.dwt();
        dwt.reset();
        dwt.start();
        if !self.is_running() {
            // Do not operate on an inactive process
            return Err(ErrorCode::FAIL);
        }

        // A process is allowed to pass any pointer if the buffer length is 0,
        // as to revoke kernel access to a memory region without granting access
        // to another one
        let res = if size == 0 {
            // Clippy complains that we're dereferencing a pointer in a public
            // and safe function here. While we are not dereferencing the
            // pointer here, we pass it along to an unsafe function, which is as
            // dangerous (as it is likely to be dereferenced down the line).
            //
            // Relevant discussion:
            // https://github.com/rust-lang/rust-clippy/issues/3045
            //
            // It should be fine to ignore the lint here, as a buffer of length
            // 0 will never allow dereferencing any memory in a safe manner.
            //
            // ### Safety
            //
            // We specify a zero-length buffer, so the implementation of
            // `ReadOnlyProcessBuffer` will handle any safety issues. Therefore,
            // we can encapsulate the unsafe.
            Ok(unsafe { ReadOnlyProcessBuffer::new(buf_start_addr, 0, self.processid()) })
        } else {
            let _ = self
                .app_memory_allocator
                .map_or(Err(ErrorCode::FAIL), |app_mem| {
                    Ok(app_mem.add_shared_readonly_buffer(buf_start_addr, size))
                })
                .map_err(|_| ErrorCode::INVAL)?;
            //     if self
            //     .in_app_owned_memory(buf_start_addr, size)
            //     .map_err(|_| ErrorCode::FAIL)?
            //     || self.in_app_flash_memory(buf_start_addr, size)
            // {
            //     // TODO: Check for buffer aliasing here

            //     if self
            //         .in_app_owned_memory(buf_start_addr, size)
            //         .map_err(|_| ErrorCode::FAIL)?
            //     {
            //         // Valid buffer, and since this is in read-write memory (i.e.
            //         // not flash), we need to adjust the process's watermark. Note:
            //         // `in_app_owned_memory()` ensures this offset does not wrap.

            //         self.breaks_and_config
            //             .map_or(Err(ErrorCode::FAIL), |breaks_and_config| {
            //                 Ok(breaks_and_config.set_high_water_mark_to_buf_end(buf_end_addr))
            //             })?;
            //     }

            // Clippy complains that we're dereferencing a pointer in a public
            // and safe function here. While we are not dereferencing the
            // pointer here, we pass it along to an unsafe function, which is as
            // dangerous (as it is likely to be dereferenced down the line).
            //
            // Relevant discussion:
            // https://github.com/rust-lang/rust-clippy/issues/3045
            //
            // It should be fine to ignore the lint here, as long as we make
            // sure that we're pointing towards userspace memory (verified using
            // `in_app_owned_memory` or `in_app_flash_memory`) and respect
            // alignment and other constraints of the Rust references created by
            // `ReadWriteProcessBuffer`.
            //
            // ### Safety
            //
            // We encapsulate the unsafe here on the condition in the TODO
            // above, as we must ensure that this `ReadOnlyProcessBuffer` will
            // be the only reference to this memory.
            Ok(unsafe { ReadOnlyProcessBuffer::new(buf_start_addr, size, self.processid()) })
        };
        dwt.stop();
        let count = dwt.count();
        crate::debug!("[EVAL] build_readonly_process_buffer {:?}", count);
        res
    }

    fn set_byte(&self, addr: FluxPtrU8Mut, value: u8) -> Result<bool, ()> {
        self.app_memory_allocator
            .map_or(Err(()), |am| unsafe { Ok(am.set_byte(addr, value)) })
    }

    fn grant_is_allocated(&self, grant_num: usize) -> Option<bool> {
        // Do not modify an inactive process.
        if !self.is_running() {
            return None;
        }

        // Update the grant pointer to the address of the new allocation.
        self.grant_pointers.map_or(None, |grant_pointers| {
            // Implement `grant_pointers[grant_num]` without a chance of a
            // panic.
            grant_pointers
                .get(grant_num)
                .map(|grant_entry| !grant_entry.grant_ptr.is_null())
        })
    }

    fn allocate_grant(
        &self,
        grant_num: usize,
        driver_num: usize,
        size: usize,
        align: usize,
    ) -> Result<(), ()> {
        let dwt = self.chip.dwt();
        dwt.reset();
        dwt.start();

        // Do not modify an inactive process.
        if !self.is_running() {
            return Err(());
        }

        // Verify the grant_num is valid.
        if grant_num >= self.kernel.get_grant_count_and_finalize() {
            return Err(());
        }

        // Verify that the grant is not already allocated. If the pointer is not
        // null then the grant is already allocated.
        if let Some(is_allocated) = self.grant_is_allocated(grant_num) {
            if is_allocated {
                return Err(());
            }
        }

        // Verify that there is not already a grant allocated with the same
        // `driver_num`.
        let exists = self.grant_pointers.map_or(false, |grant_pointers| {
            // Check our list of grant pointers if the driver number is used.
            grant_pointers.iter().any(|grant_entry| {
                // Check if the grant is both allocated (its grant pointer is
                // non null) and the driver number matches.
                (!grant_entry.grant_ptr.is_null()) && grant_entry.driver_num == driver_num
            })
        });
        // If we find a match, then the `driver_num` must already be used and
        // the grant allocation fails.
        if exists {
            return Err(());
        }

        if align == 0 {
            return Err(());
        }

        // Use the shared grant allocator function to actually allocate memory.
        // Returns `None` if the allocation cannot be created.
        let res = if let Some(grant_ptr) = self.allocate_in_grant_region_internal(size, align) {
            // Update the grant pointer to the address of the new allocation.
            self.grant_pointers.map_or(Err(()), |grant_pointers| {
                // Implement `grant_pointers[grant_num] = grant_ptr` without a
                // chance of a panic.
                grant_pointers
                    .get_mut(grant_num)
                    .map_or(Err(()), |grant_entry| {
                        // Actually set the driver num and grant pointer.
                        grant_entry.driver_num = driver_num;
                        grant_entry.grant_ptr = grant_ptr;

                        // If all of this worked, return true.
                        Ok(())
                    })
            })
        } else {
            // Could not allocate the memory for the grant region.
            Err(())
        };
        dwt.stop();
        let count = dwt.count();
        crate::debug!("[EVAL] allocate_grant {:?}", count);
        res
    }

    fn allocate_custom_grant(
        &self,
        size: usize,
        align: usize,
    ) -> Result<(ProcessCustomGrantIdentifier, NonNull<u8>), ()> {
        let dwt = self.chip.dwt();
        dwt.reset();
        dwt.start();
        // Do not modify an inactive process.
        if !self.is_running() {
            return Err(());
        }

        if align == 0 {
            return Err(());
        }

        // Use the shared grant allocator function to actually allocate memory.
        // Returns `None` if the allocation cannot be created.
        let res = self.app_memory_allocator
            .map_or(Err(()), |am| am.allocate_custom_grant(size, align));
        dwt.stop();
        let count = dwt.count();
        crate::debug!("[EVAL] allocate_custom_grant {:?}", count);
        res
    }

    fn enter_grant(&self, grant_num: usize) -> Result<NonNull<u8>, Error> {
        // Do not try to access the grant region of an inactive process.
        if !self.is_running() {
            return Err(Error::InactiveApp);
        }

        // Retrieve the grant pointer from the `grant_pointers` slice. We use
        // `[slice].get()` so that if the grant number is invalid this will
        // return `Err` and not panic.
        self.grant_pointers
            .map_or(Err(Error::KernelError), |grant_pointers| {
                // Implement `grant_pointers[grant_num]` without a chance of a
                // panic.
                match grant_pointers.get_mut(grant_num) {
                    Some(grant_entry) => {
                        // Get a copy of the actual grant pointer.
                        let grant_ptr = grant_entry.grant_ptr;

                        // Check if the grant pointer is marked that the grant
                        // has already been entered. If so, return an error.
                        if (grant_ptr.as_usize()) & 0x1 == 0x1 {
                            // Lowest bit is one, meaning this grant has been
                            // entered.
                            Err(Error::AlreadyInUse)
                        } else {
                            // Now, to mark that the grant has been entered, we
                            // set the lowest bit to one and save this as the
                            // grant pointer.
                            grant_entry.grant_ptr = (grant_ptr.as_usize() | 0x1).as_fluxptr();

                            // And we return the grant pointer to the entered
                            // grant.
                            Ok(unsafe { NonNull::new_unchecked(grant_ptr.unsafe_as_ptr()) })
                        }
                    }
                    None => Err(Error::AddressOutOfBounds),
                }
            })
    }

    fn enter_custom_grant(
        &self,
        identifier: ProcessCustomGrantIdentifier,
    ) -> Result<FluxPtrU8Mut, Error> {
        // Do not try to access the grant region of an inactive process.
        if !self.is_running() {
            return Err(Error::InactiveApp);
        }

        // Get the address of the custom grant based on the identifier.
        let custom_grant_address = self
            .get_custom_grant_address(identifier)
            .ok_or(Error::KernelError)?;

        // We never deallocate custom grants and only we can change the
        // `identifier` so we know this is a valid address for the custom grant.
        Ok(custom_grant_address.as_fluxptr())
    }

    unsafe fn leave_grant(&self, grant_num: usize) {
        // Do not modify an inactive process.
        if !self.is_running() {
            return;
        }

        self.grant_pointers.map(|grant_pointers| {
            // Implement `grant_pointers[grant_num]` without a chance of a
            // panic.
            if let Some(grant_entry) = grant_pointers.get_mut(grant_num) {
                // Get a copy of the actual grant pointer.
                let grant_ptr = grant_entry.grant_ptr;

                // Now, to mark that the grant has been released, we set the
                // lowest bit back to zero and save this as the grant
                // pointer.
                grant_entry.grant_ptr = (grant_ptr.as_usize() & !0x1).as_fluxptr();
            }
        });
    }

    fn grant_allocated_count(&self) -> Option<usize> {
        // Do not modify an inactive process.
        if !self.is_running() {
            return None;
        }

        self.grant_pointers.map(|grant_pointers| {
            // Filter our list of grant pointers into just the non-null ones,
            // and count those. A grant is allocated if its grant pointer is
            // non-null.
            grant_pointers
                .iter()
                .filter(|grant_entry| !grant_entry.grant_ptr.is_null())
                .count()
        })
    }

    fn lookup_grant_from_driver_num(&self, driver_num: usize) -> Result<usize, Error> {
        self.grant_pointers
            .map_or(Err(Error::KernelError), |grant_pointers| {
                // Filter our list of grant pointers into just the non null
                // ones, and count those. A grant is allocated if its grant
                // pointer is non-null.
                match grant_pointers.iter().position(|grant_entry| {
                    // Only consider allocated grants.
                    (!grant_entry.grant_ptr.is_null()) && grant_entry.driver_num == driver_num
                }) {
                    Some(idx) => Ok(idx),
                    None => Err(Error::OutOfMemory),
                }
            })
    }

    fn is_valid_upcall_function_pointer(&self, upcall_fn: NonNull<()>) -> Result<bool, ()> {
        let ptr = upcall_fn.as_fluxptr();
        let size = mem::size_of::<FluxPtrU8Mut>();

        // It is okay if this function is in memory or flash.
        Ok(
            self.in_app_flash_memory(ptr, size).ok_or(())?
                || self.in_app_owned_memory(ptr, size)?,
        )
    }

    fn get_process_name(&self) -> &'static str {
        self.header.get_package_name().unwrap_or("")
    }

    fn get_completion_code(&self) -> Option<Option<u32>> {
        self.completion_code.get()
    }

    fn set_syscall_return_value(&self, return_value: SyscallReturn) {
        match self.stored_state.map(|stored_state| unsafe {
            // Actually set the return value for a particular process.
            //
            // The UKB implementation uses the bounds of process-accessible
            // memory to verify that any memory changes are valid. Here, the
            // unsafe promise we are making is that the bounds passed to the UKB
            // are correct.
            let app_break = self.app_memory_break()?;
            self.chip
                .userspace_kernel_boundary()
                .set_syscall_return_value(
                    self.mem_start().ok_or(())?,
                    app_break,
                    stored_state,
                    return_value,
                )
        }) {
            Some(Ok(())) => {
                // If we get an `Ok` we are all set.

                // The process is either already in the running state (having
                // just called a nonblocking syscall like command) or needs to
                // be moved to the running state having called Yield-WaitFor and
                // now needing to be resumed. Either way we can set the state to
                // running.
                self.state.set(State::Running);
            }

            Some(Err(())) => {
                // If we get an `Err`, then the UKB implementation could not set
                // the return value, likely because the process's stack is no
                // longer accessible to it. All we can do is fault.
                self.set_fault_state();
            }

            None => {
                // We should never be here since `stored_state` should always be
                // occupied.
                self.set_fault_state();
            }
        }
    }

    fn set_process_function(&self, callback: FunctionCall) {
        // See if we can actually enqueue this function for this process.
        // Architecture-specific code handles actually doing this since the
        // exact method is both architecture- and implementation-specific.
        //
        // This can fail, for example if the process does not have enough memory
        // remaining.

        match self.stored_state.map(|stored_state| {
            // Let the UKB implementation handle setting the process's PC so
            // that the process executes the upcall function. We encapsulate
            // unsafe here because we are guaranteeing that the memory bounds
            // passed to `set_process_function` are correct.
            let app_break = self.app_memory_break()?;
            unsafe {
                self.chip.userspace_kernel_boundary().set_process_function(
                    self.mem_start().ok_or(())?,
                    app_break,
                    stored_state,
                    callback,
                )
            }
        }) {
            Some(Ok(())) => {
                // If we got an `Ok` we are all set and should mark that this
                // process is ready to be scheduled.

                // Move this process to the "running" state so the scheduler
                // will schedule it.
                self.state.set(State::Running);
            }

            Some(Err(())) => {
                // If we got an Error, then there was likely not enough room on
                // the stack to allow the process to execute this function given
                // the details of the particular architecture this is running
                // on. This process has essentially faulted, so we mark it as
                // such.
                self.set_fault_state();
            }

            None => {
                // We should never be here since `stored_state` should always be
                // occupied.
                self.set_fault_state();
            }
        }
    }

    fn switch_to(
        &self,
        mpu_configured: MpuConfiguredCapability,
        mpu_enabled: MpuEnabledCapability,
    ) -> Option<syscall::ContextSwitchReason> {
        // Cannot switch to an invalid process
        if !self.is_running() {
            return None;
        }

        let (switch_reason, stack_pointer) =
            self.stored_state.map_or((None, None), |stored_state| {
                // Switch to the process. We guarantee that the memory pointers
                // we pass are valid, ensuring this context switch is safe.
                // Therefore we encapsulate the `unsafe`.
                unsafe {
                    let (switch_reason, optional_stack_pointer) = self
                        .chip
                        .userspace_kernel_boundary()
                        .switch_to_process(mpu_configured, mpu_enabled, stored_state);
                    (Some(switch_reason), optional_stack_pointer)
                }
            });

        // If the UKB implementation passed us a stack pointer, update our
        // debugging state. This is completely optional.
        self.update_debug_sp(stack_pointer);

        switch_reason
    }

    fn debug_syscall_count(&self) -> usize {
        self.debug.map_or(0, |debug| debug.syscall_count)
    }

    fn debug_dropped_upcall_count(&self) -> usize {
        self.debug.map_or(0, |debug| debug.dropped_upcall_count)
    }

    fn debug_timeslice_expiration_count(&self) -> usize {
        self.debug
            .map_or(0, |debug| debug.timeslice_expiration_count)
    }

    fn debug_timeslice_expired(&self) {
        self.debug
            .map(|debug| debug.timeslice_expiration_count += 1);
    }

    fn debug_syscall_called(&self, last_syscall: Syscall) {
        self.debug.map(|debug| {
            debug.syscall_count += 1;
            debug.last_syscall = Some(last_syscall);
        });
    }

    fn debug_syscall_last(&self) -> Option<Syscall> {
        self.debug.map_or(None, |debug| debug.last_syscall)
    }

    fn get_addresses(&self) -> Result<ProcessAddresses, ()> {
        self.app_memory_allocator.map_or(Err(()), |am| {
            Ok(ProcessAddresses {
                flash_start: am.flash_start().as_usize(),
                flash_non_protected_start: am
                    .flash_start()
                    .wrapping_add(self.header.get_protected_size() as usize)
                    .as_usize(),
                flash_integrity_end: am.flash_start().as_usize()
                    + self.header.get_binary_end() as usize,
                flash_end: am.flash_end().as_usize(),
                sram_start: am.memory_start().as_usize(),
                sram_app_brk: am.app_break().as_usize(),
                sram_grant_start: am.kernel_break().as_usize(),
                sram_end: am.memory_end().as_usize(),
                sram_heap_start: self.debug.map_or(None, |debug| {
                    debug.app_heap_start_pointer.map(|p| p.as_usize())
                }),
                sram_stack_top: self.debug.map_or(None, |debug| {
                    debug.app_stack_start_pointer.map(|p| p.as_usize())
                }),
                sram_stack_bottom: self.debug.map_or(None, |debug| {
                    debug.app_stack_min_pointer.map(|p| p.as_usize())
                }),
            })
        })
    }

    fn get_sizes(&self) -> ProcessSizes {
        ProcessSizes {
            grant_pointers: mem::size_of::<GrantPointerEntry>()
                * self.kernel.get_grant_count_and_finalize(),
            upcall_list: Self::CALLBACKS_OFFSET,
            process_control_block: Self::PROCESS_STRUCT_OFFSET,
        }
    }

    fn print_full_process(&self, writer: &mut dyn Write) {
        if !config::CONFIG.debug_panics {
            return;
        }

        self.stored_state.map(|stored_state| {
            // We guarantee the memory bounds pointers provided to the UKB are
            // correct.
            self.app_memory_allocator.map(|am| unsafe {
                self.chip.userspace_kernel_boundary().print_context(
                    am.memory_start(),
                    am.app_break(),
                    stored_state,
                    writer,
                );
            });
        });

        // Display grant information.
        let number_grants = self.kernel.get_grant_count_and_finalize();
        let _ = writer.write_fmt(format_args!(
            "\
            \r\n Total number of grant regions defined: {}\r\n",
            self.kernel.get_grant_count_and_finalize()
        ));
        let rows = (number_grants + 2) / 3;

        // Access our array of grant pointers.
        self.grant_pointers.map(|grant_pointers| {
            // Iterate each grant and show its address.
            for i in 0..rows {
                for j in 0..3 {
                    let index = i + (rows * j);
                    if index >= number_grants {
                        break;
                    }

                    // Implement `grant_pointers[grant_num]` without a chance of
                    // a panic.
                    grant_pointers.get(index).map(|grant_entry| {
                        if grant_entry.grant_ptr.is_null() {
                            let _ =
                                writer.write_fmt(format_args!("  Grant {:>2} : --        ", index));
                        } else {
                            let _ = writer.write_fmt(format_args!(
                                "  Grant {:>2} {:#x}: {:?}",
                                index, grant_entry.driver_num, grant_entry.grant_ptr
                            ));
                        }
                    });
                }
                let _ = writer.write_fmt(format_args!("\r\n"));
            }
        });

        // Display the current state of the MPU for this process.
        self.app_memory_allocator.map(|am| {
            for region in am.regions.iter() {
                let _ = writer.write_fmt(format_args!("{}", region));
            }
        });

        // Print a helpful message on how to re-compile a process to view the
        // listing file. If a process is PIC, then we also need to print the
        // actual addresses the process executed at so that the .lst file can be
        // generated for those addresses. If the process was already compiled
        // for a fixed address, then just generating a .lst file is fine.

        let _ = self.debug.map_or(None, |debug| {
            if debug.fixed_address_flash.is_some() {
                // Fixed addresses, can just run `make lst`.
                let _ = writer.write_fmt(format_args!(
                    "\
                    \r\nTo debug libtock-c apps, run `make lst` in the app's\
                    \r\nfolder and open the arch.{:#x}.{:#x}.lst file.\r\n\r\n",
                    debug.fixed_address_flash.unwrap_or(0),
                    debug.fixed_address_ram.unwrap_or(0)
                ));
            } else {
                // PIC, need to specify the addresses.
                let sram_start = self.mem_start()?.as_usize();
                let flash_start = self.flash_start()?.as_usize();
                let flash_init_fn = flash_start + self.header.get_init_function_offset() as usize;

                let _ = writer.write_fmt(format_args!(
                    "\
                    \r\nTo debug libtock-c apps, run\
                    \r\n`make debug RAM_START={:#x} FLASH_INIT={:#x}`\
                    \r\nin the app's folder and open the .lst file.\r\n\r\n",
                    sram_start, flash_init_fn
                ));
            }
            Some(())
        });
    }

    fn get_stored_state(&self, out: &mut [u8]) -> Result<usize, ErrorCode> {
        self.stored_state
            .map(|stored_state| {
                self.chip
                    .userspace_kernel_boundary()
                    .store_context(stored_state, out)
            })
            .unwrap_or(Err(ErrorCode::FAIL))
    }

    fn get_flash_start(&self) -> Option<usize> {
        Some(self.flash_start()?.as_usize())
    }

    fn get_flash_end(&self) -> Option<usize> {
        Some(self.flash_end()?.as_usize())
    }

    fn get_sram_start(&self) -> Option<usize> {
        Some(self.mem_start()?.as_usize())
    }

    fn get_sram_end(&self) -> Option<usize> {
        Some(self.mem_end()?.as_usize())
    }
}

impl<C: 'static + Chip> ProcessStandard<'_, C> {
    // Memory offset for upcall ring buffer (10 element length).
    const CALLBACK_LEN: usize = 10;
    const CALLBACKS_OFFSET: usize = mem::size_of::<Task>() * Self::CALLBACK_LEN;

    // Memory offset to make room for this process's metadata.
    const PROCESS_STRUCT_OFFSET: usize = mem::size_of::<ProcessStandard<C>>();

    /// Create a `ProcessStandard` object based on the found `ProcessBinary`.
    // #[flux_rs::opts(check_overflow = "strict")]
    #[flux_rs::opts(solver = "z3")]
    #[flux_rs::sig(
        fn (
            _,
            _,
            ProcessBinary,
            &mut [u8],
            _,
            ShortId,
            usize
        )-> Result<(Option<&_>, &mut [u8]), (ProcessLoadError, &mut [u8])>
    )]
    pub(crate) unsafe fn create<'a>(
        kernel: &'static Kernel,
        chip: &'static C,
        pb: ProcessBinary,
        remaining_memory: &'a mut [u8],
        fault_policy: &'static dyn ProcessFaultPolicy,
        app_id: ShortId,
        index: usize,
    ) -> Result<(Option<&'static dyn Process>, &'a mut [u8]), (ProcessLoadError, &'a mut [u8])>
    {
        let dwt = chip.dwt();
        dwt.reset();
        dwt.start();
        let process_name = pb.header.get_package_name();
        let process_ram_requested_size = pb.header.get_minimum_app_ram_size() as usize;

        // Determine how much space we need in the application's memory space
        // just for kernel and grant state. We need to make sure we allocate
        // enough memory just for that.

        // Make room for grant pointers.
        let grant_ptr_size = mem::size_of::<GrantPointerEntry>();
        let grant_ptrs_num = kernel.get_grant_count_and_finalize();
        let grant_ptrs_offset = grant_ptrs_num * grant_ptr_size;

        // Initial size of the kernel-owned part of process memory can be
        // calculated directly based on the initial size of all kernel-owned
        // data structures.
        //
        // We require our kernel memory break (located at the end of the
        // MPU-returned allocated memory region) to be word-aligned. However, we
        // don't have any explicit alignment constraints from the MPU. To ensure
        // that the below kernel-owned data structures still fit into the
        // kernel-owned memory even with padding for alignment, add an extra
        // `sizeof(usize)` bytes.
        let upper_bound = (u32::MAX / 4) as usize;
        let usize_size = core::mem::size_of::<usize>();
        let callbacks_offset = Self::CALLBACKS_OFFSET;
        let process_struct_offset = Self::PROCESS_STRUCT_OFFSET;

        if !(process_struct_offset < isize_into_usize(isize::MAX)
            && 0 < process_struct_offset
            && process_struct_offset < upper_bound
            && 0 < callbacks_offset
            && callbacks_offset < upper_bound
            && 0 < usize_size
            && usize_size <= 8
            && grant_ptrs_offset < upper_bound)
        {
            return Err((ProcessLoadError::NotEnoughMemory, remaining_memory));
        }

        let initial_kernel_memory_size =
            grant_ptrs_offset + callbacks_offset + process_struct_offset + usize_size;

        // By default we start with the initial size of process-accessible
        // memory set to 0. This maximizes the flexibility that processes have
        // to allocate their memory as they see fit. If a process needs more
        // accessible memory it must use the `brk` memop syscalls to request
        // more memory.
        //
        // We must take into account any process-accessible memory required by
        // the context switching implementation and allocate at least that much
        // memory so that we can successfully switch to the process. This is
        // architecture and implementation specific, so we query that now.
        let min_process_memory_size = chip
            .userspace_kernel_boundary()
            .initial_process_app_brk_size();

        // We have to ensure that we at least ask the MPU for
        // `min_process_memory_size` so that we can be sure that `app_brk` is
        // not set inside the kernel-owned memory region. Now, in practice,
        // processes should not request 0 (or very few) bytes of memory in their
        // TBF header (i.e. `process_ram_requested_size` will almost always be
        // much larger than `min_process_memory_size`), as they are unlikely to
        // work with essentially no available memory. But, we still must protect
        // for that case.
        let min_process_ram_size = cmp::max(process_ram_requested_size, min_process_memory_size);

        // Minimum memory size for the process.
        let min_total_memory_size = min_process_ram_size + initial_kernel_memory_size;

        // Check if this process requires a fixed memory start address. If so,
        // try to adjust the memory region to work for this process.
        //
        // Right now, we only support skipping some RAM and leaving a chunk
        // unused so that the memory region starts where the process needs it
        // to.
        let remaining_memory = if let Some(fixed_memory_start) = pb.header.get_fixed_address_ram() {
            // The process does have a fixed address.
            if fixed_memory_start as usize == remaining_memory.as_fluxptr().as_usize() {
                // Address already matches.
                remaining_memory
            } else if fixed_memory_start as usize > remaining_memory.as_fluxptr().as_usize() {
                // Process wants a memory address farther in memory. Try to
                // advance the memory region to make the address match.
                let diff = (fixed_memory_start as usize)
                    .wrapping_sub(remaining_memory.as_fluxptr().as_usize());
                if diff > remaining_memory.len() {
                    // We ran out of memory.
                    let actual_address = remaining_memory
                        .as_fluxptr()
                        .as_u32()
                        .wrapping_add(remaining_memory.len() as u32)
                        .wrapping_sub(1);
                    let expected_address = fixed_memory_start;
                    return Err((
                        ProcessLoadError::MemoryAddressMismatch {
                            actual_address,
                            expected_address,
                        },
                        remaining_memory,
                    ));
                } else {
                    // Change the memory range to start where the process
                    // requested it. Because of the if statement above we know this should
                    // work. Doing it more cleanly would be good but was a bit beyond my borrow
                    // ken; calling get_mut has a mutable borrow.-pal
                    &mut remaining_memory[diff..]
                }
            } else {
                // Address is earlier in memory, nothing we can do.
                let actual_address = remaining_memory.as_fluxptr().as_u32();
                let expected_address = fixed_memory_start;
                return Err((
                    ProcessLoadError::MemoryAddressMismatch {
                        actual_address,
                        expected_address,
                    },
                    remaining_memory,
                ));
            }
        } else {
            remaining_memory
        };

        // Determine where process memory will go and allocate an MPU region.
        //
        // `[allocation_start, allocation_size)` will cover both
        //
        // - the app-owned `min_process_memory_size`-long part of memory (at
        //   some offset within `remaining_memory`), as well as
        //
        // - the kernel-owned allocation growing downward starting at the end
        //   of this allocation, `initial_kernel_memory_size` bytes long.
        //
        let Pair {
            fst: flash_ptrs,
            snd: remaining_mem_ptrs,
        } = mem_slices_to_raw_ptrs(pb.flash, remaining_memory);

        flux_rs::assert(initial_kernel_memory_size > 0);
        // Initialize MPU region configuration.
        let app_memory_alloc = match AppMemoryAllocator::allocate_app_memory(
            index,
            remaining_mem_ptrs.start,
            remaining_mem_ptrs.len,
            min_total_memory_size,
            min_process_memory_size,
            initial_kernel_memory_size,
            flash_ptrs.start,
            flash_ptrs.len,
        ) {
            Ok(bnsz) => bnsz,
            Err(allocator::AllocateAppMemoryError::FlashError) => {
                if config::CONFIG.debug_load_processes {
                    debug!(
                            "[!] flash={:#010X}-{:#010X} process={:?} - couldn't allocate MPU region for flash",
                            flash_ptrs.start.as_usize(),
                            flash_ptrs.start.as_usize().wrapping_add(flash_ptrs.len).wrapping_sub(1),
                            process_name
                        );
                }
                return Err((ProcessLoadError::MpuInvalidFlashLength, remaining_memory));
            }
            Err(allocator::AllocateAppMemoryError::HeapError) => {
                // Failed to load process. Insufficient memory.
                if config::CONFIG.debug_load_processes {
                    debug!(
                            "[!] flash={:#010X}-{:#010X} process={:?} - couldn't allocate memory region of size >= {:#X}",
                            remaining_mem_ptrs.start.as_usize(),
                            remaining_mem_ptrs.start.as_usize().wrapping_add(remaining_mem_ptrs.len).wrapping_sub(1),
                            process_name,
                            min_total_memory_size
                        );
                }
                return Err((ProcessLoadError::NotEnoughMemory, remaining_memory));
            }
        };

        let allocation_start = app_memory_alloc.memory_start();
        let allocation_size = app_memory_alloc.memory_size();

        // Determine the offset of the app-owned part of the above memory
        // allocation. An MPU may not place it at the very start of
        // `remaining_memory` for internal alignment constraints. This can only
        // overflow if the MPU implementation is incorrect; a compliant
        // implementation must return a memory allocation within the
        // `remaining_memory` slice.
        let app_memory_start_offset =
            allocation_start.as_usize() - remaining_mem_ptrs.start.as_usize();

        // Check if the memory region is valid for the process. If a process
        // included a fixed address for the start of RAM in its TBF header (this
        // field is optional, processes that are position independent do not
        // need a fixed address) then we check that we used the same address
        // when we allocated it in RAM.
        if let Some(fixed_memory_start) = pb.header.get_fixed_address_ram() {
            let actual_address =
                remaining_memory.as_fluxptr().as_u32() + app_memory_start_offset as u32;
            let expected_address = fixed_memory_start;
            if actual_address != expected_address {
                return Err((
                    ProcessLoadError::MemoryAddressMismatch {
                        actual_address,
                        expected_address,
                    },
                    remaining_memory,
                ));
            }
        }

        // With our MPU allocation, we can begin to divide up the
        // `remaining_memory` slice into individual regions for the process and
        // kernel, as follows:
        //
        //
        //  +-----------------------------------------------------------------
        //  | remaining_memory
        //  +----------------------------------------------------+------------
        //  v                                                    v
        //  +----------------------------------------------------+
        //  | allocated_padded_memory                            |
        //  +--+-------------------------------------------------+
        //     v                                                 v
        //     +-------------------------------------------------+
        //     | allocated_memory                                |
        //     +-------------------------------------------------+
        //     v                                                 v
        //     +-----------------------+-------------------------+
        //     | app_accessible_memory | allocated_kernel_memory |
        //     +-----------------------+-------------------+-----+
        //                                                 v
        //                               kernel memory break
        //                                                  \---+/
        //                                                      v
        //                                        optional padding
        //
        //
        // First split the `remaining_memory` into two slices:
        //
        // - `allocated_padded_memory`: the allocated memory region, containing
        //
        //   1. optional padding at the start of the memory region of
        //      `app_memory_start_offset` bytes,
        //
        //   2. the app accessible memory region of `process_allocated_size` (the size given by the MPU region),
        //
        //   3. optional unallocated memory, and
        //
        //   4. kernel-reserved memory, growing downward starting at
        //      `app_memory_padding`.
        //
        // - `unused_memory`: the rest of the `remaining_memory`, not assigned
        //   to this app.
        //
        let (_allocated_padded_memory, unused_memory) =
            remaining_memory.split_at_mut(app_memory_start_offset + allocation_size);

        // Now, slice off the (optional) padding at the start:
        let allocated_memory_start = app_memory_alloc.memory_start();
        let allocated_memory_len = app_memory_alloc.memory_size();

        // Set up initial grant region.
        //
        // `kernel_memory_break` is set to the end of kernel-accessible memory
        // and grows downward.
        //
        // We require the `kernel_memory_break` to be aligned to a
        // word-boundary, as we rely on this during offset calculations to
        // kernel-accessed structs (e.g. the grant pointer table) below. As it
        // moves downward in the address space, we can't use the `align_offset`
        // convenience functions.
        //
        // Calling `wrapping_sub` is safe here, as we've factored in an optional
        // padding of at most `sizeof(usize)` bytes in the calculation of
        // `initial_kernel_memory_size` above.
        let mut kernel_memory_break = app_memory_alloc.memory_end();

        kernel_memory_break =
            kernel_memory_break.wrapping_sub(kernel_memory_break.as_usize() % usize_size);

        // Now that we know we have the space we can setup the grant pointers.
        // kernel_memory_break = kernel_memory_break.offset(-(grant_ptrs_offset as isize)); // VTOCK TODO: Something about usize cast to isize here?

        // This is safe, `kernel_memory_break` is aligned to a word-boundary,
        // and `grant_ptrs_offset` is a multiple of the word size.
        #[allow(clippy::cast_ptr_alignment)]
        // Set all grant pointers to null.
        let grant_pointers = core::slice::from_raw_parts_mut(
            kernel_memory_break.unsafe_as_ptr() as *mut GrantPointerEntry,
            grant_ptrs_num,
        );
        for grant_entry in grant_pointers.iter_mut() {
            grant_entry.driver_num = 0;
            grant_entry.grant_ptr = FluxPtr::null_mut();
        }

        // Now that we know we have the space we can setup the memory for the
        // upcalls.
        let callbacks_isize = usize_into_isize(callbacks_offset);
        kernel_memory_break = kernel_memory_break.offset(-callbacks_isize);

        // This is safe today, as MPU constraints ensure that `memory_start`
        // will always be aligned on at least a word boundary, and that
        // memory_size will be aligned on at least a word boundary, and
        // `grant_ptrs_offset` is a multiple of the word size. Thus,
        // `kernel_memory_break` must be word aligned. While this is unlikely to
        // change, it should be more proactively enforced.
        //
        // TODO: https://github.com/tock/tock/issues/1739
        #[allow(clippy::cast_ptr_alignment)]
        // Set up ring buffer for upcalls to the process.
        let upcall_buf = flux_support::from_raw_parts_mut(
            kernel_memory_break.unsafe_as_ptr() as *mut Task,
            Self::CALLBACK_LEN,
        );
        let tasks = RingBuffer::new(upcall_buf);

        // Last thing in the kernel region of process RAM is the process struct.
        let process_struct_offset = usize_into_isize(process_struct_offset);
        kernel_memory_break = kernel_memory_break.offset(-process_struct_offset);
        let process_struct_memory_location = kernel_memory_break;

        // Create the Process struct in the app grant region.
        // Note that this requires every field be explicitly initialized
        // we are just transforming a pointer into a structure.
        let process: &mut ProcessStandard<C> = &mut *(process_struct_memory_location.unsafe_as_ptr()
            as *mut ProcessStandard<'static, C>);

        // Ask the kernel for a unique identifier for this process that is being
        // created.
        let unique_identifier = kernel.create_process_identifier();

        // Save copies of these in case the app was compiled for fixed addresses
        // for later debugging.
        let fixed_address_flash = pb.header.get_fixed_address_flash();
        let fixed_address_ram = pb.header.get_fixed_address_ram();

        process
            .process_id
            .set(ProcessId::new(kernel, unique_identifier, index));
        process.app_id = app_id;
        process.kernel = kernel;
        process.chip = chip;

        process.header = pb.header;

        process.grant_pointers = MapCell::new(grant_pointers);

        process.credential = pb.credential.get();
        process.footers = pb.footers;

        process.stored_state = MapCell::new(Default::default());
        // Mark this process as approved and leave it to the kernel to start it.
        process.state = Cell::new(State::Yielded);
        process.fault_policy = fault_policy;
        process.restart_count = Cell::new(0);
        process.completion_code = OptionalCell::empty();

        let app_break = app_memory_alloc.app_break();
        let memory_start = app_memory_alloc.memory_start();
        process.app_memory_allocator = MapCell::new(app_memory_alloc);
        process.tasks = MapCell::new(tasks);

        process.debug = MapCell::new(ProcessStandardDebug {
            fixed_address_flash,
            fixed_address_ram,
            app_heap_start_pointer: None,
            app_stack_start_pointer: None,
            app_stack_min_pointer: None,
            syscall_count: 0,
            last_syscall: None,
            dropped_upcall_count: 0,
            timeslice_expiration_count: 0,
        });

        // Handle any architecture-specific requirements for a new process.
        //
        // NOTE! We have to ensure that the start of process-accessible memory
        // (`app_memory_start`) is word-aligned. Since we currently start
        // process-accessible memory at the beginning of the allocated memory
        // region, we trust the MPU to give us a word-aligned starting address.
        //
        // TODO: https://github.com/tock/tock/issues/1739
        match process.stored_state.map(|stored_state| {
            chip.userspace_kernel_boundary().initialize_process(
                memory_start,
                app_break,
                stored_state,
            )
        }) {
            Some(Ok(())) => {}
            _ => {
                if config::CONFIG.debug_load_processes {
                    debug!(
                        "[!] flash={:#010X}-{:#010X} process={:?} - couldn't initialize process",
                        flash_ptrs.start.as_usize(),
                        (flash_ptrs.start.as_usize() + flash_ptrs.len).wrapping_sub(1),
                        process_name
                    );
                }
                // Note that since remaining_memory was split by split_at_mut into
                // application memory and unused_memory, a failure here will leak
                // the application memory. Not leaking it requires being able to
                // reconstitute the original memory slice.
                return Err((ProcessLoadError::InternalError, unused_memory));
            }
        };

        let app_start = flash_ptrs
            .start
            .wrapping_add(process.header.get_app_start_offset() as usize)
            .as_usize();
        let init_fn = flash_ptrs
            .start
            .wrapping_add(process.header.get_init_function_offset() as usize)
            .as_usize();

        process.tasks.map(|tasks| {
            let app_break = process
                .app_memory_break()
                .map_err(|_| ProcessLoadError::MpuConfigurationError)?
                .as_usize();
            tasks.enqueue(Task::FunctionCall(FunctionCall {
                source: FunctionCallSource::Kernel,
                pc: init_fn,
                argument0: app_start,
                argument1: allocated_memory_start.as_usize(),
                argument2: allocated_memory_len,
                argument3: app_break,
            }));
            Ok::<(), ProcessLoadError>(())
        });
        dwt.stop();
        let count = dwt.count();
        crate::debug!("[EVAL] create {}", count);
        // Return the process object and a remaining memory for processes slice.
        Ok((Some(process), unused_memory))
    }

    /// Reset the process, resetting all of its state and re-initializing it so
    /// it can start running. Assumes the process is not running but is still in
    /// flash and still has its memory region allocated to it.
    fn reset(&self) -> Result<(), ErrorCode> {
        // We need a new process identifier for this process since the restarted
        // version is in effect a new process. This is also necessary to
        // invalidate any stored `ProcessId`s that point to the old version of
        // the process. However, the process has not moved locations in the
        // processes array, so we copy the existing index.
        let old_index = self.process_id.get().index;
        let new_identifier = self.kernel.create_process_identifier();
        self.process_id
            .set(ProcessId::new(self.kernel, new_identifier, old_index));

        // Reset debug information that is per-execution and not per-process.
        self.debug.map(|debug| {
            debug.syscall_count = 0;
            debug.last_syscall = None;
            debug.dropped_upcall_count = 0;
            debug.timeslice_expiration_count = 0;
        });

        // Reset MPU region configuration.
        //
        // TODO: ideally, this would be moved into a helper function used by
        // both create() and reset(), but process load debugging complicates
        // this. We just want to create new config with only flash and memory
        // regions.
        //
        // We must have a previous MPU configuration stored, fault the
        // process if this invariant is violated. We avoid allocating
        // a new MPU configuration, as this may eventually exhaust the
        // number of available MPU configurations.
        let app_memory_alloc = self.app_memory_allocator.take().ok_or(ErrorCode::FAIL)?;
        let app_breaks = app_memory_alloc.breaks;

        // RAM and Flash

        // Re-determine the minimum amount of RAM the kernel must allocate to
        // the process based on the specific requirements of the syscall
        // implementation.
        let min_process_memory_size = self
            .chip
            .userspace_kernel_boundary()
            .initial_process_app_brk_size();

        // Recalculate initial_kernel_memory_size as was done in create()
        let grant_ptr_size = mem::size_of::<(usize, FluxPtrU8Mut)>();
        let grant_ptrs_num = self.kernel.get_grant_count_and_finalize();
        let grant_ptrs_offset = grant_ptrs_num * grant_ptr_size;

        let size_offset = Self::CALLBACKS_OFFSET + Self::PROCESS_STRUCT_OFFSET;
        let initial_kernel_memory_size = grant_ptrs_offset + size_offset;
        if !(0 < initial_kernel_memory_size && initial_kernel_memory_size <= u32::MAX as usize) {
            return Err(ErrorCode::FAIL);
        }
        let maybe_app_mem_alloc = AppMemoryAllocator::allocate_app_memory(
            new_identifier,
            app_breaks.memory_start,
            app_breaks.memory_size,
            min_process_memory_size,
            min_process_memory_size,
            initial_kernel_memory_size,
            app_breaks.flash_start,
            app_breaks.flash_size,
        );
        let app_mem_alloc: AppMemoryAllocator<<<C as Chip>::MPU as mpu::MPU>::Region> =
            match maybe_app_mem_alloc {
                Ok(breaks_and_size) => breaks_and_size,
                Err(allocator::AllocateAppMemoryError::FlashError) => {
                    return Err(ErrorCode::FAIL);
                }
                Err(allocator::AllocateAppMemoryError::HeapError) => {
                    // We couldn't configure the MPU for the process. This shouldn't
                    // happen since we were able to start the process before, but at
                    // this point it is better to leave the app faulted and not
                    // schedule it.
                    return Err(ErrorCode::NOMEM);
                }
            };

        // Reset memory pointers now that we know the layout of the process
        // memory and know that we can configure the MPU.

        let app_mpu_mem_start = app_mem_alloc.memory_start();
        let app_brk = app_mem_alloc.app_break();
        self.app_memory_allocator.replace(app_memory_alloc);

        // Handle any architecture-specific requirements for a process when it
        // first starts (as it would when it is new).
        let ukb_init_process = self.stored_state.map_or(Err(()), |stored_state| unsafe {
            self.chip.userspace_kernel_boundary().initialize_process(
                app_mpu_mem_start,
                app_brk,
                stored_state,
            )
        });
        match ukb_init_process {
            Ok(()) => {}
            Err(()) => {
                // We couldn't initialize the architecture-specific state for
                // this process. This shouldn't happen since the app was able to
                // be started before, but at this point the app is no longer
                // valid. The best thing we can do now is leave the app as still
                // faulted and not schedule it.
                return Err(ErrorCode::RESERVE);
            }
        };

        self.restart_count.increment();

        // Mark the state as `Yielded` for the scheduler.
        self.state.set(State::Yielded);

        // And queue up this app to be restarted.
        let flash_start = app_breaks.flash_start;
        let app_start = flash_start
            .wrapping_add(self.header.get_app_start_offset() as usize)
            .as_usize();
        let init_fn = flash_start
            .wrapping_add(self.header.get_init_function_offset() as usize)
            .as_usize();

        self.enqueue_task(Task::FunctionCall(FunctionCall {
            source: FunctionCallSource::Kernel,
            pc: init_fn,
            argument0: app_start,
            argument1: app_breaks.memory_start.as_usize(),
            argument2: app_breaks.memory_size,
            argument3: app_breaks.app_break.as_usize(),
        }))
    }

    fn update_debug_sp(&self, stack_pointer: Option<FluxPtrU8>) {
        #[flux_rs::spec(
            fn(debug: &mut ProcessStandardDebug, stack_pointer: _)
            ensures debug: ProcessStandardDebug
        )]
        fn update_strg(debug: &mut ProcessStandardDebug, sp: FluxPtrU8) {
            match debug.app_stack_min_pointer {
                None => debug.app_stack_min_pointer = Some(sp),
                Some(asmp) => {
                    // Update max stack depth if needed.
                    if sp < asmp {
                        debug.app_stack_min_pointer = Some(sp);
                    }
                }
            }
        }
        if let Some(sp) = stack_pointer {
            self.debug.map(|debug| {
                update_strg(debug, sp);
            });
        }
    }

    /// Checks if the buffer represented by the passed in base pointer and size
    /// is within the RAM bounds currently exposed to the processes (i.e. ending
    /// at `app_break`). If this method returns `true`, the buffer is guaranteed
    /// to be accessible to the process and to not overlap with the grant
    /// region.
    fn in_app_owned_memory(&self, buf_start_addr: FluxPtrU8Mut, size: usize) -> Result<bool, ()> {
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        self.app_memory_allocator.map_or(Err(()), |am| {
            Ok(am.in_app_ram_memory(buf_start_addr, buf_end_addr))
        })
    }

    /// Checks if the buffer represented by the passed in base pointer and size
    /// are within the readable region of an application's flash memory.  If
    /// this method returns true, the buffer is guaranteed to be readable to the
    /// process.
    fn in_app_flash_memory(&self, buf_start_addr: FluxPtrU8Mut, size: usize) -> Option<bool> {
        let buf_end_addr = buf_start_addr.wrapping_add(size);
        Some(
            buf_end_addr >= buf_start_addr
                && buf_start_addr >= self.flash_non_protected_start()?
                && buf_end_addr <= self.flash_end()?,
        )
    }

    /// Reset all `grant_ptr`s to NULL.
    unsafe fn grant_ptrs_reset(&self) {
        self.grant_pointers.map(|grant_pointers| {
            for grant_entry in grant_pointers.iter_mut() {
                grant_entry.driver_num = 0;
                grant_entry.grant_ptr = FluxPtr::null_mut();
            }
        });
    }

    /// Allocate memory in a process's grant region.
    ///
    /// Ensures that the allocation is of `size` bytes and aligned to `align`
    /// bytes.
    ///
    /// If there is not enough memory, or the MPU cannot isolate the process
    /// accessible region from the new kernel memory break after doing the
    /// allocation, then this will return `None`.
    fn allocate_in_grant_region_internal(&self, size: usize, align: usize) -> Option<FluxPtrU8> {
        self.app_memory_allocator
            .and_then(|am| am.allocate_in_grant_region_internal(size, align))
    }

    /// Use a `ProcessCustomGrantIdentifier` to find the address of the
    /// custom grant.
    ///
    /// This reverses `create_custom_grant_identifier()`.
    fn get_custom_grant_address(&self, identifier: ProcessCustomGrantIdentifier) -> Option<usize> {
        let process_memory_end = self.mem_end()?.as_usize();
        // assume(process_memory_end > identifier.offset);
        // Subtract the offset in the identifier from the end of the process
        // memory to get the address of the custom grant.
        Some(process_memory_end - identifier.offset)
    }

    /// The start address of allocated RAM for this process.
    fn mem_start(&self) -> Option<FluxPtrU8Mut> {
        self.app_memory_allocator
            .map_or(None, |am| Some(am.memory_start()))
    }

    /// The first address after the end of the allocated RAM for this process.
    // #[flux_rs::sig(fn(self: &Self[@p]) -> FluxPtrU8Mut[p.mem_start + p.mem_len])]
    fn mem_end(&self) -> Option<FluxPtrU8Mut> {
        self.app_memory_allocator
            .map_or(None, |am| Some(am.memory_end()))
    }

    /// The start address of the flash region allocated for this process.
    fn flash_start(&self) -> Option<FluxPtrU8Mut> {
        self.app_memory_allocator
            .map_or(None, |am| Some(am.flash_start()))
    }

    /// Get the first address of process's flash that isn't protected by the
    /// kernel. The protected range of flash contains the TBF header and
    /// potentially other state the kernel is storing on behalf of the process,
    /// and cannot be edited by the process.
    fn flash_non_protected_start(&self) -> Option<FluxPtrU8Mut> {
        self.app_memory_allocator.map_or(None, |am| {
            Some(
                am.flash_start()
                    .wrapping_add(self.header.get_protected_size() as usize),
            )
        })
    }

    /// The first address after the end of the flash region allocated for this
    /// process.
    fn flash_end(&self) -> Option<FluxPtrU8Mut> {
        self.app_memory_allocator
            .map_or(None, |am| Some(am.flash_end()))
    }

    /// Return the highest address the process has access to, or the current
    /// process memory brk.
    fn app_memory_break(&self) -> Result<FluxPtrU8Mut, ()> {
        self.app_memory_allocator
            .map_or(Err(()), |am| Ok(am.app_break()))
    }
}
