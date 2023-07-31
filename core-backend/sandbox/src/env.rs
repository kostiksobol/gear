// This file is part of Gear.

// Copyright (C) 2021-2023 Gear Technologies Inc.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! sp-sandbox environment for running a module.

use crate::{runtime, runtime::CallerWrap, MemoryWrap};
use alloc::{collections::BTreeSet, format};
use core::{
    convert::Infallible,
    fmt::Display,
    marker::{Send, Sync},
};
use gear_backend_common::{
    funcs::FuncsHandler,
    lazy_pages::{GlobalsAccessConfig, GlobalsAccessMod},
    runtime::RunFallibleError,
    state::{HostState, State},
    ActorTerminationReason, BackendAllocSyscallError, BackendExternalities, BackendReport,
    BackendSyscallError, BackendTermination, Environment, EnvironmentError,
    EnvironmentExecutionResult,
};
use gear_core::{
    gas::GasLeft,
    message::{DispatchKind, WasmEntryPoint},
    pages::{PageNumber, WasmPage},
};
use gear_sandbox::{
    default_executor::{
        Caller, EnvironmentDefinitionBuilder, Instance, Memory as DefaultExecutorMemory, Store,
    },
    AsContext, HostError, ReturnValue, SandboxEnvironmentBuilder, SandboxFunction,
    SandboxFunctionResult, SandboxInstance, SandboxMemory, SandboxStore, Value,
};
use gear_wasm_instrument::{
    syscalls::SysCallName::{self, *},
    GLOBAL_NAME_ALLOWANCE, GLOBAL_NAME_GAS, STACK_END_EXPORT_NAME,
};

#[derive(Clone, Copy)]
struct SandboxValue(Value);

impl From<i32> for SandboxValue {
    fn from(value: i32) -> Self {
        SandboxValue(Value::I32(value))
    }
}

impl From<u32> for SandboxValue {
    fn from(value: u32) -> Self {
        SandboxValue(Value::I32(value as i32))
    }
}

impl From<i64> for SandboxValue {
    fn from(value: i64) -> Self {
        SandboxValue(Value::I64(value))
    }
}

impl TryFrom<SandboxValue> for u32 {
    type Error = HostError;

    fn try_from(val: SandboxValue) -> Result<u32, HostError> {
        if let Value::I32(val) = val.0 {
            Ok(val as u32)
        } else {
            Err(HostError)
        }
    }
}

impl TryFrom<SandboxValue> for u64 {
    type Error = HostError;

    fn try_from(val: SandboxValue) -> Result<u64, HostError> {
        if let Value::I64(val) = val.0 {
            Ok(val as u64)
        } else {
            Err(HostError)
        }
    }
}

#[allow(unused_macros)]
macro_rules! wrap_common_func_internal_ret {
    ($func:path, $($arg_name:ident),*) => {
        move |memory: DefaultExecutorMemory| {
            move |caller: Caller<'_, HostState<Ext>>, $($arg_name,)*| -> Result<_, HostError>
            {
                let mut ctx = CallerWrap::prepare(caller, memory.clone())?;
                $func(&mut ctx, $($arg_name,)*)
            }
        }
    }
}

macro_rules! wrap_common_func_internal_no_ret {
    ($func:path, $($arg_name:ident),*) => {
        move |memory: DefaultExecutorMemory| {
            move |caller: Caller<'_, HostState<Ext>>, $($arg_name,)*| -> Result<(), HostError>
            {
                let mut ctx = CallerWrap::prepare(caller, memory.clone())?;
                $func(&mut ctx, $($arg_name,)*)
            }
        }
    }
}

#[rustfmt::skip]
macro_rules! wrap_common_func {
    ($func:path, () -> ()) =>   { wrap_common_func_internal_no_ret!($func,) };
    ($func:path, (1) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a) };
    ($func:path, (2) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b) };
    ($func:path, (3) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b, c) };
    ($func:path, (4) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b, c, d) };
    ($func:path, (5) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b, c, d, e) };
    ($func:path, (6) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b, c, d, e, f) };
    ($func:path, (7) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b, c, d, e, f, g) };
    ($func:path, (8) -> ()) =>  { wrap_common_func_internal_no_ret!($func, a, b, c, d, e, f, g, h) };

    ($func:path, () -> (1)) =>  { wrap_common_func_internal_ret!($func,)};
    ($func:path, (1) -> (1)) => { wrap_common_func_internal_ret!($func, a)};
    ($func:path, (2) -> (1)) => { wrap_common_func_internal_ret!($func, a, b)};
    ($func:path, (3) -> (1)) => { wrap_common_func_internal_ret!($func, a, b, c)};
    ($func:path, (4) -> (1)) => { wrap_common_func_internal_ret!($func, a, b, c, d)};
    ($func:path, (5) -> (1)) => { wrap_common_func_internal_ret!($func, a, b, c, d, e)};
    ($func:path, (6) -> (1)) => { wrap_common_func_internal_ret!($func, a, b, c, d, e, f)};
    ($func:path, (7) -> (1)) => { wrap_common_func_internal_ret!($func, a, b, c, d, e, f, g)};
    ($func:path, (8) -> (1)) => { wrap_common_func_internal_ret!($func, a, b, c, d, e, f, g, h)};
}

#[derive(Debug, derive_more::Display)]
pub enum SandboxEnvironmentError {
    #[display(fmt = "Failed to create env memory: {_0:?}")]
    CreateEnvMemory(gear_sandbox::Error),
    #[display(fmt = "Gas counter not found or has wrong type")]
    WrongInjectedGas,
    #[display(fmt = "Allowance counter not found or has wrong type")]
    WrongInjectedAllowance,
}

/// Environment to run one module at a time providing Ext.
pub struct SandboxEnvironment<Ext, EntryPoint = DispatchKind>
where
    Ext: BackendExternalities,
    EntryPoint: WasmEntryPoint,
{
    instance: Instance<HostState<Ext>>,
    entries: BTreeSet<DispatchKind>,
    entry_point: EntryPoint,
    store: Store<HostState<Ext>>,
    memory: DefaultExecutorMemory,
}

// A helping wrapper for `EnvironmentDefinitionBuilder` and `forbidden_funcs`.
// It makes adding functions to `EnvironmentDefinitionBuilder` shorter.
struct EnvBuilder<Ext: BackendExternalities> {
    env_def_builder: EnvironmentDefinitionBuilder<HostState<Ext>>,
    memory: DefaultExecutorMemory,
    forbidden_funcs: BTreeSet<SysCallName>,
    funcs_count: usize,
}

impl<Ext> EnvBuilder<Ext>
where
    Ext: BackendExternalities + 'static,
    Ext::UnrecoverableError: BackendSyscallError,
    RunFallibleError: From<Ext::FallibleError>,
    Ext::AllocError: BackendAllocSyscallError<ExtError = Ext::UnrecoverableError>,
{
    fn add_func<F, Args, R>(&mut self, store: &mut Store<HostState<Ext>>, name: SysCallName, f: F)
    where
        F: for<'a> SandboxFunction<Caller<'a, HostState<Ext>>, Args, R, HostState<Ext>>
            + Send
            + Sync
            + 'static,
        Args: 'static,
        R: SandboxFunctionResult + 'static,
    {
        if self.forbidden_funcs.contains(&name) {
            let memory = self.memory.clone();
            self.env_def_builder.add_host_func(
                store,
                "env",
                name.to_str(),
                wrap_common_func!(FuncsHandler::forbidden, () -> ())(memory),
            );
        } else {
            self.env_def_builder
                .add_host_func(store, "env", name.to_str(), f);
        }

        self.funcs_count += 1;
    }
}

impl<Ext: BackendExternalities> From<EnvBuilder<Ext>>
    for EnvironmentDefinitionBuilder<HostState<Ext>>
{
    fn from(builder: EnvBuilder<Ext>) -> Self {
        builder.env_def_builder
    }
}

impl<Ext, EntryPoint> SandboxEnvironment<Ext, EntryPoint>
where
    Ext: BackendExternalities + 'static,
    Ext::UnrecoverableError: BackendSyscallError,
    RunFallibleError: From<Ext::FallibleError>,
    Ext::AllocError: BackendAllocSyscallError<ExtError = Ext::UnrecoverableError>,
    EntryPoint: WasmEntryPoint,
{
    #[rustfmt::skip]
    fn bind_funcs(store: &mut Store<HostState<Ext>>, builder: &mut EnvBuilder<Ext>) {
        let memory = builder.memory.clone();
        builder.add_func(store, BlockHeight, wrap_common_func!(FuncsHandler::block_height, (1) -> ())(memory.clone()));
        builder.add_func(store, BlockTimestamp,wrap_common_func!(FuncsHandler::block_timestamp, (1) -> ())(memory.clone()));
        builder.add_func(store, CreateProgram, wrap_common_func!(FuncsHandler::create_program, (7) -> ())(memory.clone()));
        builder.add_func(store, CreateProgramWGas, wrap_common_func!(FuncsHandler::create_program_wgas, (8) -> ())(memory.clone()));
        builder.add_func(store, Debug, wrap_common_func!(FuncsHandler::debug, (2) -> ())(memory.clone()));
        builder.add_func(store, Panic, wrap_common_func!(FuncsHandler::panic, (2) -> ())(memory.clone()));
        builder.add_func(store, OomPanic, wrap_common_func!(FuncsHandler::oom_panic, () -> ())(memory.clone()));
        builder.add_func(store, Exit, wrap_common_func!(FuncsHandler::exit, (1) -> ())(memory.clone()));
        builder.add_func(store, ReplyCode, wrap_common_func!(FuncsHandler::reply_code, (1) -> ())(memory.clone()));
        builder.add_func(store, SignalCode, wrap_common_func!(FuncsHandler::signal_code, (1) -> ())(memory.clone()));
        builder.add_func(store, ReserveGas, wrap_common_func!(FuncsHandler::reserve_gas, (3) -> ())(memory.clone()));
        builder.add_func(store, ReplyDeposit, wrap_common_func!(FuncsHandler::reply_deposit, (3) -> ())(memory.clone()));
        builder.add_func(store, UnreserveGas, wrap_common_func!(FuncsHandler::unreserve_gas, (2) -> ())(memory.clone()));
        builder.add_func(store, GasAvailable, wrap_common_func!(FuncsHandler::gas_available, (1) -> ())(memory.clone()));
        builder.add_func(store, Leave, wrap_common_func!(FuncsHandler::leave, () -> ())(memory.clone()));
        builder.add_func(store, MessageId, wrap_common_func!(FuncsHandler::message_id, (1) -> ())(memory.clone()));
        builder.add_func(store, PayProgramRent, wrap_common_func!(FuncsHandler::pay_program_rent, (2) -> ())(memory.clone()));
        builder.add_func(store, ProgramId, wrap_common_func!(FuncsHandler::program_id, (1) -> ())(memory.clone()));
        builder.add_func(store, Random, wrap_common_func!(FuncsHandler::random, (2) -> ())(memory.clone()));
        builder.add_func(store, Read, wrap_common_func!(FuncsHandler::read, (4) -> ())(memory.clone()));
        builder.add_func(store, Reply, wrap_common_func!(FuncsHandler::reply, (4) -> ())(memory.clone()));
        builder.add_func(store, ReplyCommit, wrap_common_func!(FuncsHandler::reply_commit, (2) -> ())(memory.clone()));
        builder.add_func(store, ReplyCommitWGas, wrap_common_func!(FuncsHandler::reply_commit_wgas, (3) -> ())(memory.clone()));
        builder.add_func(store, ReplyPush, wrap_common_func!(FuncsHandler::reply_push, (3) -> ())(memory.clone()));
        builder.add_func(store, ReplyTo, wrap_common_func!(FuncsHandler::reply_to, (1) -> ())(memory.clone()));
        builder.add_func(store, SignalFrom, wrap_common_func!(FuncsHandler::signal_from, (1) -> ())(memory.clone()));
        builder.add_func(store, ReplyWGas, wrap_common_func!(FuncsHandler::reply_wgas, (5) -> ())(memory.clone()));
        builder.add_func(store, ReplyInput, wrap_common_func!(FuncsHandler::reply_input, (4) -> ())(memory.clone()));
        builder.add_func(store, ReplyPushInput, wrap_common_func!(FuncsHandler::reply_push_input, (3) -> ())(memory.clone()));
        builder.add_func(store, ReplyInputWGas, wrap_common_func!(FuncsHandler::reply_input_wgas, (5) -> ())(memory.clone()));
        builder.add_func(store, Send, wrap_common_func!(FuncsHandler::send, (5) -> ())(memory.clone()));
        builder.add_func(store, SendCommit, wrap_common_func!(FuncsHandler::send_commit, (4) -> ())(memory.clone()));
        builder.add_func(store, SendCommitWGas, wrap_common_func!(FuncsHandler::send_commit_wgas, (5) -> ())(memory.clone()));
        builder.add_func(store, SendInit, wrap_common_func!(FuncsHandler::send_init, (1) -> ())(memory.clone()));
        builder.add_func(store, SendPush, wrap_common_func!(FuncsHandler::send_push, (4) -> ())(memory.clone()));
        builder.add_func(store, SendWGas, wrap_common_func!(FuncsHandler::send_wgas, (6) -> ())(memory.clone()));
        builder.add_func(store, SendInput, wrap_common_func!(FuncsHandler::send_input, (5) -> ())(memory.clone()));
        builder.add_func(store, SendPushInput, wrap_common_func!(FuncsHandler::send_push_input, (4) -> ())(memory.clone()));
        builder.add_func(store, SendInputWGas, wrap_common_func!(FuncsHandler::send_input_wgas, (6) -> ())(memory.clone()));
        builder.add_func(store, Size, wrap_common_func!(FuncsHandler::size, (1) -> ())(memory.clone()));
        builder.add_func(store, Source, wrap_common_func!(FuncsHandler::source, (1) -> ())(memory.clone()));
        builder.add_func(store, Value, wrap_common_func!(FuncsHandler::value, (1) -> ())(memory.clone()));
        builder.add_func(store, ValueAvailable, wrap_common_func!(FuncsHandler::value_available, (1) -> ())(memory.clone()));
        builder.add_func(store, Wait, wrap_common_func!(FuncsHandler::wait, () -> ())(memory.clone()));
        builder.add_func(store, WaitFor, wrap_common_func!(FuncsHandler::wait_for, (1) -> ())(memory.clone()));
        builder.add_func(store, WaitUpTo, wrap_common_func!(FuncsHandler::wait_up_to, (1) -> ())(memory.clone()));
        builder.add_func(store, Wake, wrap_common_func!(FuncsHandler::wake, (3) -> ())(memory.clone()));
        builder.add_func(store, SystemReserveGas, wrap_common_func!(FuncsHandler::system_reserve_gas, (2) -> ())(memory.clone()));
        builder.add_func(store, ReservationReply, wrap_common_func!(FuncsHandler::reservation_reply, (4) -> ())(memory.clone()));
        builder.add_func(store, ReservationReplyCommit, wrap_common_func!(FuncsHandler::reservation_reply_commit, (2) -> ())(memory.clone()));
        builder.add_func(store, ReservationSend, wrap_common_func!(FuncsHandler::reservation_send, (5) -> ())(memory.clone()));
        builder.add_func(store, ReservationSendCommit, wrap_common_func!(FuncsHandler::reservation_send_commit, (4) -> ())(memory.clone()));
        builder.add_func(store, OutOfGas, wrap_common_func!(FuncsHandler::out_of_gas, () -> ())(memory.clone()));
        builder.add_func(store, OutOfAllowance, wrap_common_func!(FuncsHandler::out_of_allowance, () -> ())(memory.clone()));

        builder.add_func(store, Alloc, wrap_common_func!(FuncsHandler::alloc, (1) -> (1))(memory.clone()));
        builder.add_func(store, Free, wrap_common_func!(FuncsHandler::free, (1) -> (1))(memory));
    }
}

impl<EnvExt, EntryPoint> Environment<EntryPoint> for SandboxEnvironment<EnvExt, EntryPoint>
where
    EnvExt: BackendExternalities + 'static,
    EnvExt::UnrecoverableError: BackendSyscallError,
    RunFallibleError: From<EnvExt::FallibleError>,
    EnvExt::AllocError: BackendAllocSyscallError<ExtError = EnvExt::UnrecoverableError>,
    EntryPoint: WasmEntryPoint,
{
    type Ext = EnvExt;
    type Memory = MemoryWrap<EnvExt>;
    type SystemError = SandboxEnvironmentError;

    fn new(
        ext: Self::Ext,
        binary: &[u8],
        entry_point: EntryPoint,
        entries: BTreeSet<DispatchKind>,
        mem_size: WasmPage,
    ) -> Result<Self, EnvironmentError<Self::SystemError, Infallible>> {
        use EnvironmentError::*;
        use SandboxEnvironmentError::*;

        let entry_forbidden = entry_point
            .try_into_kind()
            .as_ref()
            .map(DispatchKind::forbidden_funcs)
            .unwrap_or_default();

        let mut store = Store::new(None);

        let memory: DefaultExecutorMemory = SandboxMemory::new(&mut store, mem_size.raw(), None)
            .map_err(|e| System(CreateEnvMemory(e)))?;

        let mut env_def_builder = EnvironmentDefinitionBuilder::new();
        env_def_builder.add_memory("env", "memory", memory.clone());

        let mut builder = EnvBuilder {
            env_def_builder,
            memory: memory.clone(),
            forbidden_funcs: ext
                .forbidden_funcs()
                .iter()
                .copied()
                .chain(entry_forbidden)
                .collect(),
            funcs_count: 0,
        };

        Self::bind_funcs(&mut store, &mut builder);

        // Check that we have implementations for all the sys-calls.
        // This is intended to panic during any testing, when the
        // condition is not met.
        assert_eq!(
            builder.funcs_count,
            SysCallName::count(),
            "Not all existing sys-calls were added to the module's env."
        );

        *store.data_mut() = Some(State {
            ext,
            termination_reason: ActorTerminationReason::Success.into(),
        });

        let env_builder: EnvironmentDefinitionBuilder<HostState<EnvExt>> = builder.into();
        let instance = Instance::new(&mut store, binary, env_builder).map_err(|e| {
            Actor(
                store
                    .data_mut()
                    .as_ref()
                    .expect("set before")
                    .ext
                    .gas_amount(),
                format!("{e:?}"),
            )
        })?;

        Ok(Self {
            instance,
            entries,
            entry_point,
            store,
            memory,
        })
    }

    fn execute<PrepareMemory, PrepareMemoryError>(
        self,
        prepare_memory: PrepareMemory,
    ) -> EnvironmentExecutionResult<PrepareMemoryError, Self, EntryPoint>
    where
        PrepareMemory: FnOnce(
            &mut Self::Memory,
            Option<u32>,
            GlobalsAccessConfig,
        ) -> Result<(), PrepareMemoryError>,
        PrepareMemoryError: Display,
    {
        use EnvironmentError::*;
        use SandboxEnvironmentError::*;

        let Self {
            mut instance,
            entries,
            entry_point,
            mut store,
            memory,
        } = self;

        let stack_end = instance
            .get_global_val(&store, STACK_END_EXPORT_NAME)
            .and_then(|global| global.as_i32())
            .map(|global| global as u32);

        let GasLeft { gas, allowance } = store
            .data_mut()
            .as_ref()
            .unwrap_or_else(|| unreachable!(""))
            .ext
            .gas_left();

        instance
            .set_global_val(&mut store, GLOBAL_NAME_GAS, Value::I64(gas as i64))
            .map_err(|_| System(WrongInjectedGas))?;

        instance
            .set_global_val(
                &mut store,
                GLOBAL_NAME_ALLOWANCE,
                Value::I64(allowance as i64),
            )
            .map_err(|_| System(WrongInjectedAllowance))?;

        let globals_config = if cfg!(not(feature = "std")) {
            GlobalsAccessConfig {
                access_ptr: instance.get_instance_ptr(),
                access_mod: GlobalsAccessMod::WasmRuntime,
            }
        } else {
            unreachable!("We cannot use sandbox backend in std environment currently");
        };

        let mut memory_wrap = MemoryWrap::new(memory.clone(), store);
        match prepare_memory(&mut memory_wrap, stack_end, globals_config) {
            Ok(_) => (),
            Err(e) => {
                let store = &mut memory_wrap.store;
                return Err(PrepareMemory(
                    store
                        .data_mut()
                        .as_ref()
                        .unwrap_or_else(|| unreachable!("state must be set in Environment::new"))
                        .ext
                        .gas_amount(),
                    e,
                ));
            }
        }
        let mut store = memory_wrap.into_store();

        let needs_execution = entry_point
            .try_into_kind()
            .map(|kind| entries.contains(&kind))
            .unwrap_or(true);

        let res = needs_execution
            .then(|| instance.invoke(&mut store, entry_point.as_entry(), &[]))
            .unwrap_or(Ok(ReturnValue::Unit));

        let gas = instance
            .get_global_val(&store, GLOBAL_NAME_GAS)
            .and_then(runtime::as_i64)
            .ok_or(System(WrongInjectedGas))?;

        let allowance = instance
            .get_global_val(&store, GLOBAL_NAME_ALLOWANCE)
            .and_then(runtime::as_i64)
            .ok_or(System(WrongInjectedAllowance))?;

        let (ext, termination_reason) = store
            .data_mut()
            .take()
            .unwrap_or_else(|| unreachable!("state must be set in Environment::new"))
            .terminate(res, gas, allowance);

        Ok(BackendReport {
            termination_reason,
            memory_wrap: MemoryWrap::new(memory, store),
            ext,
        })
    }
}
