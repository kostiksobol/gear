// This file is part of Gear.

// Copyright (C) Gear Technologies Inc.
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

//! This crate provides means to instantiate and execute wasm modules.
//!
//! It works even when the user of this library executes from
//! inside the wasm VM. In this case the same VM is used for execution
//! of both the sandbox owner and the sandboxed module, without compromising security
//! and without the performance penalty of full wasm emulation inside wasm.
//!
//! This is achieved by using bindings to the wasm VM, which are published by the host API.
//! This API is thin and consists of only a handful functions. It contains functions for
//! instantiating modules and executing them, but doesn't contain functions for inspecting the
//! module structure. The user of this library is supposed to read the wasm module.
//!
//! When this crate is used in the `std` environment all these functions are implemented by directly
//! calling the wasm VM.
//!
//! Examples of possible use-cases for this library are not limited to the following:
//!
//! - implementing smart-contract runtimes that use wasm for contract code
//! - executing a wasm substrate runtime inside of a wasm parachain

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

pub mod embedded_executor;
pub use gear_sandbox_env as env;
#[cfg(not(feature = "std"))]
pub mod host_executor;

use sp_core::RuntimeDebug;
use sp_std::prelude::*;

use sp_wasm_interface::HostPointer;
pub use sp_wasm_interface::{ReturnValue, Value, ValueType};

#[cfg(not(all(feature = "host-sandbox", not(feature = "std"))))]
pub use self::embedded_executor as default_executor;
pub use self::env::HostError;
#[cfg(all(feature = "host-sandbox", not(feature = "std")))]
pub use self::host_executor as default_executor;

/// The target used for logging.
const TARGET: &str = "runtime::sandbox";

/// Error that can occur while using this crate.
#[derive(RuntimeDebug)]
pub enum Error {
    /// Module is not valid, couldn't be instantiated.
    Module,

    /// Access to a memory or table was made with an address or an index which is out of bounds.
    ///
    /// Note that if wasm module makes an out-of-bounds access then trap will occur.
    OutOfBounds,

    /// Trying to grow memory by more than maximum limit.
    MemoryGrow,

    /// Failed to invoke the start function or an exported function for some reason.
    Execution,
}

impl From<Error> for HostError {
    fn from(_e: Error) -> HostError {
        HostError
    }
}

/// Function pointer for specifying functions by the
/// supervisor in [`EnvironmentDefinitionBuilder`].
///
/// [`EnvironmentDefinitionBuilder`]: struct.EnvironmentDefinitionBuilder.html
pub type HostFuncType<T> = fn(&mut T, &[Value]) -> Result<ReturnValue, HostError>;

pub trait SandboxStore<T> {
    fn data_mut(&mut self) -> &mut T;
}

/// Reference to a sandboxed linear memory, that
/// will be used by the guest module.
///
/// The memory can't be directly accessed by supervisor, but only
/// through designated functions [`get`](SandboxMemory::get) and [`set`](SandboxMemory::set).
pub trait SandboxMemory<T>: Sized + Clone {
    type Store<'a>: SandboxStore<T>
    where
        T: 'a;

    /// Read a memory area at the address `ptr` with the size of the provided slice `buf`.
    ///
    /// Returns `Err` if the range is out-of-bounds.
    fn get(&self, store: &Self::Store<'_>, ptr: u32, buf: &mut [u8]) -> Result<(), Error>;

    /// Write a memory area at the address `ptr` with contents of the provided slice `buf`.
    ///
    /// Returns `Err` if the range is out-of-bounds.
    fn set(&self, store: &mut Self::Store<'_>, ptr: u32, value: &[u8]) -> Result<(), Error>;

    /// Grow memory with provided number of pages.
    ///
    /// Returns `Err` if attempted to allocate more memory than permitted by the limit.
    fn grow(&self, store: &mut Self::Store<'_>, pages: u32) -> Result<u32, Error>;

    /// Returns current memory size.
    ///
    /// Maximum memory size cannot exceed 65536 pages or 4GiB.
    fn size(&self, store: &Self::Store<'_>) -> u32;

    /// Returns pointer to the begin of wasm mem buffer
    /// # Safety
    /// Pointer is intended to use by `mprotect` function.
    unsafe fn get_buff(&self, store: &mut Self::Store<'_>) -> HostPointer;
}

pub trait SandboxFunctionArg: Sized {
    const VALUE_TYPE: ValueType;

    fn from_value(value: Value) -> Result<Self, HostError>;
}

impl SandboxFunctionArg for i32 {
    const VALUE_TYPE: ValueType = ValueType::I32;

    fn from_value(value: Value) -> Result<Self, HostError> {
        // TODO: print error
        value.as_i32().ok_or(HostError)
    }
}

impl SandboxFunctionArg for u32 {
    const VALUE_TYPE: ValueType = ValueType::I32;

    fn from_value(value: Value) -> Result<Self, HostError> {
        value.as_i32().map(|x| x as u32).ok_or(HostError)
    }
}

pub trait SandboxFunctionArgs {
    fn params() -> &'static [ValueType];
}

impl SandboxFunctionArgs for () {
    fn params() -> &'static [ValueType] {
        &[]
    }
}

impl<T> SandboxFunctionArgs for (T,)
where
    T: SandboxFunctionArg,
{
    fn params() -> &'static [ValueType] {
        &[T::VALUE_TYPE]
    }
}

pub trait SandboxFunctionResult {
    fn result() -> Option<ValueType>;

    fn into_return_value(self) -> ReturnValue;
}

impl SandboxFunctionResult for () {
    fn result() -> Option<ValueType> {
        None
    }

    fn into_return_value(self) -> ReturnValue {
        ReturnValue::Unit
    }
}

impl SandboxFunctionResult for i32 {
    fn result() -> Option<ValueType> {
        Some(ValueType::I32)
    }

    fn into_return_value(self) -> ReturnValue {
        ReturnValue::Value(Value::I32(self))
    }
}

impl SandboxFunctionResult for u32 {
    fn result() -> Option<ValueType> {
        Some(ValueType::I32)
    }

    fn into_return_value(self) -> ReturnValue {
        ReturnValue::Value(Value::I32(self as i32))
    }
}

pub trait SandboxFunction<Store, Args, R, Data> {
    fn call(&self, store: Store, args: &[Value]) -> Result<R, HostError>;
}

impl<S, F, R, D> SandboxFunction<S, (), R, D> for F
where
    F: Fn(S) -> Result<R, HostError>,
    S: SandboxStore<D>,
    R: SandboxFunctionResult,
{
    fn call(&self, store: S, args: &[Value]) -> Result<R, HostError> {
        let _args: [Value; 0] = args.try_into().unwrap(); // TODO
        (self)(store)
    }
}

impl<S, A, F, R, D> SandboxFunction<S, (A,), R, D> for F
where
    F: Fn(S, A) -> Result<R, HostError>,
    S: SandboxStore<D>,
    A: SandboxFunctionArg,
    R: SandboxFunctionResult,
{
    fn call(&self, store: S, args: &[Value]) -> Result<R, HostError> {
        let args: [Value; 1] = args.try_into().unwrap(); // TODO
        let [a] = args;
        let a = A::from_value(a)?;
        (self)(store, a)
    }
}

/// Struct that can be used for defining an environment for a sandboxed module.
///
/// The sandboxed module can access only the entities which were defined and passed
/// to the module at the instantiation time.
pub trait SandboxEnvironmentBuilder<State, Memory>: Sized {
    type Caller<'a>: SandboxStore<State>
    where
        State: 'a;

    /// Construct a new `EnvironmentDefinitionBuilder`.
    fn new(state: State) -> Self;

    /// Construct a new linear memory instance.
    ///
    /// The memory allocated with initial number of pages specified by `initial`.
    /// Minimal possible value for `initial` is 0 and maximum possible is `65536`.
    /// (Since maximum addressable memory is 2<sup>32</sup> = 4GiB = 65536 * 64KiB).
    ///
    /// It is possible to limit maximum number of pages this memory instance can have by specifying
    /// `maximum`. If not specified, this memory instance would be able to allocate up to 4GiB.
    ///
    /// Allocated memory is always zeroed.
    fn create_memory(&mut self, initial: u32, maximum: Option<u32>) -> Result<Memory, Error>;

    /// Register a host function in this environment definition.
    ///
    /// NOTE that there is no constraints on type of this function. An instance
    /// can import function passed here with any signature it wants. It can even import
    /// the same function (i.e. with same `module` and `field`) several times. It's up to
    /// the user code to check or constrain the types of signatures.
    fn add_host_func<N1, N2, F, Args, R>(&mut self, module: N1, field: N2, f: F)
    where
        N1: Into<String>,
        N2: Into<String>,
        F: for<'a> SandboxFunction<Self::Caller<'a>, Args, R, State> + Send + Sync + 'static,
        Args: SandboxFunctionArgs,
        R: SandboxFunctionResult;

    /// Register a memory in this environment definition.
    fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
    where
        N1: Into<String>,
        N2: Into<String>;
}

/// Sandboxed instance of a wasm module.
///
/// This instance can be used for invoking exported functions.
pub trait SandboxInstance: Sized {
    type State;

    /// The memory type used for this sandbox.
    type Memory: SandboxMemory<Self::State>;

    /// The environment builder used to construct this sandbox.
    type EnvironmentBuilder: SandboxEnvironmentBuilder<Self::State, Self::Memory>;

    /// The globals type used for this sandbox to change globals.
    type InstanceGlobals: InstanceGlobals;

    /// Instantiate a module with the given [`EnvironmentDefinitionBuilder`]. It will
    /// run the `start` function (if it is present in the module) with the given `state`.
    ///
    /// Returns `Err(Error::Module)` if this module can't be instantiated with the given
    /// environment. If execution of `start` function generated a trap, then `Err(Error::Execution)`
    /// will be returned.
    ///
    /// [`EnvironmentDefinitionBuilder`]: struct.EnvironmentDefinitionBuilder.html
    fn new(code: &[u8], env_def_builder: Self::EnvironmentBuilder) -> Result<Self, Error>;

    /// Invoke an exported function with the given name.
    ///
    /// # Errors
    ///
    /// Returns `Err(Error::Execution)` if:
    ///
    /// - An export function name isn't a proper utf8 byte sequence,
    /// - This module doesn't have an exported function with the given name,
    /// - If types of the arguments passed to the function doesn't match function signature then
    ///   trap occurs (as if the exported function was called via call_indirect),
    /// - Trap occurred at the execution time.
    fn invoke(&mut self, name: &str, args: &[Value]) -> Result<ReturnValue, Error>;

    /// Get the value from a global with the given `name`.
    ///
    /// Returns `Some(_)` if the global could be found.
    fn get_global_val(&self, name: &str) -> Option<Value>;

    /// Get the instance providing access to exported globals.
    ///
    /// Returns `None` if the executor doesn't support the interface.
    fn instance_globals(&self) -> Option<Self::InstanceGlobals>;

    /// Get raw pointer to the executor host sandbox instance.
    fn get_instance_ptr(&self) -> HostPointer;
}

/// Error that can occur while using this crate.
#[derive(RuntimeDebug)]
pub enum GlobalsSetError {
    /// A global variable is not found.
    NotFound,

    /// A global variable is immutable or has a different type.
    Other,
}

/// This instance can be used for changing exported globals.
pub trait InstanceGlobals: Sized {
    /// Get the value from a global with the given `name`.
    ///
    /// Returns `Some(_)` if the global could be found.
    fn get_global_val(&self, name: &str) -> Option<Value>;

    /// Set the value of a global with the given `name`.
    fn set_global_val(&self, name: &str, value: Value) -> Result<(), GlobalsSetError>;
}
