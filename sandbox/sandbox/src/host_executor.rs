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

//! A WASM executor utilizing the sandbox runtime interface of the host.

use crate::{
    env, Error, ReturnValue, SandboxFunction, SandboxFunctionArgs, SandboxFunctionResult,
    SandboxStore, Value, ValueType,
};
use alloc::string::String;
use codec::{Decode, Encode};
use gear_runtime_interface::sandbox;
use gear_sandbox_env::HostError;
use sp_std::{marker::PhantomData, mem, prelude::*, rc::Rc, slice, vec};
use sp_wasm_interface::HostPointer;

impl SandboxFunctionResult for ReturnValue {
    fn result() -> Option<ValueType> {
        // TODO: make as extension trait
        unreachable!("Unused in host executor")
    }

    fn into_return_value(self) -> ReturnValue {
        self
    }
}

pub trait SandboxStoreExt {}

pub struct Store<T>(T);

impl<T> SandboxStore<T> for Store<T> {
    fn data_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T> SandboxStoreExt for Store<T> {}

pub struct Caller<'a, T>(&'a mut T);

impl<T> SandboxStore<T> for Caller<'_, T> {
    fn data_mut(&mut self) -> &mut T {
        self.0
    }
}

impl<T> SandboxStoreExt for Caller<'_, T> {}

struct MemoryHandle {
    memory_idx: u32,
}

impl Drop for MemoryHandle {
    fn drop(&mut self) {
        sandbox::memory_teardown(self.memory_idx);
    }
}

/// The linear memory used by the sandbox.
#[derive(Clone)]
pub struct Memory {
    // Handle to memory instance is wrapped to add reference-counting semantics
    // to `Memory`.
    handle: Rc<MemoryHandle>,
}

impl<T> super::SandboxMemory<T> for Memory {
    fn new(_store: &mut Store<T>, initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
        let maximum = if let Some(maximum) = maximum {
            maximum
        } else {
            env::MEM_UNLIMITED
        };

        match sandbox::memory_new(initial, maximum) {
            env::ERR_MODULE => Err(Error::Module),
            memory_idx => Ok(Memory {
                handle: Rc::new(MemoryHandle { memory_idx }),
            }),
        }
    }

    fn get<S>(&self, _store: &S, offset: u32, buf: &mut [u8]) -> Result<(), Error>
    where
        S: SandboxStore<T>,
    {
        let result = sandbox::memory_get(
            self.handle.memory_idx,
            offset,
            buf.as_mut_ptr(),
            buf.len() as u32,
        );
        match result {
            env::ERR_OK => Ok(()),
            env::ERR_OUT_OF_BOUNDS => Err(Error::OutOfBounds),
            _ => unreachable!(),
        }
    }

    fn set<S>(&self, _store: &mut S, offset: u32, val: &[u8]) -> Result<(), Error>
    where
        S: SandboxStore<T>,
    {
        let result = sandbox::memory_set(
            self.handle.memory_idx,
            offset,
            val.as_ptr() as _,
            val.len() as u32,
        );
        match result {
            env::ERR_OK => Ok(()),
            env::ERR_OUT_OF_BOUNDS => Err(Error::OutOfBounds),
            _ => unreachable!(),
        }
    }

    fn grow<S>(&self, store: &mut S, pages: u32) -> Result<u32, Error>
    where
        S: SandboxStore<T>,
    {
        let size = self.size(store);
        sandbox::memory_grow(self.handle.memory_idx, pages);
        Ok(size)
    }

    fn size<S>(&self, _store: &S) -> u32
    where
        S: SandboxStore<T>,
    {
        sandbox::memory_size(self.handle.memory_idx)
    }

    unsafe fn get_buff<S>(&self, _store: &mut S) -> HostPointer
    where
        S: SandboxStore<T>,
    {
        sandbox::get_buff(self.handle.memory_idx)
    }
}

type BoxedSandboxFunction<T> =
    Box<dyn for<'a> SandboxFunction<Caller<'a, T>, &'a [Value], ReturnValue, T>>;

/// A builder for the environment of the sandboxed WASM module.
pub struct EnvironmentDefinitionBuilder<T> {
    env_def: env::EnvironmentDefinition,
    funcs: Vec<BoxedSandboxFunction<T>>,
    retained_memories: Vec<Memory>,
}

impl<T> EnvironmentDefinitionBuilder<T> {
    fn add_entry<N1, N2>(&mut self, module: N1, field: N2, extern_entity: env::ExternEntity)
    where
        N1: Into<String>,
        N2: Into<String>,
    {
        let entry = env::Entry {
            module_name: module.into(),
            field_name: field.into(),
            entity: extern_entity,
        };
        self.env_def.entries.push(entry);
    }
}

impl<T> super::SandboxEnvironmentBuilder<T, Memory> for EnvironmentDefinitionBuilder<T> {
    fn new() -> Self {
        Self {
            env_def: env::EnvironmentDefinition {
                entries: Vec::new(),
            },
            funcs: Vec::new(),
            retained_memories: Vec::new(),
        }
    }

    fn add_host_func<N1, N2, F, Args, R>(
        &mut self,
        _store: &mut Store<T>,
        module: N1,
        field: N2,
        f: F,
    ) where
        N1: Into<String>,
        N2: Into<String>,
        F: for<'a> SandboxFunction<Caller<'a, T>, Args, R, T> + Send + Sync + 'static,
        Args: SandboxFunctionArgs + 'static,
        R: SandboxFunctionResult + 'static,
    {
        struct Converter<F, Args, R> {
            f: F,
            _args: PhantomData<Args>,
            _r: PhantomData<R>,
        }

        impl<F, State, Args, R> SandboxFunction<Caller<'_, State>, &[Value], ReturnValue, State>
            for Converter<F, Args, R>
        where
            F: for<'a> SandboxFunction<Caller<'a, State>, Args, R, State>,
            R: SandboxFunctionResult + 'static,
        {
            fn call(
                &self,
                store: Caller<'_, State>,
                args: &[Value],
            ) -> Result<ReturnValue, HostError> {
                self.f.call(store, args).map(R::into_return_value)
            }
        }

        let f = Box::new(Converter {
            f,
            _args: PhantomData,
            _r: PhantomData,
        }) as BoxedSandboxFunction<T>;
        self.funcs.push(f);
        let f = self.funcs.last().expect("infallible") as *const BoxedSandboxFunction<T>;
        let f = env::ExternEntity::Function(f as u32);
        self.add_entry(module, field, f);
    }

    fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
    where
        N1: Into<String>,
        N2: Into<String>,
    {
        // We need to retain memory to keep it alive while the EnvironmentDefinitionBuilder alive.
        self.retained_memories.push(mem.clone());

        let mem = env::ExternEntity::Memory(mem.handle.memory_idx);
        self.add_entry(module, field, mem);
    }
}

/// Sandboxed instance of a WASM module.
pub struct Instance<T> {
    instance_idx: u32,
    _retained_memories: Vec<Memory>,
    _funcs: Vec<BoxedSandboxFunction<T>>,
}

#[derive(Clone, Default)]
pub struct InstanceGlobals {
    instance_idx: Option<u32>,
}

impl super::InstanceGlobals for InstanceGlobals {
    fn get_global_val(&self, name: &str) -> Option<Value> {
        self.instance_idx
            .and_then(|i| sandbox::get_global_val(i, name))
    }

    fn set_global_val(&self, name: &str, value: Value) -> Result<(), super::GlobalsSetError> {
        match self.instance_idx {
            None => Err(super::GlobalsSetError::Other),
            Some(i) => match sandbox::set_global_val(i, name, value) {
                env::ERROR_GLOBALS_OK => Ok(()),
                env::ERROR_GLOBALS_NOT_FOUND => Err(super::GlobalsSetError::NotFound),
                _ => Err(super::GlobalsSetError::Other),
            },
        }
    }
}

/// The primary responsibility of this thunk is to deserialize arguments and
/// call the original function, specified by the index.
extern "C" fn dispatch_thunk<T>(
    serialized_args_ptr: *const u8,
    serialized_args_len: usize,
    state: usize,
    f: usize,
) -> u64 {
    let serialized_args = unsafe {
        if serialized_args_len == 0 {
            &[]
        } else {
            slice::from_raw_parts(serialized_args_ptr, serialized_args_len)
        }
    };
    let args = Vec::<Value>::decode(&mut &serialized_args[..]).expect(
        "serialized args should be provided by the runtime;
			correctly serialized data should be deserializable;
			qed",
    );

    unsafe {
        // This should be safe since `coerce_host_index_to_func` is called with an argument
        // received in an `dispatch_thunk` implementation, so `f` should point
        // on a valid host function.
        let f = f as *const BoxedSandboxFunction<T>;
        let f = f.as_ref().expect("infallible");

        // This should be safe since mutable reference to T is passed upon the invocation.
        let state = &mut *(state as *mut T);

        // Pass control flow to the designated function.
        let result = f.call(Caller(state), &args).encode();

        // Leak the result vector and return the pointer to return data.
        let result_ptr = result.as_ptr() as u64;
        let result_len = result.len() as u64;
        mem::forget(result);

        (result_ptr << 32) | result_len
    }
}

impl<T> super::SandboxInstance for Instance<T> {
    type State = T;
    type Memory = Memory;
    type EnvironmentBuilder = EnvironmentDefinitionBuilder<T>;
    type InstanceGlobals = InstanceGlobals;

    fn new(
        store: &mut Store<Self::State>,
        code: &[u8],
        env_def_builder: EnvironmentDefinitionBuilder<T>,
    ) -> Result<Instance<T>, Error> {
        let serialized_env_def: Vec<u8> = env_def_builder.env_def.encode();
        // It's very important to instantiate thunk with the right type.
        let dispatch_thunk = dispatch_thunk::<T>;
        let result = sandbox::instantiate(
            dispatch_thunk as usize as u32,
            code,
            &serialized_env_def,
            store.data_mut() as *const T as _,
        );

        let instance_idx = match result {
            env::ERR_MODULE => return Err(Error::Module),
            env::ERR_EXECUTION => return Err(Error::Execution),
            instance_idx => instance_idx,
        };

        // We need to retain memories to keep them alive while the Instance is alive.
        let retained_memories = env_def_builder.retained_memories;
        // Keep funcs allocated so `dispatch_thunk` access correct memory.
        let funcs = env_def_builder.funcs;
        Ok(Instance {
            instance_idx,
            _retained_memories: retained_memories,
            _funcs: funcs,
        })
    }

    fn invoke(
        &mut self,
        store: &mut Store<T>,
        name: &str,
        args: &[Value],
    ) -> Result<ReturnValue, Error> {
        let serialized_args = args.to_vec().encode();
        let mut return_val = vec![0u8; ReturnValue::ENCODED_MAX_SIZE];

        let result = sandbox::invoke(
            self.instance_idx,
            name,
            &serialized_args,
            return_val.as_mut_ptr() as _,
            return_val.len() as u32,
            store.data_mut() as *const T as _,
        );

        match result {
            env::ERR_OK => {
                let return_val =
                    ReturnValue::decode(&mut &return_val[..]).map_err(|_| Error::Execution)?;
                Ok(return_val)
            }
            env::ERR_EXECUTION => Err(Error::Execution),
            _ => unreachable!(),
        }
    }

    fn get_global_val(&self, _store: &Store<T>, name: &str) -> Option<Value> {
        sandbox::get_global_val(self.instance_idx, name)
    }

    fn instance_globals(&self) -> Option<Self::InstanceGlobals> {
        Some(InstanceGlobals {
            instance_idx: Some(self.instance_idx),
        })
    }

    fn get_instance_ptr(&self) -> HostPointer {
        sandbox::get_instance_ptr(self.instance_idx)
    }
}

impl<T> Drop for Instance<T> {
    fn drop(&mut self) {
        sandbox::instance_teardown(self.instance_idx);
    }
}
