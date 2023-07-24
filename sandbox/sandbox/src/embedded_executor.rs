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

//! An embedded WASM executor utilizing `wasmi`.

use alloc::string::String;
use std::marker::PhantomData;

use sp_wasm_interface::HostPointer;
use wasmi::{
    AsContext, AsContextMut, Engine, Func, FuncType, Linker, MemoryType, Module, StoreContext,
    StoreContextMut,
};

use sp_std::{collections::btree_map::BTreeMap, prelude::*};
use wasmi::{
    core::{Pages, Trap, ValueType as RuntimeValueType},
    Value as RuntimeValue,
};

use crate::{
    Error, HostError, ReturnValue, SandboxFunction, SandboxFunctionArgs, SandboxFunctionResult,
    SandboxStore, Value, ValueType,
};

pub trait SandboxStoreExt: AsContext + AsContextMut {}

pub struct Store<T>(wasmi::Store<T>);

impl<T> Store<T> {
    pub fn new(data: T) -> Self {
        let engine = Engine::default();
        let store = wasmi::Store::new(&engine, data);
        Self(store)
    }

    fn engine(&self) -> &Engine {
        self.0.engine()
    }
}

impl<T> SandboxStore<T> for Store<T> {
    fn data_mut(&mut self) -> &mut T {
        self.0.data_mut()
    }
}

impl<T> SandboxStoreExt for Store<T> {}

impl<T> AsContext for Store<T> {
    type UserState = T;

    fn as_context(&self) -> StoreContext<Self::UserState> {
        self.0.as_context()
    }
}

impl<T> AsContextMut for Store<T> {
    fn as_context_mut(&mut self) -> StoreContextMut<Self::UserState> {
        self.0.as_context_mut()
    }
}

pub struct Caller<'a, T>(wasmi::Caller<'a, T>);

impl<'a, T> Caller<'a, T> {
    pub fn set_global_val(&mut self, name: &str, value: Value) -> Option<()> {
        let global = self.0.get_export(name)?.into_global()?;
        global.set(&mut self.0, to_wasmi(value)).ok()?;
        Some(())
    }

    pub fn get_global_val(&mut self, name: &str) -> Option<Value> {
        let value = self.0.get_export(name)?.into_global()?.get(&self.0);
        Some(to_interface(value))
    }
}

impl<T> SandboxStore<T> for Caller<'_, T> {
    fn data_mut(&mut self) -> &mut T {
        self.0.data_mut()
    }
}

impl<T> SandboxStoreExt for Caller<'_, T> {}

impl<T> AsContext for Caller<'_, T> {
    type UserState = T;

    fn as_context(&self) -> StoreContext<Self::UserState> {
        self.0.as_context()
    }
}

impl<T> AsContextMut for Caller<'_, T> {
    fn as_context_mut(&mut self) -> StoreContextMut<Self::UserState> {
        self.0.as_context_mut()
    }
}

/// The linear memory used by the sandbox.
#[derive(Clone)]
pub struct Memory {
    memref: wasmi::Memory,
}

impl<T> super::SandboxMemory<T> for Memory {
    fn new(store: &mut Store<T>, initial: u32, maximum: Option<u32>) -> Result<Memory, Error> {
        let ty = MemoryType::new(initial, maximum).map_err(|_| Error::Module)?;
        let memref = wasmi::Memory::new(store, ty).map_err(|_| Error::Module)?;
        Ok(Memory { memref })
    }

    fn get<S>(&self, store: &S, ptr: u32, buf: &mut [u8]) -> Result<(), Error>
    where
        S: SandboxStore<T>,
    {
        let data = self
            .memref
            .data(store)
            .get((ptr as usize)..(ptr as usize + buf.len()))
            .ok_or(Error::OutOfBounds)?;
        buf[..].copy_from_slice(data);
        Ok(())
    }

    fn set<S>(&self, store: &mut S, ptr: u32, value: &[u8]) -> Result<(), Error>
    where
        S: SandboxStore<T>,
    {
        let data = self
            .memref
            .data_mut(store)
            .get_mut((ptr as usize)..(ptr as usize + value.len()))
            .ok_or(Error::OutOfBounds)?;
        data[..].copy_from_slice(value);
        Ok(())
    }

    fn grow<S>(&self, store: &mut S, pages: u32) -> Result<u32, Error>
    where
        S: SandboxStore<T>,
    {
        let pages = Pages::new(pages).ok_or(Error::MemoryGrow)?;
        self.memref
            .grow(store, pages)
            .map(Into::into)
            .map_err(|_| Error::MemoryGrow)
    }

    fn size<S>(&self, store: &S) -> u32
    where
        S: SandboxStore<T>,
    {
        self.memref.current_pages(store).into()
    }

    unsafe fn get_buff<S>(&self, store: &mut S) -> u64
    where
        S: SandboxStore<T>,
    {
        self.memref.data_mut(store).as_mut_ptr() as usize as u64
    }
}

enum ExternVal {
    HostFunc(Func),
    Memory(wasmi::Memory),
}

/// A builder for the environment of the sandboxed WASM module.
pub struct EnvironmentDefinitionBuilder {
    externs: BTreeMap<(String, String), ExternVal>,
}

impl super::SandboxEnvironmentBuilder<Memory> for EnvironmentDefinitionBuilder {
    fn new() -> Self {
        Self {
            externs: BTreeMap::new(),
        }
    }

    fn add_host_func<N1, N2, F, Args, R, State>(
        &mut self,
        store: &mut Store<State>,
        module: N1,
        field: N2,
        f: F,
    ) where
        N1: Into<String>,
        N2: Into<String>,
        F: for<'a> SandboxFunction<Caller<'a, State>, Args, R, State> + Send + Sync + 'static,
        Args: SandboxFunctionArgs,
        R: SandboxFunctionResult,
    {
        let params = Args::params().iter().copied().map(to_wasmi_type);
        let result = R::result().map(to_wasmi_type);
        let ty = FuncType::new(params, result);
        let func = Func::new(store, ty, move |caller, args, results| {
            let args: Vec<Value> = args.iter().cloned().map(to_interface).collect();
            let value = f
                .call(Caller(caller), &args)
                .map(R::into_return_value)
                .map_err(|HostError| Trap::new("Error calling host function"))?;
            match value {
                ReturnValue::Unit => Ok(()),
                ReturnValue::Value(value) => {
                    results[0] = to_wasmi(value);
                    Ok(())
                }
            }
        });

        self.externs
            .insert((module.into(), field.into()), ExternVal::HostFunc(func));
    }

    fn add_memory<N1, N2>(&mut self, module: N1, field: N2, mem: Memory)
    where
        N1: Into<String>,
        N2: Into<String>,
    {
        self.externs
            .insert((module.into(), field.into()), ExternVal::Memory(mem.memref));
    }
}

/// Sandboxed instance of a WASM module.
pub struct Instance<T> {
    instance: wasmi::Instance,
    _state: PhantomData<T>,
}

/// Unit-type as InstanceGlobals for wasmi executor.
pub struct InstanceGlobals(());

impl super::InstanceGlobals for InstanceGlobals {
    fn get_global_val(&self, _name: &str) -> Option<Value> {
        None
    }

    fn set_global_val(&self, _name: &str, _value: Value) -> Result<(), super::GlobalsSetError> {
        Err(super::GlobalsSetError::NotFound)
    }
}

impl<T> super::SandboxInstance for Instance<T> {
    type State = T;
    type Memory = Memory;
    type EnvironmentBuilder = EnvironmentDefinitionBuilder;
    type InstanceGlobals = InstanceGlobals;

    fn new(
        mut store: &mut Store<T>,
        code: &[u8],
        env_def_builder: EnvironmentDefinitionBuilder,
    ) -> Result<Self, Error> {
        let EnvironmentDefinitionBuilder { externs } = env_def_builder;

        let module = Module::new(store.engine(), code).map_err(|_| Error::Module)?;

        let mut linker = Linker::new(store.engine());
        for ((module, name), item) in externs {
            let item = match item {
                ExternVal::HostFunc(func) => wasmi::Extern::Func(func),
                ExternVal::Memory(mem) => wasmi::Extern::Memory(mem),
            };
            linker
                .define(&module, &name, item)
                .map_err(|_| Error::Module)?;
        }

        let instance_pre = linker
            .instantiate(&mut store, &module)
            .map_err(|_| Error::Module)?;
        let instance = instance_pre.start(&mut store).map_err(|_| Error::Module)?;

        Ok(Instance {
            instance,
            _state: PhantomData,
        })
    }

    fn invoke(
        &mut self,
        mut store: &mut Store<Self::State>,
        name: &str,
        args: &[Value],
    ) -> Result<ReturnValue, Error> {
        let args = args.iter().cloned().map(to_wasmi).collect::<Vec<_>>();

        let func = self
            .instance
            .get_func(&store, name)
            .ok_or(Error::Execution)?;

        let results = func.ty(&store).results().len();
        let mut results = vec![RuntimeValue::I32(0xBAAAAAD); results];
        func.call(&mut store, &args, &mut results)
            .map_err(|_| Error::Execution)?;

        match results.as_slice() {
            [] => Ok(ReturnValue::Unit),
            [val] => Ok(ReturnValue::Value(to_interface(val.clone()))),
            _ => Err(Error::Execution),
        }
    }

    fn get_global_val(&self, store: &Store<Self::State>, name: &str) -> Option<Value> {
        let global = self.instance.get_global(store, name)?.get(store);

        Some(to_interface(global))
    }

    fn instance_globals(&self) -> Option<Self::InstanceGlobals> {
        None
    }

    fn get_instance_ptr(&self) -> HostPointer {
        unreachable!("Must not be called for embedded executor")
    }
}

/// Convert the substrate value type to the wasmi value type.
fn to_wasmi(value: Value) -> RuntimeValue {
    match value {
        Value::I32(val) => RuntimeValue::I32(val),
        Value::I64(val) => RuntimeValue::I64(val),
        Value::F32(val) => RuntimeValue::F32(val.into()),
        Value::F64(val) => RuntimeValue::F64(val.into()),
    }
}

fn to_wasmi_type(kind: ValueType) -> RuntimeValueType {
    match kind {
        ValueType::I32 => RuntimeValueType::I32,
        ValueType::I64 => RuntimeValueType::I64,
        ValueType::F32 => RuntimeValueType::F32,
        ValueType::F64 => RuntimeValueType::F64,
    }
}

/// Convert the wasmi value type to the substrate value type.
fn to_interface(value: RuntimeValue) -> Value {
    match value {
        RuntimeValue::I32(val) => Value::I32(val),
        RuntimeValue::I64(val) => Value::I64(val),
        RuntimeValue::F32(val) => Value::F32(val.into()),
        RuntimeValue::F64(val) => Value::F64(val.into()),
        RuntimeValue::FuncRef(_) | RuntimeValue::ExternRef(_) => todo!(),
    }
}

#[cfg(test)]
mod tests {
    use super::{EnvironmentDefinitionBuilder, Instance};
    use crate::{
        default_executor::{Caller, Store},
        Error, HostError, ReturnValue, SandboxEnvironmentBuilder, SandboxInstance, SandboxStore,
        Value,
    };

    fn execute_sandboxed(code: &[u8], args: &[Value]) -> Result<ReturnValue, Error> {
        struct State {
            counter: u32,
        }

        fn env_assert(_caller: Caller<'_, State>, condition: i32) -> Result<(), HostError> {
            if condition != 0 {
                Ok(())
            } else {
                Err(HostError)
            }
        }

        fn env_inc_counter(mut caller: Caller<'_, State>, inc_by: i32) -> Result<u32, HostError> {
            let data = caller.data_mut();
            data.counter += inc_by as u32;
            Ok(data.counter)
        }

        let state = State { counter: 0 };
        let mut store = Store::new(state);

        let mut env_builder = EnvironmentDefinitionBuilder::new();
        env_builder.add_host_func(&mut store, "env", "assert", env_assert);
        env_builder.add_host_func(&mut store, "env", "inc_counter", env_inc_counter);

        let mut instance = Instance::new(&mut store, code, env_builder)?;
        instance.invoke(&mut store, "call", args)
    }

    #[test]
    fn invoke_args() {
        let code = wat::parse_str(
            r#"
		(module
			(import "env" "assert" (func $assert (param i32)))

			(func (export "call") (param $x i32) (param $y i64)
				;; assert that $x = 0x12345678
				(call $assert
					(i32.eq
						(get_local $x)
						(i32.const 0x12345678)
					)
				)

				(call $assert
					(i64.eq
						(get_local $y)
						(i64.const 0x1234567887654321)
					)
				)
			)
		)
		"#,
        )
        .unwrap();

        let result = execute_sandboxed(
            &code,
            &[Value::I32(0x12345678), Value::I64(0x1234567887654321)],
        );
        assert!(result.is_ok());
    }

    #[test]
    fn return_value() {
        let code = wat::parse_str(
            r#"
		(module
			(func (export "call") (param $x i32) (result i32)
				(i32.add
					(get_local $x)
					(i32.const 1)
				)
			)
		)
		"#,
        )
        .unwrap();

        let return_val = execute_sandboxed(&code, &[Value::I32(0x1336)]).unwrap();
        assert_eq!(return_val, ReturnValue::Value(Value::I32(0x1337)));
    }

    #[test]
    fn inc_counter() {
        let code = wat::parse_str(
            r#"
        (module
            (import "env" "assert" (func $assert (param i32)))
            (import "env" "inc_counter" (func $inc_counter (param i32) (result i32)))
        
            (func (export "call")
                i32.const 15
                call $inc_counter
                call $assert
            )
        )
        "#,
        )
        .unwrap();

        execute_sandboxed(&code, &[]).unwrap();
    }
}
