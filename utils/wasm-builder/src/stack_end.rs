// This file is part of Gear.

// Copyright (C) 2022-2023 Gear Technologies Inc.
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

use gear_wasm_instrument::STACK_END_EXPORT_NAME;
use gsys::stack_buffer::{GET_STACK_BUFFER_GLOBAL_NAME, SET_STACK_BUFFER_GLOBAL_NAME};
use pwasm_utils::parity_wasm::{
    builder,
    elements::{ExportEntry, External, Instruction, Internal, Module, ValueType},
};

const STACK_POINTER_GLOBAL_SUFFIX: &str = "__stack_pointer";

fn get_global_index(module_bytes: &[u8], name_predicate: impl Fn(&str) -> bool) -> Option<u32> {
    use wasmparser::{Name, NameSectionReader, Parser, Payload::*};

    // Search for `names` section in custom sections.
    let names_section = Parser::new(0)
        .parse_all(module_bytes)
        .filter_map(|p| p.ok())
        .find_map(|section| {
            if let CustomSection(custom_section) = section {
                if custom_section.name() == "name" {
                    Some(custom_section)
                } else {
                    None
                }
            } else {
                None
            }
        })?;

    // In all global names sub-sections search for global, which suits `name_predicate`.
    NameSectionReader::new(names_section.data(), names_section.data_offset())
        .filter_map(|name| match name {
            Ok(Name::Global(global_names)) => Some(global_names),
            _ => None,
        })
        .find_map(|global_names| {
            global_names
                .into_iter()
                .filter_map(|item| item.ok())
                .find(|naming| name_predicate(naming.name))
        })
        .map(|naming| naming.index)
}

/// Insert the export with the stack end address in `module` if there is
/// the global '__stack_pointer'.
/// By default rust compilation into wasm creates global '__stack_pointer', which
/// initialized by the end of stack address. Unfortunately this global is not an export.
///
/// This export can be used in runtime to identify the end of stack memory
/// and skip its uploading to the storage.
pub fn insert_stack_end_export(
    module_bytes: &[u8],
    module: &mut Module,
    sub_offset: u32,
) -> Result<u32, &'static str> {
    let mut stack_pointer_index = get_global_index(module_bytes, |name| {
        name.ends_with(STACK_POINTER_GLOBAL_SUFFIX)
    });

    if let Some(export_section) = module.export_section_mut() {
        let exports = export_section.entries_mut();
        if let Some(index) = exports
            .iter()
            .position(|e| e.field() == gsys::STACK_POINTER_GLOBAL_LABEL_NAME)
        {
            if stack_pointer_index.is_none() {
                // In case we do not find stack_pointer global in names section,
                // then we suppose that index is 0, due to this special export exists.
                stack_pointer_index = Some(0);
            }
            // Remove stack pointer global label if there is one.
            exports.remove(index);
        }
    };

    let stack_pointer_index = stack_pointer_index.ok_or("Cannot find stack pointer global")?;

    let glob_section = module
        .global_section_mut()
        .ok_or("Cannot find globals section")?;
    let global = glob_section
        .entries()
        .iter()
        .nth(stack_pointer_index as usize)
        .ok_or("there is no globals")?
        .clone();
    if global.global_type().content_type() != ValueType::I32 {
        return Err("has no i32 global 0");
    }

    let init_code = global.init_expr().code();
    if init_code.len() != 2 {
        return Err("num of init instructions != 2 for glob 0");
    }

    if init_code[1] != Instruction::End {
        return Err("second init instruction is not end");
    }

    let stack_end_offset = if let Instruction::I32Const(literal) = init_code[0] {
        log::debug!("stack pointer init == {:#x}", literal);
        glob_section.entries_mut().push(global);
        let index = glob_section.entries().len() as u32 - 1;
        let export_section = module
            .export_section_mut()
            .ok_or("Cannot find export section")?;
        export_section.entries_mut().push(ExportEntry::new(
            STACK_END_EXPORT_NAME.to_string(),
            Internal::Global(index),
        ));
        literal
    } else {
        return Err("has unexpected instr for init");
    };

    let stack_pointer_new_offset = (stack_end_offset as u32)
        .checked_sub(sub_offset)
        .ok_or("sub offset is greater than stack end offset")?;

    // +_+_+
    *module
        .global_section_mut()
        .unwrap()
        .entries_mut()
        .iter_mut()
        .nth(stack_pointer_index as usize)
        .unwrap()
        .init_expr_mut()
        .code_mut()
        .get_mut(0)
        .unwrap() = Instruction::I32Const(stack_pointer_new_offset as i32);

    Ok(stack_pointer_new_offset)
}

pub fn get_stack_buffer_export_indexes(module: &Module) -> (Option<u32>, Option<u32>) {
    let import_entries = if let Some(import_section) = module.import_section() {
        import_section.entries()
    } else {
        return (None, None);
    };

    let mut get_stack_buffer_index = None;
    let mut set_stack_buffer_index = None;
    let mut index = 0;
    for entry in import_entries.iter() {
        log::debug!("entry: {:?}", entry);
        match (entry.module(), entry.field()) {
            ("env", GET_STACK_BUFFER_GLOBAL_NAME) => {
                if let External::Function(_) = entry.external() {
                    get_stack_buffer_index = Some(index);
                    index += 1;
                }
            }
            ("env", SET_STACK_BUFFER_GLOBAL_NAME) => {
                if let External::Function(_) = entry.external() {
                    set_stack_buffer_index = Some(index);
                    index += 1;
                }
            }
            _ => {
                if let External::Function(_) = entry.external() {
                    index += 1;
                }
            }
        }
    }

    log::debug!(
        "get_stack_buffer_index: {:?}, set_stack_buffer_index: {:?}",
        get_stack_buffer_index,
        set_stack_buffer_index
    );

    (get_stack_buffer_index, set_stack_buffer_index)
}

pub fn insert_stack_buffer_global(
    module: &mut Module,
    stack_buffer_offset: u32,
    get_index: Option<u32>,
    set_index: Option<u32>,
) -> Result<(), &'static str> {
    *module = builder::from_module(module.clone())
        .global()
        .mutable()
        .init_expr(Instruction::I64Const(stack_buffer_offset as i64))
        .value_type()
        .i64()
        .build()
        .build();

    let gear_flags_global_index = module
        .global_section()
        .ok_or("Cannot find global section, which must be.")?
        .entries()
        .len()
        .checked_sub(1)
        .ok_or("Globals section is empty, but must be at least one element.")?
        .try_into()
        .map_err(|_| "Globals index is too big")?;

    for code in module
        .code_section_mut()
        .ok_or("Cannot find code section")?
        .bodies_mut()
    {
        for instruction in code.code_mut().elements_mut() {
            match instruction {
                Instruction::Call(call_index) => {
                    if get_index == Some(*call_index) {
                        log::debug!(
                            "Change `call {}` to `global.get {}`",
                            call_index,
                            gear_flags_global_index
                        );
                        *instruction = Instruction::GetGlobal(gear_flags_global_index);
                    } else if set_index == Some(*call_index) {
                        log::debug!(
                            "Change `call {}` to `global.set {}`",
                            call_index,
                            gear_flags_global_index
                        );
                        *instruction = Instruction::SetGlobal(gear_flags_global_index);
                    }
                }
                Instruction::CallIndirect(_, _) => {
                    // TODO: make handling for call_indirect also.
                    // log::trace!("lol");
                }
                _ => {}
            }
        }
    }

    Ok(())
}

#[test]
fn assembly_script_stack_pointer() {
    use pwasm_utils::parity_wasm::elements;

    let wat = r#"
        (module
            (import "env" "memory" (memory 1))
            (global $~lib/memory/__data_end i32 (i32.const 2380))
            (global $~lib/memory/__stack_pointer (mut i32) (i32.const 1050956))
            (export "handle" (func $handle))
            (export "init" (func $init))
            (func $handle)
            (func $init)
        )"#;

    let binary = wabt::Wat2Wasm::new()
        .validate(true)
        .write_debug_names(true)
        .convert(wat)
        .expect("failed to parse module")
        .as_ref()
        .to_vec();

    let mut module = elements::deserialize_buffer(&binary).expect("failed to deserialize binary");
    insert_stack_end_export(&binary, &mut module, 0).expect("insert_stack_end_export failed");

    let gear_stack_end = module
        .export_section()
        .expect("export section should exist")
        .entries()
        .iter()
        .find(|e| e.field() == STACK_END_EXPORT_NAME)
        .expect("export entry should exist");

    // `2` because we insert new global in wasm, which const and equal to stack pointer start offset.
    assert!(matches!(
        gear_stack_end.internal(),
        elements::Internal::Global(2)
    ));
}
