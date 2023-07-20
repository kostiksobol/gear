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

#![cfg_attr(not(feature = "std"), no_std)]

use parity_scale_codec::{Decode, Encode};
use scale_info::TypeInfo;

#[cfg(feature = "wasm-wrapper")]
mod code {
    include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));
}

#[cfg(feature = "wasm-wrapper")]
pub use code::WASM_BINARY_OPT as WASM_BINARY;

#[derive(Debug, Decode, Encode, TypeInfo)]
pub struct InputArgs {
    pub destination: [u8; 32],
}

pub const HANDLE_REPLY_EXPECT: &str = "I will fail";

#[cfg(not(feature = "wasm-wrapper"))]
mod wasm {
    use crate::{InputArgs, HANDLE_REPLY_EXPECT};
    use gstd::{msg, ActorId};

    static mut DESTINATION: ActorId = ActorId::new([0u8; 32]);

    #[no_mangle]
    extern "C" fn init() {
        let args: InputArgs = msg::load().expect("Failed to decode `InputArgs'");
        unsafe { DESTINATION = args.destination.into() };
    }

    #[no_mangle]
    extern "C" fn handle() {
        let payload = msg::load_bytes().expect("failed to load bytes");
        msg::send_bytes(unsafe { DESTINATION }, payload, msg::value())
            .expect("failed to send bytes");
    }

    #[no_mangle]
    extern "C" fn handle_reply() {
        // Will panic here as replies denied in `handle_reply`.
        msg::reply_bytes([], 0).expect(HANDLE_REPLY_EXPECT);
    }
}
