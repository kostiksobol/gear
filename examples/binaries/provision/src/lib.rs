// This file is part of Gear.

// Copyright (C) 2022 Gear Technologies Inc.
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

#[cfg(feature = "std")]
mod code {
    include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));
}

#[cfg(feature = "std")]
pub use code::WASM_BINARY_OPT as WASM_BINARY;

pub const PROVISION_AMOUNT: u64 = 1_000_000_000;
pub const SUCCESS_MESSAGE: &str = "I've received reply!";

#[cfg(not(feature = "std"))]
mod wasm {
    use super::{PROVISION_AMOUNT, SUCCESS_MESSAGE};
    use gstd::{exec, msg, ActorId, MessageId};

    static mut USER: ActorId = ActorId::zero();
    static mut MESSAGE_ID: MessageId = MessageId::zero();

    #[no_mangle]
    extern "C" fn init() {
        let source = msg::source();
        let dest = msg::load().expect("Failed to load `ActorId`");

        let message_id = msg::send_bytes_with_gas(dest, [], 0, 0).expect("Failed to send message");
        exec::create_provision(message_id, PROVISION_AMOUNT)
            .expect("Failed to create provision for message");

        unsafe {
            USER = source;
            MESSAGE_ID = message_id;
        }
    }

    #[no_mangle]
    extern "C" fn handle_reply() {
        if msg::reply_to().expect("Failed to query reply details") == unsafe { MESSAGE_ID } {
            msg::send_bytes(unsafe { USER }, SUCCESS_MESSAGE, 0)
                .expect("Failed to send message to user");
        }
    }
}
