#![feature(num_as_ne_bytes)]

use gstd::{ext, msg, ProgramId};
use std::{convert::TryInto, num::ParseIntError};

static mut MESSAGE_LOG: Vec<String> = vec![];

static mut STATE: State = State {
    send_to: ProgramId([0u8; 32]),
};
#[derive(Debug)]
struct State {
    send_to: ProgramId,
}

impl State {
    fn set_send_to(&mut self, to: ProgramId) {
        self.send_to = to;
    }
    fn send_to(&self) -> ProgramId {
        self.send_to
    }
}

fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect()
}

#[no_mangle]
pub unsafe extern "C" fn handle() {
    let new_msg = i32::from_le_bytes(msg::load().try_into().expect("Should be i32"));
    MESSAGE_LOG.push(format!("New msg: {:?}", new_msg));

    msg::send(STATE.send_to(), (new_msg + new_msg).as_ne_bytes(), u64::MAX, 0);

    ext::debug(&format!(
        "{:?} total message(s) stored: ",
        MESSAGE_LOG.len()
    ));

    for log in MESSAGE_LOG.iter() {
        ext::debug(log);
    }
}

#[no_mangle]
pub unsafe extern "C" fn init() {
    let input = String::from_utf8(msg::load()).expect("Invalid message: should be utf-8");
    let send_to = ProgramId::from_slice(
        &decode_hex(&input).expect("INTIALIZATION FAILED: INVALID PROGRAM ID"),
    );
    STATE.set_send_to(send_to);
}

fn main() {}
