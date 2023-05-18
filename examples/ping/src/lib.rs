#![no_std]

#[cfg(target_arch = "wasm32")]
extern crate galloc;

use core::str;
use gcore::msg;

#[no_mangle]
extern "C" fn handle() {
    msg::with_read(|bytes| {
        if let Ok(received_msg) = str::from_utf8(bytes) {
            if received_msg == "PING" {
                let _ = msg::reply(b"PONG", 0);
            }
        }
    })
    .unwrap();
    // let mut bytes = vec![0; msg::size()];
    // msg::read(&mut bytes).unwrap();

    // if let Ok(received_msg) = str::from_utf8(&bytes) {
    //     if received_msg == "PING" {
    //         let _ = msg::reply(b"PONG", 0);
    //     }
    // }
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable();
}
