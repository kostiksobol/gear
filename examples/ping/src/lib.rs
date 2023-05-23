#![no_std]

#[cfg(target_arch = "wasm32")]
extern crate galloc;

use core::str;
use gcore::msg;

// extern crate alloc;

// use alloc::vec;

#[no_mangle]
extern "C" fn handle() {
    // let f = |bytes| {
    //     if let Ok(received_msg) = str::from_utf8(bytes) {
    //         if received_msg == "PING" {
    //             let _ = msg::reply(b"PONG", 0);
    //         }
    //     }
    // };

    // match msg::size() {
    //     size if size <= 0x10 => {
    //         let mut buffer = [0; 0x10];
    //         f(&mut buffer);
    //     },
    //     size if size <= 0x20 => {
    //         let mut buffer = [0; 0x20];
    //         f(&mut buffer);
    //     }
    //     size if size <= 0x4000 => {
    //         let mut buffer = [0; 0x4000];
    //         f(&mut buffer);
    //     }
    //     size if size <= 0x100001 => {
    //         let mut buffer = [0; 0x100001];
    //         f(&mut buffer);
    //     }
    //     size => {
    //         let mut buffer = vec![0; size];
    //         f(buffer.as_mut_slice());
    //     }
    // }

    msg::with_read(|bytes| {
        if let Ok(received_msg) = str::from_utf8(bytes) {
            if received_msg == "PING" {
                let _ = msg::reply(b"PONG", 0);
            }
        }
    })
    .unwrap();
}

#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable();
}
