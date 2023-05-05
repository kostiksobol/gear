#![no_std]
// #![feature(lang_items, start)]

// #[no_mangle]
// pub static mut STACK_BUFFER_OFFSET: i32 = -1;

use gstd::{debug, prelude::*};

extern "C" {
    fn get_gear_flags() -> u64;
    fn set_gear_flags(i: u64);
    fn gr_size(size_ptr: *mut u32);
}

#[repr(align(16))]
#[derive(Debug, Default)]
struct StackBuffer {
    message_size: Option<u32>,
}

#[inline(never)]
fn get_message_size() -> u32 {
    unsafe {
        let flags = get_gear_flags();
        let stack_buffer_ptr = (flags & (u32::MAX as u64)) as usize as *mut StackBuffer;
        let stack_buffer_is_set = (flags & (1u64 << 32)) != 0;
        if !stack_buffer_is_set {
            debug!("reset stack buffer");
            *stack_buffer_ptr.as_mut().unwrap() = Default::default();
            let flags = flags | (1u64 << 32);
            set_gear_flags(flags);
        }
        let stack_buffer = stack_buffer_ptr.as_mut().unwrap();
        *stack_buffer.message_size.get_or_insert_with(|| {
            let mut size: u32 = 0;
            gr_size(&mut size as *mut u32);
            debug!("get size from gr_size: {}", size);
            size
        })
    }
}

#[no_mangle]
extern "C" fn handle() {
    for i in 0..10 {
        let size = get_message_size();
        debug!("{}) Lol, size is {}", i, size);
    }
}

// #[cfg(target_arch = "wasm32")]
// #[panic_handler]
// fn panic(_: &core::panic::PanicInfo) -> ! {
//     core::arch::wasm32::unreachable();
// }

// use core::mem::MaybeUninit;
// use core::ptr::NonNull;

// #[no_mangle]
// pub extern "C" fn lol_function() {
//     // Your code here
//     // This function will be executed automatically when the module is instantiated

//     unsafe {
//         let x = get_gear_flags();
//         set_gear_flags(x + 42);
//     }

//     let mut stack_allocated_var = MaybeUninit::<i32>::uninit();
//     let stack_allocated_var_ptr = NonNull::from(&mut stack_allocated_var);

//     // SAFETY: This assignment initializes the value stored in stack_allocated_var.
//     unsafe {
//         stack_allocated_var.as_mut_ptr().write(43);
//         core::mem::forget(stack_allocated_var);
//         LOL = stack_allocated_var_ptr.as_ptr() as usize as i64;
//     }

// }
