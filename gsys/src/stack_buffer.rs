use crate::{Hash, LengthWithCode};

pub const GET_STACK_BUFFER_GLOBAL_NAME: &str = "get_stack_buffer_global";
pub const SET_STACK_BUFFER_GLOBAL_NAME: &str = "set_stack_buffer_global";

extern "C" {
    pub fn get_stack_buffer_global() -> u64;
    pub fn set_stack_buffer_global(i: u64);
}

pub const BYTE_BUFFER1_SIZE: usize = 0x400;
pub const BYTE_BUFFER2_SIZE: usize = 0x800;
pub const BYTE_BUFFER3_SIZE: usize = 0x1000;
pub const BYTE_BUFFER4_SIZE: usize = 0x2000;

#[repr(C, align(0x4000))]
pub struct StackBuffer {
    pub block_height: u32,
    pub block_timestamp: u64,
    pub message_id: Hash,
    pub origin: Hash,
    pub message_size: usize,
    pub status_code: LengthWithCode,
    pub source: Hash,
    pub value: u128,
    pub byte_buffer1: [u8; BYTE_BUFFER1_SIZE],
    pub byte_buffer2: [u8; BYTE_BUFFER2_SIZE],
    pub byte_buffer3: [u8; BYTE_BUFFER3_SIZE],
    pub byte_buffer4: [u8; BYTE_BUFFER4_SIZE],
}

pub const STACK_BUFFER_SIZE: u32 = core::mem::size_of::<StackBuffer>() as u32;
