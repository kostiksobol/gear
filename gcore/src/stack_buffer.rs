use crate::{ActorId, MessageId, errors::Result};

extern "C" {
    fn get_stack_buffer_global() -> u64;
    fn set_stack_buffer_global(i: u64);
}

// const BYTE_BUFFER_SIZE: usize = 1024;

#[derive(Debug)]
struct StackBuffer {
    block_height: u32,
    block_timestamp: u64,
    message_id: MessageId,
    origin: ActorId,
    message_size: usize,
    status_code: Result<i32>,
    source: ActorId,
    value: u128,
    // byte_buffer: [u8; BYTE_BUFFER_SIZE],
}

enum HostGetterIndex {
    BlockHeight = 32,
    BlockTimestamp,
    MessageId,
    Origin,
    MessageSize,
    StatusCode,
    Source,
    Value,
}

fn call_const_getter<T: Clone>(
    index: HostGetterIndex,
    get: impl FnOnce() -> T,
    stack_buffer_field: impl FnOnce(&mut StackBuffer) -> &mut T,
) -> T {
    unsafe {
        let mut flags = get_stack_buffer_global();
        let stack_buffer_offset = (flags & (u32::MAX as u64)) as usize;
        if stack_buffer_offset == 0 {
            return get();
        }

        let stack_buffer = (stack_buffer_offset as *mut StackBuffer).as_mut().unwrap();

        let mask = 1u64 << index as u64;

        if flags & mask != 0 {
            stack_buffer_field(stack_buffer).clone()
        } else {
            let data = get();
            *stack_buffer_field(stack_buffer) = data.clone();
            flags |= mask;
            set_stack_buffer_global(flags);
            data
        }
    }
}

pub fn origin() -> ActorId {
    call_const_getter(
        HostGetterIndex::Origin,
        crate::exec::origin_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.origin,
    )
}

pub fn size() -> usize {
    call_const_getter(
        HostGetterIndex::MessageSize,
        crate::msg::size_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.message_size,
    )
}

pub fn message_id() -> MessageId {
    call_const_getter(
        HostGetterIndex::MessageId,
        crate::msg::message_id_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.message_id,
    )
}

pub fn block_height() -> u32 {
    call_const_getter(
        HostGetterIndex::BlockHeight,
        crate::exec::block_height_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.block_height,
    )
}

pub fn block_timestamp() -> u64 {
    call_const_getter(
        HostGetterIndex::BlockTimestamp,
        crate::exec::block_timestamp_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.block_timestamp,
    )
}

pub fn status_code() -> Result<i32> {
    call_const_getter(
        HostGetterIndex::StatusCode,
        crate::msg::status_code_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.status_code,
    )
}

pub fn source() -> ActorId {
    call_const_getter(
        HostGetterIndex::Source,
        crate::msg::source_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.source,
    )
}

pub fn value() -> u128 {
    call_const_getter(
        HostGetterIndex::Value,
        crate::msg::value_syscall_wrapper,
        |stack_buffer| &mut stack_buffer.value,
    )
}
