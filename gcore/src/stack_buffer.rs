use crate::{ActorId, MessageId};
use alloc::vec;
use gsys::stack_buffer::{
    get_stack_buffer_global, set_stack_buffer_global, StackBuffer, BYTE_BUFFER1_SIZE,
    BYTE_BUFFER2_SIZE, BYTE_BUFFER3_SIZE, BYTE_BUFFER4_SIZE,
};

enum HostGetterIndex {
    BlockHeight = 32,
    BlockTimestamp,
    MessageId,
    Origin,
    MessageSize,
    StatusCode,
    Source,
    Value,
    ByteBuffer1,
    ByteBuffer2,
    ByteBuffer3,
    ByteBuffer4,
}

fn call_const_getter<T: Clone + From<K>, K: Clone + From<T>>(
    index: HostGetterIndex,
    get: impl FnOnce() -> T,
    stack_buffer_field: impl FnOnce(&mut StackBuffer) -> &mut K,
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
            stack_buffer_field(stack_buffer).clone().into()
        } else {
            let data = get();
            *stack_buffer_field(stack_buffer) = data.clone().into();
            flags |= mask;
            set_stack_buffer_global(flags);
            data
        }
    }
}

pub fn with_byte_buffer<T>(size: usize, f: impl FnOnce(&mut [u8]) -> T) -> T {
    unsafe {
        let flags = get_stack_buffer_global();
        let stack_buffer_offset = (flags & (u32::MAX as u64)) as usize;
        if stack_buffer_offset == 0 {
            let mut buffer = vec![0; size];
            return f(buffer.as_mut_slice());
        }

        let stack_buffer = (stack_buffer_offset as *mut StackBuffer).as_mut().unwrap();

        let buffer_index = match size {
            size if size <= BYTE_BUFFER1_SIZE => HostGetterIndex::ByteBuffer1,
            size if size <= BYTE_BUFFER2_SIZE => HostGetterIndex::ByteBuffer2,
            size if size <= BYTE_BUFFER3_SIZE => HostGetterIndex::ByteBuffer3,
            size if size <= BYTE_BUFFER4_SIZE => HostGetterIndex::ByteBuffer4,
            _ => {
                let mut buffer = vec![0; size];
                return f(buffer.as_mut_slice());
            }
        };

        for index in buffer_index as u32..=HostGetterIndex::ByteBuffer4 as u32 {
            let mask = 1u64 << index as u64;
            if flags & mask != 0 {
                continue;
            }

            let s1 = HostGetterIndex::ByteBuffer1 as u32;
            let s2 = HostGetterIndex::ByteBuffer2 as u32;
            let s3 = HostGetterIndex::ByteBuffer3 as u32;
            let s4 = HostGetterIndex::ByteBuffer4 as u32;

            let buffer = match index {
                s if s == s1 => stack_buffer.byte_buffer1.as_mut_slice(),
                s if s == s2 => stack_buffer.byte_buffer2.as_mut_slice(),
                s if s == s3 => stack_buffer.byte_buffer3.as_mut_slice(),
                s if s == s4 => stack_buffer.byte_buffer4.as_mut_slice(),
                _ => unreachable!(),
            };

            set_stack_buffer_global(flags | mask);

            let data = f(buffer[0..size].as_mut());

            let flags = get_stack_buffer_global();
            set_stack_buffer_global(flags & !mask);

            return data;
        }

        let mut buffer = vec![0; size];
        return f(buffer.as_mut_slice());
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

pub fn status_code() -> gsys::LengthWithCode {
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
