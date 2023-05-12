use crate::{ActorId, MessageId};

extern "C" {
    fn get_gear_flags() -> u64;
    fn set_gear_flags(i: u64);
}

#[derive(Debug, Default)]
struct StackBuffer {
    block_height: u32,
    block_timestamp: u64,
    message_id: MessageId,
    origin: ActorId,
    message_size: usize,
}

enum HostGetterIndex {
    BlockHeight = 32,
    BlockTimestamp,
    MessageId,
    Origin,
    MessageSize,
}

fn call_const_getter<T: Copy>(
    index: HostGetterIndex,
    get: impl FnOnce() -> T,
    stack_buffer_field: impl FnOnce(&mut StackBuffer) -> &mut T,
) -> T {
    unsafe {
        let mut flags = get_gear_flags();
        let stack_buffer_offset = (flags & (u32::MAX as u64)) as usize;
        if stack_buffer_offset == 0 {
            return get();
        }

        let stack_buffer = (stack_buffer_offset as *mut StackBuffer).as_mut().unwrap();

        let mask = 1u64 << index as u64;

        if flags & mask != 0 {
            *stack_buffer_field(stack_buffer)
        } else {
            let data = get();
            *stack_buffer_field(stack_buffer) = data;
            flags |= mask;
            set_gear_flags(flags);
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
