use alloc::vec::Vec;
use codec::{Decode, DecodeAll, MaxEncodedLen};
<<<<<<< HEAD
use gear_backend_common::{RuntimeCtx, RuntimeCtxError};
use gear_core::{buffer::RuntimeBuffer, env::Ext, memory::WasmPageNumber};
=======
use gear_backend_common::{
    error_processor::IntoExtError, AsTerminationReason, IntoExtInfo, RuntimeCtx,
};
use gear_core::{env::Ext, RUNTIME_MAX_ALLOC_SIZE};
>>>>>>> 36d97063 (move fix for sandbox backend to vara (#1544))

use gear_core_errors::MemoryError;
use sp_sandbox::{default_executor::Memory as DefaultExecutorMemory, HostError, SandboxMemory};

use crate::{
    funcs::{FuncError, SyscallOutput, WasmCompatible},
    MemoryWrap,
};

pub(crate) struct Runtime<'a, E: Ext> {
    pub ext: &'a mut E,
    pub memory: &'a DefaultExecutorMemory,
    pub memory_wrap: &'a mut MemoryWrap,
    pub err: FuncError<E::Error>,
}

impl<'a, E: Ext> Runtime<'a, E> {
    pub(crate) fn run<T, F>(&mut self, f: F) -> SyscallOutput
    where
        T: WasmCompatible,
        F: FnOnce(&mut Self) -> Result<T, FuncError<E::Error>>,
    {
        f(self).map(WasmCompatible::throw_back).map_err(|err| {
            self.err = err;
            HostError
        })
    }
}

impl<'a, E: Ext> RuntimeCtx<E> for Runtime<'a, E> {
    fn alloc(&mut self, pages: u32) -> Result<WasmPageNumber, RuntimeCtxError<E::Error>> {
        self.ext
            .alloc(pages.into(), self.memory_wrap)
            .map_err(RuntimeCtxError::Ext)
    }

    fn read_memory(&self, ptr: u32, len: u32) -> Result<Vec<u8>, RuntimeCtxError<E::Error>> {
        let mut buf = RuntimeBuffer::try_new_default(len as usize)?;
        self.memory
            .get(ptr, buf.get_mut())
            .map_err(|_| MemoryError::OutOfBounds)?;
        Ok(buf.into_vec())
    }

    fn read_memory_into_buf(
        &self,
        ptr: u32,
        buf: &mut [u8],
    ) -> Result<(), RuntimeCtxError<E::Error>> {
        self.memory
            .get(ptr, buf)
            .map_err(|_| MemoryError::OutOfBounds)?;

        Ok(())
    }

<<<<<<< HEAD
    fn read_memory_as<D: Decode + MaxEncodedLen>(
        &self,
        ptr: u32,
    ) -> Result<D, RuntimeCtxError<E::Error>> {
=======
impl<'a, E> RuntimeCtx<E> for Runtime<'a, E>
where
    E: Ext + IntoExtInfo + 'static,
    E::Error: AsTerminationReason + IntoExtError,
{
    fn alloc(&mut self, pages: u32) -> Result<gear_core::memory::WasmPageNumber, E::Error> {
        self.ext.alloc(pages.into(), self.memory_wrap)
    }

    fn read_memory(&self, ptr: u32, len: u32) -> Result<Vec<u8>, MemoryError> {
        if len as usize > RUNTIME_MAX_ALLOC_SIZE {
            return Err(MemoryError::OutOfBounds);
        }
        let mut buf = vec![0u8; len as usize];
        self.memory
            .get(ptr, buf.as_mut_slice())
            .map_err(|_| MemoryError::OutOfBounds)?;
        Ok(buf)
    }

    fn read_memory_into_buf(&self, ptr: u32, buf: &mut [u8]) -> Result<(), MemoryError> {
        self.memory
            .get(ptr, buf)
            .map_err(|_| MemoryError::OutOfBounds)
    }

    fn read_memory_as<D: Decode + MaxEncodedLen>(&self, ptr: u32) -> Result<D, MemoryError> {
>>>>>>> 36d97063 (move fix for sandbox backend to vara (#1544))
        let buf = self.read_memory(ptr, D::max_encoded_len() as u32)?;
        let decoded = D::decode_all(&mut &buf[..]).map_err(|_| MemoryError::MemoryAccessError)?;
        Ok(decoded)
    }

    fn write_output(&mut self, out_ptr: u32, buf: &[u8]) -> Result<(), RuntimeCtxError<E::Error>> {
        self.memory
            .set(out_ptr, buf)
            .map_err(|_| MemoryError::OutOfBounds)?;

        Ok(())
    }
}
