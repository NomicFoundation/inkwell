use llvm_sys::core::{
    LLVMCreateMemoryBufferWithContentsOfFile, LLVMCreateMemoryBufferWithMemoryRange,
    LLVMCreateMemoryBufferWithMemoryRangeCopy, LLVMCreateMemoryBufferWithSTDIN, LLVMDisposeMemoryBuffer,
    LLVMGetBufferSize, LLVMGetBufferStart,
};
use llvm_sys::linker::{
    LLVMAssembleEVM, LLVMDisposeAssembleResultEVM, LLVMDisposeImmutablesEVM,
    LLVMEVMLibrarySymbol, LLVMGetImmutablesEVM,
};
#[allow(deprecated)]
use llvm_sys::object::LLVMCreateObjectFile;
use llvm_sys::prelude::LLVMMemoryBufferRef;

use crate::object_file::ObjectFile;
use crate::support::{to_c_str, LLVMString};

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::mem::{forget, MaybeUninit};
use std::path::Path;
use std::ptr;
use std::slice;

#[derive(Debug)]
pub struct MemoryBuffer {
    pub(crate) memory_buffer: LLVMMemoryBufferRef,
}

/// The outputs of [`MemoryBuffer::assemble_evm`].
#[cfg(all(feature = "llvm21-1", feature = "target-evm"))]
#[derive(Debug)]
pub struct EVMAssembleResult {
    /// The final bytecode, with zero bytes at every unresolved library slot.
    pub bytecode: MemoryBuffer,
    /// The relocatable ELF object for embedding into a later assembly,
    /// present when the call requested it.
    pub elf_object: Option<MemoryBuffer>,
    /// One (source name, bytecode offset) pair per unresolved library use.
    pub unresolved_references: Vec<(String, u64)>,
    /// One entry per input buffer: `Some(offset)` of its text in
    /// `bytecode`, or `None` when the layout left the input out.
    pub input_layout: Vec<Option<u64>>,
    /// The offset of the metadata, which ends `bytecode`.
    pub metadata_offset: u64,
}

impl MemoryBuffer {
    pub const ETHEREUM_ADDRESS_SIZE: usize = 20;

    pub unsafe fn new(memory_buffer: LLVMMemoryBufferRef) -> Self {
        assert!(!memory_buffer.is_null());

        MemoryBuffer { memory_buffer }
    }

    pub fn as_mut_ptr(&self) -> LLVMMemoryBufferRef {
        self.memory_buffer
    }

    pub fn create_from_file(path: &Path) -> Result<Self, LLVMString> {
        let path = to_c_str(path.to_str().expect("Did not find a valid Unicode path string"));
        let mut memory_buffer = ptr::null_mut();
        let mut err_string = MaybeUninit::uninit();

        let return_code = unsafe {
            LLVMCreateMemoryBufferWithContentsOfFile(
                path.as_ptr() as *const ::libc::c_char,
                &mut memory_buffer,
                err_string.as_mut_ptr(),
            )
        };

        // TODO: Verify 1 is error code (LLVM can be inconsistent)
        if return_code == 1 {
            unsafe {
                return Err(LLVMString::new(err_string.assume_init()));
            }
        }

        unsafe { Ok(MemoryBuffer::new(memory_buffer)) }
    }

    pub fn create_from_stdin() -> Result<Self, LLVMString> {
        let mut memory_buffer = ptr::null_mut();
        let mut err_string = MaybeUninit::uninit();

        let return_code = unsafe { LLVMCreateMemoryBufferWithSTDIN(&mut memory_buffer, err_string.as_mut_ptr()) };

        // TODO: Verify 1 is error code (LLVM can be inconsistent)
        if return_code == 1 {
            unsafe {
                return Err(LLVMString::new(err_string.assume_init()));
            }
        }

        unsafe { Ok(MemoryBuffer::new(memory_buffer)) }
    }

    /// This function is likely slightly cheaper than `create_from_memory_range_copy` since it intentionally
    /// leaks data to LLVM so that it doesn't have to reallocate. `create_from_memory_range_copy` may be removed
    /// in the future
    pub fn create_from_memory_range(input: &[u8], name: &str, requires_null_terminator: bool) -> Self {
        let name_c_string = to_c_str(name);

        let memory_buffer = unsafe {
            LLVMCreateMemoryBufferWithMemoryRange(
                input.as_ptr() as *const ::libc::c_char,
                input.len(),
                name_c_string.as_ptr(),
                requires_null_terminator as i32,
            )
        };

        unsafe { MemoryBuffer::new(memory_buffer) }
    }

    /// This will create a new `MemoryBuffer` from the given input.
    ///
    /// This function is likely slightly more expensive than `create_from_memory_range` since it does not leak
    /// data to LLVM, forcing LLVM to make a copy. This function may be removed in the future in favor of
    /// `create_from_memory_range`
    pub fn create_from_memory_range_copy(input: &[u8], name: &str) -> Self {
        let name_c_string = to_c_str(name);

        let memory_buffer = unsafe {
            LLVMCreateMemoryBufferWithMemoryRangeCopy(
                input.as_ptr() as *const ::libc::c_char,
                input.len(),
                name_c_string.as_ptr(),
            )
        };

        unsafe { MemoryBuffer::new(memory_buffer) }
    }

    /// Gets a byte slice of this `MemoryBuffer`.
    pub fn as_slice(&self) -> &[u8] {
        unsafe {
            let start = LLVMGetBufferStart(self.memory_buffer);

            slice::from_raw_parts(start as *const _, self.get_size())
        }
    }

    /// Gets the byte size of this `MemoryBuffer`.
    pub fn get_size(&self) -> usize {
        unsafe { LLVMGetBufferSize(self.memory_buffer) }
    }

    /// Convert this `MemoryBuffer` into an `ObjectFile`. LLVM does not currently
    /// provide any way to determine the cause of error if conversion fails.
    pub fn create_object_file(self) -> Result<ObjectFile, ()> {
        #[allow(deprecated)]
        let object_file = unsafe { LLVMCreateObjectFile(self.memory_buffer) };

        forget(self);

        if object_file.is_null() {
            return Err(());
        }

        unsafe { Ok(ObjectFile::new(object_file)) }
    }

    /// Returns immutables and their offsets.
    #[cfg(all(feature = "llvm21-1", feature = "target-evm"))]
    pub fn get_immutables_evm(&self) -> BTreeMap<String, BTreeSet<u64>> {
        let mut immutable_ids_buffer = ptr::null_mut();
        let mut immutable_offsets_buffer = ptr::null_mut();
        let immutables_size = unsafe {
            LLVMGetImmutablesEVM(
                self.memory_buffer,
                &mut immutable_ids_buffer,
                &mut immutable_offsets_buffer,
            )
        };

        let immutable_ids = if immutables_size != 0 {
            let immutable_ids_buffer_slice =
                unsafe { slice::from_raw_parts(immutable_ids_buffer, immutables_size as usize) };
            let immutable_ids = immutable_ids_buffer_slice
                .iter()
                .map(|&value| unsafe {
                    String::from(::std::ffi::CStr::from_ptr(value).to_str().expect("Always valid"))
                })
                .collect();
            immutable_ids
        } else {
            vec![]
        };
        let immutable_offsets = if immutables_size != 0 {
            let immutable_offsets_buffer_slice =
                unsafe { slice::from_raw_parts(immutable_offsets_buffer, immutables_size as usize) };
            let immutable_offsets = immutable_offsets_buffer_slice.iter().map(|&value| value).collect();
            immutable_offsets
        } else {
            vec![]
        };

        let immutables_map: BTreeMap<String, BTreeSet<u64>> = immutable_ids
            .into_iter()
            .zip(immutable_offsets.into_iter())
            .fold(BTreeMap::new(), |mut accumulator, (id, offset)| {
                accumulator.entry(id).or_insert_with(BTreeSet::new).insert(offset);
                accumulator
            });

        unsafe {
            LLVMDisposeImmutablesEVM(
                immutable_ids_buffer as *const *const ::libc::c_char,
                immutable_offsets_buffer as *const u64,
                immutables_size,
            );
        }

        immutables_map
    }

    /// Assembles the EVM dependencies given in `buffers` with the first
    /// buffer, appending `metadata` to the code and resolving the library
    /// addresses given in `library_symbols`. A library reference with no
    /// address stays as 20 zero bytes in the bytecode and is reported as an
    /// unresolved reference.
    #[cfg(all(feature = "llvm21-1", feature = "target-evm"))]
    pub fn assemble_evm(
        buffers: &[&Self],
        buffer_ids: &[&str],
        metadata: &[u8],
        library_symbols: &BTreeMap<String, [u8; Self::ETHEREUM_ADDRESS_SIZE]>,
        emit_elf_object: bool,
    ) -> EVMAssembleResult {
        let buffer_ptrs: Vec<LLVMMemoryBufferRef> = buffers.iter().map(|buffer| buffer.memory_buffer).collect();

        let buffer_ids: Vec<String> = buffer_ids
            .iter()
            .map(|id| crate::support::to_null_terminated_owned(id))
            .collect();
        let buffer_ids: Vec<*const ::libc::c_char> =
            buffer_ids.iter().map(|id| to_c_str(id.as_str()).as_ptr()).collect();

        let symbol_names: Vec<String> = library_symbols
            .keys()
            .map(|name| crate::support::to_null_terminated_owned(name.as_str()))
            .collect();
        let symbols: Vec<LLVMEVMLibrarySymbol> = symbol_names
            .iter()
            .zip(library_symbols.values())
            .map(|(name, value)| LLVMEVMLibrarySymbol {
                name: to_c_str(name.as_str()).as_ptr(),
                value: value.map(|byte| byte as ::libc::c_char),
            })
            .collect();

        let mut result = unsafe {
            LLVMAssembleEVM(
                buffer_ptrs.as_ptr(),
                buffer_ids.as_ptr(),
                buffer_ptrs.len() as u64,
                metadata.as_ptr() as *const ::libc::c_char,
                metadata.len() as u64,
                symbols.as_ptr(),
                symbols.len() as u64,
                ::libc::c_int::from(emit_elf_object),
            )
        };

        let unresolved_references = (0..result.num_unresolved as usize)
            .map(|index| unsafe {
                let name = ::std::ffi::CStr::from_ptr(*result.unresolved_names.add(index))
                    .to_str()
                    .expect("Always valid")
                    .to_owned();
                (name, *result.unresolved_offsets.add(index))
            })
            .collect();

        let input_layout = (0..result.num_inputs as usize)
            .map(|index| unsafe {
                let offset = *result.input_offsets.add(index);
                (offset != u64::MAX).then_some(offset)
            })
            .collect();
        let metadata_offset = result.metadata_offset;

        let bytecode = unsafe { MemoryBuffer::new(result.bytecode) };
        let elf_object = if result.elf_object.is_null() {
            None
        } else {
            Some(unsafe { MemoryBuffer::new(result.elf_object) })
        };
        // The wrappers above own the buffers now.
        result.bytecode = ptr::null_mut();
        result.elf_object = ptr::null_mut();
        unsafe { LLVMDisposeAssembleResultEVM(&mut result) };

        EVMAssembleResult {
            bytecode,
            elf_object,
            unresolved_references,
            input_layout,
            metadata_offset,
        }
    }
}

impl Drop for MemoryBuffer {
    fn drop(&mut self) {
        unsafe {
            LLVMDisposeMemoryBuffer(self.memory_buffer);
        }
    }
}
