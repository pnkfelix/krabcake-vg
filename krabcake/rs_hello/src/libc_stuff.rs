//! The definitions in this file are a hack to work around issues when using
//! types like `CStr` in the staticlib we create here. Namely, libcore has
//! references to functions like `strlen` that are usually associated with
//! `libc`, as well as functions like `memcmp` (which can be rewritten into
//! `bcmp` by LLVM), which should be provided by *something*, but apparently are
//! not readily provided here.
//!
//! The easiest thing to do was to just call out to all the local definitions
//! for these methods that Valgrind itself provides.

use core::ffi::{c_char, c_int, c_size_t, c_void, CStr};

#[cfg(not(test))]
#[no_mangle]
pub unsafe extern "C" fn printf(s: *const c_char) -> usize {
    unsafe { super::vgPlain_printf(s) as usize }
}

#[cfg(not(test))]
#[no_mangle]
unsafe extern "C" fn strlen(s: *const c_char) -> usize {
    extern "C" {
        fn vgPlain_strlen(s: *const c_char) -> usize;
    }
    unsafe { vgPlain_strlen(s) }
}

#[cfg(not(test))]
#[no_mangle]
unsafe extern "C" fn memcmp(s1: *const c_void, s2: *const c_void, n: c_size_t) -> usize {
    extern "C" {
        fn vgPlain_memcmp(s1: *const c_void, s2: *const c_void, n: c_size_t) -> usize;
    }
    unsafe { vgPlain_memcmp(s1, s2, n) }
}

#[cfg(not(test))]
#[no_mangle]
unsafe extern "C" fn bcmp(s1: *const c_void, s2: *const c_void, n: c_size_t) -> usize {
    unsafe { memcmp(s1, s2, n) }
}

#[cfg(not(test))]
// Only empty definition is needed; we just need it to compile
#[repr(C)]
pub struct _Unwind_Exception {}

#[cfg(not(test))]
// From https://github.com/rust-lang/rust/blob/480068c2359ea65df4481788b5ce717a548ce171/library/unwind/src/libunwind.rs#L105-L107
#[no_mangle]
unsafe extern "C-unwind" fn _Unwind_Resume(_exception: *mut _Unwind_Exception) -> ! {
    // Looping because of ! type
    #[allow(clippy::empty_loop)]
    loop {}
}
