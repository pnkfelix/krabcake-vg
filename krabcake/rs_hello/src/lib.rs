#![feature(core_intrinsics, lang_items, c_size_t)]
#![no_std]
#![allow(unused_imports)]

use core::ffi::{c_char,c_int,CStr,c_size_t,c_void};
use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn hello_world(
    printn: extern "C" fn(*const c_char, n: usize) -> usize,
    _printi: extern "C" fn(i: i32) -> usize,
    printu: extern "C" fn(u: u32) -> usize,
) {
    let msg: &[u8] = b"Hello world (from `rs_hello/src/lib.rs`)! ";
    let printed = printn(msg.as_ptr() as *const c_char, msg.len());
    let msg = b"printed: ";
    printn(msg.as_ptr() as *const c_char, msg.len());
    printu(printed as u32);
    let msg: &[u8] = b"\n";
    printn(msg.as_ptr() as *const c_char, msg.len());
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    let msg = CStr::from_bytes_with_nul(b"Panicked!\n\0").unwrap();
    unsafe { libc_stuff::printf(msg.as_ptr()); }
    core::intrinsics::abort()
}

#[lang = "eh_personality"]
fn rust_eh_personality() {
    core::intrinsics::abort()
}

// pnkfelix got tired of fighting with the linker
// "if you cannot beat 'em, join 'em."
mod libc_stuff;
