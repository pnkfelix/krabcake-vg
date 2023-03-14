#![feature(core_intrinsics)]
#![no_std]

use core::ffi::{c_char,c_int,CStr};
use core::panic::PanicInfo;
/*
extern "C" {
    fn printf(format: *const c_char, ...) -> c_int;
}
*/
#[no_mangle]
pub extern "C" fn hello_world() {
    // println!("Hello World!");
    // let msg = CStr::from_bytes_with_nul(b"Hello World!\n\0").unwrap();
    // unsafe { printf(msg.as_ptr()); }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // let msg = CStr::from_bytes_with_nul(b"Panicked!\n\0").unwrap();
    // unsafe { printf(msg.as_ptr()); }
    core::intrinsics::abort()
}

/*
pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
*/
