#![feature(core_intrinsics, lang_items, c_size_t)]
#![feature(c_unwind)]
#![no_std]
#![allow(unused_imports)]

use core::ffi::{c_char, c_int, c_longlong, c_size_t, c_uchar, c_uint};
use core::ffi::{c_ulong, c_ulonglong, c_void, CStr};
use core::panic::PanicInfo;
use core::ptr;

extern crate alloc;
use core::alloc::{GlobalAlloc, Layout};

// Can now import and use anything in alloc
use alloc::vec::Vec;

extern "C" {
    // From krabcake-vg/include/pub_tool_mallocfree.h
    // Nb: the allocators *always succeed* -- they never return NULL (Valgrind
    // will abort if they can't allocate the memory).
    // The 'cc' is a string that identifies the allocation point.  It's used when
    // --profile-heap=yes is specified.
    // extern void* VG_(malloc)         ( const HChar* cc, SizeT nbytes );
    // extern void  VG_(free)           ( void* p );
    //
    // Basic types are in krabcake-vg/VEX/pub/libvex_basictypes.h
    // HChar = C char type
    // Implementation lives in krabcake-vg/coregrind/m_mallocfree.c
    fn vgPlain_malloc(cc: *const c_char, nbytes: c_size_t) -> *mut c_void;
    fn vgPlain_free(p: *mut c_void);
}

struct ValgrindAllocator;

#[global_allocator]
static ALLOCATOR: ValgrindAllocator = ValgrindAllocator;

unsafe impl Sync for ValgrindAllocator {}

unsafe impl GlobalAlloc for ValgrindAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let cc: &[u8] = b"cc\0"; // TODO: Set a unique identifier here?
        vgPlain_malloc(cc.as_ptr() as *const c_char, layout.size()) as *mut u8
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        vgPlain_free(ptr as *mut c_void);
    }
}

extern "C" {
    fn vgPlain_sprintf(buf: *mut c_char, format: *const c_char, ...) -> u32;
    fn vgPlain_snprintf(buf: *mut c_char, size: i32, format: *const c_char, ...) -> u32;
    fn vgPlain_printf(format: *const c_char, ...) -> u32;

    fn vgPlain_dmsg(format: *const c_char, ...) -> u32;
}

#[no_mangle]
pub extern "C" fn hello_world(
    _printn: extern "C" fn(*const c_char, n: usize) -> usize,
    _printi: extern "C" fn(i: i32) -> usize,
    _printu: extern "C" fn(u: u32) -> usize,
) {
    let msg: &[u8] = b"Hello world (from `rs_hello/src/lib.rs`)!\n\0";
    unsafe { vgPlain_printf(msg.as_ptr() as *const c_char, msg.len()) };

    let mut v = Vec::new();
    v.push(0);
    v.push(1);
    v.push(2);
    unsafe {
        vgPlain_printf("v.len: %u\n\0".as_ptr() as *const c_char, v.len() as c_int);
        let end = v.pop().unwrap();
        vgPlain_printf(
            "end: %u, v.len: %u\n\0".as_ptr() as *const c_char,
            end as c_int,
            v.len() as c_int,
        );
    };
}

#[no_mangle]
pub extern "C" fn hello_world_old(
    printn: extern "C" fn(*const c_char, n: usize) -> usize,
    _printi: extern "C" fn(i: i32) -> usize,
    printu: extern "C" fn(u: u32) -> usize,
) {
    let msg: &[u8] = b"Hello world (from `rs_hello/src/lib.rs`)! ";
    let printed = unsafe { vgPlain_printf(msg.as_ptr() as *const c_char, msg.len()) };
    let msg = b"printed: ";
    printn(msg.as_ptr() as *const c_char, msg.len());
    printu(printed as u32);
    let msg: &[u8] = b"\n";
    printn(msg.as_ptr() as *const c_char, msg.len());
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    let msg = CStr::from_bytes_with_nul(b"Panicked!\n\0").unwrap();
    unsafe {
        libc_stuff::printf(msg.as_ptr());
    }
    core::intrinsics::abort()
}

#[lang = "eh_personality"]
fn rust_eh_personality() {
    core::intrinsics::abort()
}

// pnkfelix got tired of fighting with the linker
// "if you cannot beat 'em, join 'em."
mod libc_stuff;

#[derive(Copy, Clone)]
struct Tag(u64);

impl Tag {
    fn next(self) -> Tag {
        Tag(self.0 + 1)
    }
}

static mut COUNTER: Tag = Tag(0);

enum Item {
    Unique(Tag),
}

// FIXME: Need to more clearly distinguish between addresses and
// shadowing of values. I.e. the tag here needs to be attached to the
// location where an address itself is being stored, and needs to flow
// along with the address as it is copied from place to place.
static mut TRACKED: Vec<(vg_addr, Tag)> = Vec::new();

static mut STACKS: Vec<(vg_addr, Vec<Item>)> = Vec::new();

fn if_tracked_then<T>(addr: vg_addr, process_tag: impl FnOnce(Tag) -> T) -> Option<T> {
    unsafe {
        for entry in &TRACKED {
            if entry.0 == addr {
                return Some(process_tag(entry.1));
            }
        }
    }
    None
}

fn if_has_stack_then<T>(
    addr: vg_addr,
    process_stack: impl FnOnce(&mut Vec<Item>) -> T,
) -> Option<T> {
    unsafe {
        for entry in &mut STACKS {
            if entry.0 == addr {
                return Some(process_stack(&mut entry.1));
            }
        }
    }
    None
}

#[no_mangle]
pub extern "C" fn rs_client_request_borrow_mut(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg(
            "kc_handle_client_request, handle BORROW_MUT 0x%llx (<- return value) into ret: 0x%08llx\n\0"
                .as_ptr() as *const c_char,
            *arg.offset(1),
            ret,
        );
        COUNTER = COUNTER.next();
        let addr = *arg.offset(1) as vg_addr;
        let addr_recv = ret as vg_addr;
        TRACKED.push((addr_recv, COUNTER));
        let lookup = if_has_stack_then(addr, |entries| {
            entries.push(Item::Unique(Tag(addr as u64)));
        });
        if lookup.is_none() {
            let mut v = Vec::new();
            v.push(Item::Unique(Tag(addr as u64)));
            STACKS.push((addr, v));
        }

        *ret = *arg.offset(1);
    }
    true
}

#[no_mangle]
pub extern "C" fn rs_client_request_borrow_shr(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg("kc_handle_client_request, handle BORROW_SHR\n\0".as_ptr() as *const c_char);
    }
    false
}

#[no_mangle]
pub extern "C" fn rs_client_request_as_raw(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg("kc_handle_client_request, handle AS_RAW\n\0".as_ptr() as *const c_char);
    }
    false
}

#[no_mangle]
pub extern "C" fn rs_client_request_as_borrow_mut(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg(
            "kc_handle_client_request, handle AS_BORROW_MUT\n\0".as_ptr() as *const c_char,
        );
    }
    false
}

#[no_mangle]
pub extern "C" fn rs_client_request_as_borrow_shr(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg(
            "kc_handle_client_request, handle AS_BORROW_SHR\n\0".as_ptr() as *const c_char,
        );
    }
    false
}

#[no_mangle]
pub extern "C" fn rs_client_request_retag_fn_prologue(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg(
            "kc_handle_client_request, handle RETAG_FN_PROLOGUE\n\0".as_ptr() as *const c_char,
        );
    }
    false
}

#[no_mangle]
pub extern "C" fn rs_client_request_retag_assign(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg("kc_handle_client_request, handle RETAG_ASSIGN\n\0".as_ptr() as *const c_char);
    }
    false
}

#[no_mangle]
pub extern "C" fn rs_client_request_retag_raw(
    thread_id: c_uint,
    arg: *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg("kc_handle_client_request, handle RETAG_RAW\n\0".as_ptr() as *const c_char);
    }
    false
}

#[allow(non_camel_case_types)]
type vg_bool = c_uchar;
#[allow(non_camel_case_types)]
type vg_addr = c_ulong;
#[allow(non_camel_case_types)]
type vg_uint = c_uint;
#[allow(non_camel_case_types)]
type vg_int = c_int;
#[allow(non_camel_case_types)]
type vg_ulong = c_ulonglong;
#[allow(non_camel_case_types)]
type vg_long = c_longlong;
#[allow(non_camel_case_types)]
type vg_size_t = c_size_t;

#[no_mangle]
pub extern "C" fn rs_trace_cas(addr: vg_addr) {
    unsafe {
        if false {
            let mut buf = alloc::string::String::new();
            buf += "rs_trace_cas addr=%08llx";
            vgPlain_printf((buf + "\n\0").as_ptr() as *const c_char, addr);
        }
    }
}
#[no_mangle]
pub extern "C" fn rs_trace_storeg(guard: vg_long, addr: vg_addr, size: vg_size_t) {}
#[no_mangle]
pub extern "C" fn rs_trace_loadg(
    guard: vg_long,
    addr: vg_addr,
    size: vg_size_t,
    widened_size: vg_size_t,
) {
}

#[no_mangle]
pub extern "C" fn rs_trace_wrtmp(lhs_tmp: vg_uint, s1: vg_long) {
    unsafe {
        if s1 != 0 {
            vgPlain_printf(
                b"rs_trace_wrtmp lhs_tmp: %u s1: %d\n\0".as_ptr() as *const c_char,
                lhs_tmp,
                s1,
            );
        }
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_wrtmp_load(lhs_tmp: vg_uint, addr: vg_addr, size: vg_size_t) {
    if_has_stack_then(addr, |stack| unsafe {
        vgPlain_printf(
            b"rs_trace_wrtmp_load lhs_tmp: %u addr %08llx has stack len: %d\n\0".as_ptr()
                as *const c_char,
            lhs_tmp,
            addr,
            stack.len(),
        );
    });
}

#[no_mangle]
pub extern "C" fn rs_trace_store(addr: vg_addr, data: vg_ulong, size: vg_size_t, shadow_addr: vg_ulong, shadow_data: vg_ulong) {
    unsafe {
        if shadow_addr != 0 || shadow_data != 0 {
            vgPlain_printf(
                b"rs_trace_store addr: 0x%llx data: 0x%llx shadow_addr: %d shadow_data: %d \n\0".as_ptr() as *const c_char,
		addr,
		data,
		shadow_addr,	
		shadow_data
            );
        }
    }

    if_tracked_then(addr as vg_addr, |tag| unsafe {
          vgPlain_printf(
             b"rs_trace_store addr %08llx shadow_addr: %08lld shaddow_data: %08lld has tag %d\n\0".as_ptr() as *const c_char,
             addr,
             shadow_addr,
             shadow_data,
             tag.0,
             );
       });

    if_tracked_then(data as vg_addr, |tag| unsafe {
          vgPlain_printf(
             b"rs_trace_store data %08llx shadow_addr: %08lld shaddow_data: %08lld has tag %d\n\0".as_ptr() as *const c_char,
             data,
             shadow_addr,
             shadow_data,
             tag.0,
             );
       });

    if_has_stack_then(addr, |stack| unsafe {
        vgPlain_printf(
            b"rs_trace_store addr %08llx has stack len: %d\n\0".as_ptr() as *const c_char,
            addr,
            stack.len(),
        );
    });
}

#[no_mangle]
pub extern "C" fn rs_trace_store128(
    addr: vg_addr,
    data1: vg_ulong,
    data2: vg_ulong,
    size: vg_size_t,
    shadow_addr: vg_ulong,
    shadow_data: vg_ulong,
) {
}

#[no_mangle]
pub extern "C" fn rs_trace_store256(
    addr: vg_addr,
    data1: vg_ulong,
    data2: vg_ulong,
    data3: vg_ulong,
    data4: vg_ulong,
    size: vg_size_t,
    shadow_addr: vg_ulong,
    shadow_data: vg_ulong,
) {
}

#[no_mangle]
pub extern "C" fn rs_trace_llsc(addr: vg_addr) {}

#[no_mangle]
pub extern "C" fn rs_trace_put(put_offset: vg_ulong, data: vg_ulong, shadow_data: vg_ulong) {
   unsafe {
        if shadow_data != 0 {
            vgPlain_printf(
                b"rs_trace_put offset: %lld data: 0x%llx shadow_data: %d \n\0".as_ptr() as *const c_char,
		put_offset,
		data,
		shadow_data
            );
           }
   }

   if_tracked_then(data as vg_addr, |tag| unsafe {
         vgPlain_printf(
            b"rs_trace_put offset %lld data %08llx shadow_data: %08lld has tag %d\n\0".as_ptr() as *const c_char,
	    put_offset,
            data,
            shadow_data,
            tag.0,
            );
      });


   if_has_stack_then(data as vg_addr, |entries| unsafe {
        vgPlain_printf("rs_trace_put offset %lld data %08llx\n\0".as_ptr() as *const c_char, put_offset, data);
    });
}

#[no_mangle]
pub extern "C" fn rs_trace_put_just_shadow(put_offset: vg_ulong, shadow_data: vg_ulong) {
   unsafe {
        if shadow_data != 0 {
            vgPlain_printf(
                b"rs_trace_put_just_shadow offset: %lld shadow_data: %d \n\0".as_ptr() as *const c_char,
		put_offset,
		shadow_data
            );
           }
   }
}


#[no_mangle]
pub extern "C" fn rs_trace_puti(ix: vg_ulong, bias: vg_ulong, data: vg_ulong, shadow_ix: vg_ulong, shadow_data: vg_ulong) {
   unsafe {
        if shadow_ix != 0 || shadow_data != 0 {
            vgPlain_printf(
                b"rs_trace_puti shadow_ix: %d shadow_data: %d \n\0".as_ptr() as *const c_char,
                shadow_ix,
		shadow_data
            );
           }
   }

   if_tracked_then(data as vg_addr, |tag| unsafe {
         vgPlain_printf(
            b"rs_trace_puti data %08llx shadow_data: %08lld has tag %d\n\0".as_ptr() as *const c_char,
            data,
            shadow_data,
            tag.0,
            );
      });

   if_has_stack_then(data as vg_addr, |entries| unsafe {
        vgPlain_printf("rs_trace_puti %08llx\n\0".as_ptr() as *const c_char, data);
    });
}

#[no_mangle]
pub extern "C" fn rs_trace_puti_just_shadow(ix: vg_ulong, bias: vg_ulong, shadow_ix: vg_ulong, shadow_data: vg_ulong) {
   unsafe {
        if shadow_ix != 0 || shadow_data != 0 {
            vgPlain_printf(
                b"rs_trace_puti shadow_ix: %d shadow_data: %d \n\0".as_ptr() as *const c_char,
                shadow_ix,
		shadow_data
            );
           }
   }
}

#[no_mangle]
pub extern "C" fn rs_shadow_rdtmp(tmp: vg_long) -> vg_long {
    if tmp > 200 {
        unsafe {
            vgPlain_printf(
                "hello from rs_shadow_rdtmp %lld\n\0".as_ptr() as *const c_char,
                tmp,
            );
        }
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_qop(op: vg_long) -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf(
            "hello from rs_shadow_qop %lld\n\0".as_ptr() as *const c_char,
            op,
        );
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_triop(op: vg_long) -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf(
            "hello from rs_shadow_triop %lld\n\0".as_ptr() as *const c_char,
            op,
        );
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_binop(op: vg_long) -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf(
            "hello from rs_shadow_binop %lld\n\0".as_ptr() as *const c_char,
            op,
        );
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_unop(op: vg_long) -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf(
            "hello from rs_shadow_unop %lld\n\0".as_ptr() as *const c_char,
            op,
        );
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_load(addr: vg_long, s1: vg_long) -> vg_long {
    unsafe {
        if_tracked_then(addr as vg_addr, |tag| unsafe {
            vgPlain_printf(
                b"rs_shadow_load addr %08llx s1: %08lld has tag %d\n\0".as_ptr() as *const c_char,
                addr,
                s1,
                tag.0,
            );
        });
        if_has_stack_then(addr as vg_addr, |stack| unsafe {
            vgPlain_printf(
                b"rs_shadow_load addr %08llx s1: %08lld has stack len: %d\n\0".as_ptr()
                    as *const c_char,
                addr,
                s1,
                stack.len(),
            );
        });
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_const() -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf("hello from rs_shadow_const\n\0".as_ptr() as *const c_char);
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_ite(cond: vg_long, s1: vg_long, s2: vg_long, s3: vg_long) -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf(
            "hello from rs_shadow_ite %lld\n\0".as_ptr() as *const c_char,
            cond,
        );
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_get(offset: vg_long, ty: vg_long) -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf(
            "hello from rs_shadow_get %lld\n\0".as_ptr() as *const c_char,
            offset,
        );
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_geti() -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf("hello from rs_shadow_geti\n\0".as_ptr() as *const c_char);
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_ccall() -> vg_long {
    #[cfg(not_now)]
    unsafe {
        vgPlain_printf("hello from rs_shadow_ccall\n\0".as_ptr() as *const c_char);
    }
    return 0;
}
