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

use self::vex_ir::IROp;

mod vex_ir;

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
    fn vgPlain_umsg(format: *const c_char, ...) -> u32;
}

#[no_mangle]
pub extern "C" fn hello_world(
    _printn: extern "C" fn(*const c_char, n: usize) -> usize,
    _printi: extern "C" fn(i: i32) -> usize,
    _printu: extern "C" fn(u: u32) -> usize,
) {
    let msg: &[u8] = b"Hello world (from `rs_hello/src/lib.rs`)!\n\0";
    unsafe { vgPlain_printf(msg.as_ptr() as *const c_char, msg.len()) };

    // A Vec sanity check, because if the allocator stops working then
    // there's little point in trying to do so much of this in Rust.
    let mut v = Vec::new();
    v.push(0);
    v.push(1);
    v.push(2);
    let end = v.pop().unwrap();
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

#[derive(Copy, Clone, PartialEq, Eq)]
struct Tag(u64);

impl Tag {
    fn next(self) -> Tag {
        Tag(self.0 + 1)
    }
}

static mut COUNTER: Tag = Tag(0);

#[derive(Copy, Clone, PartialEq, Eq)]
enum Item {
    Unique(Tag),
}

impl Item {
    fn num(&self) -> u64 {
        match *self {
            Item::Unique(Tag(val)) => val,
        }
    }
}

// FIXME: Need to more clearly distinguish between addresses and
// shadowing of values. I.e. the tag here needs to be attached to the
// location where an address itself is being stored, and needs to flow
// along with the address as it is copied from place to place.
static mut TRACKED_ADDRS: Vec<(vg_addr, Tag)> = Vec::new();
static mut TRACKED_TEMPS: Vec<(vg_uint, Tag)> = Vec::new();
// "GREG" is "Guest Register", i.e. the emulated registers.
static mut TRACKED_GREGS: Vec<(vg_ulong, Tag)> = Vec::new();

static mut STACKS: Vec<(vg_addr, Vec<Item>)> = Vec::new();

// FIXME UGLY HACK
// this is a big bad hack: I haven't managed to connect up
// the client request return point into the rest of the
// data-flow of the krabcake-rewritten code. So for now,
// use a one-length event queue that each memory operation
// that I *have* instrumented will check, and will process
// the relevant event if it sees the corresponding memory
// location.

#[derive(Copy, Clone)]
struct SbEvent { kind: SbEventKind, stash: vg_addr, borrow: vg_addr, tag: Tag }
fn SbEvent(kind: SbEventKind, stash: vg_addr, borrow: vg_addr, tag: Tag) -> SbEvent {
    SbEvent { kind, stash, borrow, tag}
}
static mut STACKED_BORROW_EVENT: Option<SbEvent> = None;

const PRINT_MSG: bool = false;

macro_rules! msg {
    ($x: literal) => { msg!($x,) };
    ($x: literal, $($arg: expr $(,)?),*) => {{
        let x: &[u8] = $x;
        assert!(x.last() == Some(&b'\0'));
        if PRINT_MSG { vgPlain_printf(x.as_ptr() as *const c_char, $($arg),*); }
    }};
}

// This is the same as msg for now; I just wanted an easy way
// to disable the msg's in the future while keeping the alerts.
macro_rules! alert {
    ($x: literal) => { msg!($x,) };
    ($x: literal, $($arg: expr $(,)?),*) => {{
        let x: &[u8] = $x;
        assert!(x.last() == Some(&b'\0'));
        vgPlain_umsg(x.as_ptr() as *const c_char, $($arg),*);
    }};
}

unsafe fn print_stacked_borrow_event(event: SbEvent) {
    msg!(
        b"SbEvent(kind: %s, stash: 0x%08llx, borrow: 0x%08llx, tag: %d)\0",
        (event.kind).c_str(),
        event.stash,
        event.borrow,
        (event.tag).0,
    );
}

unsafe fn if_sb_event_queued_print(before: impl FnOnce(), after: impl FnOnce()) {
    if let Some(event) = STACKED_BORROW_EVENT {
        before();
        print_stacked_borrow_event(event);
        after();
    }
}

#[derive(Copy, Clone)]
enum SbEventKind {
    BorrowMut = 0x2000,
    BorrowShr,
    AsRaw,
    AsBorrowMut,
    AsBorrowShr,
    RetagFnPrologue,
    RetagAssign,
    RetagRaw,
}

impl SbEventKind {
    fn c_str(&self) -> *const c_char {
        (match *self {
            SbEventKind::BorrowMut => b"BorrowMut\0".as_ptr(),
            SbEventKind::BorrowShr => b"BorrowShr\0".as_ptr(),
            SbEventKind::AsRaw => b"AsRaw\0".as_ptr(),
            SbEventKind::AsBorrowMut => b"AsBorrowMut\0".as_ptr(),
            SbEventKind::AsBorrowShr => b"AsBorrowShr\0".as_ptr(),
            SbEventKind::RetagFnPrologue => b"RetagFnPrologue\0".as_ptr(),
            SbEventKind::RetagAssign => b"RetagAssign\0".as_ptr(),
            SbEventKind::RetagRaw => b"RetagRaw\0".as_ptr(),
        }) as *const c_char
    }
}

fn if_greg_tracked_then<T>(greg: vg_ulong, process_tag: impl FnOnce(Tag) -> T) -> Option<T> {
    unsafe {
        for entry in TRACKED_GREGS.iter().rev() {
            if entry.0 == greg {
                return Some(process_tag(entry.1));
            }
        }
    }
    None
}

fn if_temp_tracked_then<T>(temp: vg_uint, process_tag: impl FnOnce(Tag) -> T) -> Option<T> {
    unsafe {
        for entry in TRACKED_TEMPS.iter().rev() {
            if entry.0 == temp {
                return Some(process_tag(entry.1));
            }
        }
    }
    None
}

fn if_addr_tracked_then<T>(addr: vg_addr, process_tag: impl FnOnce(Tag) -> T) -> Option<T> {
    unsafe {
        for entry in TRACKED_ADDRS.iter().rev() {
            if entry.0 == addr {
                return Some(process_tag(entry.1));
            }
        }
    }
    None
}

fn if_addr_has_stack_then<T>(
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

// The (new) protocol is: the borrowing address is stored
// *in* the memory location at *arg[0].
#[no_mangle]
pub extern "C" fn rs_client_request_borrow_mut(
    thread_id: c_uint,
    arg: *const *const c_size_t,
    ret: *mut c_size_t,
) -> bool {
    unsafe {
        vgPlain_dmsg(
            "lib.rs: handle client request BORROW_MUT 0x%llx\n\0".as_ptr() as *const c_char,
            *arg.offset(1),
            ret,
        );
        COUNTER = COUNTER.next();
        let stash_addr = *arg.offset(1);
        let borrowing_addr = *stash_addr as vg_addr;
        let stash_addr = stash_addr as vg_addr;
        let lookup = if_addr_has_stack_then(borrowing_addr, |entries| {
            entries.push(Item::Unique(COUNTER));
        });
        if lookup.is_none() {
            let mut v = Vec::new();
            v.push(Item::Unique(COUNTER));
            STACKS.push((borrowing_addr, v));
        }
        TRACKED_ADDRS.push((stash_addr, COUNTER));
        assert!(STACKED_BORROW_EVENT.is_none());
        STACKED_BORROW_EVENT = Some(SbEvent(SbEventKind::BorrowMut, stash_addr, borrowing_addr, COUNTER));
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

unsafe fn check_use_1(addr: vg_addr, shadow_addr: vg_ulong) {
    assert!(shadow_addr != 0);

    // Confim that this access is legal; i.e. that:
    //
    // 1. this memory location has an associated stack
    //
    // 2. the associated stack has a Unique(T) entry, where T
    //    is the tag (i.e. the shadow value)
    //
    // 3. as a side-effect of the access, we must pop all entries that
    //    lay above the aforementioned Unique(T).
    let lookup = if_addr_has_stack_then(addr, |stack| {
        let before_len = stack.len();
        while let Some(last) = stack.last() {
            msg!(
                b"tag search seeking %d and saw %d\n\0",
                shadow_addr,
                last.num()
            );
            if last == &Item::Unique(Tag(shadow_addr)) {
                let after_len = stack.len();
                return (true, before_len, after_len);
            } else {
                stack.pop();
            }
        }
        let after_len = stack.len();
        (false, before_len, after_len)
    });
    match lookup {
        None => {
            alert!(b"ALERT no stack for address 0x%08llx even though we are accessing it via pointer with tag %d\n\0",
			   addr,
			   shadow_addr);
        }
        Some((false, _, _)) => {
            alert!(b"ALERT could not find tag in stack for address 0x%08llx even though we are accesing it via pointer with tag %d\n\0",
			   addr,
			   shadow_addr);
        }
        Some((true, before_len, after_len)) => {
            msg!(b"found tag in stack for address 0x%08llx when accessing via pointer with tag %d; stack len before: %d after: %d\n\0",
			 addr,
			 shadow_addr,
			 before_len,
			 after_len);
        }
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_cas(addr: vg_addr) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_cas sb event \0"),
            || msg!(b" addr: 0x%08llx \n\0", addr),
        );
    }
}
#[no_mangle]
pub extern "C" fn rs_trace_storeg(guard: vg_long, addr: vg_addr, size: vg_size_t) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_storeg sb event \0"),
            || msg!(b" guard: %d addr: 0x%08llx \n\0", guard, addr),
        );
    }
}
#[no_mangle]
pub extern "C" fn rs_trace_loadg(
    guard: vg_long,
    addr: vg_addr,
    size: vg_size_t,
    widened_size: vg_size_t,
) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_loadg sb event \0"),
            || msg!(b" guard: %d addr: 0x%08llx \n\0", guard, addr),
        );
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_wrtmp(lhs_tmp: vg_uint, s1: vg_long) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_wrtmp sb event \0"),
            || msg!(b" lhs_tmp: %d s1: %d \n\0", lhs_tmp, s1),
        );
    }
    unsafe {
        if s1 != 0 {
            msg!(b"rs_trace_wrtmp lhs_tmp: %u s1: %d\n\0", lhs_tmp, s1,);
            TRACKED_TEMPS.push((lhs_tmp, Tag(s1 as u64)));
        } else {
            TRACKED_TEMPS.retain(|entry| entry.0 != lhs_tmp);
        }
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_store(
    addr: vg_addr,
    data: vg_ulong,
    size: vg_size_t,
    shadow_addr: vg_ulong,
    shadow_data: vg_ulong,
) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_store sb event \0"),
            || {
                msg!(
                    b" addr: 0x%08llx data: %d (0x%08llx) shadow_addr: %d shadow_data: %d \n\0",
                    addr,
                    data,
                    data,
                    shadow_addr,
                    shadow_data,
                )
            },
        );
    }
    if_addr_tracked_then(addr as vg_addr, |tag| unsafe {
        msg!(
            b"rs_trace_store tracked addr 0x%08llx shadow_addr: %d shadow_data: %d has tag %d\n\0",
            addr,
            shadow_addr,
            shadow_data,
            tag.0,
        );
    });

    if_addr_tracked_then(data as vg_addr, |tag| unsafe {
        msg!(
            b"rs_trace_store tracked data %d (0x%08llx) shadow_addr: %d shadow_data: %d has tag %d\n\0",
            data,
            data,
            shadow_addr,
            shadow_data,
            tag.0,
        );
    });

    if_addr_has_stack_then(addr, |stack| unsafe {
        msg!(
            b"rs_trace_store has stack on addr 0x%08llx has stack len: %d\n\0",
            addr,
            stack.len(),
        );
    });

    unsafe {
        if shadow_addr != 0 || shadow_data != 0 {
            msg!(
                b"rs_trace_store non-trivial shadow on addr: 0x%llx data: %d (0x%08llx) shadow_addr: %d shadow_data: %d \n\0",
                addr,
                data,
                data,
                shadow_addr,
                shadow_data,
            );
        }

        if shadow_addr != 0 {
            // A non-trivial shadow on the address means this was a
            // *tagged* pointer; need to confirm this access is legal
            // (and update the stack to reflect a use via this tag).
            check_use_1(addr, shadow_addr);
        }

        if shadow_data != 0 {
            msg!(
                b"rs_trace_store propagating shadow data into *addr: 0x%08llx shadow_data: %d\n\0",
                addr,
                shadow_data,
            );
            TRACKED_ADDRS.push((addr, Tag(shadow_data as u64)));
        } else {
            TRACKED_ADDRS.retain(|a| a.0 != addr);
        }
    }
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
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_store128 sb event \0"),
            || msg!(b" addr: 0x%08llx  \n\0", addr),
        );
    }
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
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_store256 sb event \0"),
            || msg!(b" addr: 0x%08llx \n\0", addr),
        );
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_llsc(addr: vg_addr) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_store sb event \0"),
            || msg!(b" addr: 0x%08llx \n\0", addr),
        );
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_put(put_offset: vg_ulong, data: vg_ulong, shadow_data: vg_ulong) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_put sb event \0"),
            || {
                msg!(
                    b" put_offset: %u data: %d (0x%08llx) shadow_data: %d\n\0",
                    put_offset,
                    data,
                    data,
                    shadow_data,
                )
            },
        );
    }
    unsafe {
        if shadow_data != 0 {
            msg!(
                b"rs_trace_put non-trivial shadow on data at offset: %lld data: %d (0x%08llx) shadow_data: %d \n\0",
                put_offset,
                data,
                data,
                shadow_data,
            );
            TRACKED_GREGS.push((put_offset, Tag(shadow_data as u64)));
        } else {
            TRACKED_GREGS.retain(|entry| entry.0 != put_offset);
        }
    }

    if_addr_tracked_then(data as vg_addr, |tag| unsafe {
        msg!(
            b"rs_trace_put tracked data offset %lld data %d (0x%08llx) shadow_data: %d has tag %d\n\0",
            put_offset,
            data,
            data,
            shadow_data,
            tag.0,
        );
    });

    if_addr_has_stack_then(data as vg_addr, |entries| unsafe {
        msg!(
            b"rs_trace_put has stack on data offset %lld data %d (0x%08llx)\n\0",
            put_offset,
            data,
            data,
        );
    });
}

#[no_mangle]
pub extern "C" fn rs_trace_put_just_shadow(put_offset: vg_ulong, shadow_data: vg_ulong) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_put_just_shadow sb event \0"),
            || {
                msg!(
                    b" put_offset: %u shadow_data: %d\n\0",
                    put_offset,
                    shadow_data,
                )
            },
        );
    }
    unsafe {
        if shadow_data != 0 {
            msg!(
                b"rs_trace_put_just_shadow offset: %lld shadow_data: %d \n\0",
                put_offset,
                shadow_data,
            );
        }
    }
}

#[no_mangle]
pub extern "C" fn rs_trace_puti(
    ix: vg_ulong,
    bias: vg_ulong,
    data: vg_ulong,
    shadow_ix: vg_ulong,
    shadow_data: vg_ulong,
) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_puti sb event \0"),
            || msg!(b" ix: %u bias: %u \n\0", ix, bias),
        );
    }
    unsafe {
        if shadow_ix != 0 || shadow_data != 0 {
            msg!(
                b"rs_trace_puti shadow_ix: %d shadow_data: %d \n\0",
                shadow_ix,
                shadow_data,
            );
        }
    }

    if_addr_tracked_then(data as vg_addr, |tag| unsafe {
        msg!(
            b"rs_trace_puti data %d (0x%08llx) shadow_data: %d has tag %d\n\0",
            data,
            data,
            shadow_data,
            tag.0,
        );
    });

    if_addr_has_stack_then(data as vg_addr, |entries| unsafe {
        msg!(b"rs_trace_puti data %d (0x%08llx)\n\0", data, data,);
    });
}

#[no_mangle]
pub extern "C" fn rs_trace_puti_just_shadow(
    ix: vg_ulong,
    bias: vg_ulong,
    shadow_ix: vg_ulong,
    shadow_data: vg_ulong,
) {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_trace_puti_just_shadow sb event \0"),
            || msg!(b" ix: %u bias: %u \n\0", ix, bias),
        );
    }
    unsafe {
        if shadow_ix != 0 || shadow_data != 0 {
            msg!(
                b"rs_trace_puti shadow_ix: %d shadow_data: %d \n\0",
                shadow_ix,
                shadow_data,
            );
        }
    }
}

#[no_mangle]
pub extern "C" fn rs_shadow_rdtmp(tmp: vg_long) -> vg_long {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_rdtmp sb event \0"),
            || msg!(b" tmp: %d \n\0", tmp),
        );
    }
    unsafe {
        if let Some(tag) = if_temp_tracked_then(tmp as vg_uint, |tag| tag) {
            msg!(
                b"rs_shadow_rdtmp tracked tmp: %d has tag: %d\n\0",
                tmp,
                tag.0,
            );
            return tag.0 as vg_long;
        }
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_qop(
    op: vg_long,
    s1: vg_long,
    s2: vg_long,
    s3: vg_long,
    s4: vg_long,
) -> vg_long {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_qop sb event \0"),
            || {
                if PRINT_MSG { ppIROp(op); }
                msg!(b" \n\0");
            },
        );
    }
    if (s1 + s2 + s3 + s4) != 0 {
        unsafe {
            msg!(b"hello from rs_shadow_qop \0");
            if PRINT_MSG { ppIROp(op); }
            msg!(
                b" (0x%llx) s1: %d s2: %d s3: %d s4: %d\n\0",
                op,
                s1,
                s2,
                s3,
                s4,
            );
        }
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_triop(op: vg_long, s1: vg_long, s2: vg_long, s3: vg_long) -> vg_long {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_triop sb event \0"),
            || {
                if PRINT_MSG { ppIROp(op); }
                msg!(b" \n\0");
            },
        );
    }
    if (s1 + s2 + s3) != 0 {
        unsafe {
            msg!(b"hello from rs_shadow_triop \0");
            if PRINT_MSG { ppIROp(op); }
            msg!(b"0x%llx s1: %d s2: %d s3: %d\n\0", op, s1, s2, s3,);
        }
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_binop(op: vg_long, s1: vg_long, s2: vg_long) -> vg_long {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_binop sb event \0"),
            || {
                if PRINT_MSG { ppIROp(op); }
                msg!(b" \n\0");
            },
        );
    }
    if (s1 + s2) != 0 {
        unsafe {
            msg!(b"hello from rs_shadow_binop \0");
            if PRINT_MSG { ppIROp(op); }
            msg!(b" (0x%llx) s1: %d s2: %d\n\0", op, s1, s2,);
        }
    }
    return 0;
}

extern "C" {
    fn ppIROp(opcode: vg_long);
}

#[no_mangle]
pub extern "C" fn rs_shadow_unop(op: vg_long, s1: vg_long) -> vg_long {
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_unop sb event \0"),
            || {
                if PRINT_MSG { ppIROp(op); }
                msg!(b" \n\0");
            },
        );
    }
    if s1 != 0 {
        unsafe {
            msg!(b"hello from rs_shadow_unop \0");
            if PRINT_MSG { ppIROp(op); }
            msg!(b" (0x%llx) s1: %d\n\0", op, s1);
        }

        if IROp::is_widening(op) {
            // FIXME: why are we reading a byte here on our shadowed temp?
            return s1;
        }
        if IROp::is_narrowing(op) {
            // FIXME: is this a good idea either? At this point am
            // just grasping at straws to see shadow state flow from
            // one end to the other.
            return s1;
        }
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_load(addr: vg_long, s1: vg_long) -> vg_long {
    let memory_shadow_value_core;
    let memory_shadow_value_hack;
    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_load sb event \0"),
            || msg!(b" addr: 0x%08llx \n\0", addr),
        );
    }
    unsafe {
        if s1 != 0 {
            msg!(
                b"rs_shadow_load non-trivial shadow for addr 0x%08llx s1: %d\n\0",
                addr,
                s1,
            );
        }
        if_addr_tracked_then(addr as vg_addr, |tag| unsafe {
            msg!(
                b"rs_shadow_load tracked addr 0x%08llx s1: %d has tag %d\n\0",
                addr,
                s1,
                tag.0,
            );
        });
        if_addr_has_stack_then(addr as vg_addr, |stack| unsafe {
            msg!(
                b"rs_shadow_load addr 0x%08llx s1: %d has stack len: %d\n\0",
                addr,
                s1,
                stack.len(),
            );
        });

        if let Some(event) = STACKED_BORROW_EVENT {
            if event.stash == addr as vg_addr {
                let s0 = event.tag.0;
                msg!(b"rs_shadow_load 0x%08llx setting hack value for stashed tag %d\n\0", addr, s0);
                STACKED_BORROW_EVENT = None;
                memory_shadow_value_hack = s0 as vg_long;
            } else {
                memory_shadow_value_hack = 0;
            }
        } else {
            memory_shadow_value_hack = 0;
        }

        if s1 != 0 {
            check_use_1(addr as vg_addr, s1 as u64);
        }
    }

    memory_shadow_value_core = if_addr_tracked_then(addr as vg_addr, |tag| tag.0 as vg_long).unwrap_or(0);

    // When we remove the STACKED_BORROW_EVENT hack, all of this will be
    // replaced with just returning memory_shadow_value_core
    if (memory_shadow_value_core != 0) || (memory_shadow_value_hack != 0) {
        unsafe {
            msg!(b"rs_shadow_load 0x%08llx shadow core: %d hack: %d\n\0",
                 addr,
                 memory_shadow_value_core,
                 memory_shadow_value_hack);
        }
    }
    assert_eq!(memory_shadow_value_core, memory_shadow_value_hack);

    return memory_shadow_value_core;
}

#[no_mangle]
pub extern "C" fn rs_shadow_const() -> vg_long {
    unsafe {
        if_sb_event_queued_print(|| msg!(b"rs_shadow_const sb event \0"), || msg!(b" \n\0"));
    }
    #[cfg(not_now)]
    unsafe {
        msg!(b"hello from rs_shadow_const\n\0");
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_ite(cond: vg_long, s1: vg_long, s2: vg_long, s3: vg_long) -> vg_long {
    unsafe {
        if_sb_event_queued_print(|| msg!(b"rs_shadow_ite sb event \0"), || msg!(b" \n\0"));
    }
    let ret = if cond != 0 { s2 } else { s3 };
    unsafe {
        if ret != 0 {
            msg!(
                b"hello from rs_shadow_ite %lld s1: %d s2: %d s3: %d ret: %d\n\0",
                cond,
                s1,
                s2,
                s3,
                ret,
            );
        }
    }
    return ret;
}

#[no_mangle]
pub extern "C" fn rs_shadow_get(offset: vg_long, ty: vg_long) -> vg_long {
    let mut ret = 0;

    unsafe {
        if_sb_event_queued_print(
            || msg!(b"rs_shadow_get sb event \0"),
            || msg!(b" offset: %d \n\0", offset),
        );
    }

    if let Some(tag) = if_greg_tracked_then(offset as vg_ulong, |tag| tag) {
        unsafe {
            msg!(b"hello from rs_shadow_get %lld tag: %d\n\0", offset, tag.0,);
        }
        ret = tag.0 as vg_long;
    }
    return ret;
}

#[no_mangle]
pub extern "C" fn rs_shadow_geti() -> vg_long {
    unsafe {
        if_sb_event_queued_print(|| msg!(b"rs_shadow_geti sb event \0"), || msg!(b" \n\0"));
    }
    #[cfg(not_now)]
    unsafe {
        msg!(b"hello from rs_shadow_geti\n\0");
    }
    return 0;
}

#[no_mangle]
pub extern "C" fn rs_shadow_ccall() -> vg_long {
    unsafe {
        if_sb_event_queued_print(|| msg!(b"rs_shadow_ccall sb event \0"), || msg!(b" \n\0"));
    }
    #[cfg(not_now)]
    unsafe {
        msg!(b"hello from rs_shadow_ccall\n\0");
    }
    return 0;
}
