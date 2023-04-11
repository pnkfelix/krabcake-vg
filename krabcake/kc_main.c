
/*--------------------------------------------------------------------*/
/*--- Krabcake: The Rust-validating Valgrind tool.       kc_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Krabcake, the Rust-validating Valgrind tool,
   which attempts to detect undefined behavior in Rust programs.

   Copyright (C) 2023 Felix S Klock II
      pnkfelix@pnkfx.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_tooliface.h"

#include "kc_include.h"
#include "krabcake.h" /* for client requests */

/* For code instrumentation */
#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"

#include <stdint.h>

// Paranoia:  perf critical that requested inlining occurs; try extra hard.
#define INLINE    inline __attribute__((always_inline))


/*------------------------------------------------------------*/
/*--- Fast-case knobs                                      ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Comments on the origin tracking implementation       ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- V bits and A bits                                    ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Basic A/V bitmap representation.                     ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- shadow state tracking                                ---*/
/*------------------------------------------------------------*/

/* This is all inspired from basic infrastructure presented in MemCheck.

    |   33222222222211111111110000000000
bit |   10987654321098765432109876543210
        ================================
        PPPPPPPPPPPPPPPPssssssssssssssss
        ~~~~~~~~~~~~~~~~
          primary index ~~~~~~~~~~~~~~~~
                         secondary index
    
    |   6666555555555544444444443333333333222222222211111111110000000000
bit |   3210987654321098765432109876543210987654321098765432109876543210
        ================================================================
        zzzzzzzzzzzzzzzzzzzzzzzzzzzzPPPPPPPPPPPPPPPPPPPPssssssssssssssss
        ~~~~~~~~~~~~~~~~~~~~~~~~~~~~
        slow index to sparse aux     ~~~~~~~~~~~~~~~~~~~~
         (usually zero, hopefully)      primary index    ~~~~~~~~~~~~~~~~
                                                         secondary index
*/

#if VG_WORDSIZE == 4

/* cover the entire address space */
#  define N_PRIMARY_BITS  16

#else

/* Just handle the first 128G fast and the rest via auxiliary primaries. */
#  define N_PRIMARY_BITS  21

#endif

/* Do not change this (must remain as power of 2).
   Only change N_PRIMARY_BITS above. */
#define N_PRIMARY_MAP  ( ((UWord)1) << N_PRIMARY_BITS)

/* Do not change this. */
#define MAX_PRIMARY_ADDRESS (Addr)((((Addr)65536) * N_PRIMARY_MAP)-1)

/* --------------- Load/store slow cases. --------------- */

static
__attribute__((noinline))
void kc_LOADV_128_or_256_slow ( /*OUT*/ULong* res,
                                Addr a, SizeT nBits, Bool bigendian )
{
   ULong  pessim[4];     /* only used when p-l-ok=yes */
   SSizeT szB            = nBits / 8;
   SSizeT szL            = szB / 8;  /* Size in Longs (64-bit units) */
   SSizeT j;
   /* Code below assumes load size is a power of two and at least 64
      bits. */
   tl_assert((szB & (szB-1)) == 0 && szL > 0);

   // XXX FIXME this needs to do a lookup against the maps!
   // XXX but for now we can just fall back to 0 (defined, no extra info)
   for (j = 0; j < szL; j++) {
      res[j]  = 0;
   }

   // tl_assert(0); // unimplemented
   return;
}

static
__attribute__((noinline))
__attribute__((used))
VG_REGPARM(3)
ULong kc_LOADVn_slow ( Addr a, SizeT nBits, Bool bigendian );

static
__attribute__((noinline))
__attribute__((used))
VG_REGPARM(3) /* make sure we're using a fixed calling convention, since
                 this function may get called from hand written assembly. */
ULong kc_LOADVn_slow ( Addr a, SizeT nBits, Bool bigendian )
{
   // XXX FIXME: this needs to do a lookup against the maps!
   // XXX but for now we can just fall back to 0 (defined, no extra info)
   return 0;
   // tl_assert(0); // unimplemented
}

static
__attribute__((noinline))
void kc_STOREVn_slow ( Addr a, SizeT nBits, ULong vbytes, Bool bigendian )
{
   tl_assert(0); // unimplemented
}


/*------------------------------------------------------------*/
/*--- Setting permissions over address ranges.             ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Origin tracking stuff - cache basics                 ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Aligned fast case permission setters,                ---*/
/*--- for dealing with stacks                              ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Stack pointer adjustment                             ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Checking memory                                      ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Memory event handlers                                ---*/
/*------------------------------------------------------------*/

static
void KC_(pre_mem_read) ( CorePart part, ThreadId tid, const HChar* s,
                         Addr base, SizeT size )
{
   // VG_(dmsg)("kc_pre_mem_read %s base=%p size=%x (%d)\n", s, base, size, size);
}

static
void KC_(pre_mem_read_asciiz) ( CorePart part, ThreadId tid,
                                const HChar* s, Addr str )
{
   // VG_(dmsg)("kc_pre_mem_read_asciiz\n");
}

static
void KC_(pre_mem_write) ( CorePart part, ThreadId tid, const HChar* s,
                          Addr base, SizeT size )
{
   // VG_(dmsg)("kc_pre_mem_write\n");
}

static
void KC_(post_mem_write) ( CorePart part, ThreadId tid, Addr a, SizeT len )
{
   // VG_(dmsg)("kc_post_mem_write\n");
}

/*------------------------------------------------------------*/
/*--- Register event handlers                              ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Register-memory event handlers                       ---*/
/*------------------------------------------------------------*/

static void KC_(copy_mem_to_reg) ( CorePart part, ThreadId tid, Addr a,
                                   PtrdiffT guest_state_offset, SizeT size )
{
   VG_(dmsg)("kc_copy_mem_to_reg\n");
}

static void KC_(copy_reg_to_mem) ( CorePart part, ThreadId tid,
                                   PtrdiffT guest_state_offset, Addr a,
                                   SizeT size )
{
   VG_(dmsg)("kc_copy_reg_to_mem\n");
}


/*------------------------------------------------------------*/
/*--- Some static assertions                               ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Functions called directly from generated code:       ---*/
/*--- Load/store handlers.                                 ---*/
/*------------------------------------------------------------*/


/*------------------------------------------------------------*/
/*--- LOADV256 and LOADV128                                ---*/
/*------------------------------------------------------------*/

// FIXME: these methods have optimized variations that pnkfelix has just
// outright deleted in the interest of getting prototype up and running.

static INLINE
void kc_LOADV_128_or_256 ( /*OUT*/ULong* res,
                           Addr a, SizeT nBits, Bool isBigEndian )
{
   PROF_EVENT(MCPE_LOADV_128_OR_256);
   kc_LOADV_128_or_256_slow( res, a, nBits, isBigEndian );
   return;
}

VG_REGPARM(2) void KC_(helperc_LOADV256be) ( /*OUT*/V256* res, Addr a )
{
   kc_LOADV_128_or_256(&res->w64[0], a, 256, True);
}
VG_REGPARM(2) void KC_(helperc_LOADV256le) ( /*OUT*/V256* res, Addr a )
{
   kc_LOADV_128_or_256(&res->w64[0], a, 256, False);
}

VG_REGPARM(2) void KC_(helperc_LOADV128be) ( /*OUT*/V128* res, Addr a )
{
   kc_LOADV_128_or_256(&res->w64[0], a, 128, True);
}
VG_REGPARM(2) void KC_(helperc_LOADV128le) ( /*OUT*/V128* res, Addr a )
{
   kc_LOADV_128_or_256(&res->w64[0], a, 128, False);
}

/*------------------------------------------------------------*/
/*--- LOADV64                                              ---*/
/*------------------------------------------------------------*/


static INLINE
ULong kc_LOADV64 ( Addr a, Bool isBigEndian )
{
   PROF_EVENT(MCPE_LOADV64);
   return kc_LOADVn_slow( a, 64, isBigEndian );
}

// Generic for all platforms
VG_REGPARM(1) ULong KC_(helperc_LOADV64be) ( Addr a )
{
   return kc_LOADV64(a, True);
}

// FIXME Non-generic assembly for arm32-linux
// Generic for all platforms except {arm32,x86}-linux and x86-solaris
VG_REGPARM(1) ULong KC_(helperc_LOADV64le) ( Addr a )
{
   return kc_LOADV64(a, False);
}


/*------------------------------------------------------------*/
/*--- STOREV64                                             ---*/
/*------------------------------------------------------------*/


static INLINE
void kc_STOREV64 ( Addr a, ULong vbits64, Bool isBigEndian )
{
   PROF_EVENT(MCPE_STOREV64);
   kc_STOREVn_slow( a, 64, vbits64, isBigEndian );
}

VG_REGPARM(1) void KC_(helperc_STOREV64be) ( Addr a, ULong vbits64 )
{
   kc_STOREV64(a, vbits64, True);
}
VG_REGPARM(1) void KC_(helperc_STOREV64le) ( Addr a, ULong vbits64 )
{
   kc_STOREV64(a, vbits64, False);
}

/*------------------------------------------------------------*/
/*--- LOADV32                                              ---*/
/*------------------------------------------------------------*/


static INLINE
UWord kc_LOADV32 ( Addr a, Bool isBigEndian )
{
   PROF_EVENT(MCPE_LOADV32);
   return (UWord)kc_LOADVn_slow( a, 32, isBigEndian );
}

// Generic for all platforms
VG_REGPARM(1) UWord KC_(helperc_LOADV32be) ( Addr a )
{
   return kc_LOADV32(a, True);
}

// FIXME memcheck uses Non-generic assembly for arm32-linux

// Generic for all platforms except {arm32,x86}-linux and x86-solaris
VG_REGPARM(1) UWord KC_(helperc_LOADV32le) ( Addr a )
{
   return kc_LOADV32(a, False);
}

/*------------------------------------------------------------*/
/*--- STOREV32                                             ---*/
/*------------------------------------------------------------*/


static INLINE
void kc_STOREV32 ( Addr a, UWord vbits32, Bool isBigEndian )
{
   PROF_EVENT(MCPE_STOREV32);
   kc_STOREVn_slow( a, 32, (ULong)vbits32, isBigEndian );
}

VG_REGPARM(2) void KC_(helperc_STOREV32be) ( Addr a, UWord vbits32 )
{
   kc_STOREV32(a, vbits32, True);
}
VG_REGPARM(2) void KC_(helperc_STOREV32le) ( Addr a, UWord vbits32 )
{
   kc_STOREV32(a, vbits32, False);
}

/*------------------------------------------------------------*/
/*--- LOADV16                                              ---*/
/*------------------------------------------------------------*/


static INLINE
UWord kc_LOADV16 ( Addr a, Bool isBigEndian )
{
   PROF_EVENT(MCPE_LOADV16);
   return (UWord)kc_LOADVn_slow( a, 16, isBigEndian );
}

// Generic for all platforms
VG_REGPARM(1) UWord KC_(helperc_LOADV16be) ( Addr a )
{
   return kc_LOADV16(a, True);
}

// FIXME memcheck uses non-generic assembly for arm32-linux

// Generic for all platforms except {arm32,x86}-linux and x86-solaris
VG_REGPARM(1) UWord KC_(helperc_LOADV16le) ( Addr a )
{
   return kc_LOADV16(a, False);
}

/*------------------------------------------------------------*/
/*--- STOREV16                                             ---*/
/*------------------------------------------------------------*/


static INLINE
void kc_STOREV16 ( Addr a, UWord vbits16, Bool isBigEndian )
{
   PROF_EVENT(MCPE_STOREV16);
   kc_STOREVn_slow( a, 16, (ULong)vbits16, isBigEndian );
}


VG_REGPARM(2) void KC_(helperc_STOREV16be) ( Addr a, UWord vbits16 )
{
   kc_STOREV16(a, vbits16, True);
}
VG_REGPARM(2) void KC_(helperc_STOREV16le) ( Addr a, UWord vbits16 )
{
   kc_STOREV16(a, vbits16, False);
}

/*------------------------------------------------------------*/
/*--- LOADV8                                               ---*/
/*------------------------------------------------------------*/

/* Note: endianness is irrelevant for size == 1 */

// Non-generic assembly for arm32-linux
// Generic for all platforms except {arm32,x86}-linux and x86-solaris
VG_REGPARM(1)
UWord KC_(helperc_LOADV8) ( Addr a )
{
   PROF_EVENT(MCPE_LOADV8);
   return (UWord)kc_LOADVn_slow( a, 8, False/*irrelevant*/ );
}

/*------------------------------------------------------------*/
/*--- STOREV8                                              ---*/
/*------------------------------------------------------------*/


VG_REGPARM(2)
void KC_(helperc_STOREV8) ( Addr a, UWord vbits8 )
{
   PROF_EVENT(MCPE_STOREV8);
   kc_STOREVn_slow( a, 8, (ULong)vbits8, False/*irrelevant*/ );
}


/*------------------------------------------------------------*/
/*--- Functions called directly from generated code:       ---*/
/*--- Value-check failure handlers.                        ---*/
/*------------------------------------------------------------*/

VG_REGPARM(0)
void KC_(helperc_value_check0_fail_no_o) ( void ) {
   KC_(record_cond_error) ( VG_(get_running_tid)(), 0/*origin*/ );
}

VG_REGPARM(0)
void KC_(helperc_value_check1_fail_no_o) ( void ) {
   KC_(record_value_error) ( VG_(get_running_tid)(), 1, 0/*origin*/ );
}

VG_REGPARM(0)
void KC_(helperc_value_check4_fail_no_o) ( void ) {
   KC_(record_value_error) ( VG_(get_running_tid)(), 4, 0/*origin*/ );
}

VG_REGPARM(0)
void KC_(helperc_value_check8_fail_no_o) ( void ) {
   KC_(record_value_error) ( VG_(get_running_tid)(), 8, 0/*origin*/ );
}

VG_REGPARM(1)
void KC_(helperc_value_checkN_fail_no_o) ( HWord sz ) {
   KC_(record_value_error) ( VG_(get_running_tid)(), (Int)sz, 0/*origin*/ );
}

/*------------------------------------------------------------*/
/*--- Metadata get/set functions, for client requests.     ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Detecting leaked (unreachable) malloc'd blocks.      ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Initialisation                                       ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Sanity check machinery (permanently engaged)         ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Command line args                                    ---*/
/*------------------------------------------------------------*/


static Bool KC_(process_cmd_line_options) ( const HChar* arg )
{
   return True;
}

static void KC_(print_usage) ( void )
{
   VG_(printf)(
      "(none)\n"
      );
}

static void KC_(print_debug_usage) ( void )
{
   VG_(printf)(
"    (none)\n"
   );
}

/*------------------------------------------------------------*/
/*--- Client blocks                                        ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Client requests                                      ---*/
/*------------------------------------------------------------*/


static Bool KC_(handle_client_request) ( ThreadId tid, UWord* arg, UWord* ret )
{
   Bool  handled = False;

   if (!VG_IS_TOOL_USERREQ('K','C',arg[0]))
      return False;

   VG_(dmsg)("KC_(handle_client_request), dispatching client request code %llx\n", (ULong)arg[0]);

   switch(arg[0]) {
   case VG_USERREQ__BORROW_MUT: {
      VG_(dmsg)("KC_(handle_client_request), handle BORROW_MUT %llx (<- return value) %llx %llx %llx %llx\n",
                (ULong)arg[1], (ULong)arg[2], (ULong)arg[3], (ULong)arg[4], (ULong)arg[5]);
      *ret = arg[1];
      handled = True;
      break;
   }
   case VG_USERREQ__BORROW_SHR: {
      VG_(dmsg)("KC_(handle_client_request), handle BORROW_SHR");
      break;
   }
   case VG_USERREQ__AS_RAW: {
      VG_(dmsg)("KC_(handle_client_request), handle AS_RAW");
      break;
   }
   case VG_USERREQ__AS_BORROW_MUT: {
      VG_(dmsg)("KC_(handle_client_request), handle AS_BORROW_MUT");
      break;
   }
   case VG_USERREQ__AS_BORROW_SHR: {
      VG_(dmsg)("KC_(handle_client_request), handle AS_BORROW_SHR");
      break;
   }
   case VG_USERREQ__RETAG_FN_PROLOGUE: {
      VG_(dmsg)("KC_(handle_client_request), handle RETAG_FN_PROLOGUE");
      break;
   }
   case VG_USERREQ__RETAG_ASSIGN: {
      VG_(dmsg)("KC_(handle_client_request), handle RETAG_ASSIGN");
      break;
   }
   case VG_USERREQ__RETAG_RAW: {
      VG_(dmsg)("KC_(handle_client_request), handle RETAG_RAW");
      break;
   }
   case VG_USERREQ__INTRINSICS_ASSUME: {
      VG_(dmsg)("KC_(handle_client_request), handle INTRINSICS_ASSUME %llx %llx %llx %llx %llx\n",
                (ULong)arg[1], (ULong)arg[2], (ULong)arg[3], (ULong)arg[4], (ULong)arg[5]);
      handled = True;
      break;
   }
   default:
         VG_(message)(
            Vg_UserMsg,
            "Warning: unknown krabcake client request code %llx\n",
            (ULong)arg[0]
         );
         return False;
   }

   return handled;
}

/*------------------------------------------------------------*/
/*--- Crude profiling machinery.                           ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Origin tracking stuff                                ---*/
/*------------------------------------------------------------*/

/*--------------------------------------------*/
/*--- Origin tracking: load handlers       ---*/
/*--------------------------------------------*/

/*--------------------------------------------*/
/*--- Origin tracking: store handlers      ---*/
/*--------------------------------------------*/

/*--------------------------------------------*/
/*--- Origin tracking: sarp handlers       ---*/
/*--------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Setup and finalisation                               ---*/
/*------------------------------------------------------------*/


// declare the Rust function
extern void hello_world(
   unsigned (*printn)(char const *msg, unsigned len),
   unsigned (*printi)(int32_t i),
   unsigned (*printu)(uint32_t u));

static unsigned printi(int32_t i) {
   unsigned printed = VG_(printf)("%d", i);
   return printed;
}

static unsigned printu(uint32_t u) {
   unsigned printed = VG_(printf)("%u", u);
   return printed;
}

static unsigned printn(char const *s, unsigned limit) {
   // VG_(printf)("printn(s: `%s`, limit: %u)\n", s, limit);
   const unsigned BUF_LEN = 128;
   HChar buf[BUF_LEN+1];
   unsigned lim = limit;
   unsigned total_printed = 0;
   unsigned chunk;
   unsigned offset = 0;
   // Invariant: positive lim means offset does not run off of `s`.
   while (lim > 0 && (s+offset)[0] != '\0') {
      chunk = ((lim+1) < BUF_LEN) ? (lim+1) : BUF_LEN;

      // VG_(printf)("s+offset: `%s` limit: %u chunk: %u\n", s + offset, limit, chunk);

      // Notes: snprintf and vsnprintf write at most `size`
      // bytes *including* the terminating null byte that
      // they always include. Thus, this will print at most `chunk - 1`
      // bytes from the source string, which is why we use `lim + 1`
      // to initalize `chunk` above.
      signed sn_retval = VG_(snprintf)(buf, chunk, "%s", s + offset);
      tl_assert(sn_retval >= 0);
      // VG_(printf)("s+offset: `%s` limit: %u chunk: %u buf: `%s` sn_retval: %u\n", s + offset, limit, chunk, buf, sn_retval);

      // Valgrind's variants of [v]snprintf "differ" from C99: the return value
      // will be clamped to the provided buffer size S. If that *is* the
      // returned value, then the terminating null is written to index S-1.
      //
      // `sn_retval` can be zero, e.g. if there is an `\0` embedded in the message
      // at offset zero, which prematurely terminates it.
      //
      // But no matter what, the snprintf call above should have terminated the
      // `buf` with a `\0`.
      tl_assert(sn_retval <= chunk);
      unsigned copied;
      if (sn_retval == chunk) {
         copied = sn_retval - 1;
      } else {
         copied = sn_retval;
      }
      tl_assert(buf[copied] == '\0');
      offset += copied;
      tl_assert(copied <= lim);
      lim -= copied;

      unsigned printed = VG_(printf)("%s", buf);
      tl_assert(printed >= 0);
      total_printed += printed;
   }
   // VG_(printf)("total_printed: %u limit: %u chunk: %u\n", total_printed, limit, chunk);
   return total_printed;
}

static void KC_(post_clo_init) ( void )
{
   hello_world(printn, printi, printu);
}

/*------------------------------------------------------------*/
/*--- execution tracing                                    ---*/
/*------------------------------------------------------------*/

static void KC_(fini) ( Int exitcode )
{
}
/*------------------------------------------------------------*/
/*--- Register-memory event handlers                       ---*/
/*------------------------------------------------------------*/


static void init_shadow_memory ( void )
{

}

static void KC_(pre_clo_init)( void )
{
   VG_(details_name)            ("Krabcake");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("the Rust UB detection tool");
   VG_(details_copyright_author)(
      "Copyright (C) 2023, and GNU GPL'd by Felix S. Klock.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(basic_tool_funcs)        (KC_(post_clo_init),
                                 KC_(instrument),
                                 KC_(fini));

   VG_(needs_core_errors)         ();
   VG_(needs_command_line_options)(KC_(process_cmd_line_options),
                                   KC_(print_usage),
                                   KC_(print_debug_usage));
   VG_(needs_client_requests)     (KC_(handle_client_request));

   VG_(track_copy_mem_to_reg)     (KC_(copy_mem_to_reg));
   VG_(track_copy_reg_to_mem)     (KC_(copy_reg_to_mem));
   VG_(track_pre_mem_read)        (KC_(pre_mem_read));
   VG_(track_pre_mem_read_asciiz) (KC_(pre_mem_read_asciiz));
   VG_(track_pre_mem_write)       (KC_(pre_mem_write));
   VG_(track_post_mem_write)      (KC_(post_mem_write));

/*
   VG_(needs_sanity_checks)       (kc_cheap_sanity_check,
                                   kc_expensive_sanity_check);
   VG_(needs_print_stats)         (kc_print_stats);

needs_malloc_replacement
track_new_mem_mmap
track_change_mem_mprotect
track_copy_mem_remap

   VG_(track_pre_mem_read)        ( check_mem_is_defined );
   VG_(track_pre_mem_read_asciiz) ( check_mem_is_defined_asciiz );
   VG_(track_pre_mem_write)       ( check_mem_is_addressable );
   VG_(track_post_mem_write)      ( mc_post_mem_write );

   VG_(track_post_reg_write)                  ( mc_post_reg_write );
   VG_(track_post_reg_write_clientcall_return)( mc_post_reg_write_clientcall );

   if (KC_(clo_mc_level) >= 2) {
      VG_(track_copy_mem_to_reg)  ( mc_copy_mem_to_reg );
      VG_(track_copy_reg_to_mem)  ( mc_copy_reg_to_mem );
   }


*/
   init_shadow_memory();

   KC_(do_instrumentation_startup_checks)();
}

VG_DETERMINE_INTERFACE_VERSION(KC_(pre_clo_init))

/*--------------------------------------------------------------------*/
/*--- end                                                kc_main.c ---*/
/*--------------------------------------------------------------------*/
