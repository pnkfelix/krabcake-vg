
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
#include "pub_tool_libcprint.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_tooliface.h"

#include "krabcake.h" /* for client requests */

/* For code instrumentation */
#include "libvex_basictypes.h"
#include "libvex_ir.h"
#include "libvex.h"

#include <stdint.h>

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

static void kc_post_clo_init(void)
{
   hello_world(printn, printi, printu);
}

static void trace_wrtmp()
{
   VG_(printf)("trace_wrtmp\n");
}

static void trace_llsc()
{
   VG_(printf)("trace_llsc\n");
}

static
IRSB* kc_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      const VexGuestLayout* layout,
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   IRDirty*   di;
   IRSB*      sbOut;
   IRTypeEnv* tyenv = sbIn->tyenv;

   /* Set up SB. As this says, it copies everything except the statement list.
      That means it copies the type enviroment and the basic-block control-flow
      structure.
    */
   sbOut = deepCopyIRSBExceptStmts(sbIn);

   Int      i;
   IRStmt** sts2;

   for (i = 0; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st) continue;
      switch (st->tag) {
         // == LOAD+STORE instructions ==

         // `t<tmp> = <data>` assigns value to an (SSA) temporary.
      case Ist_WrTmp: {
         IRExpr* data = st->Ist.WrTmp.data;
         IRType  type = typeOfIRExpr(tyenv, data);
         if (data->tag == Iex_Load) {
            /* FIXME */
         }
         di = unsafeIRDirty_0_N(
            0,
            "trace_wrtmp",
            VG_(fnptr_to_fnentry)( &trace_wrtmp ),
            mkIRExprVec_0()
            );
         addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
         addStmtToIRSB( sbOut, st );
         break;
      }
         // `ST<end>(<addr>) = <data>` writes value to memory, unconditionally.
      case Ist_Store: {
         IRExpr* data = st->Ist.Store.data;
         IRType  type = typeOfIRExpr(tyenv, data);
         /* FIXME */
         addStmtToIRSB( sbOut, st );
         break;
      }
         // `t<tmp> = if (<guard>) <cvt>(LD<env>(<addr>)) else <alt>` guarded load
      case Ist_LoadG: {
         IRLoadG* lg       = st->Ist.LoadG.details;
         IRType   type     = Ity_INVALID; /* loaded type */
         IRType   typeWide = Ity_INVALID; /* after implicit widening */
         typeOfIRLoadGOp(lg->cvt, &typeWide, &type);
         /* FIXME */
         addStmtToIRSB( sbOut, st );
         break;
      }
         // `if (<guard>) ST<end>(<addr>) = <data>` guarded store; all fields
         // unconditionally evaluated.
      case Ist_StoreG: {
         /* FIXME */
         addStmtToIRSB( sbOut, st );
         break;
      }
         // `t<tmp> = CAS<end>(<addr> :: <expected> -> <new>)` atomic compare-and-swap
      case Ist_CAS: {
         Int    dataSize;
         IRType dataTy;
         IRCAS* cas = st->Ist.CAS.details;
         tl_assert(cas->addr != NULL);
         tl_assert(cas->dataLo != NULL);
         dataTy   = typeOfIRExpr(tyenv, cas->dataLo);
         /* FIXME */
         addStmtToIRSB( sbOut, st );
         break;
      }
         // `result = LD<end>-Linked(<addr>)` if STOREDATA is null
         // `result = ( ST<end>-Cond(<addr>)` if STOREDATA nonnull
      case Ist_LLSC: {
         IRType dataTy;
         if (st->Ist.LLSC.storedata == NULL) {
            /* LL */
            dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
            /* FIXME */
         } else {
            /* SC */
            dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
            /* FIXME */
         }
         di = unsafeIRDirty_0_N(
            0,
            "trace_llsc",
            VG_(fnptr_to_fnentry)( &trace_llsc ),
            mkIRExprVec_0()
            );
         addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
         addStmtToIRSB( sbOut, st );
         break;
      }

         // == REMAINING INSTRUCTIONS NOT YET MONITORED BY KRABCAKE ==

         // `IR-NoOp`, can be included or omitted without effect.
      case Ist_NoOp:
         // `IMark(<addr>, <len>, <delta>)` marks start of statements
         // representing single machine instruction.
      case Ist_IMark:
         // `AbiHint(<base>, <len>, <nia>)` says something about platform's ABI
      case Ist_AbiHint:
         // `PUT(<offset>) = <data>` writes guest register at fixed offset
      case Ist_Put:
         // `PUTI<descr>[<ix>,<bias>] = <data>` writes guest register at
         // non-fixed offset
      case Ist_PutI:
         // `ty = DIRTY <guard> <effects> ::: <callee>(<args>)` conditional call
         // to side-effecting C function.
      case Ist_Dirty:
         // `MBusEvent-Fence`,`MBusEvent-BusLock`, `MBusEvent-BusUnlock`
      case Ist_MBE:
         // `if (<guard>) goto { <jk> } <dst>` conditional exit from mid-IRSB.
      case Ist_Exit: {
            addStmtToIRSB( sbOut, st );
            break;
      }
      }
   }

   return sbOut;
}

static void kc_fini(Int exitcode)
{
}

static Bool kc_process_cmd_line_options(const HChar* arg)
{
   return True;
}

static void kc_print_usage(void)
{
   VG_(printf)(
      "(none)\n"
      );
}

static void kc_print_debug_usage(void)
{
   VG_(printf)(
"    (none)\n"
   );
}

static Bool kc_handle_client_request ( ThreadId tid, UWord* arg, UWord* ret )
{
   Bool  handled = False;

   if (!VG_IS_TOOL_USERREQ('K','C',arg[0]))
      return False;

   VG_(dmsg)("kc_handle_client_request, dispatching client request code %llx\n", (ULong)arg[0]);

   switch(arg[0]) {
   case VG_USERREQ__BORROW_MUT: {
      VG_(dmsg)("kc_handle_client_request, handle BORROW_MUT %llx (<- return value) %llx %llx %llx %llx\n",
                (ULong)arg[1], (ULong)arg[2], (ULong)arg[3], (ULong)arg[4], (ULong)arg[5]);
      *ret = arg[1];
      handled = True;
      break;
   }
   case VG_USERREQ__BORROW_SHR: {
      VG_(dmsg)("kc_handle_client_request, handle BORROW_SHR");
      break;
   }
   case VG_USERREQ__AS_RAW: {
      VG_(dmsg)("kc_handle_client_request, handle AS_RAW");
      break;
   }
   case VG_USERREQ__AS_BORROW_MUT: {
      VG_(dmsg)("kc_handle_client_request, handle AS_BORROW_MUT");
      break;
   }
   case VG_USERREQ__AS_BORROW_SHR: {
      VG_(dmsg)("kc_handle_client_request, handle AS_BORROW_SHR");
      break;
   }
   case VG_USERREQ__RETAG_FN_PROLOGUE: {
      VG_(dmsg)("kc_handle_client_request, handle RETAG_FN_PROLOGUE");
      break;
   }
   case VG_USERREQ__RETAG_ASSIGN: {
      VG_(dmsg)("kc_handle_client_request, handle RETAG_ASSIGN");
      break;
   }
   case VG_USERREQ__RETAG_RAW: {
      VG_(dmsg)("kc_handle_client_request, handle RETAG_RAW");
      break;
   }
   case VG_USERREQ__INTRINSICS_ASSUME: {
      VG_(dmsg)("kc_handle_client_request, handle INTRINSICS_ASSUME %llx %llx %llx %llx %llx\n",
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
/*--- Register-memory event handlers                       ---*/
/*------------------------------------------------------------*/

static void kc_copy_mem_to_reg ( CorePart part, ThreadId tid, Addr a,
                                 PtrdiffT guest_state_offset, SizeT size )
{
   VG_(dmsg)("kc_copy_mem_to_reg\n");
}

static void kc_copy_reg_to_mem ( CorePart part, ThreadId tid,
                                 PtrdiffT guest_state_offset, Addr a,
                                 SizeT size )
{
   VG_(dmsg)("kc_copy_reg_to_mem\n");
}

static
void kc_pre_mem_read ( CorePart part, ThreadId tid, const HChar* s,
                       Addr base, SizeT size )
{
   // VG_(dmsg)("kc_pre_mem_read %s base=%p size=%x (%d)\n", s, base, size, size);
}

static
void kc_pre_mem_read_asciiz ( CorePart part, ThreadId tid,
                              const HChar* s, Addr str )
{
   // VG_(dmsg)("kc_pre_mem_read_asciiz\n");
}

static
void kc_pre_mem_write ( CorePart part, ThreadId tid, const HChar* s,
                        Addr base, SizeT size )
{
   // VG_(dmsg)("kc_pre_mem_write\n");
}

static
void kc_post_mem_write(CorePart part, ThreadId tid, Addr a, SizeT len)
{
   // VG_(dmsg)("kc_post_mem_write\n");
}

static void kc_pre_clo_init(void)
{
   VG_(details_name)            ("Krabcake");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("the Rust UB detection tool");
   VG_(details_copyright_author)(
      "Copyright (C) 2023, and GNU GPL'd by Felix S. Klock.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(basic_tool_funcs)        (kc_post_clo_init,
                                 kc_instrument,
                                 kc_fini);

   VG_(needs_core_errors)         ();
   VG_(needs_command_line_options)(kc_process_cmd_line_options,
                                   kc_print_usage,
                                   kc_print_debug_usage);
   VG_(needs_client_requests)     (kc_handle_client_request);

   VG_(track_copy_mem_to_reg)     (kc_copy_mem_to_reg);
   VG_(track_copy_reg_to_mem)     (kc_copy_reg_to_mem);
   VG_(track_pre_mem_read)        (kc_pre_mem_read);
   VG_(track_pre_mem_read_asciiz) (kc_pre_mem_read_asciiz);
   VG_(track_pre_mem_write)       (kc_pre_mem_write);
   VG_(track_post_mem_write)      (kc_post_mem_write);

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

   if (MC_(clo_mc_level) >= 2) {
      VG_(track_copy_mem_to_reg)  ( mc_copy_mem_to_reg );
      VG_(track_copy_reg_to_mem)  ( mc_copy_reg_to_mem );
   }

   init_shadow_memory();

   MC_(do_instrumentation_startup_checks)();
*/
}

VG_DETERMINE_INTERFACE_VERSION(kc_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
