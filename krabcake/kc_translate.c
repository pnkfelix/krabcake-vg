
/*--------------------------------------------------------------------*/
/*--- Instrument IR to check borrow validty.        kc_translate.c ---*/
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

static void trace_wrtmp_load(Addr addr, SizeT size)
{
   // VG_(printf)("trace_wrtmp_load addr=%08llx size=%llu\n", addr, size);
}

static void trace_llsc()
{
   VG_(printf)("trace_llsc\n");
}

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
            IRExpr   *load_addr = data->Iex.Load.addr;
            IRType    load_ty   = data->Iex.Load.ty;
            IREndness load_end  = data->Iex.Load.end;
            Int       load_size = sizeofIRType(load_ty);
            /* FIXME */
            di = unsafeIRDirty_0_N(
               0,
               "trace_wrtmp_load",
               VG_(fnptr_to_fnentry)( &trace_wrtmp_load ),
               mkIRExprVec_2(load_addr, mkIRExpr_HWord(load_size))
               );
            addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
         }
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
