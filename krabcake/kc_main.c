
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

extern Long rs_shadow_rdtmp ( Long tmp );
extern Long rs_shadow_qop ( Long op, Long s1, Long s2, Long s3, Long s4 );
extern Long rs_shadow_triop ( Long op, Long s1, Long s2, Long s3 );
extern Long rs_shadow_binop ( Long op, Long s1, Long s2 );
extern Long rs_shadow_unop ( Long op, Long s1 );
extern Long rs_shadow_load ( Addr addr, Long s1 );
extern Long rs_shadow_const ( );
extern Long rs_shadow_ite ( Long cond, Long s1, Long s2, Long s3 );
extern Long rs_shadow_get ( Long offset, Long ty );
extern Long rs_shadow_geti ( );
extern Long rs_shadow_ccall ( );

extern void rs_trace_cas ( Addr addr );
extern void rs_trace_storeg ( Long guard, Addr addr, SizeT size );
extern void rs_trace_loadg ( Long guard, Addr addr, SizeT size, SizeT widened_size );
extern void rs_trace_wrtmp ( IRTemp lhs_tmp, ULong shadow_data );
extern void rs_trace_wrtmp_load ( IRTemp lhs_tmp, Addr addr, SizeT size );
extern void rs_trace_store ( Addr addr, ULong data, SizeT size, ULong shadow_addr, ULong shadow_data );
extern void rs_trace_store128 ( Addr addr, ULong data1, ULong data2, SizeT size, ULong shadow_addr, ULong shadow_data );
extern void rs_trace_store256 ( Addr addr, ULong data1, ULong data2, ULong data3, ULong data4, SizeT size, ULong shadow_addr, ULong shadow_data );
extern void rs_trace_llsc ( Addr addr );
extern void rs_trace_put ( ULong put_offset, ULong data, ULong shadow_data );
extern void rs_trace_put_just_shadow ( ULong put_offset, ULong shadow_data );
extern void rs_trace_puti ( ULong ix, ULong bias, ULong data, ULong shadow_ix, ULong shadow_data );
extern void rs_trace_puti_just_shadow ( ULong ix, ULong bias, ULong shadow_ix, ULong shadow_data );

static void trace_cas(Addr addr)
{
   // VG_(printf)("trace_cas addr=%08llx\n", addr);
}

/* FIXME: leaving out tracing of the stored data here for now. */
static void trace_storeg(ULong guard, Addr addr, SizeT size)
{
   VG_(printf)("trace_storeg guard=%llu addr=%08lx size=%lu\n", guard, addr, size);
}

static void trace_loadg(ULong guard, Addr addr, SizeT size, SizeT widened_size)
{
   // VG_(printf)("trace_loadg guard=%lld addr=%08llx size=%llu\n", guard, addr, size);
}

static void trace_wrtmp_load(Addr addr, SizeT size)
{
   // VG_(printf)("trace_wrtmp_load addr=%08llx size=%llu\n", addr, size);
}

static void trace_store(Addr addr, ULong data, SizeT size)
{
   // VG_(printf)("trace_store addr=%08lx data=%08llx size=%llu\n", addr, data, size);
}

static void trace_store128(Addr addr, ULong data1, ULong data2, SizeT size)
{
   VG_(printf)("trace_store128 addr=%08lx data=[%08llx, %08llx] size=%lu\n", addr, data1, data2, size);
}

static void trace_store256(Addr addr, ULong data1, ULong data2, ULong data3, ULong data4, SizeT size)
{
   VG_(printf)("trace_store128 addr=%08lx data=[%08llx, %08llx, %08llx, %08llx] size=%lu\n", addr, data1, data2, data3, data4, size);
}

static void trace_llsc(Addr addr)
{
   VG_(printf)("trace_llsc addr=%08lx\n", addr);
}

typedef enum { Orig=1, Tag=2, Stk=3, Vsh=4 } TempKind;

/* Create a new IRTemp of type 'ty' and kind 'kind'.
   See analogous function in memcheck for ideas of where this might go.
*/
static IRTemp newTemp ( IRSB *sbOut, IRType ty, TempKind kind )
{
   IRTemp     tmp = newIRTemp(sbOut->tyenv, ty);
   return tmp;
}

/* assign value to tmp */
static inline 
void assign ( HChar cat, IRSB *sbOut, IRTemp tmp, IRExpr* expr ) {
   addStmtToIRSB(sbOut, IRStmt_WrTmp(tmp,expr));
}

#define mkexpr(_tmp)             IRExpr_RdTmp((_tmp))

typedef  IRExpr  IRAtom;

/* Bind the given expression to a new temporary, and return the
   temporary.  This effectively converts an arbitrary expression into
   an atom.

   'ty' is the type of 'e' and hence the type that the new temporary
   needs to be.  But passing it in is redundant, since we can deduce
   the type merely by inspecting 'e'.  So at least use that fact to
   assert that the two types agree. */
static IRAtom* assignNew ( HChar cat, IRSB *sbOut, IRType ty, IRExpr* e )
{
   TempKind k;
   IRTemp   t;
   IRType   tyE = typeOfIRExpr(sbOut->tyenv, e);

   tl_assert(tyE == ty); /* so 'ty' is redundant (!) */
   switch (cat) {
      case 'T': k = Tag;  break;
      case 'S': k = Stk;  break;
      case 'V': k = Vsh;  break;
      case 'C': k = Orig; break; 
                /* happens when we are making up new "orig"
                   expressions, for IRCAS handling */
      default: tl_assert(0);
   }
   t = newTemp(sbOut, ty, k);
   assign(cat, sbOut, t, e);
   return mkexpr(t);
}

typedef enum ExprContext {
   /* These are the recursive occcurences of IExpr in the grammar of its definition */
   Expr_GetI_Index = 0x1F00,
   Expr_Qop_Arg1,
   Expr_Qop_Arg2,
   Expr_Qop_Arg3,
   Expr_Qop_Arg4,
   Expr_Triop_Arg1,
   Expr_Triop_Arg2,
   Expr_Triop_Arg3,
   Expr_Binop_Arg1,
   Expr_Binop_Arg2,
   Expr_Unop_Arg,
   Expr_Load_Addr,
   Expr_CCall_Arg,
   Expr_ITE_Cond,
   Expr_ITE_IfTrue,
   Expr_ITE_IfFalse,

   /* These are the occurrences of IExpr _outside_ of the IExpr definition, and
    * I am hoping they are all root entry points (i.e. that one never reaches
    * any of these within the context of an IExpr itself), though I have not
    * verified that yet. */
   Stmt_AbiHint_Base,
   Stmt_AbiHint_Nia,
   Stmt_Put_Data,   // in-progress
   Stmt_PutI_Ix,    // in-progress
   Stmt_PutI_Data,  // in-progress
   Stmt_WrTmp_Data, // "done"
   Stmt_Store_Addr, // in-progress
   Stmt_Store_Data, // in-progress
   Stmt_StoreG_Addr,
   Stmt_StoreG_Data,
   Stmt_StoreG_Guard,
   Stmt_LoadG_Addr,
   Stmt_LoadG_Alt,
   Stmt_LoadG_Guard,
   Stmt_Cas_Addr,
   Stmt_Cas_ExpectedHi,
   Stmt_Cas_ExpectedLo,
   Stmt_Cas_DataHi,
   Stmt_Cas_DataLow,
   Stmt_Llsc_Addr,
   Stmt_Llsc_StoreData, // NULL => LL, non-NULL => SC
   Stmt_Dirty_Guard, // non-null
   Stmt_Dirty_Arg,
   Stmt_Dirty_MemAddr,
   Stmt_Exit_Guard,

   Superblock_Next,
} ExprContext;

IRTemp newTagTemp ( IRSB* sbOut ) {
   return newIRTemp( sbOut->tyenv, Ity_I64 );
}

IRTemp newHWordTemp ( IRSB* sbOut ) {
   return newIRTemp( sbOut->tyenv, Ity_I64 );
}

static IRExpr* kc_construct_shadow_eval(IRSB* sbOut,
                                        IRExpr* e,
                                        ExprContext ec)
{
   IRExpr* (*recur)(IRSB *sbOut, IRExpr* e, ExprContext exc);
   recur = kc_construct_shadow_eval;

   // VG_(printf)("kc_construct_shadow_eval "); ppIRExpr(e); VG_(printf)("\n");
   
   IRDirty* di;
   IRTemp recvTmp = newTagTemp( sbOut );

   IRExpr *shadow1, *shadow2, *shadow3, *shadow4;

   switch (e->tag) {
      /* should not be seen outside of Vex */ 
   case Iex_Binder: tl_assert(0); break;
      /* The value held by a temporary.
         ppIRExpr output: t<tmp>, eg. t1 */
   case Iex_RdTmp:
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_rdtmp",
         VG_(fnptr_to_fnentry)( &rs_shadow_rdtmp ),
         mkIRExprVec_1(mkIRExpr_HWord(e->Iex.RdTmp.tmp))
         );
      break;
      /* A quaternary operation.
         ppIRExpr output: <op>(<arg1>, <arg2>, <arg3>, <arg4>),
                      eg. MAddF64r32(t1, t2, t3, t4)
      */
   case Iex_Qop:
      shadow1 = recur(sbOut, e->Iex.Qop.details->arg1, Expr_Qop_Arg1);
      shadow2 = recur(sbOut, e->Iex.Qop.details->arg2, Expr_Qop_Arg2);
      shadow3 = recur(sbOut, e->Iex.Qop.details->arg3, Expr_Qop_Arg3);
      shadow4 = recur(sbOut, e->Iex.Qop.details->arg4, Expr_Qop_Arg4);
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_qop",
         VG_(fnptr_to_fnentry)( &rs_shadow_qop ),
         mkIRExprVec_5(mkIRExpr_HWord(e->Iex.Qop.details->op),
                       shadow1, shadow2, shadow3, shadow4)
         );
      break;
      /* A ternary operation.
         ppIRExpr output: <op>(<arg1>, <arg2>, <arg3>),
                      eg. MulF64(1, 2.0, 3.0)
      */
   case Iex_Triop:
      shadow1 = recur(sbOut, e->Iex.Triop.details->arg1, Expr_Triop_Arg1);
      shadow2 = recur(sbOut, e->Iex.Triop.details->arg2, Expr_Triop_Arg2);
      shadow3 = recur(sbOut, e->Iex.Triop.details->arg3, Expr_Triop_Arg3);
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_triop",
         VG_(fnptr_to_fnentry)( &rs_shadow_triop ),
         mkIRExprVec_4(mkIRExpr_HWord(e->Iex.Triop.details->op),
                       shadow1, shadow2, shadow3)
         );
      break;
      /* A binary operation.
         ppIRExpr output: <op>(<arg1>, <arg2>), eg. Add32(t1,t2)
      */
   case Iex_Binop:
      shadow1 = recur(sbOut, e->Iex.Binop.arg1, Expr_Binop_Arg1);
      shadow2 = recur(sbOut, e->Iex.Binop.arg2, Expr_Binop_Arg2);
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_binop",
         VG_(fnptr_to_fnentry)( &rs_shadow_binop ),
         mkIRExprVec_3(mkIRExpr_HWord(e->Iex.Binop.op), shadow1, shadow2)
         );
      break;
      /* A unary operation.
         ppIRExpr output: <op>(<arg>), eg. Neg8(t1)
      */
   case Iex_Unop:
      shadow1 = recur(sbOut, e->Iex.Unop.arg, Expr_Unop_Arg);
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_unop",
         VG_(fnptr_to_fnentry)( &rs_shadow_unop ),
         mkIRExprVec_2(mkIRExpr_HWord(e->Iex.Unop.op), shadow1)
         );
      break;
      /* A load from memory -- a normal load, not a load-linked.
         ppIRExpr output: LD<end>:<ty>(<addr>), eg. LDle:I32(t1)
      */
   case Iex_Load:
      shadow1 = recur(sbOut, e->Iex.Load.addr, Expr_Load_Addr);
/*
   IRExpr   *load_addr = data->Iex.Load.addr;
   IRType    load_ty   = data->Iex.Load.ty;
   IREndness load_end  = data->Iex.Load.end;
   Int       load_size = sizeofIRType(load_ty);
*/
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_load",
         VG_(fnptr_to_fnentry)( &rs_shadow_load ),
         mkIRExprVec_2(e->Iex.Load.addr, shadow1)
         );
      break;
      /* A constant-valued expression.
         ppIRExpr output: <con>, eg. 0x4:I32
      */
   case Iex_Const:
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_const",
         VG_(fnptr_to_fnentry)( &rs_shadow_const ),
         mkIRExprVec_0()
         );
      break;
      /* A ternary if-then-else operator. Note both iftrue and iffalse are
         evaluated in all cases.
         ppIRExpr output: ITE(<cond>,<iftrue>,<iffalse>),
                         eg. ITE(t6,t7,t8)
      */
   case Iex_ITE:
      shadow1 = recur(sbOut, e->Iex.ITE.cond, Expr_ITE_Cond);
      shadow2 = recur(sbOut, e->Iex.ITE.iftrue, Expr_ITE_IfTrue);
      shadow3 = recur(sbOut, e->Iex.ITE.iffalse, Expr_ITE_IfFalse);
      IRTemp extendTmp = newHWordTemp(sbOut);
      IRExpr* cond = IRExpr_Unop(Iop_1Uto64, e->Iex.ITE.cond);
      cond = assignNew('V', sbOut, Ity_I64, cond);
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_ite",
         VG_(fnptr_to_fnentry)( &rs_shadow_ite ),
         mkIRExprVec_4(cond, shadow1, shadow2, shadow3)
         );
      break;
      /* Read a guest register, at a fixed offset in the guest state.
         ppIRExpr output: GET:<ty>(<offset>), eg. GET:I32(0) */
   case Iex_Get:
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_get",
         VG_(fnptr_to_fnentry)( &rs_shadow_get ),
         mkIRExprVec_2(mkIRExpr_HWord(e->Iex.Get.offset),
                       mkIRExpr_HWord(e->Iex.Get.ty))
         );
      break;
      /* Read a guest register at a non-fixed offset in the guest state; allows
         circular indexing into parts of the guest state. 
         ppIRExpr output: GETI<descr>[<ix>,<bias] eg. GETI(128:8xI8)[t1,0] */
   case Iex_GetI:
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_geti",
         VG_(fnptr_to_fnentry)( &rs_shadow_geti ),
         mkIRExprVec_0()
         );
      break;
      /* A call to a pure (no side-effects) helper C function.
         ppIRExpr output: <cee>(<args>):<retty>
                      eg. foo{0x80489304}(t1, t2):I32 */
   case Iex_CCall:
      di = unsafeIRDirty_1_N(
         recvTmp,
         0,
         "rs_shadow_ccall",
         VG_(fnptr_to_fnentry)( &rs_shadow_ccall ),
         mkIRExprVec_0()
         );
      break;
      /* Two special kinds of IRExpr, which can ONLY be used in
         argument lists for dirty helper calls (IRDirty.args) and in NO
         OTHER PLACES.  And then only in very limited ways.  */
   case Iex_VECRET:
   case Iex_GSPTR:
      /* FIXME should I print something here to remind myself these cases are not handled? */
      tl_assert(0); // unimplemented
      break;
   }

   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   return IRExpr_RdTmp( recvTmp );
}

static void kc_instrument_expr_eval(IRSB* sbOut,
                                    IRExpr* data,
                                    ExprContext context)
{
   IRDirty* di;
   switch (data->tag) {
      /* should not be seen outside of Vex */ 
   case Iex_Binder: tl_assert(0); break;
      /* The value held by a temporary.
         ppIRExpr output: t<tmp>, eg. t1 */
   case Iex_RdTmp: break;
      /* A quaternary operation.
         ppIRExpr output: <op>(<arg1>, <arg2>, <arg3>, <arg4>),
                      eg. MAddF64r32(t1, t2, t3, t4)
      */
   case Iex_Qop:
      kc_instrument_expr_eval(sbOut, data->Iex.Qop.details->arg1, Expr_Qop_Arg1);
      kc_instrument_expr_eval(sbOut, data->Iex.Qop.details->arg2, Expr_Qop_Arg2);
      kc_instrument_expr_eval(sbOut, data->Iex.Qop.details->arg3, Expr_Qop_Arg3);
      kc_instrument_expr_eval(sbOut, data->Iex.Qop.details->arg4, Expr_Qop_Arg4);
      break;
      /* A ternary operation.
         ppIRExpr output: <op>(<arg1>, <arg2>, <arg3>),
                      eg. MulF64(1, 2.0, 3.0)
      */
   case Iex_Triop:
      kc_instrument_expr_eval(sbOut, data->Iex.Triop.details->arg1, Expr_Triop_Arg1);
      kc_instrument_expr_eval(sbOut, data->Iex.Triop.details->arg2, Expr_Triop_Arg2);
      kc_instrument_expr_eval(sbOut, data->Iex.Triop.details->arg3, Expr_Triop_Arg3);
      break;
      /* A binary operation.
         ppIRExpr output: <op>(<arg1>, <arg2>), eg. Add32(t1,t2)
      */
   case Iex_Binop:
      kc_instrument_expr_eval(sbOut, data->Iex.Binop.arg1, Expr_Binop_Arg1);
      kc_instrument_expr_eval(sbOut, data->Iex.Binop.arg2, Expr_Binop_Arg2);
      break;
      /* A unary operation.
         ppIRExpr output: <op>(<arg>), eg. Neg8(t1)
      */
   case Iex_Unop:
      kc_instrument_expr_eval(sbOut, data->Iex.Unop.arg, Expr_Unop_Arg);
      break;
      /* A load from memory -- a normal load, not a load-linked.
         ppIRExpr output: LD<end>:<ty>(<addr>), eg. LDle:I32(t1)
      */
   case Iex_Load:
      kc_instrument_expr_eval(sbOut, data->Iex.Load.addr, Expr_Load_Addr);
      break;
      /* A constant-valued expression.
         ppIRExpr output: <con>, eg. 0x4:I32
      */
   case Iex_Const:
      break;
      /* A ternary if-then-else operator. Note both iftrue and iffalse are
         evaluated in all cases.
         ppIRExpr output: ITE(<cond>,<iftrue>,<iffalse>),
                         eg. ITE(t6,t7,t8)
      */
   case Iex_ITE:
      kc_instrument_expr_eval(sbOut, data->Iex.ITE.cond, Expr_ITE_Cond);
      kc_instrument_expr_eval(sbOut, data->Iex.ITE.iftrue, Expr_ITE_IfTrue);
      kc_instrument_expr_eval(sbOut, data->Iex.ITE.iffalse, Expr_ITE_IfFalse);
      break;

      /* A call to a pure (no side-effects) helper C function.
         ppIRExpr output: <cee>(<args>):<retty>
                      eg. foo{0x80489304}(t1, t2):I32 */
   case Iex_CCall:
      /* Read a guest register, at a fixed offset in the guest state.
         ppIRExpr output: GET:<ty>(<offset>), eg. GET:I32(0) */
   case Iex_Get:
      /* Read a guest register at a non-fixed offset in the guest state; allows
         circular indexing into parts of the guest state. 
         ppIRExpr output: GETI<descr>[<ix>,<bias] eg. GETI(128:8xI8)[t1,0] */
   case Iex_GetI:
      /* Two special kinds of IRExpr, which can ONLY be used in
         argument lists for dirty helper calls (IRDirty.args) and in NO
         OTHER PLACES.  And then only in very limited ways.  */
   case Iex_VECRET:
   case Iex_GSPTR:
      /* FIXME should I print something here to remind myself these cases are not handled? */
      break;
   }
}

static void kc_instrument_put ( IRSB* sbOut,
                                IRStmt *st,
                                IRExpr* shadow_data )
{
   tl_assert(st->tag == Ist_Put);
   /* FIXME review overall semantics here */
   Int       put_offset = st->Ist.Put.offset;
   IRExpr*   put_data   = st->Ist.Put.data;
   /* FIXME its hard to make a generic trace routine here because the VEX IR can
    * do things like "PUT a V128 constant value into an appropriately sized
    * register."  So for the demo, we cheat here and don't bother about the
    * cases that are not the right size.
    */
   IRType    ty         = typeOfIRExpr(sbOut->tyenv, put_data);
   Int       put_size   = sizeofIRType(ty);
   IRDirty*  di;
   if (ty == Ity_I64) {
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_put",
         VG_(fnptr_to_fnentry)( &rs_trace_put ),
         mkIRExprVec_3(mkIRExpr_HWord(put_offset), put_data, shadow_data)
         );
   } else {
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_put_just_shadow",
         VG_(fnptr_to_fnentry)( &rs_trace_put_just_shadow ),
         mkIRExprVec_2(mkIRExpr_HWord(put_offset), shadow_data)
         );
   }
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st );
}

static void kc_instrument_puti ( IRSB* sbOut,
                                 IRStmt *st,
                                 IRExpr* shadow_ix,
                                 IRExpr* shadow_data )
{
   tl_assert(st->tag == Ist_PutI);
   IRExpr*   puti_ix   = st->Ist.PutI.details->ix;
   Int       puti_bias = st->Ist.PutI.details->bias;
   IRExpr*   puti_data = st->Ist.PutI.details->data;
   /* FIXME there is a bunch more information in PutI descr that we are just
    * dropping here */
   /* FIXME its hard to make a generic trace routine here because the VEX IR can
    * do things like "PUT a V128 constant value into an appropriately sized
    * register."  So for the demo, we cheat here and don't bother about the
    * cases that are not the right size.
    */
   IRType    ty         = typeOfIRExpr(sbOut->tyenv, puti_data);
   Int       puti_size   = sizeofIRType(ty);
   IRDirty*  di;
   if (ty == Ity_I64) {
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_puti",
         VG_(fnptr_to_fnentry)( &rs_trace_puti ),
         mkIRExprVec_5(puti_ix, mkIRExpr_HWord(puti_bias), puti_data, shadow_ix, shadow_data)
         );
   } else {
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_puti_just_shadow",
         VG_(fnptr_to_fnentry)( &rs_trace_puti_just_shadow ),
         mkIRExprVec_4(puti_ix, mkIRExpr_HWord(puti_bias), shadow_ix, shadow_data)
         );
   }
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st );
}

static void  kc_instrument_llsc ( IRSB* sbOut,
                                  IRStmt *st)
{
   tl_assert(st->tag == Ist_LLSC);
   IRType dataTy;
   IRTypeEnv* tyenv = sbOut->tyenv;
   if (st->Ist.LLSC.storedata == NULL) {
      /* LL */
      dataTy = typeOfIRTemp(tyenv, st->Ist.LLSC.result);
      /* FIXME */
   } else {
      /* SC */
      dataTy = typeOfIRExpr(tyenv, st->Ist.LLSC.storedata);
      /* FIXME */
   }
   IRExpr* llsc_addr = st->Ist.LLSC.addr;
   IRDirty* di = unsafeIRDirty_0_N(
      0,
      "rs_trace_llsc",
      VG_(fnptr_to_fnentry)( &rs_trace_llsc ),
      mkIRExprVec_1(llsc_addr)
      );
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st );
}

static void kc_instrument_cas ( IRSB* sbOut,
                                IRStmt *st)
{
   tl_assert(st->tag == Ist_CAS);
   Int    dataSize;
   IRType dataTy;
   IRCAS* cas = st->Ist.CAS.details;
   tl_assert(cas->addr != NULL);
   tl_assert(cas->dataLo != NULL);
   IRExpr* cas_addr = cas->addr;
   IRDirty* di = unsafeIRDirty_0_N(
      0,
      "rs_trace_cas",
      VG_(fnptr_to_fnentry)( &rs_trace_cas ),
      mkIRExprVec_1(cas_addr)
      );
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st );
}

static void kc_instrument_storeg ( IRSB* sbOut,
                                   IRStmt *st)
{
   // `if (<guard>) ST<end>(<addr>) = <data>` guarded store; all fields
   // unconditionally evaluated.

   tl_assert(st->tag == Ist_StoreG);
   IRTypeEnv* tyenv = sbOut->tyenv;
   IRStoreG* sg       = st->Ist.StoreG.details;

   /* FIXME */

   IRExpr *store_guard = sg->guard;
   IRExpr *store_addr  = sg->addr;
   IRExpr *store_data  = sg->data;

   /* FIXME: This unconditionally calls the tracing for both true and false
      guards, relying on the callee to not inspect the memory if the guard is
      false.  It would be better to not invoke the tracing routine at all if the
      guard is false. */
   store_guard = IRExpr_Unop(Iop_1Uto64, store_guard);
   store_guard = assignNew('V', sbOut, Ity_I64, store_guard);
   IRType    store_type = typeOfIRExpr(tyenv, store_data);
   Int       store_size = sizeofIRType(store_type);

   tl_assert(0); // unimplemented
   IRDirty* di = unsafeIRDirty_0_N(
      0,
      "rs_trace_storeg",
      VG_(fnptr_to_fnentry)( &rs_trace_storeg ),
      mkIRExprVec_3(store_guard, store_addr, mkIRExpr_HWord(store_size))
      );
   addStmtToIRSB( sbOut, st );
}

static void kc_instrument_loadg ( IRSB* sbOut,
                                  IRStmt *st)
{
   tl_assert(st->tag == Ist_LoadG);
   IRTypeEnv* tyenv = sbOut->tyenv;
   IRLoadG* lg       = st->Ist.LoadG.details;
   IRType   type     = Ity_INVALID; /* loaded type */
   IRType   typeWide = Ity_INVALID; /* after implicit widening */
   typeOfIRLoadGOp(lg->cvt, &typeWide, &type);
   Int      load_size = sizeofIRType(type);
   Int      load_widened_size = sizeofIRType(typeWide);

   IRExpr *load_guard = lg->guard;
   IRExpr *load_addr  = lg->addr;

#if 0
   VG_(printf)("load_guard pre ");
   ppIRExpr(load_guard);
   VG_(printf)(" : ");
   ppIRType(typeOfIRExpr(tyenv, load_guard));
   VG_(printf)("\n");
#endif
   
   /* FIXME: This unconditionally calls the tracing for both true and false
      guards, relying on the callee to not inspect the memory if the guard is
      false.  It would be better to not invoke the tracing routine at all if the
      guard is false. */
   load_guard = IRExpr_Unop(Iop_1Uto64, load_guard);
   load_guard = assignNew('V', sbOut, Ity_I64, load_guard);

   IRDirty* di = unsafeIRDirty_0_N(
      0,
      "rs_trace_loadg",
      VG_(fnptr_to_fnentry)( &rs_trace_loadg ),
      mkIRExprVec_4(load_guard, load_addr, mkIRExpr_HWord(load_size), mkIRExpr_HWord(load_widened_size))
      );
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st );
}

static void kc_instrument_wrtmp ( IRSB* sbOut,
                                  IRStmt *st,
                                  IRExpr* shadow_data )
{
   // `t<tmp> = <data>` assigns value to an (SSA) temporary.
   tl_assert(st->tag == Ist_WrTmp);
   IRTypeEnv* tyenv = sbOut->tyenv;
   IRTemp  lhs_tmp = st->Ist.WrTmp.tmp;
   IRExpr* data = st->Ist.WrTmp.data;
   IRType  type = typeOfIRExpr(tyenv, data);
   /* FIXME */
   IRDirty* di = unsafeIRDirty_0_N(
      0,
      "rs_trace_wrtmp",
      VG_(fnptr_to_fnentry)( &rs_trace_wrtmp ),
      mkIRExprVec_2(mkIRExpr_HWord(lhs_tmp), shadow_data )
      );
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st );
}

static void kc_instrument_store ( IRSB* sbOut,
                                  IRStmt* st,
                                  IRExpr* shadow_addr,
                                  IRExpr* shadow_data )
{
   IRDirty* di;
   // `ST<end>(<addr>) = <data>` writes value to memory, unconditionally.
   IRTypeEnv* tyenv = sbOut->tyenv;

   IREndness store_endian  = st->Ist.Store.end;
   IRExpr*   store_addr = st->Ist.Store.addr;
   IRExpr*   store_data = st->Ist.Store.data;
   IRType    store_type = typeOfIRExpr(tyenv, store_data);
   Int       store_size = sizeofIRType(store_type);

   /* FIXME */
   switch (store_type) {
   case Ity_I1:
   case Ity_I8:
   case Ity_I16:
   case Ity_I32:
   case Ity_I64:
   case Ity_F16:
   case Ity_F32:
   case Ity_F64:
   case Ity_D32:
   case Ity_D64: {
      switch (store_type) {
      case Ity_I1:
         store_data = IRExpr_Unop(Iop_1Uto64, store_data);
         break;
      case Ity_I8:
         store_data = IRExpr_Unop(Iop_8Uto64, store_data);
         break;
      case Ity_I16:
         store_data = IRExpr_Unop(Iop_16Uto64, store_data);
         break;
      case Ity_I32:
         store_data = IRExpr_Unop(Iop_32Uto64, store_data);
         break;
      case Ity_I64:
         break;
      default:
         VG_(printf)("unhandled store_type: ");
         ppIRType(store_type);
         VG_(printf)(" (%d) \n", store_type);
         tl_assert(0);
      }
      if (store_type != Ity_I64) {
         store_data = assignNew('V', sbOut, Ity_I64, store_data);
      }
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_store",
         VG_(fnptr_to_fnentry)( &rs_trace_store ),
         mkIRExprVec_5(store_addr, store_data, mkIRExpr_HWord(store_size), shadow_addr, shadow_data)
         );
      break;
   }
            
   case Ity_I128:
   case Ity_D128:
   case Ity_F128:
   case Ity_V128: {
      // XXX FIXME worry about these cases after the demo
      addStmtToIRSB( sbOut, st ); 
      return;

      switch (store_type) {
      case Ity_D128:
         tl_assert(0); // XXX FIXME unimplemented
         break;
      case Ity_F128:
         store_data = assignNew('V', sbOut, Ity_F128, store_data);
         store_data = assignNew('V', sbOut, Ity_I128, IRExpr_Unop(Iop_ReinterpF128asI128, store_data));
         break;
      case Ity_V128:
         store_data = assignNew('V', sbOut, Ity_V128, store_data);
         store_data = assignNew('V', sbOut, Ity_I128, IRExpr_Unop(Iop_ReinterpV128asI128, store_data));
      case Ity_I128:
         break;
      }
      IRExpr* store_data1 = assignNew('V', sbOut, Ity_I64, IRExpr_Unop(Iop_128to64, store_data));
      IRExpr* store_data2 = assignNew('V', sbOut, Ity_I64, IRExpr_Unop(Iop_128HIto64, store_data));
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_store128",
         VG_(fnptr_to_fnentry)( &rs_trace_store128 ),
         mkIRExprVec_6(store_addr, store_data1, store_data2, mkIRExpr_HWord(store_size), shadow_addr, shadow_data)
         );
      break;
   }
   case Ity_V256: {
      // XXX FIXME worry about these cases after the demo
      addStmtToIRSB( sbOut, st ); 
      return;

      IRExpr* store_data1 = assignNew('V', sbOut, Ity_I64, IRExpr_Unop(Iop_V256to64_0, store_data));
      IRExpr* store_data2 = assignNew('V', sbOut, Ity_I64, IRExpr_Unop(Iop_V256to64_1, store_data));
      IRExpr* store_data3 = assignNew('V', sbOut, Ity_I64, IRExpr_Unop(Iop_V256to64_2, store_data));
      IRExpr* store_data4 = assignNew('V', sbOut, Ity_I64, IRExpr_Unop(Iop_V256to64_3, store_data));
      di = unsafeIRDirty_0_N(
         0,
         "rs_trace_store256",
         VG_(fnptr_to_fnentry)( &rs_trace_store256 ),
         mkIRExprVec_8(store_addr, store_data1, store_data2, store_data3, store_data4, mkIRExpr_HWord(store_size), shadow_addr, shadow_data)
         );
      break;
   }
   default:
      tl_assert(0); // unreachable
   }
   addStmtToIRSB( sbOut, IRStmt_Dirty(di) );
   addStmtToIRSB( sbOut, st ); 
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

   /* Set up SB. As this says, it copies everything except the statement list.
      That means it copies the type enviroment and the basic-block control-flow
      structure.
    */
   sbOut = deepCopyIRSBExceptStmts(sbIn);
   IRTypeEnv* tyenv = sbOut->tyenv;

   Int      i;
   IRStmt** sts2;

   for (i = 0; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st) continue;
      switch (st->tag) {
         // == LOAD+STORE instructions ==

         // `t<tmp> = <data>` assigns value to an (SSA) temporary.
      case Ist_WrTmp: {
         IRExpr* shadow_data = kc_construct_shadow_eval(sbOut, st->Ist.WrTmp.data, Stmt_WrTmp_Data);
         kc_instrument_wrtmp(sbOut, st, shadow_data);
         break;
      }
         // `ST<end>(<addr>) = <data>` writes value to memory, unconditionally.
      case Ist_Store: {
         IRExpr* shadow_addr = kc_construct_shadow_eval(sbOut, st->Ist.Store.addr, Stmt_Store_Addr);
         IRExpr* shadow_data = kc_construct_shadow_eval(sbOut, st->Ist.Store.data, Stmt_Store_Data);
         kc_instrument_store(sbOut, st, shadow_addr, shadow_data);
         break;
      }
         // `t<tmp> = if (<guard>) <cvt>(LD<end>(<addr>)) else <alt>` guarded load
      case Ist_LoadG: {
         kc_instrument_loadg(sbOut, st);
         break;
      }
         // `if (<guard>) ST<end>(<addr>) = <data>` guarded store; all fields
         // unconditionally evaluated.
      case Ist_StoreG: {
         kc_instrument_storeg(sbOut, st);
         break;
      }
         // `t<tmp> = CAS<end>(<addr> :: <expected> -> <new>)` atomic compare-and-swap
      case Ist_CAS: {
         kc_instrument_cas(sbOut, st);
         break;
      }
         // `result = LD<end>-Linked(<addr>)` if STOREDATA is null
         // `result = ( ST<end>-Cond(<addr>)` if STOREDATA nonnull
      case Ist_LLSC: {
         kc_instrument_llsc(sbOut, st);
         break;
      }

         // `PUT(<offset>) = <data>` writes guest register at fixed offset
      case Ist_Put: {
         IRExpr* shadow_data = kc_construct_shadow_eval(sbOut, st->Ist.Put.data, Stmt_Put_Data);
         kc_instrument_put(sbOut, st, shadow_data);
         break;
      }
         // `PUTI<descr>[<ix>,<bias>] = <data>` writes guest register at
         // non-fixed offset
      case Ist_PutI: {
         IRExpr* shadow_ix = kc_construct_shadow_eval(sbOut, st->Ist.PutI.details->ix, Stmt_PutI_Ix);
         IRExpr* shadow_data = kc_construct_shadow_eval(sbOut, st->Ist.PutI.details->data, Stmt_PutI_Data);
         kc_instrument_puti(sbOut, st, shadow_ix, shadow_data);
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

extern Bool rs_client_request_borrow_mut ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_borrow_shr ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_as_raw ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_as_borrow_mut ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_as_borrow_shr ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_retag_fn_prologue ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_retag_assign ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_retag_raw ( ThreadId tid, UWord* arg, UWord* ret );
extern Bool rs_client_request_intrinsics_assume ( ThreadId tid, UWord* arg, UWord* ret );

static Bool kc_handle_client_request ( ThreadId tid, UWord* arg, UWord* ret )
{
   Bool  handled = False;

   if (!VG_IS_TOOL_USERREQ('K','C',arg[0]))
      return False;

   VG_(dmsg)("kc_handle_client_request, dispatching client request code %llx\n", (ULong)arg[0]);

   switch(arg[0]) {
   case VG_USERREQ__BORROW_MUT: {
      handled = rs_client_request_borrow_mut(tid, arg, ret);
      break;
   }
   case VG_USERREQ__BORROW_SHR: {
      handled = rs_client_request_borrow_shr(tid, arg, ret);
      break;
   }
   case VG_USERREQ__AS_RAW: {
      handled = rs_client_request_as_raw(tid, arg, ret);
      break;
   }
   case VG_USERREQ__AS_BORROW_MUT: {
      handled = rs_client_request_as_borrow_mut(tid, arg, ret);
      break;
   }
   case VG_USERREQ__AS_BORROW_SHR: {
      handled = rs_client_request_as_borrow_shr(tid, arg, ret);
      break;
   }
   case VG_USERREQ__RETAG_FN_PROLOGUE: {
      handled = rs_client_request_retag_fn_prologue(tid, arg, ret);
      break;
   }
   case VG_USERREQ__RETAG_ASSIGN: {
      handled = rs_client_request_retag_assign(tid, arg, ret);
      break;
   }
   case VG_USERREQ__RETAG_RAW: {
      handled = rs_client_request_retag_raw(tid, arg, ret);
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
