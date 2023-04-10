
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
#include "pub_tool_mallocfree.h"

#include "kc_include.h"

/*------------------------------------------------------------*/
/*--- Forward decls                                        ---*/
/*------------------------------------------------------------*/

struct _KCEnv;

// See below for comments explaining what this is for.
typedef
   enum __attribute__((packed)) { HuUnU=0, HuPCa=1, HuOth=2 }
   HowUsed;

static IRType  shadowTypeV ( IRType ty );
static IRExpr* expr2vbits ( struct _KCEnv* kce, IRExpr* e,
                            HowUsed hu/*use HuOth if unknown*/ );
static IRTemp  findShadowTmpB ( struct _KCEnv* kce, IRTemp orig );

static IRExpr *i128_const_zero(void);


/* See (TODO adapt) docs from mc_translate.c */
typedef
   /* TBD will _probably_ expand to Tag and Stk as distinct things. */
   enum { Orig=1, TBD=2 }
   TempKind;

/* See (TODO adapt) docs from mc_translate.c */
typedef
   struct {
      TempKind kind;
      IRTemp   shadowV;
   }
   TempMapEnt;

/* See (TODO adapt) docs from mc_translate.c */
typedef
   struct _KCEnv {
      IRSB* sb;
      Bool  trace;
      XArray* /* of TempMapEnt */ tmpMap;
      IRType hWordTy;
   }
   KCEnv;

/* See (TODO adapt) docs from mc_translate.c */
static IRTemp newTemp ( KCEnv* kce, IRType ty, TempKind kind )
{
   Word       newIx;
   TempMapEnt ent;
   IRTemp     tmp = newIRTemp(kce->sb->tyenv, ty);
   ent.kind    = kind;
   ent.shadowV = IRTemp_INVALID;
   newIx = VG_(addToXA)( kce->tmpMap, &ent );
   tl_assert(newIx == (Word)tmp);
   return tmp;
}


/* See (TODO adapt) docs from mc_translate.c */
static IRTemp findShadowTmpV ( KCEnv* kce, IRTemp orig )
{
   TempMapEnt* ent;
   /* VG_(indexXA) range-checks 'orig', hence no need to check
      here. */
   ent = (TempMapEnt*)VG_(indexXA)( kce->tmpMap, (Word)orig );
   tl_assert(ent->kind == Orig);
   if (ent->shadowV == IRTemp_INVALID) {
      IRTemp tmpV
        = newTemp( kce, shadowTypeV(kce->sb->tyenv->types[orig]), TBD );
      /* newTemp may cause kce->tmpMap to resize, hence previous results
         from VG_(indexXA) are invalid. */
      ent = (TempMapEnt*)VG_(indexXA)( kce->tmpMap, (Word)orig );
      tl_assert(ent->kind == Orig);
      tl_assert(ent->shadowV == IRTemp_INVALID);
      ent->shadowV = tmpV;
   }
   return ent->shadowV;
}

/* See (TODO adapt) docs from mc_translate.c */
static void newShadowTmpV ( KCEnv* kce, IRTemp orig )
{
   TempMapEnt* ent;
   /* VG_(indexXA) range-checks 'orig', hence no need to check
      here. */
   ent = (TempMapEnt*)VG_(indexXA)( kce->tmpMap, (Word)orig );
   tl_assert(ent->kind == Orig);
   if (1) {
      IRTemp tmpV
        = newTemp( kce, shadowTypeV(kce->sb->tyenv->types[orig]), TBD );
      /* newTemp may cause kce->tmpMap to resize, hence previous results
         from VG_(indexXA) are invalid. */
      ent = (TempMapEnt*)VG_(indexXA)( kce->tmpMap, (Word)orig );
      tl_assert(ent->kind == Orig);
      ent->shadowV = tmpV;
   }
}


/*------------------------------------------------------------*/
/*--- IRAtoms -- a subset of IRExprs                       ---*/
/*------------------------------------------------------------*/

/* An atom is either an IRExpr_Const or an IRExpr_Tmp, as defined by
   isIRAtom() in libvex_ir.h.  Because this instrumenter expects flat
   input, most of this code deals in atoms.  Usefully, a value atom
   always has a V-value which is also an atom: constants are shadowed
   by constants, and temps are shadowed by the corresponding shadow
   temporary. */

typedef  IRExpr  IRAtom;

/* (used for sanity checks only): is this an atom which looks
   like it's from original code? */
static Bool isOriginalAtom ( KCEnv* kce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_RdTmp) {
      TempMapEnt* ent = VG_(indexXA)( kce->tmpMap, a1->Iex.RdTmp.tmp );
      return ent->kind == Orig;
   }
   return False;
}

/* (used for sanity checks only): is this an atom which looks
   like it's from shadow code? */
static Bool isShadowAtom ( KCEnv* kce, IRAtom* a1 )
{
   if (a1->tag == Iex_Const)
      return True;
   if (a1->tag == Iex_RdTmp) {
      TempMapEnt* ent = VG_(indexXA)( kce->tmpMap, a1->Iex.RdTmp.tmp );
      return ent->kind == TBD;
   }
   return False;
}

/* (used for sanity checks only): check that both args are atoms and
   are identically-kinded. */
static Bool sameKindedAtoms ( IRAtom* a1, IRAtom* a2 )
{
   if (a1->tag == Iex_RdTmp && a2->tag == Iex_RdTmp)
      return True;
   if (a1->tag == Iex_Const && a2->tag == Iex_Const)
      return True;
   return False;
}


/*------------------------------------------------------------*/
/*--- Type management                                      ---*/
/*------------------------------------------------------------*/

/* Shadow state is always accessed using integer types.  This returns
   an integer type with the same size (as per sizeofIRType) as the
   given type.  The only valid shadow types are Bit, I8, I16, I32,
   I64, I128, V128, V256. */

static IRType shadowTypeV ( IRType ty )
{
   switch (ty) {
      case Ity_I1:
      case Ity_I8:
      case Ity_I16:
      case Ity_I32: 
      case Ity_I64: 
      case Ity_I128: return ty;
      case Ity_F16:  return Ity_I16;
      case Ity_F32:  return Ity_I32;
      case Ity_D32:  return Ity_I32;
      case Ity_F64:  return Ity_I64;
      case Ity_D64:  return Ity_I64;
      case Ity_F128: return Ity_I128;
      case Ity_D128: return Ity_I128;
      case Ity_V128: return Ity_V128;
      case Ity_V256: return Ity_V256;
      default: ppIRType(ty); 
               VG_(tool_panic)("memcheck:shadowTypeV");
   }
}

/* Produce a 'defined' value of the given shadow type.  Should only be
   supplied shadow types (Bit/I8/I16/I32/UI64). */
static IRExpr* definedOfType ( IRType ty ) {
   switch (ty) {
      case Ity_I1:   return IRExpr_Const(IRConst_U1(False));
      case Ity_I8:   return IRExpr_Const(IRConst_U8(0));
      case Ity_I16:  return IRExpr_Const(IRConst_U16(0));
      case Ity_I32:  return IRExpr_Const(IRConst_U32(0));
      case Ity_I64:  return IRExpr_Const(IRConst_U64(0));
      case Ity_I128: return i128_const_zero();
      case Ity_V128: return IRExpr_Const(IRConst_V128(0x0000));
      case Ity_V256: return IRExpr_Const(IRConst_V256(0x00000000));
      default:       VG_(tool_panic)("memcheck:definedOfType");
   }
}


/*------------------------------------------------------------*/
/*--- Constructing IR fragments                            ---*/
/*------------------------------------------------------------*/

/* add stmt to a bb */
static inline void stmt ( HChar cat, KCEnv* kce, IRStmt* st ) {
   if (kce->trace) {
      VG_(printf)("  %c: ", cat);
      ppIRStmt(st);
      VG_(printf)("\n");
   }
   addStmtToIRSB(kce->sb, st);
}

/* assign value to tmp */
static inline 
void assign ( HChar cat, KCEnv* kce, IRTemp tmp, IRExpr* expr ) {
   stmt(cat, kce, IRStmt_WrTmp(tmp,expr));
}

/* build various kinds of expressions */
#define triop(_op, _arg1, _arg2, _arg3) \
                                 IRExpr_Triop((_op),(_arg1),(_arg2),(_arg3))
#define binop(_op, _arg1, _arg2) IRExpr_Binop((_op),(_arg1),(_arg2))
#define unop(_op, _arg)          IRExpr_Unop((_op),(_arg))
#define mkU1(_n)                 IRExpr_Const(IRConst_U1(_n))
#define mkU8(_n)                 IRExpr_Const(IRConst_U8(_n))
#define mkU16(_n)                IRExpr_Const(IRConst_U16(_n))
#define mkU32(_n)                IRExpr_Const(IRConst_U32(_n))
#define mkU64(_n)                IRExpr_Const(IRConst_U64(_n))
#define mkV128(_n)               IRExpr_Const(IRConst_V128(_n))
#define mkexpr(_tmp)             IRExpr_RdTmp((_tmp))

/* Bind the given expression to a new temporary, and return the
   temporary.  This effectively converts an arbitrary expression into
   an atom.

   'ty' is the type of 'e' and hence the type that the new temporary
   needs to be.  But passing it in is redundant, since we can deduce
   the type merely by inspecting 'e'.  So at least use that fact to
   assert that the two types agree. */
static IRAtom* assignNew ( HChar cat, KCEnv* kce, IRType ty, IRExpr* e )
{
   TempKind k;
   IRTemp   t;
   IRType   tyE = typeOfIRExpr(kce->sb->tyenv, e);

   tl_assert(tyE == ty); /* so 'ty' is redundant (!) */
   switch (cat) {
      case 'V': k = TBD;  break;
      case 'C': k = Orig; break; 
                /* happens when we are making up new "orig"
                   expressions, for IRCAS handling */
      default: tl_assert(0);
   }
   t = newTemp(kce, ty, k);
   assign(cat, kce, t, e);
   return mkexpr(t);
}


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
   Bool       verboze = 0||False;
   IRDirty*   di;
   KCEnv      kce;
   IRSB*      sbOut;
   IRTypeEnv* tyenv = sbIn->tyenv;
   Int        i, j;
   IRStmt*    st;
   IRStmt**   sts2;

   /* Set up SB. As this says, it copies everything except the statement list.
      That means it copies the type enviroment and the basic-block control-flow
      structure.
    */
   sbOut = deepCopyIRSBExceptStmts(sbIn);

   VG_(memset)(&kce, 0, sizeof(kce));
   kce.sb             = sbOut;
   kce.trace          = verboze;
   kce.hWordTy        = hWordTy;

   /* Initialise the running the tmp environment. */

   kce.tmpMap = VG_(newXA)( VG_(malloc), "kc.KC_(instrument).1", VG_(free),
                            sizeof(TempMapEnt));
   VG_(hintSizeXA) (kce.tmpMap, sbIn->tyenv->types_used);
   for (i = 0; i < sbIn->tyenv->types_used; i++) {
      TempMapEnt ent;
      ent.kind    = Orig;
      ent.shadowV = IRTemp_INVALID;
      VG_(addToXA)( kce.tmpMap, &ent );
   }
   tl_assert( VG_(sizeXA)( kce.tmpMap ) == sbIn->tyenv->types_used );

   /* Finally, begin instrumentation. */

   tl_assert(kce.sb == sbOut);
   tl_assert(kce.sb != sbIn);

   /* Copy verbatim any IR preamble preceding the first IMark */

   i = 0;
   while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
      st = sbIn->stmts[i];
      tl_assert(st);
      tl_assert(isFlatIRStmt(st));

      stmt( 'C', &kce, sbIn->stmts[i] );
      i++;
   }

   /*
     Scans the preamble looking for assignments to temporaries. For each one
     found it creates an assignment to the corresponding (V) shadow temp,
     marking it as 'defined'. This is the same resulting IR as if the main
     instrumentation loop before had been applied to the statement
     'tmp = CONSTANT'.
   */
   for (j = 0; j < i; j++) {
      if (sbIn->stmts[j]->tag == Ist_WrTmp) {
         /* findShadowTmpV checks its arg is an original tmp;
            no need to assert that here. */
         IRTemp tmp_o = sbIn->stmts[j]->Ist.WrTmp.tmp;
         IRTemp tmp_v = findShadowTmpV(&kce, tmp_o);
         IRType ty_v  = typeOfIRTemp(sbOut->tyenv, tmp_v);
         assign( 'V', &kce, tmp_v, definedOfType( ty_v ) );
      }
   }

   /* Iterate over the remaining stmts to generate instrumentation. */

   tl_assert(sbIn->stmts_used > 0);
   tl_assert(i >= 0);
   tl_assert(i < sbIn->stmts_used);
   tl_assert(sbIn->stmts[i]->tag == Ist_IMark);

   /* XXX resume comparison against mc_translate.c here XXX */
   
   for (/* use current i*/; i < sbIn->stmts_used; i++) {
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

/*------------------------------------------------------------*/
/*--- Helper functions for 128-bit ops                     ---*/
/*------------------------------------------------------------*/

static IRExpr *i128_const_zero(void)
{
   IRAtom* z64 = IRExpr_Const(IRConst_U64(0));
   return binop(Iop_64HLto128, z64, z64);
}
