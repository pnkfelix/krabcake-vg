
/*--------------------------------------------------------------------*/
/*--- Instrument IR to check borrow validty.        kc_translate.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Krabcake, the Rust-validating Valgrind tool,
   which attempts to detect undefined behavior in Rust programs.

   Copyright (C) 2023 Felix S Klock II
      pnkfelix@pnkfx.org
   adapted from mc_translate.c, Copyright (C) 2000-2017 Julian Seward
      jseward@acm.org

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

/* N.B.: mc_translate has a special HowUsed argument, hu, used to specialize
   binop codegen when it can. We are going to try to get away without using that
   at all. (But its possible we might need it too, because we too will be doing
   things like computing memory addresses via adds/subs, and those seem to be
   makred as HuPCa in some scenarios via a preInstrumentationAnalysis.
 */ 
static IRExpr* expr2vbits ( struct _KCEnv* kce, IRExpr* e );

static IRTemp  findShadowTmpB ( struct _KCEnv* kce, IRTemp orig );

static IRExpr *i128_const_zero(void);

/*------------------------------------------------------------*/
/*--- Memcheck running state, and tmp management.          ---*/
/*------------------------------------------------------------*/

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

      /* READONLY: the guest layout. */
      const VexGuestLayout* layout;

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

/*------------------------------------------------------------*/
/*--- Helper functions for 128-bit ops                     ---*/
/*------------------------------------------------------------*/

static IRExpr *i128_const_zero(void)
{
   IRAtom* z64 = IRExpr_Const(IRConst_U64(0));
   return binop(Iop_64HLto128, z64, z64);
}

/*------------------------------------------------------------*/
/*--- Constructing definedness primitive ops               ---*/
/*------------------------------------------------------------*/


/* --------- Defined-if-either-defined --------- */

static IRAtom* mkDifD1 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I1, binop(Iop_And1, a1, a2));
}

static IRAtom* mkDifD8 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I8, binop(Iop_And8, a1, a2));
}

static IRAtom* mkDifD16 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I16, binop(Iop_And16, a1, a2));
}

static IRAtom* mkDifD32 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I32, binop(Iop_And32, a1, a2));
}

static IRAtom* mkDifD64 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I64, binop(Iop_And64, a1, a2));
}

static IRAtom* mkDifDV128 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_V128, binop(Iop_AndV128, a1, a2));
}

static IRAtom* mkDifDV256 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_V256, binop(Iop_AndV256, a1, a2));
}

/* --------- Undefined-if-either-undefined --------- */

static IRAtom* mkUifU1 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I1, binop(Iop_Or1, a1, a2));
}

static IRAtom* mkUifU8 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I8, binop(Iop_Or8, a1, a2));
}

static IRAtom* mkUifU16 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I16, binop(Iop_Or16, a1, a2));
}

static IRAtom* mkUifU32 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I32, binop(Iop_Or32, a1, a2));
}

static IRAtom* mkUifU64 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_I64, binop(Iop_Or64, a1, a2));
}

static IRAtom* mkUifU128 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   IRAtom *tmp1, *tmp2, *tmp3, *tmp4, *tmp5, *tmp6;
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   tmp1 = assignNew('V', kce, Ity_I64, unop(Iop_128to64, a1));
   tmp2 = assignNew('V', kce, Ity_I64, unop(Iop_128HIto64, a1));
   tmp3 = assignNew('V', kce, Ity_I64, unop(Iop_128to64, a2));
   tmp4 = assignNew('V', kce, Ity_I64, unop(Iop_128HIto64, a2));
   tmp5 = assignNew('V', kce, Ity_I64, binop(Iop_Or64, tmp1, tmp3));
   tmp6 = assignNew('V', kce, Ity_I64, binop(Iop_Or64, tmp2, tmp4));

   return assignNew('V', kce, Ity_I128, binop(Iop_64HLto128, tmp6, tmp5));
}

static IRAtom* mkUifUV128 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_V128, binop(Iop_OrV128, a1, a2));
}

static IRAtom* mkUifUV256 ( KCEnv* kce, IRAtom* a1, IRAtom* a2 ) {
   tl_assert(isShadowAtom(kce,a1));
   tl_assert(isShadowAtom(kce,a2));
   return assignNew('V', kce, Ity_V256, binop(Iop_OrV256, a1, a2));
}

static IRAtom* mkUifU ( KCEnv* kce, IRType vty, IRAtom* a1, IRAtom* a2 ) {
   switch (vty) {
      case Ity_I8:   return mkUifU8(kce, a1, a2);
      case Ity_I16:  return mkUifU16(kce, a1, a2);
      case Ity_I32:  return mkUifU32(kce, a1, a2);
      case Ity_I64:  return mkUifU64(kce, a1, a2);
      case Ity_I128: return mkUifU128(kce, a1, a2);
      case Ity_V128: return mkUifUV128(kce, a1, a2);
      case Ity_V256: return mkUifUV256(kce, a1, a2);
      default:
         VG_(printf)("\n"); ppIRType(vty); VG_(printf)("\n");
         VG_(tool_panic)("memcheck:mkUifU");
   }
}

/* --------- The Left-family of operations. --------- */

static IRAtom* mkLeft8 ( KCEnv* kce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(kce,a1));
   return assignNew('V', kce, Ity_I8, unop(Iop_Left8, a1));
}

static IRAtom* mkLeft16 ( KCEnv* kce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(kce,a1));
   return assignNew('V', kce, Ity_I16, unop(Iop_Left16, a1));
}

static IRAtom* mkLeft32 ( KCEnv* kce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(kce,a1));
   return assignNew('V', kce, Ity_I32, unop(Iop_Left32, a1));
}

static IRAtom* mkLeft64 ( KCEnv* kce, IRAtom* a1 ) {
   tl_assert(isShadowAtom(kce,a1));
   return assignNew('V', kce, Ity_I64, unop(Iop_Left64, a1));
}

/* --------- The Right-family of operations. --------- */

/* Unfortunately these are a lot more expensive then their Left
   counterparts.  Fortunately they are only very rarely used -- only for
   count-leading-zeroes instrumentation. */

static IRAtom* mkRight32 ( KCEnv* kce, IRAtom* a1 )
{
   for (Int i = 1; i <= 16; i *= 2) {
      // a1 |= (a1 >>u i)
      IRAtom* tmp
         = assignNew('V', kce, Ity_I32, binop(Iop_Shr32, a1, mkU8(i)));
      a1 = assignNew('V', kce, Ity_I32, binop(Iop_Or32, a1, tmp));
   }
   return a1;
}

static IRAtom* mkRight64 ( KCEnv* kce, IRAtom* a1 )
{
   for (Int i = 1; i <= 32; i *= 2) {
      // a1 |= (a1 >>u i)
      IRAtom* tmp
         = assignNew('V', kce, Ity_I64, binop(Iop_Shr64, a1, mkU8(i)));
      a1 = assignNew('V', kce, Ity_I64, binop(Iop_Or64, a1, tmp));
   }
   return a1;
}

/* --------- 'Improvement' functions for AND/OR. --------- */

/* ImproveAND(data, vbits) = data OR vbits.  Defined (0) data 0s give
   defined (0); all other -> undefined (1).
*/
static IRAtom* mkImproveAND1 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_I1, binop(Iop_Or1, data, vbits));
}

static IRAtom* mkImproveAND8 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_I8, binop(Iop_Or8, data, vbits));
}

static IRAtom* mkImproveAND16 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_I16, binop(Iop_Or16, data, vbits));
}

static IRAtom* mkImproveAND32 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_I32, binop(Iop_Or32, data, vbits));
}

static IRAtom* mkImproveAND64 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_I64, binop(Iop_Or64, data, vbits));
}

static IRAtom* mkImproveANDV128 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_V128, binop(Iop_OrV128, data, vbits));
}

static IRAtom* mkImproveANDV256 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew('V', kce, Ity_V256, binop(Iop_OrV256, data, vbits));
}

/* ImproveOR(data, vbits) = ~data OR vbits.  Defined (0) data 1s give
   defined (0); all other -> undefined (1).
*/
static IRAtom* mkImproveOR1 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_I1, 
             binop(Iop_Or1, 
                   assignNew('V', kce, Ity_I1, unop(Iop_Not1, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR8 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_I8, 
             binop(Iop_Or8, 
                   assignNew('V', kce, Ity_I8, unop(Iop_Not8, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR16 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_I16, 
             binop(Iop_Or16, 
                   assignNew('V', kce, Ity_I16, unop(Iop_Not16, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR32 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_I32, 
             binop(Iop_Or32, 
                   assignNew('V', kce, Ity_I32, unop(Iop_Not32, data)), 
                   vbits) );
}

static IRAtom* mkImproveOR64 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_I64, 
             binop(Iop_Or64, 
                   assignNew('V', kce, Ity_I64, unop(Iop_Not64, data)), 
                   vbits) );
}

static IRAtom* mkImproveORV128 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_V128, 
             binop(Iop_OrV128, 
                   assignNew('V', kce, Ity_V128, unop(Iop_NotV128, data)), 
                   vbits) );
}

static IRAtom* mkImproveORV256 ( KCEnv* kce, IRAtom* data, IRAtom* vbits )
{
   tl_assert(isOriginalAtom(kce, data));
   tl_assert(isShadowAtom(kce, vbits));
   tl_assert(sameKindedAtoms(data, vbits));
   return assignNew(
             'V', kce, Ity_V256, 
             binop(Iop_OrV256, 
                   assignNew('V', kce, Ity_V256, unop(Iop_NotV256, data)), 
                   vbits) );
}

/* --------- Pessimising casts. --------- */

/* The function returns an expression of type DST_TY. If any of the VBITS
   is undefined (value == 1) the resulting expression has all bits set to
   1. Otherwise, all bits are 0. */

static IRAtom* mkPCastTo( KCEnv* kce, IRType dst_ty, IRAtom* vbits ) 
{
   IRType  src_ty;
   IRAtom* tmp1;

   /* Note, dst_ty is a shadow type, not an original type. */
   tl_assert(isShadowAtom(kce,vbits));
   src_ty = typeOfIRExpr(kce->sb->tyenv, vbits);

   /* Fast-track some common cases */
   if (src_ty == Ity_I32 && dst_ty == Ity_I32)
      return assignNew('V', kce, Ity_I32, unop(Iop_CmpwNEZ32, vbits));

   if (src_ty == Ity_I64 && dst_ty == Ity_I64)
      return assignNew('V', kce, Ity_I64, unop(Iop_CmpwNEZ64, vbits));

   if (src_ty == Ity_I32 && dst_ty == Ity_I64) {
      /* PCast the arg, then clone it. */
      IRAtom* tmp = assignNew('V', kce, Ity_I32, unop(Iop_CmpwNEZ32, vbits));
      return assignNew('V', kce, Ity_I64, binop(Iop_32HLto64, tmp, tmp));
   }

   if (src_ty == Ity_I32 && dst_ty == Ity_V128) {
      /* PCast the arg, then clone it 4 times. */
      IRAtom* tmp = assignNew('V', kce, Ity_I32, unop(Iop_CmpwNEZ32, vbits));
      tmp = assignNew('V', kce, Ity_I64, binop(Iop_32HLto64, tmp, tmp));
      return assignNew('V', kce, Ity_V128, binop(Iop_64HLtoV128, tmp, tmp));
   }

   if (src_ty == Ity_I32 && dst_ty == Ity_V256) {
      /* PCast the arg, then clone it 8 times. */
      IRAtom* tmp = assignNew('V', kce, Ity_I32, unop(Iop_CmpwNEZ32, vbits));
      tmp = assignNew('V', kce, Ity_I64, binop(Iop_32HLto64, tmp, tmp));
      tmp = assignNew('V', kce, Ity_V128, binop(Iop_64HLtoV128, tmp, tmp));
      return assignNew('V', kce, Ity_V256, binop(Iop_V128HLtoV256, tmp, tmp));
   }

   if (src_ty == Ity_I64 && dst_ty == Ity_I32) {
      /* PCast the arg.  This gives all 0s or all 1s.  Then throw away
         the top half. */
      IRAtom* tmp = assignNew('V', kce, Ity_I64, unop(Iop_CmpwNEZ64, vbits));
      return assignNew('V', kce, Ity_I32, unop(Iop_64to32, tmp));
   }

   if (src_ty == Ity_V128 && dst_ty == Ity_I64) {
      /* Use InterleaveHI64x2 to copy the top half of the vector into
         the bottom half.  Then we can UifU it with the original, throw
         away the upper half of the result, and PCast-I64-to-I64
         the lower half. */
      // Generates vbits[127:64] : vbits[127:64]
      IRAtom* hi64hi64
         = assignNew('V', kce, Ity_V128,
                     binop(Iop_InterleaveHI64x2, vbits, vbits));
      // Generates
      //   UifU(vbits[127:64],vbits[127:64]) : UifU(vbits[127:64],vbits[63:0])
      //   == vbits[127:64] : UifU(vbits[127:64],vbits[63:0])
      IRAtom* lohi64 
         = mkUifUV128(kce, hi64hi64, vbits);
      // Generates UifU(vbits[127:64],vbits[63:0])
      IRAtom* lo64
         = assignNew('V', kce, Ity_I64, unop(Iop_V128to64, lohi64));
      // Generates
      //   PCast-to-I64( UifU(vbits[127:64], vbits[63:0] )
      //   == PCast-to-I64( vbits[127:0] )
      IRAtom* res
         = assignNew('V', kce, Ity_I64, unop(Iop_CmpwNEZ64, lo64));
      return res;
   }

   /* Else do it the slow way .. */
   /* First of all, collapse vbits down to a single bit. */
   tmp1   = NULL;
   switch (src_ty) {
      case Ity_I1:
         tmp1 = vbits;
         break;
      case Ity_I8: 
         tmp1 = assignNew('V', kce, Ity_I1, unop(Iop_CmpNEZ8, vbits));
         break;
      case Ity_I16: 
         tmp1 = assignNew('V', kce, Ity_I1, unop(Iop_CmpNEZ16, vbits));
         break;
      case Ity_I32: 
         tmp1 = assignNew('V', kce, Ity_I1, unop(Iop_CmpNEZ32, vbits));
         break;
      case Ity_I64: 
         tmp1 = assignNew('V', kce, Ity_I1, unop(Iop_CmpNEZ64, vbits));
         break;
      case Ity_I128: {
         /* Gah.  Chop it in half, OR the halves together, and compare
            that with zero. */
         IRAtom* tmp2 = assignNew('V', kce, Ity_I64, unop(Iop_128HIto64, vbits));
         IRAtom* tmp3 = assignNew('V', kce, Ity_I64, unop(Iop_128to64, vbits));
         IRAtom* tmp4 = assignNew('V', kce, Ity_I64, binop(Iop_Or64, tmp2, tmp3));
         tmp1         = assignNew('V', kce, Ity_I1, 
                                       unop(Iop_CmpNEZ64, tmp4));
         break;
      }
      case Ity_V128: {
         /* Chop it in half, OR the halves together, and compare that
          * with zero.
          */
         IRAtom* tmp2 = assignNew('V', kce, Ity_I64, unop(Iop_V128HIto64, vbits));
         IRAtom* tmp3 = assignNew('V', kce, Ity_I64, unop(Iop_V128to64, vbits));
         IRAtom* tmp4 = assignNew('V', kce, Ity_I64, binop(Iop_Or64, tmp2, tmp3));
         tmp1         = assignNew('V', kce, Ity_I1,
                                       unop(Iop_CmpNEZ64, tmp4));
         break;
      }
      default:
         ppIRType(src_ty);
         VG_(tool_panic)("mkPCastTo(1)");
   }
   tl_assert(tmp1);
   /* Now widen up to the dst type. */
   switch (dst_ty) {
      case Ity_I1:
         return tmp1;
      case Ity_I8: 
         return assignNew('V', kce, Ity_I8, unop(Iop_1Sto8, tmp1));
      case Ity_I16: 
         return assignNew('V', kce, Ity_I16, unop(Iop_1Sto16, tmp1));
      case Ity_I32: 
         return assignNew('V', kce, Ity_I32, unop(Iop_1Sto32, tmp1));
      case Ity_I64: 
         return assignNew('V', kce, Ity_I64, unop(Iop_1Sto64, tmp1));
      case Ity_V128:
         tmp1 = assignNew('V', kce, Ity_I64,  unop(Iop_1Sto64, tmp1));
         tmp1 = assignNew('V', kce, Ity_V128, binop(Iop_64HLtoV128, tmp1, tmp1));
         return tmp1;
      case Ity_I128:
         tmp1 = assignNew('V', kce, Ity_I64,  unop(Iop_1Sto64, tmp1));
         tmp1 = assignNew('V', kce, Ity_I128, binop(Iop_64HLto128, tmp1, tmp1));
         return tmp1;
      case Ity_V256:
         tmp1 = assignNew('V', kce, Ity_I64,  unop(Iop_1Sto64, tmp1));
         tmp1 = assignNew('V', kce, Ity_V128, binop(Iop_64HLtoV128,
                                                    tmp1, tmp1));
         tmp1 = assignNew('V', kce, Ity_V256, binop(Iop_V128HLtoV256,
                                                    tmp1, tmp1));
         return tmp1;
      default: 
         ppIRType(dst_ty);
         VG_(tool_panic)("mkPCastTo(2)");
   }
}

/* This is a minor variant.  It takes an arg of some type and returns
   a value of the same type.  The result consists entirely of Defined
   (zero) bits except its least significant bit, which is a PCast of
   the entire argument down to a single bit. */
static IRAtom* mkPCastXXtoXXlsb ( KCEnv* kce, IRAtom* varg, IRType ty )
{
   if (ty == Ity_V128) {
      /* --- Case for V128 --- */
      IRAtom* varg128 = varg;
      // generates: PCast-to-I64(varg128)
      IRAtom* pcdTo64 = mkPCastTo(kce, Ity_I64, varg128);
      // Now introduce zeros (defined bits) in the top 63 places
      // generates: Def--(63)--Def PCast-to-I1(varg128)
      IRAtom* d63pc 
         = assignNew('V', kce, Ity_I64, binop(Iop_And64, pcdTo64, mkU64(1)));
      // generates: Def--(64)--Def
      IRAtom* d64
         = definedOfType(Ity_I64);
      // generates: Def--(127)--Def PCast-to-I1(varg128)
      IRAtom* res
         = assignNew('V', kce, Ity_V128, binop(Iop_64HLtoV128, d64, d63pc));
      return res;
   }
   if (ty == Ity_I64) {
      /* --- Case for I64 --- */
      // PCast to 64
      IRAtom* pcd = mkPCastTo(kce, Ity_I64, varg);
      // Zero (Def) out the top 63 bits
      IRAtom* res 
         = assignNew('V', kce, Ity_I64, binop(Iop_And64, pcd, mkU64(1)));   
      return res;
   }
   /*NOTREACHED*/
   tl_assert(0);
}

/* --------- Optimistic casts. --------- */

/* The function takes and returns an expression of type TY. If any of the
   VBITS indicate defined (value == 0) the resulting expression has all bits
   set to 0. Otherwise, all bits are 1.  In words, if any bits are defined
   then all bits are made to be defined.

   In short we compute (vbits - (vbits >>u 1)) >>s (bitsize(vbits)-1).
*/
static IRAtom* mkOCastAt( KCEnv* kce, IRType ty, IRAtom* vbits )
{
   IROp opSUB, opSHR, opSAR;
   UInt sh;

   switch (ty) {
      case Ity_I64:
         opSUB = Iop_Sub64; opSHR = Iop_Shr64; opSAR = Iop_Sar64; sh = 63;
         break;
      case Ity_I32:
         opSUB = Iop_Sub32; opSHR = Iop_Shr32; opSAR = Iop_Sar32; sh = 31;
         break;
      case Ity_I16:
         opSUB = Iop_Sub16; opSHR = Iop_Shr16; opSAR = Iop_Sar16; sh = 15;
         break;
      case Ity_I8:
         opSUB = Iop_Sub8; opSHR = Iop_Shr8; opSAR = Iop_Sar8; sh = 7;
         break;
      default:
         ppIRType(ty);
         VG_(tool_panic)("mkOCastTo");
   }

   IRAtom *shr1, *at;
   shr1 = assignNew('V', kce,ty, binop(opSHR, vbits, mkU8(1)));
   at   = assignNew('V', kce,ty, binop(opSUB, vbits, shr1));
   at   = assignNew('V', kce,ty, binop(opSAR, at, mkU8(sh)));
   return at;
}


/* --------- Accurate interpretation of CmpEQ/CmpNE. --------- */
/* 
   Normally, we can do CmpEQ/CmpNE by doing UifU on the arguments, and
   PCasting to Ity_U1.  However, sometimes it is necessary to be more
   accurate.  The insight is that the result is defined if two
   corresponding bits can be found, one from each argument, so that
   both bits are defined but are different -- that makes EQ say "No"
   and NE say "Yes".  Hence, we compute an improvement term and DifD
   it onto the "normal" (UifU) result.

   The result is:

   PCastTo<1> (
      -- naive version
      UifU<sz>(vxx, vyy)

      `DifD<sz>`

      -- improvement term
      OCast<sz>(vec)
   )

   where
     vec contains 0 (defined) bits where the corresponding arg bits 
     are defined but different, and 1 bits otherwise.

     vec = Or<sz>( vxx,   // 0 iff bit defined
                   vyy,   // 0 iff bit defined
                   Not<sz>(Xor<sz>( xx, yy )) // 0 iff bits different
                 )

     If any bit of vec is 0, the result is defined and so the 
     improvement term should produce 0...0, else it should produce
     1...1.

     Hence require for the improvement term:

        OCast(vec) = if vec == 1...1 then 1...1 else 0...0

     which you can think of as an "optimistic cast" (OCast, the opposite of
     the normal "pessimistic cast" (PCast) family.  An OCast says all bits
     are defined if any bit is defined.

     It is possible to show that

         if vec == 1...1 then 1...1 else 0...0

     can be implemented in straight-line code as

         (vec - (vec >>u 1)) >>s (word-size-in-bits - 1)

   We note that vec contains the sub-term Or<sz>(vxx, vyy).  Since UifU is
   implemented with Or (since 1 signifies undefinedness), this is a
   duplicate of the UifU<sz>(vxx, vyy) term and so we can CSE it out, giving
   a final version of:

   let naive = UifU<sz>(vxx, vyy)
       vec   = Or<sz>(naive, Not<sz>(Xor<sz)(xx, yy))
   in
       PCastTo<1>( DifD<sz>(naive, OCast<sz>(vec)) )

   This was extensively re-analysed and checked on 6 July 05 and again
   in July 2017.
*/
static IRAtom* expensiveCmpEQorNE ( KCEnv*  kce,
                                    IRType  ty,
                                    IRAtom* vxx, IRAtom* vyy, 
                                    IRAtom* xx,  IRAtom* yy )
{
   IRAtom *naive, *vec, *improved, *final_cast;
   IROp   opDIFD, opUIFU, opOR, opXOR, opNOT;

   tl_assert(isShadowAtom(kce,vxx));
   tl_assert(isShadowAtom(kce,vyy));
   tl_assert(isOriginalAtom(kce,xx));
   tl_assert(isOriginalAtom(kce,yy));
   tl_assert(sameKindedAtoms(vxx,xx));
   tl_assert(sameKindedAtoms(vyy,yy));
 
   switch (ty) {
      case Ity_I8:
         opDIFD = Iop_And8;
         opUIFU = Iop_Or8;
         opOR   = Iop_Or8;
         opXOR  = Iop_Xor8;
         opNOT  = Iop_Not8;
         break;
      case Ity_I16:
         opDIFD = Iop_And16;
         opUIFU = Iop_Or16;
         opOR   = Iop_Or16;
         opXOR  = Iop_Xor16;
         opNOT  = Iop_Not16;
         break;
      case Ity_I32:
         opDIFD = Iop_And32;
         opUIFU = Iop_Or32;
         opOR   = Iop_Or32;
         opXOR  = Iop_Xor32;
         opNOT  = Iop_Not32;
         break;
      case Ity_I64:
         opDIFD = Iop_And64;
         opUIFU = Iop_Or64;
         opOR   = Iop_Or64;
         opXOR  = Iop_Xor64;
         opNOT  = Iop_Not64;
         break;
      default:
         VG_(tool_panic)("expensiveCmpEQorNE");
   }

   naive 
      = assignNew('V', kce, ty, binop(opUIFU, vxx, vyy));

   vec 
      = assignNew(
           'V', kce,ty, 
           binop( opOR,
                  naive,
                  assignNew(
                     'V', kce,ty,
                     unop(opNOT,
                          assignNew('V', kce,ty, binop(opXOR, xx, yy))))));

   improved
      = assignNew( 'V', kce,ty, 
                   binop(opDIFD, naive, mkOCastAt(kce, ty, vec)));

   final_cast
      = mkPCastTo( kce, Ity_I1, improved );

   return final_cast;
}


/* --------- Semi-accurate interpretation of CmpORD. --------- */

/* CmpORD32{S,U} does PowerPC-style 3-way comparisons:

      CmpORD32S(x,y) = 1<<3   if  x <s y
                     = 1<<2   if  x >s y
                     = 1<<1   if  x == y

   and similarly the unsigned variant.  The default interpretation is:

      CmpORD32{S,U}#(x,y,x#,y#) = PCast(x# `UifU` y#)  
                                  & (7<<1)

   The "& (7<<1)" reflects the fact that all result bits except 3,2,1
   are zero and therefore defined (viz, zero).

   Also deal with a special case better:

      CmpORD32S(x,0)

   Here, bit 3 (LT) of the result is a copy of the top bit of x and
   will be defined even if the rest of x isn't.  In which case we do:

      CmpORD32S#(x,x#,0,{impliedly 0}#)
         = PCast(x#) & (3<<1)      -- standard interp for GT#,EQ#
           | (x# >>u 31) << 3      -- LT# = x#[31]

   Analogous handling for CmpORD64{S,U}.
*/
static Bool isZeroU32 ( IRAtom* e )
{
   return
      toBool( e->tag == Iex_Const
              && e->Iex.Const.con->tag == Ico_U32
              && e->Iex.Const.con->Ico.U32 == 0 );
}

static Bool isZeroU64 ( IRAtom* e )
{
   return
      toBool( e->tag == Iex_Const
              && e->Iex.Const.con->tag == Ico_U64
              && e->Iex.Const.con->Ico.U64 == 0 );
}

static IRAtom* doCmpORD ( KCEnv*  kce,
                          IROp    cmp_op,
                          IRAtom* xxhash, IRAtom* yyhash, 
                          IRAtom* xx,     IRAtom* yy )
{
   Bool   m64      = cmp_op == Iop_CmpORD64S || cmp_op == Iop_CmpORD64U;
   Bool   syned    = cmp_op == Iop_CmpORD64S || cmp_op == Iop_CmpORD32S;
   IROp   opOR     = m64 ? Iop_Or64   : Iop_Or32;
   IROp   opAND    = m64 ? Iop_And64  : Iop_And32;
   IROp   opSHL    = m64 ? Iop_Shl64  : Iop_Shl32;
   IROp   opSHR    = m64 ? Iop_Shr64  : Iop_Shr32;
   IROp   op1UtoWS = m64 ? Iop_1Uto64 : Iop_1Uto32;
   IRType ty       = m64 ? Ity_I64    : Ity_I32;
   Int    width    = m64 ? 64         : 32;

   Bool (*isZero)(IRAtom*) = m64 ? isZeroU64 : isZeroU32;

   tl_assert(isShadowAtom(kce,xxhash));
   tl_assert(isShadowAtom(kce,yyhash));
   tl_assert(isOriginalAtom(kce,xx));
   tl_assert(isOriginalAtom(kce,yy));
   tl_assert(sameKindedAtoms(xxhash,xx));
   tl_assert(sameKindedAtoms(yyhash,yy));
   tl_assert(cmp_op == Iop_CmpORD32S || cmp_op == Iop_CmpORD32U
             || cmp_op == Iop_CmpORD64S || cmp_op == Iop_CmpORD64U);

   if (0) {
      ppIROp(cmp_op); VG_(printf)(" "); 
      ppIRExpr(xx); VG_(printf)(" "); ppIRExpr( yy ); VG_(printf)("\n");
   }

   if (syned && isZero(yy)) {
      /* fancy interpretation */
      /* if yy is zero, then it must be fully defined (zero#). */
      tl_assert(isZero(yyhash));
      // This is still inaccurate, but I don't think it matters, since
      // nobody writes code of the form
      // "is <partially-undefined-value> signedly greater than zero?".
      // We therefore simply declare "x >s 0" to be undefined if any bit in
      // x is undefined.  That's clearly suboptimal in some cases.  Eg, if
      // the highest order bit is a defined 1 then x is negative so it
      // doesn't matter whether the remaining bits are defined or not.
      IRAtom* t_0_gt_0_0
         = assignNew(
              'V', kce,ty,
              binop(
                 opAND,
                 mkPCastTo(kce,ty, xxhash),
                 m64 ? mkU64(1<<2) : mkU32(1<<2)
              ));
      // For "x <s 0", we can just copy the definedness of the top bit of x
      // and we have a precise result.
      IRAtom* t_lt_0_0_0
         = assignNew(
              'V', kce,ty,
              binop(
                 opSHL,
                 assignNew(
                    'V', kce,ty,
                    binop(opSHR, xxhash, mkU8(width-1))),
                 mkU8(3)
              ));
      // For "x == 0" we can hand the problem off to expensiveCmpEQorNE.
      IRAtom* t_0_0_eq_0
         = assignNew(
              'V', kce,ty,
              binop(
                 opSHL,
                 assignNew('V', kce,ty,
                    unop(
                    op1UtoWS,
                    expensiveCmpEQorNE(kce, ty, xxhash, yyhash, xx, yy))
                 ),
                 mkU8(1)
              ));
      return
         binop(
            opOR,
            assignNew('V', kce,ty, binop(opOR, t_lt_0_0_0, t_0_gt_0_0)),
            t_0_0_eq_0
         );
   } else {
      /* standard interpretation */
      IRAtom* sevenLeft1 = m64 ? mkU64(7<<1) : mkU32(7<<1);
      return 
         binop( 
            opAND, 
            mkPCastTo( kce,ty,
                       mkUifU(kce,ty, xxhash,yyhash)),
            sevenLeft1
         );
   }
}

/*------------------------------------------------------------*/
/*--- Emit a test and complaint if something is undefined. ---*/
/*------------------------------------------------------------*/

static IRAtom* schemeE ( KCEnv* kce, IRExpr* e ); /* fwds */

/* Set the annotations on a dirty helper to indicate that the stack
   pointer and instruction pointers might be read.  This is the
   behaviour of all 'emit-a-complaint' style functions we might
   call. */

static void setHelperAnns ( KCEnv* kce, IRDirty* di )
{
   di->nFxState = 2;
   di->fxState[0].fx        = Ifx_Read;
   di->fxState[0].offset    = kce->layout->offset_SP;
   di->fxState[0].size      = kce->layout->sizeof_SP;
   di->fxState[0].nRepeats  = 0;
   di->fxState[0].repeatLen = 0;
   di->fxState[1].fx        = Ifx_Read;
   di->fxState[1].offset    = kce->layout->offset_IP;
   di->fxState[1].size      = kce->layout->sizeof_IP;
   di->fxState[1].nRepeats  = 0;
   di->fxState[1].repeatLen = 0;
}

static void complainIfUndefined ( KCEnv* kce, IRAtom* atom, IRExpr *guard )
{
   IRAtom*  vatom;
   IRType   ty;
   Int      sz;
   IRDirty* di;
   IRAtom*  cond;
   void*    fn;
   const HChar* nm;
   IRExpr** args;
   Int      nargs;

   if (guard)
      tl_assert(isOriginalAtom(kce, guard));

   tl_assert(isOriginalAtom(kce, atom));
   vatom = expr2vbits( kce, atom );
   tl_assert(isShadowAtom(kce, vatom));
   tl_assert(sameKindedAtoms(atom, vatom));

   ty = typeOfIRExpr(kce->sb->tyenv, vatom);

   /* sz is only used for constructing the error message */
   sz = ty==Ity_I1 ? 0 : sizeofIRType(ty);

   cond = mkPCastTo( kce, Ity_I1, vatom );
   /* cond will be 0 if all defined, and 1 if any not defined. */

   fn    = NULL;
   nm    = NULL;
   args  = NULL;
   nargs = -1;

   switch (sz) {
      case 0:
         fn    = &KC_(helperc_value_check0_fail_no_o);
         nm    = "KC_(helperc_value_check0_fail_no_o)";
         args  = mkIRExprVec_0();
         nargs = 0;
         break;
      case 1:
         fn    = &KC_(helperc_value_check1_fail_no_o);
         nm    = "KC_(helperc_value_check1_fail_no_o)";
         args  = mkIRExprVec_0();
         nargs = 0;
         break;
      case 4:
         fn    = &KC_(helperc_value_check4_fail_no_o);
         nm    = "KC_(helperc_value_check4_fail_no_o)";
         args  = mkIRExprVec_0();
         nargs = 0;
         break;
      case 8:
         fn    = &KC_(helperc_value_check8_fail_no_o);
         nm    = "KC_(helperc_value_check8_fail_no_o)";
         args  = mkIRExprVec_0();
         nargs = 0;
         break;
      case 2:
      case 16:
         fn    = &KC_(helperc_value_checkN_fail_no_o);
         nm    = "KC_(helperc_value_checkN_fail_no_o)";
         args  = mkIRExprVec_1( mkIRExpr_HWord( sz ) );
         nargs = 1;
         break;
      default:
         VG_(tool_panic)("unexpected szB");
   }

   tl_assert(fn);
   tl_assert(nm);
   tl_assert(args);
   tl_assert(nargs >= 0 && nargs <= 2);

   di = unsafeIRDirty_0_N( nargs/*regparms*/, nm, 
                           VG_(fnptr_to_fnentry)( fn ), args );
   di->guard = cond; // and cond is PCast-to-1(atom#)

   /* If the complaint is to be issued under a guard condition, AND
      that into the guard condition for the helper call. */
   if (guard) {
      IRAtom *g1 = assignNew('V', kce, Ity_I32, unop(Iop_1Uto32, di->guard));
      IRAtom *g2 = assignNew('V', kce, Ity_I32, unop(Iop_1Uto32, guard));
      IRAtom *e  = assignNew('V', kce, Ity_I32, binop(Iop_And32, g1, g2));
      di->guard  = assignNew('V', kce, Ity_I1,  unop(Iop_32to1, e));
   }

   setHelperAnns( kce, di );
   stmt( 'V', kce, IRStmt_Dirty(di));

   /* If |atom| is shadowed by an IRTemp, set the shadow tmp to be
      defined -- but only in the case where the guard evaluates to
      True at run-time.  Do the update by setting the orig->shadow
      mapping for tmp to reflect the fact that this shadow is getting
      a new value. */
   tl_assert(isIRAtom(vatom));
   /* sameKindedAtoms ... */
   if (vatom->tag == Iex_RdTmp) {
      tl_assert(atom->tag == Iex_RdTmp);
      if (guard == NULL) {
         // guard is 'always True', hence update unconditionally
         newShadowTmpV(kce, atom->Iex.RdTmp.tmp);
         assign('V', kce, findShadowTmpV(kce, atom->Iex.RdTmp.tmp), 
                          definedOfType(ty));
      } else {
         // update the temp only conditionally.  Do this by copying
         // its old value when the guard is False.
         // The old value ..
         IRTemp old_tmpV = findShadowTmpV(kce, atom->Iex.RdTmp.tmp);
         newShadowTmpV(kce, atom->Iex.RdTmp.tmp);
         IRAtom* new_tmpV
            = assignNew('V', kce, shadowTypeV(ty),
                        IRExpr_ITE(guard, definedOfType(ty),
                                          mkexpr(old_tmpV)));
         assign('V', kce, findShadowTmpV(kce, atom->Iex.RdTmp.tmp), new_tmpV);
      }
   }
}

/*------------------------------------------------------------*/
/*--- Shadowing PUTs/GETs, and indexed variants thereof    ---*/
/*------------------------------------------------------------*/

static Bool isAlwaysDefd ( KCEnv* kce, Int offset, Int size )
{
   Int minoffD, maxoffD, i;
   Int minoff = offset;
   Int maxoff = minoff + size - 1;
   tl_assert((minoff & ~0xFFFF) == 0);
   tl_assert((maxoff & ~0xFFFF) == 0);

   for (i = 0; i < kce->layout->n_alwaysDefd; i++) {
      minoffD = kce->layout->alwaysDefd[i].offset;
      maxoffD = minoffD + kce->layout->alwaysDefd[i].size - 1;
      tl_assert((minoffD & ~0xFFFF) == 0);
      tl_assert((maxoffD & ~0xFFFF) == 0);

      if (maxoff < minoffD || maxoffD < minoff)
         continue; /* no overlap */
      if (minoff >= minoffD && maxoff <= maxoffD)
         return True; /* completely contained in an always-defd section */

      VG_(tool_panic)("memcheck:isAlwaysDefd:partial overlap");
   }
   return False; /* could not find any containing section */
}

static
void do_shadow_PUT ( KCEnv* kce,  Int offset, 
                     IRAtom* atom, IRAtom* vatom, IRExpr *guard )
{
   IRType ty;

   if (atom) {
      tl_assert(!vatom);
      tl_assert(isOriginalAtom(kce, atom));
      vatom = expr2vbits( kce, atom );
   } else {
      tl_assert(vatom);
      tl_assert(isShadowAtom(kce, vatom));
   }

   ty = typeOfIRExpr(kce->sb->tyenv, vatom);
   tl_assert(ty != Ity_I1);
   if (isAlwaysDefd(kce, offset, sizeofIRType(ty))) {
      /* later: no ... */
      /* emit code to emit a complaint if any of the vbits are 1. */
      /* complainIfUndefined(kce, atom); */
   } else {
      /* Do a plain shadow Put. */
      if (guard) {
         /* If the guard expression evaluates to false we simply Put the value
            that is already stored in the guest state slot */
         IRAtom *cond, *iffalse;

         cond    = assignNew('V', kce, Ity_I1, guard);
         iffalse = assignNew('V', kce, ty,
                             IRExpr_Get(offset + kce->layout->total_sizeB, ty));
         vatom   = assignNew('V', kce, ty, IRExpr_ITE(cond, vatom, iffalse));
      }
      stmt( 'V', kce, IRStmt_Put( offset + kce->layout->total_sizeB, vatom ));
   }
}

static
void do_shadow_PUTI ( KCEnv* kce, IRPutI *puti)
{
   IRAtom* vatom;
   IRType  ty, tyS;
   Int     arrSize;;
   IRRegArray* descr = puti->descr;
   IRAtom*     ix    = puti->ix;
   Int         bias  = puti->bias;
   IRAtom*     atom  = puti->data;

   tl_assert(isOriginalAtom(kce,atom));
   vatom = expr2vbits( kce, atom );
   tl_assert(sameKindedAtoms(atom, vatom));
   ty   = descr->elemTy;
   tyS  = shadowTypeV(ty);
   arrSize = descr->nElems * sizeofIRType(ty);
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom(kce,ix));
   complainIfUndefined(kce, ix, NULL);
   if (isAlwaysDefd(kce, descr->base, arrSize)) {
      /* later: no ... */
      /* emit code to emit a complaint if any of the vbits are 1. */
      /* complainIfUndefined(kce, atom); */
   } else {
      /* Do a cloned version of the Put that refers to the shadow
         area. */
      IRRegArray* new_descr 
         = mkIRRegArray( descr->base + kce->layout->total_sizeB, 
                         tyS, descr->nElems);
      stmt( 'V', kce, IRStmt_PutI( mkIRPutI(new_descr, ix, bias, vatom) ));
   }
}

static 
IRExpr* shadow_GET ( KCEnv* kce, Int offset, IRType ty )
{
   IRType tyS = shadowTypeV(ty);
   tl_assert(ty != Ity_I1);
   tl_assert(ty != Ity_I128);
   if (isAlwaysDefd(kce, offset, sizeofIRType(ty))) {
      /* Always defined, return all zeroes of the relevant type */
      return definedOfType(tyS);
   } else {
      /* return a cloned version of the Get that refers to the shadow
         area. */
      /* FIXME: this isn't an atom! */
      return IRExpr_Get( offset + kce->layout->total_sizeB, tyS );
   }
}

/* Return an expression which contains the V bits corresponding to the
   given GETI (passed in in pieces). 
*/
static
IRExpr* shadow_GETI ( KCEnv* kce, 
                      IRRegArray* descr, IRAtom* ix, Int bias )
{
   IRType ty   = descr->elemTy;
   IRType tyS  = shadowTypeV(ty);
   Int arrSize = descr->nElems * sizeofIRType(ty);
   tl_assert(ty != Ity_I1);
   tl_assert(isOriginalAtom(kce,ix));
   complainIfUndefined(kce, ix, NULL);
   if (isAlwaysDefd(kce, descr->base, arrSize)) {
      /* Always defined, return all zeroes of the relevant type */
      return definedOfType(tyS);
   } else {
      /* return a cloned version of the Get that refers to the shadow
         area. */
      IRRegArray* new_descr 
         = mkIRRegArray( descr->base + kce->layout->total_sizeB, 
                         tyS, descr->nElems);
      return IRExpr_GetI( new_descr, ix, bias );
   }
}


/*------------------------------------------------------------*/
/*--- Generating approximations for unknown operations,    ---*/
/*--- using lazy-propagate semantics                       ---*/
/*------------------------------------------------------------*/

static
IRAtom* mkLazy2 ( KCEnv* kce, IRType finalVty, IRAtom* va1, IRAtom* va2 )
{
   tl_assert(0); // unimplemented
}


/* 3-arg version of the above. */
static
IRAtom* mkLazy3 ( KCEnv* kce, IRType finalVty, 
                  IRAtom* va1, IRAtom* va2, IRAtom* va3 )
{
   tl_assert(0); // unimplemented
}


/* 4-arg version of the above. */
static
IRAtom* mkLazy4 ( KCEnv* kce, IRType finalVty, 
                  IRAtom* va1, IRAtom* va2, IRAtom* va3, IRAtom* va4 )
{
   IRAtom* at;
   IRType t1 = typeOfIRExpr(kce->sb->tyenv, va1);
   IRType t2 = typeOfIRExpr(kce->sb->tyenv, va2);
   IRType t3 = typeOfIRExpr(kce->sb->tyenv, va3);
   IRType t4 = typeOfIRExpr(kce->sb->tyenv, va4);
   tl_assert(isShadowAtom(kce,va1));
   tl_assert(isShadowAtom(kce,va2));
   tl_assert(isShadowAtom(kce,va3));
   tl_assert(isShadowAtom(kce,va4));

   
   if (1) {
      VG_(printf)("mkLazy4: ");
      ppIRType(t1);
      VG_(printf)(" x ");
      ppIRType(t2);
      VG_(printf)(" x ");
      ppIRType(t3);
      VG_(printf)(" x ");
      ppIRType(t4);
      VG_(printf)(" -> ");
      ppIRType(finalVty);
      VG_(printf)("\n");
   }

   tl_assert(0);
}


/* Do the lazy propagation game from a null-terminated vector of
   atoms.  This is presumably the arguments to a helper call, so the
   IRCallee info is also supplied in order that we can know which
   arguments should be ignored (via the .mcx_mask field). 
*/
static
IRAtom* mkLazyN ( KCEnv* kce, 
                  IRAtom** exprvec, IRType finalVtype, IRCallee* cee )
{
   // pnkfelix thinks the mc_translate version of this effectively
   // 1. figures out what the computed value type is (by taking the min
   //    definedness-length of all elements of exprvec), and then
   // 2. computes the OR of all of exprvec for that computed value type.
   //
   // (pnkfelix thinks that the reason for step 1 is to allow for a
   // micro-optimized aka speedier version of step 1.)
   //
   // In any case, for the purposes of krabcake, we can just go with
   // treating it as all defined.
   return definedOfType(finalVtype);
}

/*------------------------------------------------------------*/
/*--- Generating expensive sequences for exact carry-chain ---*/
/*--- propagation in add/sub and related operations.       ---*/
/*------------------------------------------------------------*/

static
IRAtom* expensiveAddSub ( KCEnv*  kce,
                          Bool    add,
                          IRType  ty,
                          IRAtom* qaa, IRAtom* qbb, 
                          IRAtom* aa,  IRAtom* bb )
{
   IRAtom *a_min, *b_min, *a_max, *b_max;
   IROp   opAND, opOR, opXOR, opNOT, opADD, opSUB;

   tl_assert(isShadowAtom(kce,qaa));
   tl_assert(isShadowAtom(kce,qbb));
   tl_assert(isOriginalAtom(kce,aa));
   tl_assert(isOriginalAtom(kce,bb));
   tl_assert(sameKindedAtoms(qaa,aa));
   tl_assert(sameKindedAtoms(qbb,bb));

   return definedOfType(ty);
}


/*------------------------------------------------------------*/
/*--- Scalar shifts.                                       ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Helpers for dealing with vector primops.             ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Generate shadow values from all kinds of IRExprs.    ---*/
/*------------------------------------------------------------*/

static 
IRAtom* expr2vbits_Qop ( KCEnv* kce,
                         IROp op,
                         IRAtom* atom1, IRAtom* atom2, 
                         IRAtom* atom3, IRAtom* atom4 )
{
   IRAtom* vatom1 = expr2vbits( kce, atom1 );
   IRAtom* vatom2 = expr2vbits( kce, atom2 );
   IRAtom* vatom3 = expr2vbits( kce, atom3 );
   IRAtom* vatom4 = expr2vbits( kce, atom4 );

   tl_assert(isOriginalAtom(kce,atom1));
   tl_assert(isOriginalAtom(kce,atom2));
   tl_assert(isOriginalAtom(kce,atom3));
   tl_assert(isOriginalAtom(kce,atom4));
   tl_assert(isShadowAtom(kce,vatom1));
   tl_assert(isShadowAtom(kce,vatom2));
   tl_assert(isShadowAtom(kce,vatom3));
   tl_assert(isShadowAtom(kce,vatom4));

   switch (op) {
      case Iop_MAddF64:
      case Iop_MAddF64r32:
      case Iop_MSubF64:
      case Iop_MSubF64r32:
         return definedOfType(Ity_I64);

      case Iop_MAddF32:
      case Iop_MSubF32:
         return definedOfType(Ity_I32);

      case Iop_MAddF128:
      case Iop_MSubF128:
      case Iop_NegMAddF128:
      case Iop_NegMSubF128:
         return definedOfType(Ity_I128);

      /* V256-bit data-steering */
      case Iop_64x4toV256:
         return definedOfType(Ity_V256);

      /* I32/I64 x I8 x I8 x I8 -> I32/I64 */
      case Iop_Rotx32:
         return definedOfType(Ity_I32);
      case Iop_Rotx64:
         return definedOfType(Ity_I64);
      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Qop");
   }
}

static 
IRAtom* expr2vbits_Triop ( KCEnv* kce,
                           IROp op,
                           IRAtom* atom1, IRAtom* atom2, IRAtom* atom3 )
{
   IRAtom* vatom1 = expr2vbits( kce, atom1 );
   IRAtom* vatom2 = expr2vbits( kce, atom2 );
   IRAtom* vatom3 = expr2vbits( kce, atom3 );

   tl_assert(isOriginalAtom(kce,atom1));
   tl_assert(isOriginalAtom(kce,atom2));
   tl_assert(isOriginalAtom(kce,atom3));
   tl_assert(isShadowAtom(kce,vatom1));
   tl_assert(isShadowAtom(kce,vatom2));
   tl_assert(isShadowAtom(kce,vatom3));
   tl_assert(sameKindedAtoms(atom1,vatom1));
   tl_assert(sameKindedAtoms(atom2,vatom2));
   tl_assert(sameKindedAtoms(atom3,vatom3));

   switch (op) {
      case Iop_AddF128:
      case Iop_SubF128:
      case Iop_MulF128:
      case Iop_DivF128:
      case Iop_AddD128:
      case Iop_SubD128:
      case Iop_MulD128:
      case Iop_DivD128:
      case Iop_QuantizeD128:
         /* I32(rm) x F128/D128 x F128/D128 -> F128/D128 */
         return definedOfType(Ity_I128);
      case Iop_AddF64:
      case Iop_AddD64:
      case Iop_AddF64r32:
      case Iop_SubF64:
      case Iop_SubD64:
      case Iop_SubF64r32:
      case Iop_MulF64:
      case Iop_MulD64:
      case Iop_MulF64r32:
      case Iop_DivF64:
      case Iop_DivD64:
      case Iop_DivF64r32:
      case Iop_ScaleF64:
      case Iop_Yl2xF64:
      case Iop_Yl2xp1F64:
      case Iop_AtanF64:
      case Iop_PRemF64:
      case Iop_PRem1F64:
      case Iop_QuantizeD64:
         /* I32(rm) x F64/D64 x F64/D64 -> F64/D64 */
         return definedOfType(Ity_I64);
      case Iop_PRemC3210F64:
      case Iop_PRem1C3210F64:
         /* I32(rm) x F64 x F64 -> I32 */
         return definedOfType(Ity_I32);
      case Iop_AddF32:
      case Iop_SubF32:
      case Iop_MulF32:
      case Iop_DivF32:
         /* I32(rm) x F32 x F32 -> I32 */
         return definedOfType(Ity_I32);
      case Iop_AddF16:
      case Iop_SubF16:
         /* I32(rm) x F16 x F16 -> I16 */
         return definedOfType(Ity_I16);
      case Iop_SignificanceRoundD64:
         /* IRRoundingMode(I32) x I8 x D64 -> D64 */
         return definedOfType(Ity_I64);
      case Iop_SignificanceRoundD128:
         /* IRRoundingMode(I32) x I8 x D128 -> D128 */
         return definedOfType(Ity_I128);
      case Iop_SliceV128:
         /* (V128, V128, I8) -> V128 */
         complainIfUndefined(kce, atom3, NULL);
         return definedOfType(Ity_I128);
      case Iop_SetElem8x8:
      case Iop_SetElem16x4:
      case Iop_SetElem32x2:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);
      case Iop_SetElem8x16:
      case Iop_SetElem16x8:
      case Iop_SetElem32x4:
      case Iop_SetElem64x2:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I128);
         /* Int 128-bit Integer three arg  */
      case Iop_2xMultU64Add128CarryOut:
      case Iop_Perm8x16x2:
         /* (V128, V128, V128) -> V128 */
         complainIfUndefined(kce, atom3, NULL);
         return definedOfType(Ity_I128);
      /* Vector FP with rounding mode as the first arg */
      case Iop_Add64Fx2:
      case Iop_Sub64Fx2:
      case Iop_Mul64Fx2:
      case Iop_Div64Fx2:
      case Iop_Scale2_64Fx2:
         return definedOfType(Ity_V128);
      case Iop_Add32Fx4:
      case Iop_Sub32Fx4:
      case Iop_Mul32Fx4:
      case Iop_Div32Fx4:
      case Iop_Scale2_32Fx4:
         return definedOfType(Ity_V128);
      case Iop_Add64Fx4:
      case Iop_Sub64Fx4:
      case Iop_Mul64Fx4:
      case Iop_Div64Fx4:
         return definedOfType(Ity_V256);
      case Iop_Add16Fx8:
      case Iop_Sub16Fx8:
         return definedOfType(Ity_V128);
      case Iop_Add32Fx8:
      case Iop_Sub32Fx8:
      case Iop_Mul32Fx8:
      case Iop_Div32Fx8:
         return definedOfType(Ity_V256);
      case Iop_F32x4_2toQ16x8:
         return definedOfType(Ity_V128);
      case Iop_F64x2_2toQ32x4:
         return definedOfType(Ity_V128);
      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Triop");
   }
}

static 
IRAtom* expr2vbits_Binop ( KCEnv* kce,
                           IROp op,
                           IRAtom* atom1, IRAtom* atom2)
{
   IRType  and_or_ty = Ity_INVALID;
   IRAtom* (*uifu)    (KCEnv*, IRAtom*, IRAtom*) = NULL;
   IRAtom* (*difd)    (KCEnv*, IRAtom*, IRAtom*) = NULL;
   IRAtom* (*improve) (KCEnv*, IRAtom*, IRAtom*) = NULL;

   IRAtom* vatom1 = expr2vbits( kce, atom1 );
   IRAtom* vatom2 = expr2vbits( kce, atom2 );

   tl_assert(isOriginalAtom(kce,atom1));
   tl_assert(isOriginalAtom(kce,atom2));
   tl_assert(isShadowAtom(kce,vatom1));
   tl_assert(isShadowAtom(kce,vatom2));
   tl_assert(sameKindedAtoms(atom1,vatom1));
   tl_assert(sameKindedAtoms(atom2,vatom2));

   switch (op) {

      /* 32-bit SIMD */

      case Iop_Add16x2:
      case Iop_HAdd16Ux2:
      case Iop_HAdd16Sx2:
      case Iop_Sub16x2:
      case Iop_HSub16Ux2:
      case Iop_HSub16Sx2:
      case Iop_QAdd16Sx2:
      case Iop_QSub16Sx2:
      case Iop_QSub16Ux2:
      case Iop_QAdd16Ux2:
         return definedOfType(Ity_I32);

      case Iop_Add8x4:
      case Iop_HAdd8Ux4:
      case Iop_HAdd8Sx4:
      case Iop_Sub8x4:
      case Iop_HSub8Ux4:
      case Iop_HSub8Sx4:
      case Iop_QSub8Ux4:
      case Iop_QAdd8Ux4:
      case Iop_QSub8Sx4:
      case Iop_QAdd8Sx4:
         return definedOfType(Ity_I32);

      /* 64-bit SIMD */

      case Iop_ShrN8x8:
      case Iop_ShrN16x4:
      case Iop_ShrN32x2:
      case Iop_SarN8x8:
      case Iop_SarN16x4:
      case Iop_SarN32x2:
      case Iop_ShlN16x4:
      case Iop_ShlN32x2:
      case Iop_ShlN8x8:
         /* Same scheme as with all other shifts. */
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_QNarrowBin32Sto16Sx4:
      case Iop_QNarrowBin16Sto8Sx8:
      case Iop_QNarrowBin16Sto8Ux8:
         return definedOfType(Ity_I64);

      case Iop_Min8Ux8:
      case Iop_Min8Sx8:
      case Iop_Max8Ux8:
      case Iop_Max8Sx8:
      case Iop_Avg8Ux8:
      case Iop_QSub8Sx8:
      case Iop_QSub8Ux8:
      case Iop_Sub8x8:
      case Iop_CmpGT8Sx8:
      case Iop_CmpGT8Ux8:
      case Iop_CmpEQ8x8:
      case Iop_QAdd8Sx8:
      case Iop_QAdd8Ux8:
      case Iop_QSal8x8:
      case Iop_QShl8x8:
      case Iop_Add8x8:
      case Iop_Mul8x8:
      case Iop_PolynomialMul8x8:
         return definedOfType(Ity_I64);

      case Iop_Min16Sx4:
      case Iop_Min16Ux4:
      case Iop_Max16Sx4:
      case Iop_Max16Ux4:
      case Iop_Avg16Ux4:
      case Iop_QSub16Ux4:
      case Iop_QSub16Sx4:
      case Iop_Sub16x4:
      case Iop_Mul16x4:
      case Iop_MulHi16Sx4:
      case Iop_MulHi16Ux4:
      case Iop_CmpGT16Sx4:
      case Iop_CmpGT16Ux4:
      case Iop_CmpEQ16x4:
      case Iop_QAdd16Sx4:
      case Iop_QAdd16Ux4:
      case Iop_QSal16x4:
      case Iop_QShl16x4:
      case Iop_Add16x4:
      case Iop_QDMulHi16Sx4:
      case Iop_QRDMulHi16Sx4:
         return definedOfType(Ity_I64);

      case Iop_Sub32x2:
      case Iop_Mul32x2:
      case Iop_Max32Sx2:
      case Iop_Max32Ux2:
      case Iop_Min32Sx2:
      case Iop_Min32Ux2:
      case Iop_CmpGT32Sx2:
      case Iop_CmpGT32Ux2:
      case Iop_CmpEQ32x2:
      case Iop_Add32x2:
      case Iop_QAdd32Ux2:
      case Iop_QAdd32Sx2:
      case Iop_QSub32Ux2:
      case Iop_QSub32Sx2:
      case Iop_QSal32x2:
      case Iop_QShl32x2:
      case Iop_QDMulHi32Sx2:
      case Iop_QRDMulHi32Sx2:
         return definedOfType(Ity_I64);

      case Iop_QSub64Ux1:
      case Iop_QSub64Sx1:
      case Iop_QAdd64Ux1:
      case Iop_QAdd64Sx1:
      case Iop_QSal64x1:
      case Iop_QShl64x1:
      case Iop_Sal64x1:
         return definedOfType(Ity_I64);

      case Iop_QShlNsatSU8x8:
      case Iop_QShlNsatUU8x8:
      case Iop_QShlNsatSS8x8:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_QShlNsatSU16x4:
      case Iop_QShlNsatUU16x4:
      case Iop_QShlNsatSS16x4:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_QShlNsatSU32x2:
      case Iop_QShlNsatUU32x2:
      case Iop_QShlNsatSS32x2:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_QShlNsatSU64x1:
      case Iop_QShlNsatUU64x1:
      case Iop_QShlNsatSS64x1:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_PwMax32Sx2:
      case Iop_PwMax32Ux2:
      case Iop_PwMin32Sx2:
      case Iop_PwMin32Ux2:
      case Iop_PwMax32Fx2:
      case Iop_PwMin32Fx2:
         return definedOfType(Ity_I64);

      case Iop_PwMax16Sx4:
      case Iop_PwMax16Ux4:
      case Iop_PwMin16Sx4:
      case Iop_PwMin16Ux4:
         return definedOfType(Ity_I64);

      case Iop_PwMax8Sx8:
      case Iop_PwMax8Ux8:
      case Iop_PwMin8Sx8:
      case Iop_PwMin8Ux8:
         return definedOfType(Ity_I64);

      case Iop_PwAdd32x2:
      case Iop_PwAdd32Fx2:
         return definedOfType(Ity_I64);

      case Iop_PwAdd16x4:
         return definedOfType(Ity_I64);

      case Iop_PwAdd8x8:
         return definedOfType(Ity_I64);

      case Iop_Shl8x8:
      case Iop_Shr8x8:
      case Iop_Sar8x8:
      case Iop_Sal8x8:
         return definedOfType(Ity_I64);

      case Iop_Shl16x4:
      case Iop_Shr16x4:
      case Iop_Sar16x4:
      case Iop_Sal16x4:
         return definedOfType(Ity_I64);

      case Iop_Shl32x2:
      case Iop_Shr32x2:
      case Iop_Sar32x2:
      case Iop_Sal32x2:
         return definedOfType(Ity_I64);

      /* 64-bit data-steering */
      case Iop_InterleaveLO32x2:
      case Iop_InterleaveLO16x4:
      case Iop_InterleaveLO8x8:
      case Iop_InterleaveHI32x2:
      case Iop_InterleaveHI16x4:
      case Iop_InterleaveHI8x8:
      case Iop_CatOddLanes8x8:
      case Iop_CatEvenLanes8x8:
      case Iop_CatOddLanes16x4:
      case Iop_CatEvenLanes16x4:
      case Iop_InterleaveOddLanes8x8:
      case Iop_InterleaveEvenLanes8x8:
      case Iop_InterleaveOddLanes16x4:
      case Iop_InterleaveEvenLanes16x4:
         return definedOfType(Ity_I64);

      case Iop_GetElem8x8:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);
      case Iop_GetElem16x4:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);
      case Iop_GetElem32x2:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_Perm8x8:
      case Iop_PermOrZero8x8:
         return definedOfType(Ity_I64);

      /* V128-bit SIMD */

      case Iop_I32StoF32x4:
      case Iop_F32toI32Sx4:
      case Iop_Sqrt16Fx8:
         return definedOfType(Ity_V128);
      case Iop_Sqrt32Fx4:
         return definedOfType(Ity_V128);
      case Iop_Sqrt64Fx2:
         return definedOfType(Ity_V128);

      case Iop_ShrN8x16:
      case Iop_ShrN16x8:
      case Iop_ShrN32x4:
      case Iop_ShrN64x2:
      case Iop_SarN8x16:
      case Iop_SarN16x8:
      case Iop_SarN32x4:
      case Iop_SarN64x2:
      case Iop_ShlN8x16:
      case Iop_ShlN16x8:
      case Iop_ShlN32x4:
      case Iop_ShlN64x2:
         /* Same scheme as with all other shifts.  Note: 22 Oct 05:
            this is wrong now, scalar shifts are done properly lazily.
            Vector shifts should be fixed too. */
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      /* V x V shifts/rotates are done using the standard lazy scheme. */
      /* For the non-rounding variants of bi-di vector x vector
         shifts (the Iop_Sh.. ops, that is) we use the lazy scheme.
         But note that this is overly pessimistic, because in fact only
         the bottom 8 bits of each lane of the second argument are taken
         into account when shifting.  So really we ought to ignore
         undefinedness in bits 8 and above of each lane in the
         second argument. */
      case Iop_Shl8x16:
      case Iop_Shr8x16:
      case Iop_Sar8x16:
      case Iop_Sal8x16:
      case Iop_Rol8x16:
      case Iop_Sh8Sx16:
      case Iop_Sh8Ux16:
         return definedOfType(Ity_V128);

      case Iop_Shl16x8:
      case Iop_Shr16x8:
      case Iop_Sar16x8:
      case Iop_Sal16x8:
      case Iop_Rol16x8:
      case Iop_Sh16Sx8:
      case Iop_Sh16Ux8:
         return definedOfType(Ity_V128);

      case Iop_Shl32x4:
      case Iop_Shr32x4:
      case Iop_Sar32x4:
      case Iop_Sal32x4:
      case Iop_Rol32x4:
      case Iop_Sh32Sx4:
      case Iop_Sh32Ux4:
         return definedOfType(Ity_V128);

      case Iop_Shl64x2:
      case Iop_Shr64x2:
      case Iop_Sar64x2:
      case Iop_Sal64x2:
      case Iop_Rol64x2:
      case Iop_Sh64Sx2:
      case Iop_Sh64Ux2:
         return definedOfType(Ity_V128);

      /* For the rounding variants of bi-di vector x vector shifts, the
         rounding adjustment can cause undefinedness to propagate through
         the entire lane, in the worst case.  Too complex to handle 
         properly .. just UifU the arguments and then PCast them.
         Suboptimal but safe. */
      case Iop_Rsh8Sx16:
      case Iop_Rsh8Ux16:
         return definedOfType(Ity_V128);
      case Iop_Rsh16Sx8:
      case Iop_Rsh16Ux8:
         return definedOfType(Ity_V128);
      case Iop_Rsh32Sx4:
      case Iop_Rsh32Ux4:
         return definedOfType(Ity_V128);
      case Iop_Rsh64Sx2:
      case Iop_Rsh64Ux2:
         return definedOfType(Ity_V128);

      case Iop_F32ToFixed32Ux4_RZ:
      case Iop_F32ToFixed32Sx4_RZ:
      case Iop_Fixed32UToF32x4_RN:
      case Iop_Fixed32SToF32x4_RN:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      case Iop_F32ToFixed32Ux2_RZ:
      case Iop_F32ToFixed32Sx2_RZ:
      case Iop_Fixed32UToF32x2_RN:
      case Iop_Fixed32SToF32x2_RN:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_I64);

      case Iop_QSub8Ux16:
      case Iop_QSub8Sx16:
      case Iop_Sub8x16:
      case Iop_Min8Ux16:
      case Iop_Min8Sx16:
      case Iop_Max8Ux16:
      case Iop_Max8Sx16:
      case Iop_CmpGT8Sx16:
      case Iop_CmpGT8Ux16:
      case Iop_CmpEQ8x16:
      case Iop_Avg8Ux16:
      case Iop_Avg8Sx16:
      case Iop_QAdd8Ux16:
      case Iop_QAdd8Sx16:
      case Iop_QAddExtUSsatSS8x16:
      case Iop_QAddExtSUsatUU8x16:
      case Iop_QSal8x16:
      case Iop_QShl8x16:
      case Iop_Add8x16:
      case Iop_Mul8x16:
      case Iop_MulHi8Sx16:
      case Iop_MulHi8Ux16:
      case Iop_PolynomialMul8x16:
      case Iop_PolynomialMulAdd8x16:
         return definedOfType(Ity_V128);

      case Iop_QSub16Ux8:
      case Iop_QSub16Sx8:
      case Iop_Sub16x8:
      case Iop_Mul16x8:
      case Iop_MulHi16Sx8:
      case Iop_MulHi16Ux8:
      case Iop_Min16Sx8:
      case Iop_Min16Ux8:
      case Iop_Max16Sx8:
      case Iop_Max16Ux8:
      case Iop_CmpGT16Sx8:
      case Iop_CmpGT16Ux8:
      case Iop_CmpEQ16x8:
      case Iop_Avg16Ux8:
      case Iop_Avg16Sx8:
      case Iop_QAdd16Ux8:
      case Iop_QAdd16Sx8:
      case Iop_QAddExtUSsatSS16x8:
      case Iop_QAddExtSUsatUU16x8:
      case Iop_QSal16x8:
      case Iop_QShl16x8:
      case Iop_Add16x8:
      case Iop_QDMulHi16Sx8:
      case Iop_QRDMulHi16Sx8:
      case Iop_PolynomialMulAdd16x8:
      /* PwExtUSMulQAdd8x16 is a bit subtle.  The effect of it is that each
         16-bit chunk of the output is formed from corresponding 16-bit chunks
         of the input args, so we can treat it like an other binary 16x8
         operation.  That's despite it having '8x16' in its name. */
      case Iop_PwExtUSMulQAdd8x16:
         return definedOfType(Ity_V128);

      case Iop_Sub32x4:
      case Iop_CmpGT32Sx4:
      case Iop_CmpGT32Ux4:
      case Iop_CmpEQ32x4:
      case Iop_QAdd32Sx4:
      case Iop_QAdd32Ux4:
      case Iop_QSub32Sx4:
      case Iop_QSub32Ux4:
      case Iop_QAddExtUSsatSS32x4:
      case Iop_QAddExtSUsatUU32x4:
      case Iop_QSal32x4:
      case Iop_QShl32x4:
      case Iop_Avg32Ux4:
      case Iop_Avg32Sx4:
      case Iop_Add32x4:
      case Iop_Max32Ux4:
      case Iop_Max32Sx4:
      case Iop_Min32Ux4:
      case Iop_Min32Sx4:
      case Iop_Mul32x4:
      case Iop_MulHi32Sx4:
      case Iop_MulHi32Ux4:
      case Iop_QDMulHi32Sx4:
      case Iop_QRDMulHi32Sx4:
      case Iop_PolynomialMulAdd32x4:
         return definedOfType(Ity_V128);

      case Iop_Sub64x2:
      case Iop_Add64x2:
      case Iop_Avg64Ux2:
      case Iop_Avg64Sx2:
      case Iop_Max64Sx2:
      case Iop_Max64Ux2:
      case Iop_Min64Sx2:
      case Iop_Min64Ux2:
      case Iop_CmpEQ64x2:
      case Iop_CmpGT64Sx2:
      case Iop_CmpGT64Ux2:
      case Iop_QSal64x2:
      case Iop_QShl64x2:
      case Iop_QAdd64Ux2:
      case Iop_QAdd64Sx2:
      case Iop_QSub64Ux2:
      case Iop_QSub64Sx2:
      case Iop_QAddExtUSsatSS64x2:
      case Iop_QAddExtSUsatUU64x2:
      case Iop_PolynomialMulAdd64x2:
      case Iop_CipherV128:
      case Iop_CipherLV128:
      case Iop_NCipherV128:
      case Iop_NCipherLV128:
      case Iop_MulI128by10E:
      case Iop_MulI128by10ECarry:
         return definedOfType(Ity_V128);

      case Iop_Add128x1:
      case Iop_Sub128x1:
      case Iop_CmpNEZ128x1:
         return definedOfType(Ity_V128);

      case Iop_DivU128:
      case Iop_DivS128:
      case Iop_DivU128E:
      case Iop_DivS128E:
      case Iop_ModU128:
      case Iop_ModS128:
         /* I128 x I128 -> I128 */
         return definedOfType(Ity_V128);

      case Iop_QNarrowBin64Sto32Sx4:
      case Iop_QNarrowBin64Uto32Ux4:
      case Iop_QNarrowBin32Sto16Sx8:
      case Iop_QNarrowBin32Uto16Ux8:
      case Iop_QNarrowBin32Sto16Ux8:
      case Iop_QNarrowBin16Sto8Sx16:
      case Iop_QNarrowBin16Uto8Ux16:
      case Iop_QNarrowBin16Sto8Ux16:
         return definedOfType(Ity_V128);

      case Iop_Min64Fx2:
      case Iop_Max64Fx2:
      case Iop_CmpLT64Fx2:
      case Iop_CmpLE64Fx2:
      case Iop_CmpEQ64Fx2:
      case Iop_CmpUN64Fx2:
      case Iop_RecipStep64Fx2:
      case Iop_RSqrtStep64Fx2:
         return definedOfType(Ity_V128);

      case Iop_CmpLT16Fx8:
      case Iop_CmpLE16Fx8:
      case Iop_CmpEQ16Fx8:
         return definedOfType(Ity_V128);

      case Iop_Sub64F0x2:
      case Iop_Mul64F0x2:
      case Iop_Min64F0x2:
      case Iop_Max64F0x2:
      case Iop_Div64F0x2:
      case Iop_CmpLT64F0x2:
      case Iop_CmpLE64F0x2:
      case Iop_CmpEQ64F0x2:
      case Iop_CmpUN64F0x2:
      case Iop_Add64F0x2:
         return definedOfType(Ity_V128);

      case Iop_Min32Fx4:
      case Iop_Max32Fx4:
      case Iop_CmpLT32Fx4:
      case Iop_CmpLE32Fx4:
      case Iop_CmpEQ32Fx4:
      case Iop_CmpUN32Fx4:
      case Iop_CmpGT32Fx4:
      case Iop_CmpGE32Fx4:
      case Iop_RecipStep32Fx4:
      case Iop_RSqrtStep32Fx4:
         return definedOfType(Ity_V128);

      case Iop_Sub32Fx2:
      case Iop_Mul32Fx2:
      case Iop_Min32Fx2:
      case Iop_Max32Fx2:
      case Iop_CmpEQ32Fx2:
      case Iop_CmpGT32Fx2:
      case Iop_CmpGE32Fx2:
      case Iop_Add32Fx2:
      case Iop_RecipStep32Fx2:
      case Iop_RSqrtStep32Fx2:
         return definedOfType(Ity_I64);

      case Iop_Sub32F0x4:
      case Iop_Mul32F0x4:
      case Iop_Min32F0x4:
      case Iop_Max32F0x4:
      case Iop_Div32F0x4:
      case Iop_CmpLT32F0x4:
      case Iop_CmpLE32F0x4:
      case Iop_CmpEQ32F0x4:
      case Iop_CmpUN32F0x4:
      case Iop_Add32F0x4:
         return definedOfType(Ity_V128);

      case Iop_QShlNsatSU8x16:
      case Iop_QShlNsatUU8x16:
      case Iop_QShlNsatSS8x16:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      case Iop_QShlNsatSU16x8:
      case Iop_QShlNsatUU16x8:
      case Iop_QShlNsatSS16x8:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      case Iop_QShlNsatSU32x4:
      case Iop_QShlNsatUU32x4:
      case Iop_QShlNsatSS32x4:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      case Iop_QShlNsatSU64x2:
      case Iop_QShlNsatUU64x2:
      case Iop_QShlNsatSS64x2:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      /* Q-and-Qshift-by-imm-and-narrow of the form (V128, I8) -> V128.
         To make this simpler, do the following:
         * complain if the shift amount (the I8) is undefined
         * pcast each lane at the wide width
         * truncate each lane to half width
         * pcast the resulting 64-bit value to a single bit and use
           that as the least significant bit of the upper half of the
           result. */
      case Iop_QandQShrNnarrow64Uto32Ux2:
      case Iop_QandQSarNnarrow64Sto32Sx2:
      case Iop_QandQSarNnarrow64Sto32Ux2:
      case Iop_QandQRShrNnarrow64Uto32Ux2:
      case Iop_QandQRSarNnarrow64Sto32Sx2:
      case Iop_QandQRSarNnarrow64Sto32Ux2:
      case Iop_QandQShrNnarrow32Uto16Ux4:
      case Iop_QandQSarNnarrow32Sto16Sx4:
      case Iop_QandQSarNnarrow32Sto16Ux4:
      case Iop_QandQRShrNnarrow32Uto16Ux4:
      case Iop_QandQRSarNnarrow32Sto16Sx4:
      case Iop_QandQRSarNnarrow32Sto16Ux4:
      case Iop_QandQShrNnarrow16Uto8Ux8:
      case Iop_QandQSarNnarrow16Sto8Sx8:
      case Iop_QandQSarNnarrow16Sto8Ux8:
      case Iop_QandQRShrNnarrow16Uto8Ux8:
      case Iop_QandQRSarNnarrow16Sto8Sx8:
      case Iop_QandQRSarNnarrow16Sto8Ux8:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      case Iop_Mull32Sx2:
      case Iop_Mull32Ux2:
      case Iop_QDMull32Sx2:
         return definedOfType(Ity_V128);

      case Iop_Mull16Sx4:
      case Iop_Mull16Ux4:
      case Iop_QDMull16Sx4:
         return definedOfType(Ity_V128);

      case Iop_Mull8Sx8:
      case Iop_Mull8Ux8:
      case Iop_PolynomialMull8x8:
         return definedOfType(Ity_V128);

      case Iop_PwAdd32x4:
         return definedOfType(Ity_V128);

      case Iop_PwAdd16x8:
         return definedOfType(Ity_V128);

      case Iop_PwAdd8x16:
         return definedOfType(Ity_V128);

      /* V128-bit data-steering */
      case Iop_SetV128lo32:
      case Iop_SetV128lo64:
      case Iop_64HLtoV128:
      case Iop_InterleaveLO64x2:
      case Iop_InterleaveLO32x4:
      case Iop_InterleaveLO16x8:
      case Iop_InterleaveLO8x16:
      case Iop_InterleaveHI64x2:
      case Iop_InterleaveHI32x4:
      case Iop_InterleaveHI16x8:
      case Iop_InterleaveHI8x16:
      case Iop_CatOddLanes8x16:
      case Iop_CatOddLanes16x8:
      case Iop_CatOddLanes32x4:
      case Iop_CatEvenLanes8x16:
      case Iop_CatEvenLanes16x8:
      case Iop_CatEvenLanes32x4:
      case Iop_InterleaveOddLanes8x16:
      case Iop_InterleaveOddLanes16x8:
      case Iop_InterleaveOddLanes32x4:
      case Iop_InterleaveEvenLanes8x16:
      case Iop_InterleaveEvenLanes16x8:
      case Iop_InterleaveEvenLanes32x4:
      case Iop_PackOddLanes8x16:
      case Iop_PackOddLanes16x8:
      case Iop_PackOddLanes32x4:
      case Iop_PackEvenLanes8x16:
      case Iop_PackEvenLanes16x8:
      case Iop_PackEvenLanes32x4:
         return definedOfType(Ity_V128);

      case Iop_GetElem8x16:
         return definedOfType(Ity_I8);
      case Iop_GetElem16x8:
         return definedOfType(Ity_I16);
      case Iop_GetElem32x4:
         return definedOfType(Ity_I32);
      case Iop_GetElem64x2:
         return definedOfType(Ity_I64);

      case Iop_Perm8x16:
      case Iop_PermOrZero8x16:
         return definedOfType(Ity_V128);

      case Iop_Perm32x4:
         return definedOfType(Ity_V128);

      case Iop_MullEven16Ux8:
      case Iop_MullEven16Sx8:
         return definedOfType(Ity_V128);

      case Iop_MullEven8Ux16:
      case Iop_MullEven8Sx16:
         return definedOfType(Ity_V128);

      case Iop_MullEven32Ux4:
      case Iop_MullEven32Sx4:
         return definedOfType(Ity_V128);

      case Iop_NarrowBin32to16x8: 
      case Iop_NarrowBin16to8x16: 
      case Iop_NarrowBin64to32x4:
         return definedOfType(Ity_V128);

      case Iop_ShrV128:
      case Iop_SarV128:
      case Iop_ShlV128:
      case Iop_I128StoBCD128:
         return definedOfType(Ity_V128);

      case Iop_I128UtoF128:
      case Iop_I128StoF128:
         return definedOfType(Ity_I128);

      case Iop_BCDAdd:
      case Iop_BCDSub:
         return definedOfType(Ity_V128);

      /* SHA Iops */
      case Iop_SHA256:
      case Iop_SHA512:
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V128);

      /* I128-bit data-steering */
      case Iop_64HLto128:
         return definedOfType(Ity_I128);

      /* V256-bit SIMD */

      case Iop_Max64Fx4:
      case Iop_Min64Fx4:
         return definedOfType(Ity_V256);

      case Iop_Max32Fx8:
      case Iop_Min32Fx8:
         return definedOfType(Ity_V256);

      /* V256-bit data-steering */
      case Iop_V128HLtoV256:
         return definedOfType(Ity_V256);

      /* Scalar floating point */

      case Iop_F32toI64S:
      case Iop_F32toI64U:
         /* I32(rm) x F32 -> I64 */
         return definedOfType(Ity_I64);

      case Iop_I64StoF32:
         /* I32(rm) x I64 -> F32 */
         return definedOfType(Ity_I32);

      case Iop_RoundF64toInt:
      case Iop_RoundF64toF32:
      case Iop_F64toI64S:
      case Iop_F64toI64U:
      case Iop_I64StoF64:
      case Iop_I64UtoF64:
      case Iop_SinF64:
      case Iop_CosF64:
      case Iop_TanF64:
      case Iop_2xm1F64:
      case Iop_SqrtF64:
      case Iop_RecpExpF64:
         /* I32(rm) x I64/F64 -> I64/F64 */
         return definedOfType(Ity_I64);

      case Iop_ShlD64:
      case Iop_ShrD64:
      case Iop_RoundD64toInt:
         /* I32(rm) x D64 -> D64 */
         return definedOfType(Ity_I64);

      case Iop_ShlD128:
      case Iop_ShrD128:
      case Iop_RoundD128toInt:
         /* I32(rm) x D128 -> D128 */
         return definedOfType(Ity_I128);

      case Iop_RoundF128toInt:
         /* I32(rm) x F128 -> F128 */
         return definedOfType(Ity_I128);

      case Iop_D64toI64S:
      case Iop_D64toI64U:
      case Iop_I64StoD64:
      case Iop_I64UtoD64:
         /* I32(rm) x I64/D64 -> D64/I64 */
         return definedOfType(Ity_I64);

      case Iop_F32toD32:
      case Iop_F64toD32:
      case Iop_F128toD32:
      case Iop_D32toF32:
      case Iop_D64toF32:
      case Iop_D128toF32:
         /* I32(rm) x F32/F64/F128/D32/D64/D128 -> D32/F32 */
         return definedOfType(Ity_I32);

      case Iop_F32toD64:
      case Iop_F64toD64:
      case Iop_F128toD64:
      case Iop_D32toF64:
      case Iop_D64toF64:
      case Iop_D128toF64:
         /* I32(rm) x F32/F64/F128/D32/D64/D128 -> D64/F64 */
         return definedOfType(Ity_I64);

      case Iop_F32toD128:
      case Iop_F64toD128:
      case Iop_F128toD128:
      case Iop_D32toF128:
      case Iop_D64toF128:
      case Iop_D128toF128:
      case Iop_I128StoD128:
         /* I32(rm) x F32/F64/F128/D32/D64/D128 -> D128/F128 */
         return definedOfType(Ity_I128);

      case Iop_SqrtF16:
         /* I32(rm) x F16 -> F16 */
         return definedOfType(Ity_I16);

      case Iop_RoundF32toInt:
      case Iop_SqrtF32:
      case Iop_RecpExpF32:
         /* I32(rm) x I32/F32 -> I32/F32 */
         return definedOfType(Ity_I32);

      case Iop_SqrtF128:
         /* I32(rm) x F128 -> F128 */
         return definedOfType(Ity_I128);

      case Iop_I32StoF32:
      case Iop_I32UtoF32:
      case Iop_F32toI32S:
      case Iop_F32toI32U:
         /* First arg is I32 (rounding mode), second is F32/I32 (data). */
         return definedOfType(Ity_I32);

      case Iop_F64toF16:
      case Iop_F32toF16:
         /* First arg is I32 (rounding mode), second is F64/F32 (data). */
         return definedOfType(Ity_I16);

      case Iop_F128toI32S: /* IRRoundingMode(I32) x F128 -> signed I32  */
      case Iop_F128toI32U: /* IRRoundingMode(I32) x F128 -> unsigned I32  */
      case Iop_F128toF32:  /* IRRoundingMode(I32) x F128 -> F32         */
      case Iop_D128toI32S: /* IRRoundingMode(I32) x D128 -> signed I32  */
      case Iop_D128toI32U: /* IRRoundingMode(I32) x D128 -> unsigned I32  */
         return definedOfType(Ity_I32);

      case Iop_F128toI128S:   /* IRRoundingMode(I32) x F128 -> signed I128 */
      case Iop_RndF128:       /* IRRoundingMode(I32) x F128 -> F128 */
      case Iop_D128toI128S:   /* IRRoundingMode(I32) x D128 -> signed I128 */
         return definedOfType(Ity_I128);

      case Iop_F128toI64S: /* IRRoundingMode(I32) x F128 -> signed I64  */
      case Iop_F128toI64U: /* IRRoundingMode(I32) x F128 -> unsigned I64  */
      case Iop_F128toF64:  /* IRRoundingMode(I32) x F128 -> F64         */
      case Iop_D128toD64:  /* IRRoundingMode(I64) x D128 -> D64 */
      case Iop_D128toI64S: /* IRRoundingMode(I64) x D128 -> signed I64  */
      case Iop_D128toI64U: /* IRRoundingMode(I32) x D128 -> unsigned I64  */
         return definedOfType(Ity_I64);

      case Iop_F64HLtoF128:
      case Iop_D64HLtoD128:
         return definedOfType(Ity_I128);

      case Iop_F64toI32U:
      case Iop_F64toI32S:
      case Iop_F64toF32:
      case Iop_I64UtoF32:
      case Iop_D64toI32U:
      case Iop_D64toI32S:
         /* First arg is I32 (rounding mode), second is F64/D64 (data). */
         return definedOfType(Ity_I32);

      case Iop_D64toD32:
         /* First arg is I32 (rounding mode), second is D64 (data). */
         return definedOfType(Ity_I32);

      case Iop_F64toI16S:
         /* First arg is I32 (rounding mode), second is F64 (data). */
         return definedOfType(Ity_I16);

      case Iop_InsertExpD64:
         /*  I64 x I64 -> D64 */
         return definedOfType(Ity_I64);

      case Iop_InsertExpD128:
         /*  I64 x I128 -> D128 */
         return definedOfType(Ity_I128);

      case Iop_CmpF16:
      case Iop_CmpF32:
      case Iop_CmpF64:
      case Iop_CmpF128:
      case Iop_CmpD64:
      case Iop_CmpD128:
      case Iop_CmpExpD64:
      case Iop_CmpExpD128:
         return definedOfType(Ity_I32);

      case Iop_MaxNumF32:
      case Iop_MinNumF32:
         /* F32 x F32 -> F32 */
         return definedOfType(Ity_I32);

      case Iop_MaxNumF64:
      case Iop_MinNumF64:
         /* F64 x F64 -> F64 */
         return definedOfType(Ity_I64);

      /* non-FP after here */

      case Iop_DivModU64to32:
      case Iop_DivModS64to32:
         return definedOfType(Ity_I64);

      case Iop_DivModU128to64:
      case Iop_DivModS128to64:
         return definedOfType(Ity_I128);

      case Iop_8HLto16:
         return definedOfType(Ity_I16);
      case Iop_16HLto32:
         return definedOfType(Ity_I32);
      case Iop_32HLto64:
         return definedOfType(Ity_I64);

      case Iop_DivModU64to64:
      case Iop_DivModS64to64:
         return definedOfType(Ity_I128);

      case Iop_MullS64:
      case Iop_MullU64:
         return definedOfType(Ity_I128);

      case Iop_DivModU32to32:
      case Iop_DivModS32to32:
         return definedOfType(Ity_I64);

      case Iop_MullS32:
      case Iop_MullU32:
         return definedOfType(Ity_I64);

      case Iop_MullS16:
      case Iop_MullU16:
         return definedOfType(Ity_I16);

      case Iop_MullS8:
      case Iop_MullU8:
         return definedOfType(Ity_I8);

      case Iop_Sad8Ux4: /* maybe we could do better?  ftm, do mkLazy2. */
      case Iop_DivS32:
      case Iop_DivU32:
      case Iop_DivU32E:
      case Iop_DivS32E:
      case Iop_QAdd32S: /* could probably do better */
      case Iop_QSub32S: /* could probably do better */
         return definedOfType(Ity_I32);

      case Iop_DivS64:
      case Iop_DivU64:
      case Iop_DivS64E:
      case Iop_DivU64E:
         return definedOfType(Ity_I64);

      case Iop_Add32:
         return expensiveAddSub(kce,True,Ity_I32,
                                vatom1,vatom2, atom1,atom2);
      case Iop_Sub32:
         return expensiveAddSub(kce,False,Ity_I32,
                                vatom1,vatom2, atom1,atom2);

      case Iop_Mul32:
         return definedOfType(Ity_I32);

      case Iop_CmpORD32S:
      case Iop_CmpORD32U:
         return definedOfType(Ity_I32);
      case Iop_CmpORD64S:
      case Iop_CmpORD64U:
         return definedOfType(Ity_I64);

      case Iop_Add64:
         return expensiveAddSub(kce,True,Ity_I64,
                                vatom1,vatom2, atom1,atom2);
      case Iop_Sub64:
         return expensiveAddSub(kce,False,Ity_I64,
                                vatom1,vatom2, atom1,atom2);
      case Iop_Mul64:
         return definedOfType(Ity_I64);

      case Iop_Mul16:
      case Iop_Add16:
      case Iop_Sub16:
         return definedOfType(Ity_I16);

      case Iop_Mul8:
      case Iop_Sub8:
      case Iop_Add8:
         return definedOfType(Ity_I8);

      ////---- CmpXX64
      case Iop_CmpEQ64: case Iop_CmpNE64:
      case Iop_ExpCmpNE64:
      case Iop_CmpLE64S: case Iop_CmpLE64U: 
      case Iop_CmpLT64U: case Iop_CmpLT64S:
         return definedOfType(Ity_I1);

      ////---- CmpXX32
      case Iop_CmpEQ32: case Iop_CmpNE32:
      case Iop_ExpCmpNE32:
      case Iop_CmpLE32S: case Iop_CmpLE32U: 
      case Iop_CmpLT32U: case Iop_CmpLT32S:
         return definedOfType(Ity_I1);

      ////---- CmpXX16
      case Iop_CmpEQ16: case Iop_CmpNE16:
      case Iop_ExpCmpNE16:
         return definedOfType(Ity_I1);

      ////---- CmpXX8
      case Iop_CmpEQ8: case Iop_CmpNE8:
         return definedOfType(Ity_I1);

      ////---- end CmpXX{64,32,16,8}

      case Iop_CasCmpEQ8:  case Iop_CasCmpNE8:
      case Iop_CasCmpEQ16: case Iop_CasCmpNE16:
      case Iop_CasCmpEQ32: case Iop_CasCmpNE32:
      case Iop_CasCmpEQ64: case Iop_CasCmpNE64:
         return definedOfType(Ity_I1);

      case Iop_Shl64: case Iop_Shr64: case Iop_Sar64:
         return definedOfType(Ity_I64);

      case Iop_Shl32: case Iop_Shr32: case Iop_Sar32:
         return definedOfType(Ity_I32);

      case Iop_Shl16: case Iop_Shr16: case Iop_Sar16:
         return definedOfType(Ity_I16);

      case Iop_Shl8: case Iop_Shr8: case Iop_Sar8:
         return definedOfType(Ity_I8);

      case Iop_AndV256:
         return definedOfType(Ity_V256);
      case Iop_AndV128:
         return definedOfType(Ity_V128);
      case Iop_And64:
         return definedOfType(Ity_I64);
      case Iop_And32:
         return definedOfType(Ity_I32);
      case Iop_And16:
         return definedOfType(Ity_I16);
      case Iop_And8:
         return definedOfType(Ity_I8);
      case Iop_And1:
         return definedOfType(Ity_I1);

      case Iop_OrV256:
         return definedOfType(Ity_V256);
      case Iop_OrV128:
         return definedOfType(Ity_V128);
      case Iop_Or64:
         return definedOfType(Ity_I64);
      case Iop_Or32:
         return definedOfType(Ity_I32);
      case Iop_Or16:
         return definedOfType(Ity_I16);
      case Iop_Or8:
         return definedOfType(Ity_I8);
      case Iop_Or1:
         return definedOfType(Ity_I1);

      case Iop_Xor8:
         return definedOfType(Ity_I8);
      case Iop_Xor16:
         return definedOfType(Ity_I16);
      case Iop_Xor32:
         return definedOfType(Ity_I32);
      case Iop_Xor64:
         return definedOfType(Ity_I64);
      case Iop_XorV128:
         return definedOfType(Ity_V128);
      case Iop_XorV256:
         return definedOfType(Ity_V256);

      /* V256-bit SIMD */

      case Iop_ShrN16x16:
      case Iop_ShrN32x8:
      case Iop_ShrN64x4:
      case Iop_SarN16x16:
      case Iop_SarN32x8:
      case Iop_ShlN16x16:
      case Iop_ShlN32x8:
      case Iop_ShlN64x4:
         /* Same scheme as with all other shifts.  Note: 22 Oct 05:
            this is wrong now, scalar shifts are done properly lazily.
            Vector shifts should be fixed too. */
         complainIfUndefined(kce, atom2, NULL);
         return definedOfType(Ity_V256);

      case Iop_QSub8Ux32:
      case Iop_QSub8Sx32:
      case Iop_Sub8x32:
      case Iop_Min8Ux32:
      case Iop_Min8Sx32:
      case Iop_Max8Ux32:
      case Iop_Max8Sx32:
      case Iop_CmpGT8Sx32:
      case Iop_CmpEQ8x32:
      case Iop_Avg8Ux32:
      case Iop_QAdd8Ux32:
      case Iop_QAdd8Sx32:
      case Iop_Add8x32:
         return definedOfType(Ity_V256);

      case Iop_QSub16Ux16:
      case Iop_QSub16Sx16:
      case Iop_Sub16x16:
      case Iop_Mul16x16:
      case Iop_MulHi16Sx16:
      case Iop_MulHi16Ux16:
      case Iop_Min16Sx16:
      case Iop_Min16Ux16:
      case Iop_Max16Sx16:
      case Iop_Max16Ux16:
      case Iop_CmpGT16Sx16:
      case Iop_CmpEQ16x16:
      case Iop_Avg16Ux16:
      case Iop_QAdd16Ux16:
      case Iop_QAdd16Sx16:
      case Iop_Add16x16:
         return definedOfType(Ity_V256);

      case Iop_Sub32x8:
      case Iop_CmpGT32Sx8:
      case Iop_CmpEQ32x8:
      case Iop_Add32x8:
      case Iop_Max32Ux8:
      case Iop_Max32Sx8:
      case Iop_Min32Ux8:
      case Iop_Min32Sx8:
      case Iop_Mul32x8:
         return definedOfType(Ity_V256);

      case Iop_Sub64x4:
      case Iop_Add64x4:
      case Iop_CmpEQ64x4:
      case Iop_CmpGT64Sx4:
         return definedOfType(Ity_V256);

      case Iop_I32StoF32x8:
      case Iop_F32toI32Sx8:
         return definedOfType(Ity_V256);

      case Iop_Perm32x8:
         return definedOfType(Ity_V256);

      case Iop_QandSQsh64x2:  case Iop_QandUQsh64x2:
      case Iop_QandSQRsh64x2: case Iop_QandUQRsh64x2:
      case Iop_QandSQsh32x4:  case Iop_QandUQsh32x4:
      case Iop_QandSQRsh32x4: case Iop_QandUQRsh32x4:
      case Iop_QandSQsh16x8:  case Iop_QandUQsh16x8:
      case Iop_QandSQRsh16x8: case Iop_QandUQRsh16x8:
      case Iop_QandSQsh8x16:  case Iop_QandUQsh8x16:
      case Iop_QandSQRsh8x16: case Iop_QandUQRsh8x16:
         return definedOfType(Ity_V256);

      case Iop_F32toF16x4:
         return definedOfType(Ity_I64);

      case Iop_F32toF16x8:
         return definedOfType(Ity_V128);

      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Binop");
   }
}

static 
IRExpr* expr2vbits_Unop ( KCEnv* kce, IROp op, IRAtom* atom )
{
   /* For the widening operations {8,16,32}{U,S}to{16,32,64}, the
      selection of shadow operation implicitly duplicates the logic in
      do_shadow_LoadG and should be kept in sync (in the very unlikely
      event that the interpretation of such widening ops changes in
      future).  See comment in do_shadow_LoadG. */
   IRAtom* vatom = expr2vbits( kce, atom );
   tl_assert(isOriginalAtom(kce,atom));
   switch (op) {

      case Iop_Abs64Fx2:
      case Iop_Neg64Fx2:
      case Iop_RSqrtEst64Fx2:
      case Iop_RecipEst64Fx2:
      case Iop_Log2_64Fx2:
         return definedOfType(Ity_V128);

      case Iop_Sqrt64F0x2:
         return definedOfType(Ity_V128);

      case Iop_Sqrt32Fx8:
      case Iop_RSqrtEst32Fx8:
      case Iop_RecipEst32Fx8:
         return definedOfType(Ity_V256);

      case Iop_Sqrt64Fx4:
         return definedOfType(Ity_V256);

      case Iop_RecipEst32Fx4:
      case Iop_I32UtoF32x4_DEP:
      case Iop_I32StoF32x4_DEP:
      case Iop_QF32toI32Ux4_RZ:
      case Iop_QF32toI32Sx4_RZ:
      case Iop_RoundF32x4_RM:
      case Iop_RoundF32x4_RP:
      case Iop_RoundF32x4_RN:
      case Iop_RoundF32x4_RZ:
      case Iop_RecipEst32Ux4:
      case Iop_Abs32Fx4:
      case Iop_Neg32Fx4:
      case Iop_RSqrtEst32Fx4:
      case Iop_Log2_32Fx4:
      case Iop_Exp2_32Fx4:
         return definedOfType(Ity_V128);

      case Iop_I32UtoF32x2_DEP:
      case Iop_I32StoF32x2_DEP:
      case Iop_RecipEst32Fx2:
      case Iop_RecipEst32Ux2:
      case Iop_Abs32Fx2:
      case Iop_Neg32Fx2:
      case Iop_RSqrtEst32Fx2:
         return definedOfType(Ity_I64);

      case Iop_Sqrt32F0x4:
      case Iop_RSqrtEst32F0x4:
      case Iop_RecipEst32F0x4:
         return definedOfType(Ity_V128);

      case Iop_Abs16Fx8:
      case Iop_Neg16Fx8:
         return definedOfType(Ity_V128);

      // These are self-shadowing.
      case Iop_32UtoV128:
      case Iop_64UtoV128:
      case Iop_Dup8x16:
      case Iop_Dup16x8:
      case Iop_Dup32x4:
      case Iop_Reverse1sIn8_x16:
      case Iop_Reverse8sIn16_x8:
      case Iop_Reverse8sIn32_x4:
      case Iop_Reverse16sIn32_x4:
      case Iop_Reverse8sIn64_x2:
      case Iop_Reverse16sIn64_x2:
      case Iop_Reverse32sIn64_x2:
      case Iop_V256toV128_1: case Iop_V256toV128_0:
      case Iop_ZeroHI64ofV128:
      case Iop_ZeroHI96ofV128:
      case Iop_ZeroHI112ofV128:
      case Iop_ZeroHI120ofV128:
      case Iop_ReinterpI128asV128:  /* I128 -> V128 */
         return definedOfType(Ity_V128);

      case Iop_F128HItoF64:  /* F128 -> high half of F128 */
      case Iop_D128HItoD64:  /* D128 -> high half of D128 */
         return definedOfType(Ity_I64);

      case Iop_F128LOtoF64:  /* F128 -> low  half of F128 */
      case Iop_D128LOtoD64:  /* D128 -> low  half of D128 */
         return definedOfType(Ity_I64);

      case Iop_NegF128:
      case Iop_AbsF128:
      case Iop_RndF128:
      case Iop_TruncF128toI128S: /* F128 -> I128S */
      case Iop_TruncF128toI128U: /* F128 -> I128U */
      case Iop_ReinterpV128asI128:  /* V128 -> I128 */
      case Iop_ReinterpI128asF128:
      case Iop_ReinterpF128asI128:
         return definedOfType(Ity_I128);

      case Iop_BCD128toI128S:
      case Iop_MulI128by10:
      case Iop_MulI128by10Carry:
      case Iop_F16toF64x2:
      case Iop_F64toF16x2_DEP:
         return definedOfType(Ity_I128);

      case Iop_ReinterpI32asF32:
      case Iop_ReinterpF32asI32:
         return definedOfType(Ity_I32);

      case Iop_ReinterpF64asI64:
      case Iop_ReinterpI64asF64:
      case Iop_ReinterpI64asD64:
      case Iop_ReinterpD64asI64:
         return definedOfType(Ity_I64);

      case Iop_I32StoF128: /* signed I32 -> F128 */
      case Iop_I64StoF128: /* signed I64 -> F128 */
      case Iop_I32UtoF128: /* unsigned I32 -> F128 */
      case Iop_I64UtoF128: /* unsigned I64 -> F128 */
      case Iop_F32toF128:  /* F32 -> F128 */
      case Iop_F64toF128:  /* F64 -> F128 */
      case Iop_I32StoD128: /* signed I64 -> D128 */
      case Iop_I64StoD128: /* signed I64 -> D128 */
      case Iop_I32UtoD128: /* unsigned I32 -> D128 */
      case Iop_I64UtoD128: /* unsigned I64 -> D128 */
         return definedOfType(Ity_I128);

      case Iop_F16toF64:
      case Iop_F32toF64: 
      case Iop_I32StoF64:
      case Iop_I32UtoF64:
      case Iop_NegF64:
      case Iop_AbsF64:
      case Iop_RSqrtEst5GoodF64:
      case Iop_RoundF64toF64_NEAREST:
      case Iop_RoundF64toF64_NegINF:
      case Iop_RoundF64toF64_PosINF:
      case Iop_RoundF64toF64_ZERO:
      case Iop_D32toD64:
      case Iop_I32StoD64:
      case Iop_I32UtoD64:
      case Iop_ExtractExpD64:    /* D64  -> I64 */
      case Iop_ExtractExpD128:   /* D128 -> I64 */
      case Iop_ExtractSigD64:    /* D64  -> I64 */
      case Iop_ExtractSigD128:   /* D128 -> I64 */
      case Iop_DPBtoBCD:
      case Iop_BCDtoDPB:
         return definedOfType(Ity_I64);

      case Iop_D64toD128:
         return definedOfType(Ity_I128);

      case Iop_TruncF64asF32:
      case Iop_NegF32:
      case Iop_AbsF32:
      case Iop_F16toF32: 
         return definedOfType(Ity_I32);

      case Iop_AbsF16:
      case Iop_NegF16:
         return definedOfType(Ity_I16);

      case Iop_Ctz32: case Iop_CtzNat32:
         return definedOfType(Ity_I32);
      case Iop_Ctz64: case Iop_CtzNat64:
         return definedOfType(Ity_I64);

      case Iop_Clz32: case Iop_ClzNat32:
         return definedOfType(Ity_I32);
      case Iop_Clz64: case Iop_ClzNat64:
         return definedOfType(Ity_I64);

      case Iop_PopCount32:
         return definedOfType(Ity_I32);
      case Iop_PopCount64:
         return definedOfType(Ity_I64);

      // These are self-shadowing.
      case Iop_1Uto64:
      case Iop_1Sto64:
      case Iop_8Uto64:
      case Iop_8Sto64:
      case Iop_16Uto64:
      case Iop_16Sto64:
      case Iop_32Sto64:
      case Iop_32Uto64:
      case Iop_V128to64:
      case Iop_V128HIto64:
      case Iop_128HIto64:
      case Iop_128to64:
      case Iop_Dup8x8:
      case Iop_Dup16x4:
      case Iop_Dup32x2:
      case Iop_Reverse8sIn16_x4:
      case Iop_Reverse8sIn32_x2:
      case Iop_Reverse16sIn32_x2:
      case Iop_Reverse8sIn64_x1:
      case Iop_Reverse16sIn64_x1:
      case Iop_Reverse32sIn64_x1:
      case Iop_V256to64_0: case Iop_V256to64_1:
      case Iop_V256to64_2: case Iop_V256to64_3:
         return definedOfType(Ity_I64);

      // These are self-shadowing.
      case Iop_64to32:
      case Iop_64HIto32:
      case Iop_1Uto32:
      case Iop_1Sto32:
      case Iop_8Uto32:
      case Iop_16Uto32:
      case Iop_16Sto32:
      case Iop_8Sto32:
      case Iop_V128to32:
      case Iop_Reverse8sIn32_x1:
         return definedOfType(Ity_I32);

      // These are self-shadowing.
      case Iop_1Sto16:
      case Iop_8Sto16:
      case Iop_8Uto16:
      case Iop_32to16:
      case Iop_32HIto16:
      case Iop_64to16:
      case Iop_GetMSBs8x16:
         return definedOfType(Ity_I16);

      // These are self-shadowing.
      case Iop_1Uto8:
      case Iop_1Sto8:
      case Iop_16to8:
      case Iop_16HIto8:
      case Iop_32to8:
      case Iop_64to8:
      case Iop_GetMSBs8x8:
         return definedOfType(Ity_I8);

      case Iop_32to1:
         return definedOfType(Ity_I1);

      case Iop_64to1:
         return definedOfType(Ity_I1);

      case Iop_NotV256:
         return definedOfType(Ity_V256);
      case Iop_NotV128:
         return definedOfType(Ity_V128);
      case Iop_Not64:
         return definedOfType(Ity_I64);
      case Iop_Not32:
         return definedOfType(Ity_I32);
      case Iop_Not16:
         return definedOfType(Ity_I16);
      case Iop_Not8:
         return definedOfType(Ity_I8);
      case Iop_Not1:
         return definedOfType(Ity_I1);

      case Iop_CmpNEZ8x8:
      case Iop_Cnt8x8:
      case Iop_Clz8x8:
      case Iop_Cls8x8:
      case Iop_Abs8x8:
         return definedOfType(Ity_I64);

      case Iop_CmpNEZ8x16:
      case Iop_Cnt8x16:
      case Iop_Clz8x16:
      case Iop_Cls8x16:
      case Iop_Abs8x16:
      case Iop_Ctz8x16:
         return definedOfType(Ity_V128);

      case Iop_CmpNEZ16x4:
      case Iop_Clz16x4:
      case Iop_Cls16x4:
      case Iop_Abs16x4:
         return definedOfType(Ity_I64);

      case Iop_CmpNEZ16x8:
      case Iop_Clz16x8:
      case Iop_Cls16x8:
      case Iop_Abs16x8:
      case Iop_Ctz16x8:
         return definedOfType(Ity_V128);

      case Iop_CmpNEZ32x2:
      case Iop_Clz32x2:
      case Iop_Cls32x2:
      case Iop_F32toI32Ux2_RZ:
      case Iop_F32toI32Sx2_RZ:
      case Iop_Abs32x2:
         return definedOfType(Ity_I64);

      case Iop_CmpNEZ32x4:
      case Iop_Clz32x4:
      case Iop_Cls32x4:
      case Iop_F32toI32Ux4_RZ:
      case Iop_F32toI32Sx4_RZ:
      case Iop_Abs32x4:
      case Iop_RSqrtEst32Ux4:
      case Iop_Ctz32x4:
         return definedOfType(Ity_V128);

      case Iop_TruncF128toI32S: /* F128 -> I32S (result stored in 64-bits) */
      case Iop_TruncF128toI32U: /* F128 -> I32U (result stored in 64-bits) */
      case Iop_CmpwNEZ32:
         return definedOfType(Ity_I32);

      case Iop_TruncF128toI64S: /* F128 -> I64S */
      case Iop_TruncF128toI64U: /* F128 -> I64U */
      case Iop_CmpwNEZ64:
         return definedOfType(Ity_I64);

      case Iop_CmpNEZ64x2:
      case Iop_CipherSV128:
      case Iop_Clz64x2:
      case Iop_Abs64x2:
      case Iop_Ctz64x2:
         return definedOfType(Ity_V128);

      // This is self-shadowing.
      case Iop_PwBitMtxXpose64x2:
         return definedOfType(Ity_V128);

      case Iop_NarrowUn16to8x8:
      case Iop_NarrowUn32to16x4:
      case Iop_NarrowUn64to32x2:
         return definedOfType(Ity_I64);
      case Iop_QNarrowUn16Sto8Sx8:
      case Iop_QNarrowUn16Sto8Ux8:
      case Iop_QNarrowUn16Uto8Ux8:
      case Iop_QNarrowUn32Sto16Sx4:
      case Iop_QNarrowUn32Sto16Ux4:
      case Iop_QNarrowUn32Uto16Ux4:
      case Iop_QNarrowUn64Sto32Sx2:
      case Iop_QNarrowUn64Sto32Ux2:
      case Iop_QNarrowUn64Uto32Ux2:
         return definedOfType(Ity_I64);

      case Iop_F32toF16x4_DEP:
         return definedOfType(Ity_I64);

      case Iop_Widen8Sto16x8:
      case Iop_Widen8Uto16x8:
      case Iop_Widen16Sto32x4:
      case Iop_Widen16Uto32x4:
      case Iop_Widen32Sto64x2:
      case Iop_Widen32Uto64x2:
         return definedOfType(Ity_V128);

      case Iop_F16toF32x4:
         return definedOfType(Ity_V128);

      case Iop_F16toF32x8:
         return definedOfType(Ity_V256);

      case Iop_PwAddL32Ux2:
      case Iop_PwAddL32Sx2:
         return definedOfType(Ity_I64);

      case Iop_PwAddL16Ux4:
      case Iop_PwAddL16Sx4:
         return definedOfType(Ity_I64);

      case Iop_PwAddL8Ux8:
      case Iop_PwAddL8Sx8:
         return definedOfType(Ity_I64);

      case Iop_PwAddL32Ux4:
      case Iop_PwAddL32Sx4:
         return definedOfType(Ity_V128);

      case Iop_PwAddL64Ux2:
         return definedOfType(Ity_V128);

      case Iop_PwAddL16Ux8:
      case Iop_PwAddL16Sx8:
         return definedOfType(Ity_V128);

      case Iop_PwAddL8Ux16:
      case Iop_PwAddL8Sx16:
         return definedOfType(Ity_V128);

      case Iop_I64UtoF32:
      default:
         ppIROp(op);
         VG_(tool_panic)("memcheck:expr2vbits_Unop");
   }
}

/* Worker function -- do not call directly.  See comments on
   expr2vbits_Load for the meaning of |guard|.

   Generates IR to (1) perform a definedness test of |addr|, (2)
   perform a validity test of |addr|, and (3) return the Vbits for the
   location indicated by |addr|.  All of this only happens when
   |guard| is NULL or |guard| evaluates to True at run time.

   If |guard| evaluates to False at run time, the returned value is
   the IR-mandated 0x55..55 value, and no checks nor shadow loads are
   performed.

   The definedness of |guard| itself is not checked.  That is assumed
   to have been done before this point, by the caller. */
static
IRAtom* expr2vbits_Load_WRK ( KCEnv* kce,
                              IREndness end, IRType ty,
                              IRAtom* addr, UInt bias, IRAtom* guard )
{
   tl_assert(isOriginalAtom(kce,addr));
   tl_assert(end == Iend_LE || end == Iend_BE);

   /* First, emit a definedness test for the address.  This also sets
      the address (shadow) to 'defined' following the test. */
   complainIfUndefined( kce, addr, guard );

   /* Now cook up a call to the relevant helper function, to read the data V
      bits from shadow memory.  Note that I128 loads are done by pretending
      we're doing a V128 load, and then converting the resulting V128 vbits
      word to an I128, right at the end of this function -- see `castedToI128`
      below.  (It's only a minor hack :-) This pertains to bug 444399. */
   ty = shadowTypeV(ty);

   void*        helper           = NULL;
   const HChar* hname            = NULL;
   Bool         ret_via_outparam = False;

   if (end == Iend_LE) {
      switch (ty) {
         case Ity_V256: helper = &KC_(helperc_LOADV256le);
                        hname = "KC_(helperc_LOADV256le)";
                        ret_via_outparam = True;
                        break;
         case Ity_I128: // fallthrough.  See comment above.
         case Ity_V128: helper = &KC_(helperc_LOADV128le);
                        hname = "KC_(helperc_LOADV128le)";
                        ret_via_outparam = True;
                        break;
         case Ity_I64:  helper = &KC_(helperc_LOADV64le);
                        hname = "KC_(helperc_LOADV64le)";
                        break;
         case Ity_I32:  helper = &KC_(helperc_LOADV32le);
                        hname = "KC_(helperc_LOADV32le)";
                        break;
         case Ity_I16:  helper = &KC_(helperc_LOADV16le);
                        hname = "KC_(helperc_LOADV16le)";
                        break;
         case Ity_I8:   helper = &KC_(helperc_LOADV8);
                        hname = "KC_(helperc_LOADV8)";
                        break;
         default:       ppIRType(ty);
                        VG_(tool_panic)("memcheck:expr2vbits_Load_WRK(LE)");
      }
   } else {
      switch (ty) {
         case Ity_V256: helper = &KC_(helperc_LOADV256be);
                        hname = "KC_(helperc_LOADV256be)";
                        ret_via_outparam = True;
                        break;
         case Ity_V128: helper = &KC_(helperc_LOADV128be);
                        hname = "KC_(helperc_LOADV128be)";
                        ret_via_outparam = True;
                        break;
         case Ity_I64:  helper = &KC_(helperc_LOADV64be);
                        hname = "KC_(helperc_LOADV64be)";
                        break;
         case Ity_I32:  helper = &KC_(helperc_LOADV32be);
                        hname = "KC_(helperc_LOADV32be)";
                        break;
         case Ity_I16:  helper = &KC_(helperc_LOADV16be);
                        hname = "KC_(helperc_LOADV16be)";
                        break;
         case Ity_I8:   helper = &KC_(helperc_LOADV8);
                        hname = "KC_(helperc_LOADV8)";
                        break;
         default:       ppIRType(ty);
                        VG_(tool_panic)("memcheck:expr2vbits_Load_WRK(BE)");
      }
   }

   tl_assert(helper);
   tl_assert(hname);

   /* Generate the actual address into addrAct. */
   IRAtom* addrAct;
   if (bias == 0) {
      addrAct = addr;
   } else {
      IROp    mkAdd;
      IRAtom* eBias;
      IRType  tyAddr  = kce->hWordTy;
      tl_assert( tyAddr == Ity_I32 || tyAddr == Ity_I64 );
      mkAdd   = tyAddr==Ity_I32 ? Iop_Add32 : Iop_Add64;
      eBias   = tyAddr==Ity_I32 ? mkU32(bias) : mkU64(bias);
      addrAct = assignNew('V', kce, tyAddr, binop(mkAdd, addr, eBias) );
   }

   /* We need to have a place to park the V bits we're just about to
      read. */
   IRTemp datavbits = newTemp(kce, ty == Ity_I128 ? Ity_V128 : ty, TBD);

   /* Here's the call. */
   IRDirty* di;
   if (ret_via_outparam) {
      di = unsafeIRDirty_1_N( datavbits, 
                              2/*regparms*/, 
                              hname, VG_(fnptr_to_fnentry)( helper ), 
                              mkIRExprVec_2( IRExpr_VECRET(), addrAct ) );
   } else {
      di = unsafeIRDirty_1_N( datavbits, 
                              1/*regparms*/, 
                              hname, VG_(fnptr_to_fnentry)( helper ), 
                              mkIRExprVec_1( addrAct ) );
   }

   setHelperAnns( kce, di );
   if (guard) {
      di->guard = guard;
      /* Ideally the didn't-happen return value here would be all-ones
         (all-undefined), so it'd be obvious if it got used
         inadvertently.  We can get by with the IR-mandated default
         value (0b01 repeating, 0x55 etc) as that'll still look pretty
         undefined if it ever leaks out. */
   }
   stmt( 'V', kce, IRStmt_Dirty(di) );

   if (ty == Ity_I128) {
      IRAtom* castedToI128
         = assignNew('V', kce, Ity_I128,
                     unop(Iop_ReinterpV128asI128, mkexpr(datavbits)));
      return castedToI128;
   } else {
      return mkexpr(datavbits);
   }
}

static
IRAtom* expr2vbits_Load ( KCEnv* kce,
                          IREndness end, IRType ty,
                          IRAtom* addr, UInt bias,
                          IRAtom* guard )
{
   tl_assert(end == Iend_LE || end == Iend_BE);
   switch (shadowTypeV(ty)) {
      case Ity_I8:
      case Ity_I16:
      case Ity_I32:
      case Ity_I64:
      case Ity_I128:
      case Ity_V128:
      case Ity_V256:
         return expr2vbits_Load_WRK(kce, end, ty, addr, bias, guard);
      default:
         VG_(tool_panic)("expr2vbits_Load");
   }
}

static
IRAtom* expr2vbits_Load_guarded_General ( KCEnv* kce,
                                          IREndness end, IRType ty,
                                          IRAtom* addr, UInt bias,
                                          IRAtom* guard,
                                          IROp vwiden, IRAtom* valt )
{
   tl_assert(0); // unimplemented
}

static
IRAtom* expr2vbits_Load_guarded_Simple ( KCEnv* kce, 
                                         IREndness end, IRType ty, 
                                         IRAtom* addr, UInt bias,
                                         IRAtom *guard )
{
   tl_assert(0); // unimplemented
}

static
IRAtom* expr2vbits_ITE ( KCEnv* kce, 
                         IRAtom* cond, IRAtom* iftrue, IRAtom* iffalse )
{
   IRAtom *vbitsC, *vbits0, *vbits1;
   IRType ty;
   /* Given ITE(cond, iftrue,  iffalse),  generate
            ITE(cond, iftrue#, iffalse#) `UifU` PCast(cond#)
      That is, steer the V bits like the originals, but trash the 
      result if the steering value is undefined.  This gives 
      lazy propagation. */

   tl_assert(isOriginalAtom(kce, cond));
   tl_assert(isOriginalAtom(kce, iftrue));
   tl_assert(isOriginalAtom(kce, iffalse));

   vbitsC = expr2vbits(kce, cond );
   vbits1 = expr2vbits(kce, iftrue );
   vbits0 = expr2vbits(kce, iffalse );
   ty = typeOfIRExpr(kce->sb->tyenv, vbits0);

   return
      mkUifU(kce, ty, assignNew('V', kce, ty, 
                                     IRExpr_ITE(cond, vbits1, vbits0)),
                      mkPCastTo(kce, ty, vbitsC) );
}

/* --------- This is the main expression-handling function. --------- */

static
IRExpr* expr2vbits ( KCEnv* kce, IRExpr* e )
{
   switch (e->tag) {

      case Iex_Get:
         return shadow_GET( kce, e->Iex.Get.offset, e->Iex.Get.ty );

      case Iex_GetI:
         return shadow_GETI( kce, e->Iex.GetI.descr, 
                                  e->Iex.GetI.ix, e->Iex.GetI.bias );

      case Iex_RdTmp:
         return IRExpr_RdTmp( findShadowTmpV(kce, e->Iex.RdTmp.tmp) );

      case Iex_Const:
         return definedOfType(shadowTypeV(typeOfIRExpr(kce->sb->tyenv, e)));

      case Iex_Qop:
         return expr2vbits_Qop(
                   kce,
                   e->Iex.Qop.details->op,
                   e->Iex.Qop.details->arg1, e->Iex.Qop.details->arg2,
                   e->Iex.Qop.details->arg3, e->Iex.Qop.details->arg4
                );

      case Iex_Triop:
         return expr2vbits_Triop(
                   kce,
                   e->Iex.Triop.details->op,
                   e->Iex.Triop.details->arg1, e->Iex.Triop.details->arg2,
                   e->Iex.Triop.details->arg3
                );

      case Iex_Binop:
         return expr2vbits_Binop(
                   kce,
                   e->Iex.Binop.op,
                   e->Iex.Binop.arg1, e->Iex.Binop.arg2
                );

      case Iex_Unop:
         return expr2vbits_Unop( kce, e->Iex.Unop.op, e->Iex.Unop.arg );

      case Iex_Load:
         return expr2vbits_Load( kce, e->Iex.Load.end,
                                      e->Iex.Load.ty, 
                                      e->Iex.Load.addr, 0/*addr bias*/, 
                                      NULL/* guard == "always True"*/ );

      case Iex_CCall:
         return mkLazyN( kce, e->Iex.CCall.args, 
                              e->Iex.CCall.retty,
                              e->Iex.CCall.cee );

      case Iex_ITE:
         return expr2vbits_ITE( kce, e->Iex.ITE.cond, e->Iex.ITE.iftrue, 
                                     e->Iex.ITE.iffalse);

      default: 
         VG_(printf)("\n");
         ppIRExpr(e);
         VG_(printf)("\n");
         VG_(tool_panic)("memcheck: expr2vbits");
   }
}

/*------------------------------------------------------------*/
/*--- Generate shadow stmts from all kinds of IRStmts.     ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- MC Origin tracking stuff                             ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- MC Post-tree-build final tidying                     ---*/
/*------------------------------------------------------------*/

static Bool is_helperc_value_checkN_fail ( const HChar* name )
{
   /* This is expensive because it happens a lot.  We are checking to
      see whether |name| is one of the following 8 strings:

         KC_(helperc_value_check8_fail_no_o)
         KC_(helperc_value_check4_fail_no_o)
         KC_(helperc_value_check0_fail_no_o)
         KC_(helperc_value_check1_fail_no_o)
         KC_(helperc_value_check8_fail_w_o)
         KC_(helperc_value_check0_fail_w_o)
         KC_(helperc_value_check1_fail_w_o)
         KC_(helperc_value_check4_fail_w_o)

      To speed it up, check the common prefix just once, rather than
      all 8 times.
   */
   const HChar* prefix = "KC_(helperc_value_check";

   HChar n, p;
   while (True) {
      n = *name;
      p = *prefix;
      if (p == 0) break; /* ran off the end of the prefix */
      /* We still have some prefix to use */
      if (n == 0) return False; /* have prefix, but name ran out */
      if (n != p) return False; /* have both pfx and name, but no match */
      name++;
      prefix++;
   }

   /* Check the part after the prefix. */
   tl_assert(*prefix == 0 && *name != 0);
   return    0==VG_(strcmp)(name, "8_fail_no_o)")
          || 0==VG_(strcmp)(name, "4_fail_no_o)")
          || 0==VG_(strcmp)(name, "0_fail_no_o)")
          || 0==VG_(strcmp)(name, "1_fail_no_o)")
          || 0==VG_(strcmp)(name, "8_fail_w_o)")
          || 0==VG_(strcmp)(name, "4_fail_w_o)")
          || 0==VG_(strcmp)(name, "0_fail_w_o)")
          || 0==VG_(strcmp)(name, "1_fail_w_o)");
}

/*------------------------------------------------------------*/
/*--- KC Startup assertion checking                        ---*/
/*------------------------------------------------------------*/

void KC_(do_instrumentation_startup_checks) ( void )
{
   /* Make a best-effort check to see that is_helperc_value_checkN_fail
      is working as we expect. */

#  define CHECK(_expected, _string) \
      tl_assert((_expected) == is_helperc_value_checkN_fail(_string))

   /* It should identify these 8, and no others, as targets. */
   CHECK(True, "KC_(helperc_value_check8_fail_no_o)");
   CHECK(True, "KC_(helperc_value_check4_fail_no_o)");
   CHECK(True, "KC_(helperc_value_check0_fail_no_o)");
   CHECK(True, "KC_(helperc_value_check1_fail_no_o)");
   CHECK(True, "KC_(helperc_value_check8_fail_w_o)");
   CHECK(True, "KC_(helperc_value_check0_fail_w_o)");
   CHECK(True, "KC_(helperc_value_check1_fail_w_o)");
   CHECK(True, "KC_(helperc_value_check4_fail_w_o)");

   /* Ad-hoc selection of other strings gathered via a quick test. */
   CHECK(False, "amd64g_dirtyhelper_CPUID_avx2");
   CHECK(False, "amd64g_dirtyhelper_RDTSC");
   CHECK(False, "KC_(helperc_b_load1)");
   CHECK(False, "KC_(helperc_b_load2)");
   CHECK(False, "KC_(helperc_b_load4)");
   CHECK(False, "KC_(helperc_b_load8)");
   CHECK(False, "KC_(helperc_b_load16)");
   CHECK(False, "KC_(helperc_b_load32)");
   CHECK(False, "KC_(helperc_b_store1)");
   CHECK(False, "KC_(helperc_b_store2)");
   CHECK(False, "KC_(helperc_b_store4)");
   CHECK(False, "KC_(helperc_b_store8)");
   CHECK(False, "KC_(helperc_b_store16)");
   CHECK(False, "KC_(helperc_b_store32)");
   CHECK(False, "KC_(helperc_LOADV8)");
   CHECK(False, "KC_(helperc_LOADV16le)");
   CHECK(False, "KC_(helperc_LOADV32le)");
   CHECK(False, "KC_(helperc_LOADV64le)");
   CHECK(False, "KC_(helperc_LOADV128le)");
   CHECK(False, "KC_(helperc_LOADV256le)");
   CHECK(False, "KC_(helperc_STOREV16le)");
   CHECK(False, "KC_(helperc_STOREV32le)");
   CHECK(False, "KC_(helperc_STOREV64le)");
   CHECK(False, "KC_(helperc_STOREV8)");
   CHECK(False, "track_die_mem_stack_8");
   CHECK(False, "track_new_mem_stack_8_w_ECU");
   CHECK(False, "KC_(helperc_MAKE_STACK_UNINIT_w_o)");
   CHECK(False, "VG_(unknown_SP_update_w_ECU)");

#  undef CHECK
}


/*------------------------------------------------------------*/
/*--- Krabcake main                                        ---*/
/*------------------------------------------------------------*/

static void trace_wrtmp_load(Addr addr, SizeT size)
{
   // VG_(printf)("trace_wrtmp_load addr=%08llx size=%llu\n", addr, size);
}

static void trace_llsc()
{
   VG_(printf)("trace_llsc\n");
}

IRSB* KC_(instrument) ( VgCallbackClosure* closure,
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
   Int        i, j, firstStmt;
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
   kce.layout         = layout;
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

   for (/* use current i*/; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      firstStmt = sbOut->stmts_used;

      if (!st) continue; // mc_translate does not have this. Should we assert st here instead?

      if (verboze) {
         VG_(printf)("\n");
         ppIRStmt(st);
         VG_(printf)("\n");
      }

      switch (st->tag) {
         // == LOAD+STORE instructions ==

         // `t<tmp> = <data>` assigns value to an (SSA) temporary.
      case Ist_WrTmp: {
         IRTemp  dst  = st->Ist.WrTmp.tmp;  // LHS
         IRExpr* data = st->Ist.WrTmp.data; // RHS

         tl_assert(dst < (UInt)sbIn->tyenv->types_used);

         IRType  type = typeOfIRExpr(tyenv, data);

         assign( 'V', &kce, findShadowTmpV(&kce, st->Ist.WrTmp.tmp), 
                 expr2vbits( &kce, st->Ist.WrTmp.data ));

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


/*--------------------------------------------------------------------*/
/*--- end                                           kc_translate.c ---*/
/*--------------------------------------------------------------------*/
