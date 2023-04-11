/*--------------------------------------------------------------------*/
/*--- A header file for all parts of KrabCake tool.   kc_include.h ---*/
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

#ifndef __KC_INCLUDE_H
#define __KC_INCLUDE_H

#define KC_(str)    VGAPPEND(vgKrabCake_,str)

/* This is a private header file for use only within the
   krabcake/ directory. */

/*------------------------------------------------------------*/
/*--- Tracking the heap                                    ---*/
/*------------------------------------------------------------*/

/* By default, we want at least a 16B redzone on client heap blocks
   for Krabcake.
   The default can be modified by --redzone-size. */
#define KC_MALLOC_DEFAULT_REDZONE_SZB    16
// effective redzone, as (possibly) modified by --redzone-size:
extern SizeT KC_(Malloc_Redzone_SzB);

/*------------------------------------------------------------*/
/*--- Origin tracking translate-time support               ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Profiling of memory events                           ---*/
/*------------------------------------------------------------*/

/* Define to collect detailed performance info. */
/* #define KC_PROFILE_MEMORY */
#ifdef KC_PROFILE_MEMORY

/* Order of enumerators does not matter. But KCPE_LAST has to be the 
   last entry in the list as it is used as an array bound. */
enum {
   KCPE_LOADV8,
   KCPE_LOADV8_SLOW1,
   KCPE_LOADV8_SLOW2,
   KCPE_LOADV16,
   KCPE_LOADV16_SLOW1,
   KCPE_LOADV16_SLOW2,
   KCPE_LOADV32,
   KCPE_LOADV32_SLOW1,
   KCPE_LOADV32_SLOW2,
   KCPE_LOADV64,
   KCPE_LOADV64_SLOW1,
   KCPE_LOADV64_SLOW2,
   KCPE_LOADV_128_OR_256,
   KCPE_LOADV_128_OR_256_SLOW_LOOP,
   KCPE_LOADV_128_OR_256_SLOW1,
   KCPE_LOADV_128_OR_256_SLOW2,
   KCPE_LOADVN_SLOW,
   KCPE_LOADVN_SLOW_LOOP,
   KCPE_STOREV8,
   KCPE_STOREV8_SLOW1,
   KCPE_STOREV8_SLOW2,
   KCPE_STOREV8_SLOW3,
   KCPE_STOREV8_SLOW4,
   KCPE_STOREV16,
   KCPE_STOREV16_SLOW1,
   KCPE_STOREV16_SLOW2,
   KCPE_STOREV16_SLOW3,
   KCPE_STOREV16_SLOW4,
   KCPE_STOREV32,
   KCPE_STOREV32_SLOW1,
   KCPE_STOREV32_SLOW2,
   KCPE_STOREV32_SLOW3,
   KCPE_STOREV32_SLOW4,
   KCPE_STOREV64,
   KCPE_STOREV64_SLOW1,
   KCPE_STOREV64_SLOW2,
   KCPE_STOREV64_SLOW3,
   KCPE_STOREV64_SLOW4,
   KCPE_STOREVN_SLOW,
   KCPE_STOREVN_SLOW_LOOP,
   KCPE_MAKE_ALIGNED_WORD32_UNDEFINED,
   KCPE_MAKE_ALIGNED_WORD32_UNDEFINED_SLOW,
   KCPE_MAKE_ALIGNED_WORD64_UNDEFINED,
   KCPE_MAKE_ALIGNED_WORD64_UNDEFINED_SLOW,
   KCPE_MAKE_ALIGNED_WORD32_NOACCESS,
   KCPE_MAKE_ALIGNED_WORD32_NOACCESS_SLOW,
   KCPE_MAKE_ALIGNED_WORD64_NOACCESS,
   KCPE_MAKE_ALIGNED_WORD64_NOACCESS_SLOW,
   KCPE_MAKE_MEM_NOACCESS,
   KCPE_MAKE_MEM_UNDEFINED,
   KCPE_MAKE_MEM_UNDEFINED_W_OTAG,
   KCPE_MAKE_MEM_DEFINED,
   KCPE_CHEAP_SANITY_CHECK,
   KCPE_EXPENSIVE_SANITY_CHECK,
   KCPE_COPY_ADDRESS_RANGE_STATE,
   KCPE_COPY_ADDRESS_RANGE_STATE_LOOP1,
   KCPE_COPY_ADDRESS_RANGE_STATE_LOOP2,
   KCPE_CHECK_MEM_IS_NOACCESS,
   KCPE_CHECK_MEM_IS_NOACCESS_LOOP,
   KCPE_IS_MEM_ADDRESSABLE,
   KCPE_IS_MEM_ADDRESSABLE_LOOP,
   KCPE_IS_MEM_DEFINED,
   KCPE_IS_MEM_DEFINED_LOOP,
   KCPE_IS_MEM_DEFINED_COMPREHENSIVE,
   KCPE_IS_MEM_DEFINED_COMPREHENSIVE_LOOP,
   KCPE_IS_DEFINED_ASCIIZ,
   KCPE_IS_DEFINED_ASCIIZ_LOOP,
   KCPE_FIND_CHUNK_FOR_OLD,
   KCPE_FIND_CHUNK_FOR_OLD_LOOP,
   KCPE_SET_ADDRESS_RANGE_PERMS,
   KCPE_SET_ADDRESS_RANGE_PERMS_SINGLE_SECMAP,
   KCPE_SET_ADDRESS_RANGE_PERMS_STARTOF_SECMAP,
   KCPE_SET_ADDRESS_RANGE_PERMS_MULTIPLE_SECMAPS,
   KCPE_SET_ADDRESS_RANGE_PERMS_DIST_SM1,
   KCPE_SET_ADDRESS_RANGE_PERMS_DIST_SM2,
   KCPE_SET_ADDRESS_RANGE_PERMS_DIST_SM1_QUICK,
   KCPE_SET_ADDRESS_RANGE_PERMS_DIST_SM2_QUICK,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP1A,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP1B,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP1C,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP8A,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP8B,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP64K,
   KCPE_SET_ADDRESS_RANGE_PERMS_LOOP64K_FREE_DIST_SM,
   KCPE_NEW_MEM_STACK,
   KCPE_NEW_MEM_STACK_4,
   KCPE_NEW_MEM_STACK_8,
   KCPE_NEW_MEM_STACK_12,
   KCPE_NEW_MEM_STACK_16,
   KCPE_NEW_MEM_STACK_32,
   KCPE_NEW_MEM_STACK_112,
   KCPE_NEW_MEM_STACK_128,
   KCPE_NEW_MEM_STACK_144,
   KCPE_NEW_MEM_STACK_160,
   KCPE_DIE_MEM_STACK,
   KCPE_DIE_MEM_STACK_4,
   KCPE_DIE_MEM_STACK_8,
   KCPE_DIE_MEM_STACK_12,
   KCPE_DIE_MEM_STACK_16,
   KCPE_DIE_MEM_STACK_32,
   KCPE_DIE_MEM_STACK_112,
   KCPE_DIE_MEM_STACK_128,
   KCPE_DIE_MEM_STACK_144,
   KCPE_DIE_MEM_STACK_160,
   KCPE_MAKE_STACK_UNINIT_W_O,
   KCPE_MAKE_STACK_UNINIT_NO_O,
   KCPE_MAKE_STACK_UNINIT_128_NO_O,
   KCPE_MAKE_STACK_UNINIT_128_NO_O_ALIGNED_16,
   KCPE_MAKE_STACK_UNINIT_128_NO_O_ALIGNED_8,
   KCPE_MAKE_STACK_UNINIT_128_NO_O_SLOWCASE,
   /* Do not add enumerators past this line. */
   KCPE_LAST
};

extern ULong KC_(event_ctr)[KCPE_LAST];

#  define PROF_EVENT(ev)                           \
   do { tl_assert((ev) >= 0 && (ev) < KCPE_LAST);  \
      KC_(event_ctr)[ev]++;                        \
   } while (False);

#else

#  define PROF_EVENT(ev)    /* */

#endif   /* KC_PROFILE_MEMORY */


/*------------------------------------------------------------*/
/*--- V and A bits (Victoria & Albert ?)                   ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Leak checking                                        ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Errors and suppressions                              ---*/
/*------------------------------------------------------------*/

/* Did we show to the user, any errors for which an uninitialised
   value origin could have been collected (but wasn't) ?  If yes,
   then, at the end of the run, print a 1 line message advising that a
   rerun with --track-origins=yes might help. */
extern Bool KC_(any_value_errors);

/* Standard functions for error and suppressions as required by the
   core/tool iface */
Bool KC_(eq_Error)           ( VgRes res, const Error* e1, const Error* e2 );
void KC_(before_pp_Error)    ( const Error* err );
void KC_(pp_Error)           ( const Error* err );
UInt KC_(update_Error_extra) ( const Error* err );

Bool KC_(is_recognised_suppression) ( const HChar* name, Supp* su );

Bool KC_(read_extra_suppression_info) ( Int fd, HChar** buf,
                                        SizeT* nBuf, Int* lineno, Supp *su );

Bool KC_(error_matches_suppression) ( const Error* err, const Supp* su );

SizeT KC_(get_extra_suppression_info) ( const Error* err,
                                        /*OUT*/HChar* buf, Int nBuf );
SizeT KC_(print_extra_suppression_use) ( const Supp* su,
                                         /*OUT*/HChar* buf, Int nBuf );
void KC_(update_extra_suppression_use) ( const Error* err, const Supp* su );

const HChar* KC_(get_error_name) ( const Error* err );

/* Recording of errors */
void KC_(record_address_error) ( ThreadId tid, Addr a, Int szB,
                                 Bool isWrite );
void KC_(record_cond_error)    ( ThreadId tid, UInt otag );
void KC_(record_value_error)   ( ThreadId tid, Int szB, UInt otag );
void KC_(record_jump_error)    ( ThreadId tid, Addr a );

void KC_(record_free_error)            ( ThreadId tid, Addr a ); 
void KC_(record_illegal_mempool_error) ( ThreadId tid, Addr a );

/*
void KC_(record_freemismatch_error)    ( ThreadId tid, KC_Chunk* mc );
*/

void KC_(record_overlap_error)  ( ThreadId tid, const HChar* function,
                                  Addr src, Addr dst, SizeT szB );
void KC_(record_core_mem_error) ( ThreadId tid, const HChar* msg );
void KC_(record_regparam_error) ( ThreadId tid, const HChar* msg, UInt otag );
void KC_(record_memparam_error) ( ThreadId tid, Addr a, 
                                  Bool isAddrErr, const HChar* msg, UInt otag );
void KC_(record_user_error)     ( ThreadId tid, Addr a,
                                  Bool isAddrErr, UInt otag );

/*
Bool KC_(record_leak_error)     ( ThreadId tid,
                                  UInt n_this_record,
                                  UInt n_total_records,
                                  LossRecord* lossRecord,
                                  Bool print_record,
                                  Bool count_error );
*/

Bool KC_(record_fishy_value_error)  ( ThreadId tid, const HChar* function,
                                      const HChar *argument_name, SizeT value );

/* Leak kinds tokens to call VG_(parse_enum_set). */
extern const HChar* KC_(parse_leak_kinds_tokens);

/* prints a description of address a in the specified debuginfo epoch */
void KC_(pp_describe_addr) ( DiEpoch ep, Addr a );

/* Is this address in a user-specified "ignored range" ? */
Bool KC_(in_ignored_range) ( Addr a );

/* Is this address in a user-specified "ignored range of offsets below
   the current thread's stack pointer?" */
Bool KC_(in_ignored_range_below_sp) ( Addr sp, Addr a, UInt szB );

/*------------------------------------------------------------*/
/*--- Client blocks                                        ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Command line options + defaults                      ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Instrumentation                                      ---*/
/*------------------------------------------------------------*/

/* Functions defined in kc_main.c */

/* For the fail_w_o functions, the UWord arg is actually the 32-bit
   origin tag and should really be UInt, but to be simple and safe
   considering it's called from generated code, just claim it to be a
   UWord. */
VG_REGPARM(2) void KC_(helperc_value_checkN_fail_w_o) ( HWord, UWord );
VG_REGPARM(1) void KC_(helperc_value_check8_fail_w_o) ( UWord );
VG_REGPARM(1) void KC_(helperc_value_check4_fail_w_o) ( UWord );
VG_REGPARM(1) void KC_(helperc_value_check1_fail_w_o) ( UWord );
VG_REGPARM(1) void KC_(helperc_value_check0_fail_w_o) ( UWord );

/* And call these ones instead to report an uninitialised value error
   but with no origin available. */
VG_REGPARM(1) void KC_(helperc_value_checkN_fail_no_o) ( HWord );
VG_REGPARM(0) void KC_(helperc_value_check8_fail_no_o) ( void );
VG_REGPARM(0) void KC_(helperc_value_check4_fail_no_o) ( void );
VG_REGPARM(0) void KC_(helperc_value_check1_fail_no_o) ( void );
VG_REGPARM(0) void KC_(helperc_value_check0_fail_no_o) ( void );

/* V-bits load/store helpers */
VG_REGPARM(1) void KC_(helperc_STOREV64be) ( Addr, ULong );
VG_REGPARM(1) void KC_(helperc_STOREV64le) ( Addr, ULong );
VG_REGPARM(2) void KC_(helperc_STOREV32be) ( Addr, UWord );
VG_REGPARM(2) void KC_(helperc_STOREV32le) ( Addr, UWord );
VG_REGPARM(2) void KC_(helperc_STOREV16be) ( Addr, UWord );
VG_REGPARM(2) void KC_(helperc_STOREV16le) ( Addr, UWord );
VG_REGPARM(2) void KC_(helperc_STOREV8)    ( Addr, UWord );

VG_REGPARM(2) void  KC_(helperc_LOADV256be) ( /*OUT*/V256*, Addr );
VG_REGPARM(2) void  KC_(helperc_LOADV256le) ( /*OUT*/V256*, Addr );
VG_REGPARM(2) void  KC_(helperc_LOADV128be) ( /*OUT*/V128*, Addr );
VG_REGPARM(2) void  KC_(helperc_LOADV128le) ( /*OUT*/V128*, Addr );
VG_REGPARM(1) ULong KC_(helperc_LOADV64be)  ( Addr );
VG_REGPARM(1) ULong KC_(helperc_LOADV64le)  ( Addr );
VG_REGPARM(1) UWord KC_(helperc_LOADV32be)  ( Addr );
VG_REGPARM(1) UWord KC_(helperc_LOADV32le)  ( Addr );
VG_REGPARM(1) UWord KC_(helperc_LOADV16be)  ( Addr );
VG_REGPARM(1) UWord KC_(helperc_LOADV16le)  ( Addr );
VG_REGPARM(1) UWord KC_(helperc_LOADV8)     ( Addr );

VG_REGPARM(3)
void KC_(helperc_MAKE_STACK_UNINIT_w_o) ( Addr base, UWord len, Addr nia );

VG_REGPARM(2)
void KC_(helperc_MAKE_STACK_UNINIT_no_o) ( Addr base, UWord len );

VG_REGPARM(1)
void KC_(helperc_MAKE_STACK_UNINIT_128_no_o) ( Addr base );

/* Origin tag load/store helpers */
VG_REGPARM(2) void  KC_(helperc_b_store1) ( Addr a, UWord d32 );
VG_REGPARM(2) void  KC_(helperc_b_store2) ( Addr a, UWord d32 );
VG_REGPARM(2) void  KC_(helperc_b_store4) ( Addr a, UWord d32 );
VG_REGPARM(2) void  KC_(helperc_b_store8) ( Addr a, UWord d32 );
VG_REGPARM(2) void  KC_(helperc_b_store16)( Addr a, UWord d32 );
VG_REGPARM(2) void  KC_(helperc_b_store32)( Addr a, UWord d32 );
VG_REGPARM(1) UWord KC_(helperc_b_load1) ( Addr a );
VG_REGPARM(1) UWord KC_(helperc_b_load2) ( Addr a );
VG_REGPARM(1) UWord KC_(helperc_b_load4) ( Addr a );
VG_REGPARM(1) UWord KC_(helperc_b_load8) ( Addr a );
VG_REGPARM(1) UWord KC_(helperc_b_load16)( Addr a );
VG_REGPARM(1) UWord KC_(helperc_b_load32)( Addr a );

/* Functions defined in kc_translate.c */
IRSB* KC_(instrument) ( VgCallbackClosure* closure,
                        IRSB* sbIn,
                        const VexGuestLayout* layout,
                        const VexGuestExtents* vge,
                        const VexArchInfo* archinfo_host,
                        IRType gWordTy, IRType hWordTy );

/* Check some assertions to do with the instrumentation machinery. */
void KC_(do_instrumentation_startup_checks)( void );

#endif /* ndef __KC_INCLUDE_H */

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
