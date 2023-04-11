
/*--------------------------------------------------------------------*/
/*--- Management, printing, etc, of errors and suppressions.       ---*/
/*---                                                  kc_errors.c ---*/
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

#include "kc_include.h"

/*------------------------------------------------------------*/
/*--- Error types                                          ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Printing errors                                      ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Recording errors                                     ---*/
/*------------------------------------------------------------*/

void KC_(record_address_error) ( ThreadId tid, Addr a, Int szB,
                                 Bool isWrite )
{
   tl_assert(0); // unimplemented
}

void KC_(record_value_error) ( ThreadId tid, Int szB, UInt otag )
{
   tl_assert(0); // unimplemented
}

void KC_(record_cond_error) ( ThreadId tid, UInt otag )
{
   tl_assert(0); // unimplemented
}

void KC_(record_jump_error)    ( ThreadId tid, Addr a )
{
   tl_assert(0); // unimplemented
}

void KC_(record_free_error)            ( ThreadId tid, Addr a )
{
   tl_assert(0); // unimplemented
}

void KC_(record_illegal_mempool_error) ( ThreadId tid, Addr a )
{
   tl_assert(0); // unimplemented
}

void KC_(record_overlap_error)  ( ThreadId tid, const HChar* function,
                                  Addr src, Addr dst, SizeT szB )
{
   tl_assert(0); // unimplemented
}

void KC_(record_core_mem_error) ( ThreadId tid, const HChar* msg )
{
   tl_assert(0); // unimplemented
}

void KC_(record_regparam_error) ( ThreadId tid, const HChar* msg, UInt otag )
{
   tl_assert(0); // unimplemented
}

void KC_(record_memparam_error) ( ThreadId tid, Addr a, 
                                  Bool isAddrErr, const HChar* msg, UInt otag )
{
   tl_assert(0); // unimplemented
}

void KC_(record_user_error)     ( ThreadId tid, Addr a,
                                  Bool isAddrErr, UInt otag )
{
   tl_assert(0); // unimplemented
}


/*------------------------------------------------------------*/
/*--- Other error operations                               ---*/
/*------------------------------------------------------------*/

/*------------------------------------------------------------*/
/*--- Suppressions                                         ---*/
/*------------------------------------------------------------*/

/*--------------------------------------------------------------------*/
/*--- end                                              kc_errors.c ---*/
/*--------------------------------------------------------------------*/

