
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
#include "pub_tool_tooliface.h"

#include "krabcake.h" /* for client requests */

extern void hello_world(void); // declare the Rust function

static void kc_post_clo_init(void)
{
   hello_world();
}

static
IRSB* kc_instrument ( VgCallbackClosure* closure,
                      IRSB* bb,
                      const VexGuestLayout* layout,
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   return bb;
}

static void kc_fini(Int exitcode)
{
}

static Bool kc_process_cmd_line_options(const HChar* arg)
{}

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
   Int   i;
   Addr  bad_addr;
   Bool  handled = False;

   if (!VG_IS_TOOL_USERREQ('K','C',arg[0]))
      return False;

   VG_(dmsg)("kc_handle_client_request, dispatching client request code %llx\n", (ULong)arg[0]);

   switch(arg[0]) {
   case VG_USERREQ__BORROW_MUT: {
      VG_(dmsg)("kc_handle_client_request, handle BORROW_MUT %llx %llx\n",
                arg[1], arg[2]);
      *ret = arg[1];
      handled = True;
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
