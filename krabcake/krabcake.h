#include "valgrind.h"

typedef enum {
   VG_USERREQ__BORROW_MUT = VG_USERREQ_TOOL_BASE('K','C'),
   VG_USERREQ__BORROW_SHR,
   VG_USERREQ__AS_RAW,
   VG_USERREQ__AS_BORROW_MUT,
   VG_USERREQ__AS_BORROW_SHR,
   VG_USERREQ__RETAG_FN_PROLOGUE,
   VG_USERREQ__RETAG_ASSIGN,
   VG_USERREQ__RETAG_RAW,
   VG_USERREQ__INTRINSICS_ASSUME,
   VG_USERREQ__PRINT_TAG_OF,
   VG_USERREQ__PRINT_STACK_OF,
   _VG_USERREQ__KRABCAKE_RECORD_OVERLAP_ERROR
   = VG_USERREQ_TOOL_BASE('K','C') + 256
} Vg_KrabCakeClientRequest;

// encodes &mut PLACE, supplying pointee type first to placate cc
#define KC_BORROW_MUT(_type, _place)                             \
   ((_type*) VALGRIND_DO_CLIENT_REQUEST_EXPR(                    \
      &(_place), VG_USERREQ__BORROW_MUT, &(_place), 0, 0, 0, 0))

// encodes &PLACE, supplying pointee type first to placate cc
#define KC_BORROW(_type, _place)                                \
   ((_type*) VALGRIND_DO_CLIENT_REQUEST_EXPR(                   \
      &(_place), VG_USERREQ__BORROW_SHR, &(_place), 0, 0, 0, 0))
