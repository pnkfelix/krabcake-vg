include $(top_srcdir)/Makefile.tool.am

EXTRA_DIST = docs/kc-manual.xml

RSHELLO_DIR = rs_hello
RSHELLO_TARGET = $(RSHELLO_DIR)/target/release

#$(RSHELLO_TARGET)/librs_hello.a:
#	cd $(srcdir)/$(RSHELLO_DIR); \
#            cd $(CARGO) rustc --release -- \
#            -C lto --emit dep-info,link=$(abs_builddir)/$@

# $(RSHELLO_TARGET)/librs_hello.a:
#	cd $(srcdir)/$(RSHELLO_DIR) && $(CARGO) build --release

$(RSHELLO_TARGET)/librs_hello.amd64.a: $(RSHELLO_DIR)/src/lib.rs $(RSHELLO_DIR)/src/*.rs
	rustc --edition=2021 --target=x86_64-unknown-linux-gnu --crate-type=staticlib -C panic=abort $< -o $@

$(RSHELLO_TARGET)/librs_hello.x86.a: $(RSHELLO_DIR)/src/lib.rs $(RSHELLO_DIR)/src/*.rs
	rustc --edition=2021 --target=i586-unknown-linux-gnu --crate-type=staticlib -C panic=abort $< -o $@

clean-local:
	cd $(srcdir)/$(RSHELLO_DIR); cargo clean

#----------------------------------------------------------------------------
# krabcake-<platform>
#----------------------------------------------------------------------------

noinst_PROGRAMS  = krabcake-@VGCONF_ARCH_PRI@-@VGCONF_OS@
if VGCONF_HAVE_PLATFORM_SEC
noinst_PROGRAMS += krabcake-@VGCONF_ARCH_SEC@-@VGCONF_OS@
endif

KRABCAKE_SOURCES_COMMON = kc_main.c

# RUST_EXTRA_LD_FLAGS = -ldl -lrt -lpthread -lgcc_s -lc -lm -lrt -lutil
# RUST_EXTRA_LD_FLAGS = -ldl -lrt -lpthread -lc -lm -lrt -lutil
RUST_EXTRA_LD_FLAGS =

krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_SOURCES      = \
	$(KRABCAKE_SOURCES_COMMON)
krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS       = $(LTO_CFLAGS) \
	$(AM_CFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)
krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_PRI_CAPS@)      \
	$(RSHELLO_TARGET)/librs_hello.@VGCONF_ARCH_PRI@.a
krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_PRI_CAPS@)      \
	$(RSHELLO_TARGET)/librs_hello.@VGCONF_ARCH_PRI@.a
krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_PRI_CAPS@)    \
	$(RUST_EXTRA_LD_FLAGS)
krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_PRI@ \
	$(LINK) \
	$(krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_CFLAGS) \
	$(krabcake_@VGCONF_ARCH_PRI@_@VGCONF_OS@_LDFLAGS)

if VGCONF_HAVE_PLATFORM_SEC
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_SOURCES      = \
	$(KRABCAKE_SOURCES_COMMON)
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CPPFLAGS     = \
	$(AM_CPPFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS       = $(LTO_CFLAGS) \
	$(AM_CFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_DEPENDENCIES = \
	$(TOOL_DEPENDENCIES_@VGCONF_PLATFORM_SEC_CAPS@)      \
	$(RSHELLO_TARGET)/librs_hello.@VGCONF_ARCH_SEC@.a
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDADD        = \
	$(TOOL_LDADD_@VGCONF_PLATFORM_SEC_CAPS@)      \
	$(RSHELLO_TARGET)/librs_hello.@VGCONF_ARCH_SEC@.a
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS      = \
	$(TOOL_LDFLAGS_@VGCONF_PLATFORM_SEC_CAPS@)    \
	$(RUST_EXTRA_LD_FLAGS)
krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LINK = \
	$(top_builddir)/coregrind/link_tool_exe_@VGCONF_OS@ \
	@VALT_LOAD_ADDRESS_SEC@ \
	$(LINK) \
	$(krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_CFLAGS) \
	$(krabcake_@VGCONF_ARCH_SEC@_@VGCONF_OS@_LDFLAGS)
endif


