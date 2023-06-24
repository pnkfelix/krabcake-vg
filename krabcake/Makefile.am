include $(top_srcdir)/Makefile.tool.am

EXTRA_DIST = docs/kc-manual.xml

RSHELLO_DIR = rs_hello
# RSHELLO_TARGET = $(RSHELLO_DIR)/target/release
RSHELLO_TARGET = $(RSHELLO_DIR)/target/debug
RSHELLO_TARGET_DEBUG64 = $(RSHELLO_DIR)/target/debug64
RSHELLO_TARGET_DEBUG32 = $(RSHELLO_DIR)/target/debug32

#$(RSHELLO_TARGET)/librs_hello.a:
#	cd $(srcdir)/$(RSHELLO_DIR); \
#            cd $(CARGO) rustup run nightly rustc --release -- \
#            -C lto --emit dep-info,link=$(abs_builddir)/$@

# $(RSHELLO_TARGET)/librs_hello.a:
#	cd $(srcdir)/$(RSHELLO_DIR) && $(CARGO) build --release

$(RSHELLO_TARGET)/librs_hello.amd64.a: $(RSHELLO_TARGET_DEBUG64)/librs_hello.amd64.a
	mkdir -p $(dir $@)
	cp $< $@

$(RSHELLO_TARGET)/librs_hello.x86.a: $(RSHELLO_TARGET_DEBUG32)/librs_hello.x86.a
	mkdir -p $(dir $@)
	cp $< $@


$(RSHELLO_TARGET)/nightly_installed:
#	[[ -n $$CI ]] && if ! rustup toolchain list | grep -q nightly ; then rustup toolchain install nightly; fi
	mkdir -p $(dir $@)
	if ! rustup toolchain list | grep -q nightly ; then rustup toolchain install nightly; fi
	touch $@

$(RSHELLO_TARGET_DEBUG64)/librs_hello.amd64.a: $(RSHELLO_DIR)/src/lib.rs $(RSHELLO_DIR)/src/*.rs $(RSHELLO_TARGET)/nightly_installed
	mkdir -p $(dir $@)
	rustup target add x86_64-unknown-linux-gnu
# When `-C` flag to cargo is stable, use it here instead of manually chdir'ing
	cd $(RSHELLO_DIR) && cargo build --target=x86_64-unknown-linux-gnu
	cp $(RSHELLO_DIR)/target/x86_64-unknown-linux-gnu/debug/librs_hello.a $@

$(RSHELLO_TARGET_DEBUG32)/librs_hello.x86.a: $(RSHELLO_DIR)/src/lib.rs $(RSHELLO_DIR)/src/*.rs $(RSHELLO_TARGET)/nightly_installed
	mkdir -p $(dir $@)
	rustup target add i586-unknown-linux-gnu
# When `-C` flag to cargo is stable, use it here instead of manually chdir'ing
	cd $(RSHELLO_DIR) && cargo build --target=i586-unknown-linux-gnu
	cp $(RSHELLO_DIR)/target/i586-unknown-linux-gnu/debug/librs_hello.a $@

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


