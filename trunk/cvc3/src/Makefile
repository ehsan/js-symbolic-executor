include ../Makefile.local

###########################################################
#### Developers: add new API files to HEADER_NAMES ########
###########################################################

# Header files that define the exposed API
HEADER_NAMES = \
  assumptions.h \
  c_interface.h \
  c_interface_defs.h \
  cdflags.h \
  cdlist.h \
  cdmap.h \
  cdmap_ordered.h \
  cdo.h \
  circuit.h \
  clause.h \
  cnf.h \
  cnf_manager.h \
  command_line_exception.h \
  command_line_flags.h \
  common_proof_rules.h \
  compat_hash_map.h \
  compat_hash_set.h \
  context.h \
  cvc_util.h \
  debug.h \
  dpllt.h \
  dpllt_basic.h \
  dpllt_minisat.h \
  eval_exception.h \
  exception.h \
  expr.h \
  expr_hash.h \
  expr_manager.h \
  expr_map.h \
  expr_op.h \
  expr_stream.h \
  expr_transform.h \
  expr_value.h \
  formula_value.h \
  fdstream.h \
  hash_fun.h \
  hash_table.h \
  hash_map.h \
  hash_set.h \
  kinds.h \
  lang.h \
  memory_manager.h \
  memory_manager_chunks.h \
  memory_manager_malloc.h \
  memory_manager_context.h \
  notifylist.h \
  os.h \
  parser.h \
  proof.h \
  rational.h \
  parser_exception.h \
  pretty_printer.h \
  queryresult.h \
  sat_api.h \
  search.h \
  search_impl_base.h \
  search_sat.h \
  search_simple.h \
  search_fast.h \
  smartcdo.h \
  smtlib_exception.h \
  sound_exception.h \
  statistics.h \
  theorem.h \
  theorem_manager.h \
  theorem_producer.h \
  theory_arith.h \
  theory_arith_new.h \
  theory_arith_old.h \
  theory_arith3.h \
  theory_array.h \
  theory_bitvector.h \
  theory_core.h \
  theory_datatype.h \
  theory_datatype_lazy.h \
  theory.h \
  theory_quant.h \
  theory_records.h \
  theory_simulate.h \
  theory_uf.h \
  translator.h \
  typecheck_exception.h \
  type.h \
  variable.h \
  vc_cmd.h \
  vc.h \
  vcl.h

MODULES = cvc_util \
	context \
	expr \
	theorem \
	sat \
	theory_core \
	theory_arith \
	theory_array \
	theory_bitvector \
	theory_datatype \
	theory_quant \
	theory_records \
	theory_simulate \
	theory_uf \
	search \
	parser \
	translator \
	vcl \
	c_interface

CVC_EXE = $(TOP)/bin/$(PROJECTNAME)
LIB_BASE=$(LIB_DIR)/$(LIB_BASE_NAME)
LIB_STATIC_NAME=$(LIB_BASE_NAME).$(STATIC_LIB_SUFFIX)
LIB_SHARED_BASE=$(LIB_BASE_NAME).$(SHARED_LIB_SUFFIX)
ifneq ($(CYGWIN),)
    LIB_SHARED_MAJOR=$(LIB_BASE_NAME)-$(subst .,-,$(LIB_MAJOR_VERSION)).$(SHARED_LIB_SUFFIX)
    LIB_SHARED_COMPAT=$(LIB_BASE_NAME)-$(subst .,-,$(LIB_COMPAT_VERSION)).$(SHARED_LIB_SUFFIX)
    LIB_SHARED_FULL=$(LIB_BASE_NAME)-$(subst .,-,$(LIB_VERSION)).$(SHARED_LIB_SUFFIX)
else
ifneq ($(MAC_OSX),)
    LIB_SHARED_MAJOR=$(LIB_BASE_NAME).$(LIB_MAJOR_VERSION).$(SHARED_LIB_SUFFIX)
    LIB_SHARED_COMPAT=$(LIB_BASE_NAME).$(LIB_COMPAT_VERSION).$(SHARED_LIB_SUFFIX)
    LIB_SHARED_FULL=$(LIB_BASE_NAME).$(LIB_VERSION).$(SHARED_LIB_SUFFIX)
else
    LIB_SHARED_MAJOR=$(LIB_SHARED_BASE).$(LIB_MAJOR_VERSION)
    LIB_SHARED_COMPAT=$(LIB_SHARED_BASE).$(LIB_COMPAT_VERSION)
    LIB_SHARED_FULL=$(LIB_SHARED_BASE).$(LIB_VERSION)
endif
endif
# LIB_SONAME=$(LIB_SHARED_FULL).$(SONAME)
LIB_STATIC=$(LIB_DIR)/$(LIB_STATIC_NAME)
LIB_SHARED=$(LIB_DIR)/$(LIB_SHARED_FULL)
LIBS = $(patsubst %, $(LIB_DIR)/lib%.$(STATIC_LIB_SUFFIX), $(MODULES))
ifeq ($(STATIC),1)
  LIB_TO_BUILD = $(LIB_STATIC)
else
  LIB_TO_BUILD = $(LIB_SHARED)
endif
# Using notdirx, in case path has spaces
CVC_LIB_NAME = $(call notdirx, $(LIB_TO_BUILD))
CVC_LIB_DIR = $(TOP)/lib
CVC_LIB = $(CVC_LIB_DIR)/$(CVC_LIB_NAME)

.PHONY: all build depend clean spotty install print_src distclean

all: build

# List all module subdirs here
build:
	cd util && $(MAKE) $(TARGET)
	cd context && $(MAKE) $(TARGET)
	cd expr && $(MAKE) $(TARGET)
	cd theorem && $(MAKE) $(TARGET)
	cd sat && $(MAKE) $(TARGET)
	cd theory_core && $(MAKE) $(TARGET)
	cd theory_arith && $(MAKE) $(TARGET)
	cd theory_array && $(MAKE) $(TARGET)
	cd theory_bitvector && $(MAKE) $(TARGET)
	cd theory_datatype && $(MAKE) $(TARGET)
	cd theory_quant && $(MAKE) $(TARGET)
	cd theory_records && $(MAKE) $(TARGET)
	cd theory_simulate && $(MAKE) $(TARGET)
	cd theory_uf && $(MAKE) $(TARGET)
	cd search && $(MAKE) $(TARGET)
	cd parser && $(MAKE) $(TARGET)
	cd translator && $(MAKE) $(TARGET)
	cd vcl && $(MAKE) $(TARGET)
	cd c_interface && $(MAKE) $(TARGET)
ifndef TARGET
	@rm -rf $(CVC_LIB)
	$(MAKE) $(CVC_LIB)
endif
	cd cvc3 && $(MAKE) $(TARGET) VERSION=$(VERSION)

# No need to change anything below this point when adding headers/modules

UNPACKTMPDIR=$(TOP)/unpack_tmp


$(LIB_STATIC): $(LIBS)
	-rm -rf $(UNPACKTMPDIR)
	$(TOP)/bin/unpack $(UNPACKTMPDIR) $(LIBS) > UNPACKED
	cat UNPACKED | xargs $(AR) ruvs '$@.$(LIB_VERSION)'
	rm -rf $(UNPACKTMPDIR) UNPACKED
	@echo Linking $(LIB_STATIC_NAME) to $@
	ln -sf $(LIB_STATIC_NAME).$(LIB_VERSION) '$@'

$(LIB_SHARED): $(LIBS)
	@echo Building shared library $(LIB_SHARED)
	-rm -rf $(UNPACKTMPDIR)
	$(TOP)/bin/unpack $(UNPACKTMPDIR) $(LIBS) > UNPACKED
ifneq ($(MAC_OSX),)
	cat UNPACKED | xargs $(CXX) $(SHARED) $(CXXFLAGS) $(LDFLAGS) \
    -install_name $(libdir)/$(LIB_SHARED_MAJOR) \
    -compatibility_version $(LIB_COMPAT_VERSION) \
    -current_version $(LIB_VERSION) \
    -o '$(LIB_SHARED)' `` $(LD_LIBS)
else
ifneq ($(CYGWIN),)
	eval $(CXX) $(SHARED) $(CXXFLAGS) $(LDFLAGS) \
    -Wl,-soname,$(LIB_SHARED_MAJOR) -o \''$(LIB_SHARED)'\' `cat UNPACKED` $(LD_LIBS)
else
	cat UNPACKED | xargs $(CXX) $(SHARED) $(CXXFLAGS) $(LDFLAGS) \
    -Wl,-soname,$(LIB_SHARED_MAJOR) -o '$(LIB_SHARED)' `` $(LD_LIBS)
	$(LDCONFIG) -nv $(LIB_DIR)
endif
endif
	ln -sf $(LIB_SHARED_FULL) $(LIB_DIR)/$(LIB_SHARED_COMPAT)
	ln -sf $(LIB_SHARED_FULL) $(LIB_DIR)/$(LIB_SHARED_MAJOR)
	ln -sf $(LIB_SHARED_FULL) $(LIB_DIR)/$(LIB_SHARED_BASE)
	@rm -rf $(UNPACKTMPDIR) UNPACKED

ifeq ($(STATIC),1)
$(CVC_LIB): $(LIB_STATIC)
	ln -sf $(LIB_STATIC).$(LIB_VERSION) '$(call dirx,$@)/$(LIB_STATIC_NAME).$(LIB_VERSION)'
	ln -sf $(LIB_STATIC_NAME).$(LIB_VERSION) '$@'
else
$(CVC_LIB): $(LIB_SHARED)
	ln -sf $(LIB_SHARED) '$(call dirx,$@)/$(LIB_SHARED_FULL)'
ifeq ($(MAC_OSX),)
ifeq ($(CYGWIN),)
	$(LDCONFIG) -nv '$(call dirx,$@)'
endif
endif
	ln -sf $(LIB_SHARED_FULL) '$(call dirx,$@)/$(LIB_SHARED_COMPAT)'
	ln -sf $(LIB_SHARED_FULL) '$(call dirx,$@)/$(LIB_SHARED_MAJOR)'
	ln -sf $(LIB_SHARED_FULL) '$(call dirx,$@)/$(LIB_SHARED_BASE)'
endif

# Standard make targets

depend:
	$(MAKE) build TARGET=depend

clean:
	$(MAKE) build TARGET=clean
	rm -f $(LIB_STATIC)* $(LIB_SHARED)* $(CVC_LIB)

distclean:
	$(MAKE) build TARGET=distclean
	rm -rf cvc3.pc

spotty:
	$(MAKE) build TARGET=spotty
	rm -f $(LIB_STATIC) $(LIB_SHARED) $(CVC_LIB)

HEADERS = $(patsubst %, $(TOP)/src/include/%, $(HEADER_NAMES))

install: $(HEADERS)
	$(MAKE) build TARGET=
	mkdir -p $(incdir)
	$(INSTALL) $(INSTALL_FLAGS) -m 644 $(HEADERS) $(incdir)
	mkdir -p $(libdir)
ifeq ($(STATIC),1)
	$(INSTALL) $(INSTALL_FLAGS) -m 644 $(CVC_LIB_DIR)/$(CVC_LIB_NAME).$(LIB_VERSION) $(libdir)
	ln -sf $(CVC_LIB_NAME).$(LIB_VERSION) $(libdir)/$(call notdirx,$(CVC_LIB))
else
	$(INSTALL) $(INSTALL_FLAGS) -m 644 $(CVC_LIB) $(libdir)
ifeq ($(MAC_OSX),)
ifeq ($(CYGWIN),)
	$(LDCONFIG) -nv $(libdir)
endif
endif
	ln -sf $(CVC_LIB_NAME) $(libdir)/$(LIB_SHARED_COMPAT) 
	ln -sf $(CVC_LIB_NAME) $(libdir)/$(LIB_SHARED_MAJOR)
	ln -sf $(CVC_LIB_NAME) $(libdir)/$(LIB_SHARED_BASE)
endif
	mkdir -p $(bindir)
	$(INSTALL) $(INSTALL_FLAGS) -m 755 $(CVC_EXE) $(bindir)
	mkdir -p $(libdir)/pkgconfig
	$(INSTALL) $(INSTALL_FLAGS) -m 644 cvc3.pc $(libdir)/pkgconfig

ifndef FILELIST
FILELIST = /dev/null
endif

print_src:
	$(MAKE) build TARGET=print_src
	echo $(patsubst %, src/include/%, $(HEADER_NAMES)) >> $(FILELIST)
