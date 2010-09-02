# Makefile for creating the java wrapper around the cvc library
# as well as a java command line client

include ../Makefile.local

### Variables

# package name
PACKAGE = cvc3

# directories
# source files: java, cpp
SOURCE_PATH = src
# header files: h
HEADER_PATH = include
# object files: class, o
OBJ_PATH    = obj
# library files: so, jar
REL_LIB_PATH  = java/lib
LIB_PATH      = $(TOP)/$(REL_LIB_PATH)
REL_ARCH_LIB_PATH = $(REL_LIB_PATH)/$(PLATFORM_WITH_OPTIONS)
ARCH_LIB_PATH = $(TOP)/$(REL_ARCH_LIB_PATH)

CPPFLAGS += $(JAVA_INCLUDES)

ifneq ($(CYGWIN),)
CPPFLAGS += '-D__int64=long long'
endif

ifeq ($(OPTIMIZED), 1)
CXXFLAGS += -O2
else
CXXFLAGS += -D_CVC3_DEBUG_MODE -g -O0
endif


# Java compiler flags
# - source 1.4 is needed for Escjava
# - Xlint may be compiler dependent
JFLAGS += -Xlint -g -source 1.4

# source files
# java files of the library wrapper
LIB_FILES = \
	JniUtils \
	Cvc3Exception TypecheckException SoundException EvalException \
	CLException ParserException SmtlibException DebugException \
	Embedded EmbeddedManager \
	InputLanguage QueryResult SatResult FormulaValue \
	Expr ExprMut ExprManager ExprManagerMut \
	Type TypeMut Op OpMut Rational RationalMut \
	Theorem TheoremMut Proof ProofMut Context ContextMut \
	Flag Flags FlagsMut \
	Statistics StatisticsMut ValidityChecker
# java files of the test program
TEST_FILES = Test
# java files of the stand alone program
PROG_FILES = TimeoutHandler Cvc3
# all java files, library and stand alone
JAVA_FILES = $(LIB_FILES) $(TEST_FILES) $(PROG_FILES)
# jni files of the library wrapper
JNI_FILES = \
	EmbeddedManager \
	Expr ExprMut ExprManager \
	Type TypeMut Op OpMut Rational RationalMut \
	Theorem TheoremMut Proof ProofMut Context ContextMut \
	Flag Flags FlagsMut \
	Statistics StatisticsMut ValidityChecker
# stub files
IMPL_FILES = $(addsuffix _impl.cpp,$(JNI_FILES))
# generated files
JNI_CPP_FILES = $(patsubst %,%.cpp,$(JNI_FILES))
# non-generated files
SRC_CPP_FILES = JniUtils.cpp 
# all cpp files (to compile)
CPP_FILES = $(SRC_CPP_FILES) $(JNI_CPP_FILES)

HEADER_FILES = JniUtils.h
PYTHON_FILES = run_all.py run_tests.py create_impl.py
MANIFEST_FILES = Cvc3_manifest Test_manifest

DIST_FILES = \
Makefile \
README \
$(addprefix $(SOURCE_PATH)/$(PACKAGE)/, \
  $(addsuffix .java, $(JAVA_FILES)) \
  $(IMPL_FILES) $(SRC_CPP_FILES)) \
$(addprefix $(HEADER_PATH)/$(PACKAGE)/, $(HEADER_FILES)) \
$(PYTHON_FILES) \
$(MANIFEST_FILES)


# target files
# java library files compiled to class files 
LIB_CLASS_FILES = $(patsubst %,%.class,$(LIB_FILES))
# test files compiled to class files 
TEST_CLASS_FILES = $(patsubst %,%.class,$(TEST_FILES))
# cvc3 standalone files compiled to class files 
PROG_CLASS_FILES = $(patsubst %,%.class,$(PROG_FILES))
# all compiled java files, library and stand alone
CLASS_FILES = $(LIB_CLASS_FILES) $(TEST_CLASS_FILES) $(PROG_CLASS_FILES)
# jni header files created from the library class files
H_FILES = $(patsubst %,%.h,$(JNI_FILES))
# precompiled header files
GCH_FILES = $(patsubst %.h,%.h.gch,$(H_FILES)) JniUtils.h.gch
# cpp files compiled to object files
JNI_O_FILES = $(patsubst %.cpp,%.o,$(JNI_CPP_FILES))
O_FILES = $(patsubst %.cpp,%.o,$(CPP_FILES))

# library files
# cpp library
LIB_PREFIX = lib
LIB_JNI_NAME = $(LIB_PREFIX)cvc3jni
ifneq ($(CYGWIN),)
  LIB_JNI_BASE   = $(LIB_JNI_NAME).$(SHARED_LIB_SUFFIX)
  LIB_JNI   = $(LIB_JNI_NAME)-$(subst .,-,$(LIB_VERSION)).$(SHARED_LIB_SUFFIX)
  LIB_JNI_COMPAT  = $(LIB_JNI_NAME)-$(subst .,-,$(LIB_COMPAT_VERSION)).$(SHARED_LIB_SUFFIX)
  LIB_JNI_MAJOR  = $(LIB_JNI_NAME)-$(subst .,-,$(LIB_MAJOR_VERSION)).$(SHARED_LIB_SUFFIX)
else
LIB_JNI_BASE   = $(LIB_JNI_NAME).$(SHARED_LIB_SUFFIX)
ifneq ($(MAC_OSX),)
  LIB_JNI   = $(LIB_JNI_NAME).$(LIB_VERSION).$(SHARED_LIB_SUFFIX)
  LIB_JNI_COMPAT  = $(LIB_JNI_NAME).$(LIB_COMPAT_VERSION).$(SHARED_LIB_SUFFIX)
  LIB_JNI_MAJOR  = $(LIB_JNI_NAME).$(LIB_MAJOR_VERSION).$(SHARED_LIB_SUFFIX)
else
  LIB_JNI   = $(LIB_JNI_BASE).$(LIB_VERSION)
  LIB_JNI_COMPAT  = $(LIB_JNI_BASE).$(LIB_COMPAT_VERSION)
  LIB_JNI_MAJOR  = $(LIB_JNI_BASE).$(LIB_MAJOR_VERSION)
endif
endif
# java library
LIB_CVC3  = libcvc3-$(LIB_VERSION).jar
# test alone
PROG_TEST = cvc3test.jar
# java stand alone
PROG_CVC3 = cvc3.jar


### virtual file lookup paths
#VPATH = src/cvc3/
vpath %.java  $(SOURCE_PATH)/$(PACKAGE)
vpath %.cpp   $(SOURCE_PATH)/$(PACKAGE)
vpath %.h     $(HEADER_PATH)/$(PACKAGE)
vpath %.h.gch $(HEADER_PATH)/$(PACKAGE)
vpath %.class $(OBJ_PATH)/$(PACKAGE)
vpath %.o     $(OBJ_PATH)/$(PACKAGE)


.PHONY: all classes headers objects libs libjni libcvc3 testlib cvc3 test regress print_src clean distclean %.d

### rules

all: classes headers objects libs
libs: libjni libcvc3 testlib cvc3

%.d:
	if [ ! -d $* ]; then mkdir -p $*; fi

$(OBJ_PATH): $(OBJ_PATH).d
$(LIB_PATH): $(LIB_PATH).d
$(ARCH_LIB_PATH): $(ARCH_LIB_PATH).d

# compile each java file
classes: $(OBJ_PATH) $(CLASS_FILES) 
$(CLASS_FILES): %.class: %.java $(OBJ_PATH)
	$(JAVAC) $(JFLAGS) -sourcepath $(SOURCE_PATH) \
	-d $(OBJ_PATH) $(SOURCE_PATH)/$(PACKAGE)/$*.java

# create a jni header file for each library class file
#headers: $(H_FILES) $(GCH_FILES)
headers: $(OBJ_PATH) $(H_FILES)
$(H_FILES): %.h: %.class $(OBJ_PATH)
	$(JAVAH) -jni -force -classpath $(OBJ_PATH) \
	-o $(HEADER_PATH)/$(PACKAGE)/$*.h $(PACKAGE).$*

# precompile headers
$(GCH_FILES): %.h.gch: %.h
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) \
	-I ../src/include -I $(HEADER_PATH)/$(PACKAGE)/ \
	-o $(HEADER_PATH)/$(PACKAGE)/$*.h.gch $(HEADER_PATH)/$(PACKAGE)/$*.h

# compile each cpp file
$(JNI_CPP_FILES): %.cpp: %_impl.cpp %.h JniUtils.h
	$(PYTHON) ./create_impl.py \
	$(HEADER_PATH)/$(PACKAGE)/$*.h \
	$(SOURCE_PATH)/$(PACKAGE)/$*_impl.cpp \
	$(SOURCE_PATH)/$(PACKAGE)/$*.cpp

objects: $(OBJ_PATH) $(O_FILES) 
$(O_FILES): %.o: %.cpp %.h $(OBJ_PATH)
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -c \
	-I ../src/include -I $(HEADER_PATH)/$(PACKAGE)/ \
	-o $(OBJ_PATH)/$(PACKAGE)/$*.o $(SOURCE_PATH)/$(PACKAGE)/$*.cpp

# create the cpp jni wrapper library

libjni: $(ARCH_LIB_PATH)/$(LIB_JNI) $(LIB_PATH)/$(LIB_JNI)
$(ARCH_LIB_PATH)/$(LIB_JNI): $(O_FILES) $(ARCH_LIB_PATH)
ifneq ($(MAC_OSX),)
	$(CXX) $(SHARED) $(CXXFLAGS) $(LDFLAGS) \
      -install_name $(libdir)/$(LIB_JNI_MAJOR) \
      -compatibility_version $(LIB_COMPAT_VERSION) \
      -current_version $(LIB_VERSION) \
      -L../lib $(OBJ_PATH)/$(PACKAGE)/*.o \
      -o '$(ARCH_LIB_PATH)/$(LIB_JNI)' `` -lcvc3 $(LD_LIBS)
else
	$(CXX) $(SHARED) $(CXXFLAGS) $(LDFLAGS) \
      -Wl,-soname,$(LIB_JNI_COMPAT) \
      -L ../lib $(OBJ_PATH)/$(PACKAGE)/*.o \
      -o $(ARCH_LIB_PATH)/$(LIB_JNI) -lcvc3 $(LD_LIBS)
ifeq ($(CYGWIN),)
	$(LDCONFIG) -nv $(ARCH_LIB_PATH)
endif
endif
	ln -sf $(LIB_JNI) $(ARCH_LIB_PATH)/$(LIB_JNI_COMPAT)
	ln -sf $(LIB_JNI) $(ARCH_LIB_PATH)/$(LIB_JNI_MAJOR)
	ln -sf $(LIB_JNI) $(ARCH_LIB_PATH)/$(LIB_JNI_BASE)

#	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -shared \

#$(LIB_PATH)/$(LIB_JNI): $(O_FILES)
#	ar ruvs $(LIB_PATH)/libcvc3jni.a $(OBJ_PATH)/$(PACKAGE)/*.o
#	$(CXX) $(CXXFLAGS) -shared -Wl,-soname,$(LIB_JNI) \
#	-L ../lib -lc -lcvc3 -lgmp \
#	$(LIB_PATH)/libcvc3jni.a \
#	-o $(LIB_PATH)/$(LIB_JNI)

#ar ruvs /media/data/ESCJava/CVC3/cvc3/lib/linux-i686-debug/libvcl.a  /media/data/ESCJava/CVC3/cvc3/obj/vcl/linux-i686-debug/vcl.o  /media/data/ESCJava/CVC3/cvc3/obj/vcl/linux-i686-debug/vc_cmd.o

$(LIB_PATH)/$(LIB_JNI): $(ARCH_LIB_PATH)/$(LIB_JNI)
	ln -sf $< $@
# [chris] ldconfig seems to just delete the .so's!
# $(LDCONFIG) -nv '$(call dirx,$@)'
	ln -sf $(LIB_JNI) '$(call dirx,$@)/$(LIB_JNI_COMPAT)'
	ln -sf $(LIB_JNI) '$(call dirx,$@)/$(LIB_JNI_MAJOR)'
	ln -sf $(LIB_JNI) '$(call dirx,$@)/$(LIB_JNI_BASE)'

# create the java wrapper library
libcvc3: $(LIB_PATH) $(LIB_PATH)/$(LIB_CVC3)
$(LIB_PATH)/$(LIB_CVC3): $(LIB_CLASS_FILES)
	cd $(OBJ_PATH) && $(JAR) cf ../../$(REL_LIB_PATH)/$(LIB_CVC3) $(PACKAGE)/*.class


install: $(ARCH_LIB_PATH)/$(LIB_JNI) $(LIB_PATH)/$(LIB_CVC3)
	mkdir -p $(javadir)
	$(INSTALL) $(INSTALL_FLAGS) -m 644 $(LIB_PATH)/$(LIB_CVC3) $(javadir)
	mkdir -p $(libdir)
	$(INSTALL) $(INSTALL_FLAGS) -m 644 $(ARCH_LIB_PATH)/$(LIB_JNI) $(libdir)
	ln -sf $(LIB_JNI) $(libdir)/$(LIB_JNI_MAJOR)
	ln -sf $(LIB_JNI) $(libdir)/$(LIB_JNI_COMPAT)
	ln -sf $(LIB_JNI) $(libdir)/$(LIB_JNI_BASE)
ifeq ($(MAC_OSX),)
ifeq ($(CYGWIN),)
	$(LDCONFIG) -nv $(libdir)
endif
endif
#	chmod 644 $(libdir)/$(LIB_JNI)


# create the java stand alone program
cvc3: $(LIB_PATH) $(LIB_PATH)/$(PROG_CVC3)
$(LIB_PATH)/$(PROG_CVC3): $(PROG_CLASS_FILES)
	$(JAR) -cmf Cvc3_manifest ../$(REL_LIB_PATH)/$(PROG_CVC3)
	@for i in $(PROG_CLASS_FILES); do \
	  echo $(JAR) -uf ../$(REL_LIB_PATH)/$(PROG_CVC3) -C $(OBJ_PATH) $(PACKAGE)/$$i; \
	  $(JAR) -uf ../$(REL_LIB_PATH)/$(PROG_CVC3) -C $(OBJ_PATH) $(PACKAGE)/$$i; \
	done

# create the test stand alone program
testlib: $(LIB_PATH) $(LIB_PATH)/$(PROG_TEST)

test: testlib
	$(JAVA) $(JREFLAGS) -Djava.library.path=../$(REL_ARCH_LIB_PATH) -ea -jar ../$(REL_LIB_PATH)/$(PROG_TEST)

$(LIB_PATH)/$(PROG_TEST): $(TEST_CLASS_FILES)
	echo -e "Main-Class: cvc3/Test\nClass-Path: $(LIB_CVC3)\n" > Test_manifest
	$(JAR) -cmf Test_manifest ../$(REL_LIB_PATH)/$(PROG_TEST)
	@for i in $(TEST_CLASS_FILES); do \
	  echo $(JAR) -uf ../$(REL_LIB_PATH)/$(PROG_TEST) -C $(OBJ_PATH) $(PACKAGE)/$$i; \
	  $(JAR) -uf ../$(REL_LIB_PATH)/$(PROG_TEST) -C $(OBJ_PATH) $(PACKAGE)/$$i; \
	done

regress: cvc3
	$(PYTHON) ./run_tests.py \
	-vc '$(JAVA) $(JREFLAGS) -Djava.library.path=../$(REL_LIB_PATH) -ea -Xss100M -jar ../$(REL_LIB_PATH)/$(PROG_CVC3)' \
	-t 15 -m 500 -l 4 ../benchmarks


ifndef FILELIST
FILELIST = /dev/null
endif

print_src:
	echo $(addprefix java/, $(DIST_FILES)) >> $(FILELIST)
#	echo $(patsubst %, src/include/%, $(HEADER_NAMES)) >> $(FILELIST)



# clean up

clean: $(OBJ_PATH)
	rm -f $(addprefix $(SOURCE_PATH)/$(PACKAGE)/, $(JNI_CPP_FILES))
	rm -fr $(OBJ_PATH)/$(PACKAGE)/*
	rm -fr $(LIB_PATH)/*
	rm -f $(addprefix $(HEADER_PATH)/$(PACKAGE)/, $(H_FILES) $(GCH_FILES))

distclean: clean
