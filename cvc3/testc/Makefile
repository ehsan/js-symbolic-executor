##################################################
# About this Makefile
#
# This Makefile depends on srcMakefile.opts
##################################################

EXECUTABLE = testc

LD_LIBS = -l$(PROJECTNAME)

BASE_DIR = $(TOP)/testc

OTHER_OBJ = $(OBJ_DIR)/main.o
OTHER_DEPENDENCIES = $(TOP)/lib/lib$(PROJECTNAME).$(LIB_SUFFIX)
MY_DEPEND = 1

TRANSIENT = $(OBJ_DIR)/main.o

include ../Makefile.local

$(OBJ_DIR)/main.o : main.c
	@mkdir -p $(OBJ_DIR)
	gcc $(CXXFLAGS) -g -I../src/include -o $(OBJ_DIR)/main.o -c main.c

depend: main.c
	@mkdir -p $(OBJ_DIR)
	@-rm -f $(MAKEFILE_DEPS) $(MAKEFILE_DEPS_TMP) $(MAKEFILE_DEPS_TMP2)
	@echo '# Dependencies for C files' >> $(MAKEFILE_DEPS_TMP)
	@echo >> $(MAKEFILE_DEPS_TMP)
	@echo "Making dependencies for $(SRC)"
	gcc -M -g -I../src/include main.c >> $(MAKEFILE_DEPS_TMP)
	@echo >> $(MAKEFILE_DEPS_TMP)
	@sed -e '/^.*:/ s#^#$(OBJ_DIR)/#' < $(MAKEFILE_DEPS_TMP) > $(MAKEFILE_DEPS_TMP2)
	@cat $(MAKEFILE_DEPS_TMP2) > $(MAKEFILE_DEPS)
	@rm -f $(MAKEFILE_DEPS_TMP) $(MAKEFILE_DEPS_TMP2)
