##################################################
# About this Makefile
#
# This Makefile depends on srcMakefile.opts
##################################################

EXECUTABLE=test

SRC = main.cpp george.cpp

HEADERS = george.h

#On some compilers, george.cpp takes forever with -O2
EXTRAFLAGS = -O0

LD_LIBS = -l$(PROJECTNAME)

OTHER_DEPENDENCIES = $(TOP)/lib/lib$(PROJECTNAME).$(LIB_SUFFIX)

BASE_DIR = $(TOP)/test

include ../Makefile.local
