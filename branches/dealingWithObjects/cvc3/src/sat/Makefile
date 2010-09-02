##################################################
# About this Makefile
#
# This Makefile depends on Makefile.opts
##################################################

MODULE = sat

SRC = $(EXTRA_SAT_CPP) \
      cnf.cpp \
      cnf_manager.cpp \
      cnf_theorem_producer.cpp \
      dpllt_basic.cpp \
      sat_api.cpp \
      dpllt_minisat.cpp \
      minisat_types.cpp \
      minisat_derivation.cpp \
      minisat_solver.cpp


HEADERS = $(EXTRA_SAT_HEADERS) \
          cnf_rules.h \
          cnf_theorem_producer.h \
	  sat_proof.h \
          minisat_global.h \
          minisat_heap.h \
          minisat_types.h \
          minisat_varorder.h \
          minisat_derivation.h \
          minisat_solver.h

LIBRARY=libsat.a

EXTRAFLAGS=$(DPLL_BASIC)

include ../../Makefile.local
