##################################################
# About this Makefile
#
# This Makefile depends on Makefile.opts
##################################################

MODULE = search

SRC = \
 clause.cpp \
 search_impl_base.cpp \
 search.cpp \
 search_fast.cpp \
 search_theorem_producer.cpp \
 search_sat.cpp \
 search_simple.cpp \
 variable.cpp \
 circuit.cpp \
 decision_engine.cpp \
 decision_engine_dfs.cpp \
 LFSCObject.cpp \
 LFSCUtilProof.cpp \
 LFSCBoolProof.cpp \
 LFSCConvert.cpp \
 LFSCLraProof.cpp \
 LFSCPrinter.cpp \
 LFSCProof.cpp \
 TReturn.cpp \
 Util.cpp
# decision_engine_caching.cpp \
# decision_engine_mbtf.cpp

HEADERS = search_rules.h search_theorem_producer.h decision_engine.h decision_engine_dfs.h decision_engine_caching.h decision_engine_mbtf.h Util.h TReturn.h Object.h LFSCUtilProof.h LFSCProof.h LFSCPrinter.h LFSCObject.h LFSCLraProof.h LFSCConvert.h LFSCBoolProof.h

LIBRARY=libsearch.a

EXTRAFLAGS=$(DPLL_BASIC)

include ../../Makefile.local
