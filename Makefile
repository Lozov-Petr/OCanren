MKDIR ?= mkdir -vp
CP    ?= cp

.NOTPARALLEL :

OB=ocamlbuild -use-ocamlfind -classic-display
ifdef OBV
OB += -verbose 6
endif

SRC=src,src/core,src/std
SRC_TRANSL=src,src/core,src/std,regression,transl

CMA_TARGETS=src/OCanren.cma
CMO_TARGETS=regression/tester.cmo
#TESTER_TARGETS=regression/tester.cmo regression/tester.cmx
BYTE_TARGETS=$(CMA_TARGETS) $(CMO_TARGETS)
NATIVE_TARGETS= $(CMA_TARGETS:.cma=.cmxa) $(CMO_TARGETS:.cmo=.cmx)
TESTS_ENVIRONMENT=./test.sh
JSOO_LIB=jsoo_runner/jsoo_runner.cma

.PHONY: all celan clean clean_tests install uninstall tests test regression promote_all \
	ppx doc \
	only-toplevel toplevel lib tester bundle plugin samples transl

.DEFAULT_GOAL: all

all: bundle samples
bundle: lib plugin
lib:
	$(OB) -r -Is $(SRC) $(BYTE_TARGETS) $(NATIVE_TARGETS)

ppx:
	$(OB) -Is src ppx/ppx_repr_bin.cmxa ppx/pa_ocanren_bin.cmxa \
	  ppx/ppx_ocanren_all.cma ppx/ppx_ocanren_all.cmxa ppx/ppx_ocanren_all.cmxs \
		ppx/ppx_ocanren_all.native

plugin:
	$(OB) camlp5/pa_ocanren.cmo

compile_transl: lib
	$(OB) -Is $(SRC),transl transl/ml2mk_pp.native

transl:
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/bottles_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/bridge_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/einstein_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/GCW_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/hanoi_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/hm_inferencer_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/logic_interpreter_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/lorry_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/scheme_interpreter_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/sudoku4x4_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/samples/unify_run.native

transl_micro:
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/bottles_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/bridge_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/GCW_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/hanoi_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/lorry_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/scheme_interpreter_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/sudoku4x4_run.native
	$(OB) -Is $(SRC_TRANSL) transl/ml2mk_pp.native transl/micro/unify_run.native

celan: clean

clean: clean_tests
	$(RM) -r _build *.log  *.native *.byte *.docdir

clean_transl:
	$(RM) -r _build/transl  *.log  *.native *.byte *.docdir

######################## Tests related stuff  ##########################
REGRES_CASES := 000 002sort 001 004 005 006 007 009 010 011 013 014 015runaway 016sorto 017tabling 018prjc 019tablingCache 020

define TESTRULES
BYTE_TEST_EXECUTABLES += regression/test$(1).byte
NATIVE_TEST_EXECUTABLES += regression/test$(1).native
TEST_MLS += regression/test$(1).ml

.PHONY: test_$(1) test$(1).native compile_tests_native compile_tests_byte \
	promote$(1) promote_test$(1)

test$(1).native: regression/test$(1).native
test$(1).byte:   regression/test$(1).byte

regression/test$(1).byte: regression/test$(1).ml
	$(OB) -Is $(SRC) $$@

regression/test$(1).native: regression/test$(1).ml
	$(OB) -Is $(SRC) $$@

run_tests: test_$(1)
test_$(1):
	@cd regression  && $(TESTS_ENVIRONMENT) ../test$(1).native; \
	if [ $$$$? -ne 0 ] ; then echo "$(1) FAILED"; else echo "$(1) PASSED"; fi

promote_all: promote_$(1)
promote_test$(1): promote_$(1)
promote_$(1):
	./test$(1).native > regression/orig/test$(1).log

endef
$(foreach i,$(REGRES_CASES),$(eval $(call TESTRULES,$(i)) ) )

.PHONY: compile_tests_native compile_tests_byte compile_tests run_tests

compile_tests_native: plugin $(TEST_MLS)
	$(OB) -Is $(SRC) $(NATIVE_TEST_EXECUTABLES)

compile_tests_byte: plugin $(TEST_MLS)
	$(OB) -Is $(SRC) $(BYTE_TEST_EXECUTABLES)

compile_tests: compile_tests_native

clean_tests:
	$(RM) -r _build/regression

promote:

samples: bundle
	$(MAKE) -C samples

tests: plugin lib compile_tests run_tests
regression: tests
test: tests

######################## Samples stuff #######################################
SAMPLES_CASES=tree sorting WGC lorry
.PHONY: compile_samples test_samples
compile_samples:
	$(MAKE) -C samples all
test_samples:
clean: clean_samples
clean_samples:
	$(MAKE) -C samples clean

define SAMPLESRULES
.PHONY: test_sample_$(1)
test_samples: test_sample_$(1)
test_sample_$(1):
	cd samples && $(TESTS_ENVIRONMENT) ./$(1).native; \
	if [ $$$$? -ne 0 ] ; then echo "$(1) FAILED"; else echo "$(1) PASSED"; fi

endef
$(foreach i,$(SAMPLES_CASES),$(eval $(call SAMPLESRULES,$(i)) ) )
######################## Installation related stuff ##########################
INSTALL_TARGETS=META \
	$(wildcard _build/regression/tester.cmi) \
	$(wildcard _build/regression/tester.cmo) \
	$(wildcard _build/regression/tester.cmx) \
	$(wildcard _build/regression/tester.o) \
	$(wildcard _build/src/*.cmi) \
	$(wildcard _build/src/core/*.cmi) \
	$(wildcard _build/src/std/*.cmi) \
	_build/src/OCanren.cmx \
	_build/src/OCanren.cma \
	_build/src/OCanren.cmxa \
	$(wildcard _build/ppx/ppx_ocanren_all.cma) \
	$(wildcard _build/ppx/ppx_ocanren_all.cmxa) \
	$(wildcard _build/ppx/ppx_ocanren_all.cmxs) \
	$(wildcard _build/ppx/ppx_ocanren_all.native) \
	$(wildcard _build/src/OCanren.[oa]) \
	$(wildcard _build/ppxnew/pp_distrib.native) \
	$(wildcard _build/ppxnew/ppx_distrib.a) \
	$(wildcard _build/ppxnew/ppx_distrib.cm[tiaox]) \
	$(wildcard _build/ppxnew/ppx_distrib.cmxa) \
	$(wildcard _build/camlp5/pa_ocanren.cm[oi]) \

BUNDLEDIR=_build/bundle/ocanren

define MAKE_BUNDLE_RULE
$(BUNDLEDIR)/$(notdir $(1)): $(1)
	@cp $(1) $(BUNDLEDIR)
MAKE_BUNDLE_TARGETS += $(BUNDLEDIR)/$(notdir $(1))
endef
$(foreach i,$(INSTALL_TARGETS),$(eval $(call MAKE_BUNDLE_RULE,$(i)) ) )

rmbundledir:
	@$(RM) -r $(BUNDLEDIR)

$(BUNDLEDIR):
	@$(MKDIR) $@

bundle: rmbundledir $(BUNDLEDIR)
	$(MAKE) really_make_bundle

really_make_bundle: $(MAKE_BUNDLE_TARGETS)

install: bundle
	ocamlfind install ocanren $(BUNDLEDIR)/*

uninstall:
	ocamlfind remove ocanren

doc: all bundle compile_tests
	$(OB) OCanren.docdir/index.html -Is src
