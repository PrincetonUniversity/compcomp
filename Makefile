#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU General Public License as published by  #
#  the Free Software Foundation, either version 2 of the License, or  #
#  (at your option) any later version.  This file is also distributed #
#  under the terms of the INRIA Non-Commercial License Agreement.     #
#                                                                     #
#######################################################################

include Makefile.config

DIRS=lib common $(ARCH)/$(VARIANT) $(ARCH) backend cfrontend core linking driver \
  flocq/Core flocq/Prop flocq/Calc flocq/Appli exportclight

RECDIRS=lib common backend cfrontend core linking driver flocq exportclight

# NOTE:
# To use a nonstandard Ssreflect+MathComp installation, 
# change the following two configuration variables to 
# point to the base directories of your Ssreflect and 
# MathComp installations.

# If SSREFLECT is set to "" (default), no additional 
# include directives will be passed to coqc.

SSREFLECT=""
MATHCOMP=""

COQINCLUDES0=$(foreach d, $(RECDIRS), -R $(d) -as compcert.$(d)) \
  -I $(ARCH)/$(VARIANT) -as compcert.$(ARCH).$(VARIANT) \
  -I $(ARCH) -as compcert.$(ARCH)

ifeq ($(SSREFLECT),"")
  COQINCLUDES=$(COQINCLUDES0)
else 
  COQINCLUDES=$(COQINCLUDES0) \
  -I $(SSREFLECT)/src -R $(SSREFLECT)/theories -as Ssreflect \
  -R $(MATHCOMP)/theories -as MathComp
endif

CAMLINCLUDES=$(patsubst %,-I %, $(DIRS)) -I extraction -I cparser

COQC=coqc -q $(COQINCLUDES)
COQDEP=coqdep $(COQINCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(COQINCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(COQINCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -j 2 \
  -no-hygiene \
  -no-links \
  $(CAMLINCLUDES)
OCB_OPTIONS_CHECKLINK=\
  $(OCB_OPTIONS) \
  -I checklink \
  -use-ocamlfind
OCB_OPTIONS_CLIGHTGEN=\
  $(OCB_OPTIONS) \
  -I exportclight

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

FLOCQ=\
  Fcore_Raux.v Fcore_Zaux.v Fcore_defs.v Fcore_digits.v                     \
  Fcore_float_prop.v Fcore_FIX.v Fcore_FLT.v Fcore_FLX.v                    \
  Fcore_FTZ.v Fcore_generic_fmt.v Fcore_rnd.v Fcore_rnd_ne.v                \
  Fcore_ulp.v Fcore.v                                                       \
  Fcalc_bracket.v Fcalc_digits.v Fcalc_div.v Fcalc_ops.v                    \
  Fcalc_round.v Fcalc_sqrt.v                                                \
  Fprop_div_sqrt_error.v Fprop_mult_error.v Fprop_plus_error.v              \
  Fprop_relative.v Fprop_Sterbenz.v                                         \
  Fappli_rnd_odd.v Fappli_IEEE.v Fappli_IEEE_bits.v

# General-purpose libraries (in lib/)

LIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Nan.v Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v \
  Values.v Smallstep.v Behaviors.v Switch.v Determinism.v Subtyping.v

# Back-end modules (in backend/, $(ARCH)/, $(ARCH)/$(VARIANT))

BACKEND=\
  Cminor.v Cminor_coop.v Cminor_eff.v \
  Op.v OpEFF.v \
  CminorSel.v CminorSel_coop.v CminorSel_eff.v \
  SelectOp.v SelectDiv.v SelectLong.v Selection.v \
  I64Helpers.v BuiltinEffects.v SelectionNEW.v SelectLongNEW.v \
  SelectOpproof.v SelectDivproof.v SelectLongproof.v SelectLongproofEFF.v \
  Selectionproof.v SelectionproofEFF.v \
  Registers.v RTL.v RTL_coop.v RTL_eff.v \
  RTLgen.v RTLgenspec.v RTLgenproof.v RTLgenproofEFF.v \
  RTL2RTL_proofEFF.v \
  Tailcall.v Tailcallproof.v  TailcallproofEFF.v \
  Inlining.v Inliningspec.v Inliningproof.v \
  Renumber.v Renumberproof.v RenumberproofEFF.v \
  RTLtyping.v \
  Kildall.v Liveness.v \
  ConstpropOp.v Constprop.v ConstpropOpproof.v Constpropproof.v \
  CombineOp.v CSE.v CombineOpproof.v CSEproof.v \
  Machregs.v Locations.v Conventions1.v Conventions.v \
  LTL.v LTL_coop.v LTL_eff.v \
  Allocation.v Allocproof.v AllocproofEFF.v \
  Tunneling.v Tunnelingproof.v  TunnelingproofEFF.v \
  Linear.v Linear_coop.v Linear_eff.v Lineartyping.v \
  Linearize.v Linearizeproof.v LinearizeproofEFF.v \
  CleanupLabels.v CleanupLabelsproof.v CleanupLabelsproofEFF.v \
  load_frame.v Mach.v Mach_coop.v Mach_eff.v \
  Bounds.v Stacklayout.v Stacking.v Stackingproof.v StackingproofEFF.v \
  Asm.v Asmgen.v Asmgenproof0.v Asmgenproof1.v Asmgenproof.v \
  AsmEFF.v AsmgenEFF.v Asm_coop.v Asm_eff.v \
  Asmgenproof0EFF.v Asmgenproof1EFF.v AsmgenproofEFF.v Asm_nucular.v \

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Cstrategy.v Cexec.v \
  Initializers.v Initializersproof.v \
  SimplExpr.v SimplExprspec.v SimplExprproof.v \
  Clight.v Clight_coop.v Clight_eff.v ClightBigstep.v \
  SimplLocals.v SimplLocalsproof.v SimplLocalsproofEFF.v \
  Cshmgen.v Cshmgenproof.v CshmgenproofEFF.v \
  Csharpminor.v Csharpminor_coop.v Csharpminor_eff.v \
  Cminorgen.v Cminorgenproof.v \
  CminorgenproofRestructured.v CminorgenproofSIM.v CminorgenproofEFF.v

# Core separate compilation modules (in core/)

CORE=Extensionality.v \
  base.v eq_dec.v Address.v \
  Coqlib2.v \
  mem_lemmas.v mem_wd.v \
  core_semantics.v core_semantics_lemmas.v \
  extspec.v step_lemmas.v \
  StructuredInjections.v \
  effect_semantics.v reach.v effect_simulations.v \
  rg_lemmas.v \
  effect_simulations_lemmas.v effect_properties.v effect_corediagram_trans.v \
  effect_simulations_trans.v \
  FiniteMaps.v mem_interpolation_defs.v mem_interpolation_II.v \
  effect_interpolation_II.v effect_interpolants.v effect_interpolation_proofs.v \
  arguments.v compcert.v \
  closed_safety.v closed_safety_weak.v trace_semantics.v\
  nucular_semantics.v \
  wholeprog_simulations.v wholeprog_lemmas.v \
  barebones_simulations.v \
  val_casted.v

# Linking files

LINKING=cast.v pos.v stack.v seq_lemmas.v pred_lemmas.v core_semantics_tcs.v \
  sepcomp.v gallina_coresem.v inj_lemmas.v join_sm.v reestablish.v wf_lemmas.v\
  linking_spec.v linking.v compcert_linking.v compcert_linking_lemmas.v \
  disjointness.v reach_lemmas.v rc_semantics.v rc_semantics_lemmas.v \
  linking_inv.v ret_lemmas.v call_lemmas.v linking_proof.v context_equiv.v

# Putting everything together (in driver/)

DRIVER=CompositionalCompiler.v Compiler.v CompositionalComplements.v Complements.v

# All source files

FILES=$(LIB) $(COMMON) $(BACKEND) $(CFRONTEND) $(CORE) $(LINKING) $(DRIVER) $(FLOCQ)

# Symbolic links vs. copy

ifneq (,$(findstring CYGWIN,$(shell uname -s)))
SLN=cp
else
SLN=ln -s
endif

all:
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) runtime
endif
ifeq ($(CCHECKLINK),true)
	$(MAKE) cchecklink
endif

proof: $(FILES:.v=.vo)

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

ccomp: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.native \
        && rm -f ccomp && $(SLN) _build/driver/Driver.native ccomp

ccomp.prof: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.p.native \
        && rm -f ccomp.prof && $(SLN) _build/driver/Driver.p.native ccomp.prof

ccomp.byte: extraction/STAMP driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) Driver.d.byte \
        && rm -f ccomp.byte && $(SLN) _build/driver/Driver.d.byte ccomp.byte

runtime:
	$(MAKE) -C runtime

cchecklink: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS_CHECKLINK) Validator.native \
        && rm -f cchecklink && $(SLN) _build/checklink/Validator.native cchecklink

cchecklink.byte: driver/Configuration.ml
	$(OCAMLBUILD) $(OCB_OPTIONS_CHECKLINK) Validator.d.byte \
        && rm -f cchecklink.byte && $(SLN) _build/checklink/Validator.d.byte cchecklink.byte

clightgen: extraction/STAMP driver/Configuration.ml exportclight/Clightdefs.vo
	$(OCAMLBUILD) $(OCB_OPTIONS_CLIGHTGEN) Clightgen.native \
        && rm -f clightgen && $(SLN) _build/exportclight/Clightgen.native clightgen

clightgen.byte: extraction/STAMP driver/Configuration.ml exportclight/Clightdefs.vo
	$(OCAMLBUILD) $(OCB_OPTIONS_CLIGHTGEN) Clightgen.d.byte \
        && rm -f clightgen.byte && $(SLN) _build/exportclight/Clightgen.d.byte clightgen.byte

.PHONY: proof extraction ccomp ccomp.prof ccomp.byte runtime cchecklink cchecklink.byte clightgen clightgen.byte

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex doc/coq2html.mll

tools/ndfun: tools/ndfun.ml
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/glob/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod -w $*.v

driver/Configuration.ml: Makefile.config VERSION
	(echo let stdlib_path = "\"$(LIBDIR)\""; \
         echo let prepro = "\"$(CPREPRO)\""; \
         echo let asm = "\"$(CASM)\""; \
         echo let linker = "\"$(CLINKER)\""; \
         echo let arch = "\"$(ARCH)\""; \
         echo let variant = "\"$(VARIANT)\""; \
         echo let system = "\"$(SYSTEM)\""; \
         echo let has_runtime_lib = $(HAS_RUNTIME_LIB); \
         echo let asm_supports_cfi = $(ASM_SUPPORTS_CFI); \
         version=`cat VERSION`; \
         echo let version = "\"$$version\"") \
        > driver/Configuration.ml

.depend: 
	touch .depend

depend: $(FILES) exportclight/Clightdefs.v .depend
	$(COQDEP) $^ \
        | sed -e 's|$(ARCH)/$(VARIANT)/|$$(ARCH)/$$(VARIANT)/|g' \
              -e 's|$(ARCH)/|$$(ARCH)/|g' \
        > .depend

install:
	install -d $(BINDIR)
	install ./ccomp $(BINDIR)
ifeq ($(CCHECKLINK),true)
	install ./cchecklink $(BINDIR)
endif
ifeq ($(HAS_RUNTIME_LIB),true)
	$(MAKE) -C runtime install
endif

clean:
	rm -f $(patsubst %, %/*.vo, $(DIRS))
	rm -f ccomp ccomp.byte cchecklink cchecklink.byte clightgen clightgen.byte
	rm -rf _build
	rm -rf doc/html doc/*.glob
	rm -f doc/coq2html.ml doc/coq2html
	rm -f driver/Configuration.ml
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli
	rm -f tools/ndfun
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

# Problems with coqchk (coq 8.4.pl2):
# Integers.Int.Z_mod_modulus_range takes forever to check
# Floats.Float.double_of_bits_of_double takes forever to check
# AST.external_function gives "Failure: impredicative Type inductive type"
# Asm.instruction gives "Failure: impredicative Type inductive type"
# Mach.instruction gives "Failure: impredicative Type inductive type"
# UnionFind.UF.elt gives "Anomaly: Uncaught exception Reduction.NotConvertible"

check-proof: $(FILES)
	$(COQCHK) -admit Integers -admit Floats -admit AST -admit Asm -admit Mach -admit UnionFind Complements 

print-includes:
	@echo $(COQINCLUDES)

include .depend

FORCE:
