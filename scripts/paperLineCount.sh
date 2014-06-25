#!/bin/bash

#count_files
# $1: file names
function count_files {
  cat $1 | wc -l | awk '{printf "%d ", $1;}'
}

#count
# $1: phase name
# $2: spec files
# $3: proof files
# $4: compcert proof files
function count {
  echo -n "$1 & "
  count_files "$2"; echo -n "& "
  count_files "$3"; echo -n "& "
  count_files "$4"
  echo "\\\\"
}

#count-nocompcert
# $1: phase name
# $2: spec files
# $3: proof files
function count-nocompcert {
  echo -n "$1 & "
  count_files "$2"; echo -n "& "
  count_files "$3"; echo -n "& "
  echo "\\\\"
}

SIMPLLOCALS_SPEC_FILES="../cfrontend/Clight.v ../cfrontend/Clight_coop.v ../cfrontend/Clight_eff.v"
SIMPLLOCALS_PROOF_FILES="../cfrontend/SimplLocalsproofEFF.v"
SIMPLLOCALS_PROOF_FILES_COMPCERT="../cfrontend/SimplLocalsproof.v"
count "SimplLocals" "$SIMPLLOCALS_SPEC_FILES" "$SIMPLLOCALS_PROOF_FILES" "$SIMPLLOCALS_PROOF_FILES_COMPCERT"

CMINORGEN_SPEC_FILES="../cfrontend/Csharpminor.v ../cfrontend/Csharpminor_coop.v ../cfrontend/Csharpminor_eff.v ../backend/Cminor.v ../backend/Cminor_coop.v ../backend/Cminor_eff.v"
CMINORGEN_PROOF_FILES="../cfrontend/CminorgenproofSIM.v ../cfrontend/CminorgenproofEFF.v"
CMINORGEN_PROOF_FILES_COMPCERT="../cfrontend/Cminorgenproof.v"
count "Cminorgen" "$CMINORGEN_SPEC_FILES" "$CMINORGEN_PROOF_FILES" "$CMINORGEN_PROOF_FILES_COMPCERT"

RTLGEN_SPEC_FILES="../backend/CminorSel.v ../backend/CminorSel_coop.v ../backend/CminorSel_eff.v ../backend/RTL.v ../backend/RTL_coop.v ../backend/RTL_eff.v"
RTLGEN_PROOF_FILES="../backend/RTLgenproofEFF.v"
RTLGEN_PROOF_FILES_COMPCERT="../backend/RTLgenproof.v"
count "RTLgen" "$RTLGEN_SPEC_FILES" "$RTLGEN_PROOF_FILES" "$RTLGEN_PROOF_FILES_COMPCERT"

STACKING_SPEC_FILES="../backend/Linear.v ../backend/Linear_coop.v ../backend/Linear_eff.v ../backend/Mach.v ../backend/Mach_coop.v ../backend/Mach_eff.v"
STACKING_PROOF_FILES="../backend/StackingproofEFF.v"
STACKING_PROOF_FILES_COMPCERT="../backend/Stackingproof.v"
count "Stacking" "$STACKING_SPEC_FILES" "$STACKING_PROOF_FILES" "$STACKING_PROOF_FILES_COMPCERT"

STRUCTUREDSIM_SPEC_FILES="../core/effect_simulations.v ../core/effect_semantics.v"
STRUCTUREDSIM_PROOF_FILES="../core/effect_corediagram_trans.v ../core/effect_interpolants.v ../core/effect_interpolation_II.v ../core/effect_interpolation_proofs.v ../core/effect_properties.v ../core/effect_simulations_lemmas.v ../core/effect_simulations_trans.v ../core/reach.v ../core/rg_lemmas.v ../core/StructuredInjections.v"
count-nocompcert "Structured Simulations (\S\ref{sec:ssdetails})" "$STRUCTUREDSIM_SPEC_FILES" "$STRUCTUREDSIM_PROOF_FILES" ""

LINKING_SPEC_FILES="../linking/linking_spec.v ../linking/compcert_linking.v ../linking/rc_semantics.v ../linking/context_equiv.v ../linking/pos.v ../core/nucular_semantics.v"
LINKING_PROOF_FILES="../linking/compcert_linking_lemmas.v ../linking/cast.v ../linking/compcert_linking_lemmas.v ../linking/disjointness.v ../linking/inj_lemmas.v ../linking/join_sm.v ../linking/linking_inv.v ../linking/linking_proof.v ../linking/pred_lemmas.v ../linking/rc_semantics_lemmas.v ../linking/reach_lemmas.v ../linking/reestablish.v ../linking/ret_lemmas.v ../linking/seq_lemmas.v ../linking/stacking.v ../linking/stack.v ../linking/wf_lemmas.v"
count-nocompcert "Linking (\S\ref{sec:linking})" "$LINKING_SPEC_FILES" "$LINKING_PROOF_FILES" ""




