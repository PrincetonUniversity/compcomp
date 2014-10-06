#!/bin/bash

#count_files
# $1: file names (or hand-counted loc, if first file argument does not exist)
# $2: number of unused spec. lines to subtract, if any
function count_files {
  UNUSED=$2
  if [ ! -f `echo $1 | awk '{print $1;}'` ]; then echo $1
  else cat $1 | wc -l | sed -e "s/$/\t${UNUSED}/" | awk '{printf "%d ", $1-$2;}'
  fi
}

#count
# $1: phase name
# $2: spec files
# $3: compcert spec files
# $4: proof files
# $5: compcert proof files
# $6: no. compcert spec lines not used in Compositional CompCert
function count {
  echo -n "$1 & "
  count_files "$3" 0; echo -n "& "
  count_files "$2" $6; echo -n "& "
  count_files "$5" 0; echo -n "& "
  count_files "$4" 0
  echo "\\\\"
}

#count-nocompcert
# $1: phase name
# $2: spec files
# $3: proof files
function count-nocompcert {
  echo -n "$1 && "
  count_files "$2" 0; echo -n "&& "
  count_files "$3" 0
  echo "\\\\"
}

echo "\begin{tabular}{|l|r r |r r|}"
echo "\hline            & \multicolumn{2}{c|}{Specs.}        & \multicolumn{2}{c|}{Proofs} \\\\ \hline"
echo "\emph{Compiler Phases:} & old & new & old & new \\\\"

SIMPLLOCALS_SPEC_FILES="../cfrontend/Clight.v ../cfrontend/Clight_coop.v ../cfrontend/Clight_eff.v"
SIMPLLOCALS_SPEC_FILES_COMPCERT="../cfrontend/Clight.v"
SIMPLLOCALS_PROOF_FILES="../cfrontend/SimplLocalsproof_comp.v"
SIMPLLOCALS_PROOF_FILES_COMPCERT="../cfrontend/SimplLocalsproof.v"
SIMPLLOCALS_UNUSED_SPECS=`./countCompCertOpsem.sh ../cfrontend/Clight.v` #Counts lines not used in Compositional CompCert
count "SimplLocals" "$SIMPLLOCALS_SPEC_FILES" "$SIMPLLOCALS_SPEC_FILES_COMPCERT" "$SIMPLLOCALS_PROOF_FILES" "$SIMPLLOCALS_PROOF_FILES_COMPCERT" "$SIMPLLOCALS_UNUSED_SPECS"

CMINORGEN_SPEC_FILES="../cfrontend/Csharpminor.v ../cfrontend/Csharpminor_coop.v ../cfrontend/Csharpminor_eff.v ../backend/Cminor.v ../backend/Cminor_coop.v ../backend/Cminor_eff.v"
CMINORGEN_SPEC_FILES_COMPCERT="../cfrontend/Csharpminor.v ../backend/Cminor.v"
CMINORGEN_PROOF_FILES="../cfrontend/CminorgenproofSIM.v ../cfrontend/Cminorgenproof_comp.v"
CMINORGEN_PROOF_FILES_COMPCERT="../cfrontend/Cminorgenproof.v"
#Unused specs counted by hand, equals 1115loc
count "Cminorgen" "$CMINORGEN_SPEC_FILES" "$CMINORGEN_SPEC_FILES_COMPCERT" "$CMINORGEN_PROOF_FILES" "$CMINORGEN_PROOF_FILES_COMPCERT" "1115"

RTLGEN_SPEC_FILES="../backend/CminorSel.v ../backend/CminorSel_coop.v ../backend/CminorSel_eff.v ../backend/RTL.v ../backend/RTL_coop.v ../backend/RTL_eff.v"
RTLGEN_SPEC_FILES_COMPCERT="../backend/CminorSel.v ../backend/RTL.v"
RTLGEN_PROOF_FILES="../backend/RTLgenproof_comp.v"
RTLGEN_PROOF_FILES_COMPCERT="../backend/RTLgenproof.v"
RTLGEN_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/CminorSel.v ../backend/RTL.v` #Counts lines not used in Compositional CompCert
count "RTLgen" "$RTLGEN_SPEC_FILES" "$RTLGEN_SPEC_FILES_COMPCERT" "$RTLGEN_PROOF_FILES" "$RTLGEN_PROOF_FILES_COMPCERT" "$RTLGEN_UNUSED_SPECS"

TAILCALL_SPEC_FILES="../backend/RTL.v ../backend/RTL_coop.v ../backend/RTL_eff.v"
TAILCALL_SPEC_FILES_COMPCERT="../backend/RTL.v"
TAILCALL_PROOF_FILES="../backend/Tailcallproof_comp.v"
TAILCALL_PROOF_FILES_COMPCERT="../backend/Tailcallproof.v"
TAILCALL_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/RTL.v` #Counts lines not used in Compositional CompCert
count "Tailcall" "$TAILCALL_SPEC_FILES" "$TAILCALL_SPEC_FILES_COMPCERT" "$TAILCALL_PROOF_FILES" "$TAILCALL_PROOF_FILES_COMPCERT" "$TAILCALL_UNUSED_SPECS"

STACKING_SPEC_FILES="../backend/Linear.v ../backend/Linear_coop.v ../backend/Linear_eff.v ../backend/Mach.v ../backend/Mach_coop.v ../backend/Mach_eff.v"
STACKING_SPEC_FILES_COMPCERT="../backend/Linear.v ../backend/Mach.v"
STACKING_PROOF_FILES="../backend/Stackingproof_comp.v"
STACKING_PROOF_FILES_COMPCERT="../backend/Stackingproof.v"
STACKING_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/Linear.v ../backend/Mach.v` #Counts lines not used in Compositional CompCert
count "Stacking" "$STACKING_SPEC_FILES" "$STACKING_SPEC_FILES_COMPCERT" "$STACKING_PROOF_FILES" "$STACKING_PROOF_FILES_COMPCERT" "$STACKING_UNUSED_SPECS"

echo "\hline"
echo "\emph{Theories:} & & & & \\\\"

STRUCTUREDINJ_PROOF_FILES="../core/structured_injections.v"
count-nocompcert "Structured Injs. (\S\ref{sec:ss})" "55" "$STRUCTUREDINJ_PROOF_FILES" 

STRUCTUREDSIM_SPEC_FILES="../core/simulations.v ../core/semantics.v"
STRUCTUREDSIM_PROOF_FILES="../core/effect_properties.v ../core/simulations_lemmas.v ../core/reach.v ../core/relyguarantee_lemmas.v ../core/structured_injections.v"
count-nocompcert "Structured Sims. (\S\ref{sec:ss})" "$STRUCTUREDSIM_SPEC_FILES" "$STRUCTUREDSIM_PROOF_FILES" 

VERTICALCOMP_SPEC_FILES="../core/interpolants.v"
VERTICALCOMP_PROOF_FILES="../core/internal_diagram_trans.v ../core/interpolation_II.v ../core/interpolation_proofs.v ../core/simulations_trans.v"
count-nocompcert "Transitivity (\S\ref{sec:composition})" "$VERTICALCOMP_SPEC_FILES" "$VERTICALCOMP_PROOF_FILES" 

LINKING_SPEC_FILES="../linking/linking_spec.v ../linking/compcert_linking.v ../linking/rc_semantics.v ../linking/context_equiv.v ../linking/pos.v ../core/nucular_semantics.v"
LINKING_PROOF_FILES="../linking/compcert_linking_lemmas.v ../linking/cast.v ../linking/compcert_linking_lemmas.v ../linking/disjointness.v ../linking/inj_lemmas.v ../linking/join_sm.v ../linking/linking_inv.v ../linking/linking_proof.v ../linking/pred_lemmas.v ../linking/rc_semantics_lemmas.v ../linking/reach_lemmas.v ../linking/reestablish.v ../linking/ret_lemmas.v ../linking/seq_lemmas.v ../linking/stacking.v ../linking/stack.v ../linking/wf_lemmas.v"
count-nocompcert "Linking (\S\ref{sec:linking}, \S\ref{sec:composition})" "$LINKING_SPEC_FILES" "$LINKING_PROOF_FILES" ""

echo "\hline"
echo "\end{tabular}"
