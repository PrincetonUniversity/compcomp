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

#count_lemmas
# - count the number of lines starting with the 'Lemma' keyword.
# - this may slightly undercount total number of distinct lemmas proved.
# $1: file names 
function count_lemmas {
  if [ ! -f `echo $1 | awk '{print $1;}'` ]; then echo $1
  else grep -e "Lemma\|Theorem" $1 | wc -l | awk '{printf "%d ", $1;}'
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
  count_files "$4" 0; echo -n "& "
  count_lemmas "$5"; echo -n "& "
  count_lemmas "$4"
  echo "\\\\"
}

#count-nocompcert
# $1: phase name
# $2: spec files
# $3: proof files
function count-nocompcert {
  echo -n "$1 && "
  count_files "$2" 0; echo -n "&& "
  count_files "$3" 0; echo -n "&& "
  count_lemmas "$3"
  echo "\\\\"
}

echo "\begin{tabular}{|l|r r |r r|r r|}"
echo "\hline            & \multicolumn{2}{c|}{Specs.}        & \multicolumn{2}{c|}{Proofs}  & \multicolumn{2}{c|}{Lemmas} \\\\ \hline"
echo "\emph{Compiler Phases:} & old & new & old & new & old & new \\\\"

SIMPLLOCALS_SPEC_FILES="../cfrontend/Clight.v ../cfrontend/Clight_coop.v ../cfrontend/Clight_eff.v"
SIMPLLOCALS_SPEC_FILES_COMPCERT="../cfrontend/Clight.v"
SIMPLLOCALS_PROOF_FILES="../cfrontend/SimplLocalsproof_comp.v"
SIMPLLOCALS_PROOF_FILES_COMPCERT="../cfrontend/SimplLocalsproof.v"
SIMPLLOCALS_UNUSED_SPECS=`./countCompCertOpsem.sh ../cfrontend/Clight.v` #Counts lines not used in Compositional CompCert
count "SimplLocals" "$SIMPLLOCALS_SPEC_FILES" "$SIMPLLOCALS_SPEC_FILES_COMPCERT" "$SIMPLLOCALS_PROOF_FILES" "$SIMPLLOCALS_PROOF_FILES_COMPCERT" "$SIMPLLOCALS_UNUSED_SPECS"

CSHMGEN_SPEC_FILES="../cfrontend/Clight.v ../cfrontend/Clight_coop.v ../cfrontend/Clight_eff.v ../cfrontend/Csharpminor.v ../cfrontend/Csharpminor_coop.v ../cfrontend/Csharpminor_eff.v"
CSHMGEN_SPEC_FILES_COMPCERT="../cfrontend/Clight.v ../cfrontend/Csharpminor.v"
CSHMGEN_PROOF_FILES="../cfrontend/Cshmgenproof_comp.v"
CSHMGEN_PROOF_FILES_COMPCERT="../cfrontend/Cshmgenproof.v"
CSHMGEN_UNUSED_SPECS=`./countCompCertOpsem.sh ../cfrontend/Clight.v ../cfrontend/Csharpminor.v` #Counts lines not used in Compositional CompCert
count "Csharpminorgen" "$CSHMGEN_SPEC_FILES" "$CSHMGEN_SPEC_FILES_COMPCERT" "$CSHMGEN_PROOF_FILES" "$CSHMGEN_PROOF_FILES_COMPCERT" "$CSHMGEN_UNUSED_SPECS"

CMINORGEN_SPEC_FILES="../cfrontend/Csharpminor.v ../cfrontend/Csharpminor_coop.v ../cfrontend/Csharpminor_eff.v ../backend/Cminor.v ../backend/Cminor_coop.v ../backend/Cminor_eff.v"
CMINORGEN_SPEC_FILES_COMPCERT="../cfrontend/Csharpminor.v ../backend/Cminor.v"
CMINORGEN_PROOF_FILES="../cfrontend/CminorgenproofSIM.v ../cfrontend/Cminorgenproof_comp.v"
CMINORGEN_PROOF_FILES_COMPCERT="../cfrontend/Cminorgenproof.v"
#Unused specs counted by hand, equals 1115loc
count "Cminorgen" "$CMINORGEN_SPEC_FILES" "$CMINORGEN_SPEC_FILES_COMPCERT" "$CMINORGEN_PROOF_FILES" "$CMINORGEN_PROOF_FILES_COMPCERT" "1115"

SELECTION_SPEC_FILES="../backend/Cminor.v ../backend/Cminor_coop.v ../backend/Cminor_eff.v ../backend/CminorSel.v ../backend/CminorSel_coop.v ../backend/CminorSel_eff.v"
SELECTION_SPEC_FILES_COMPCERT="../backend/Cminor.v ../backend/CminorSel.v"
SELECTION_PROOF_FILES="../backend/SelectLongproof_comp.v ../backend/SelectDivproof.v ../backend/Selectionproof_comp.v ../ia32/SelectOpproof.v"
SELECTION_PROOF_FILES_COMPCERT="../backend/SelectLongproof.v ../backend/SelectDivproof.v ../backend/Selectionproof.v ../ia32/SelectOpproof.v"
SELECTION_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/Cminor.v ../backend/CminorSel.v` #Counts lines not used in Compositional CompCert
count "Selection" "$SELECTION_SPEC_FILES" "$SELECTION_SPEC_FILES_COMPCERT" "$SELECTION_PROOF_FILES" "$SELECTION_PROOF_FILES_COMPCERT" "$SELECTION_UNUSED_SPECS"

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

RENUMBERING_SPEC_FILES="../backend/RTL.v ../backend/RTL_coop.v ../backend/RTL_eff.v"
RENUMBERING_SPEC_FILES_COMPCERT="../backend/RTL.v"
RENUMBERING_PROOF_FILES="../backend/Renumberproof_comp.v"
RENUMBERING_PROOF_FILES_COMPCERT="../backend/Renumberproof.v"
RENUMBERING_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/RTL.v` #Counts lines not used in Compositional CompCert
count "Renumbering" "$RENUMBERING_SPEC_FILES" "$RENUMBERING_SPEC_FILES_COMPCERT" "$RENUMBERING_PROOF_FILES" "$RENUMBERING_PROOF_FILES_COMPCERT" "$RENUMBERING_UNUSED_SPECS"

ALLOCATION_SPEC_FILES="../backend/RTL.v ../backend/RTL_coop.v ../backend/RTL_eff.v ../backend/LTL.v ../backend/LTL_coop.v ../backend/LTL_eff.v"
ALLOCATION_SPEC_FILES_COMPCERT="../backend/RTL.v ../backend/LTL.v"
ALLOCATION_PROOF_FILES="../backend/Allocproof_comp.v"
ALLOCATION_PROOF_FILES_COMPCERT="../backend/Allocproof.v"
ALLOCATION_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/RTL.v ../backend/LTL.v` #Counts lines not used in Compositional CompCert
count "Allocation" "$ALLOCATION_SPEC_FILES" "$ALLOCATION_SPEC_FILES_COMPCERT" "$ALLOCATION_PROOF_FILES" "$ALLOCATION_PROOF_FILES_COMPCERT" "$ALLOCATION_UNUSED_SPECS"

TUNNELING_SPEC_FILES="../backend/LTL.v ../backend/LTL_coop.v ../backend/LTL_eff.v"
TUNNELING_SPEC_FILES_COMPCERT="../backend/LTL.v"
TUNNELING_PROOF_FILES="../backend/Tunnelingproof_comp.v"
TUNNELING_PROOF_FILES_COMPCERT="../backend/Tunnelingproof.v"
TUNNELING_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/LTL.v` #Counts lines not used in Compositional CompCert
count "Tunneling" "$TUNNELING_SPEC_FILES" "$TUNNELING_SPEC_FILES_COMPCERT" "$TUNNELING_PROOF_FILES" "$TUNNELING_PROOF_FILES_COMPCERT" "$TUNNELING_UNUSED_SPECS"

LINEARIZE_SPEC_FILES="../backend/LTL.v ../backend/LTL_coop.v ../backend/LTL_eff.v ../backend/Linear.v ../backend/Linear_coop.v ../backend/Linear_eff.v"
LINEARIZE_SPEC_FILES_COMPCERT="../backend/LTL.v ../backend/Linear.v"
LINEARIZE_PROOF_FILES="../backend/Linearizeproof_comp.v"
LINEARIZE_PROOF_FILES_COMPCERT="../backend/Linearizeproof.v"
LINEARIZE_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/LTL.v ../backend/Linear.v` #Counts lines not used in Compositional CompCert
count "Linearize" "$LINEARIZE_SPEC_FILES" "$LINEARIZE_SPEC_FILES_COMPCERT" "$LINEARIZE_PROOF_FILES" "$LINEARIZE_PROOF_FILES_COMPCERT" "$LINEARIZE_UNUSED_SPECS"

CLEANUP_LABELS_SPEC_FILES="../backend/Linear.v ../backend/Linear_coop.v ../backend/Linear_eff.v"
CLEANUP_LABELS_SPEC_FILES_COMPCERT="../backend/Linear.v"
CLEANUP_LABELS_PROOF_FILES="../backend/CleanupLabelsproof_comp.v"
CLEANUP_LABELS_PROOF_FILES_COMPCERT="../backend/CleanupLabelsproof.v"
CLEANUP_LABELS_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/Linear.v` #Counts lines not used in Compositional CompCert
count "Cleanup Labels" "$CLEANUP_LABELS_SPEC_FILES" "$CLEANUP_LABELS_SPEC_FILES_COMPCERT" "$CLEANUP_LABELS_PROOF_FILES" "$CLEANUP_LABELS_PROOF_FILES_COMPCERT" "$CLEANUP_LABELS_UNUSED_SPECS"

STACKING_SPEC_FILES="../backend/Linear.v ../backend/Linear_coop.v ../backend/Linear_eff.v ../backend/Mach.v ../backend/Mach_coop.v ../backend/Mach_eff.v"
STACKING_SPEC_FILES_COMPCERT="../backend/Linear.v ../backend/Mach.v"
STACKING_PROOF_FILES="../backend/Stackingproof_comp.v"
STACKING_PROOF_FILES_COMPCERT="../backend/Stackingproof.v"
STACKING_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/Linear.v ../backend/Mach.v` #Counts lines not used in Compositional CompCert
count "Stacking" "$STACKING_SPEC_FILES" "$STACKING_SPEC_FILES_COMPCERT" "$STACKING_PROOF_FILES" "$STACKING_PROOF_FILES_COMPCERT" "$STACKING_UNUSED_SPECS"

ASMGEN_SPEC_FILES="../backend/Mach.v ../backend/Mach_coop.v ../backend/Mach_eff.v ../ia32/Asm.v ../backend/Asm_coop.v ../backend/Asm_eff.v"
ASMGEN_SPEC_FILES_COMPCERT="../backend/Mach.v ../ia32/Asm.v"
ASMGEN_PROOF_FILES="../backend/Asmgenproof0_comp.v ../backend/Asmgenproof1_comp.v ../backend/Asmgenproof_comp.v"
ASMGEN_PROOF_FILES_COMPCERT="../backend/Asmgenproof0.v ../ia32/Asmgenproof1.v ../ia32/Asmgenproof.v"
ASMGEN_UNUSED_SPECS=`./countCompCertOpsem.sh ../backend/Mach.v ../ia32/Asm.v` #Counts lines not used in Compositional CompCert
count "Asmgen" "$ASMGEN_SPEC_FILES" "$ASMGEN_SPEC_FILES_COMPCERT" "$ASMGEN_PROOF_FILES" "$ASMGEN_PROOF_FILES_COMPCERT" "$ASMGEN_UNUSED_SPECS"

echo "\hline"
echo "\emph{Theories:} & & & & & & \\\\"

INTERACTIONSEM_SPEC_FILES="../core/semantics.v"
INTERACTIONSEM_PROOF_FILES="../core/semantics_lemmas.v"
count-nocompcert "Interaction Sems. (Chapter~\ref{ch:coresem})" "$INTERACTIONSEM_SPEC_FILES" "$INTERACTIONSEM_PROOF_FILES"

TRACESEM_SPEC_FILES="../core/trace_semantics.v"
count-nocompcert "Trace Sems. (Chapter~\ref{ch:coresem})" "$TRACESEM_SPEC_FILES" "-"

GALLINASEM_SPEC_FILES="../linking/gallina_coresem.v"
count-nocompcert "Gallina Sems. (Chapter~\ref{ch:coresem})" "$GALLINASEM_SPEC_FILES" "-"

LINKING_SPEC_FILES="../linking/linking_spec.v ../linking/linking.v ../linking/compcert_linking.v ../linking/rc_semantics.v ../linking/context.v ../linking/context_equiv.v ../linking/pos.v"
LINKING_PROOF_FILES="../linking/compcert_linking_lemmas.v ../linking/cast.v ../linking/compcert_linking_lemmas.v ../linking/disjointness.v ../linking/inj_lemmas.v ../linking/join_sm.v ../linking/linking_inv.v ../linking/linking_proof.v ../linking/pred_lemmas.v ../linking/rc_semantics_lemmas.v ../linking/reach_lemmas.v ../linking/reestablish.v ../linking/ret_lemmas.v ../linking/seq_lemmas.v ../linking/stacking.v ../linking/stack.v ../linking/wf_lemmas.v"
count-nocompcert "Linking (Chapter~\ref{ch:linking})" "$LINKING_SPEC_FILES" "$LINKING_PROOF_FILES" ""

CLOSEDSIM_SPEC_FILES="../core/closed_simulations.v"
CLOSEDSIM_PROOF_FILES="../core/closed_simulations_lemmas.v"
count-nocompcert "Whole-Program Sims. (Chapter~\ref{ch:sims})" "$CLOSEDSIM_SPEC_FILES" "$CLOSEDSIM_PROOF_FILES"

STRUCTUREDINJ_PROOF_FILES="../core/structured_injections.v"
count-nocompcert "Structured Injs. (Chapter~\ref{ch:sims})" "55" "$STRUCTUREDINJ_PROOF_FILES" 

STRUCTUREDSIM_SPEC_FILES="../core/simulations.v ../core/semantics.v"
STRUCTUREDSIM_PROOF_FILES="../core/effect_properties.v ../core/simulations_lemmas.v ../core/reach.v ../core/relyguarantee_lemmas.v ../core/structured_injections.v"
count-nocompcert "Structured Sims. (Chapter~\ref{ch:sims})" "$STRUCTUREDSIM_SPEC_FILES" "$STRUCTUREDSIM_PROOF_FILES" 

VERTICALCOMP_SPEC_FILES="../core/interpolants.v"
VERTICALCOMP_PROOF_FILES="../core/internal_diagram_trans.v ../core/interpolation_II.v ../core/interpolation_proofs.v ../core/simulations_trans.v"
count-nocompcert "Transitivity (Chapter~\ref{ch:sepcomp})" "$VERTICALCOMP_SPEC_FILES" "$VERTICALCOMP_PROOF_FILES" 

VALID_SEMANTICS_SPEC_FILES="../core/nucular_semantics.v"
count-nocompcert "Valid Semantics (Chapter~\ref{ch:sepcomp})" "$VALID_SEMANTICS_SPEC_FILES" "-"

RC_SEMANTICS_SPEC_FILES="../linking/rc_semantics.v"
count-nocompcert "Reach-Closed Semantics (Chapter~\ref{ch:sepcomp})" "$RC_SEMANTICS_SPEC_FILES" "-"

CONTEXTS_SPEC_FILES="../linking/context.v"
count-nocompcert "Well-Defined Contexts (Chapter~\ref{ch:sepcomp})" "$CONTEXTS_SPEC_FILES" "-"

C_CONTEXTS_PROOF_FILES="../linking/clight_nucular.v ../cfrontend/Clight_self_simulates.v ../cfrontend/Clight_lemmas.v ../linking/safe_clight_rc.v"
count-nocompcert "Clight Well-Defined (Chapter~\ref{ch:sepcomp})" "-" "$C_CONTEXTS_PROOF_FILES"

echo "\hline"
echo "\end{tabular}"
