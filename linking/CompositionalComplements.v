Require Import pos.
Require Import compcert_linking.
Require Import linking_proof.
Require Import context_equiv.
Require Import simulations.
Require Import nucular_semantics.
Require Import closed_simulations_lemmas.
Require Import Asm_coop.
Require Import Asm_nucular.
Require Import CompositionalCompiler.

(** * Contextual Equivalence for CompCert Clight->x86 Asm *)

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Notations and convenient definitions: *)

Notation Clight_module := (program Clight.fundef Ctypes.type).
Notation Asm_module := (AsmEFF.program).

Definition mk_src_sem (p : Clight_module) :=
  let ge := Genv.globalenv p in 
  @Modsem.mk Clight.fundef Ctypes.type ge Clight_coop.CL_core (Clight_eff.CL_eff_sem1 hf).

Definition mk_tgt_sem (tp : Asm_module) :=
  let tge := Genv.globalenv tp in
  @Modsem.mk AsmEFF.fundef unit tge Asm_coop.state (Asm_eff.Asm_eff_sem hf).

(** Apply the contextual equivalence functor from
   linking/context_equiv.v to to linking/linking_proof.v.*)

Module CE := ContextEquiv LinkingSimulation.

Section CompositionalComplements.

(** There are [N] modules. *)

Variable N : pos.

(** Source and target modules. ['I_N -> A], for [A : Type], is the type of finite
 functions from [{0..N-1}] to [A]. *)

Variable source_modules : 'I_N -> Clight_module.
Variable target_modules : 'I_N -> Asm_module.

(** The function [plt] maps a subset of the possible function names to the
  modules in which they are defined. *)

Variable plt : ident -> option 'I_N.

(** Wrap the source and target modules as 'Modsem's (as in Section 3). *)

Definition sems_S (ix : 'I_N) := mk_src_sem (source_modules ix).
Definition sems_T (ix : 'I_N) := mk_tgt_sem (target_modules ix).

(** [ge_top] and the two [domeq_*] hypotheses below constrain the source--target
  global envs. of the modules in [sems_S] and [sems_T] to have equal domain, as
  explained in Section 3. *)

Variable ge_top : ge_ty.
Variable domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (sems_S ix).(Modsem.ge).
Variable domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (sems_T ix).(Modsem.ge). 

(** The target modules are (independently) compiled from the respective
  source modules ([transf_clight_program] compiles Clight programs to Asm). *)

Variable transf : 
  forall ix : 'I_N, 
  transf_clight_program (source_modules ix) 
  = Errors.OK (target_modules ix).

(** Here we just prove that compilation preserves the set of global symbols. *)

Lemma find_syms :
  forall (i : 'I_N) (id : ident) (bf : block),
  Genv.find_symbol (Modsem.ge (sems_S i)) id = Some bf ->
  Genv.find_symbol (Modsem.ge (sems_T i)) id = Some bf.
Proof.
intros idx id bf.
unfold sems_S, sems_T; simpl.
generalize (transf idx); intros H.
apply transf_clight_program_preserves_syms with (s := id) in H.
rewrite H; auto.
Qed.

(** The (deterministic) context [C]. Assumptions on [C] are: 
- [sim_C]: C self-simulates ([C <= C]) (cf. Definition 2, pg. 10). 
- [det_C]: C is deterministic (cf. Definition 2, pg. 10). This is true,
      e.g., of all Clight and assembly contexts. 
- [nuke_C] restricts contexts to those that store only valid blocks.  This is
      footnote 5 on pg. 9 of the paper (one reviewer suggested we describe this
      condition in a bit more detail in the paper; we tend to agree and plan to
      do so in the final version). It turns out that this condition holds of all
      assembly contexts; see backend/Asm_nucular.v for the proof. 
- [domeq_C]: The global environment attached to the [C] module semantics 
      has the same domain (set of blocks marked "global") as [ge_top]. *)

(** NOTE: many of these side conditions fall away nicely if we abandon 
    'semantic' contexts, and instead express [C] in, e.g., CompCert Asm.
    But the current statement of the theorem is more general; for example,
    it supports contexts that are just mathematical relations expressed 
    in Coq's Gallina. *) 

Variable C : Modsem.t.   
Variable sim_C : 
  SM_simulation.SM_simulation_inject 
  C.(Modsem.sem) C.(Modsem.sem) C.(Modsem.ge) C.(Modsem.ge).
Variable nuke_C : Nuke_sem.t (Modsem.sem C).
Variable det_C : semantics_lemmas.corestep_fun (Modsem.sem C).
Variable domeq_C : genvs_domain_eq ge_top C.(Modsem.ge).

(** [CE.linker_S] ensures that both the context [C] the source
  modules [sems_S] are reach-closed. See file linking/context_equiv.v for
  details. Since the POPL deadline, we have proved that all safe Clight programs
  are reach-closed in this way. *)

Notation source_linked_semantics := (CE.linker_S sems_S plt C).
Notation target_linked_semantics := (CE.linker_T sems_T plt C).
Definition safe ge l m := 
  forall n, closed_safety.safeN source_linked_semantics ge n l m.

Lemma asm_modules_nucular (ix : 'I_N) : Nuke_sem.t (Modsem.sem (sems_T ix)).
Proof. solve[apply Asm_is_nuc]. Qed.

(** The [init] hypothesis just ensures that no module defines the same function
  twice. *)

Variable lnr : forall ix : 'I_N, 
  list_norepet (map fst (prog_defs (source_modules ix))).

(** Here we prove that [S_i <= T_i] for each source/target module pair, using
  Theorem [transf_clight_program_correct] from
  driver/CompositionalCompiler.v. *)

Lemma modules_inject (ix : 'I_N) : 
  SM_simulation.SM_simulation_inject 
    (Modsem.sem (sems_S ix)) (Modsem.sem (sems_T ix)) 
    (Modsem.ge (sems_S ix)) (Modsem.ge (sems_T ix)).
Proof.
generalize (transf ix); intros H.
eapply transf_clight_program_correct in H; eauto.
Qed.

(** The entry point for the linked program: *)

Variable main : Values.val.

(** * Contextual Equivalence in Matching States *)

(** Starting from matching source--target states, the source/target programs
 equiterminate when linked with [C], assuming the source linked program is safe
 and reach-closed (see above).  This is Corollary 2 on pg. 11 of the paper. *)

Notation lifted_sim := 
  (CE.lifted_sim asm_modules_nucular plt modules_inject domeq_S domeq_T 
   find_syms sim_C domeq_C nuke_C main).

Theorem context_equiv cd mu l1 m1 l2 m2 
  (source_safe : safe ge_top l1 m1) 
  (match12 : Wholeprog_sim.match_state lifted_sim cd mu l1 m1 l2 m2) :
  (terminates source_linked_semantics ge_top l1 m1 
   <-> terminates target_linked_semantics ge_top l2 m2).
Proof. 
eapply CE.context_equiv; eauto.   
unfold CE.extend_sems; intros ix; destruct (lt_dec ix N); auto.
simpl; intros m m' m'' ge c c' c'' H H2. 
simpl in H, H2; eapply asm_step_det; eauto.
Qed.

(** * Contextual Equivalence in Initial States *)

(** The following corollary (really, of CE.context_equiv) specializes
  to entry point main and the initial state of the linked program. *)

Theorem init_context_equiv l1 m1 m2 j vals1 vals2
  (source_safe : safe ge_top l1 m1)
  (init1 : initial_core source_linked_semantics ge_top main vals1 = Some l1)
  (init1_inv : cc_init_inv j ge_top vals1 m1 ge_top vals2 m2) :
  exists l2, 
  [/\ initial_core target_linked_semantics ge_top main vals2 = Some l2
    & (terminates source_linked_semantics ge_top l1 m1 
   <-> terminates target_linked_semantics ge_top l2 m2)].
Proof. 
eapply CE.init_context_equiv; eauto.
apply: asm_modules_nucular.
apply: modules_inject.
apply: find_syms.
unfold CE.extend_sems; intros ix; destruct (lt_dec ix N); auto.
simpl; intros m m' m'' ge c c' c'' H H2. 
simpl in H, H2; eapply asm_step_det; eauto.
Qed.

End CompositionalComplements.
  
