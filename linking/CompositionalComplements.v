(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import pos.
Require Import compcert_linking.
Require Import linking_proof.
Require Import context_equiv.
Require Import simulations.
Require Import rc_semantics.
Require Import nucular_semantics.
Require Import closed_simulations_lemmas.
Require Import safe_clight_rc.
Require Import Asm_coop.
Require Import Asm_nucular.
Require Import CompositionalCompiler.

(** * Contextual Equivalence for CompCert Clight->x86 Asm *)

(** Notations and convenient definitions: *)

Notation Clight_module := (program Clight.fundef Ctypes.type).
Notation Asm_module := (Asm_comp.program).

Definition mk_src_sem (p : Clight_module) :=
  let ge := Genv.globalenv p in 
  @Modsem.mk Clight.fundef Ctypes.type ge Clight_coop.CL_core (Clight_eff.CL_eff_sem1 hf).

Definition mk_tgt_sem (tp : Asm_module) :=
  let tge := Genv.globalenv tp in
  @Modsem.mk Asm_comp.fundef unit tge Asm_coop.state (Asm_eff.Asm_eff_sem hf).

(** Apply the contextual equivalence functor from [linking/context_equiv.v] to
[linking/linking_proof.v]. *)

Module CE := ContextEquiv LinkingSimulation.

Lemma compcert_equiv  
(** There are [N] modules. *)
  (N : pos)

(** Source and target modules. ['I_N -> A], for [A : Type], is the type of finite
  functions from [{0..N-1}] to [A]. *)
  (source_modules : 'I_N -> Clight_module)
  (target_modules : 'I_N -> Asm_module)

(** The function [plt] maps a subset of the possible function names to the
  modules in which they are defined. *)
  (plt : ident -> option 'I_N) 

(** The entry point *)
  (main : val) :

(** Wrap the source and target modules as 'Modsem's (as in Section 3). *)
  let sems_S (ix : 'I_N) := mk_src_sem (source_modules ix) in
  let sems_T (ix : 'I_N) := mk_tgt_sem (target_modules ix) in
  let prog_S := Prog.mk sems_S main in
  let prog_T := Prog.mk sems_T main in

(** [ge_top] and the two [domeq_*] hypotheses below constrain the source--target
  global envs. of the modules in [sems_S] and [sems_T] to have equal domain, as
  explained in Section 3. *)
  forall ge_top : ge_ty,
  forall domeq_S : (forall ix : 'I_N, genvs_domain_eq ge_top (sems_S ix).(Modsem.ge)),

(** No module defines the same module twice. *)
  forall lnr : (forall ix : 'I_N, list_norepet (map fst (prog_defs (source_modules ix)))),

(** The target modules are (independently) compiled from the respective
  source modules ([transf_clight_program] compiles Clight programs to Asm). *)
  forall transf : 
    (forall ix : 'I_N, transf_clight_program (source_modules ix) 
                     = Errors.OK (target_modules ix)),

(** All of the above together imply that [prog_S] and [prog_T] are contextually
  equivalent. *) 
  Equiv_ctx ge_top plt prog_S prog_T.

Proof.
move=> sems_S sems_T prog_S prog_T ge_top deqS lnr transf.
have find_syms :
  forall (i : 'I_N) (id : ident) (bf : block),
  Genv.find_symbol (Modsem.ge (sems_S i)) id = Some bf ->
  Genv.find_symbol (Modsem.ge (sems_T i)) id = Some bf.
{ move=> idx id bf; rewrite /sems_S /sems_T /=; move: (transf idx)=> H.
  by apply transf_clight_program_preserves_syms with (s := id) in H; rewrite H. }
apply: CE.equiv=> //.
by move=> ix; apply: Clight_RC.
by move=> ix; apply: Asm_is_nuc.
move=> ix; rewrite /Prog.sems/= => m m' m'' ge c c' c'' /= H H2. 
by eapply asm_step_det; eauto.
move=> ix; move: (transf ix)=> H.
by eapply transf_clight_program_correct in H; eauto.
Qed.

Module PR := ProgRefines LinkingSimulation.

Lemma compcert_refines
  (N : pos)
  (source_modules : 'I_N -> Clight_module)
  (target_modules : 'I_N -> Asm_module)
  (plt : ident -> option 'I_N) 
  (main : val) :
  let sems_S (ix : 'I_N) := mk_src_sem (source_modules ix) in
  let sems_T (ix : 'I_N) := mk_tgt_sem (target_modules ix) in
  let prog_S := Prog.mk sems_S main in
  let prog_T := Prog.mk sems_T main in
  forall ge_top : ge_ty,
  forall domeq_S : (forall ix : 'I_N, genvs_domain_eq ge_top (sems_S ix).(Modsem.ge)),
  forall lnr : (forall ix : 'I_N, list_norepet (map fst (prog_defs (source_modules ix)))),
  forall transf : 
    (forall ix : 'I_N, transf_clight_program (source_modules ix) 
                     = Errors.OK (target_modules ix)),
  forall EM : ClassicalFacts.excluded_middle,
  Prog_refines ge_top plt prog_S prog_T.
Proof.
move=> sems_S sems_T prog_S prog_T ge_top deqS lnr transf EM.
have find_syms :
  forall (i : 'I_N) (id : ident) (bf : block),
  Genv.find_symbol (Modsem.ge (sems_S i)) id = Some bf ->
  Genv.find_symbol (Modsem.ge (sems_T i)) id = Some bf.
{ move=> idx id bf; rewrite /sems_S /sems_T /=; move: (transf idx)=> H.
  by apply transf_clight_program_preserves_syms with (s := id) in H; rewrite H. }
apply: PR.refines=> //.
by move=> ix; apply: Clight_RC.
by move=> ix; apply: Asm_is_nuc.
move=> ix; rewrite /Prog.sems/= => m m' m'' ge c c' c'' /= H H2. 
by eapply asm_step_det; eauto.
move=> ix; move: (transf ix)=> H.
by eapply transf_clight_program_correct in H; eauto.
Qed.  
