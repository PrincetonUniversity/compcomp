(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Globalenvs.

Require Import effect_simulations.
Require Import effect_simulations_trans.

(** Languages (syntax and semantics). *)
Require Clight.
Require Clight_coop.
Require Clight_eff.
Require Csharpminor.
Require Csharpminor_coop.
Require Csharpminor_eff.
Require Cminor.
Require Cminor_coop.
Require Cminor_eff.
Require CminorSel.
Require CminorSel_coop.
Require CminorSel_eff.
Require RTL.
Require RTL_coop.
Require RTL_eff.
Require LTL.
Require LTL_coop.
Require LTL_eff.
Require Linear.
Require Linear_coop.
Require Linear_eff.
Require Mach.
Require Mach_coop.
Require Mach_eff.
Require AsmEFF.
Require Asm_coop.
Require Asm_eff.
(** Translation passes. *)
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require SelectionNEW.
Require RTLgen.
Require Tailcall.
Require Renumber.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplLocalsproofEFF.
Require CshmgenproofEFF.
Require CminorgenproofEFF.
Require SelectionproofEFF.
Require RTLgenproofEFF.
Require TailcallproofEFF.
Require RenumberproofEFF.
Require AllocproofEFF.
Require TunnelingproofEFF.
Require LinearizeproofEFF.
Require CleanupLabelsproofEFF.
Require StackingproofEFF.
Require AsmgenproofEFF.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: RTL.program -> unit.
Parameter print_RTL_tailcall: RTL.program -> unit.
Parameter print_RTL_inline: RTL.program -> unit.
Parameter print_RTL_constprop: RTL.program -> unit.
Parameter print_RTL_cse: RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

(** We define three translation functions for whole programs: one
  starting with a Clight program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res AsmEFF.program :=
   OK f
   @@ print print_RTL
   @@ Tailcall.transf_program
   @@ print print_RTL_tailcall
   @@ Renumber.transf_program
  @@@ Allocation.transf_program
   @@ print print_LTL
   @@ Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ CleanupLabels.transf_program
  @@@ Stacking.transf_program
   @@ print print_Mach
  @@@ AsmgenEFF.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res AsmEFF.program :=
   OK p
   @@ print print_Cminor
  @@@ SelectionNEW.sel_program
  @@@ RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res AsmEFF.program :=
  OK p 
   @@ print print_Clight
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ transf_cminor_program.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto. 
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit), 
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto. 
Qed.

Lemma fst_transform_globdef_eq A B V (f : A -> B) (gv : ident*globdef A V) :
  fst (transform_program_globdef f gv) = fst gv.
Proof.
destruct gv; destruct g; auto.
Qed.

Lemma map_fst_transform_globdef_eq A B V (f : A -> B) (l : list (ident*globdef A V)) :
  map fst (map (transform_program_globdef f) l) = map fst l.
Proof.
induction l; auto.
simpl; rewrite fst_transform_globdef_eq, IHl; auto.
Qed.

Lemma map_fst_transf_globdefs_eq A B V (f : A -> res B) p (l : list (ident*globdef B V)) :
  transf_globdefs f (fun v => OK v) (prog_defs p) = OK l ->
  map fst (prog_defs p) = map fst l.
Proof.
generalize (prog_defs p); intros l0.
revert l0 l.
induction l0; inversion 1; subst; auto.
simpl in *.
destruct a.
destruct g.
destruct (f f0); try solve[inv H].
monadInv H.
monadInv H1.
simpl in *.
f_equal.
solve[rewrite <-IHl0; auto].
monadInv H.
monadInv H1.
simpl.
f_equal.
solve[rewrite <-IHl0; auto].
Qed.

Lemma list_norepet_transform F V (p : AST.program F V) G (f : F -> G) :
  list_norepet (map fst (prog_defs p)) <-> 
  list_norepet (map fst (prog_defs (transform_program f p))).
Proof.
unfold transform_program; simpl.
rewrite map_fst_transform_globdef_eq; split; auto.
Qed.

Lemma list_norepet_transform_partial F V (p : AST.program F V) G (f : F -> res G) p' :
  transform_partial_program f p = OK p' ->
  list_norepet (map fst (prog_defs p)) ->
  list_norepet (map fst (prog_defs p')).
Proof.
unfold transform_partial_program, transform_partial_program2, bind.
case_eq (transf_globdefs f (fun v : V => OK v) (prog_defs p)); try inversion 2.
erewrite map_fst_transf_globdefs_eq; eauto.
Qed.

Section transf_correct.

Variables hf : I64Helpers.helper_functions.

Theorem transf_rtl_program_correct 
      p tp
      (defs_norepet: list_norepet (map fst (prog_defs p))) 
      (init_mem: exists m0, Genv.init_mem p = Some m0) :
  transf_rtl_program p = OK tp ->
  SM_simulation.SM_simulation_inject 
    (RTL_eff.rtl_eff_sem hf) (Asm_eff.Asm_eff_sem hf) 
    (Genv.globalenv p) (Genv.globalenv tp).
Proof.
  intros H.
  unfold transf_rtl_program in H.
  repeat rewrite compose_print_identity in H.   
  simpl in H.
  set (p1 := Tailcall.transf_program p) in *.
  set (p2 := Renumber.transf_program p1) in *.
  destruct (Allocation.transf_program p2) as [p3|] eqn:?; simpl in H; try discriminate.
  set (p4 := Tunneling.tunnel_program p3) in *.
  destruct (Linearize.transf_program p4) as [p5|] eqn:?; simpl in H; try discriminate.
  set (p6 := CleanupLabels.transf_program p5) in *.
  destruct (Stacking.transf_program p6) as [p7|] eqn:?; simpl in H; try discriminate.

  (* Tailcall *)
  eapply eff_sim_trans. apply TailcallproofEFF.transl_program_correct; auto.

  (* Renumber *)
  assert (list_norepet (map fst (prog_defs (Tailcall.transf_program p)))).
  { unfold Tailcall.transf_program; rewrite <-list_norepet_transform; auto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem (Tailcall.transf_program p) = Some m0).
  { destruct init_mem as [m0 init_mem]. 
    unfold Tailcall.transf_program; exploit Genv.init_mem_transf; eauto. }
  eapply eff_sim_trans. apply RenumberproofEFF.transl_program_correct; auto.

  (* Allocation *)
  assert (list_norepet (map fst (prog_defs p2))).
  { unfold p2, Renumber.transf_program; rewrite <-list_norepet_transform; auto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem p2 = Some m0).
  { destruct H1 as [m0 H1].
    unfold p2, Renumber.transf_program; exploit Genv.init_mem_transf; eauto. }
  eapply eff_sim_trans. apply AllocproofEFF.transl_program_correct; eauto.   

  (* Tunneling *)
  assert (list_norepet (map fst (prog_defs p3))).
  { revert Heqr; unfold Allocation.transf_program; intros.
    eapply list_norepet_transform_partial; eauto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem p3 = Some m0).
  { destruct H1 as [m0 H1]. destruct H3 as [m1 H3].
    eexists; eapply Genv.init_mem_transf_partial; eauto. }
  eapply eff_sim_trans. apply TunnelingproofEFF.transl_program_correct; auto.   

  (* Linearize *)
  assert (list_norepet (map fst (prog_defs p4))).
  { unfold p4, Tunneling.tunnel_program; rewrite <-list_norepet_transform; auto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem p4 = Some m0).
  { destruct H1 as [m0 H1]. destruct H3 as [m1 H3]. destruct H5 as [m2 H5].
    unfold p4, Tunneling.tunnel_program; exploit Genv.init_mem_transf; eauto. }
  eapply eff_sim_trans. apply LinearizeproofEFF.transl_program_correct; eauto.   

  (* CleanupLabels *)  
  assert (list_norepet (map fst (prog_defs p5))).
  { revert Heqr; unfold Linearize.transf_program; intros.
    eapply list_norepet_transform_partial; eauto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem p5 = Some m0).
  { destruct H1 as [m0 H1]. destruct H3 as [m1 H3]. destruct H5 as [m2 H5].
    destruct H7 as [m3 H7].
    eexists; eapply Genv.init_mem_transf_partial; eauto. }
  eapply eff_sim_trans. apply CleanupLabelsproofEFF.transl_program_correct; eauto.   

  (* Stacking *)
  assert (list_norepet (map fst (prog_defs p6))).
  { unfold p6, CleanupLabels.transf_program; rewrite <-list_norepet_transform; auto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem p6 = Some m0).
  { destruct H1 as [m0 H1]. destruct H3 as [m1 H3]. destruct H5 as [m2 H5].
    destruct H7 as [m3 H7]. destruct H9 as [m4 H9].
    unfold p6, CleanupLabels.transf_program; exploit Genv.init_mem_transf; eauto. }
  eapply eff_sim_trans. apply StackingproofEFF.transl_program_correct; eauto.
    eexact AsmgenproofEFF.return_address_exists. 

  (* Asmgen *)  
  assert (list_norepet (map fst (prog_defs p7))).
  { revert Heqr; unfold Allocation.transf_program; intros.
    eapply list_norepet_transform_partial; eauto. }
  assert (exists m0 : Memory.Mem.mem, Genv.init_mem p7 = Some m0).
  { destruct H1 as [m0 H1]. destruct H3 as [m1 H3]. destruct H5 as [m2 H5].
    destruct H7 as [m3 H7]. destruct H9 as [m4 H9]. destruct H11 as [m5 H11].
    eexists; eapply Genv.init_mem_transf_partial; eauto. }
  apply AsmgenproofEFF.transl_program_correct; eauto.   
Qed.  

Theorem transf_cminor_program_correct 
      p tp
      (defs_norepet: list_norepet (map fst (prog_defs p))) 
      (init_mem: exists m0, Genv.init_mem p = Some m0) 
      (helpers: BuiltinEffects.i64_helpers_correct (Genv.globalenv p) hf) :
  transf_cminor_program p = OK tp ->
  SM_simulation.SM_simulation_inject 
    (Cminor_eff.cmin_eff_sem hf) (Asm_eff.Asm_eff_sem hf) 
    (Genv.globalenv p) (Genv.globalenv tp).
Proof.
  intros H.
  unfold transf_cminor_program in H.
  repeat rewrite compose_print_identity in H.   
  simpl in H.
  destruct (SelectionNEW.sel_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (RTLgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.  

  (* Selection *)
  eapply eff_sim_trans. apply SelectionproofEFF.transl_program_correct; auto.
  unfold SelectionNEW.sel_program.
Abort. (*in progress*)

(* HERE: Must pull get_helpers out of SelectionNEW into toplevel compilation function *)

Theorem transf_clight_program_correct
      p tp
      (defs_norepet: list_norepet (map fst (prog_defs p))) 
      (init_mem: exists m0, Genv.init_mem p = Some m0) :
  transf_clight_program p = OK tp ->
  SM_simulation.SM_simulation_inject 
    (clight_eff_sem hf) (Asm_eff_sem hf) 
    (Genv.globalenv p) (Genv.globalenv tp).
Proof.
  intros. 
  assert (F: forward_simulation (Clight.semantics1 p) (Asm.semantics tp)).
  revert H; unfold transf_clight_program; simpl.
  rewrite print_identity.
  caseEq (SimplLocals.transf_program p); simpl; try congruence; intros p0 EQ0.
  caseEq (Cshmgen.transl_program p0); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply SimplLocalsproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_program_correct _ _ EQ3)). 

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.
