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
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require AsmEFF.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require SelectionNEW.
Require RTLgen.
Require Tailcall.
(*Require Inlining.*)
Require Renumber.
(*Require Constprop.
Require CSE.*)
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Stacking.
Require AsmgenEFF.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproofEFF.
Require CshmgenproofEFF.
Require CminorgenproofEFF.
Require SelectionproofEFF.
Require RTLgenproofEFF.
Require TailcallproofEFF.
(*Require Inliningproof.*)
Require RenumberproofEFF.
(*Require Constpropproof.
Require CSEproof.*)
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
(*Parameter print_RTL_inline: RTL.program -> unit.
Parameter print_RTL_constprop: RTL.program -> unit.
Parameter print_RTL_cse: RTL.program -> unit.*)
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
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res AsmEFF.program :=
   OK f
   @@ print print_RTL
   @@ Tailcall.transf_program
   @@ print print_RTL_tailcall
(*  @@@ Inlining.transf_program*)
   @@ Renumber.transf_program
(*  @@ print print_RTL_inline*)
(*   @@ Constprop.transf_program*)
(*  @@ Renumber.transf_program*)
(*   @@ print print_RTL_constprop
  @@@ CSE.transf_program
   @@ print print_RTL_cse*)
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

(*Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p 
  @@@ SimplExpr.transl_program
  @@@ transf_clight_program.
*)

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. (*destruct (printer prog);*) auto. 
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit), 
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto. 
Qed.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)
Remark list_norepet_map_inv:
  forall (A B: Type) (f: A -> B) 
   (Finj: forall a b, f a = f b -> a=b) (l: list A),
  list_norepet l -> list_norepet (List.map f l).
Proof.
  induction l; simpl; intros.
  constructor.
  inv H. constructor; auto. red; intros; elim H2. specialize (IHl H3). 
  apply in_map_iff in H. destruct H as [? [? ?]]. apply Finj in H.
  subst; trivial.
Qed.

Remark list_norepet_map_invProd:
  forall (A B C: Type) (f: C*A -> C*B) 
   (Hf: forall c a, exists b, f (c,a) = (c,b))
   (l:list (C*A)),
   list_norepet (map fst l) ->
   list_norepet (map fst (List.map f l)).
Proof.
  induction l; simpl; intros.
  constructor.
  inv H. constructor; auto. red; intros; elim H2. specialize (IHl H3).
  apply in_map_iff in H. destruct H as [? [? ?]]. clear H2. 
  destruct x; simpl in *. subst; simpl in *.
  destruct a. simpl in *. destruct (Hf c a). rewrite H in *. clear H. 
  simpl in H0. apply in_map_iff in H0. destruct H0 as [? [? ?]].
  destruct x0. destruct (Hf c0 a0). rewrite H1 in H. inv H.
  apply in_map_iff. exists (c,a0); auto.
Qed.

Lemma TransformLNR_partial: forall {A B V} f p q
 (LNR: list_norepet (map fst (prog_defs p)))
 (TPP: @transform_partial_program A B V f p = OK q),
 list_norepet (map fst (prog_defs q)).
Proof. intros.  destruct p. simpl in *. 
unfold transform_partial_program, transform_partial_program2 in TPP. 
monadInv TPP. (* destruct x; simpl in *. constructor.*)
generalize dependent x. (*generalize dependent p.*)
induction prog_defs; simpl in *; intros.
  inv EQ. constructor.
inv LNR. destruct a.
  destruct g.
    remember (f f0) as d.
    destruct d; inv EQ. monadInv H0.
    specialize (IHprog_defs H2 _ EQ).
    constructor; eauto.
    simpl in *. intros N. apply H1. clear H1.
    apply in_map_iff. 
Admitted. 

Lemma TransformLNR_partial2: forall {A B V W} f g p q
 (LNR: list_norepet (map fst (prog_defs p)))
 (TPP: @transform_partial_program2 A B V W f g p = OK q),
 list_norepet (map fst (prog_defs q)).
Admitted.

Lemma TransformLNR: forall {A B V} f p 
 (LNR: list_norepet (map fst (prog_defs p))),
 list_norepet (map fst (prog_defs (@transform_program A B V f p))).
Proof. intros.  destruct p. simpl in *. clear prog_main.
eapply list_norepet_map_invProd; trivial.
intros. unfold transform_program_globdef.
destruct a.
 eexists; reflexivity.
 eexists; reflexivity. 
Qed.

Require Import effect_simulations.
Require Import effect_simulations_trans.
Require Import Globalenvs.
Require Import Cminor_eff.
Require Import Clight_eff.
Require Import RTL_eff.
Require Import Asm_eff.

Variable hf : I64Helpers.helper_functions.
Axiom HelpersOK: I64Helpers.get_helpers = OK hf.

Theorem transf_rtl_program_correct:
  forall p tp m0 (INIT: Genv.init_mem p = Some m0)
  (LNR: list_norepet (map fst (prog_defs p))),
  transf_rtl_program p = OK tp ->
  SM_simulation.SM_simulation_inject (rtl_eff_sem hf) (Asm_eff_sem hf)
      (Genv.globalenv p) (Genv.globalenv tp).
Proof.
  intros. 
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
  eapply eff_sim_trans.
    eapply TailcallproofEFF.transl_program_correct. 
    assumption. exists m0. assumption.
  apply Genv.init_mem_transf with (transf:= Tailcall.transf_fundef)
      in INIT.
  eapply TransformLNR in LNR.
  eapply eff_sim_trans.
    eapply RenumberproofEFF.transl_program_correct.
    eapply LNR.
    exists m0. apply INIT. 
  eapply Genv.init_mem_transf with (transf:= Renumber.transf_fundef)
      in INIT.
  eapply TransformLNR in LNR.
  eapply eff_sim_trans.
    eapply AllocproofEFF.transl_program_correct.
    instantiate (1:=p3). auto.
    eapply LNR.
    exists m0. apply INIT.  
  eapply Genv.init_mem_transf_partial in INIT.  2: eauto.
  eapply TransformLNR_partial in LNR.  2: eauto.
  eapply eff_sim_trans.
    eapply TunnelingproofEFF.transl_program_correct.
    eassumption.
    exists m0. apply INIT. 
  eapply Genv.init_mem_transf in INIT. 
  eapply TransformLNR in LNR. 
  eapply eff_sim_trans.
    eapply LinearizeproofEFF.transl_program_correct. 
    eassumption. 
    eassumption.
    exists m0. apply INIT. 
  eapply Genv.init_mem_transf_partial in INIT. 2: eauto.
  eapply TransformLNR_partial in LNR. 2: eauto.
  eapply eff_sim_trans.
    eapply CleanupLabelsproofEFF.transl_program_correct.
    eassumption.
    exists m0. apply INIT. 
  eapply Genv.init_mem_transf in INIT.
  eapply TransformLNR in LNR. 
  eapply eff_sim_trans.
    eapply StackingproofEFF.transl_program_correct.
    eexact AsmgenproofEFF.return_address_exists. eassumption.
    eassumption.
    exists m0. apply INIT. 
  eapply Genv.init_mem_transf_partial in INIT. 2: eauto.
  eapply TransformLNR_partial in LNR. 2: eauto.
  apply AsmgenproofEFF.transl_program_correct. 
    eassumption.
    eassumption.
    exists m0. apply INIT.
Qed.

Theorem transf_cminor_program_correct:
  forall p tp m0 (INIT: Genv.init_mem p = Some m0)
  (LNR: list_norepet (map fst (prog_defs p))),
  transf_cminor_program p = OK tp ->
  SM_simulation.SM_simulation_inject (cmin_eff_sem hf) (Asm_eff_sem hf)
      (Genv.globalenv p) (Genv.globalenv tp).
Proof.
  intros.
  unfold transf_cminor_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  destruct (SelectionNEW.sel_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (RTLgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.
  eapply eff_sim_trans.
    eapply SelectionproofEFF.transl_program_correct.
     apply BuiltinEffects.get_helpers_correct. apply HelpersOK.
     unfold SelectionNEW.sel_program. unfold bind.
     rewrite HelpersOK. trivial.
     assumption.
     exists m0. eassumption.
  unfold SelectionNEW.sel_program in Heqr. unfold bind in Heqr.
     rewrite HelpersOK in Heqr. inv Heqr. 
  eapply Genv.init_mem_transf in INIT. 
  eapply TransformLNR in LNR.   
  eapply eff_sim_trans.
    eapply RTLgenproofEFF.transl_program_correct.
     eassumption.
     eassumption.
     exists m0. apply INIT.
  eapply Genv.init_mem_transf_partial in INIT. 2: eauto.
  eapply TransformLNR_partial in LNR.  
    eapply transf_rtl_program_correct; try eassumption. 
    unfold  RTLgen.transl_program in Heqr0. eassumption. 
Qed.

Theorem transf_clight_program_correct:
  forall p tp m0 (INIT: Genv.init_mem p = Some m0)
  (LNR: list_norepet (map fst (prog_defs p))),
  transf_clight_program p = OK tp ->
  SM_simulation.SM_simulation_inject (CL_eff_sem1 hf) 
      (Asm_eff_sem hf)
      (Genv.globalenv p) (Genv.globalenv tp).
Proof.
  intros.
  unfold transf_clight_program in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  destruct (SimplLocals.transf_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (Cshmgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.
  destruct (Cminorgen.transl_program p2) as [p3|] eqn:?; simpl in H; try discriminate.
  eapply eff_sim_trans.
    eapply SimplLocalsproofEFF.transl_program_correct. eassumption.
     eassumption. 
     exists m0; eassumption.
  eapply Genv.init_mem_transf_partial in INIT. 2: eauto.
  eapply TransformLNR_partial in LNR. 2: eauto.
  eapply eff_sim_trans.
    eapply CshmgenproofEFF.transl_program_correct. 
    eassumption.
    eassumption.
    exists m0; eassumption.
 
  eapply Genv.init_mem_transf_partial2 in INIT. Focus 2. eapply Heqr0. 
  eapply TransformLNR_partial2 in LNR. 2: eauto.
   
  eapply eff_sim_trans.
    eapply CminorgenproofEFF.transl_program_correct. 
    eassumption.
    eassumption.
    exists m0; eassumption. 
  eapply Genv.init_mem_transf_partial in INIT. 2: eauto.
  eapply TransformLNR_partial in LNR. 2: eauto.
  eapply transf_cminor_program_correct; eassumption. 
Qed.
