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

(** Correctness proof for common subexpression elimination. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Errors.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import RTLtyping.
Require Import Kildall.
Require Import CombineOp.
Require Import CombineOpproof.
Require Import CSE.

Require Import Integers.

Require Import Axioms.
Require Import mem_lemmas.
(*Require Import core_semantics.
Require Import core_semantics_lemmas.*)
Require Import semantics.
Require Import structured_injections.
Require Import reach.
Require Import effect_semantics.
Require Import simulations.
Require Import effect_properties.
Require Import simulations_lemmas.

Require Import RTL_coop.
Require Import BuiltinEffects.
Require Import RTL_eff.

(** * Semantic properties of value numberings *)

(** ** Well-formedness of numberings *)

(** A numbering is well-formed if all registers mentioned in equations
  are less than the ``next'' register number given in the numbering.
  This guarantees that the next register is fresh with respect to
  the equations. *)

Definition wf_rhs (next: valnum) (rh: rhs) : Prop :=
  match rh with
  | Op op vl => forall v, In v vl -> Plt v next
  | Load chunk addr vl => forall v, In v vl -> Plt v next
  end.

Definition wf_equation (next: valnum) (vr: valnum) (rh: rhs) : Prop :=
  Plt vr next /\ wf_rhs next rh.

Inductive wf_numbering (n: numbering) : Prop :=
  wf_numbering_intro
    (EQS: forall v rh,
          In (v, rh) n.(num_eqs) -> wf_equation n.(num_next) v rh)
    (REG: forall r v,
          PTree.get r n.(num_reg) = Some v -> Plt v n.(num_next))
    (VAL: forall r v,
          In r (PMap.get v n.(num_val)) -> PTree.get r n.(num_reg) = Some v).

Lemma wf_empty_numbering:
  wf_numbering empty_numbering.
Proof.
  unfold empty_numbering; split; simpl; intros.
  contradiction.
  rewrite PTree.gempty in H. congruence.
  rewrite PMap.gi in H. contradiction. 
Qed.

Lemma wf_rhs_increasing:
  forall next1 next2 rh,
  Ple next1 next2 ->
  wf_rhs next1 rh -> wf_rhs next2 rh.
Proof.
  intros; destruct rh; simpl; intros; apply Plt_Ple_trans with next1; auto.
Qed.

Lemma wf_equation_increasing:
  forall next1 next2 vr rh,
  Ple next1 next2 ->
  wf_equation next1 vr rh -> wf_equation next2 vr rh.
Proof.
  intros. destruct H0. split. 
  apply Plt_Ple_trans with next1; auto.
  apply wf_rhs_increasing with next1; auto.
Qed.

(** We now show that all operations over numberings 
  preserve well-formedness. *)

Lemma wf_valnum_reg:
  forall n r n' v,
  wf_numbering n ->
  valnum_reg n r = (n', v) ->
  wf_numbering n' /\ Plt v n'.(num_next) /\ Ple n.(num_next) n'.(num_next).
Proof.
  intros until v. unfold valnum_reg. intros WF VREG. inversion WF.
  destruct ((num_reg n)!r) as [v'|] eqn:?.
(* found *)
  inv VREG. split. auto. split. eauto. apply Ple_refl.
(* not found *)
  inv VREG. split. 
  split; simpl; intros.
  apply wf_equation_increasing with (num_next n). apply Ple_succ. auto. 
  rewrite PTree.gsspec in H. destruct (peq r0 r).
  inv H. apply Plt_succ.
  apply Plt_trans_succ; eauto.
  rewrite PMap.gsspec in H. destruct (peq v (num_next n)). 
  subst v. simpl in H. destruct H. subst r0. apply PTree.gss. contradiction.
  rewrite PTree.gso. eauto. exploit VAL; eauto. congruence. 
  simpl. split. apply Plt_succ. apply Ple_succ.
Qed.

Lemma wf_valnum_regs:
  forall rl n n' vl,
  wf_numbering n ->
  valnum_regs n rl = (n', vl) ->
  wf_numbering n' /\
  (forall v, In v vl -> Plt v n'.(num_next)) /\
  Ple n.(num_next) n'.(num_next).
Proof.
  induction rl; intros.
  simpl in H0. inversion H0. subst n'; subst vl. 
  simpl. intuition. 
  simpl in H0. 
  caseEq (valnum_reg n a). intros n1 v1 EQ1.
  caseEq (valnum_regs n1 rl). intros ns vs EQS.
  rewrite EQ1 in H0; rewrite EQS in H0; simpl in H0.
  inversion H0. subst n'; subst vl. 
  generalize (wf_valnum_reg _ _ _ _ H EQ1); intros [A1 [B1 C1]].
  generalize (IHrl _ _ _ A1 EQS); intros [As [Bs Cs]].
  split. auto.
  split. simpl; intros. elim H1; intro.
    subst v. eapply Plt_Ple_trans; eauto.
    auto.
  eapply Ple_trans; eauto.
Qed.

Lemma find_valnum_rhs_correct:
  forall rh vn eqs,
  find_valnum_rhs rh eqs = Some vn -> In (vn, rh) eqs.
Proof.
  induction eqs; simpl.
  congruence.
  case a; intros v r'. case (eq_rhs rh r'); intro.
  intro. left. congruence.
  intro. right. auto.
Qed.

Lemma find_valnum_num_correct:
  forall rh vn eqs,
  find_valnum_num vn eqs = Some rh -> In (vn, rh) eqs.
Proof.
  induction eqs; simpl.
  congruence.
  destruct a as [v' r']. destruct (peq vn v'); intros. 
  left. congruence.
  right. auto.
Qed.

Remark in_remove:
  forall (A: Type) (eq: forall (x y: A), {x=y}+{x<>y}) x y l,
  In y (List.remove eq x l) <-> x <> y /\ In y l.
Proof.
  induction l; simpl. 
  tauto.
  destruct (eq x a). 
  subst a. rewrite IHl. tauto. 
  simpl. rewrite IHl. intuition congruence.
Qed.

Lemma wf_forget_reg:
  forall n rd r v,
  wf_numbering n ->
  In r (PMap.get v (forget_reg n rd)) -> r <> rd /\ PTree.get r n.(num_reg) = Some v.
Proof.
  unfold forget_reg; intros. inversion H. 
  destruct ((num_reg n)!rd) as [vd|] eqn:?. 
  rewrite PMap.gsspec in H0. destruct (peq v vd). 
  subst vd. rewrite in_remove in H0. destruct H0. split. auto. eauto. 
  split; eauto. exploit VAL; eauto. congruence. 
  split; eauto. exploit VAL; eauto. congruence.
Qed.

Lemma wf_update_reg:
  forall n rd vd r v,
  wf_numbering n ->
  In r (PMap.get v (update_reg n rd vd)) -> PTree.get r (PTree.set rd vd n.(num_reg)) = Some v.
Proof.
  unfold update_reg; intros. inversion H. rewrite PMap.gsspec in H0. 
  destruct (peq v vd). 
  subst v; simpl in H0. destruct H0. 
  subst r. apply PTree.gss. 
  exploit wf_forget_reg; eauto. intros [A B]. rewrite PTree.gso; eauto. 
  exploit wf_forget_reg; eauto. intros [A B]. rewrite PTree.gso; eauto. 
Qed.

Lemma wf_add_rhs:
  forall n rd rh,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  wf_numbering (add_rhs n rd rh).
Proof.
  intros. inversion H. unfold add_rhs. 
  destruct (find_valnum_rhs rh n.(num_eqs)) as [vres|] eqn:?.
(* found *)
  exploit find_valnum_rhs_correct; eauto. intros IN. 
  split; simpl; intros. 
  auto.
  rewrite PTree.gsspec in H1. destruct (peq r rd). 
  inv H1. exploit EQS; eauto. intros [A B]. auto. 
  eauto. 
  eapply wf_update_reg; eauto. 
(* not found *)
  split; simpl; intros.
  destruct H1.
  inv H1. split. apply Plt_succ. apply wf_rhs_increasing with n.(num_next). apply Ple_succ. auto.
  apply wf_equation_increasing with n.(num_next). apply Ple_succ. auto.
  rewrite PTree.gsspec in H1. destruct (peq r rd). 
  inv H1. apply Plt_succ.
  apply Plt_trans_succ. eauto. 
  eapply wf_update_reg; eauto. 
Qed.

Lemma wf_add_op:
  forall n rd op rs,
  wf_numbering n ->
  wf_numbering (add_op n rd op rs).
Proof.
  intros. unfold add_op. destruct (is_move_operation op rs) as [r|] eqn:?.
(* move *)
  destruct (valnum_reg n r) as [n' v] eqn:?.
  exploit wf_valnum_reg; eauto. intros [A [B C]]. inversion A.
  constructor; simpl; intros.
  eauto.
  rewrite PTree.gsspec in H0. destruct (peq r0 rd). inv H0. auto. eauto.
  eapply wf_update_reg; eauto. 
(* not a move *)
  destruct (valnum_regs n rs) as [n' vs] eqn:?.
  exploit wf_valnum_regs; eauto. intros [A [B C]].
  eapply wf_add_rhs; eauto.
Qed.

Lemma wf_add_load:
  forall n rd chunk addr rs,
  wf_numbering n ->
  wf_numbering (add_load n rd chunk addr rs).
Proof.
  intros. unfold add_load. 
  caseEq (valnum_regs n rs). intros n' vl EQ. 
  generalize (wf_valnum_regs _ _ _ _ H EQ). intros [A [B C]].
  apply wf_add_rhs; auto.
Qed.

Lemma wf_add_unknown:
  forall n rd,
  wf_numbering n ->
  wf_numbering (add_unknown n rd).
Proof.
  intros. inversion H. unfold add_unknown. constructor; simpl; intros.
  eapply wf_equation_increasing; eauto. auto with coqlib. 
  rewrite PTree.gsspec in H0. destruct (peq r rd). 
  inv H0. auto with coqlib.
  apply Plt_trans_succ; eauto.
  exploit wf_forget_reg; eauto. intros [A B]. rewrite PTree.gso; eauto.
Qed.

Remark kill_eqs_in:
  forall pred v rhs eqs,
  In (v, rhs) (kill_eqs pred eqs) -> In (v, rhs) eqs /\ pred rhs = false.
Proof.
  induction eqs; simpl; intros. 
  tauto.
  destruct (pred (snd a)) eqn:?. 
  exploit IHeqs; eauto. tauto. 
  simpl in H; destruct H. subst a. auto. exploit IHeqs; eauto. tauto. 
Qed.

Lemma wf_kill_equations:
  forall pred n, wf_numbering n -> wf_numbering (kill_equations pred n).
Proof.
  intros. inversion H. unfold kill_equations; split; simpl; intros.
  exploit kill_eqs_in; eauto. intros [A B]. auto. 
  eauto.
  eauto.
Qed.

Lemma wf_add_store:
  forall n chunk addr rargs rsrc,
  wf_numbering n -> wf_numbering (add_store n chunk addr rargs rsrc).
Proof.
  intros. unfold add_store. 
  destruct (valnum_regs n rargs) as [n1 vargs] eqn:?.
  exploit wf_valnum_regs; eauto. intros [A [B C]].
  assert (wf_numbering (kill_equations (filter_after_store chunk addr vargs) n1)).
    apply wf_kill_equations. auto.
  destruct chunk; auto; apply wf_add_rhs; auto.
Qed.

Lemma wf_transfer:
  forall f pc n, wf_numbering n -> wf_numbering (transfer f pc n).
Proof.
  intros. unfold transfer. 
  destruct (f.(fn_code)!pc); auto.
  destruct i; auto.
  apply wf_add_op; auto.
  apply wf_add_load; auto.
  apply wf_add_store; auto.
  apply wf_empty_numbering.
  apply wf_empty_numbering.
  destruct e; (apply wf_empty_numbering ||
               apply wf_add_unknown; auto; apply wf_kill_equations; auto).
Qed.

(** As a consequence, the numberings computed by the static analysis
  are well formed. *)

Theorem wf_analyze:
  forall f approx pc, analyze f = Some approx -> wf_numbering approx!!pc.
Proof.
  unfold analyze; intros.
  eapply Solver.fixpoint_invariant with (P := wf_numbering); eauto.
  exact wf_empty_numbering.   
  intros. eapply wf_transfer; eauto. 
Qed.

(** ** Properties of satisfiability of numberings *)

Module ValnumEq.
  Definition t := valnum.
  Definition eq := peq.
End ValnumEq.

Module VMap := EMap(ValnumEq).

Section SATISFIABILITY.

Variable ge: genv.
Variable sp: val.

(** Agremment between two mappings from value numbers to values
  up to a given value number. *)

Definition valu_agree (valu1 valu2: valnum -> val) (upto: valnum) : Prop :=
  forall v, Plt v upto -> valu2 v = valu1 v.

Lemma valu_agree_refl:
  forall valu upto, valu_agree valu valu upto.
Proof.
  intros; red; auto.
Qed.

Lemma valu_agree_trans:
  forall valu1 valu2 valu3 upto12 upto23,
  valu_agree valu1 valu2 upto12 ->
  valu_agree valu2 valu3 upto23 ->
  Ple upto12 upto23 ->
  valu_agree valu1 valu3 upto12.
Proof.
  intros; red; intros. transitivity (valu2 v).
  apply H0. apply Plt_Ple_trans with upto12; auto.
  apply H; auto.
Qed.

Lemma valu_agree_list:
  forall valu1 valu2 upto vl,
  valu_agree valu1 valu2 upto ->
  (forall v, In v vl -> Plt v upto) ->
  map valu2 vl = map valu1 vl.
Proof.
  intros. apply list_map_exten. intros. symmetry. apply H. auto.
Qed.

(** The [numbering_holds] predicate (defined in file [CSE]) is
  extensional with respect to [valu_agree]. *)

Lemma numbering_holds_exten:
  forall valu1 valu2 n rs m,
  valu_agree valu1 valu2 n.(num_next) ->
  wf_numbering n ->
  numbering_holds valu1 ge sp rs m n ->
  numbering_holds valu2 ge sp rs m n.
Proof.
  intros. inversion H0. inversion H1. split; intros.
  exploit EQS; eauto. intros [A B]. red in B.
  generalize (H2 _ _ H4).
  unfold equation_holds; destruct rh.
  rewrite (valu_agree_list valu1 valu2 n.(num_next)). 
  rewrite H. auto. auto. auto. auto.
  rewrite (valu_agree_list valu1 valu2 n.(num_next)). 
  rewrite H. auto. auto. auto. auto. 
  rewrite H. auto. eauto.
Qed.

(** [valnum_reg] and [valnum_regs] preserve the [numbering_holds] predicate.
  Moreover, it is always the case that the returned value number has
  the value of the given register in the final assignment of values to
  value numbers. *)

Lemma valnum_reg_holds:
  forall valu1 rs n r n' v m,
  wf_numbering n ->
  numbering_holds valu1 ge sp rs m n ->
  valnum_reg n r = (n', v) ->
  exists valu2,
    numbering_holds valu2 ge sp rs m n' /\
    valu2 v = rs#r /\
    valu_agree valu1 valu2 n.(num_next).
Proof.
  intros until v. unfold valnum_reg. 
  caseEq (n.(num_reg)!r).
  (* Register already has a value number *)
  intros. inversion H2. subst n'; subst v0. 
  inversion H1. 
  exists valu1. split. auto. 
  split. symmetry. auto.
  apply valu_agree_refl.
  (* Register gets a fresh value number *)
  intros. inversion H2. subst n'. subst v. inversion H1.
  set (valu2 := VMap.set n.(num_next) rs#r valu1).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
    red; intros. unfold valu2. apply VMap.gso. 
    auto with coqlib.
  destruct (numbering_holds_exten _ _ _ _ _ AG H0 H1) as [A B].
  exists valu2. 
  split. split; simpl; intros. auto. 
  unfold valu2, VMap.set, ValnumEq.eq. 
  rewrite PTree.gsspec in H5. destruct (peq r0 r).
  inv H5. rewrite peq_true. auto.
  rewrite peq_false. auto. 
  assert (Plt vn (num_next n)). inv H0. eauto. 
  red; intros; subst; eapply Plt_strict; eauto. 
  split. unfold valu2. rewrite VMap.gss. auto. 
  auto.
Qed.

Lemma valnum_regs_holds:
  forall rs rl valu1 n n' vl m,
  wf_numbering n ->
  numbering_holds valu1 ge sp rs m n ->
  valnum_regs n rl = (n', vl) ->
  exists valu2,
    numbering_holds valu2 ge sp rs m n' /\
    List.map valu2 vl = rs##rl /\
    valu_agree valu1 valu2 n.(num_next).
Proof.
  induction rl; simpl; intros.
  (* base case *)
  inversion H1; subst n'; subst vl.
  exists valu1. split. auto. split. auto. apply valu_agree_refl.
  (* inductive case *)
  caseEq (valnum_reg n a); intros n1 v1 EQ1.
  caseEq (valnum_regs n1 rl); intros ns vs EQs.
  rewrite EQ1 in H1; rewrite EQs in H1. inversion H1. subst vl; subst n'.
  generalize (valnum_reg_holds _ _ _ _ _ _ _ H H0 EQ1).
  intros [valu2 [A [B C]]].
  generalize (wf_valnum_reg _ _ _ _ H EQ1). intros [D [E F]].
  generalize (IHrl _ _ _ _ _ D A EQs). 
  intros [valu3 [P [Q R]]].
  exists valu3. 
  split. auto. 
  split. simpl. rewrite R. congruence. auto.
  eapply valu_agree_trans; eauto.
Qed.

(** A reformulation of the [equation_holds] predicate in terms
  of the value to which a right-hand side of an equation evaluates. *)

Definition rhs_evals_to
    (valu: valnum -> val) (rh: rhs) (m: mem) (v: val) : Prop :=
  match rh with
  | Op op vl => 
      eval_operation ge sp op (List.map valu vl) m = Some v
  | Load chunk addr vl =>
      exists a,
      eval_addressing ge sp addr (List.map valu vl) = Some a /\
      Mem.loadv chunk m a = Some v
  end.

Lemma equation_evals_to_holds_1:
  forall valu rh v vres m,
  rhs_evals_to valu rh m v ->
  equation_holds valu ge sp m vres rh ->
  valu vres = v.
Proof.
  intros until m. unfold rhs_evals_to, equation_holds.
  destruct rh. congruence.
  intros [a1 [A1 B1]] [a2 [A2 B2]]. congruence.
Qed.

Lemma equation_evals_to_holds_2:
  forall valu rh v vres m,
  wf_rhs vres rh ->
  rhs_evals_to valu rh m v ->
  equation_holds (VMap.set vres v valu) ge sp m vres rh.
Proof.
  intros until m. unfold wf_rhs, rhs_evals_to, equation_holds.
  rewrite VMap.gss. 
  assert (forall vl: list valnum,
            (forall v, In v vl -> Plt v vres) ->
            map (VMap.set vres v valu) vl = map valu vl).
    intros. apply list_map_exten. intros. 
    symmetry. apply VMap.gso. apply Plt_ne. auto.
  destruct rh; intros; rewrite H; auto.
Qed.

(** The numbering obtained by adding an equation [rd = rhs] is satisfiable
  in a concrete register set where [rd] is set to the value of [rhs]. *)

Lemma add_rhs_satisfiable_gen:
  forall n rh valu1 rs rd rs' m,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  numbering_holds valu1 ge sp rs m n ->
  rhs_evals_to valu1 rh m (rs'#rd) ->
  (forall r, r <> rd -> rs'#r = rs#r) ->
  numbering_satisfiable ge sp rs' m (add_rhs n rd rh).
Proof.
  intros. unfold add_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)).
  (* RHS found *)
  intros vres FINDVN. inversion H1.
  exists valu1. split; simpl; intros.
  auto. 
  rewrite PTree.gsspec in H6.
  destruct (peq r rd).
  inv H6. 
  symmetry. eapply equation_evals_to_holds_1; eauto.
  apply H4. apply find_valnum_rhs_correct. congruence.
  rewrite H3; auto.
  (* RHS not found *)
  intro FINDVN. 
  set (valu2 := VMap.set n.(num_next) (rs'#rd) valu1).
  assert (AG: valu_agree valu1 valu2 n.(num_next)).
    red; intros. unfold valu2. apply VMap.gso. 
    auto with coqlib.
  elim (numbering_holds_exten _ _ _ _ _ AG H H1); intros.
  exists valu2. split; simpl; intros.
  destruct H6. 
  inv H6. unfold valu2. eapply equation_evals_to_holds_2; eauto. auto. 
  rewrite PTree.gsspec in H6. destruct (peq r rd).
  unfold valu2. inv H6. rewrite VMap.gss. auto.
  rewrite H3; auto.
Qed.

Lemma add_rhs_satisfiable:
  forall n rh valu1 rs rd v m,
  wf_numbering n ->
  wf_rhs n.(num_next) rh ->
  numbering_holds valu1 ge sp rs m n ->
  rhs_evals_to valu1 rh m v ->
  numbering_satisfiable ge sp (rs#rd <- v) m (add_rhs n rd rh).
Proof.
  intros. eapply add_rhs_satisfiable_gen; eauto. 
  rewrite Regmap.gss; auto.
  intros. apply Regmap.gso; auto.
Qed.

(** [add_op] returns a numbering that is satisfiable in the register
  set after execution of the corresponding [Iop] instruction. *)

Lemma add_op_satisfiable:
  forall n rs op args dst v m,
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  eval_operation ge sp op rs##args m = Some v ->
  numbering_satisfiable ge sp (rs#dst <- v) m (add_op n dst op args).
Proof.
  intros. inversion H0.
  unfold add_op.
  caseEq (@is_move_operation reg op args).
  intros arg EQ. 
  destruct (is_move_operation_correct _ _ EQ) as [A B]. subst op args.
  caseEq (valnum_reg n arg). intros n1 v1 VL.
  generalize (valnum_reg_holds _ _ _ _ _ _ _ H H2 VL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_reg _ _ _ _ H VL). intros [D [E F]].  
  elim A; intros. exists valu2; split; simpl; intros.
  auto. rewrite Regmap.gsspec. rewrite PTree.gsspec in H5.
  destruct (peq r dst). simpl in H1. congruence. auto.
  intro NEQ. caseEq (valnum_regs n args). intros n1 vl VRL.
  generalize (valnum_regs_holds _ _ _ _ _ _ _ H H2 VRL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_regs _ _ _ _ H VRL). intros [D [E F]].
  apply add_rhs_satisfiable with valu2; auto.
  simpl. congruence. 
Qed.

(** [add_load] returns a numbering that is satisfiable in the register
  set after execution of the corresponding [Iload] instruction. *)

Lemma add_load_satisfiable:
  forall n rs chunk addr args dst a v m,
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.loadv chunk m a = Some v ->
  numbering_satisfiable ge sp (rs#dst <- v) m (add_load n dst chunk addr args).
Proof.
  intros. inversion H0.
  unfold add_load.
  caseEq (valnum_regs n args). intros n1 vl VRL.
  generalize (valnum_regs_holds _ _ _ _ _ _ _ H H3 VRL). intros [valu2 [A [B C]]].
  generalize (wf_valnum_regs _ _ _ _ H VRL). intros [D [E F]].
  apply add_rhs_satisfiable with valu2; auto.
  simpl. exists a; split; congruence. 
Qed.

(** [add_unknown] returns a numbering that is satisfiable in the
  register set after setting the target register to any value. *)

Lemma add_unknown_satisfiable:
  forall n rs dst v m,
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  numbering_satisfiable ge sp (rs#dst <- v) m (add_unknown n dst).
Proof.
  intros. destruct H0 as [valu A]. 
  set (valu' := VMap.set n.(num_next) v valu).
  assert (numbering_holds valu' ge sp rs m n). 
    eapply numbering_holds_exten; eauto.
    unfold valu'; red; intros. apply VMap.gso. auto with coqlib.
  destruct H0 as [B C].
  exists valu'; split; simpl; intros.
  eauto.
  rewrite PTree.gsspec in H0. rewrite Regmap.gsspec. 
  destruct (peq r dst). inversion H0. unfold valu'. rewrite VMap.gss; auto.
  eauto.
Qed.

(** Satisfiability of [kill_equations]. *)

Lemma kill_equations_holds:
  forall pred valu n rs m m',
  (forall v r,
   equation_holds valu ge sp m v r -> pred r = false -> equation_holds valu ge sp m' v r) ->
  numbering_holds valu ge sp rs m n ->
  numbering_holds valu ge sp rs m' (kill_equations pred n).
Proof.
  intros. destruct H0 as [A B]. red; simpl. split; intros. 
  exploit kill_eqs_in; eauto. intros [C D]. eauto. 
  auto.
Qed.

(** [kill_loads] preserves satisfiability.  Moreover, the resulting numbering
  is satisfiable in any concrete memory state. *)

Lemma kill_loads_satisfiable:
  forall n rs m m',
  numbering_satisfiable ge sp rs m n ->
  numbering_satisfiable ge sp rs m' (kill_loads n).
Proof.
  intros. destruct H as [valu A]. exists valu. eapply kill_equations_holds with (m := m); eauto.
  intros. destruct r; simpl in *. rewrite <- H. apply op_depends_on_memory_correct; auto. 
  congruence.
Qed.

(** [add_store] returns a numbering that is satisfiable in the memory state
  after execution of the corresponding [Istore] instruction. *)

Lemma add_store_satisfiable:
  forall n rs chunk addr args src a m m',
  wf_numbering n ->
  numbering_satisfiable ge sp rs m n ->
  eval_addressing ge sp addr rs##args = Some a ->
  Mem.storev chunk m a (rs#src) = Some m' ->
  Val.has_type (rs#src) (type_of_chunk_use chunk) ->
  numbering_satisfiable ge sp rs m' (add_store n chunk addr args src).
Proof.
  intros. unfold add_store. destruct H0 as [valu A].
  destruct (valnum_regs n args) as [n1 vargs] eqn:?.
  exploit valnum_regs_holds; eauto. intros [valu' [B [C D]]].
  exploit wf_valnum_regs; eauto. intros [U [V W]].
  set (n2 := kill_equations (filter_after_store chunk addr vargs) n1).
  assert (numbering_holds valu' ge sp rs m' n2).
    apply kill_equations_holds with (m := m); auto.
    intros. destruct r; simpl in *. 
    rewrite <- H0. apply op_depends_on_memory_correct; auto.
    destruct H0 as [a' [P Q]]. 
    destruct (eq_list_valnum vargs l); simpl in H4; try congruence. subst l.
    rewrite negb_false_iff in H4.
    exists a'; split; auto. 
    destruct a; simpl in H2; try congruence.
    destruct a'; simpl in Q; try congruence.
    simpl. rewrite <- Q. 
    rewrite C in P. eapply Mem.load_store_other; eauto.
    exploit addressing_separated_sound; eauto. intuition congruence.
  assert (N2: numbering_satisfiable ge sp rs m' n2).
    exists valu'; auto.
  set (n3 := add_rhs n2 src (Load chunk addr vargs)).
  assert (N3: Val.load_result chunk (rs#src) = rs#src -> numbering_satisfiable ge sp rs m' n3).
    intro EQ. unfold n3. apply add_rhs_satisfiable_gen with valu' rs.
    apply wf_kill_equations; auto.
    red. auto. auto.
    red. exists a; split. congruence. 
    rewrite <- EQ. destruct a; simpl in H2; try discriminate. simpl. 
    eapply Mem.load_store_same; eauto. 
    auto.
  destruct chunk; auto; apply N3. 
  simpl in H3. destruct (rs#src); auto || contradiction.
  simpl in H3. destruct (rs#src); auto || contradiction.
  simpl in H3. destruct (rs#src); auto || contradiction.
  simpl in H3. destruct (rs#src); auto || contradiction.
Qed.

(** Correctness of [reg_valnum]: if it returns a register [r],
  that register correctly maps back to the given value number. *)

Lemma reg_valnum_correct:
  forall n v r, wf_numbering n -> reg_valnum n v = Some r -> n.(num_reg)!r = Some v.
Proof.
  unfold reg_valnum; intros. inv H. 
  destruct ((num_val n)#v) as [| r1 rl] eqn:?; inv H0. 
  eapply VAL. rewrite Heql. auto with coqlib.
Qed.

(** Correctness of [find_rhs]: if successful and in a
  satisfiable numbering, the returned register does contain the 
  result value of the operation or memory load. *)

Lemma find_rhs_correct:
  forall valu rs m n rh r,
  wf_numbering n ->
  numbering_holds valu ge sp rs m n ->
  find_rhs n rh = Some r ->
  rhs_evals_to valu rh m rs#r.
Proof.
  intros until r. intros WF NH. 
  unfold find_rhs. 
  caseEq (find_valnum_rhs rh n.(num_eqs)); intros.
  exploit find_valnum_rhs_correct; eauto. intros.
  exploit reg_valnum_correct; eauto. intros.
  inversion NH. 
  generalize (H3 _ _ H1). rewrite (H4 _ _ H2). 
  destruct rh; simpl; auto.
  discriminate.
Qed.

(** Correctness of operator reduction *)

Section REDUCE.

Variable A: Type.
Variable f: (valnum -> option rhs) -> A -> list valnum -> option (A * list valnum).
Variable V: Type.
Variable rs: regset.
Variable m: mem.
Variable sem: A -> list val -> option V.
Hypothesis f_sound:
  forall eqs valu op args op' args',
  (forall v rhs, eqs v = Some rhs -> equation_holds valu ge sp m v rhs) ->
  f eqs op args = Some(op', args') ->
  sem op' (map valu args') = sem op (map valu args).
Variable n: numbering.
Variable valu: valnum -> val.
Hypothesis n_holds: numbering_holds valu ge sp rs m n.
Hypothesis n_wf: wf_numbering n.

Lemma regs_valnums_correct:
  forall vl rl, regs_valnums n vl = Some rl -> rs##rl = map valu vl.
Proof.
  induction vl; simpl; intros.
  inv H. auto.
  destruct (reg_valnum n a) as [r1|] eqn:?; try discriminate.
  destruct (regs_valnums n vl) as [rx|] eqn:?; try discriminate.
  inv H. simpl; decEq; auto. 
  eapply (proj2 n_holds); eauto. eapply reg_valnum_correct; eauto.
Qed.

Lemma reduce_rec_sound:
  forall niter op args op' rl' res,
  reduce_rec A f n niter op args = Some(op', rl') ->
  sem op (map valu args) = Some res ->
  sem op' (rs##rl') = Some res.
Proof.
  induction niter; simpl; intros.
  discriminate.
  destruct (f (fun v : valnum => find_valnum_num v (num_eqs n)) op args)
           as [[op1 args1] | ] eqn:?.
  assert (sem op1 (map valu args1) = Some res).
    rewrite <- H0. eapply f_sound; eauto.
    simpl; intros. apply (proj1 n_holds). eapply find_valnum_num_correct; eauto. 
  destruct (reduce_rec A f n niter op1 args1) as [[op2 rl2] | ] eqn:?.
  inv H. eapply IHniter; eauto.
  destruct (regs_valnums n args1) as [rl|] eqn:?.
  inv H. erewrite regs_valnums_correct; eauto.
  discriminate.
  discriminate.
Qed.

Lemma reduce_sound:
  forall op rl vl op' rl' res,
  reduce A f n op rl vl = (op', rl') ->
  map valu vl = rs##rl ->
  sem op rs##rl = Some res ->
  sem op' rs##rl' = Some res.
Proof.
  unfold reduce; intros. 
  destruct (reduce_rec A f n 4%nat op vl) as [[op1 rl1] | ] eqn:?; inv H.
  eapply reduce_rec_sound; eauto. congruence.
  auto.
Qed.

End REDUCE.

End SATISFIABILITY.

(** The numberings associated to each instruction by the static analysis
  are inductively satisfiable, in the following sense: the numbering
  at the function entry point is satisfiable, and for any RTL execution 
  from [pc] to [pc'], satisfiability at [pc] implies 
  satisfiability at [pc']. *)

Theorem analysis_correct_1:
  forall ge sp rs m f approx pc pc' i,
  analyze f = Some approx ->
  f.(fn_code)!pc = Some i -> In pc' (successors_instr i) ->
  numbering_satisfiable ge sp rs m (transfer f pc approx!!pc) ->
  numbering_satisfiable ge sp rs m approx!!pc'.
Proof.
  intros.
  assert (Numbering.ge approx!!pc' (transfer f pc approx!!pc)).
    eapply Solver.fixpoint_solution; eauto.
  apply H3. auto.
Qed.

Theorem analysis_correct_entry:
  forall ge sp rs m f approx,
  analyze f = Some approx ->
  numbering_satisfiable ge sp rs m approx!!(f.(fn_entrypoint)).
Proof.
  intros. 
  replace (approx!!(f.(fn_entrypoint))) with Solver.L.top.
  apply empty_numbering_satisfiable.
  symmetry. eapply Solver.fixpoint_entry; eauto.
Qed.

(*LENB: copied the notion of register agreement from TailcallproofEFF*)
Definition regset_inject j (rs rs': regset) : Prop :=
  forall r, val_inject j (rs#r) (rs'#r).

Lemma regset_get_list j:
  forall rs rs' l,
  regset_inject j rs rs' -> val_list_inject j (rs##l) (rs'##l).
Proof.
  induction l; simpl; intros; constructor; auto.
Qed.

Lemma regset_set j:
  forall rs rs' v v' r,
  regset_inject j rs rs' -> val_inject j v v' ->
  regset_inject j (rs#r <- v) (rs'#r <- v').
Proof.
  intros; red; intros. repeat rewrite PMap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma regset_init_regs j:
  forall params vl vl',
  val_list_inject j vl vl' ->
  regset_inject j (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply regset_set. auto. auto.
Qed.

Lemma regset_incr j:
  forall rs rs' j' (RI: regset_inject j rs rs')
 (INC: inject_incr j j'), regset_inject j' rs rs'. 
Proof.
  intros. red; intros.
  eapply val_inject_incr; eauto.
Qed.

Definition RHS_max mx (rh:rhs):Prop :=
  match rh with 
   Op _ l => forall a, In a l -> Plt a mx
  | Load _ _ l => forall a, In a l -> Plt a mx
  end.

(** * Semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Variable tprog : program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf_partial transf_fundef prog TRANSF).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf_partial transf_fundef prog TRANSF).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial transf_fundef prog TRANSF).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial transf_fundef prog TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> funsig tf = funsig f.
Proof.
  unfold transf_fundef; intros. destruct f; monadInv H; auto.
  unfold transf_function in EQ. destruct (type_function f); try discriminate. 
  destruct (analyze f); try discriminate. inv EQ; auto. 
Qed.

Lemma find_function_translated:
  forall ros rs f,
  find_function ge ros rs = Some f ->
  exists tf, find_function tge ros rs = Some tf /\ transf_fundef f = OK tf.
Proof.
  intros until f; destruct ros; simpl.
  intro. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intro.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

Lemma find_function_preserved' mu rs rs' ros fd tf: forall
        (FIND: find_function ge ros rs = Some fd)
        (GFP : globalfunction_ptr_inject ge (as_inj mu))
        (RI : regset_inject (restrict (as_inj mu) (vis mu)) rs rs')
        (TF : transf_fundef fd = OK tf),
   find_function tge ros rs' = Some tf.
Proof. intros.
    unfold find_function, Genv.find_funct in FIND.
    unfold find_function, Genv.find_funct.
    destruct ros.
      specialize (RI r). destruct (rs # r); inv FIND. inv RI.
      destruct (Int.eq_dec i Int.zero); inv H0. 
      destruct (GFP _ _ H1).
      destruct (restrictD_Some _ _ _ _ _ H3).
      rewrite H4 in H; inv H. rewrite Int.add_zero.
      destruct (funct_ptr_translated _ _ H1) as [? [? ?]].
      rewrite H. rewrite H6 in TF; inv TF.
      destruct (Int.eq_dec Int.zero Int.zero); trivial. elim n; trivial.
    rewrite symbols_preserved.
      destruct (Genv.find_symbol ge i); inv FIND. 
      destruct (funct_ptr_translated _ _ H0) as [? [? ?]].
      rewrite H1 in TF; inv TF. trivial.
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    split. intros. rewrite varinfo_preserved. intuition.
    intros. split.
      intros [f H].
        apply funct_ptr_translated in H. 
        destruct H as [? [? _]]. 
        eexists; eassumption.
     intros [f H]. 
         apply (@Genv.find_funct_ptr_rev_transf_partial
           _ _ _ transf_fundef prog _ TRANSF) in H.
         destruct H as [? [? _]]. eexists; eassumption.
Qed.         

Definition transf_function' (f: function) (approxs: PMap.t numbering) : function :=
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (transf_code approxs f.(fn_code))
    f.(fn_entrypoint).

(** The proof of semantic preservation is a simulation argument using
  diagrams of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                   |t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Left: RTL execution in the original program.  Right: RTL execution in
  the optimized program.  Precondition (top) and postcondition (bottom):
  agreement between the states, including the fact that
  the numbering at [pc] (returned by the static analysis) is satisfiable.
*)

Definition SPlocal mu sp sp':= 
  exists spb spb', sp=Vptr spb Int.zero /\ 
                   sp'=Vptr spb' Int.zero /\
                   local_of mu spb = Some(spb',0).

Inductive match_stackframes mu: 
          list stackframe -> list stackframe -> typ -> Prop :=
  | match_stackframes_nil:
      forall ty, match_stackframes mu nil nil ty (*WAS: ty=Tint*)
  | match_stackframes_cons:
      forall res sp pc rs f approx tyenv s s' ty sp' rs' 
           (ANALYZE: analyze f = Some approx)
           (WTF: wt_function f tyenv)
           (WTREGS: wt_regset tyenv rs)
           (TYRES: subtype ty (tyenv res) = true)
           (SAT: forall v m, numbering_satisfiable ge sp 
                                 (rs#res <- v) m approx!!pc)
           (RI: regset_inject (restrict (as_inj mu) (vis mu)) rs rs')
           (STACKS: match_stackframes mu s s' (proj_sig_res (fn_sig f)))
           (SP: SPlocal mu sp sp'),
    match_stackframes mu
      (Stackframe res f sp pc rs :: s)
      (Stackframe res (transf_function' f approx) sp' pc rs' :: s')
      ty.

Lemma match_stackframes_intern_incr mu s s' ty mu': forall
       (MS: match_stackframes mu s s' ty)
       (INC: intern_incr mu mu') (WD': SM_wd mu'),
       match_stackframes mu' s s' ty.
Proof. intros.
  induction MS; econstructor; eauto.
    eapply regset_incr; try eassumption.
      eapply intern_incr_restrict; eassumption.
    destruct SP as [spb [spb' [B [B' SP]]]].
      exists spb, spb'. eapply INC in SP. auto.
Qed.

Lemma match_stackframes_extern_incr mu s s' ty mu': forall
       (MS: match_stackframes mu s s' ty)
       (INC: extern_incr mu mu') (WD': SM_wd mu'),
       match_stackframes mu' s s' ty.
Proof. intros.
  induction MS; econstructor; eauto.
    eapply regset_incr; try eassumption.
      eapply extern_incr_restrict; eassumption.
    destruct SP as [spb [spb' [B [B' SP]]]].
      exists spb, spb'. rewrite <- (extern_incr_local _ _ INC). auto. 
Qed.

Lemma match_stackframes_replace_locals mu ty: forall s s'
      (MS : match_stackframes mu s s' ty) pubS pubT,
  match_stackframes (replace_locals mu pubS pubT) s s' ty.
Proof.
  intros.
  induction MS; econstructor; eauto.
  rewrite replace_locals_as_inj, replace_locals_vis. assumption.
  destruct SP as [spb [spb' [SP [SP' LOC]]]].
  exists spb, spb'. rewrite replace_locals_local. auto.
Qed.

Lemma match_stackframes_replace_externs mu ty s s': forall
    (MS: match_stackframes mu s s' ty) frgnS frgnT
    (HfrgnSrc: forall b, frgnBlocksSrc mu b = true -> frgnS b = true),
  match_stackframes (replace_externs mu frgnS frgnT) s s' ty.
Proof.
  intros.
  induction MS; econstructor; eauto.
    rewrite replace_externs_as_inj, replace_externs_vis.
    eapply regset_incr; eauto.
      red; intros. destruct (restrictD_Some _ _ _ _ _ H).
      apply restrictI_Some; trivial.
      unfold vis in H1. destruct (locBlocksSrc mu b); simpl in *; trivial.
     apply HfrgnSrc; trivial.
  destruct SP as [spb [spb' [SP [SP' LOC]]]].
  exists spb, spb'. rewrite replace_externs_local. auto.
Qed.

Inductive match_states mu: RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_states_intro:
      forall s sp pc rs m s' f approx tyenv sp' rs' m'
             (ANALYZE: analyze f = Some approx)
             (WTF: wt_function f tyenv)
             (WTREGS: wt_regset tyenv rs)
             (SAT: numbering_satisfiable ge sp rs m approx!!pc)
             (RI: regset_inject (restrict (as_inj mu) (vis mu)) rs rs')
             (SP: SPlocal mu sp sp')
             (STACKS: match_stackframes mu s s' (proj_sig_res (fn_sig f))),
      match_states mu (RTL_State s f sp pc rs) m
                   (RTL_State s' (transf_function' f approx) sp' pc rs') m'
  | match_states_call:
      forall s f tf args m s' args' m',
      match_stackframes mu s s' (proj_sig_res (funsig f)) ->
      Val.has_type_list args (sig_args (funsig f)) ->
      transf_fundef f = OK tf ->
      val_list_inject (restrict (as_inj mu) (vis mu)) args args' ->
      match_states mu (RTL_Callstate s f args) m
                      (RTL_Callstate s' tf args') m'
  | match_states_return:
      forall s s' ty v m v' m',
      match_stackframes mu s s' ty ->
      Val.has_type v ty ->
      val_inject (restrict (as_inj mu) (vis mu)) v v' ->
      match_states mu (RTL_Returnstate s v) m
                      (RTL_Returnstate s' v') m'.

Definition MATCH mu c1 m1 c2 m2:Prop :=
  match_states (restrict_sm mu (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma MATCH_wd: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma MATCH_restrict: forall mu c1 m1 c2 m2 X
  (MC: MATCH mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m1 X), 
  MATCH (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm, restrict_sm_nest; assumption.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. rewrite restrict_sm_all.
  eapply restrict_preserves_globalfun_ptr; try eassumption.
  unfold vis in HX. intuition.
split. 
  rewrite restrict_sm_frgnBlocksSrc. apply Glob.
split. 
  destruct SMV.
  split; intros.
    rewrite restrict_sm_DOM in H1.
    apply (H _ H1).
  rewrite restrict_sm_RNG in H1.
    apply (H0 _ H1).
split. assumption.
  rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.
Qed.

Lemma MATCH_valid: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), sm_valid mu m1 m2.
Proof. intros. eapply MC. Qed.

Lemma MATCH_PG: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2),
  meminj_preserves_globals ge (extern_of mu) /\
  (forall b : block, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.

(*NEW*) Variable hf : I64Helpers.helper_functions.

Lemma MATCH_initial: forall v 
  (vals1 : list val) c1 (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (Ini : initial_core (rtl_eff_sem hf) ge v vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (R : list_norepet (map fst (prog_defs prog)))
  (J: forall b1 b2 d, j b1 = Some (b2, d) -> 
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (InitMem : exists m0 : mem, Genv.init_mem prog = Some m0 
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m1) 
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))
  (GDE: genvs_domain_eq ge tge)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core (rtl_eff_sem hf) tge v vals2 = Some c2 /\
  MATCH
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof.
intros.
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1 
            (sig_args (funsig (Internal f))) 
           && val_casted.vals_defined vals1).
  2: solve[intros H2; rewrite H2 in H1; inv H1].
  intros H2; rewrite H2 in H1. 

  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  intros l _.
  2: solve[inversion 2].

  simpl. inversion 1. inv H1. clear H3.
  exploit funct_ptr_translated; eauto. intros [tf [FP TF]].
    unfold tge in FP. rewrite FP. (*monadInv TF. *)
    unfold rtl_eff_sem, rtl_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.

  assert (Zlength vals2 = Zlength vals1) as ->. 
  { apply forall_inject_val_list_inject in VInj. clear - VInj. 
    induction VInj; auto. rewrite !Zlength_cons, IHVInj; auto. }
  unfold transf_fundef in TF. simpl in TF. 
(*  change (fn_sig (transf_function f)) with (funsig (Internal x)).*)
  assert (val_casted.val_has_type_list_func vals2
          (sig_args (funsig tf)) =true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; simpl in H2. solve[inv H2].
    assert (sig_args (funsig tf)
          = sig_args (funsig (Internal f))) as ->.
    { specialize (sig_preserved (Internal f)). simpl. intros. 
      rewrite (H0 _ TF). reflexivity. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (funsig (Internal f)))); auto. }

  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; inv H2. }

  simpl. monadInv TF. eexists; split. 
  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  solve[simpl; auto].
  intros CONTRA. solve[elimtype False; auto].
  2: intros CONTRA; solve[elimtype False; auto].

  clear e e0.
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  remember (val_casted.val_has_type_list_func vals1 (sig_args (funsig (Internal f))) &&
         val_casted.vals_defined vals1) as vc.
  destruct vc; inv H2. 
  split. simpl.
    eapply match_states_call; try eassumption.
      econstructor. 
      apply eq_sym in Heqvc. apply andb_true_iff in Heqvc. 
        apply val_casted.val_has_type_list_func_charact. 
        apply Heqvc. 
      unfold transf_fundef, transf_partial_fundef, bind.
        rewrite EQ. trivial. 
      unfold vis, initial_SM; simpl.
        eapply val_list_inject_incr.
          Focus 2. apply forall_inject_val_list_inject.
                    eapply restrict_forall_vals_inject; try eassumption.
          intros bb Hbb. apply Hbb.
          red; intros. destruct (restrictD_Some _ _ _ _ _ H2). 
            apply restrictI_Some. 
              unfold as_inj; simpl. apply joinI. left. 
                apply restrictI_Some.  assumption. 
                apply REACH_nil. rewrite H4; intuition.
              apply REACH_nil. rewrite H4; intuition.
  rewrite initial_SM_as_inj.
  intuition.
    (*as in selectionproofEFF*)
      red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         destruct InitMem as [m0 [INIT_MEM [? ?]]].
         specialize (H3 _ _ _ INIT_MEM H2). 
         destruct (valid_init_is_global _ R _ INIT_MEM _ H3) as [id Hid]. 
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock. 
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
 Qed. 

Lemma MATCH_atExternal: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) (c2 : RTL_core)
  (m2 : mem) (e : external_function) (vals1 : list val) (ef_sig : signature),
MATCH mu c1 m1 c2 m2 ->
at_external (rtl_eff_sem hf) c1 = Some (e, ef_sig, vals1) ->
Mem.inject (as_inj mu) m1 m2 /\
(exists vals2 : list val,
   Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
   at_external (rtl_eff_sem hf) c2 = Some (e, ef_sig, vals2) /\
   (forall pubSrc' pubTgt' : block -> bool,
    pubSrc' =
    (fun b : block => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
    pubTgt' =
    (fun b : block => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
    forall nu : SM_Injection,
    nu = replace_locals mu pubSrc' pubTgt' ->
    MATCH nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2)).
Proof. intros.
 destruct H as [MC [RC [PG [GFP [Glob [SMV [WDmu MINJ]]]]]]].
 simpl in *. inv MC; simpl in *; inv H0.
 destruct f; inv H5.
 split; trivial.
 rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
 simpl. 
 monadInv H2.
 destruct (observableEF_dec hf e0); inv H4.
 eexists.
    split. eapply val_list_inject_forall_inject. eassumption.
    split. reflexivity.
 intros.
assert (WDnu: SM_wd nu).
  subst.
  eapply replace_locals_wd; eauto.
    intros b Hb.
    apply andb_true_iff in Hb. destruct Hb.
    exploit (REACH_local_REACH _ WDmu); try eassumption.
      eapply val_list_inject_forall_inject. 
      eapply val_list_inject_incr; try eassumption.
      apply restrict_incr.
    intros [b2 [d [loc R2]]].
      exists b2, d.
      rewrite loc, R2. destruct (local_DomRng _ WDmu _ _ _ loc). intuition.
   intros b Hb. apply andb_true_iff in Hb. eapply Hb.
split. subst.
  split. 
    econstructor; eauto; rewrite <- restrict_sm_replace_locals, replace_locals_vis.
       eapply match_stackframes_replace_locals; eassumption.
    rewrite replace_locals_as_inj, replace_locals_vis. 
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
rewrite replace_locals_as_inj, replace_locals_vis,
         replace_locals_frgnBlocksSrc.
intuition.
  split; intros b Hb.
    rewrite replace_locals_DOM in Hb. eapply SMV; trivial.
    rewrite replace_locals_RNG in Hb. eapply SMV; trivial.
assert (MINJR: Mem.inject (restrict (as_inj mu) (vis mu)) m1 m2). 
  eapply inject_restrict; try eassumption.
assert (RCnu: REACH_closed m1 (mapped (shared_of nu))).
  subst. rewrite replace_locals_shared.
  clear MINJ.
  red; intros b Hb. apply REACHAX in Hb. destruct Hb as [L HL].
    generalize dependent b.
    induction L; simpl; intros; inv HL. trivial.
    specialize (IHL _ H4); clear H4.
    destruct (mappedD_true _ _ IHL) as [[bb ofs] Hbb]. clear IHL.
    apply mapped_charT.
    assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MINJR)).
    destruct (joinD_Some _ _ _ _ _ Hbb); clear Hbb.
      exploit (MV b' z bb ofs).
        eapply restrictI_Some. apply foreign_in_all; eassumption.
          unfold vis. unfold foreign_of in H0. destruct mu. simpl in *.
          destruct (frgnBlocksSrc b'); inv H0. intuition.
        assumption.
      clear MV; intros. rewrite H7 in H2. inv H2.
      exists (b2, delta). apply joinI.
      remember (locBlocksSrc mu b) as d.
      destruct d; apply eq_sym in Heqd. 
        right; simpl. 
        split. eapply locBlocksSrc_foreignNone; eassumption.
        destruct (restrictD_Some _ _ _ _ _ H8); clear H8.
        destruct (joinD_Some _ _ _ _ _ H2).
          destruct (extern_DomRng _ WDmu _ _ _ H6).
          apply extBlocksSrc_locBlocksSrc in H8. rewrite H8 in Heqd; inv Heqd.
           trivial.
        destruct H6. rewrite H8.
        assert (Rb: REACH m1 (exportedSrc mu vals1) b = true).
          eapply REACH_cons; try eassumption.
          eapply REACH_nil. unfold exportedSrc, sharedSrc. apply foreign_in_shared in H0. rewrite H0. intuition.
        rewrite Rb; trivial.
      left. eapply restrict_vis_foreign; try eassumption.
               destruct (restrictD_Some _ _ _ _ _ H8).
               rewrite (as_inj_locBlocks _ _ _ _ WDmu H2) in Heqd. trivial.
    destruct H0. remember (locBlocksSrc mu b' && REACH m1 (exportedSrc mu vals1) b') as d. 
       destruct d; apply eq_sym in Heqd; inv H2.
       apply andb_true_iff in Heqd; destruct Heqd.
      exploit (MV b' z bb ofs).
        eapply restrictI_Some. apply local_in_all; eassumption.
          unfold vis. rewrite H2; trivial.
        assumption.
      clear MV; intros. rewrite H7 in H8. inv H8.
      exists (b2, delta). apply joinI.
      remember (locBlocksSrc mu b) as d.
      destruct d; apply eq_sym in Heqd. 
        right; simpl. destruct (restrictD_Some _ _ _ _ _ H11); clear H11.
        split. eapply locBlocksSrc_foreignNone; eassumption.
        destruct (joinD_Some _ _ _ _ _ H8).
          destruct (extern_DomRng _ WDmu _ _ _ H10).
          apply extBlocksSrc_locBlocksSrc in H11. rewrite H11 in Heqd; inv Heqd.
           trivial.
        destruct H10. rewrite H11.
        assert (REACH m1 (exportedSrc mu vals1) b = true).
          eapply REACH_cons; try eassumption.
        rewrite H12. trivial.
      simpl. left. eapply restrict_vis_foreign; try eassumption.
               destruct (restrictD_Some _ _ _ _ _ H11).
               rewrite (as_inj_locBlocks _ _ _ _ WDmu H8) in Heqd. trivial.
eapply inject_mapped. eapply MINJ. eassumption.
  subst. rewrite replace_locals_shared.
    red; intros b b' delta Hb. destruct (joinD_Some _ _ _ _ _ Hb); clear Hb.
    eapply foreign_in_all; eassumption.
    destruct H0.
      destruct (locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b); inv H2.
      rewrite H5; eapply local_in_all; eassumption.
Qed.

Lemma MATCH_afterExternal: forall (mu : SM_Injection) (st1 st2 : RTL_core) (m1 : mem)
  (e : external_function) (vals1 : list val) (m2 : mem) (ef_sig : signature)
  (vals2 : list val) (e' : external_function) (ef_sig' : signature)
  (INJ: Mem.inject (as_inj mu) m1 m2)
  (MTCH: MATCH mu st1 m1 st2 m2)
  (AtExtSrc: at_external (rtl_eff_sem hf) st1 = Some (e, ef_sig, vals1))
  (AtExtTgt: at_external (rtl_eff_sem hf) st2 = Some (e', ef_sig', vals2))
  (ArgsInj: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
  (pubSrc' : block -> bool)
  (HpubSrc: pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
  (pubTgt' : block -> bool)
  (HpubTgt: pubTgt' = (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
  (nu : SM_Injection)
  (Hnu: nu = replace_locals mu pubSrc' pubTgt')
  (nu' : SM_Injection) (ret1 : val) (m1' : mem) (ret2 : val) (m2' : mem)
  (Ret1TP: Val.has_type ret1 (proj_sig_res (AST.ef_sig e)))
  (Ret2TP: Val.has_type ret2 (proj_sig_res (AST.ef_sig e')))
  (INC: extern_incr nu nu')
  (SEP: globals_separate tge nu nu')
  (WDnu': SM_wd nu')
  (SMVnu': sm_valid nu' m1' m2')
  (INJnu': Mem.inject (as_inj nu') m1' m2')
  (RetInj: val_inject (as_inj nu') ret1 ret2)
  (FWD1: mem_forward m1 m1')  
  (FWD2: mem_forward m2 m2')
  (frgnSrc' : block -> bool)
  (HfrgnSrc: frgnSrc' = (fun b =>
      DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
  (frgnTgt' : block -> bool)
  (HfrgnTgt: frgnTgt' = (fun b =>
      DomTgt nu' b &&
      (negb (locBlocksTgt nu' b) && REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
  mu' (Hmu': mu' = replace_externs nu' frgnSrc' frgnTgt')
  (UnchPrivSrc: Mem.unchanged_on (fun b z => locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
  (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists st1' st2' : RTL_core,
  after_external (rtl_eff_sem hf) (Some ret1) st1 = Some st1' /\
  after_external (rtl_eff_sem hf) (Some ret2) st2 = Some st2' /\
  MATCH mu' st1' m1' st2' m2'.
Proof. intros. simpl.
 destruct MTCH as [MC [RC [PG [GFP [Glob [VAL [WDmu MINJ]]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H4. simpl in *. 
 inv H1. 
 destruct (observableEF_dec hf e0); inv H5; inv AtExtTgt.
 eexists. eexists.
    split. reflexivity.
    split. reflexivity.
(* inv TF.*)
 assert (INCvisNu': inject_incr
  (restrict (as_inj nu')
     (vis
        (replace_externs nu'
           (fun b : Values.block =>
            DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
           (fun b : Values.block =>
            DomTgt nu' b &&
            (negb (locBlocksTgt nu' b) &&
             REACH m2' (exportedTgt nu' (ret2 :: nil)) b))))) (as_inj nu')).
      unfold vis. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc.
      apply restrict_incr. 
assert (RC': REACH_closed m1' (mapped (as_inj nu'))).
        eapply inject_REACH_closed; eassumption.
assert (PGnu': meminj_preserves_globals (Genv.globalenv prog) (as_inj nu')). 
  eapply meminj_preserves_globals_extern_incr_separate. eassumption.
    rewrite replace_locals_as_inj. assumption.
    assumption. 
    specialize (genvs_domain_eq_isGlobal _ _ GDE_lemma). intros GL.
    red. unfold ge in GL. rewrite GL. apply SEP.
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H4); clear H4.
  apply orb_true_iff in IHL.
  remember (locBlocksSrc nu' b') as l.
  destruct l; apply eq_sym in Heql.
  (*case locBlocksSrc nu' b' = true*)
    clear IHL.
    remember (pubBlocksSrc nu' b') as p.
    destruct p; apply eq_sym in Heqp.
      assert (Rb': REACH m1' (mapped (as_inj nu')) b' = true).
        apply REACH_nil. 
        destruct (pubSrc _ WDnu' _ Heqp) as [bb2 [dd1 [PUB PT]]].
        eapply mappedI_true.
         apply (pub_in_all _ WDnu' _ _ _ PUB).
      assert (Rb:  REACH m1' (mapped (as_inj nu')) b = true).
        eapply REACH_cons; try eassumption.
      specialize (RC' _ Rb).
      destruct (mappedD_true _ _ RC') as [[b2 d1] AI'].
      remember (locBlocksSrc nu' b) as d.
      destruct d; simpl; trivial.
      apply andb_true_iff. 
      split. eapply as_inj_DomRng; try eassumption.
      eapply REACH_cons; try eassumption.
        apply REACH_nil. unfold exportedSrc.
        rewrite (pubSrc_shared _ WDnu' _ Heqp). intuition.
      destruct (UnchPrivSrc) as [UP UV]; clear UnchLOOR.
        specialize (UP b' z Cur Readable). 
        specialize (UV b' z). 
        destruct INC as [_ [_ [_ [_ [LCnu' [_ [PBnu' [_ [FRGnu' _]]]]]]]]].
        rewrite <- LCnu'. rewrite replace_locals_locBlocksSrc.  
        rewrite <- LCnu' in Heql. rewrite replace_locals_locBlocksSrc in *.
        rewrite <- PBnu' in Heqp. rewrite replace_locals_pubBlocksSrc in *.
        clear INCvisNu'. 
        rewrite Heql in *. simpl in *. intuition.
        assert (VB: Mem.valid_block m1 b').
          eapply VAL. unfold DOM, DomSrc. rewrite Heql. intuition.
        apply (H1 VB) in H5.
        rewrite (H3 H5) in H7. clear H1 H3.
        remember (locBlocksSrc mu b) as q.
        destruct q; simpl; trivial; apply eq_sym in Heqq.
        assert (Rb : REACH m1 (vis mu) b = true).
           eapply REACH_cons; try eassumption.
           apply REACH_nil. unfold vis. rewrite Heql; trivial.
        specialize (RC _ Rb). unfold vis in RC.
           rewrite Heqq in RC; simpl in *.
        rewrite replace_locals_frgnBlocksSrc in FRGnu'.
        rewrite FRGnu' in RC.
        apply andb_true_iff.  
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ RC). intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ RC). intuition.
  (*case DomSrc nu' b' &&
    (negb (locBlocksSrc nu' b') &&
     REACH m1' (exportedSrc nu' (ret1 :: nil)) b') = true*)
    destruct IHL. congruence.
    apply andb_true_iff in H1. simpl in H1. 
    destruct H1 as [DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchLOOR UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ INJnu' RET
               _ Rb' (fun b => true)) as [b2 [d1 [AI' _]]]; trivial.
           assert (REACH m1' (mapped (as_inj nu')) b = true).
             eapply REACH_cons; try eassumption.
             apply REACH_nil. eapply mappedI_true; eassumption.
           specialize (RC' _ H1). 
           destruct (mappedD_true _ _ RC') as [[? ?] ?].
           eapply as_inj_DomRng; eassumption.
    eapply REACH_cons; try eassumption.
    
assert (RRC: REACH_closed m1' (fun b : Values.block =>
                         mapped (as_inj nu') b &&
                           (locBlocksSrc nu' b
                            || DomSrc nu' b &&
                               (negb (locBlocksSrc nu' b) &&
                           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
  eapply REACH_closed_intersection; eassumption.
assert (GFnu': forall b, isGlobalBlock (Genv.globalenv prog) b = true ->
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
     intros. specialize (Glob _ H1).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in Glob.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ Glob). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ Glob). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ Glob). intuition.
split. (* clear - WDnu' INC H INJnu' RetInj H0.*)
  econstructor; try eassumption;
     try rewrite <- restrict_sm_replace_externs, replace_externs_vis.
  eapply match_stackframes_replace_externs.
    eapply match_stackframes_extern_incr; try eapply INC; trivial.
    eapply match_stackframes_replace_locals; eauto.
     instantiate (1:= fun b =>
              locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b). 
     instantiate (1:= fun b =>
              locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b).
     red in INC. red. 
       rewrite replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
        replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
        replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
        replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
        replace_locals_local, replace_locals_extern in *.
        
       rewrite restrict_sm_frgnBlocksSrc, restrict_sm_frgnBlocksTgt,
         restrict_sm_pubBlocksSrc, restrict_sm_pubBlocksTgt,
         restrict_sm_locBlocksSrc, restrict_sm_locBlocksTgt,
         restrict_sm_extBlocksSrc, restrict_sm_extBlocksTgt,
         restrict_sm_local, restrict_sm_extern.
       rewrite restrict_sm_frgnBlocksSrc, restrict_sm_frgnBlocksTgt,
         restrict_sm_locBlocksSrc, restrict_sm_locBlocksTgt,
         restrict_sm_extBlocksSrc, restrict_sm_extBlocksTgt,
         restrict_sm_local, restrict_sm_extern.
       intuition. 
       red; intros. destruct (restrictD_Some _ _ _ _ _ H11); clear H11.
         apply restrictI_Some. apply H1; trivial.
         unfold vis in H14. unfold DomSrc. rewrite H6 in H14.
           destruct (locBlocksSrc nu' b); simpl in *; trivial. 
           rewrite H10 in H14. 
           rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H14); simpl.
           apply REACH_nil. unfold exportedSrc.
            rewrite (frgnSrc_shared _ WDnu' _ H14). intuition.
       rewrite H4. unfold restrict. extensionality b.
         unfold vis, DomSrc. rewrite H10, H6.
         remember (local_of nu' b) as d. 
         destruct d; apply eq_sym in Heqd.
           destruct p.
           destruct (local_DomRng _ WDnu' _ _ _ Heqd) as [lS _].
           rewrite lS; simpl; trivial.
         destruct (locBlocksSrc nu' b || frgnBlocksSrc nu' b). 
         destruct (locBlocksSrc nu' b
       || (locBlocksSrc nu' b || extBlocksSrc nu' b) &&
          (negb (locBlocksSrc nu' b) &&
           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)); simpl; trivial. 
         destruct (locBlocksSrc nu' b
       || (locBlocksSrc nu' b || extBlocksSrc nu' b) &&
          (negb (locBlocksSrc nu' b) &&
           REACH m1' (exportedSrc nu' (ret1 :: nil)) b)); simpl; trivial. 
        apply restrict_sm_WD. assumption.
         unfold vis, DomSrc. intros. 
           destruct (locBlocksSrc nu' b); simpl in *; trivial. 
           rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H1); simpl.
           apply REACH_nil. unfold exportedSrc.
            rewrite (frgnSrc_shared _ WDnu' _ H1). intuition.
        rewrite restrict_sm_frgnBlocksSrc.
          unfold DomSrc. intros.
           rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ H1); simpl.
           rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H1); simpl.
           apply REACH_nil. unfold exportedSrc.
            rewrite (frgnSrc_shared _ WDnu' _ H1). intuition.
  unfold vis. rewrite replace_externs_as_inj. 
    rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc,
      restrict_sm_locBlocksSrc, restrict_sm_all.
    rewrite restrict_nest; trivial.
       eapply restrict_val_inject; try eassumption.
       intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H1; trivial.
  rewrite replace_externs_as_inj; trivial.
  
  destruct (eff_after_check2 _ _ _ _ _ INJnu' RetInj 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMVnu').
  unfold vis in *.
  rewrite replace_externs_locBlocksSrc, 
      replace_externs_frgnBlocksSrc in *.
  intuition.
  red; intros b fb Hb. destruct (GFP _ _ Hb). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed.

Ltac TransfInstr :=
  match goal with
  | H1: (PTree.get ?pc ?c = Some ?instr), f: function, approx: PMap.t numbering |- _ =>
      cut ((transf_function' f approx).(fn_code)!pc = Some(transf_instr approx!!pc instr));
      [ simpl transf_instr
      | unfold transf_function', transf_code; simpl; rewrite PTree.gmap; 
        unfold option_map; rewrite H1; reflexivity ]
  end.

Lemma MATCH_effcore_diagram: 
  forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
      (CS: effstep (rtl_eff_sem hf) ge U1 st1 m1 st1' m1')
      st2 mu m2 
      (MTCH: MATCH mu st1 m1 st2 m2)
      (LNR: list_norepet (map fst (prog_defs prog))),
  exists st2' m2' (U2 : block -> Z -> bool),
     effstep (rtl_eff_sem hf) tge U2 st2 m2 st2' m2' 
  /\ exists mu',
     intern_incr mu mu' /\
     globals_separate ge mu mu' /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH mu' st1' m1' st2' m2' /\
     SM_wd mu' /\
     sm_valid mu' m1' m2' /\
    (forall 
      (EffSrc: forall b ofs, U1 b ofs = true -> vis mu b = true)
      b2 ofs, U2 b2 ofs = true ->
      visTgt mu b2 = true /\
      (locBlocksTgt mu b2 = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b2, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros. 
assert (SymbPres := symbols_preserved).
induction CS; 
   destruct MTCH as [MSTATE PRE]; inv MSTATE. 

{ (* Inop *) 
  exists (RTL_State s' (transf_function' f approx) sp' pc' rs'), m2. 
  eexists; split.
  eapply rtl_effstep_exec_Inop; try TransfInstr; auto. 
  exists mu.
  split. apply intern_incr_refl.
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_irrefl); intuition.
  split. 2: intuition.
  split. 
      econstructor; eauto. 
      exploit analysis_correct_1; try eassumption.
        instantiate (1:=pc'); left; trivial. 
           unfold transfer. rewrite H. eassumption.
       trivial.
  intuition. }

{ (* Iop *) 
  TransfInstr; intros C.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]].
  destruct SP as [spb [spb' [B [B' SP]]]]. subst sp; subst sp'. 
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; assumption.
  exploit eval_operation_inject; try eapply H0; eauto. 
     rewrite <- restrict_sm_all. 
     apply local_in_all.
     apply restrict_sm_WD; trivial. eassumption. 
     eapply regset_get_list; eassumption.
  rewrite eval_shift_stack_operation; simpl; rewrite Int.add_zero_l. 
  intros [v' [F G]]. 
  destruct (is_trivial_op op) eqn:?. 
  (*case is_trivial_op op = true*)
    exists (RTL_State s' (transf_function' f approx) 
          (Vptr spb' (Int.repr 0)) pc'
          (rs'#res <- v')), m2.
    eexists; split.
      eapply rtl_effstep_exec_Iop'; eauto.
      rewrite <- F. apply eval_operation_preserved. 
        exact symbols_preserved.
    exists mu.
    split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
    split. apply sm_locally_allocatedChar.
           repeat split; extensionality bb; 
              try rewrite (freshloc_irrefl); intuition.
    split. 2: intuition.
    split. 2: intuition.
    econstructor; eauto. 
      eapply wt_exec_Iop; eauto. eapply wt_instr_at; eauto.   
      eapply analysis_correct_1; eauto. simpl; auto.
        unfold transfer; rewrite H. 
        eapply add_op_satisfiable; eauto. eapply wf_analyze; eauto.
      rewrite vis_restrict_sm, restrict_sm_all,
          restrict_nest in *; trivial.
        eapply regset_set; assumption.
      exists spb, spb'; auto.
  (*case is_trivial_op op = false*)
    destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
    assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
    destruct SAT as [valu1 NH1].
    exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
    assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
    destruct (find_rhs n1 (Op op vl)) as [r|] eqn:?.
    (* replaced by move *)
      assert (EV: rhs_evals_to ge (Vptr spb Int.zero) valu2 
                   (Op op vl) m rs#r). 
        eapply find_rhs_correct; eauto.
      assert (RES: rs#r = v). red in EV. congruence.
      eexists; eexists; eexists.
      split. eapply rtl_effstep_exec_Iop'; eauto.
               simpl. reflexivity.
      exists mu.
      split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
      split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
      split. 2: intuition.
      split. 2: intuition.
      econstructor; eauto. 
        eapply wt_exec_Iop; eauto. eapply wt_instr_at; eauto.   
        eapply analysis_correct_1; eauto. simpl; auto.
          unfold transfer; rewrite H. 
          eapply add_op_satisfiable; eauto. 
          exists valu1. assumption.
        rewrite vis_restrict_sm, restrict_sm_all,
            restrict_nest in *; trivial.
          eapply regset_set; try assumption.
          destruct v. constructor.
            specialize (RI r); rewrite RES in RI. apply RI.
            specialize (RI r); rewrite RES in RI. apply RI.
            specialize (RI r); rewrite RES in RI. apply RI.
            specialize (RI r); rewrite RES in RI. apply RI.
        exists spb, spb'; auto. 
  (* possibly simplified *)
    destruct (reduce operation combine_op n1 op args vl) as [op' args'] eqn:?.
    assert (RES: eval_operation ge (Vptr spb Int.zero) op' rs##args' m = Some v).
      eapply reduce_sound with (sem := fun op vl => eval_operation ge (Vptr spb Int.zero) op vl m); eauto. 
      intros; eapply combine_op_sound; eauto.
    exploit eval_operation_inject; try eapply RES; eauto. 
     rewrite <- restrict_sm_all. 
     apply local_in_all.
     apply restrict_sm_WD; trivial. eassumption. 
     eapply regset_get_list; eassumption.
    rewrite eval_shift_stack_operation; simpl; rewrite Int.add_zero_l. 
    intros [v'' [F' G']]. 
    
    eexists; eexists; eexists.
    split. eapply rtl_effstep_exec_Iop'; eauto.
       instantiate (1:=v'').
       rewrite <- F'. apply eval_operation_preserved. 
          exact symbols_preserved.
      exists mu.
      split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
      split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
      split. 2: intuition.
      split. 2: intuition.
      econstructor; eauto. 
        eapply wt_exec_Iop. 2: eapply H0. eapply wt_instr_at; eauto. 
           assumption.  
        eapply analysis_correct_1; eauto. simpl; auto.
          unfold transfer; rewrite H. 
          eapply add_op_satisfiable; eauto. 
          exists valu1. assumption.
        rewrite vis_restrict_sm, restrict_sm_all,
            restrict_nest in *; trivial.
          eapply regset_set; assumption.
        exists spb, spb'; auto. }

{ (* Iload *)
  TransfInstr; intros C.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]].
  destruct SP as [spb [spb' [B [B' SP]]]]. subst sp; subst sp'.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; assumption.
(*  exists (State s' (transf_function' f approx) sp pc' (rs#dst <- v) m); split.*)
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (find_rhs n1 (Load chunk addr vl)) as [r|] eqn:?.
  { (* replaced by move *)
    assert (EV: rhs_evals_to ge (Vptr spb Int.zero) valu2 
         (Load chunk addr vl) m rs#r). eapply find_rhs_correct; eauto.
    assert (RES: rs#r = v).
      red in EV. destruct EV as [a' [EQ1 EQ2]]. congruence.
    clear EV.
    exploit eval_addressing_inject; try eexact H0; try eassumption. 
      rewrite <- restrict_sm_all. 
      apply local_in_all.
      apply restrict_sm_WD; trivial. eassumption. 
      eapply regset_get_list; eassumption. 
    intros [a1' [F1 G1]].
    exploit Mem.loadv_inject. eapply MInjR. eexact H1. eexact G1.
    intros [v' [LD' ValInjV']].
    eexists; eexists; eexists; split. 
      eapply rtl_effstep_exec_Iop'; eauto. simpl. reflexivity.
    exists mu.
    split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
    split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
    split. 2: intuition.
    split. 2: intuition.
    econstructor; eauto. 
      eapply wt_exec_Iload; eauto. eapply wt_instr_at; eauto.
      eapply analysis_correct_1; eauto. simpl; auto. 
        unfold transfer; rewrite H. 
        eapply add_load_satisfiable; eauto. exists valu1. assumption. 
      rewrite vis_restrict_sm, restrict_sm_all,
            restrict_nest in *; trivial.
          eapply regset_set; try assumption.
      destruct v. constructor.
            specialize (RI r); rewrite RES in RI. apply RI.
            specialize (RI r); rewrite RES in RI. apply RI.
            specialize (RI r); rewrite RES in RI. apply RI.
            specialize (RI r); rewrite RES in RI. apply RI.
      exists spb, spb'; auto. }

  { (* possibly simplified *)
    destruct (reduce addressing combine_addr n1 addr args vl)
     as [addr' args'] eqn:?.
    assert (ADDR: eval_addressing ge (Vptr spb Int.zero)
                    addr' rs##args' = Some a).
      eapply reduce_sound with (sem := fun addr vl => eval_addressing ge (Vptr spb Int.zero) addr vl); eauto. 
      intros; eapply combine_addr_sound; eauto.
    exploit eval_addressing_inject; try eexact ADDR; try eassumption. 
      rewrite <- restrict_sm_all. 
      apply local_in_all.
      apply restrict_sm_WD; trivial. eassumption. 
      eapply regset_get_list; eassumption. 
    rewrite eval_shift_stack_addressing; simpl; rewrite Int.add_zero_l. 
    intros [a1' [F1 G1]].
    exploit Mem.loadv_inject. eapply MInjR. eexact H1. eexact G1.
    intros [v' [LD' ValInjV']].
    eexists; eexists; eexists; split. 
       eapply rtl_effstep_exec_Iload; eauto.
         rewrite <- F1. apply eval_addressing_preserved. 
         exact symbols_preserved.
    exists mu.
    split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
    split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
    split. 2: intuition.
    split. 2: intuition.
    econstructor; eauto. 
      eapply wt_exec_Iload; eauto. eapply wt_instr_at; eauto.
      eapply analysis_correct_1; eauto. simpl; auto. 
        unfold transfer; rewrite H. 
        eapply add_load_satisfiable; eauto. exists valu1. assumption. 
      rewrite vis_restrict_sm, restrict_sm_all,
            restrict_nest in *; trivial.
          eapply regset_set; assumption.
      exists spb, spb'; auto. } }

{ (* Istore *)
  TransfInstr; intros C.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]]. 
  destruct SP as [spb [spb' [B [B' SP]]]]. subst sp; subst sp'.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; assumption.
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  destruct SAT as [valu1 NH1].
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (reduce addressing combine_addr n1 addr args vl) as [addr' args'] eqn:?.
  assert (ADDR: eval_addressing ge (Vptr spb Int.zero) addr' rs##args' = Some a).
    eapply reduce_sound with (sem := fun addr vl => eval_addressing ge (Vptr spb Int.zero) addr vl); eauto. 
    intros; eapply combine_addr_sound; eauto.
  exploit eval_addressing_inject; try eexact ADDR; try eassumption. 
      rewrite <- restrict_sm_all. 
      apply local_in_all.
      apply restrict_sm_WD; trivial. eassumption. 
      eapply regset_get_list; eassumption. 
    rewrite eval_shift_stack_addressing; simpl; rewrite Int.add_zero_l. 
    intros [a' [ADDR' G1]].
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu)));
     try eassumption.
      eapply RI. 
  intros [m'' [P Q]].
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_Istore; eauto.
      rewrite <- ADDR'. apply eval_addressing_preserved. 
      exact symbols_preserved.
  assert (SMV': sm_valid mu m' m'').
        split; intros; 
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
  exists mu.
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (storev_freshloc _ _ _ _ _ P);
            try rewrite (storev_freshloc _ _ _ _ _ H1); intuition.
  split. 
    split.
      econstructor; eauto.
        eapply analysis_correct_1; eauto. simpl; auto. 
          unfold transfer; rewrite H.
        eapply add_store_satisfiable; eauto. exists valu1; assumption. 
        exploit wt_instr_at; eauto. intros WTI; inv WTI.
          eapply Val.has_subtype; eauto.  
        rewrite vis_restrict_sm, restrict_sm_all,
            restrict_nest in *; trivial.
        exists spb, spb'; auto. 
    specialize (RI src).
    intuition.
      destruct a; inv H1.
           eapply REACH_Store; try eassumption. 
           inv G1. destruct (restrictD_Some _ _ _ _ _ H6); trivial.
           intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.   
                  rewrite H1 in RI. inv RI.
                  destruct (restrictD_Some _ _ _ _ _ H8); trivial.

      exploit (Mem.storev_mapped_inject (as_inj mu)). eassumption. eassumption. 
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
           eapply val_inject_incr; try eassumption. eapply restrict_incr.
         intros [m2'' [ST2 INJ]]. rewrite ST2 in P. inv P. eassumption. 
   intuition. 
      apply StoreEffectD in H4. destruct H4 as [i [VADDR' _]]. subst. 
        inv G1; inv H1. eapply visPropagateR; eassumption.
      eapply StoreEffect_PropagateLeft; eassumption. }

{ (* Icall *) 
  TransfInstr; intros C.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]].
  destruct SP as [spb [spb' [B [B' SP]]]]. subst sp; subst sp'.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']].
  exploit find_function_preserved'; eauto. 
  clear FIND'; intros FIND'.
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_Icall; eauto.
      apply sig_preserved; auto.
  exploit wt_instr_at; eauto. intros WTI; inv WTI.
  exists mu.
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
  split. 2: intuition.
  split. 2: intuition.
  econstructor; eauto. 
    econstructor; eauto. 
    intros. eapply analysis_correct_1; eauto. simpl; auto. 
      unfold transfer; rewrite H. 
      apply empty_numbering_satisfiable.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
    exists spb, spb'; auto.
    eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto. 
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
      apply regset_get_list; assumption. }

{ (* Itailcall *)
  TransfInstr; intros C.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]].
  destruct SP as [spb [spb' [B [B' SP]]]]. subst sp'. inv B.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (GFPR: globalfunction_ptr_inject ge (restrict (as_inj mu) (vis mu))). 
            eapply restrict_GFP_vis; eassumption.
  rewrite restrict_sm_local in SP. 
  destruct (restrictD_Some _ _ _ _ _ SP).
  exploit (free_parallel_inject (as_inj mu)); eauto. 
    apply local_in_all; eassumption.
  intros [m'' [P Q]]. simpl in *. rewrite Zplus_0_r in P.
  exploit find_function_translated; eauto. intros [tf [FIND' TRANSF']].
  exploit find_function_preserved'; eauto. 
  clear FIND'; intros FIND'. 
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_Itailcall; eauto.
      apply sig_preserved; auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H2).
        repeat split; extensionality bb; intuition.
  assert (SMV': sm_valid mu m' m'').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
  exploit wt_instr_at; eauto. intros WTI; inv WTI.
  split.
    split.
      econstructor; eauto. 
        replace (proj_sig_res (funsig fd)) with (proj_sig_res (fn_sig f)). auto. 
          unfold proj_sig_res. rewrite H8; auto.
        eapply Val.has_subtype_list; eauto. apply wt_regset_list; auto.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
          apply regset_get_list; assumption.
     intuition.
       eapply REACH_closed_free; eassumption.
  destruct (restrictD_Some _ _ _ _ _ SP).
  apply local_in_all in H4; trivial.
  intuition.
    apply FreeEffectD in H6. destruct H6 as [? [VB Arith2]]; subst.
      eapply visPropagate; eassumption. 
    simpl in H6. 
          eapply FreeEffect_PropagateLeft; eassumption. }
        
{ (* Ibuiltin *)
  TransfInstr; intros C.
  destruct SP as [spb [spb' [B [B' SP]]]]. subst sp. subst sp'.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  assert (ArgsInj:= regset_get_list _ _ _ args RI).
  exploit (inlineable_extern_inject ge tge); try eapply PRE;
    try eassumption; try apply GDE_lemma.
  intros [mu' [v' [m'' [TEC [ResInj [MINJ' [UNMAPPED [LOOR 
           [INC [SEP [GSEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]]]].
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_Ibuiltin; eauto. 
  exists mu'.
  split; trivial.
  split; trivial.
  split; trivial.
  split. 
    split.
      { econstructor; eauto.
        eapply wt_exec_Ibuiltin; eauto. eapply wt_instr_at; eauto.
        eapply analysis_correct_1; eauto. simpl; auto.
          unfold transfer; rewrite H.
          assert (CASE1: numbering_satisfiable ge (Vptr spb Int.zero) 
                      (rs#res <- v) m' empty_numbering).
          { apply empty_numbering_satisfiable. }
          assert (CASE2: m' = m -> numbering_satisfiable ge
                     (Vptr spb Int.zero) (rs#res <- v) m' 
                      (add_unknown approx#pc res)).
          { intros. subst m'. apply add_unknown_satisfiable. 
            eapply wf_analyze; eauto. auto. }
          assert (CASE3: numbering_satisfiable ge (Vptr spb Int.zero)
                       (rs#res <- v) m'
                         (add_unknown (kill_loads approx#pc) res)).
         { apply add_unknown_satisfiable. apply wf_kill_equations. 
              eapply wf_analyze; eauto.
              eapply kill_loads_satisfiable; eauto. }
         destruct ef; auto; apply CASE2; inv H0; auto.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
          eapply regset_set; try eassumption.
            eapply regset_incr; try eassumption.
            eapply intern_incr_restrict; eassumption.
        exists spb, spb'. split; trivial. split; trivial. 
          rewrite restrict_sm_local in *.
          destruct (restrictD_Some _ _ _ _ _ SP). 
          apply restrictI_Some. 
            eapply INC; eassumption. 
            eapply intern_incr_vis; eassumption.
        eapply match_stackframes_intern_incr; try eassumption.
          eapply restrict_sm_intern_incr; eassumption.
          apply restrict_sm_WD; trivial. }
      intuition.
        apply intern_incr_as_inj in INC; trivial.
          apply sm_inject_separated_mem in SEP; trivial.
          eapply meminj_preserves_incr_sep; eassumption. 
        red; intros b fb Hb. destruct (H3 _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
        rewrite <- (intern_incr_frgnBlocksSrc _ _ INC). eauto. 
  split; trivial. 
  split; trivial.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  intros. eapply BuiltinEffect_Propagate; eassumption.  }

{ (* Icond *)
  TransfInstr; intros C.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  destruct (valnum_regs approx!!pc args) as [n1 vl] eqn:?.
  assert (wf_numbering approx!!pc). eapply wf_analyze; eauto.
  elim SAT; intros valu1 NH1.
  exploit valnum_regs_holds; eauto. intros [valu2 [NH2 [EQ AG]]]. 
  assert (wf_numbering n1). eapply wf_valnum_regs; eauto. 
  destruct (reduce condition combine_cond n1 cond args vl) as [cond' args'] eqn:?.
  assert (RES: eval_condition cond' rs##args' m = Some b).
    eapply reduce_sound with (sem := fun cond vl => eval_condition cond vl m); eauto. 
    intros; eapply combine_cond_sound; eauto.
  assert (ArgsInj:= regset_get_list _ _ _ args' RI).
  assert (RES':  eval_condition cond' rs'##args' m2 = Some b).
    eapply eval_condition_inject; eauto.
    eapply inject_restrict; eassumption.
  clear RES.
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_Icond; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
  split. 2: intuition.
  split. 2: intuition. 
  econstructor; eauto.
  destruct b; eapply analysis_correct_1; eauto; simpl; auto;
  unfold transfer; rewrite H; auto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial. }

{ (* Ijumptable *)
  TransfInstr; intros C.
  eexists; eexists; eexists; split.
    eapply rtl_effstep_exec_Ijumptable; eauto. 
   specialize (RI arg). rewrite H0 in RI; inv RI. trivial.
  exists mu.
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
             repeat split; extensionality bb; 
                try rewrite (freshloc_irrefl); intuition.
  split. 2: intuition.
  split. 2: intuition. 
  econstructor; eauto.
  eapply analysis_correct_1; eauto. simpl. eapply list_nth_z_in; eauto.
  unfold transfer; rewrite H; auto. }

{ (* Ireturn *)
  TransfInstr; intros C.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  destruct SP as [spb [spb' [B [B' Rsp]]]]; subst. inv B.  
  rewrite restrict_sm_local in Rsp.
  destruct (restrictD_Some _ _ _ _ _ Rsp) as [LocSp visSp]. 
  assert (SP:= local_in_all _ WD _ _ _ LocSp). 
  exploit free_parallel_inject; eauto. 
     apply restrictI_Some; eassumption. 
  simpl; rewrite Zplus_0_r; intros [m'' [P Q]].
  assert (SMV': sm_valid mu m' m'').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
  eexists; eexists; eexists; split.
    eapply rtl_effstep_exec_Ireturn; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
            repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _  P);
            try rewrite (freshloc_free _ _ _ _ _  H0); intuition.
  split. 
    split.  
      econstructor; eauto.
        exploit wt_instr_at; eauto. intros WTI; inv WTI; simpl. auto.
        unfold proj_sig_res; rewrite H2. eapply Val.has_subtype; eauto.
        destruct or; simpl. apply RI. constructor. 
      intuition.
        eapply REACH_closed_free; eassumption.
          eapply free_free_inject; try eassumption.
            simpl. rewrite Zplus_0_r. apply P.
  intuition.
      eapply FreeEffectD in H1. destruct H1 as [? [VB Arith]]; subst. 
         eapply visPropagate; eassumption.
      eapply FreeEffect_PropagateLeft; eassumption. }

{ (* internal function *)
  monadInv H8. unfold transf_function in EQ. 
  destruct (type_function f) as [tyenv|] eqn:?; try discriminate.
  destruct (analyze f) as [approx|] eqn:?; inv EQ. 
  assert (WTF: wt_function f tyenv). apply type_function_correct; auto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl. 
      intros [mu' [m2' [stk' [Alloc' [INJ' [IntInc' [HA [HB [HC [HD [HE [HF HG]]]]]]]]]]]]. 
  eexists; eexists; eexists; split.
    eapply rtl_effstep_exec_function_internal; eauto. 
  exists mu'.
  split. assumption.
    split. solve[eapply intern_incr_globals_separate; eauto]. 
  split. assumption.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    intros ? ? ? Rb. destruct (restrictD_Some _ _ _ _ _ Rb).
    eapply restrictI_Some.
    eapply intern_incr_as_inj; try eassumption.
    eapply intern_incr_vis; eassumption.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
  assert (TgtB2: DomTgt mu stk' = false).
        remember (DomTgt mu stk') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
  assert (locSP: local_of mu' stk = Some (stk', 0)).
    destruct (joinD_Some _ _ _ _ _ HA) as [EXT | [EXT LOC]]; trivial.
    rewrite <- (intern_incr_extern _ _ IntInc') in EXT. 
      assert (DomSrc mu stk = true). eapply extern_DomRng'; eassumption.
      congruence.
  split. 
    split; simpl. 
      econstructor; eauto.
        apply wt_init_regs. inv WTF. eapply Val.has_subtype_list; eauto.
        apply analysis_correct_entry; auto.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
          eapply regset_init_regs. 
          eapply val_list_inject_incr; eassumption.
        exists stk, stk'. rewrite restrict_sm_local'; auto. 
        eapply match_stackframes_intern_incr; try eassumption.
          eapply restrict_sm_intern_incr; eassumption.
          apply restrict_sm_WD; trivial.
      intuition.
        eapply meminj_preserves_incr_sep_vb with (m0:=m)(tm:=m2). eapply PG.
          intros. apply as_inj_DomRng in H1.
                  split; eapply SMV; eapply H1.
          assumption.
        apply intern_incr_as_inj; eassumption.
        apply sm_inject_separated_mem. assumption.
        assumption.
        red; intros. destruct (GFP _ _ H1). split; trivial.
           eapply intern_incr_as_inj; eassumption.
        rewrite <- (intern_incr_frgnBlocksSrc _ _ IntInc'). auto.
    intuition. }

{ (* external function : only nonobservables*)
  monadInv H8.   
  specialize (EFhelpers _ _ OBS); intros OBS'.   
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  exploit (inlineable_extern_inject ge tge); try eapply PRE; try eassumption; try apply GDE_lemma. 
  intros [mu' [v' [m'' [TEC [ResInj [MINJ' [UNMAPPED [LOOR [INC [SEP [GSEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]]]].
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_function_external; eauto.
  exists mu'.
  split. assumption. 
  split. assumption. 
  split. assumption. 
  split. 
    split. 
      econstructor; eauto.
        eapply match_stackframes_intern_incr; try eassumption.
          eapply restrict_sm_intern_incr; eassumption.
          apply restrict_sm_WD; trivial.
        simpl. eapply external_call_well_typed; eauto. 
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
    intuition.
      eapply meminj_preserves_incr_sep_vb with (m0:=m)(tm:=m2). eapply PG.
          intros ? ? ? AI. apply as_inj_DomRng in AI.
                  split; eapply SMV; eapply AI.
          assumption.
        apply intern_incr_as_inj; eassumption.
        apply sm_inject_separated_mem. assumption.
        assumption.
      intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
           eapply intern_incr_as_inj; eassumption.
        rewrite <- (intern_incr_frgnBlocksSrc _ _ INC). auto.
  split. trivial. split. trivial.
  intros. eapply BuiltinEffect_Propagate; try eassumption. }

{ (* return *)
  inv H1.
  eexists; eexists; eexists; split. 
    eapply rtl_effstep_exec_return; eauto.
  exists mu. 
  split. apply intern_incr_refl. 
  split. solve [apply gsep_refl].
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality b'; 
            try rewrite (freshloc_irrefl); intuition.
  split. 2: intuition.
  split. 2: intuition.
  econstructor; eauto.
    apply wt_regset_assign; auto. eapply Val.has_subtype; eauto.  
    eapply regset_set; assumption. }
Qed.

Theorem transl_program_correct:
  forall (LNR: list_norepet (map fst (prog_defs prog)))
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
SM_simulation.SM_simulation_inject (rtl_eff_sem hf)
  (rtl_eff_sem hf) ge tge.
Proof.
intros.
assert (GDE:= GDE_lemma).
 eapply inj_simulation_plus_typed with
  (match_states:=fun x mu st m st' m' => MATCH mu st m st' m')
  (measure:=fun x => O).
(*genvs_dom_eq*)
  assumption.
(*match_wd*)
  intros; apply H.
(*match_visible*)
  intros. apply H.
(*match_restrict
  intros x. apply MATCH_restrict.*)
(*match_valid*)
  intros. apply H.
(*match_genv*)
  intros x. eapply MATCH_PG. 
(*initial_core*)
  { intros.
    eapply (MATCH_initial _ _ _); eauto.
    destruct init_mem as [m0 INIT].
    exists m0; split; auto.
    unfold meminj_preserves_globals in H2.    
    destruct H2 as [A [B C]].

    assert (P: forall p q, {Ple p q} + {Plt q p}).
      intros p q.
      case_eq (Pos.leb p q).
      intros TRUE.
      apply Pos.leb_le in TRUE.
      left; auto.
      intros FALSE.
      apply Pos.leb_gt in FALSE.
      right; auto.

    cut (forall b, Plt b (Mem.nextblock m0) -> 
           exists id, Genv.find_symbol ge id = Some b). intro D.
    
    split.
    destruct (P (Mem.nextblock m0) (Mem.nextblock m1)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H2.
    assert (Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - H8; unfold Mem.valid_block in H8.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H2.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H8; unfold Mem.valid_block in H8.
    xomega.
    
    intros b LT.    
    unfold ge. 
    apply valid_init_is_global with (b0 := b) in INIT.
    eapply INIT; auto.
    apply LNR.
    apply LT. }
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]]. 
    destruct c1; inv H0. destruct stack; inv H1.
    inv MC. exists v'.
    split. assumption.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
    split. eassumption.
    simpl. inv H1. trivial. }
(* at_external*)
  { apply MATCH_atExternal. }
(* after_external*)
  { apply MATCH_afterExternal. }
(*effcore_diagram*)
 { intros. exploit MATCH_effcore_diagram; try eassumption.
   intros [st2' [m2' [U2 [CS' [mu' [INC [GSEP
       [LOCALLOC [MTCH [WD' [SVM' UH]]]]]]]]]]]. 
   exists st2', m2', mu'.
     repeat (split; trivial).
     exists U2. split; trivial.
     left. apply effstep_plus_one; assumption. }
Qed.

End PRESERVATION.
