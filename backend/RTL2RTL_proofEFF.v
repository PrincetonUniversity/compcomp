Require Import Coqlib.
Require Import Maps.
Require Import Globalenvs.
Require Import Registers.
Require Import Values.
Require Import RTL.
Require Import StructuredInjections.

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
