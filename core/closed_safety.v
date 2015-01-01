Require Import compcert_imports. Import CompcertLibraries.

Require Import semantics.
Require Import semantics_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section closed_safety.

Variable (G C D Z M : Type).

Variable sem : CoreSemantics G C M.

Variable ge : G.

Fixpoint safeN (n : nat) (c : C) (m : M) : Prop :=
  match n with
    | O => True
    | S n' => 
      match halted sem c with
        | None => 
          (exists c', exists m', corestep sem ge c m c' m') /\
          (forall c' m', corestep sem ge c m c' m' -> safeN n' c' m') 
        | Some i => True
      end
  end.

Fixpoint safeN_det (n : nat) (c : C) (m : M) : Prop :=
  match n with
    | O => True
    | S n' => 
      match halted sem c with
        | None => exists c', exists m', 
                    corestep sem ge c m c' m' /\ safeN_det n' c' m'
        | Some i => True
      end
  end.

Lemma det_safeN_det n c m : 
  corestep_fun sem -> 
  safeN_det n c m -> 
  safeN n c m.
Proof.
intros Hfun; revert c m; induction n; simpl; auto.
intros c m.
destruct (halted sem c); auto.
intros [c' [m' [Hstep Hsafe]]].
split.
exists c', m'; auto.
intros c'' m'' Hstep'.
destruct (Hfun _ _ _ _ _ _ _ Hstep Hstep').
subst c' m'; apply IHn; auto.
Qed.

Lemma safe_downward1 n c m : safeN (S n) c m -> safeN n c m.
Proof.
revert c m; induction n; simpl; intros; auto.
destruct (halted sem c); auto.
destruct H as [H H0].
destruct H as [c' [m' H2]].
split. exists c', m'; auto.
intros c'' m'' H3. 
specialize (H0 _ _ H3). destruct n; auto.
Qed.

Lemma safe_downward (n n' : nat) c m :
  le n' n -> safeN n c m -> safeN n' c m.
Proof.
do 2 intro. revert c m H0. induction H; auto.
intros. apply IHle. apply safe_downward1. auto.
Qed.

Lemma safe_corestep_forward c m c' m' n :
  corestep sem ge c m c' m' -> safeN (S n) c m -> 
  safeN n c' m'.
Proof.
simpl; intros. 
generalize H as H'; intro.
eapply corestep_not_halted in H; rewrite H in H0.
destruct H0 as [H1 H2]. clear H H1.
apply H2; auto.
Qed.

Lemma safe_corestepN_forward c m c' m' n n0 :
  corestepN sem ge n0 c m c' m' -> 
  safeN (n + S n0) c m -> safeN n c' m'.
Proof.
intros.
revert c m c' m' n H H0.
induction n0; intros; auto.
simpl in H; inv H.
eapply safe_downward in H0; eauto. omega.
simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
eapply IHn0; eauto.
assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by omega.
rewrite Heq in H0.
eapply safe_corestep_forward in H0; eauto.
Qed.

Lemma safe_corestep_backward:
  forall c m c' m' n,
    corestep_fun sem ->
    corestep sem ge c m c' m' -> safeN (n - 1) c' m' -> safeN n c m.
Proof.
simpl; intros.
revert c m c' m' H H0 H1.
induction n; simpl; intros; auto.
erewrite corestep_not_halted; eauto.
split.
exists c', m'; auto.
intros c'' m'' Hstep.
assert (Heq: (n = S n - 1)%nat) by omega.
rewrite Heq; simpl.
assert (n - 0 = n)%nat as -> by omega.
destruct (H _ _ _ _ _ _ _ H0 Hstep).
subst c''; subst m''; auto.
Qed.

Lemma safe_corestepN_backward:
  forall c m c' m' n n0,
    corestep_fun sem ->
    corestepN sem ge n0 c m c' m' -> safeN (n - n0) c' m' -> safeN n c m.
Proof.
simpl; intros.
revert c m c' m' n H H0 H1.
induction n0; intros; auto.
simpl in H0; inv H0.
solve[assert (Heq: (n = n - 0)%nat) by omega; rewrite Heq; auto].
simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
assert (H2: safeN (n - 1 - n0) c' m'). 
eapply safe_downward in H1; eauto. omega.
specialize (IHn0 _ _ _ _ (n - 1)%nat H STEPN H2). 
eapply safe_corestep_backward; eauto.
Qed.

Lemma corestep_star_fun : 
  corestep_fun sem -> 
  forall c m c' m' c'' m'' n,
  corestepN sem ge n c m c' m' -> 
  corestepN sem ge n c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
intro FUN. intros. revert c m H H0. induction n; auto.
simpl. intros ? ?. inversion 1; subst. inversion 1; subst. 
split; auto.
simpl.
intros c m H H2.
destruct H as [c2 [m2 [STEP STEPN]]].
destruct H2 as [c2' [m2' [STEP' STEPN']]].
assert (c2 = c2' /\ m2 = m2').
  unfold corestep_fun in FUN. eapply FUN; eauto.
inv H.
eapply IHn; eauto.
Qed.

End closed_safety.

(** Behaviors-related stuff; should probably go in a new file. *)

Definition terminates {G C M} (csem : CoreSemantics G C M) 
    (ge : G) (c : C) (m : M) :=
  exists c' m', corestep_star csem ge c m c' m' 
  /\ exists v, halted csem c' = Some v.

Definition safe {G C M} (csem : CoreSemantics G C M) ge c m :=
  forall n, safeN csem ge n c m.

Definition forever_steps_or_halted {G C M} (csem : CoreSemantics G C M) ge c m :=
  forall n, safeN_det csem ge n c m.

Lemma safeN_safeN_det G C M (csem : CoreSemantics G C M) ge c m n :
  safeN csem ge n c m -> 
  safeN_det csem ge n c m.
Proof.
revert c m; induction n; auto.
intros c m; simpl.
destruct (halted csem c); auto.
intros [[c' [m' Hhlt]] H].
exists c', m'; split; auto.
Qed.

Lemma safe_forever_steps_or_halted G C M (csem : CoreSemantics G C M) ge c m :
  safe csem ge c m -> 
  forever_steps_or_halted csem ge c m.
Proof.
intros H n; specialize (H n); apply safeN_safeN_det; auto.
Qed.

Inductive behavior : Type := Termination | Divergence | Going_wrong.

Inductive has_behavior {G C M} (csem : CoreSemantics G C M) ge c m : behavior -> Prop :=
  | Terminates : 
      terminates csem ge c m -> has_behavior csem ge c m Termination
  | Diverges : 
      forever_steps_or_halted csem ge c m -> ~terminates csem ge c m -> 
      has_behavior csem ge c m Divergence
  | Goes_wrong :
      ~safe csem ge c m -> has_behavior csem ge c m Going_wrong.

Inductive behavior_refines : behavior -> behavior -> Prop :=
  | Equitermination : behavior_refines Termination Termination 
  | Equidivergence : behavior_refines Divergence Divergence
  | Any_going_wrong : forall any, behavior_refines any Going_wrong.

