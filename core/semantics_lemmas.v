(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST. 
Require Import Globalenvs.
Require Import Axioms.

Require Import mem_lemmas.
Require Import semantics.

Definition corestep_fun {G C M : Type} (sem : CoreSemantics G C M) :=
  forall (m m' m'' : M) ge c c' c'',
  corestep sem ge c m c' m' -> 
  corestep sem ge c m c'' m'' -> 
  c'=c'' /\ m'=m''.

(**  Multistepping *)

Section corestepN.
  Context {G C M:Type} (Sem:CoreSemantics G C M) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
      | O => fun c m c' m' => (c,m) = (c',m')
      | S k => fun c1 m1 c3 m3 => exists c2, exists m2,
        corestep Sem ge c1 m1 c2 m2 /\
        corestepN k c2 m2 c3 m3
    end.

  Lemma corestepN_add : forall n m c1 m1 c3 m3,
    corestepN (n+m) c1 m1 c3 m3 <->
    exists c2, exists m2,
      corestepN n c1 m1 c2 m2 /\
      corestepN m c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m x x0 c3 m3).
    apply H in H2. 
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m x1 x2 c3 m3). 
    eauto.
  Qed.

  Definition corestep_plus c m c' m' :=
    exists n, corestepN (S n) c m c' m'.

  Definition corestep_star c m c' m' :=
    exists n, corestepN n c m c' m'.

  Lemma corestep_plus_star : forall c1 c2 m1 m2,
    corestep_plus c1 m1 c2 m2 -> corestep_star c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma corestep_plus_trans : forall c1 c2 c3 m1 m2 m3,
    corestep_plus c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 -> 
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add (S n1) (S n2) c1 m1 c3 m3) as [_ H].
    eexists. apply H. exists c2. exists m2. split; assumption.
  Qed.

  Lemma corestep_star_plus_trans : forall c1 c2 c3 m1 m2 m3,
    corestep_star c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 -> 
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add n1 (S n2) c1 m1 c3 m3) as [_ H]. 
    rewrite <- plus_n_Sm in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_plus_star_trans: forall c1 c2 c3 m1 m2 m3,
    corestep_plus c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 -> 
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add (S n1) n2 c1 m1 c3 m3) as [_ H]. 
    rewrite plus_Sn_m in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_star_trans: forall c1 c2 c3 m1 m2 m3, 
    corestep_star c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 -> 
    corestep_star c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add n1 n2 c1 m1 c3 m3) as [_ H]. 
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_plus_one: forall c m c' m',
    corestep  Sem ge c m c' m' -> corestep_plus c m c' m'.
  Proof. intros. unfold corestep_plus, corestepN. simpl.
    exists O. exists c'. exists m'. eauto. 
  Qed.

  Lemma corestep_plus_two: forall c m c' m' c'' m'',
    corestep  Sem ge c m c' m' -> corestep  Sem ge c' m' c'' m'' -> 
    corestep_plus c m c'' m''.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. 
    exists c''. exists m''. split; trivial. reflexivity.
  Qed.

  Lemma corestep_star_zero: forall c m, corestep_star  c m c m.
  Proof. intros. exists O. reflexivity. Qed.

  Lemma corestep_star_one: forall c m c' m',
    corestep  Sem ge c m c' m' -> corestep_star c m c' m'.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. reflexivity. 
  Qed.

  Lemma corestep_plus_split: forall c m c' m',
    corestep_plus c m c' m' ->
    exists c'', exists m'', corestep  Sem ge c m c'' m'' /\ 
      corestep_star c'' m'' c' m'.
  Proof. intros.
    destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*. 
    exists c2. exists m2. split. assumption. exists n. assumption.  
  Qed.

End corestepN.

Section memstepN.
  Context {G C:Type} (M:@MemSem G C) (g:G).

Lemma corestepN_mem n: forall c m c' m', corestepN M g n c m c' m' -> mem_step m m'.
induction n; intros; inv H.
  apply mem_step_refl.
  destruct H0 as [m'' [CS CSN]]. eapply mem_step_trans. 
  eapply corestep_mem; eassumption.
  eapply IHn; eassumption.
Qed.

Lemma corestep_plus_mem c m c' m' (H:corestep_plus M g c m c' m'): mem_step m m'.
destruct H as [n H]. eapply corestepN_mem; eassumption. Qed.

Lemma corestep_star_mem c m c' m' (H:corestep_star M g c m c' m'): mem_step m m'.
destruct H as [n H]. eapply corestepN_mem; eassumption. Qed.

Lemma memsem_preservesN P (HP: memstep_preserve P)
      n c m c' m' (H: corestepN M g n c m c' m'): P m m'.
apply corestepN_mem in H. apply HP; trivial. Qed. 

Lemma memsem_preserves_plus P (HP:memstep_preserve P)
      c m c' m' (H: corestep_plus M g c m c' m'): P m m'.
destruct H. apply (memsem_preservesN _ HP) in H; trivial. Qed.

Lemma memsem_preserves_star P (HP:memstep_preserve P)
      c m c' m' (H: corestep_star M g c m c' m'): P m m'.
destruct H. apply (memsem_preservesN _ HP) in H; trivial. Qed.

Lemma corestepN_fwd n  c m c' m'
   (CS:corestepN M g n c m c' m'): mem_forward m m'.
Proof.
eapply memsem_preservesN; try eassumption. apply mem_forward_preserve.
Qed.

Lemma corestep_plus_fwd c m c' m'
   (CS:corestep_plus M g c m c' m'): mem_forward m m'.
Proof.
destruct CS. eapply corestepN_fwd; eassumption.
Qed.

Lemma corestep_star_fwd c m c' m'
   (CS:corestep_star M g c m c' m'): mem_forward m m'.
Proof.
destruct CS. eapply corestepN_fwd; eassumption.
Qed.
 
Lemma corestepN_rdonly n c m c' m'
    (CS:corestepN M g n c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
eapply (memsem_preservesN _ readonly_preserve'); eassumption.
Qed.

Lemma corestep_plus_rdonly c m c' m'
   (CS:corestep_plus M g c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
destruct CS. eapply corestepN_rdonly; eassumption.
Qed.

Lemma corestep_star_rdonly c m c' m'
   (CS:corestep_star M g c m c' m')b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
destruct CS. eapply corestepN_rdonly; eassumption.
Qed.
 
End memstepN.


