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
Require Import semantics_lemmas.

(** * Cooperating Interaction Semantics *)

(** Cooperating semantics impose additional constraints; in particular, they
   specialize interaction semantics to CompCert memories and require that the
   memories produced by coresteps are [forward] wrt. the initial memory. See
   [core/mem_lemmas.v] for the defn. of [mem_forward]. *)

Record CoopCoreSem {G C} :=
  { coopsem :> CoreSemantics G C mem
  ; corestep_fwd : 
      forall g c m c' m' (CS: corestep coopsem g c m c' m'), 
      mem_forward m m'
  ; corestep_rdonly: 
      forall g c m c' m' (CS: corestep coopsem g c m c' m') b, 
      Mem.valid_block m b -> readonly m b m'}.

Implicit Arguments CoopCoreSem [].

Definition MemSem2CoopCoreSem {G C} (s:@MemSem G C): @CoopCoreSem G C.
Proof.
eapply Build_CoopCoreSem with (coopsem := s).
apply semantics_lemmas.corestep_fwd.
apply semantics_lemmas.corestep_rdonly.
Defined.

(* superseded by MemSem
Definition decay m m' := forall b ofs, 
    (~Mem.valid_block m b -> forall p, Mem.perm m' b ofs Cur p -> Mem.perm m' b ofs Cur Freeable) /\
    (Mem.perm m b ofs Cur Freeable -> forall p, Mem.perm m' b ofs Cur p -> Mem.perm m' b ofs Cur Freeable) /\
    (~Mem.perm m b ofs Cur Freeable -> forall p, Mem.perm m b ofs Cur p -> Mem.perm m' b ofs Cur p) /\
    (Mem.valid_block m b -> forall p, Mem.perm m' b ofs Cur p -> Mem.perm m b ofs Cur p).

Lemma decay_refl m: decay m m.
Proof. red; intros; intuition.
  apply Mem.perm_valid_block in H0; contradiction.
Qed.

Lemma decay_trans m m' m'' (F: mem_forward m m'): decay m m' -> decay m' m'' -> decay m m''.
Proof. red; intros.
  destruct (H b ofs) as [K1 [K2 [K3 K4]]].
  destruct (H0 b ofs) as [L1 [L2 [L3 L4]]].
  repeat split; intros.
+ destruct (valid_block_dec m' b); eauto.
+ eapply L2; eauto. eapply K2; try eassumption. eapply L4; try eassumption. apply F. eapply Mem.perm_valid_block; eassumption.
+ eapply L3; eauto. intros N. specialize (K3 H1 _ H2). apply Mem.perm_valid_block in H2. eapply H1. eapply K4; eassumption.
+ apply K4; trivial. apply L4; trivial. apply F; trivial. 
Qed.

Lemma store_decay m b ofs v ch m': Mem.store ch m b ofs v = Some m' -> decay m m'.
Proof. intros.
  repeat split; intros.
+ apply Mem.perm_valid_block in H1. 
  elim H0; clear H0. eapply Mem.store_valid_block_2; eassumption.
+ eapply Mem.perm_store_1; eassumption.
+ eapply Mem.perm_store_1; eassumption.
+ eapply Mem.perm_store_2; eassumption.
Qed.

Lemma alloc_decay m lo hi m' b: Mem.alloc m lo hi = (m', b) -> decay m m'.
Proof. intros.
  repeat split; intros.
+ specialize (Mem.perm_alloc_inv _ _ _ _ _ H _ _ _ _ H1); intros.
  destruct (eq_block b0 b); subst.
    apply (Mem.perm_alloc_2 _ _ _ _ _ H ofs Cur H2).
  elim H0. eapply Mem.perm_valid_block; eassumption.
+ specialize (Mem.perm_alloc_inv _ _ _ _ _ H _ _ _ _ H1); intros.
  destruct (eq_block b0 b); subst.
    apply (Mem.perm_alloc_2 _ _ _ _ _ H ofs Cur H2).
  apply (Mem.perm_alloc_1 _ _ _ _ _ H _ _ _ _ H0).
+ apply (Mem.perm_alloc_1 _ _ _ _ _ H _ _ _ _ H1).  
+ eapply Mem.perm_alloc_4; try eassumption.
  intros N; subst. eapply Mem.fresh_block_alloc; eassumption.
Qed.   

Lemma free_decay m b lo hi m': Mem.free m b lo hi = Some m' -> decay m m'.
Proof. intros.
 repeat split; intros.
+ specialize (Mem.perm_free_3 _ _ _ _ _ H _ _ _ _ H1); intros.
  apply Mem.perm_valid_block in H2. contradiction.
+ destruct (Mem.perm_free_inv _ _ _ _ _ H _ _ _ _ H0); trivial.
  destruct H2; subst b0. eelim Mem.perm_free_2; eassumption.
+ specialize (Mem.free_range_perm _ _ _ _ _ H); intros.
  eapply Mem.perm_free_1; try eassumption.
  destruct (eq_block b0 b); subst. 2: left; trivial. right.
  destruct (zlt ofs lo). left; trivial. right. 
  destruct (zle hi ofs); trivial.
  elim H0. apply H2. omega. 
+ eapply Mem.perm_free_3; eassumption.
Qed.

Lemma freelist_decay: forall l m m', Mem.free_list m l = Some m' -> decay m m'.
Proof. induction l; simpl; intros.
  inv H. apply decay_refl.
  destruct a. destruct p. remember (Mem.free m b z0 z) as d.
  destruct d; inv H; symmetry in Heqd. 
  eapply decay_trans. 
  eapply free_forward; eassumption.
  eapply free_decay; eassumption.
  auto.
Qed.

Lemma storebytes_decay m b ofs bytes m': Mem.storebytes m b ofs bytes = Some m' -> decay m m'.
Proof. intros.
  repeat split; intros.
+ apply Mem.perm_valid_block in H1. 
  elim H0; clear H0. eapply Mem.storebytes_valid_block_2; eassumption.
+ eapply Mem.perm_storebytes_1; eassumption.
+ eapply Mem.perm_storebytes_1; eassumption.
+ eapply Mem.perm_storebytes_2; eassumption.
Qed.

Lemma ec_decay ef (F V : Type) (ge : Genv.t F V) vargs m1 t vres m2:
      external_call ef ge vargs m1 t vres m2 -> decay m1 m2.
Proof. intros EC.
destruct ef; simpl in *; inv EC; try apply decay_refl.
{ inv H. apply decay_refl. eapply store_decay; eassumption. }
{ inv H0. apply decay_refl. eapply store_decay; eassumption. }
{ eapply decay_trans. eapply alloc_forward; eassumption. 
  eapply alloc_decay; eassumption. 
  eapply store_decay; eassumption. }
{ eapply free_decay; eassumption. }
{ eapply storebytes_decay; eassumption. } 
Qed.

Theorem decay_preserve: memstep_preserve (fun m m' => mem_forward m m' /\ decay m m').
Proof.
constructor.
+ intros; split. eapply mem_forward_trans. apply H. apply H0.
  eapply decay_trans. apply H. apply H. apply H0.
+ intros; induction H. 
  split; intros. eapply storebytes_forward; eassumption.
    eapply storebytes_decay; eassumption.
  split; intros. eapply alloc_forward; eassumption.
    eapply alloc_decay; eassumption.
  intros; split. eapply freelist_forward; eassumption.
    eapply freelist_decay; eassumption.
  destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    eapply decay_trans; eassumption.
Qed.

Record DecayCoreSem {G C} :=
  { decaysem :> @CoopCoreSem G C 
  ; corestep_decay : forall g c m c' m'
       (CS: corestep decaysem g c m c' m'), decay m m'}.


Definition myDecaySem {G C} (s:@MemSem G C): @DecayCoreSem G C.
Proof.
eapply Build_DecayCoreSem with (decaysem := myCoopCoreSem s).
simpl. eapply (memsem_preserves s _ decay_preserve); eassumption.
Defined.
*)