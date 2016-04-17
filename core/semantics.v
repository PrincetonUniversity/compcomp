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

(** * Interaction Semantics *)

(** NOTE: In the code, we call interaction semantics [CoreSemantics]. *)

(** The [G] type parameter is the type of global environments, the type
   [C] is the type of core states, and the type [E] is the type of
   extension requests. *)

(** [at_external] gives a way to determine when the sequential
   execution is blocked on an extension call, and to extract the
   data necessary to execute the call. *)
   
(** [after_external] give a way to inject the extension call results
   back into the sequential state so execution can continue. *)

(** [initial_core] produces the core state corresponding to an entry
   point of a module.  The arguments are the genv, a pointer to the
   function to run, and the arguments for that function. *)

(** [halted] indicates when a program state has reached a halted state,
   and what it's exit code/return value is when it has reached such
   a state. *)

(** [corestep] is the fundamental small-step relation for the
   sequential semantics. *)

(** The remaining properties give basic sanity properties which constrain
   the behavior of programs. *)
(** -1 a state cannot be both blocked on an extension call and also step, *)
(** -2 a state cannot both step and be halted, and *)
(** -3 a state cannot both be halted and blocked on an external call. *)

Record CoreSemantics {G C M : Type} : Type :=
  { initial_core : G -> val -> list val -> option C
  ; at_external : C -> option (external_function * signature * list val)
  ; after_external : option val -> C -> option C
  ; halted : C -> option val
  ; corestep : G -> C -> M -> C -> M -> Prop

  ; corestep_not_at_external: 
      forall ge m q m' q', corestep ge q m q' m' -> at_external q = None
  ; corestep_not_halted: 
      forall ge m q m' q', corestep ge q m q' m' -> halted q = None
  ; at_external_halted_excl: 
      forall q, at_external q = None \/ halted q = None }.

Implicit Arguments CoreSemantics [].

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

Record DecayCoreSem {G C} :=
  { decaysem :> @CoopCoreSem G C 
  ; corestep_decay : forall g c m c' m'
       (CS: corestep decaysem g c m c' m'), decay m m'}.

Implicit Arguments CoopCoreSem [].

Inductive mem_step m m' : Prop :=
    mem_step_storebytes: forall b ofs bytes,
       Mem.storebytes m b ofs bytes = Some m' -> mem_step m m'
  | mem_step_alloc: forall lo hi b',
       Mem.alloc m lo hi = (m',b') -> mem_step m m'
  | mem_step_freelist: forall l,
       Mem.free_list m l = Some m' -> mem_step m m'
  (*Some non-observable external calls do alloc;store, so are not a single mem-step*)
  | mem_step_trans: forall m'',
       mem_step m m'' -> mem_step m'' m' -> mem_step m m'.

Lemma mem_step_refl m: mem_step m m.
  apply (mem_step_freelist _ _ nil); trivial.
Qed. 
 
Lemma mem_step_free: 
      forall m b lo hi m', Mem.free m b lo hi = Some m' -> mem_step m m'.
Proof.
 intros. eapply (mem_step_freelist _ _ ((b,lo,hi)::nil)). 
 simpl. rewrite H; reflexivity.
Qed.

Lemma mem_step_store: 
      forall m ch b a v m', Mem.store ch m b a v = Some m' -> mem_step m m'.
Proof.
 intros. eapply mem_step_storebytes. eapply Mem.store_storebytes; eassumption. 
Qed.

Record memstep_preserve (P:mem -> mem -> Prop) :=
  { 
    preserve_trans: forall m1 m2 m3, P m1 m2 -> P m2 m3 -> P m1 m3;
    preserve_mem: forall m m', mem_step m m' -> P m m'
  }.

Lemma preserve_refl {P} (HP: memstep_preserve P): forall m, P m m.
Proof. intros. eapply (preserve_mem _ HP). apply mem_step_refl. Qed.

Lemma preserve_free {P} (HP: memstep_preserve P): 
      forall m b lo hi m', Mem.free m b lo hi = Some m' -> P m m'.
Proof.
 intros. eapply (preserve_mem _ HP). eapply mem_step_free; eauto. Qed.

Theorem preserve_conj {P Q} (HP:memstep_preserve P) (HQ: memstep_preserve Q):
        memstep_preserve (fun m m' => P m m' /\ Q m m').
Proof.
intros. constructor.
+ intros. destruct H; destruct H0. split. eapply HP; eauto. eapply HQ; eauto.
+ intros; split. apply HP; trivial. apply HQ; trivial. 
Qed.

(*opposite direction appears not to hold*)
Theorem preserve_impl {A} (P:A -> mem -> mem -> Prop) (Q:A->Prop):
        (forall a, Q a -> memstep_preserve (P a)) -> memstep_preserve (fun m m' => forall a, Q a -> P a m m').
Proof.
intros.
constructor; intros.
+ eapply H; eauto. 
+ apply H; eauto.
Qed.

Lemma preserve_exensional {P Q} (HP:memstep_preserve P) (PQ:P=Q): memstep_preserve Q.
subst; trivial. Qed.

(*opposite direction appears not to hold*)
Theorem preserve_univ {A} (P:A -> mem -> mem -> Prop):
        (forall a, memstep_preserve (P a)) -> memstep_preserve (fun m m' => forall a, P a m m').
Proof. intros.
eapply preserve_exensional.
eapply (@preserve_impl A (fun a m m'=> P a m m') (fun a=>True)). 
intros. apply H. extensionality m. extensionality m'. apply prop_ext. intuition.
Qed.

Theorem mem_forward_preserve: memstep_preserve mem_forward.
Proof.
constructor.
+ apply mem_forward_trans.
+ intros. induction H.
  eapply storebytes_forward; eassumption. 
  eapply alloc_forward; eassumption. 
  eapply freelist_forward; eassumption.
  eapply mem_forward_trans; eassumption.
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

Theorem readonly_preserve b: memstep_preserve (fun m m' => mem_forward m m' /\ (Mem.valid_block m b -> readonly m b m')).
Proof.
constructor.
+ intros. destruct H; destruct H0. 
  split; intros. eapply mem_forward_trans; eassumption.
  eapply readonly_trans; eauto. apply H2. apply H. eassumption.
+ intros; induction H. 
  - split; intros. eapply storebytes_forward; eassumption.
    eapply storebytes_readonly; eassumption.
  - intros. 
    split; intros. eapply alloc_forward; eassumption.
    eapply alloc_readonly; eassumption.
  - intros.
    split; intros. eapply freelist_forward; eassumption.
    eapply freelist_readonly; eassumption.
  - destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    intros. eapply readonly_trans. eauto. apply H4. apply H1; eassumption.
Qed.

Theorem readonly_preserve': 
   memstep_preserve (fun m m' => mem_forward m m' /\ (forall b, Mem.valid_block m b -> readonly m b m')).
Proof. 
eapply preserve_exensional.
eapply preserve_univ; intros. apply (readonly_preserve a).
  extensionality m. extensionality m'. apply prop_ext.
  split; intros. split. eapply H. apply xH. intros. eapply (H b). trivial. 
  destruct H. split; eauto. 
Qed.

Record MemSem {G C} :=
  { csem :> @CoreSemantics G C mem

  ; corestep_mem : forall g c m c' m' (CS: corestep csem g c m c' m'), mem_step m m'
  }.

Lemma memsem_preserves {G C} (s: @MemSem G C) P (HP:memstep_preserve P):
      forall g c m c' m', corestep s g c m c' m'-> P m m'.
Proof. intros.
  apply corestep_mem in H.
  eapply preserve_mem; eassumption.
Qed.

(*

Lemma coalg_preserves {G C} (s: @CoalgSem G C) P (HP:step_preserve P):
      forall n  c m c' m', corestepN n s g c m c' m'-> P m m'.
Proof. intros.
  apply corestepD in H.
  destruct H as [? | [[? [? [? ?]]] | [[? [? [? ?]]]| [? ?]]]]; subst; trivial.
  apply HP.
  eapply (preserve_storebytes _ HP); eassumption. 
  eapply (preserve_alloc _ HP); eassumption.
  generalize dependent m. rename x into l.
  induction l; simpl; intros. 
  + inv H. apply HP.
  + destruct a. destruct p. remember (Mem.free m b z0 z) as q.
    symmetry in Heqq; destruct q; inv H. 
    eapply (preserve_trans _ HP).  eapply (preserve_free _ HP); eassumption. apply IHl. eassumption.
Qed.
eapply HPA; eassumption. 
eapply HPFL; eassumption.
  des

Definition mkPsem {G C} (P:mem -> Prop) (s: @CoalgSem G C) (HP:step_preserve P): @PreserveSem G C P.
destruct s as [SEM HSEM].
eapply Build_PreserveSem with (psem:=SEM); intros.
specialize (freelist_preserve HP); intros HPFL.
apply HSEM in CS; clear HSEM. destruct HP as [HPS HPA _].
destruct CS as [? | [[? [? [? ?]]] | [[? [? [? ?]]]| [? ?]]]]; subst; trivial.
eapply HPS; eassumption. 
eapply HPA; eassumption. 
eapply HPFL; eassumption.
Defined. 


Record PreserveSem' {G C P} (HP: step_preserve P):=
  { qsem :> @CoopCoreSem G C 
  ; corestep_pres : forall g c m c' m'
       (CS: corestep qsem g c m c' m'), P m -> P m'}.

Definition mkQsem {G C} (P:mem -> Prop) (s: @CoalgSem G C) (HP:step_preserve P): @PreserveSem' G C _ HP.
destruct s as [SEM HSEM].
eapply Build_PreserveSem' with (qsem:=SEM); intros.
specialize (freelist_preserve HP); intros HPFL.
apply HSEM in CS; clear HSEM. destruct HP as [HPS HPA _].
destruct CS as [? | [[? [? [? ?]]] | [[? [? [? ?]]]| [? ?]]]]; subst; trivial.
eapply HPS; eassumption. 
eapply HPA; eassumption. 
eapply HPFL; eassumption.
Defined. 

Record step_preserve (P:mem -> Prop) :=
  { storebytes_preserve: forall m b ofs bytes m',
       Mem.storebytes m b ofs bytes = Some m' -> P m -> P m';
    alloc_preserve: forall m lo hi m' b',
       Mem.alloc m lo hi = (m',b') -> P m -> P m';
    free_preserve: forall m b lo hi m',
       Mem.free m b lo hi = Some m' -> P m -> P m'
  }.

Lemma store_preserve {P} (HP: step_preserve P) m1 b ofs ch v m2:
   Mem.store ch m1 b ofs v = Some m2 -> P m1 -> P m2.
Proof. intros. apply Mem.store_storebytes in H. destruct HP. eauto. Qed.

Lemma freelist_preserve {P} (HP: step_preserve P):
  forall l m1 m2, Mem.free_list m1 l = Some m2 -> P m1 -> P m2.
Proof.
  induction l; simpl; intros. inv H; trivial. 
  destruct a. destruct p. 
  remember (Mem.free m1 b z0 z) as q.
  destruct q; inv H. symmetry in Heqq. apply (IHl _ _ H2).
  destruct HP. eauto. 
Qed. 

Record PreserveSem {G C} P :=
  { psem :> @CoopCoreSem G C 
  ; corestep_preserve : forall g c m c' m'
       (CS: corestep psem g c m c' m'), P m -> P m'}.

Record CoalgSem {G C} :=
  { coalgsem :> @CoopCoreSem G C 
  ; corestepD : forall g c m c' m' (CS: corestep coalgsem g c m c' m'),
      m = m' \/
      (exists b ofs bytes, Mem.storebytes m b ofs bytes = Some m') \/
      (exists lo hi b', Mem.alloc m lo hi = (m',b')) \/
      (exists l, Mem.free_list m l = Some m') }.

Definition mkPsem {G C} (P:mem -> Prop) (s: @CoalgSem G C) (HP:step_preserve P): @PreserveSem G C P.
destruct s as [SEM HSEM].
eapply Build_PreserveSem with (psem:=SEM); intros.
specialize (freelist_preserve HP); intros HPFL.
apply HSEM in CS; clear HSEM. destruct HP as [HPS HPA _].
destruct CS as [? | [[? [? [? ?]]] | [[? [? [? ?]]]| [? ?]]]]; subst; trivial.
eapply HPS; eassumption. 
eapply HPA; eassumption. 
eapply HPFL; eassumption.
Defined. 


Record PreserveSem' {G C P} (HP: step_preserve P):=
  { qsem :> @CoopCoreSem G C 
  ; corestep_pres : forall g c m c' m'
       (CS: corestep qsem g c m c' m'), P m -> P m'}.

Definition mkQsem {G C} (P:mem -> Prop) (s: @CoalgSem G C) (HP:step_preserve P): @PreserveSem' G C _ HP.
destruct s as [SEM HSEM].
eapply Build_PreserveSem' with (qsem:=SEM); intros.
specialize (freelist_preserve HP); intros HPFL.
apply HSEM in CS; clear HSEM. destruct HP as [HPS HPA _].
destruct CS as [? | [[? [? [? ?]]] | [[? [? [? ?]]]| [? ?]]]]; subst; trivial.
eapply HPS; eassumption. 
eapply HPA; eassumption. 
eapply HPFL; eassumption.
Defined. 
*)

Lemma extcall_mem_step fundef type g ef vargs m t vres m': 
      @external_call ef fundef type g vargs m t vres m' ->
      mem_step m m'.
Proof. 
intros. destruct ef; simpl in *; inv H; try apply mem_step_refl.
    inv H0. try apply mem_step_refl.
      eapply mem_step_storebytes.
      apply Mem.store_storebytes; eassumption.
    inv H1. try apply mem_step_refl.
      eapply mem_step_storebytes.
      apply Mem.store_storebytes; eassumption.
    eapply mem_step_trans.
    eapply mem_step_alloc. eassumption.
      eapply mem_step_storebytes.
      apply Mem.store_storebytes; eassumption.
    eapply mem_step_free; eassumption. 
    eapply mem_step_storebytes; eassumption.
Qed.
