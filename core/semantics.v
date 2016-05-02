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


(* Memory sematics - CoreSemantics that are specialized to CompCert memories
   and evolve memory only according to mem_step. Previous notions CoopCoreSem,
   and DecaySem are deprecated, but for now collected in file CoopCoreSem.v *)
Record MemSem {G C} :=
  { csem :> @CoreSemantics G C mem

  ; corestep_mem : forall g c m c' m' (CS: corestep csem g c m c' m'), mem_step m m'
  }.

Implicit Arguments MemSem [].

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

(*From Compcert2.6*)
Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Lemma storebytes_unch_loc_unwritable b ofs: forall l m m' (L: Mem.storebytes m b ofs l = Some m'),
      Mem.unchanged_on (loc_not_writable m) m m'.
Proof.
intros.
split; intros.
+ split; intros. 
  eapply Mem.perm_storebytes_1; eassumption.
  eapply Mem.perm_storebytes_2; eassumption.
+ rewrite (Mem.storebytes_mem_contents _ _ _ _ _ L).
  apply Mem.storebytes_range_perm in L.
  destruct (eq_block b0 b); subst.
  - destruct (zle ofs ofs0).
      destruct (zlt ofs0 (ofs + Z.of_nat (length l))).
        elim H. eapply Mem.perm_max. apply L. omega. 
      rewrite PMap.gss. apply Mem.setN_other. intros. omega.
    rewrite PMap.gss. apply Mem.setN_other. intros. omega.
  - rewrite PMap.gso; trivial.
Qed.

Lemma unch_on_loc_not_writable_trans m1 m2 m3 
        (Q : Mem.unchanged_on (loc_not_writable m1) m1 m2)
        (W : Mem.unchanged_on (loc_not_writable m2) m2 m3)
        (F:mem_forward m1 m2):
     Mem.unchanged_on (loc_not_writable m1) m1 m3.
Proof.
  destruct Q as [Q1 Q2]. destruct W as [W1 W2].
  split; intros.
  - cut (Mem.perm m2 b ofs k p <-> Mem.perm m3 b ofs k p).
      specialize (Q1 _ _ k p H H0). intuition.
    apply W1; clear W1. intros N. apply H. apply Q1; trivial. apply F; trivial.
  -  rewrite W2; clear W2.
       apply Q2; trivial.
     intros N; apply H. apply F; trivial. eapply Mem.perm_valid_block; eassumption.
     apply Q1; trivial. eapply Mem.perm_valid_block; eassumption.
Qed.

Theorem loc_not_writable_preserve: 
   memstep_preserve (fun m m' => mem_forward m m' /\ Mem.unchanged_on (loc_not_writable m) m m').
Proof.
constructor.
+ intros. destruct H as [F1 Q]; destruct H0 as [F2 W].
  split; intros. eapply mem_forward_trans; eassumption. clear F2.
  eapply unch_on_loc_not_writable_trans; eassumption.
+ intros; induction H. 
  - split; intros. eapply storebytes_forward; eassumption.
    eapply storebytes_unch_loc_unwritable; eassumption.
  - split; intros. eapply alloc_forward; eassumption.
    eapply Mem.alloc_unchanged_on; eassumption. 
  - split; intros. eapply freelist_forward; eassumption.
    generalize dependent m.
    induction l; simpl; intros. inv H. apply Mem.unchanged_on_refl.
    destruct a. destruct p. 
    remember (Mem.free m b z0 z) as w. destruct w; inv H. symmetry in Heqw.
    eapply unch_on_loc_not_writable_trans.
      eapply Mem.free_unchanged_on. eassumption. 
        intros i I N. elim N; clear N. 
        eapply Mem.perm_max. eapply Mem.perm_implies. eapply Mem.free_range_perm; eassumption. constructor.
      apply IHl; eassumption.
      eapply free_forward; eassumption.
  - destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    intros. clear H H0 H3. eapply unch_on_loc_not_writable_trans; eassumption. 
Qed.

Lemma freelist_perm: forall l m m' (L : Mem.free_list m l = Some m') b (B: Mem.valid_block m b)
      ofs (P': Mem.perm m' b ofs Max Nonempty) k p,
      Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p.
Proof. induction l; simpl; intros.
+ inv L; split; trivial.
+ destruct a. destruct p0.
  remember (Mem.free m b0 z0 z) as w. symmetry in Heqw.
  destruct w; inv L.
  specialize (IHl _ _  H0 _ (Mem.valid_block_free_1 _ _ _ _ _ Heqw _ B) _ P' k p).
  assert (P: Mem.perm m b ofs k p <-> Mem.perm m0 b ofs k p).
  { clear IHl. destruct (Mem.perm_free_list _ _ _ _ _ _ _ H0 P') as [P ?]; clear H0 P'.
    destruct (eq_block b0 b); subst.
    - destruct (zlt ofs z0).
      * split; intros. apply (Mem.perm_free_1 _ _ _ _ _ Heqw) in H0; eauto.
        eapply Mem.perm_free_3; eassumption.
      * destruct (zle z ofs).
        split; intros. apply (Mem.perm_free_1 _ _ _ _ _ Heqw) in H0; eauto.
                       eapply Mem.perm_free_3; eassumption.
        split; intros.
          eelim (Mem.perm_free_2 _ _ _ _ _ Heqw ofs Max Nonempty); clear Heqw; trivial. omega. 
        eelim (Mem.perm_free_2 _ _ _ _ _ Heqw ofs Max Nonempty); clear Heqw. omega.
          eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
    - split; intros.
      * eapply (Mem.perm_free_1 _ _ _ _ _ Heqw); trivial. intuition.
      * eapply (Mem.perm_free_3 _ _ _ _ _ Heqw); trivial.
  }
  intuition.
Qed.

Theorem perm_preserve: 
   memstep_preserve (fun m m' =>  mem_forward m m' /\ forall b, Mem.valid_block m b -> forall ofs, Mem.perm m' b ofs Max Nonempty -> 
                                  forall k p, Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p).
Proof. 
constructor.
+ intros; split. eapply mem_forward_trans. apply H. apply H0.
  destruct H; destruct H0. intros.
  assert (M: Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p).
  - clear H2. apply H1; trivial. apply H0; trivial. apply H; trivial.
  - clear H1.
    assert (VB2: Mem.valid_block m2 b). apply H; trivial. 
    destruct (H2 _ VB2 _ H4 k p); destruct M. split; intros; eauto.
+ intros; induction H. 
  - split; intros. eapply storebytes_forward; eassumption.
    split; intros. eapply Mem.perm_storebytes_1; eassumption.
    eapply Mem.perm_storebytes_2; eassumption.
  - split; intros. eapply alloc_forward; eassumption.
    split; intros. eapply Mem.perm_alloc_1; eassumption.
    eapply Mem.perm_alloc_4; try eassumption.
    intros N; subst b'. elim (Mem.fresh_block_alloc _ _ _ _ _ H H0).
  - intros; split. eapply freelist_forward; eassumption. 
    apply (freelist_perm _ _ _ H).
  - clear H H0. destruct IHmem_step1; destruct IHmem_step2. 
    split. eapply mem_forward_trans; eassumption.
    intros. 
    assert (M: Mem.perm m b ofs k p <-> Mem.perm m'' b ofs k p).
    * clear H2. apply H0; trivial. apply H1; trivial. apply H; trivial.
    * clear H0.
      assert (VB2: Mem.valid_block m'' b). apply H; trivial.   
      destruct (H2 _ VB2 _ H4 k p); destruct M. split; intros; eauto.
Qed.

Lemma memsem_preserves {G C} (s: @MemSem G C) P (HP:memstep_preserve P):
      forall g c m c' m', corestep s g c m c' m'-> P m m'.
Proof. intros.
  apply corestep_mem in H.
  eapply preserve_mem; eassumption.
Qed.

Lemma corestep_fwd {C G} (s:@MemSem G C) g c m c' m'
   (CS:corestep s g c m c' m' ): mem_forward m m'.
Proof.
eapply memsem_preserves; try eassumption. apply mem_forward_preserve.
Qed.

Lemma corestep_rdonly {C G} (s:@MemSem G C) g c m c' m'
   (CS:corestep s g c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
eapply (memsem_preserves s _ readonly_preserve'); eassumption.
Qed.


Inductive e_step m m' : Prop :=
    mem_step_estep: mem_step m m' -> e_step m m'
  | drop_perm_estep: forall b lo hi p, 
      Mem.drop_perm m b lo hi p = Some m' -> e_step m m'
  | change_cur_estep: 
      (forall b ofs, (Mem.mem_access m) !! b ofs Max = (Mem.mem_access m') !! b ofs Max) ->
      Mem.unchanged_on (loc_not_writable m) m m' ->
      (Mem.mem_contents m = Mem.mem_contents m') ->
      Mem.nextblock m = Mem.nextblock m' -> e_step m m'
  | estep_trans: forall m'',
       e_step m m'' -> e_step m'' m' -> e_step m m'.

Lemma e_step_refl m: e_step m m.
Proof. apply mem_step_estep. apply mem_step_refl. Qed.

Lemma estep_forward m m' (E:e_step m m'): mem_forward m m'.
Proof.
induction E.
apply mem_forward_preserve; eassumption.
+ split; intros.
    eapply Mem.drop_perm_valid_block_1; eassumption.
    eapply Mem.perm_drop_4; eassumption.
+ split; intros.
  unfold Mem.valid_block in *. rewrite H2 in *; assumption.
  unfold Mem.perm. rewrite H. apply H4.
+ eapply mem_forward_trans; eassumption.
Qed.

Lemma estep_unch_on_loc_not_writable m m' (E:e_step m m'): Mem.unchanged_on (loc_not_writable m) m m'.
Proof.
induction E.
+ apply loc_not_writable_preserve in H. apply H. 
+ unfold Mem.drop_perm in H. 
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv H; simpl in *.
  split; simpl; trivial.
  intros. red in H.
  unfold Mem.perm; simpl. rewrite PMap.gsspec.
  destruct (peq b0 b); subst; simpl. 2: intuition.
  destruct (zle lo ofs); simpl. 2: intuition.
  destruct (zlt ofs hi); simpl. 2: intuition.
  elim H. eapply Mem.perm_max. eapply Mem.perm_implies. apply r. omega. constructor.
+ trivial. 
+ eapply unch_on_loc_not_writable_trans; try eassumption. eapply estep_forward; eassumption.
Qed.

(*
Theorem loadbytes_drop m b lo hi p m' (D:Mem.drop_perm m b lo hi p = Some m'):
  forall b' ofs, 
  b' <> b \/ ofs < lo \/ hi <= ofs \/ perm_order p Readable ->
  Mem.loadbytes m' b' ofs 1 = Mem.loadbytes m b' ofs 1.
Proof.
  intros.
Transparent Mem.loadbytes.
  unfold Mem.loadbytes.
  destruct (Mem.range_perm_dec m b' ofs (ofs + 1) Cur Readable). 
  rewrite pred_dec_true.
  unfold Mem.drop_perm in D. destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv D. simpl. auto.
  red; intros. specialize (Mem.perm_drop_1 _ _ _ _ _ _ D ofs0 Cur); intros.
    destruct (eq_block b' b); subst.
      destruct H. eapply Mem.perm_drop_3. eassumption. left; trivial. apply r. trivial.
      destruct (zlt ofs lo). eapply Mem.perm_drop_3. eassumption. right. omega. apply r. trivial.
      destruct H. omega. 
      destruct (zle hi ofs). eapply Mem.perm_drop_3. eassumption. right. omega. apply r. trivial. 
      destruct H. omega.
      eapply Mem.perm_implies. apply H1. omega. trivial.
   eapply Mem.perm_drop_3. eassumption. left; trivial. apply r. omega.

  destruct (Mem.range_perm_dec m' b' ofs (ofs + 1) Cur Readable); trivial.
  elim n; clear n. red; intros. eapply Mem.perm_drop_4. eassumption. apply r. trivial.
Qed. 
*)