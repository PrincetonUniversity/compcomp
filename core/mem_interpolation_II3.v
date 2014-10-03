Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.
Require Import FiniteMaps.
Require Import Axioms.

Require Import mem_lemmas.
Require Import mem_interpolation_defs.
Require Import StructuredInjections.

Require Import pure.
Require Import full_composition.



(***************************
 * UNSTRUCTURED INJECTIONS *
 ***************************)

(*Shifts the image of an injection by n up
 * The new target memory should be (size) large than
 *)
Definition shiftT (j: meminj) (n:block):meminj :=
  fun b =>
    match j b with
        | Some (b2, d) => Some ((b2 + n)%positive, d)
        | None => None
    end.
Infix ">>":= shiftT (at level 80, right associativity).

(*Shifts the domain of an injection down by n
 * The new target memory should be (size) large than
 *)
Definition shiftS (j: meminj) (n:block):meminj :=
  fun b => match ( b ?= n)%positive with
               | Gt => j (b - n)%positive
               | _ => None
           end.
Infix "<<":= shiftS (at level 80, right associativity).

(* fID satisfies (fID .*. f) = f and it's pure *)  
Definition filter_id (j:meminj): meminj:=
  fun b =>
    match j b with
        | Some _ => Some (b, 0)
        | None => None
    end.

(* size is the size of the memory being mapped
 * The new target memory should be (size) large than 
 * the original memory.
 *)
Definition add_inj (j k: meminj): meminj := 
  fun b =>
    match j b with
      | Some p => Some p
      | None => k b
    end.

Infix "(+)":= add_inj (at level 90, right associativity).

(* New definition for mkInjection
 * Assumes the new middle memory is the addition of m1 and m2
 * So everything mapped by j * k, is mapped identically
 * And everything else, mapped only by l, passes through the 
 * extra memory space added in m2 (of size m1).
 *)
Definition mkInjections (sizeM2:block)(j k l: meminj) 
                     :  meminj * meminj := 
   (j (+) (filter_id l >> sizeM2),
    k (+) ( l << sizeM2)).

(* Legacy: mkInjection that matches the type of the old version *)
Definition mkInjections' (m1 m1' m2 :mem)(j k l: meminj) 
                     :  meminj * meminj * block * block := 
  let n1 := Mem.nextblock m1' in
  let n2 := Mem.nextblock m2 in
  match mkInjections n2 j k l with
      | (j', k') => (j', k', n1, (n2 + n1)%positive)
                      end.


(**************************
 * mkInjection Properties *
 **************************)

Lemma pos_be_pos: forall a b, (a + b ?= b = Gt)%positive.
  intros. apply Pos.gt_iff_add. exists a. apply Pos.add_comm.
Qed.

Lemma MKIcomposition:
  forall j k l sizeM2,
    full_comp j k ->
    inject_incr (compose_meminj j k) l ->
    (forall b p, k b = Some p -> (b < sizeM2)%positive) ->
    forall  j' k',
      mkInjections sizeM2 j k l = (j', k') ->
      l = compose_meminj j' k'.
  unfold mkInjections; intros j k l ? full incr valid j' k' mk. inversion mk.
  unfold add_inj, shiftT, shiftS, compose_meminj, filter_id.
  extensionality b.
  destruct (j b) eqn:jb. destruct p.
  destruct (k b0) eqn:kb. destruct p.
  + apply incr. unfold compose_meminj; rewrite jb; rewrite kb; trivial.
  + apply full in jb. destruct jb as [b2 [d' kb0]]. rewrite kb0 in kb; inversion kb.
  + destruct (l b) eqn:lb; trivial.
    destruct (k (b + sizeM2)%positive) eqn: ksmthng. 
    - apply valid in ksmthng.
      clear - ksmthng; contradict ksmthng. rewrite Pos.add_comm; apply Pos.lt_not_add_l.
    - rewrite (Pos.add_sub), lb. rewrite pos_be_pos; destruct p; auto.
Qed.

Lemma  MKI_incr12:
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
   inject_incr j j'.
  intros j k l sizeM2 j' k' MKI; inversion MKI.
  unfold inject_incr, add_inj, shiftT. intros b b' d H; rewrite H; auto.
Qed.

Lemma  MKI_incr23:
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
   inject_incr k k'.
  intros j k l sizeM2 j' k' MKI; inversion MKI.
  unfold inject_incr, add_inj, shiftT. intros b b' d H; rewrite H; auto.
Qed.

Lemma MKI_norm:
  forall j k l sizeM2,
    full_comp j k ->
    (forall b p, k b = Some p -> (b < sizeM2)%positive) ->
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      full_comp j' k'.
  unfold full_comp. intros j k l sizeM2 full valid j' k' MKI b0 b1 delta1 mapj.
  inversion MKI.
  assert (map:= mapj); clear mapj.
  rewrite H0 in map; unfold add_inj in map.
  destruct (j b0) eqn:jb0.
  + destruct p; inversion map.
    apply full in jb0; destruct jb0 as [b2 [delta2 kb1]].
    exists b2, delta2.
    unfold add_inj, shiftT.
    subst b; rewrite kb1; auto.
  + unfold shiftT in map.
    destruct (filter_id l b0) eqn:filter_l; try solve[inversion map].
    destruct p; inversion map.
    unfold add_inj, shiftS.
    destruct (k (b + sizeM2)%positive) eqn:mapk.
    - apply valid in mapk.
      contradict mapk. rewrite Pos.add_comm; apply Pos.lt_not_add_l.
    - unfold filter_id in filter_l. destruct (l b0) eqn:lb0; try solve [inversion filter_l].
      destruct p. rewrite Pos.add_sub. inversion filter_l. subst b0.
      rewrite pos_be_pos; exists b2, z0; trivial.
Qed.

Lemma destruct_inj12:
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      forall (b1 b2 : block) (d1 : Z),
        j' b1 = Some (b2, d1) ->
        j b1 = Some (b2, d1) \/
        (exists (b3 : block) (d : Z), l b1 = Some (b3, d)).
  intros.
  inversion H. subst j' k'.
  unfold add_inj, shiftT in H0.
  destruct (j b1) eqn:jb1.
  + left. destruct p; inversion H0; auto.
  + right. destruct (filter_id l b1) eqn:filtl; try solve [inversion H0].
    destruct p. unfold filter_id in filtl.
    destruct (l b1); try solve[ inversion filtl].
    destruct p as [b3 d]; exists b3, d; auto.
    
Qed.

Lemma destruct_inj23:
  forall j k l sizeM2,
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      forall (b2 b3 : block) (d2 : Z),
        k' b2 = Some (b3, d2) ->
        k b2 = Some (b3, d2) \/
        (exists (b1 : block), l b1 = Some (b3, d2)).
  intros.
  inversion H. subst j' k'.
  unfold add_inj, shiftS in H0.
  destruct (k b2) eqn:jb2.
  + left. destruct p; inversion H0; auto.
  + right. destruct ((b2 ?= sizeM2)%positive); try solve[inversion H0].
    exists (b2 - sizeM2)%positive; trivial.
Qed.

(* Legacy: The following lemmas mathc some old lemmas. Probably useless now. *)
Definition removeUndefs (j l j':meminj):meminj := 
   fun b => match j b with 
              None => match l b with 
                         None => None | Some (b1,delta1) => j' b 
                      end
            | Some p => Some p
            end.

Lemma Undefs_removed:
  forall j k l sizeM2 j' k', 
    mkInjections sizeM2 j k l = (j', k') ->
    j' = removeUndefs j l j'.
  unfold mkInjections; intros. inversion H.
  unfold add_inj, shiftT, shiftS, removeUndefs.
  extensionality b. 
  destruct (j b) eqn:jb; trivial.
  unfold filter_id.
  destruct (l b) eqn:lb; trivial.
  destruct p; trivial.
Qed.

Lemma RU_composememinj: 
  forall j k l sizeM2,
    full_comp j k ->
    inject_incr (compose_meminj j k) l ->
    (forall b p, k b = Some p -> (b < sizeM2)%positive) ->
    forall  j' k',
    mkInjections sizeM2 j k l = (j', k') ->
    l = compose_meminj (removeUndefs j l j') k'.
  intros. erewrite <- Undefs_removed; eauto.
  eapply MKIcomposition; eauto.
Qed.

Lemma RU_composememinj': forall m1 m1' m2 j k l j' k' n1' n2' 
       (HI: mkInjections' m1 m1' m2 j k l = (j',k',n1',n2'))
       (InjIncr: inject_incr (compose_meminj j k) l)
       (m3: mem)
       (InjSep: full_comp j k)
       (VBj1: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m1 b1)
       (VBj2: forall b1 b2 ofs2, j b1 = Some(b2,ofs2) -> Mem.valid_block m2 b2)
       (VBk2: forall b1 b2 ofs2, k b1 = Some(b2,ofs2) -> Mem.valid_block m2 b1)
       (VBL1': forall b1 b3 ofs3, l b1 = Some (b3, ofs3) -> (b1 < n1')%positive),
      l = compose_meminj (removeUndefs j l j') k'.
 intros. 
 apply (RU_composememinj j k l (Mem.nextblock m2) InjSep); eauto. 
 intros; destruct p; eapply VBk2; eauto.
 unfold mkInjections' in HI. destruct (mkInjections (Mem.nextblock m2) j k l); inversion HI; auto.
Qed.








(*************************
 * STRUCTURED INJECTIONS *
 *************************)

Definition buni (bset1 bset2: block -> bool): block -> bool :=
  fun b => bset1 b || bset2 b.

Definition bshift (bset : block -> bool) (num: block): block -> bool :=
  fun b => match (b ?= num)%positive with
             | Lt => false
             | _ => bset (b-num)%positive 
           end.

Definition bconcat (bset1 bset2: block -> bool) (num: block) : block -> bool :=
  buni bset1 (bshift bset2 num).

Definition change_ext (mu: SM_Injection) extS extT (ext_inj: meminj): SM_Injection :=
  match mu with
    | {| locBlocksSrc := locBSrc;
         locBlocksTgt := locBTgt;
         pubBlocksSrc := pubBSrc;
         pubBlocksTgt := pubBTgt;
         local_of := local;
         extBlocksSrc := extBSrc;
         extBlocksTgt := extBTgt;
         frgnBlocksSrc := fSrc;
         frgnBlocksTgt := fTgt;
         extern_of := extern |} =>
      Build_SM_Injection
       locBSrc
       locBTgt
       pubBSrc
       pubBTgt
       local
       extS (* This changes *)
       extT (* This changes *)
       fSrc
       fTgt
       ext_inj (* This changes *)
    end.

(*************************
 * STRUCTURED Properties *
 *************************)

Lemma bconcat_larger1: 
  forall set1 set2 num b,
    set1 b = true -> 
    bconcat set1 set2 num b = true.
  intros s1 s2 n b H; unfold bconcat, buni, bshift; rewrite H; auto.
Qed.
Lemma bconcat_larger2: 
  forall set1 set2 num b,
    set2 b = true -> 
    bconcat set1 set2 num (b + num)%positive = true.
  intros s1 s2 n b H; unfold bconcat, buni, bshift.
  rewrite pos_be_pos; rewrite Pos.add_sub, H; apply orb_true_r.
Qed.



Lemma change_ext_partial_wd: 
  forall mu,
    SM_wd mu ->
    forall mu' extS extT j,
      mu' = change_ext mu extS extT j ->
      (forall (b1 b2 : block) (z : Z),
                   local_of mu' b1 = Some (b2, z) ->
                   locBlocksSrc mu' b1 = true /\ locBlocksTgt mu' b2 = true) /\
      (forall b1 : block,
               pubBlocksSrc mu' b1 = true ->
               exists (b2 : block) (z : Z),
                 local_of mu' b1 = Some (b2, z) /\ pubBlocksTgt mu' b2 = true) /\
      (forall b : block,
                        pubBlocksTgt mu' b = true -> locBlocksTgt mu' b = true).
  intros ? SMWD ? ? ? ? ? . subst mu'. destruct SMWD.
  unfold change_ext; destruct mu; simpl in *; intuition.
Qed.


Lemma MKI_wd12:
  forall mu12 j k l sizeM2,
    SM_wd mu12 ->
    j = extern_of mu12 ->
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      forall extS extT
         (disjoint_extern_local_Src : 
            forall b : block, locBlocksSrc mu12 b = false \/extS b = false)
         (disjoint_extern_local_Tgt : 
            forall b : block, locBlocksTgt mu12 b = false \/ extT b = false)
         (extern_DomRng : forall (b1 b2 : block) (z : Z),
                  j' b1 = Some (b2, z) -> extS b1 = true /\ extT b2 = true)
         (frgnBlocksExternTgt : forall b : block,
                        frgnBlocksTgt mu12 b = true -> extT b = true),
   SM_wd (change_ext mu12 extS extT j').
  intros mu12 j k l sizeM2 SMWD jID j' k' MKI extS extT.
  intros disjoint_extern_local_Src
         disjoint_extern_local_Tgt
         extern_DomRng
         frgnBlocksExternTgt.
  unfold change_ext; destruct mu12; simpl in *.
  destruct SMWD; constructor; simpl in *; auto.
  (* remains to prove frgnSrcAx *)
  { intros.
    apply frgnSrcAx in H.
    destruct H as [b2 [z2 [extof frgnB]]].
    exists b2, z2.
    split; auto.
    inversion MKI; inversion jID.
    unfold add_inj. rewrite extof; auto. 
  }
Qed.

Lemma MKI_wd23:
  forall mu23 j k l sizeM2,
    SM_wd mu23 ->
    k = extern_of mu23 ->
    forall j' k',
      (j', k') = mkInjections sizeM2 j k l ->
      forall extS extT
         (disjoint_extern_local_Src : 
            forall b : block, locBlocksSrc mu23 b = false \/extS b = false)
         (disjoint_extern_local_Tgt : 
            forall b : block, locBlocksTgt mu23 b = false \/ extT b = false)
         (extern_DomRng : forall (b1 b2 : block) (z : Z),
                  k' b1 = Some (b2, z) -> extS b1 = true /\ extT b2 = true)
         (frgnBlocksExternTgt : forall b : block,
                        frgnBlocksTgt mu23 b = true -> extT b = true),
   SM_wd (change_ext mu23 extS extT k').
  intros mu23 j k l sizeM2 SMWD jID j' k' MKI extS extT.
  intros disjoint_extern_local_Src
         disjoint_extern_local_Tgt
         extern_DomRng
         frgnBlocksExternTgt.
  unfold change_ext; destruct mu23; simpl in *.
  destruct SMWD; constructor; simpl in *; auto.
  (* remains to prove frgnSrcAx *)
  { intros.
    apply frgnSrcAx in H.
    destruct H as [b2 [z2 [extof frgnB]]].
    exists b2, z2.
    split; auto.
    inversion MKI; inversion jID.
    unfold add_inj. rewrite extof; auto. 
  }
Qed.


(*I don't know why the following are needed.*)
Lemma destruct_sminj12:
  forall nu12 j,
    SM_wd nu12 ->
    j = extern_of nu12 ->
    forall nu' l,
      l = extern_of nu' ->
      forall k sizeM2 j' k',
        (j', k') = mkInjections sizeM2 j k l ->
        forall extS extT,
        forall (b1 b2 : block) (d1 : Z),
          as_inj (change_ext nu12 extS extT j') b1 = Some (b2, d1) ->
          as_inj nu12 b1 = Some (b2, d1) \/
          (exists (b3 : block) (d : Z), as_inj nu' b1 = Some (b3, d)).
  unfold as_inj, join, change_ext;
  intros nu12 j SMWD jID nu' l lID k sizeM2 j' k' MKI extT extS b1 b2 d1; 
  destruct nu12; simpl in *.
  destruct (j' b1)  eqn:jb1.
  + destruct p. inversion MKI. 
    eapply destruct_inj12 in jb1; eauto; destruct jb1.
    - left. rewrite <- jID; rewrite H.
      inversion H2; subst; auto.
    - right. destruct H as [b3 [d3 lb1]]; rewrite <- lID; rewrite lb1.
      exists b3, d3; auto.
  + intros. apply disjoint_extern_local in SMWD.
    simpl in SMWD; destruct (SMWD b1) as [extNone | locNone].
    - left; rewrite extNone; exact H.
    - rewrite locNone in H; inversion H.
Qed.

Lemma destruct_sminj23:
  forall nu23 k,
    SM_wd nu23 ->
    k = extern_of nu23 ->
    forall nu' l,
      l = extern_of nu' ->
      forall j sizeM2 j' k',
        (j', k') = mkInjections sizeM2 j k l ->
        forall extS extT,
        forall (b2 b3 : block) (d2 : Z),
          as_inj (change_ext nu23 extS extT k') b2 = Some (b3, d2) ->
          as_inj nu23 b2 = Some (b3, d2) \/
          (exists (b1 : block), as_inj nu' b1 = Some (b3, d2)).
  unfold as_inj, join, change_ext;
  intros nu23 j SMWD jID nu' l lID k sizeM2 j' k' MKI extT extS b2 b3 d2; 
  destruct nu23; simpl in *.
  destruct (k' b2)  eqn:kb2.
  + destruct p. inversion MKI. 
    eapply destruct_inj23 in kb2; eauto; destruct kb2.
    - left. rewrite <- jID; rewrite H.
      inversion H2; subst; auto.
    - right. destruct H as [b1 lb1]; rewrite <- lID. 
      exists b1; rewrite lb1; trivial.
  + intros. apply disjoint_extern_local in SMWD.
    simpl in SMWD; destruct (SMWD b2) as [extNone | locNone].
    - left; rewrite extNone; exact H.
    - rewrite locNone in H; inversion H.
Qed.

(*************************
 *         MEMORY        *
 *************************)
Parameter mem_add: mem -> mem -> mem.

Definition mem_add_cont (m1 m2:mem):=
  fun (b: block)=>
    let n1 := (Mem.nextblock m1) in
    match (b ?= n1)%positive with
        | Lt => (Mem.mem_contents m1) !! b
        | _ => (Mem.mem_contents m1) !! (b - n1)
    end.
Definition mem_add_acc (m1 m2:mem):=
  fun (b: block)=>
    let n1 := (Mem.nextblock m1) in
    match (b ?= n1)%positive with
        | Lt => (Mem.mem_access m1) !! b
        | _ => (Mem.mem_access m1) !! (b - n1)
    end.
Definition mem_add_nb (m1 m2:mem):=
  let n1 := Mem.nextblock m1 in
  let n2 := Mem.nextblock m2 in
  (n1 + n2)%positive. 

Axiom mem_add_ax: forall (m1 m2 m3: mem), 
                    m3 = mem_add m1 m2 ->
                    (forall b, (Mem.mem_contents m3) !! b = mem_add_cont m1 m2 b) /\
                    (forall b, (Mem.mem_access m3) !! b  = mem_add_acc m1 m2 b) /\
                    (Mem.nextblock m3 = mem_add_nb m1 m2).

Lemma mem_add_contx: forall (m1 m2: mem),
                    (forall b, (Mem.mem_contents (mem_add m1 m2)) !! b = mem_add_cont m1 m2 b).
  intros; remember (mem_add m1 m2) as m3; apply mem_add_ax; auto.
Qed.

Lemma mem_add_accx: forall (m1 m2: mem),
                    (forall b, (Mem.mem_access (mem_add m1 m2)) !! b = mem_add_acc m1 m2 b).
  intros; remember (mem_add m1 m2) as m3; apply mem_add_ax; auto.
Qed.

Lemma mem_add_nbx: forall (m1 m2: mem),
                    (Mem.nextblock (mem_add m1 m2)) = mem_add_nb m1 m2.
  intros; remember (mem_add m1 m2) as m3; apply mem_add_ax; auto.
Qed.

(*************************
 *    MEMORY PROPRTIES   *
 *************************)

Lemma mem_add_forward: forall m1' m2,
  mem_forward m2 (mem_add m2 m1').
  unfold mem_forward. intros m1' m2 b bval_m2.
  split.
  + unfold Mem.valid_block in *.
    rewrite mem_add_nbx.
    unfold mem_add_nb.
    apply (Plt_trans _ _ _ bval_m2). 
    apply Pos.lt_iff_add; exists ( Mem.nextblock m1'); auto.
  + unfold Mem.valid_block, Plt, Pos.lt in bval_m2.
    unfold Mem.perm. rewrite mem_add_accx; unfold mem_add_acc.
    rewrite bval_m2; auto.
Qed.

Lemma mem_add_unchanged: 
  forall m1' m2,
    let in_m2 := fun b z => Plt b (Mem.nextblock m2) in
    Mem.unchanged_on in_m2 m2 (mem_add m2 m1').
  intros; constructor; intros.
  unfold in_m2 in H. 
  + unfold Mem.perm. rewrite mem_add_accx; unfold mem_add_acc. 
    rewrite H; split; trivial.
  + unfold Mem.perm. rewrite mem_add_contx; unfold mem_add_cont. 
    rewrite H; split; trivial.
Qed.


(*mem_unchanged_on_sub*)
  

(*Lemma MKI_meminj12:
  forall j k l m1' m2,
    Mem.inject j 
    forall *)