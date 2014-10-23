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

Definition range_eq (j f:meminj) (sizeM:block):=
  forall b2 b1 delta, (b2 < sizeM)%positive -> f b1 = Some (b2, delta) -> j b1 = Some(b2, delta).

Lemma MKI_range_eq:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    range_eq j j' sizeM2.
  intros j k l sizeM2 j' k' MKI; inversion MKI.
  unfold range_eq; intros b2 b1 delta range jmap'.
  unfold add_inj, shiftT in jmap'.
  destruct (j b1) eqn:jmap; trivial.
  destruct (filter_id l b1) eqn:lmap; trivial.
  destruct p; inversion jmap'.
  rewrite <- H2 in range.
  xomega.
Qed.

Lemma MKI_restrict:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b1 b2 delta, j' b1 = Some (b2, delta) ->
                        (b2 < sizeM2)%positive ->
                        j b1 = Some (b2, delta).
  intros. inversion H. unfold add_inj, shiftT in *; subst j'.
  destruct (j b1) eqn: jmap; trivial.
  destruct (filter_id l b1); trivial; destruct p.
  inversion H0. rewrite <- H3 in H1; xomega.
Qed.

Lemma MKI_None12:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b,
      j b = None ->
      l b = None ->
      j' b = None.
  intros ? ? ? ? ? ? H ? ? ? ; inversion H; 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst; rewrite H0, H1; auto. 
Qed.

Lemma MKI_None23:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b,
      k b = None ->
      l (b - sizeM2)%positive = None ->
      k' b = None.
  intros ? ? ? ? ? ? H ? ? ? ; inversion H; 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst; rewrite H0, H1; destruct (b ?= sizeM2)%positive; trivial.
Qed.

Lemma MKI_Some12:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b b2 d,
      j' b = Some (b2, d) ->
      j b = Some (b2, d) \/ j b = None /\ (exists b2' d', l b = Some (b2', d') /\ b2 = (b + sizeM2)%positive /\ d = 0).
  intros. inversion H; clear H. 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst.
  destruct (j b) eqn:jmap.
  destruct p; inversion H0; subst. left; auto.
  destruct (l b) eqn:lmap.
  destruct p; inversion H0; subst. right; split; trivial; exists b0, z; intuition.
  inversion H0.
Qed.

Lemma MKI_Some23:
  forall j k l sizeM2,
  forall j' k',
    (j', k') = mkInjections sizeM2 j k l ->
    forall b2 b3 d,
      k' b2 = Some (b3, d) ->
      k b2 = Some (b3, d) \/ k b2 = None /\ (l (b2 - sizeM2)%positive = Some (b3, d) /\ (b2 ?= sizeM2)%positive = Gt).
  intros. inversion H; clear H. 
  unfold add_inj, shiftT, filter_id, shiftS in *.
  subst.
  destruct (k b2) eqn:jmap.
  destruct p; inversion H0; subst. left; auto.
  destruct ((b2 ?= sizeM2)%positive) eqn:ineq; try solve [inversion H0].
  right; auto. 
Qed.

Lemma MKI_Some12':
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

Lemma MKI_Some23':
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

Lemma ext_change_ext: forall mu extS extT ext_inj,
                        extern_of (change_ext mu extS extT ext_inj) = ext_inj.
  intros. unfold extern_of; destruct mu; auto.
Qed.
Lemma loc_change_ext: forall mu extS extT ext_inj,
                        local_of (change_ext mu extS extT ext_inj) = local_of mu.
  intros. unfold extern_of; destruct mu; auto.
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
    eapply MKI_Some12' in jb1; eauto; destruct jb1.
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
    eapply MKI_Some23' in kb2; eauto; destruct kb2.
    - left. rewrite <- jID; rewrite H.
      inversion H2; subst; auto.
    - right. destruct H as [b1 lb1]; rewrite <- lID. 
      exists b1; rewrite lb1; trivial.
  + intros. apply disjoint_extern_local in SMWD.
    simpl in SMWD; destruct (SMWD b2) as [extNone | locNone].
    - left; rewrite extNone; exact H.
    - rewrite locNone in H; inversion H.
Qed.

(*A way to split cases when using change_ext*)

(*************************
 *         MEMORY        *
 *************************)
Parameter mem_add: meminj -> mem -> mem -> mem.

Definition mem_add_cont' (m1 m2:mem):=
  fun (b: block)=>
    let n2 := (Mem.nextblock m2) in
    match (b ?= n2)%positive with
        | Lt => (Mem.mem_contents m2) !! b
        | _ => (Mem.mem_contents m2) !! (b - n2)
    end.

Definition has_preimage (f:meminj) (m:mem) (b2:block):=
  exists b1 delta, Mem.valid_block m b1 /\ 
                   f b1 = Some (b2, delta).
Definition loc_preimage (f:meminj) (m:mem) (b2:block) (ofs:Z) :=
  exists b1 delta, Mem.valid_block m b1 /\ 
                   f b1 = Some (b2, delta) /\
                   Mem.perm m b1 (ofs - delta) Max Nonempty.

(*Lemma preimage_source: forall f m b2 ofs,
                         (exists b1 delta, source f m b2 ofs = Some( b1, delta)) <->
                         loc_preimage f m b2 ofs.
  acdmit.
  (*intros; split; intros. 
  + destruct H as [b1 [delta soc]]. unfold loc_preimage; exists b1, delta. 
    split.

acdmit.
  + destruct *)
Qed.*)

Definition acc_property (f:meminj) (m1' m2:mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> 
     forall k ofs2,
       match source f m1' b2 ofs2 with
           Some(b1,ofs1) =>  (AM !! b2) ofs2 k = 
                             (m1'.(Mem.mem_access) !! b1) ofs1 k
         | None =>           (AM !! b2) ofs2 k = 
                             (m2.(Mem.mem_access) !! b2) ofs2 k
       end) /\
    (~ Mem.valid_block m2 b2 -> forall k ofs,
                             (AM !! b2) ofs k =
                             (m1'.(Mem.mem_access) !! (b2 - m2.(Mem.nextblock))%positive) ofs k).


Lemma valid_dec: forall m b, {Mem.valid_block m b} + {~Mem.valid_block m b}.
  intros. unfold Mem.valid_block. apply plt.
Qed.

Definition mem_add_acc (f:meminj) (m1' m2:mem):=
  fun b2 ofs2 k =>
    if valid_dec m2 b2 then 
      (match source f m1' b2 ofs2 with
           Some(b1,ofs1) =>  (m1'.(Mem.mem_access) !! b1) ofs1 k
         | None =>           (m2.(Mem.mem_access) !! b2) ofs2 k
       end)
    else (m1'.(Mem.mem_access) !! (b2 - m2.(Mem.nextblock))%positive) ofs2 k.

Print Mem.inject'.
Print Mem.mem_inj.
Print memval_inject.

Definition mem_add_cont (f:meminj) (m1' m2:mem):=
  fun b2 ofs2 =>
    if valid_dec m2 b2 then 
      (match source f m1' b2 ofs2 with
           Some(b1,ofs1) =>  inject_memval f (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
         | None =>           ZMap.get ofs2 ( m2.(Mem.mem_contents) !! b2)
       end)
    else inject_memval f (ZMap.get ofs2 (m1'.(Mem.mem_contents) !! (b2 - m2.(Mem.nextblock)))).


Definition mem_add_nb (m1 m2:mem):=
  let n1 := Mem.nextblock m1 in
  let n2 := Mem.nextblock m2 in
  (n2 + n1)%positive. 

Axiom mem_add_ax: forall (f:meminj) (m1 m2 m3: mem), 
                    m3 = mem_add f m2 m1 ->
                    (forall b ofs, ZMap.get ofs (Mem.mem_contents m3) !! b = 
                                   mem_add_cont f m1 m2 b ofs) /\
                    (forall b, (Mem.mem_access m3) !! b = 
                               mem_add_acc f m1 m2 b) /\  
                    (Mem.nextblock m3 = mem_add_nb m1 m2).

Lemma mem_add_contx:
  forall f m1' m2, 
    (forall b ofs, 
       ZMap.get ofs (Mem.mem_contents (mem_add f m2 m1')) !! b = 
       mem_add_cont f m1' m2 b ofs).
  intros; remember (mem_add f m2 m1') as m3; destruct (mem_add_ax f m1' m2 m3) as [A [B C]]; auto.
Qed.

Lemma mem_add_accx:
  forall f m1' m2, (forall b, (Mem.mem_access (mem_add f m2 m1')) !! b = mem_add_acc f m1' m2 b).
  intros; remember (mem_add f m2 m1') as m3; destruct (mem_add_ax f m1' m2 m3) as [A [B C]]; auto.
Qed.

Lemma mem_add_nbx: forall (f:meminj) (m1 m2: mem),
                    (Mem.nextblock (mem_add f m2 m1)) = mem_add_nb m1 m2.
  intros; remember (mem_add f m2 m1) as m3; destruct (mem_add_ax f m1 m2 m3) as [A [B C]]; auto.
Qed.

(*************************
 *    MEMORY PROPRTIES   *
 *************************)

(* usefull in the next lemma *)
Lemma xH_smallest: forall b, ~ Plt b 1.
  intros.
  unfold not, Plt, Pos.lt, Pos.compare; intros.
  destruct b; simpl in H; inversion H.
Qed.

(*
Lemma loc_preimage_dec:
  forall j m b ofs, loc_preimage m j b ofs \/ ~ loc_preimage m j b ofs.

Lemma preimage_dec:
  forall m b j, has_preimage m j b \/ ~ has_preimage m j b.
  acdmit.
  (*intros.
  unfold has_preimage.
  unfold Mem.valid_block.
  remember (Mem.nextblock m) as N; clear HeqN m.
  generalize N; apply positive_Peano_ind.
  + right.
    unfold not; intros. destruct H as [b1 [ delta [H1 H2]]].
    apply (xH_smallest b1); assumption.
  + intros.
    destruct H as [[b1 [delta [H1 H2]]] | H].
  - left. exists b1, delta. split; trivial.
    apply Plt_trans_succ; auto.
  - destruct (j x) eqn:map; try destruct p.
    * destruct (AST.ident_eq b0 b).
      left; subst; exists x, z; split; auto.
      apply Plt_succ.
      right. unfold not; intros [b1 [delta [H1 H2]]].
      apply H. apply Plt_succ_inv in H1. destruct H1.
      exists b1, delta; auto.
      subst; rewrite map in H2; inversion H2. apply n in H1; inversion H1.
    * right. intros [b1 [delta [H1 H2]]]; apply H.
      apply Plt_succ_inv in H1. destruct H1.
      exists b1, delta; auto.
      subst; rewrite map in H2; inversion H2. *)
Qed.
*)

Definition corresponding_preimage (f:meminj) (sizeM1 sizeM2:block):=
  forall b1 b2 delta, f b1 = Some (b2, delta) -> (b2 < sizeM2)%positive -> (b1 < sizeM1)%positive.


(*Lemma mem_add_unchanged: 
  forall f m1' m2,
    forall j m1,
    corresponding_preimage f (Mem.nextblock m1) (Mem.nextblock m2) ->
    range_eq j f (Mem.nextblock m2) ->
    mem_forward m1 m1' ->
    Mem.mem_inj j m1 m2 ->
    let in_m2 := fun b z => Plt b (Mem.nextblock m2) in
    Mem.unchanged_on in_m2 m2 (mem_add f m2 m1').
  intros f m1' m2 j m1 corpre range mfwrd minj.
  constructor; intros.
  (*unfold Mem.valid_block in H0.
  destruct (preimage_dec m1' b f) as [H1 | H1]; unfold has_preimage in H1.
  + destruct H1 as [b1 [delta [valb1 fmap]]].
    assert (jmap:=fmap); apply (incr _ _ _ bval_m2) in jmap.
    intros. unfold Mem.perm in *.
    destruct minj as [mi_perm A B ]; clear A B.
    move mi_perm at bottom.
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply mi_perm; eauto.
    eapply memFwrd. 
    eapply corrpre; eauto.
    Lemma mem_add_add_simpl: 
      forall f m1' m2 b1 b2 delta,
        Mem.valid_block m1' b1 ->
        f b1 = Some (b2, delta) ->
        forall ofs k p,
        Mem.perm (mem_add f m2 m1') b2 (ofs + delta) k p ->
        Mem.perm m1' b1 ofs k p.
      acdmit.
      (*intros f m1' m2 b1 b2 delta memval fmap ofs k p memperm.
      destruct (mem_add_accx f m1' m2 b2) as [H1 H2].
      unfold Mem.perm in H1.
      unfold Mem.perm. unfold Mem.perm_order'.*)
    Qed.
    eapply (mem_add_add_simpl _ _ _ _ _ _ valb1 fmap); eauto.
    replace ((ofs - delta) + delta) with ofs by omega; eauto.
    - destruct (mem_add_accx f m1' m2 b) as [H H0].
      unfold Mem.perm; intros.
      rewrite (H0 H1); auto.
Qed.

  + unfold Mem.perm. rewrite mem_add_accx; unfold mem_add_acc. 
    rewrite H; split; trivial.*) acdmit.
  + unfold Mem.perm. rewrite mem_add_contx; unfold mem_add_cont. 
    rewrite H; split; trivial.
Qed.*)

Definition mi_perm f m1 m2 := forall (b1 b2 : block) (delta ofs : Z) 
                (k : perm_kind) (p : permission),
              f b1 = Some (b2, delta) ->
              Mem.perm m1 b1 ofs k p -> Mem.perm m2 b2 (ofs + delta) k p.

Lemma mem_add_forward: 
  forall (j':meminj) m1' m2,
  forall (j:meminj) m1,
    (forall b1 p, j b1 = Some p -> Mem.valid_block m1 b1) -> 
    (* range_eq j j' (Mem.nextblock m2) -> *)
    mem_forward m1 m1' ->
    mi_perm j m1 m2 ->
  mem_forward m2 (mem_add j m2 m1').
  unfold mem_forward. intros j' m1' m2 j m1 corrpre (*incr*) memFwrd miperm b bval_m2.
  split.
  + unfold Mem.valid_block in *.
    rewrite mem_add_nbx.
    unfold mem_add_nb.
    apply (Plt_trans _ _ _ bval_m2). 
    apply Pos.lt_iff_add; exists ( Mem.nextblock m1'); auto.
  + intros ofs per.
    unfold Mem.perm. rewrite (mem_add_accx j m1' m2  b); unfold mem_add_acc.
    destruct (valid_dec m2 b); try contradiction.
    destruct (source j m1' b ofs) eqn: sour; trivial.
    destruct p; intros.
    symmetry in sour; eapply source_SomeE in sour. 
    destruct sour as [b1 [delta [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
    inversion invertible.
    (*specialize (incr _ _ _ bval_m2 mapj').*)
    subst ofs.
    apply (miperm _ _ _ _ _ _ mapj).
    unfold Mem.perm in H; rewrite H1 in H.
    apply memFwrd; auto.
    apply (corrpre _ _ mapj).
    unfold Mem.perm; subst z b0; auto.
Qed.



(*
Lemma MKI_meminj12:
  forall j k l mu12,
    SM_wd mu12 ->
    j = extern_of mu12 ->
    forall j' k' sizeM2,
      (j', k') = mkInjections sizeM2 j k l ->
      forall m1 m2,
        Mem.inject (as_inj mu12) m1 m2 -> 
        forall m1',
          mem_forward m1 m1'->
          forall nu12' extS extT,
            nu12' = change_ext mu12 extS extT j' ->
      Mem.inject (as_inj nu12') m1' (mem_add m2 m1').
  intros. constructor.
  { constructor.
    intros.
    assert (disj:  (as_inj mu12 b1 = Some (b2, delta)) \/  as_inj mu12 b1 = None /\ 
                   j' b1 = Some (b2, delta)) by acdmit. 
    destruct disj as [mu12b1 | jb1].
    destruct H2. destruct mi_inj.
    assert (mu12b1':=mu12b1).
    eapply mi_perm in mu12b1.
    Lemma mperm_subset: forall m m' b ofs k p,
      Mem.perm m b ofs k p ->
      Mem.perm (mem_add m m') b ofs k p.
      unfold Mem.perm; intros.
      assert (HH:= H); apply Mem.perm_valid_block in HH.
      rewrite mem_add_accx; unfold mem_add_acc.
      rewrite HH; auto.
    Qed.
    apply mperm_subset; eauto.
    
    assert (Mem.valid_block m1 b1). 
    { destruct (plt b1 (Mem.nextblock m1)); auto.
      apply mi_freeblocks in n; rewrite n in mu12b1'; inversion mu12b1'. }
    apply H3 in H2. destruct H2. apply aH7.
    apply mi_mappedblocks.
      
Acdmitted.*)


(***********************************
 *      Other Properties           *
 ***********************************)

Lemma as_in_SomeE: forall mu b1 b2 delta,
                     as_inj mu b1 = Some (b2, delta) ->
                     extern_of mu b1 = Some (b2, delta) \/
                     local_of mu b1 = Some (b2, delta).
  unfold as_inj, join; intros.
  destruct (extern_of mu b1) eqn:ext; try (destruct p); inversion H; auto.
Qed.

Lemma no_overlap_forward: forall mu m1 m1' m2, 
                            sm_valid mu m1 m2 ->
                            SM_wd mu ->
                            mem_forward m1 m1' ->
                            Mem.meminj_no_overlap (as_inj mu) m1 ->
                            Mem.meminj_no_overlap (as_inj mu) m1'.
  unfold Mem.meminj_no_overlap; intros mu m1 m1' m2 sval SMWD mfwd minj; intros.
  eapply minj; eauto;
  (apply mfwd; auto); 
  [destruct (as_inj_DomRng _ _ _ _ H0 SMWD) as [DOMtrue RNGtrue] |
   destruct (as_inj_DomRng _ _ _ _ H1 SMWD) as [DOMtrue RNGtrue]];
  ( destruct sval as [DOMval RNGval]; apply DOMval; auto; apply mfwd; auto).
Qed.


Lemma perm_order_trans': forall a b c,
                           Mem.perm_order' a b ->
                           perm_order b c ->
                           Mem.perm_order' a c.
  unfold Mem.perm_order'; intros.
  destruct a; trivial. eapply perm_order_trans; eauto.
Qed.

Lemma any_Max_Nonempty: forall m b ofs k p,
                          Mem.perm m b ofs k p ->
                          Mem.perm m b ofs Max Nonempty.
  unfold Mem.perm;  intros.
  
  destruct k.
  eapply perm_order_trans'; eauto. apply perm_any_N. 
  unfold Mem.mem_access in *; destruct m.
  rewrite po_oo. eapply po_trans; eauto.
  rewrite po_oo in H. eapply po_trans; eauto.
  unfold Mem.perm_order''. apply perm_any_N.
Qed.

Lemma forward_nextblock_not: forall m m',
                               mem_forward m m' ->
                               forall b,
                               ~ Mem.valid_block m' b ->
                               ~ Mem.valid_block m b.
  unfold not, Mem.valid_block.
  intros m m' mfwd b nvalid valid; apply nvalid; apply (Pos.lt_le_trans _ _ _ valid). apply forward_nextblock; assumption.
Qed.