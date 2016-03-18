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

(** Clight self-simulates. *)

Require Import FSets.
Require FSetAVL.
Require Import Coqlib.
Require Import Errors.
Require Import Ordered.
Require Import AST.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Clight.
Require Import SimplLocals.

Require Import mem_lemmas.
Require Import semantics.
Require Import semantics_lemmas.
Require Import reach.
Require Import effect_semantics.
Require Import structured_injections.
Require Import simulations.
Require Import effect_properties.
Require Import simulations_lemmas.
Require Import BuiltinEffects.

Require Export Axioms.
Require Import Clight_coop.
Require Import Clight_eff.
Require Import val_casted.

Lemma blocks_of_bindingD: forall l b lo hi 
      (I: In (b,lo,hi) (map block_of_binding l)),
      lo=0 /\ exists x tp, In (x,(b,tp)) l.
Proof. intros l.
  induction l; simpl; intros. contradiction.
  destruct I. 
    destruct a as [? [? ?]]. simpl in H. inv H.
    split; trivial. exists i, t; left; trivial.
  destruct (IHl _ _ _ H) as [HH [x [tp Hx]]].
  split; trivial. exists x, tp; right; trivial.
Qed.

Lemma blocks_of_envD: forall te b lo hi 
       (I:In (b, lo, hi) (blocks_of_env te)),
      lo=0 /\ exists x tp, te!x = Some(b,tp).
Proof. intros.
  destruct (blocks_of_bindingD _ _ _ _ I) as [HH [x [tp Hx]]].
  split; trivial.
  exists x, tp. eapply PTree.elements_complete. apply Hx.
Qed.

Lemma FreelistEffect_Dtrue2:
  forall (m : mem) (L : list (block * Z * Z))
    (b : block) (ofs : Z),
  FreelistEffect m L b ofs = true ->
  exists bb lo hi,  In (bb, lo, hi)  L /\ 
      FreeEffect m lo hi bb b ofs = true.
Proof. intros m L.
  induction L; simpl; intros. intuition.
  destruct a as [[? ?] ?].
  apply orb_true_iff in H. destruct H.
    destruct (IHL _ _ H) as [? [? [? [? ?]]]].
    exists x, x0, x1; split; trivial. right; trivial.
  exists b0, z, z0. split; trivial. left; trivial.
Qed.

Lemma FreelistEffect_I: forall m L lo hi b ofs,
      Mem.valid_block m b -> In (b,lo,hi) L -> lo <= ofs < hi -> 
      FreelistEffect m L b ofs = true.
Proof. intros. unfold FreelistEffect.
  induction L; simpl in *. inv H0.
  destruct H0; subst.
  apply orb_true_iff. clear IHL. right.
    unfold FreeEffect. simpl.
    destruct (valid_block_dec m b).
      destruct (eq_block b b); simpl. destruct H1.
          apply andb_true_iff. split. destruct (zle lo ofs). trivial. omega. 
         destruct (zlt ofs hi); trivial. omega. 
      elim n; trivial. 
     contradiction. 
  destruct a as [[? ?] ?].
  rewrite (IHL H0).  trivial.
Qed. 

Module VSF := FSetFacts.Facts(VSet).
Module VSP := FSetProperties.Properties(VSet).

Lemma nextblock_eq_freshloc m m1 m2: forall
      (EQ: Mem.nextblock m1 = Mem.nextblock m2),
      freshloc m m1 = freshloc m m2.
Proof. intros. unfold freshloc.
  extensionality b. 
  destruct (valid_block_dec m1 b); simpl. red in v. rewrite EQ in v. 
    destruct (valid_block_dec m2 b); simpl; trivial. elim n. apply v. 
  destruct (valid_block_dec m2 b); simpl; trivial. elim n. red. rewrite EQ. apply v.
Qed.

Lemma assign_loc_freshloc: forall ty m b ofs v m' (AL:assign_loc ty m b ofs v m'),
  freshloc m m' = fun b => false.
Proof. intros.
  inv AL. apply (storev_freshloc _ _ _ _ _ H0).
  apply (storebytes_freshloc _ _ _ _ _ H4).
Qed. 

Lemma sharedSrc_vis mu b: sharedSrc mu b = true -> 
                          SM_wd mu -> vis mu b = true.
Proof. 
  intros. rewrite sharedSrc_iff_frgnpub in H; trivial.
  specialize (pubBlocksLocalSrc _ H0); intros. unfold vis.
  destruct (frgnBlocksSrc mu b); intuition.
Qed.

Lemma restrict_sm_sharedSrc_vis_X mu X: forall
        (HX : forall b : block, vis mu b = true -> X b = true)
        (WD: SM_wd mu),
        sharedSrc (restrict_sm mu X) = sharedSrc mu.
Proof. intros.
  rewrite sharedSrc_iff_frgnpub, restrict_sm_frgnBlocksSrc, restrict_sm_pubBlocksSrc. 
  rewrite sharedSrc_iff_frgnpub; trivial.
  apply restrict_sm_WD; assumption.
Qed.

Lemma incr_restrict_shared_vis mu: SM_wd mu ->
      inject_incr (restrict (as_inj mu) (sharedSrc mu))
                  (restrict (as_inj mu) (vis mu)).
Proof. red; intros. 
  destruct (restrictD_Some _ _ _ _ _ H0).
  apply sharedSrc_vis in H2; trivial.
  apply restrictI_Some; trivial.
Qed.

Section PRESERVATION.

Variable prog: program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv prog.

(*NEW*) Variable hf : I64Helpers.helper_functions.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  auto.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  auto.
Qed.

Lemma type_of_global_preserved:
  forall id ty, type_of_global ge id = Some ty -> type_of_global tge id = Some ty.
Proof.
  unfold type_of_global; intros.
  rewrite varinfo_preserved. destruct (Genv.find_var_info ge id). auto. 
  destruct (Genv.find_funct_ptr ge id) as [fd|] eqn:?; inv H.
  unfold tge. unfold ge in Heqo. rewrite Heqo; auto.
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
  unfold ge, tge.
  apply genvs_domain_eq_refl.
Qed.

(** Matching between environments before and after *)

Inductive match_var mu (e: env) (m: mem) (te: env) (tle: temp_env) (id: ident) : Prop :=
  | match_var_not_lifted: forall b ty b'
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = Some(b', ty))
      (MAPPED: local_of mu b = Some(b', 0)), 
      match_var mu e m te tle id
  | match_var_not_local: forall
      (ENV: e!id = None)
      (TENV: te!id = None),
      match_var mu e m te tle id.

Record match_envs mu
                  (e: env) (le: temp_env) (m: mem) (lo hi: block)
                  (te: env) (tle: temp_env) (tlo thi: block) : Prop :=
  mk_match_envs {
    me_vars:
      forall id, match_var mu e m te tle id;
    me_temps:
      forall id v,
      le!id = Some v ->
      (exists tv, tle!id = Some tv /\ val_inject (restrict (as_inj mu) (vis mu)) v tv);
    me_inj:
      forall id1 b1 ty1 id2 b2 ty2, e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2;
    me_range:
      forall id b ty, e!id = Some(b, ty) -> Ple lo b /\ Plt b hi /\  locBlocksSrc mu b =true;
    me_trange:
      forall id b ty, te!id = Some(b, ty) -> Ple tlo b /\ Plt b thi /\  locBlocksTgt mu b =true;
    me_mapped:
      forall id b' ty,
      te!id = Some(b', ty) -> exists b, restrict (as_inj mu) (vis mu) b = Some(b', 0) /\ e!id = Some(b, ty);
    me_flat:
      forall id b' ty b delta,
      te!id = Some(b', ty) -> as_inj mu b = Some(b', delta) -> e!id = Some(b, ty) /\ delta = 0;
    me_incr:
      Ple lo hi;
    me_tincr:
      Ple tlo thi
  }.

(** Invariance by change of memory and injection *)

Lemma match_envs_intern_invariant:
  forall mu e le m lo hi te tle tlo thi mu' m',
  match_envs mu e le m lo hi te tle tlo thi ->
  (forall b chunk v,
    as_inj mu b = None -> Ple lo b /\ Plt b hi -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  intern_incr mu mu' ->
  (*(forall b, Ple lo b /\ Plt b hi -> as_inj mu' b = as_inj mu b) ->*)
  (forall b b' delta, as_inj mu' b = Some(b', delta) -> Ple tlo b' /\ Plt b' thi -> as_inj mu' b = as_inj mu b) ->
  forall (WD: SM_wd mu) (WD': SM_wd mu'),
  match_envs mu' e le m' lo hi te tle tlo thi.
Proof.
  intros until m'; intros ME LD INCR INV. 
  destruct ME; constructor; eauto. 
(* vars *)
  intros. generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_not_lifted; eauto.
     eapply INCR; eauto. 
  eapply match_var_not_local; eauto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [v' [A B]]. 
  exists v'; split; eauto.
  eapply val_inject_incr; try eassumption.
  eapply intern_incr_restrict; eassumption.
  (*range*)

  intros. 
  destruct (me_range0 _ _ _ H) as [Rng1 [Rng2 Rng3]].
    eapply INCR in Rng3.
    intuition.   
  (*trange*)
  intros. 
  destruct (me_trange0 _ _ _ H) as [Rng1 [Rng2 Rng3]].
    eapply INCR in Rng3.
    intuition. 
    (* mapped *)
  intros. exploit me_mapped0; eauto. intros [b [A B]]. exists b; split; auto.
   eapply intern_incr_restrict; eassumption.  
(* flat *)
  intros. eapply me_flat0; eauto. rewrite <- H0.
  destruct (me_trange0 _ _ _ H) as [? [? ?]]. 
  symmetry. eapply INV; eauto.
Qed.

Definition privBlocksSrc mu b := locBlocksSrc mu b && negb (pubBlocksSrc mu b).

Lemma match_envs_extern_invariantPriv:
  forall mu e le m lo hi te tle tlo thi mu' m',
  match_envs mu e le m lo hi te tle tlo thi ->
  (forall b chunk v,
    privBlocksSrc mu b = true -> Ple lo b /\ Plt b hi -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  extern_incr mu mu' ->
  (*(forall b, Ple lo b /\ Plt b hi -> as_inj mu' b = as_inj mu b) ->
  (forall b b' delta, as_inj mu' b = Some(b', delta) -> Ple tlo b' /\ Plt b' thi -> as_inj mu' b = as_inj mu b) ->*)
  forall (WD: SM_wd mu) (WD': SM_wd mu'),
  match_envs mu' e le m' lo hi te tle tlo thi.
Proof.
  intros until m'; intros ME LD INCR (*INV1 INV2*).
  destruct ME; constructor; eauto. 
(* vars *)
  intros. generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_not_lifted; eauto.
    assert (LocMuMu': local_of mu = local_of mu') by eapply INCR.
    rewrite LocMuMu' in *; trivial.
  eapply match_var_not_local; eauto.
(* temps *)
  intros. exploit me_temps0; eauto. intros [v' [A B]]. 
  exists v'; split; eauto.
  eapply val_inject_incr; try eassumption.
   eapply extern_incr_restrict; eassumption. 
(* range *)
  intros. 
  destruct (me_range0 _ _ _ H) as [Rng1 [Rng2 Rng3]].
    rewrite (extern_incr_locBlocksSrc _ _ INCR) in Rng3.
    intuition. 
(* trange *)
  intros. 
  destruct (me_trange0 _ _ _ H) as [Rng1 [Rng2 Rng3]].
    rewrite (extern_incr_locBlocksTgt _ _ INCR) in Rng3.
    intuition. 
(* mapped *)
  intros. exploit me_mapped0; eauto. intros [b [A B]]. exists b; split; auto.
   eapply extern_incr_restrict; eassumption.  
(* flat *)
  intros. eapply me_flat0; eauto. rewrite <- H0.
  destruct (me_trange0 _ _ _ H) as [Rng1 [Rng2 Rng3]]. 
  rewrite H0.
  rewrite (extern_incr_locBlocksTgt _ _ INCR) in Rng3.
  destruct (joinD_Some _ _ _ _ _ H0) as [EXT' | [EXT' LOC']]; clear H0.
    assert (LocBF: locBlocksTgt mu' b' = false).
      eapply extern_DomRng'; eassumption.
    rewrite LocBF in Rng3; discriminate.
      rewrite <- (extern_incr_local _ _ INCR) in LOC'.
        apply local_in_all in LOC'; trivial.
Qed.

(*
Lemma match_envs_extcallPriv:
  forall mu e le m lo hi te tle tlo thi tm mu' m',
  match_envs mu e le m lo hi te tle tlo thi ->
  Mem.unchanged_on (fun b ofs => privBlocksSrc mu b = true) m m' ->
  extern_incr mu mu' ->
  sm_inject_separated mu mu' m tm ->
  Ple hi (Mem.nextblock m) -> Ple thi (Mem.nextblock tm) ->
  forall (WD: SM_wd mu) (WD': SM_wd mu'),
  match_envs mu' e le m' lo hi te tle tlo thi.
Proof.
  intros. 
  apply sm_inject_separated_mem in H2; trivial.
  eapply match_envs_extern_invariantPriv; eauto. 
  intros. eapply Mem.load_unchanged_on; eauto.
  red in H2. intros. destruct (as_inj mu b) as [[b' delta]|] eqn:?. 
  eapply (extern_incr_as_inj _ _ H1); eauto.
  destruct (as_inj mu' b) as [[b' delta]|] eqn:?; auto.
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  xomegaContradiction.
  apply extern_incr_as_inj in H1; trivial.
  intros. destruct (as_inj mu b) as [[b'' delta']|] eqn:?. eauto. 
  exploit H2; eauto. unfold Mem.valid_block. intros [A B].
  xomegaContradiction.
Qed.*)

(** Correctness of [make_cast] *)

Lemma make_cast_correct:
  forall e le m a v1 tto v2,
  eval_expr tge e le m a v1 ->
  sem_cast v1 (typeof a) tto = Some v2 ->
  eval_expr tge e le m (make_cast a tto) v2.
Proof.
  intros.
  assert (DFL: eval_expr tge e le m (Ecast a tto) v2).
    econstructor; eauto.
  unfold sem_cast, make_cast in *. 
  destruct (classify_cast (typeof a) tto); auto.
  destruct v1; inv H0; auto.
  destruct sz2; auto. destruct v1; inv H0; auto.
  destruct sz2; auto. destruct v1; inv H0; auto.
  destruct v1; inv H0; auto.
  destruct v1; try discriminate.
  destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; auto.
  destruct v1; try discriminate.
  destruct (ident_eq id1 id2 && fieldlist_eq fld1 fld2); inv H0; auto.
  inv H0; auto.
Qed.

(** Preservation by assignment to a temporary *)

Lemma match_envs_set_temp:
  forall mu e le m lo hi te tle tlo thi id v tv,
  match_envs mu e le m lo hi te tle tlo thi ->
  val_inject (restrict (as_inj mu) (vis mu)) v tv ->
  match_envs mu e (PTree.set id v le) m lo hi te (PTree.set id tv tle) tlo thi.
Proof.
  intros. 
  destruct H. constructor; eauto; intros.
(* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_not_lifted; eauto. 
  eapply match_var_not_local; eauto. 
(* temps *)
  rewrite PTree.gsspec in *. destruct (peq id0 id). 
  inv H. exists tv; auto. 
  eapply me_temps0; eauto. 
Qed.

Lemma match_envs_set_opttemp:
  forall mu e le m lo hi te tle tlo thi optid v tv,
  match_envs mu e le m lo hi te tle tlo thi ->
  val_inject (restrict (as_inj mu) (vis mu)) v tv ->
  match_envs mu e (set_opttemp optid v le) m lo hi te (set_opttemp optid tv tle) tlo thi.
Proof.
  intros. unfold set_opttemp. destruct optid; simpl in H0.
  eapply match_envs_set_temp; eauto.
  auto.
Qed.

(** Extensionality with respect to temporaries *)

Lemma match_envs_temps_exten:
  forall mu e le m lo hi te tle tlo thi tle',
  match_envs mu e le m lo hi te tle tlo thi ->
  (forall id, tle'!id = tle!id) ->
  match_envs mu e le m lo hi te tle' tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id); intros MV; inv MV.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite H0. eauto.
Qed.

(** Invariance by assignment to an irrelevant temporary *)

Lemma match_envs_change_temp:
  forall mu e le m lo hi te tle tlo thi id v,
  match_envs mu e le m lo hi te tle tlo thi ->
  le!id = None -> 
  match_envs mu e le m lo hi te (PTree.set id v tle) tlo thi.
Proof.
  intros. destruct H. constructor; auto; intros.
  (* vars *)
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_not_lifted; eauto.
  eapply match_var_not_local; eauto.
  (* temps *)
  rewrite PTree.gso. eauto. congruence.
Qed.

(** Allocation and initialization of parameters *)

Lemma alloc_variables_nextblock:
  forall e m vars e' m',
  alloc_variables e m vars e' m' -> Ple (Mem.nextblock m) (Mem.nextblock m').
Proof.
  induction 1.
  apply Ple_refl.
  eapply Ple_trans; eauto. exploit Mem.nextblock_alloc; eauto. intros EQ; rewrite EQ. apply Ple_succ. 
Qed.

Lemma alloc_variables_range:
  forall id b ty e m vars e' m',
  alloc_variables e m vars e' m' ->
  e'!id = Some(b, ty) -> e!id = Some(b, ty) \/ Ple (Mem.nextblock m) b /\ Plt b (Mem.nextblock m').
Proof.
  induction 1; intros.
  auto.
  exploit IHalloc_variables; eauto. rewrite PTree.gsspec. intros [A|A].
  destruct (peq id id0). inv A. 
  right. exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto.
  generalize (alloc_variables_nextblock _ _ _ _ _ H0). intros A B C. 
  subst b. split. apply Ple_refl. eapply Plt_le_trans; eauto. rewrite B. apply Plt_succ. 
  auto.
  right. exploit Mem.nextblock_alloc; eauto. intros B. rewrite B in A. xomega. 
Qed.

Lemma alloc_variables_injective:
  forall id1 b1 ty1 id2 b2 ty2 e m vars e' m',
  alloc_variables e m vars e' m' ->
  (e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2) ->
  (forall id b ty, e!id = Some(b, ty) -> Plt b (Mem.nextblock m)) ->
  (e'!id1 = Some(b1, ty1) -> e'!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2).
Proof.
  induction 1; intros. 
  eauto.
  eapply IHalloc_variables; eauto. 
  repeat rewrite PTree.gsspec; intros.
  destruct (peq id1 id); destruct (peq id2 id).
  congruence.
  inv H6. exploit Mem.alloc_result; eauto. exploit H2; eauto. unfold block; xomega.
  inv H7. exploit Mem.alloc_result; eauto. exploit H2; eauto. unfold block; xomega.
  eauto.
  intros. rewrite PTree.gsspec in H6. destruct (peq id0 id). inv H6.
  exploit Mem.alloc_result; eauto. exploit Mem.nextblock_alloc; eauto. unfold block; xomega.
  exploit H2; eauto. exploit Mem.nextblock_alloc; eauto. unfold block; xomega.
Qed.

Definition alloc_left_unmapped_sm (mu: SM_Injection) b1: SM_Injection :=
  Build_SM_Injection (fun b => eq_block b b1 || locBlocksSrc mu b)
                     (locBlocksTgt mu)
                     (pubBlocksSrc mu) (pubBlocksTgt mu)
                     (fun b => if eq_block b b1 then None 
                               else local_of mu b)
                     (extBlocksSrc mu) (extBlocksTgt mu)
                     (frgnBlocksSrc mu) (frgnBlocksTgt mu) (extern_of mu).

Lemma alloc_left_unmapped_sm_wd: forall mu b1 (WD: SM_wd mu)
      (NEW1: DomSrc mu b1 = false),
      SM_wd (alloc_left_unmapped_sm mu b1).
Proof. intros. 
econstructor; simpl in *; try solve [eapply WD].
  intros. apply orb_false_iff in NEW1.
    remember (eq_block b b1) as d.
    destruct d; simpl in *; apply eq_sym in Heqd.
      subst. right. apply NEW1.
      apply WD.
  intros. 
    remember (eq_block b0 b1) as d.
      destruct d; simpl in *; apply eq_sym in Heqd. inv H.
    apply (local_DomRng _ WD _ _ _ H).
  intros.
    destruct (pubSrc _ WD _ H) as [bb [dd [PB PT]]].
    exists bb, dd.
    remember (eq_block b0 b1) as d.
      destruct d; simpl in *; apply eq_sym in Heqd.
        subst. unfold DomSrc in NEW1.
        rewrite (pubBlocksLocalSrc _ WD _ H) in NEW1. simpl in *. discriminate.
      rewrite (pub_in_local _ _ _ _ PB).
      split; trivial. 
Qed.

Lemma alloc_left_unmapped_sm_as_inj_same: forall mu b1 (WD: SM_wd mu)
      (NEW1: DomSrc mu b1 = false),
      as_inj (alloc_left_unmapped_sm mu b1) b1 = None. 
Proof. intros.
  unfold as_inj, join; simpl.
  remember (extern_of mu b1) as d.
  destruct d; apply eq_sym in Heqd; simpl. destruct p.
    destruct (extern_DomRng' _ WD _ _ _ Heqd). rewrite NEW1 in H0. intuition.
  destruct (eq_block b1 b1); subst; trivial.
    elim n. trivial.
Qed.

Lemma alloc_left_unmapped_sm_as_inj_other: forall mu b1 b (H: b<>b1),
      as_inj (alloc_left_unmapped_sm mu b1) b = as_inj mu b.
Proof. intros.
  unfold as_inj, join; simpl.
  destruct (eq_block b b1); subst; trivial. elim H. trivial.
Qed.

Lemma alloc_left_unmapped_sm_intern_incr: 
      forall mu b1 (H: as_inj mu b1 = None) (WD: SM_wd mu),
      intern_incr mu (alloc_left_unmapped_sm mu b1).
Proof. intros.
  specialize (local_in_all _ WD); intros.
  red; intros. destruct mu; simpl in *.
  intuition.
  red; intros.
  destruct (eq_block b b1); subst.
     rewrite (H0 _ _ _ H1) in H. inv H.
  assumption.
Qed.

Lemma alloc_left_unmapped_sm_inject_incr: 
      forall mu b1 (H: as_inj mu b1 = None),
      inject_incr (as_inj mu) (as_inj (alloc_left_unmapped_sm mu b1)).
Proof. intros.
  red; intros.
  destruct (eq_block b b1); subst. congruence.
  rewrite alloc_left_unmapped_sm_as_inj_other; trivial.
Qed.

Lemma alloc_left_unmapped_sm_DomSrc mu b1:
      DomSrc (alloc_left_unmapped_sm mu b1) = fun b => eq_block b b1 || DomSrc mu b.
Proof. intros. extensionality b. 
  unfold DomSrc, alloc_left_unmapped_sm; simpl.
  rewrite <- orb_assoc. trivial.
Qed.

Lemma alloc_left_unmapped_sm_DomTgt mu b1:
      DomTgt (alloc_left_unmapped_sm mu b1) = DomTgt mu.
Proof. intros. reflexivity. Qed.

Lemma REACH_closed_alloc_left_unmapped_sm: forall m lo hi sp m'
          (ALLOC : Mem.alloc m lo hi = (m', sp))
          mu (RC: REACH_closed m (vis mu)),
      REACH_closed m' (vis (alloc_left_unmapped_sm mu sp)).
Proof.
  red; intros.
  unfold vis. simpl.
  destruct (eq_block b sp); try subst b. trivial.
  simpl.
  apply RC. rewrite REACHAX in H. 
  destruct H as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
    apply REACH_nil.
      unfold vis in H. simpl in H.
      destruct (eq_block b sp); try subst b. elim n; trivial.
      apply H.
    destruct (eq_block b' sp); try subst b'.
      rewrite (AllocContentsUndef1 _ _ _ _ _ ALLOC) in H4. inv H4. 
    specialize (IHL _ H1 n1); clear H1.
      apply (Mem.perm_alloc_4 _ _ _ _ _ ALLOC) in H2; trivial. 
      destruct (Mem.alloc_unchanged_on (fun bb zz => True)
         _ _ _ _ _ ALLOC) as [UP UC].
      rewrite UC in H4; trivial. 
        eapply REACH_cons; try eassumption. 
Qed.

Theorem alloc_left_unmapped_sm_inject:
  forall mu m1 m2 lo hi m1' b1,
  Mem.inject (as_inj mu) m1 m2 ->
  Mem.alloc m1 lo hi = (m1', b1) ->
  forall (WD: SM_wd mu) (SMV: sm_valid mu m1 m2) 
         (RC: REACH_closed m1 (vis mu)),
  exists mu',
     Mem.inject (as_inj mu') m1' m2
  /\ intern_incr mu mu'
  /\ as_inj mu' b1 = None
  /\ (forall b, b <> b1 -> as_inj mu' b = as_inj mu b)
  /\ SM_wd mu' /\ sm_valid mu' m1' m2
  /\ sm_locally_allocated mu mu' m1 m2 m1' m2 
  /\ REACH_closed m1' (vis mu').
Proof.
  intros. inversion H.
(*  set (f' := fun b => if eq_block b b1 then None else f b).*)
  exists (alloc_left_unmapped_sm mu b1).
  specialize (alloc_DomSrc _ _ _ SMV _ _ _ _ H0). intros DomB1.
  assert (FRESH: as_inj mu b1 = None).
    case_eq (as_inj mu b1); intros; trivial.
    destruct p. exploit as_inj_DomRng; try eassumption. intros [KK _]. rewrite KK in DomB1; discriminate.
  exploit (alloc_left_unmapped_sm_intern_incr); try eassumption. intros INCR.
  exploit alloc_left_unmapped_sm_as_inj_same; try eassumption. intros AIB1; rewrite AIB1.
  assert (AIother:= alloc_left_unmapped_sm_as_inj_other mu b1).
assert (Mem.mem_inj (as_inj (alloc_left_unmapped_sm mu b1)) m1 m2).
    inversion mi_inj; constructor; eauto with mem.
    intros. destruct (eq_block b0 b1). congruence.
            rewrite (AIother _ n) in H1. eauto.
    intros. destruct (eq_block b0 b1). congruence.
            rewrite (AIother _ n) in H1. eauto.
    intros. destruct (eq_block b0 b1). congruence. 
            rewrite (AIother _ n) in H1.
            apply memval_inject_incr with (as_inj mu); auto.
            eapply alloc_left_unmapped_sm_inject_incr; eassumption. 
split.
{ (*Mem.inject*)
  split.
  + (* inj *)
  eapply Mem.alloc_left_unmapped_inj; eauto. 
  + (* freeblocks *)
  intros. destruct (eq_block b b1); subst; eauto.
          rewrite (AIother _ n).
  apply mi_freeblocks. red; intro; elim H3. eauto with mem. 
  + (* mappedblocks *)
  intros. destruct (eq_block b b1); subst. congruence. 
          rewrite (AIother _ n) in H2. eauto. 
  + (* no overlap *)
  red; intros.
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
  eapply mi_no_overlap. eexact H2.
    rewrite (AIother _ n) in *. eauto.
    rewrite (AIother _ n0) in *. eauto.
  exploit Mem.perm_alloc_inv. eauto. eexact H5. rewrite dec_eq_false; auto.  
  exploit Mem.perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto. 
  + (* representable *)
  intros.
  destruct (eq_block b b1); subst.
    rewrite AIB1 in *; discriminate.
  rewrite (AIother _ n) in H2.
  eapply mi_representable; try eassumption.
  destruct H3; eauto using Mem.perm_alloc_4.
  + (*spill -- same proof as in SimplLocals_proof_comp.v*)
  intros.
  destruct (eq_block b0 b1).
  - subst. rewrite alloc_left_unmapped_sm_as_inj_same in H2; trivial. inv H2.
  - rewrite alloc_left_unmapped_sm_as_inj_other in H2; trivial.
    destruct (mi_spill _ _ _ _ _ _ H2 H3).
    left. eapply Mem.perm_alloc_1; eassumption.
    right. intros N. elim H4; clear H4. eapply Mem.perm_alloc_4; eassumption.
}
intuition.
(* SM_wd*)
  eapply alloc_left_unmapped_sm_wd; eassumption.
(* sm_valid*)
  split; intros. 
  unfold DOM in H2; rewrite alloc_left_unmapped_sm_DomSrc in H2.
    destruct (eq_block b0 b1); try subst b0.
      apply (Mem.valid_new_block _ _ _ _ _ H0).
    simpl in H2.
    apply (Mem.valid_block_alloc _ _ _ _ _ H0).
    apply SMV; trivial.
  unfold RNG in H2. rewrite alloc_left_unmapped_sm_DomTgt in H2.
     apply SMV; trivial. 
(*sm_locally_allocated*)
  apply sm_locally_allocatedChar. 
  repeat rewrite alloc_left_unmapped_sm_DomSrc.
  repeat rewrite alloc_left_unmapped_sm_DomTgt.
  repeat split; extensionality bb; 
   try rewrite (freshloc_irrefl m2); 
   try rewrite (freshloc_alloc _ _ _ _ _ H0); simpl. 
   apply orb_comm. intuition. 
   apply orb_comm. intuition. 
(* REACH_closed*)
  clear - RC H0.
  eapply REACH_closed_alloc_left_unmapped_sm; eassumption.
Qed.  

Lemma match_alloc_variables:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall mu tm te,
  list_norepet (var_names vars) ->
  Mem.inject (as_inj mu) m tm ->
  forall (WD: SM_wd mu) (SMV: sm_valid mu m tm)
         (RC: REACH_closed m (vis mu)),
  exists mu', exists te', exists tm',
      alloc_variables te tm vars te' tm'
  /\ Mem.inject (as_inj mu') m' tm'
  /\ intern_incr mu mu'
  /\ (forall b, Mem.valid_block m b -> as_inj mu' b = as_inj mu b)
  /\ (forall b b' delta, as_inj mu' b = Some(b', delta) -> Mem.valid_block tm b' -> as_inj mu' b = as_inj mu b)
  /\ (forall b b' delta, as_inj mu' b = Some(b', delta) -> ~Mem.valid_block tm b' -> 
         exists id, exists ty, e'!id = Some(b, ty) /\ te'!id = Some(b', ty) /\ delta = 0)
  /\ (forall id ty, In (id, ty) vars ->
      exists b, 
          e'!id = Some(b, ty)
       /\ (*NEW*) locBlocksSrc mu' b = true
       /\ exists tb, te'!id = Some(tb, ty) /\ as_inj mu' b = Some(tb, 0))
  /\ (forall id, ~In id (var_names vars) -> e'!id = e!id /\ te'!id = te!id)
  /\ SM_wd mu' /\ sm_valid mu' m' tm'
  /\ sm_locally_allocated mu mu' m tm m' tm' 
  /\ REACH_closed m' (vis mu').
Proof.
  induction 1; intros.
  (* base case *)
  exists mu; exists te; exists tm. simpl.
  split. constructor.
  split. auto. split. apply intern_incr_refl.
         split. auto.  split. auto. 
  split. intros. elim H2. eapply Mem.mi_mappedblocks; eauto.
  split. tauto. split. auto.
  intuition. apply sm_locally_allocated_refl. 
  
  (* inductive case *)
  simpl in H1. inv H1. simpl.
  (* variable is not lifted out of memory *)
  exploit alloc_parallel_intern.
    eauto. eauto. eauto. eauto. apply Zle_refl. apply Zle_refl. 
  intros [mu1 [tm1 [tb1 [A [B [C [D [E [SEP1 [LocAlloc1 [WD1 [SMV1 RC1]]]]]]]]]]]].
  exploit IHalloc_variables; eauto. instantiate (1 := PTree.set id (tb1, ty) te). 
  intros [mu' [te' [tm' [J [K [L [M [N [Q [O [P MU']]]]]]]]]]].
  exists mu'; exists te'; exists tm'.
  split. simpl. econstructor; eauto.
  split. auto.
  split. eapply intern_incr_trans; eauto. 
  split. intros. transitivity (as_inj mu1 b). apply M. eapply Mem.valid_block_alloc; eauto. 
    apply E. apply Mem.valid_not_valid_diff with m; auto. eapply Mem.fresh_block_alloc; eauto. 
  split. intros. transitivity (as_inj mu1 b). eapply N; eauto. eapply Mem.valid_block_alloc; eauto. 
    destruct (eq_block b b1); auto. subst. 
    assert (as_inj mu' b1 = as_inj mu1 b1). apply M. eapply Mem.valid_new_block; eauto.
    rewrite H4 in H1. rewrite D in H1. inv H1. eelim Mem.fresh_block_alloc; eauto.
  split. intros. destruct (eq_block b' tb1). 
    subst b'. rewrite (N _ _ _ H1) in H1.
    destruct (eq_block b b1). subst b. rewrite D in H1; inv H1. 
    exploit (P id); auto. intros [X Y]. exists id; exists ty.
    rewrite X; rewrite Y. repeat rewrite PTree.gss. auto.
    rewrite E in H1; auto. elim H3. eapply Mem.mi_mappedblocks; eauto. 
    eapply Mem.valid_new_block; eauto.
    eapply Q; eauto. unfold Mem.valid_block in *.
    exploit Mem.nextblock_alloc. eexact A. exploit Mem.alloc_result. eexact A. 
    unfold block; xomega.
  split. intros. destruct (ident_eq id0 id).
    (* same var *)
    subst id0.
    assert (ty0 = ty).
      destruct H1. congruence. elim H5. unfold var_names. change id with (fst (id, ty0)). apply in_map; auto.
    subst ty0. 
    exploit P; eauto. intros [X Y]. rewrite X. rewrite Y. 
    exists b1. split. apply PTree.gss.
    split. eapply L. apply sm_locally_allocatedChar in LocAlloc1.
           assert (LBS: locBlocksSrc mu1 = fun b => locBlocksSrc mu b || freshloc m m1 b) by eapply LocAlloc1.
           rewrite LBS; clear LBS LocAlloc1.
           rewrite (freshloc_alloc _ _ _ _ _ H).
           destruct (eq_block b1 b1); auto; intuition.
    exists tb1; split. 
    apply PTree.gss.
    rewrite M. auto. eapply Mem.valid_new_block; eauto. 
    (* other vars *)
    exploit (O id0 ty0). destruct H1. congruence. auto. 
    auto.
  split. intros. exploit (P id0). tauto. intros [X Y]. rewrite X; rewrite Y.
    split; apply PTree.gso; intuition.
  intuition.
  apply alloc_forward in H.
  apply alloc_forward in A.
  apply alloc_variables_forward in H0.
  apply alloc_variables_forward in J.
  eapply sm_locally_allocated_trans; try eassumption.
Qed.

Lemma alloc_variables_load:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  forall chunk b ofs v,
  Mem.load chunk m b ofs = Some v ->
  Mem.load chunk m' b ofs = Some v.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. eapply Mem.load_alloc_other; eauto.
Qed.

Lemma sizeof_by_value:
  forall ty chunk,
  access_mode ty = By_value chunk -> size_chunk chunk <= sizeof ty.
Proof.
  unfold access_mode; intros.
Local Opaque alignof. 
  destruct ty; try destruct i; try destruct s; try destruct f; inv H;
  apply align_le; apply alignof_pos.
Qed.

Definition env_initial_value (e: env) (m: mem) :=
  forall id b ty chunk,
  e!id = Some(b, ty) -> access_mode ty = By_value chunk -> Mem.load chunk m b 0 = Some Vundef.
 
Lemma alloc_variables_initial_value:
  forall e m vars e' m',
  alloc_variables e m vars e' m' ->
  env_initial_value e m ->
  env_initial_value e' m'.
Proof.
  induction 1; intros.
  auto.
  apply IHalloc_variables. red; intros. rewrite PTree.gsspec in H2. 
  destruct (peq id0 id). inv H2. 
  eapply Mem.load_alloc_same'; eauto. 
  omega. rewrite Zplus_0_l. eapply sizeof_by_value; eauto. 
  apply Zdivide_0. 
  eapply Mem.load_alloc_other; eauto. 
Qed.

Lemma create_undef_temps_charact:
  forall id ty vars, In (id, ty) vars -> (create_undef_temps vars)!id = Some Vundef.
Proof.
  induction vars; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss. 
  destruct a as [id1 ty1]. rewrite PTree.gsspec. destruct (peq id id1); auto. 
Qed.

Lemma create_undef_temps_inv:
  forall vars id v, (create_undef_temps vars)!id = Some v -> v = Vundef /\ In id (var_names vars).
Proof.
  induction vars; simpl; intros. 
  rewrite PTree.gempty in H; congruence.
  destruct a as [id1 ty1]. rewrite PTree.gsspec in H. destruct (peq id id1).
  inv H. auto.
  exploit IHvars; eauto. tauto.
Qed.

Lemma create_undef_temps_exten:
  forall id l1 l2,
  (In id (var_names l1) <-> In id (var_names l2)) ->
  (create_undef_temps l1)!id = (create_undef_temps l2)!id.
Proof.
  assert (forall id l1 l2,
          (In id (var_names l1) -> In id (var_names l2)) ->
          (create_undef_temps l1)!id = None \/ (create_undef_temps l1)!id = (create_undef_temps l2)!id).
    intros. destruct ((create_undef_temps l1)!id) as [v1|] eqn:?; auto.
    exploit create_undef_temps_inv; eauto. intros [A B]. subst v1.
    exploit list_in_map_inv. unfold var_names in H. apply H. eexact B.
    intros [[id1 ty1] [P Q]]. simpl in P; subst id1.
    right; symmetry; eapply create_undef_temps_charact; eauto.
  intros. 
  exploit (H id l1 l2). tauto. 
  exploit (H id l2 l1). tauto. 
  intuition congruence.
Qed.

Remark var_names_app:
  forall vars1 vars2, var_names (vars1 ++ vars2) = var_names vars1 ++ var_names vars2.
Proof.
  intros. apply map_app. 
Qed.

Remark filter_app:
  forall (A: Type) (f: A -> bool) l1 l2,
  List.filter f (l1 ++ l2) = List.filter f l1 ++ List.filter f l2.
Proof.
  induction l1; simpl; intros.
  auto.
  destruct (f a). simpl. decEq; auto. auto.
Qed.

Remark filter_charact:
  forall (A: Type) (f: A -> bool) x l,
  In x (List.filter f l) <-> In x l /\ f x = true.
Proof.
  induction l; simpl. tauto. 
  destruct (f a) eqn:?. 
  simpl. rewrite IHl. intuition congruence.
  intuition congruence.
Qed.

Remark filter_norepet:
  forall (A: Type) (f: A -> bool) l,
  list_norepet l -> list_norepet (List.filter f l).
Proof.
  induction 1; simpl. constructor. 
  destruct (f hd); auto. constructor; auto. rewrite filter_charact. tauto. 
Qed.

Remark filter_map:
  forall (A B: Type) (f: A -> B) (pa: A -> bool) (pb: B -> bool),
  (forall a, pb (f a) = pa a) ->
  forall l, List.map f (List.filter pa l) = List.filter pb (List.map f l).
Proof.
  induction l; simpl.
  auto.
  rewrite H. destruct (pa a); simpl; congruence.
Qed.

Lemma create_undef_temps_lifted:
  forall id f,
  ~ In id (var_names (fn_params f)) ->
  (create_undef_temps (add_lifted (cenv_for f) (fn_vars f) (fn_temps f))) ! id =
  (create_undef_temps (add_lifted (cenv_for f) (fn_params f ++ fn_vars f) (fn_temps f))) ! id.
Proof.
  intros. apply create_undef_temps_exten. 
  unfold add_lifted. rewrite filter_app. 
  unfold var_names in *. 
  repeat rewrite map_app. repeat rewrite in_app. intuition. 
  exploit list_in_map_inv; eauto. intros [[id1 ty1] [P Q]]. simpl in P. subst id. 
  rewrite filter_charact in Q. destruct Q. 
  elim H. change id1 with (fst (id1, ty1)). apply List.in_map. auto.
Qed.

Lemma vars_and_temps_properties:
  forall cenv params vars temps,
  list_norepet (var_names params ++ var_names vars) ->
  list_disjoint (var_names params) (var_names temps) ->
  list_norepet (var_names params)
  /\ list_norepet (var_names (remove_lifted cenv (params ++ vars)))
  /\ list_disjoint (var_names params) (var_names (add_lifted cenv vars temps)).
Proof.
  intros. rewrite list_norepet_app in H. destruct H as [A [B C]].
  split. auto.
  split. unfold remove_lifted. unfold var_names. erewrite filter_map. 
  instantiate (1 := fun a => negb (VSet.mem a cenv)). 2: auto.
  apply filter_norepet. rewrite map_app. apply list_norepet_append; assumption.
  unfold add_lifted. rewrite var_names_app. 
  unfold var_names at 2. erewrite filter_map. 
  instantiate (1 := fun a => VSet.mem a cenv). 2: auto.
  change (map fst vars) with (var_names vars).
  red; intros.
  rewrite in_app in H1. destruct H1.
  rewrite filter_charact in H1. destruct H1. apply C; auto.
  apply H0; auto.
Qed.

Theorem match_envs_alloc_variables:
  forall m vars e m' temps mu tm,
  alloc_variables empty_env m vars e m' ->
  list_norepet (var_names vars) ->
  Mem.inject (as_inj mu) m tm ->
  forall (WD: SM_wd mu) (SMV: sm_valid mu m tm)
         (RC: REACH_closed m (vis mu)),
  exists mu', exists te, exists tm',
     alloc_variables empty_env tm vars te tm'
  /\ match_envs mu' e (create_undef_temps temps) m' (Mem.nextblock m) (Mem.nextblock m')
                    te (create_undef_temps temps) (Mem.nextblock tm) (Mem.nextblock tm')
  /\ Mem.inject (as_inj mu') m' tm'
  /\ intern_incr mu mu'
  /\ (forall b, Mem.valid_block m b -> as_inj mu' b = as_inj mu b)
  /\ (forall b b' delta, as_inj mu' b = Some(b', delta) -> Mem.valid_block tm b' -> as_inj mu' b = as_inj mu b)
  /\ SM_wd mu' /\ sm_valid mu' m' tm'
  /\ sm_locally_allocated mu mu' m tm m' tm' 
  /\ REACH_closed m' (vis mu').
Proof.
  intros. 
  exploit (match_alloc_variables); eauto. instantiate (1 := empty_env). 
  intros [mu' [te [tm' [A [B [C [D [E [K [F [G [WD' [SMV' [LocAlloc' RC']]]]]]]]]]]]]]. 
  exists mu'; exists te; exists tm'.
  split. auto. split; auto.
  constructor; intros.
  (* vars *)
  destruct (In_dec ident_eq id (var_names vars)).
  unfold var_names in i. exploit list_in_map_inv; eauto.
  intros [[id' ty] [EQ IN]]; simpl in EQ; subst id'.
  exploit F; eauto. intros [b [P R]]. 
  (* local var, not lifted *)
  destruct R as [LBS [tb [U V]]].
  eapply match_var_not_lifted; try eassumption.
     rewrite <- locBlocksSrc_as_inj_local; eassumption.
  (* non-local var *)
  exploit G; eauto. unfold empty_env. rewrite PTree.gempty. intros [U V].
  eapply match_var_not_local; eauto. 

  (* temps *)
  exploit create_undef_temps_inv; eauto. intros [P Q]. subst v.
  unfold var_names in Q. exploit list_in_map_inv; eauto. 

  (* injective *)
  eapply alloc_variables_injective. eexact H. 
  rewrite PTree.gempty. congruence.
  intros. rewrite PTree.gempty in H5. congruence.
  eauto. eauto. auto. 

  (* range *)
  exploit alloc_variables_range. eexact H. eauto. 
  rewrite PTree.gempty. intros [X | [M M']]. discriminate. 
  destruct (in_dec peq id (var_names vars)). 
    unfold var_names in i. apply in_map_iff in i. 
    destruct i as [[i t] [I IN]]. subst id. 
    destruct (F _ _ IN) as [bb [? [? _]]]. simpl in H2.
    rewrite H2 in H3. inv H3. intuition. 
  destruct (G _ n).
    rewrite H2 in H3. 
    rewrite PTree.gempty in H3. congruence. 


  (* trange *)
  exploit alloc_variables_range. eexact A. eauto. 
  rewrite PTree.gempty. intros [X | [TM TM']]. discriminate.
  destruct (in_dec peq id (var_names vars)). 
    unfold var_names in i. apply in_map_iff in i. 
    destruct i as [[i t] [I IN]]. subst id. simpl in H2.
    destruct (F _ _ IN) as [bb [? [? ?]]]. 
    destruct H5 as [tb [TEi AI']].
      rewrite H2 in TEi; inv TEi.
      rewrite (as_inj_locBlocks _ _ _ _ WD' AI') in H4.
      intuition.      
  destruct (G _ n).
    rewrite H2 in H4. 
    rewrite PTree.gempty in H4. congruence.
    
  (* mapped *)
  destruct (In_dec ident_eq id (var_names vars)).
  unfold var_names in i. exploit list_in_map_inv; eauto. 
  intros [[id' ty'] [EQ IN]]; simpl in EQ; subst id'.
  exploit F; eauto. intros [b [P [LBS Q]]].
  destruct Q as [tb [U V]].
  exists b; split. unfold vis. eapply restrictI_Some; intuition.
    congruence. congruence.
  exploit G; eauto. rewrite PTree.gempty. intuition congruence.

  (* flat *)
  exploit alloc_variables_range. eexact A. eauto. 
  rewrite PTree.gempty. intros [P|P]. congruence.

  exploit K; eauto. unfold Mem.valid_block. xomega. 
  intros [id0 [ty0 [U [V W]]]]. split; auto. 
  destruct (ident_eq id id0). congruence.
  assert (b' <> b').
  eapply alloc_variables_injective with (e' := te) (id1 := id) (id2 := id0); eauto.
  rewrite PTree.gempty; congruence. 
  intros until ty1; rewrite PTree.gempty; congruence.
  congruence.

  (* incr *)
  eapply alloc_variables_nextblock; eauto.
  eapply alloc_variables_nextblock; eauto.

  intuition.
Qed.

Lemma assign_loc_inject:
  forall f ty m loc ofs v m' tm loc' ofs' v',
  assign_loc ty m loc ofs v m' ->
  val_inject f (Vptr loc ofs) (Vptr loc' ofs') ->
  val_inject f v v' ->
  Mem.inject f m tm ->
  exists tm',
     assign_loc ty tm loc' ofs' v' tm'
  /\ Mem.inject f m' tm'
  /\ (forall b chunk v,
      f b = None -> Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v).
Proof.
  intros. inv H.
  (* by value *)
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [A B]].
  exists tm'; split. eapply assign_loc_value; eauto. 
  split. auto.
  intros. rewrite <- H5. eapply Mem.load_store_other; eauto.
  left. inv H0. congruence.
  (* by copy *)
  inv H0. inv H1.
  rename b' into bsrc. rename ofs'0 into osrc. 
  rename loc into bdst. rename ofs into odst.
  rename loc' into bdst'. rename b2 into bsrc'.
  exploit Mem.loadbytes_length; eauto. intros LEN.
  assert (SZPOS: sizeof ty > 0) by apply sizeof_pos.
  assert (RPSRC: Mem.range_perm m bsrc (Int.unsigned osrc) (Int.unsigned osrc + sizeof ty) Cur Nonempty).
    eapply Mem.range_perm_implies. eapply Mem.loadbytes_range_perm; eauto. auto with mem.
  assert (RPDST: Mem.range_perm m bdst (Int.unsigned odst) (Int.unsigned odst + sizeof ty) Cur Nonempty).
    replace (sizeof ty) with (Z_of_nat (length bytes)).
    eapply Mem.range_perm_implies. eapply Mem.storebytes_range_perm; eauto. auto with mem.
    rewrite LEN. apply nat_of_Z_eq. omega.
  assert (PSRC: Mem.perm m bsrc (Int.unsigned osrc) Cur Nonempty).
    apply RPSRC. omega.
  assert (PDST: Mem.perm m bdst (Int.unsigned odst) Cur Nonempty).
    apply RPDST. omega.
  exploit Mem.address_inject.  eauto. eexact PSRC. eauto. intros EQ1.
  exploit Mem.address_inject.  eauto. eexact PDST. eauto. intros EQ2.
  exploit Mem.loadbytes_inject; eauto. intros [bytes2 [A B]].
  exploit Mem.storebytes_mapped_inject; eauto. intros [tm' [C D]].
  exists tm'. 
  split. eapply assign_loc_copy; try rewrite EQ1; try rewrite EQ2; eauto. 
  eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_blockcopy_1248.
  eapply Zdivide_trans. apply alignof_blockcopy_divides. apply sizeof_alignof_compat.
  eapply Mem.aligned_area_inject with (m := m); eauto. apply alignof_blockcopy_1248.
  eapply Zdivide_trans. apply alignof_blockcopy_divides. apply sizeof_alignof_compat.
  eapply Mem.disjoint_or_equal_inject with (m := m); eauto.
  apply Mem.range_perm_max with Cur; auto.
  apply Mem.range_perm_max with Cur; auto.
  split. auto.
  intros. rewrite <- H0. eapply Mem.load_storebytes_other; eauto. 
  left. congruence.
Qed.

Remark bind_parameter_temps_inv:
  forall id params args le le',
  bind_parameter_temps params args le = Some le' ->
  ~In id (var_names params) ->
  le'!id = le!id.
Proof.
  induction params; simpl; intros. 
  destruct args; inv H. auto.
  destruct a as [id1 ty1]. destruct args; try discriminate. 
  transitivity ((PTree.set id1 v le)!id). 
  eapply IHparams; eauto. apply PTree.gso. intuition. 
Qed.

Lemma assign_loc_nextblock:
  forall ty m b ofs v m',
  assign_loc ty m b ofs v m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction 1. 
  simpl in H0. eapply Mem.nextblock_store; eauto.
  eapply Mem.nextblock_storebytes; eauto.
Qed.

Lemma  bind_parameters_nextblock: forall e params m args m' 
       (B: bind_parameters e m params args m'),
       Mem.nextblock m' = Mem.nextblock m.
Proof. intros e params.
  induction params; intros; inv B; trivial.
  rewrite (IHparams _ _ _ H6); clear IHparams.
    inv H3. simpl in *. apply (Mem.nextblock_store _ _ _ _ _ _ H0).
    apply (Mem.nextblock_storebytes _ _ _ _ _ H7).
Qed.

Fixpoint bind_parameters_effect e mu (params :list (ident * type)) (vals: list val) :=
 match params, vals with
   (idt :: params), (v1 :: vl) => 
     match e!(fst idt)
     with Some x => 
            fun b z => bind_parameters_effect e mu params vl b z ||
                       match as_inj mu (fst x) with 
                         None => false 
                       | Some(bb,d) => assign_loc_Effect (snd x) bb Int.zero b z
                       end
        | _ => fun b z => false
     end
  | _,_ => fun b z => false
 end.

Theorem store_params_correct_eff:
  forall le mu lo hi te tlo thi e m params args m',
  bind_parameters e m params args m' ->
  forall tm tle targs,
  list_norepet (var_names params) ->
  list_forall2 val_casted args (map snd params) ->
  val_list_inject (restrict (as_inj mu) (vis mu)) args targs ->
  match_envs mu e le m lo hi te tle tlo thi ->
  Mem.inject (as_inj mu) m tm ->
  (forall id, In id (var_names params) -> le!id = None) ->
  forall (WD: SM_wd mu) (SMV: sm_valid mu m tm) (RC:REACH_closed m (vis mu)),
  exists tm',
     bind_parameters te tm params targs tm'
  /\ Mem.inject (as_inj mu) m' tm'
  /\ match_envs mu e le m' lo hi te tle tlo thi
  /\ Mem.nextblock tm' = Mem.nextblock tm
  /\ sm_valid mu m' tm' 
  /\ REACH_closed m' (vis mu) 
  /\ (forall bb z, bind_parameters_effect e mu params targs bb z = true
                   -> exists b d, local_of mu b = Some(bb,d)).
Proof.
  induction 1; simpl; intros until targs; 
    intros NOREPET CASTED VINJ MENV MINJ (*TLE*) LE WD SMV RC.
  (* base case *)
  inv VINJ. (*exists tle1;*) exists tm; eexists. constructor.
  split. auto. 
  split. apply match_envs_temps_exten with tle; auto. intuition.
  (* inductive case *)
  inv NOREPET. inv CASTED. inv VINJ.
  exploit me_vars; eauto. instantiate (1 := id); intros MV.

  (* still in memory *)
  inv MV; try congruence. rewrite ENV in H; inv H.
  exploit (assign_loc_inject (as_inj mu)); try eassumption.
       econstructor. eapply local_in_all; eassumption.
         rewrite Int.add_zero. reflexivity. 
        eapply val_inject_incr; try eassumption. 
          apply restrict_incr.           
  intros [tm1 [A [B C]]].
  assert (SMV1: sm_valid mu m1 tm1).
     red. split; intros.
         apply assign_loc_forward in H0. apply H0. apply SMV. trivial.
         apply assign_loc_forward in A. apply A. apply SMV. trivial.     
  exploit IHbind_parameters. eauto. eauto. eauto.
  instantiate (1 := (*PTree.set id v'*) tle).
  (*apply match_envs_change_temp.*)
  eapply match_envs_intern_invariant; eauto. apply intern_incr_refl.
  eapply B. auto. auto. auto.
  (*REACH_closed m1 (vis mu)*)
      assert (MinjR:  Mem.inject (restrict (as_inj mu) (vis mu)) m tm).
           eapply inject_restrict; try eassumption.
      clear IHbind_parameters. 
      inv H0.
          (*by_value*)
             inv H2. 
             eapply REACH_Store; try eassumption.
               unfold vis. destruct (local_DomRng _ WD _ _ _ MAPPED).
                 rewrite H0; intuition.
               intros. rewrite getBlocksD, getBlocksD_nil in H0.
                       inv H6; try inv H0. rewrite H8. rewrite orb_false_r in H8.
                       destruct (eq_block b1 b'0); subst.
                         destruct (restrictD_Some _ _ _ _ _ H2); trivial.
                       inv H8.
          (*by_copy*)
             eapply REACH_Storebytes; try eassumption.
               unfold vis. destruct (local_DomRng _ WD _ _ _ MAPPED).
                 rewrite H0; intuition.
             intros bb off n Hbb. inv H6.
             destruct (Mem.loadbytes_inject _ _ _ _ _ _ _ _ _ MinjR H11 H14)
                as [bytes2 [LoadBytes2 MapBytes]].
             clear - Hbb MapBytes.
               induction MapBytes; inv Hbb.
               inv H. apply (restrictD_Some _ _ _ _ _ H4).
               apply (IHMapBytes H0).
  intros [tm' [EFF1 [U [V [X [Y [Z SMV2]]]]]]].
  (*exists tle;*) exists tm'; eexists. econstructor; eauto.
  rewrite ENV; simpl.
  specialize (local_in_all _ WD _ _ _ MAPPED); intros AI.
  rewrite AI.
  assert (HH: forall bb z, bind_parameters_effect e mu params vl' bb z
        || assign_loc_Effect ty b' Int.zero bb z = true -> 
        exists b d, local_of mu b = Some (bb, d)).
  { intros. apply orb_true_iff in H; destruct H.
    specialize (SMV2 _ _ H). auto.
    unfold assign_loc_Effect in H.
    destruct (eq_block bb b'); subst; simpl in *.
    solve[exists b, 0; trivial].
    inv A; rewrite H2 in H. 
    assert (bb = b'). 
    { rewrite !andb_true_iff in H. destruct H as [[? ?] ?]. 
      unfold eq_block in H. destruct (peq b' bb). subst; auto. simpl in H; congruence. }
    subst. elimtype False; auto.
    assert (bb = b'). 
    { rewrite !andb_true_iff in H. destruct H as [[? ?] ?]. 
      unfold eq_block in H. destruct (peq bb b'). subst; auto. simpl in H; congruence. }
    subst. elimtype False; auto. }
  intuition.   
  rewrite (assign_loc_nextblock _ _ _ _ _ _ A) in X. auto.
Qed.

Lemma bind_parameters_load:
  forall e chunk b ofs,
  (forall id b' ty, e!id = Some(b', ty) -> b <> b') ->
  forall m params args m',
  bind_parameters e m params args m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2.
  auto.
  rewrite IHbind_parameters.
  assert (b <> b0) by eauto.
  inv H1. 
  simpl in H5. eapply Mem.load_store_other; eauto.
  eapply Mem.load_storebytes_other; eauto.
Qed.

(** Freeing of local variables *)

Lemma free_blocks_of_env_perm_1:
  forall m e m' id b ty ofs k p,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.perm m' b ofs k p ->
  0 <= ofs < sizeof ty ->
  False.
Proof.
  intros. exploit Mem.perm_free_list; eauto. intros [A B].
  apply B with 0 (sizeof ty); auto.
  unfold blocks_of_env. change (b, 0, sizeof ty) with (block_of_binding (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma free_list_perm':
  forall b lo hi l m m',
  Mem.free_list m l = Some m' ->
  In (b, lo, hi) l ->
  Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  destruct a as [[b1 lo1] hi1]. 
  destruct (Mem.free m b1 lo1 hi1) as [m1|] eqn:?; try discriminate.
  destruct H0. inv H0. eapply Mem.free_range_perm; eauto. 
  red; intros. eapply Mem.perm_free_3; eauto. eapply IHl; eauto. 
Qed.

Lemma free_blocks_of_env_perm_2:
  forall m e m' id b ty,
  Mem.free_list m (blocks_of_env e) = Some m' ->
  e!id = Some(b, ty) ->
  Mem.range_perm m b 0 (sizeof ty) Cur Freeable.
Proof.
  intros. eapply free_list_perm'; eauto. 
  unfold blocks_of_env. change (b, 0, sizeof ty) with (block_of_binding (id, (b, ty))).
  apply in_map. apply PTree.elements_correct. auto.
Qed.

Lemma can_free_list:
  forall l m,
  (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable) ->
  list_norepet (map (fun b_lo_hi => fst(fst b_lo_hi)) l) ->
  exists m', Mem.free_list m l = Some m'.
Proof.
  induction l; simpl; intros.
  exists m; auto.
  destruct a as [[b lo] hi]. simpl in H0. inv H0. 
  destruct (Mem.range_perm_free m b lo hi) as [m1 A]; auto. 
  rewrite A. apply IHl; auto. intros. 
  red; intros. eapply Mem.perm_free_1; eauto. 
  left; red; intros. subst b0. elim H3.
  set (F := fun b_lo_hi : block * Z * Z => fst (fst b_lo_hi)).
  change b with (F (b,lo0,hi0)). eapply in_map; auto.
  eapply H; eauto. 
Qed.

Lemma free_list_right_inject:
  forall j m1 l m2 m2',
  Mem.inject j m1 m2 ->
  Mem.free_list m2 l = Some m2' ->
  (forall b1 b2 delta lo hi ofs k p,
     j b1 = Some(b2, delta) -> In (b2, lo, hi) l ->
     Mem.perm m1 b1 ofs k p -> lo <= ofs + delta < hi -> False) ->
  Mem.inject j m1 m2'.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a as [[b lo] hi]. destruct (Mem.free m2 b lo hi) as [m21|] eqn:?; try discriminate.
  eapply IHl with (m2 := m21); eauto.
  eapply Mem.free_right_inject; eauto. 
Qed.

Theorem match_envs_free_blocks:
  forall mu e le m lo hi te tle tlo thi m' tm,
  match_envs mu e le m lo hi te tle tlo thi ->
  Mem.inject (as_inj mu) m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  exists tm',
     Mem.free_list tm (blocks_of_env te) = Some tm'
  /\ Mem.inject (as_inj mu) m' tm'.
Proof.
  intros.
  assert (exists tm', Mem.free_list tm (blocks_of_env te) = Some tm').
    apply can_free_list.
    intros. unfold blocks_of_env in H2.
    exploit list_in_map_inv; eauto. intros [[id [b' ty]] [EQ IN]].
    simpl in EQ; inv EQ. 
    exploit me_mapped; eauto. eapply PTree.elements_complete; eauto. 
    intros [b [A B]]. 
    change 0 with (0 + 0). replace (sizeof ty) with (sizeof ty + 0) by omega.
    destruct (restrictD_Some _ _ _ _ _ A). 
    eapply Mem.range_perm_inject; eauto. 
    eapply free_blocks_of_env_perm_2; eauto.
    (* no repetitions *)
    set (F := fun id => match te!id with Some(b, ty) => b | None => xH end).
    replace (map (fun b_lo_hi : block * Z * Z => fst (fst b_lo_hi)) (blocks_of_env te))
       with (map F (map (fun x => fst x) (PTree.elements te))).
    apply list_map_norepet. apply PTree.elements_keys_norepet. 
    intros. 
    exploit list_in_map_inv. eexact H2. intros [[id1 [b1' ty1]] [EQ1 IN1]].
    exploit list_in_map_inv. eexact H3. intros [[id2 [b2' ty2]] [EQ2 IN2]].
    simpl in *. subst x y.
    assert (te!id1 = Some(b1', ty1)) by (apply PTree.elements_complete; auto).
    assert (te!id2 = Some(b2', ty2)) by (apply PTree.elements_complete; auto).
    exploit me_mapped. eauto. eexact H5. intros [b1 [P1 Q1]].
      destruct (restrictD_Some _ _ _ _ _ P1) as [PP1 Vis1]; clear P1; rename PP1 into P1.
    exploit me_mapped. eauto. eexact H6. intros [b2 [P2 Q2]].
      destruct (restrictD_Some _ _ _ _ _ P2) as [PP2 Vis2]; clear P2; rename PP2 into P2.
    assert (b1 <> b2) by (eapply me_inj; eauto). 
    exploit Mem.mi_no_overlap; eauto. 
    instantiate (1 := 0). apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply free_blocks_of_env_perm_2; eauto. generalize (sizeof_pos ty1); omega.
    instantiate (1 := 0). apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
    eapply free_blocks_of_env_perm_2; eauto. generalize (sizeof_pos ty2); omega.
    intros [A | A]; try omegaContradiction. 
    unfold F. rewrite H5; rewrite H6. auto.
    unfold blocks_of_env. repeat rewrite list_map_compose. apply list_map_exten; intros. 
    unfold F. destruct x as [id [b ty]]. simpl. erewrite PTree.elements_complete; eauto. auto.
  destruct H2 as [tm' FREE].
(*  assert (MinjR:  Mem.inject (restrict (as_inj mu) (vis mu)) m tm).
           eapply inject_restrict; try eassumption.*)
  exists tm'; split; auto.
  eapply free_list_right_inject; eauto. 
  eapply Mem.free_list_left_inject; eauto. 
  intros. unfold blocks_of_env in H3. exploit list_in_map_inv; eauto. 
  intros [[id [b' ty]] [EQ IN]]. simpl in EQ. inv EQ.
  exploit PTree.elements_complete; try eassumption. intros TESome.
  exploit me_mapped; try eassumption. intros [b [Rbb Ebb]].
  exploit me_flat; eauto. 
  intros [P Q]. subst delta. eapply free_blocks_of_env_perm_1 with (m := m); eauto.
  omega. 
Qed.

(** Matching global environments *)

Inductive match_globalenvs (f: meminj) (bound: block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta gv (GV: Genv.find_var_info ge b2 = Some gv),
               f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma match_globalenvs_preserves_globals:
  forall f,
  (exists bound, match_globalenvs f bound) ->
  meminj_preserves_globals ge f.
Proof.
  intros. destruct H as [bound MG]. inv MG.
  split; intros. eauto. split; intros. eauto. symmetry. eapply IMAGE; eauto.
Qed. 

(** Evaluation of expressions *)

Section EVAL_EXPR.

Variables e te: env.
Variables le tle: temp_env.
Variables m tm: mem.
Variable mu: SM_Injection. 
Variables lo hi tlo thi: block.
Hypothesis MATCH: match_envs mu e le m lo hi te tle tlo thi.
Hypothesis MEMINJ: Mem.inject (as_inj mu) m tm.
Hypothesis GLOB: exists bound, match_globalenvs (restrict (as_inj mu) (vis mu)) bound.
Hypothesis WD: SM_wd mu.

Lemma deref_loc_inject:
  forall ty loc ofs v loc' ofs',
  deref_loc ty m loc ofs v ->
  val_inject (as_inj mu) (Vptr loc ofs) (Vptr loc' ofs') ->
  exists tv, deref_loc ty tm loc' ofs' tv /\ val_inject (as_inj mu) v tv.
Proof.
  intros. inv H. 
  (* by value *)
  exploit Mem.loadv_inject; eauto. intros [tv [A B]]. 
  exists tv; split; auto. eapply deref_loc_value; eauto.
  (* by reference *)
  exists (Vptr loc' ofs'); split; auto. eapply deref_loc_reference; eauto.
  (* by copy *)
  exists (Vptr loc' ofs'); split; auto. eapply deref_loc_copy; eauto.
Qed.

Lemma eval_simpl_expr:
  forall a v,
  eval_expr ge e le m a v ->
  exists tv, eval_expr tge te tle tm a tv /\ val_inject (as_inj mu) v tv

with eval_simpl_lvalue:
  forall a b ofs,
  eval_lvalue ge e le m a b ofs ->
  exists b', exists ofs', eval_lvalue tge te tle tm a b' ofs' 
                          /\ val_inject (as_inj mu) (Vptr b ofs) (Vptr b' ofs').

Proof.
  destruct 1; simpl; intros.
(* const *)
  exists (Vint i); split; auto. constructor.
  exists (Vfloat f); split; auto. constructor.
  exists (Vlong i); split; auto. constructor.
(* tempvar *)
  exploit me_temps; eauto. intros [tv [A B]].
  exists tv; split; auto. constructor; auto.
  eapply val_inject_incr; try eassumption.
    eapply restrict_incr.
(* addrof *)
  exploit eval_simpl_lvalue; eauto. 
  intros [b' [ofs' [A B]]]. 
  exists (Vptr b' ofs'); split; auto. constructor; auto. 
(* unop *)
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_unary_operation_inject; eauto. intros [tv [C D]].
  exists tv; split; auto. econstructor; eauto. 
(* binop *)
  exploit eval_simpl_expr. eexact H. intros [tv1 [A B]].
  exploit eval_simpl_expr. eexact H0. intros [tv2 [C D]].
  exploit sem_binary_operation_inject; eauto. intros [tv [E F]].
  exists tv; split; auto. econstructor; eauto. repeat rewrite typeof_simpl_expr; auto.
(* cast *)
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_cast_inject; eauto. intros [tv2 [C D]].
  exists tv2; split; auto. econstructor. eauto. auto.
(* rval *)
  exploit eval_simpl_lvalue; eauto. intros [loc' [ofs' [A B]]].
  exploit deref_loc_inject; eauto. intros [tv [C D]].
  exists tv; split; auto. econstructor. eexact A. auto. 

(* lvalues *)
  destruct 1; simpl; intros.
(* local var *)
  exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
  rewrite ENV in H; inv H.
  eexists; exists Int.zero; split.
  apply eval_Evar_local; eauto.
  econstructor; eauto. eapply local_in_all; try eassumption.
  rewrite Int.add_zero; trivial.
(* global var *)
  exploit me_vars; eauto. instantiate (1 := id). intros MV. inv MV; try congruence.
  exists l; exists Int.zero; split.
  apply eval_Evar_global. auto. rewrite <- H0. apply symbols_preserved. 
  eapply type_of_global_preserved; eauto. 
  destruct GLOB as [bound GLOB1]. inv GLOB1.
  destruct (restrictD_Some _ _ _ _ _ (DOMAIN _ (SYMBOLS _ _ H0))).
  econstructor; eauto. 
(* deref *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]]. 
  inversion B. subst. 
  econstructor; econstructor; split; eauto. econstructor; eauto. 
(* field struct *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]]. 
  inversion B. subst. 
  econstructor; econstructor; split. 
  eapply eval_Efield_struct; eauto. 
  econstructor; eauto. repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
(* field union *)
  exploit eval_simpl_expr; eauto. intros [tv [A B]]. 
  inversion B. subst. 
  econstructor; econstructor; split. 
  eapply eval_Efield_union; eauto. eauto.
Qed.

Lemma eval_simpl_exprlist:
  forall al tyl vl,
  eval_exprlist ge e le m al tyl vl ->
  val_casted_list vl tyl /\
  exists tvl,
     eval_exprlist tge te tle tm al tyl tvl
  /\ val_list_inject (as_inj mu) vl tvl.
Proof.
  induction 1; simpl; intros.
  split. constructor. econstructor; split. constructor. auto.
  exploit eval_simpl_expr; eauto. intros [tv1 [A B]].
  exploit sem_cast_inject; eauto. intros [tv2 [C D]]. 
  destruct IHeval_exprlist as [E [tvl [F G]]].
  split. constructor; auto. eapply cast_val_is_casted; eauto.  
  exists (tv2 :: tvl); split. econstructor; eauto.
  auto.
Qed.

End EVAL_EXPR.

(** Matching continuations *)

Inductive match_cont mu : cont -> cont -> mem -> block -> block -> Prop :=
  | match_Kstop: forall m bound tbound hi,
      match_globalenvs (restrict (as_inj mu) (vis mu)) hi -> Ple hi bound -> Ple hi tbound ->
      match_cont mu Kstop Kstop m bound tbound
  | match_Kseq: forall s k ts tk m bound tbound,
      s = ts ->
      match_cont mu k tk m bound tbound ->
      match_cont mu (Kseq s k) (Kseq ts tk) m bound tbound
  | match_Kloop1: forall s1 s2 k ts1 ts2 tk m bound tbound,
      s1 = ts1 ->
      s2 = ts2 ->
      match_cont mu k tk m bound tbound ->
      match_cont mu (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk) m bound tbound
  | match_Kloop2: forall s1 s2 k ts1 ts2 tk m bound tbound,
      s1 = ts1 ->
      s2 = ts2 ->
      match_cont mu k tk m bound tbound ->
      match_cont mu (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk) m bound tbound
  | match_Kswitch: forall k tk m bound tbound,
      match_cont mu k tk m bound tbound ->
      match_cont mu (Kswitch k) (Kswitch tk) m bound tbound
  | match_Kcall: forall optid fn e le k tfn te tle tk m hi thi lo tlo bound tbound
      (DISJ: list_disjoint (var_names (fn_params fn)) (var_names (fn_temps fn))),
      fn = tfn ->
      match_envs mu e le m lo hi te tle tlo thi ->
      match_cont mu k tk m lo tlo ->
      Ple hi bound -> Ple thi tbound ->
      match_cont mu (Kcall optid fn e le k)
                    (Kcall optid tfn te tle tk) m bound tbound.

Lemma match_cont_match_globalenvs mu k tk m bound tbound : 
  forall (MC: match_cont mu k tk m bound tbound),
  exists hi, match_globalenvs (restrict (as_inj mu) (vis mu)) hi /\ Ple hi bound.
Proof. 
  intros. induction MC; eauto. 
  destruct IHMC as [h [MG LE]].
  exists h; split; trivial. inv H0. xomega.
Qed.

(** Invariance property by change of memory and injection *)

Lemma match_cont_intern_invariant:
  forall mu' m' mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  (forall b chunk v,
    as_inj mu b = None -> Plt b bound -> 
    Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  intern_incr mu mu' ->
  (forall b, Plt b bound -> as_inj mu' b = as_inj mu b) ->
  (forall b b' delta, as_inj mu' b = Some(b', delta) -> 
                      Plt b' tbound -> as_inj mu' b = as_inj mu b) ->
  forall (WD: SM_wd mu) (WD': SM_wd mu'),
  match_cont mu' k tk m' bound tbound.
Proof.
  induction 1; intros LOAD INCR INJ1 INJ2; econstructor; eauto.
(* globalenvs *)
  inv H. constructor; intros; eauto.
    specialize (DOMAIN _ H).
    eapply intern_incr_restrict; try eassumption.
  assert (restrict (as_inj mu) (vis mu) b1 = Some (b2, delta)). 
    destruct (restrictD_Some _ _ _ _ _ H); clear H.
    rewrite (INJ2 _ _ _ H3) in H3.
     apply (intern_incr_vis_inv _ _ WD WD' INCR _ _ _ H3) in H4.
     apply restrictI_Some; trivial. xomega.
  eapply IMAGE; eauto.
(* call *)
  eapply match_envs_intern_invariant; eauto. 
  intros. apply LOAD; auto. xomega.
  (*intros. apply INJ1. auto; xomega.*)
  intros. eapply INJ2; eauto; xomega.
  eapply IHmatch_cont; eauto. 
  intros; apply LOAD; auto. inv H0; xomega.
  intros; apply INJ1. inv H0; xomega.
  intros; eapply INJ2; eauto. inv H0; xomega.
Qed.

Lemma match_cont_extern_invariantPriv: (*Obsolete *)
  forall mu' m' mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  (forall b chunk v,
    privBlocksSrc mu b = true -> Plt b bound -> 
    Mem.load chunk m b 0 = Some v -> Mem.load chunk m' b 0 = Some v) ->
  extern_incr mu mu' ->
  (*(forall b, Plt b bound -> as_inj mu' b = as_inj mu b) ->
  (forall b b' delta, as_inj mu' b = Some(b', delta) -> Plt b' tbound -> 
                      as_inj mu' b = as_inj mu b) ->*)
 forall (GSEP : globals_separate tge mu mu')
        (WD: SM_wd mu) (WD': SM_wd mu'),
  match_cont mu' k tk m' bound tbound.
Proof.
  induction 1; intros LOAD INCR SEP; econstructor; eauto.
(* globalenvs *)
  inv H. constructor; intros; eauto.
    specialize (DOMAIN _ H).
    eapply extern_incr_restrict; try eassumption.
  assert (restrict (as_inj mu) (vis mu) b1 = Some (b2, delta)).
    destruct (restrictD_Some _ _ _ _ _ H); clear H.
    rewrite <- (extern_incr_vis _ _ INCR) in H4.
    remember (as_inj mu b1) as d; apply eq_sym in Heqd.
    destruct d.
      destruct p.
      rewrite (extern_incr_as_inj _ _ INCR WD' _ _ _ Heqd) in H3; 
          inv H3. apply restrictI_Some; trivial.
    specialize (SEP _ _ _ Heqd H3).
      unfold isGlobalBlock, genv2blocksBool in SEP. simpl in SEP.
      rewrite varinfo_preserved, GV, orb_true_r in SEP; inv SEP. 
  eapply IMAGE; eauto.
(* call *)
  eapply match_envs_extern_invariantPriv; eauto. 
  intros. apply LOAD; auto. xomega.

  eapply IHmatch_cont; eauto. 
  intros; apply LOAD; auto. inv H0; xomega.
  Qed.


(** Invariance by assignment to location "above" *)

Lemma match_cont_intern_assign_loc:
  forall mu k tk m bound tbound ty loc ofs v m',
  match_cont mu k tk m bound tbound ->
  assign_loc ty m loc ofs v m' ->
  Ple bound loc ->
  forall (WD: SM_wd mu),
  match_cont mu k tk m' bound tbound.
Proof.
  intros. assert (MU:= intern_incr_refl mu). eapply match_cont_intern_invariant; eauto.
  intros. rewrite <- H4. inv H0.
  (* scalar *)
  simpl in H6. eapply Mem.load_store_other; eauto. left. unfold block; xomega. 
  (* block copy *)
  eapply Mem.load_storebytes_other; eauto. left. unfold block; xomega.  
Qed.

(** Invariance by external calls *)


Lemma match_cont_extcallPriv:
  forall mu k tk m bound tbound tm mu' m',
  match_cont mu k tk m bound tbound ->
  Mem.unchanged_on (fun b ofs => privBlocksSrc mu b = true) m m' ->
  extern_incr mu mu' ->
  globals_separate (Genv.globalenv prog) mu mu' ->
  (*sm_inject_separated mu mu' m tm ->*)
  Ple bound (Mem.nextblock m) -> Ple tbound (Mem.nextblock tm) ->
  forall (WD: SM_wd mu) (WD': SM_wd mu') (SMV: sm_valid mu m tm),
  match_cont mu' k tk m' bound tbound.
Proof.
  
  intros. 
  eapply match_cont_extern_invariantPriv; eauto. 
  intros. eapply Mem.load_unchanged_on; eauto.
 (* intros. (*destruct H2 as [H2 [H2Dom H2Tgt]].*)
  eapply match_cont_extern_invariantPriv; eauto. 
  intros. eapply Mem.load_unchanged_on; eauto. 
  intros. destruct (as_inj mu b) as [[b' delta] | ] eqn:?.
     eapply extern_incr_as_inj; eassumption.
  destruct SMV as [SMVD _].
    destruct (as_inj mu' b) as [[b' delta] | ] eqn:?; auto.
    exploit as_inj_DomRng; try eassumption. intros [D' T'] .
    exploit H2; eauto. unfold Mem.valid_block in H2Dom. intros [A B]. 
      specialize (H2Dom _ A D'). xomegaContradiction.
  intros. destruct (as_inj mu b) as [[b'' delta''] | ] eqn:?.
      eapply extern_incr_as_inj; eassumption.
    exploit as_inj_DomRng; try eassumption. intros [D' T'].
    exploit H2; eauto. intros [A B].  
    unfold Mem.valid_block in H2Tgt. specialize (H2Tgt _  B T'). xomegaContradiction.*)
Qed.

(** Invariance by change of bounds *)

Lemma match_cont_incr_bounds:
  forall mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  forall bound' tbound',
  Ple bound bound' -> Ple tbound tbound' ->
  match_cont mu k tk m bound' tbound'.
Proof.
  induction 1; intros; econstructor; eauto; xomega.
Qed.

(** [match_cont] and call continuations. *)

Lemma match_cont_change_cenv:
  forall mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  is_call_cont k ->
  match_cont mu k tk m bound tbound.
Proof.
  intros. inv H; simpl in H0; try contradiction; econstructor; eauto.
Qed.

Lemma match_cont_is_call_cont:
  forall mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  is_call_cont k ->
  is_call_cont tk.
Proof.
  intros. inv H; auto. 
Qed.

Lemma match_cont_call_cont:
  forall mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  match_cont mu (call_cont k) (call_cont tk) m bound tbound.
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

(** [match_cont] and freeing of environment blocks *)

Remark free_list_nextblock:
  forall l m m',
  Mem.free_list m l = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.nextblock m1). eauto. eapply Mem.nextblock_free; eauto. 
Qed.

Remark free_list_load:
  forall chunk b' l m m',
  Mem.free_list m l = Some m' ->
  (forall b lo hi, In (b, lo, hi) l -> Plt b' b) ->
  Mem.load chunk m' b' 0 = Mem.load chunk m b' 0.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  destruct a. destruct p. destruct (Mem.free m b z0 z) as [m1|] eqn:?; try discriminate.
  transitivity (Mem.load chunk m1 b' 0). eauto. 
  eapply Mem.load_free. eauto. left. assert (Plt b' b) by eauto. unfold block; xomega.
Qed.

Lemma match_cont_free_env:
  forall mu e le m lo hi te tle tm tlo thi k tk m' tm',
  match_envs mu e le m lo hi te tle tlo thi ->
  match_cont mu k tk m lo tlo ->
  Ple hi (Mem.nextblock m) ->
  Ple thi (Mem.nextblock tm) ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  Mem.free_list tm (blocks_of_env te) = Some tm' ->
  forall (WD: SM_wd mu),
  match_cont mu k tk m' (Mem.nextblock m') (Mem.nextblock tm').
Proof.
  intros. apply match_cont_incr_bounds with lo tlo.
  eapply match_cont_intern_invariant; eauto. 
  intros. rewrite <- H7. eapply free_list_load; eauto. 
  unfold blocks_of_env; intros. exploit list_in_map_inv; eauto. 
  intros [[id [b1 ty]] [P Q]]. simpl in P. inv P. 
  exploit me_range; eauto. eapply PTree.elements_complete; eauto. xomega.
  apply intern_incr_refl.
  rewrite (free_list_nextblock _ _ _ H3). inv H; xomega.
  rewrite (free_list_nextblock _ _ _ H4). inv H; xomega.
Qed.

(** Matching of global environments *)

Lemma match_cont_globalenv:
  forall mu k tk m bound tbound,
  match_cont mu k tk m bound tbound ->
  exists bound, match_globalenvs (restrict (as_inj mu) (vis mu)) bound.
Proof.
  induction 1; auto. exists hi; auto. 
Qed.

Hint Resolve match_cont_globalenv: compat.

Lemma match_cont_find_funct:
  forall mu k tk m bound tbound vf fd tvf,
  match_cont mu k tk m bound tbound ->
  Genv.find_funct ge vf = Some fd ->
  val_inject (as_inj mu) vf tvf ->
  exists tfd, Genv.find_funct tge tvf = Some tfd /\ fd = tfd.
Proof.
  intros. exploit match_cont_globalenv; eauto. intros [bound1 MG]. destruct MG.
  inv H1; simpl in H0; try discriminate. destruct (Int.eq_dec ofs1 Int.zero); try discriminate.
  subst ofs1.
  assert (as_inj mu b1 = Some(b1, 0)).
    eapply restrictD_Some. 
    apply DOMAIN. eapply FUNCTIONS; eauto. 
  rewrite H1 in H2; inv H2.
  rewrite Int.add_zero. simpl. rewrite dec_eq_true. 
  exists fd; split; auto.
Qed.

Lemma match_var_replace_locals mu e m te tle id: forall
        (MV: match_var mu e m te tle id) 
        PS PT,
      match_var (replace_locals mu PS PT) e m te tle id.
Proof. intros.
inv MV.
  eapply match_var_not_lifted; try eassumption.
    rewrite replace_locals_local; trivial.
  eapply match_var_not_local; try eassumption.
Qed.

Lemma match_envs_replace_locals mu e le m lo hi te tle tlo thi: forall
       (ME: match_envs mu e le m lo hi te tle tlo thi) PS PT,
        match_envs (replace_locals mu PS PT) e le m lo hi te tle tlo thi.
Proof. intros.
inv ME; econstructor; try eassumption.
  intros. specialize (me_vars0 id).
    eapply match_var_replace_locals; eassumption.
  rewrite replace_locals_as_inj, replace_locals_vis; trivial.
  rewrite replace_locals_locBlocksSrc; trivial.
  rewrite replace_locals_locBlocksTgt; trivial.
  rewrite replace_locals_as_inj, replace_locals_vis; trivial.
  rewrite replace_locals_as_inj; trivial.
Qed. 

Lemma match_cont_replace_locals  mu k tk m1 bound tbound : forall
      (MCONT : match_cont mu k tk m1 bound tbound) PS PT,
      match_cont (replace_locals mu PS PT) k tk m1 bound tbound.
Proof. intros.
  induction MCONT; econstructor; try eassumption.
    rewrite replace_locals_as_inj, replace_locals_vis; trivial.
    apply match_envs_replace_locals; trivial.
Qed.
    
Lemma match_var_replace_externsSpecific mu e m te tle id ret1 ret2 m1' m2': forall
        (MV: match_var mu e m te tle id) (WD: SM_wd mu),
match_var (replace_externs mu 
   (fun b : block =>
      DomSrc mu b &&
      (negb (locBlocksSrc mu b) &&
       REACH m1' (exportedSrc mu (ret1 :: nil)) b))
   (fun b : block =>
      DomTgt mu b &&
      (negb (locBlocksTgt mu b) &&
       REACH m2' (exportedTgt mu (ret2 :: nil)) b))) e m te tle id.
Proof. intros.
inv MV.
  eapply match_var_not_lifted; try eassumption.
    rewrite replace_externs_local; trivial.
  eapply match_var_not_local; try eassumption.
Qed.

Lemma match_var_replace_externs mu e m te tle id: forall
        (MV: match_var mu e m te tle id) FS FT 
        (HFS: forall b, vis mu b = true -> locBlocksSrc mu b || FS b = true) (WD: SM_wd mu),
match_var (replace_externs mu FS FT) e m te tle id.
Proof. intros.
inv MV.
  eapply match_var_not_lifted; try eassumption.
    rewrite replace_externs_local; trivial.
  eapply match_var_not_local; try eassumption.
Qed.

Lemma match_envs_replace_externs mu e le m lo hi te tle tlo thi: forall
        (ME: match_envs mu e le m lo hi te tle tlo thi) FS FT
        (HFS: forall b, vis mu b = true -> locBlocksSrc mu b || FS b = true) (WD: SM_wd mu),
      match_envs (replace_externs mu FS FT) e le m lo hi te tle tlo thi.
Proof. intros.
inv ME; econstructor; try eassumption.
  intros. specialize (me_vars0 id).
    eapply match_var_replace_externs; eassumption.
  rewrite replace_externs_as_inj, replace_externs_vis.
    intros. destruct (me_temps0 _ _ H) as [tv [TTLE VInj]]; clear H.
    exists tv; split; trivial.
    eapply val_inject_incr; try eassumption.
    red; intros. destruct (restrictD_Some _ _ _ _ _ H); clear H.
    eapply restrictI_Some; trivial. apply HFS; trivial. 
  rewrite replace_externs_locBlocksSrc; trivial.
  rewrite replace_externs_locBlocksTgt; trivial.
  rewrite replace_externs_as_inj, replace_externs_vis.
    intros. destruct (me_mapped0 _ _ _ H) as [b [Rb Eb]]; clear H.
    exists b; split; trivial.
    destruct (restrictD_Some _ _ _ _ _ Rb); clear Rb.
    eapply restrictI_Some; trivial. apply HFS; trivial. 
  rewrite replace_externs_as_inj. assumption.
Qed.  

Lemma match_cont_replace_externs mu k tk m1 bound tbound : forall
        (MCONT : match_cont mu k tk m1 bound tbound) FS FT
        (HFS: forall b, vis mu b = true -> locBlocksSrc mu b || FS b = true) 
        (PGmu : meminj_preserves_globals (Genv.globalenv prog) (as_inj mu))
        (WD: SM_wd mu),
      match_cont (replace_externs mu FS FT) k tk m1 bound tbound.
Proof. intros.
  induction MCONT; econstructor; try eassumption.
    rewrite replace_externs_as_inj, replace_externs_vis; trivial.
    inv H; econstructor; try eassumption.
    intros. specialize (DOMAIN _ H).
     destruct (restrictD_Some _ _ _ _ _ DOMAIN).
     apply restrictI_Some; trivial.
     apply HFS. trivial.
    intros. destruct (restrictD_Some _ _ _ _ _ H); clear H.
           symmetry. eapply PGmu; eassumption.
  eapply match_envs_replace_externs; try eassumption.
Qed.

(** Relating execution states *)

Inductive match_states mu: CL_core -> mem -> CL_core -> mem -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk te tle tm lo hi tlo thi
        (TRF: f = tf)
        (TRS: s = ts)
        (MENV: match_envs mu e le m lo hi te tle tlo thi)
        (MCONT: match_cont mu k tk m lo tlo)
        (MINJ: Mem.inject (as_inj mu) m tm)
        (BOUND: Ple hi (Mem.nextblock m))
        (TBOUND: Ple thi (Mem.nextblock tm))
        (DISJ: list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))),
      match_states mu (CL_State f s k e le) m
                      (CL_State tf ts tk te tle) tm
  | match_call_state:
      forall fd vargs k m tfd tvargs tk tm targs tres
        (TRFD: fd = tfd)
        (MCONT: match_cont mu k tk m (Mem.nextblock m) (Mem.nextblock tm))
        (MINJ: Mem.inject (as_inj mu) m tm)
        (AINJ: val_list_inject (restrict (as_inj mu) (vis mu)) vargs tvargs)
        (FUNTY: type_of_fundef fd = Tfunction targs tres)
        (ANORM: val_casted_list vargs targs)
        (DISJ: forall f, fd = Internal f -> 
               list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))),
      match_states mu (CL_Callstate fd vargs k) m
                      (CL_Callstate tfd tvargs tk) tm
  | match_return_state:
      forall v k m tv tk tm 
        (MCONT: match_cont mu k tk m (Mem.nextblock m) (Mem.nextblock tm))
        (MINJ: Mem.inject (as_inj mu) m tm)
        (RINJ: val_inject (restrict (as_inj mu) (vis mu)) v tv),
      match_states mu (CL_Returnstate v k) m
                      (CL_Returnstate tv tk) tm.

Definition MATCH' (d:CL_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu.

Definition MATCH d mu c1 m1 c2 m2:Prop :=
  MATCH' d mu c1 m1 c2 m2 /\
  (mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2).

Lemma MATCH_wd: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma match_var_restrict mu e m te tle id: forall
      (MV: match_var mu e m te tle id) X
      (HX : forall b : block, vis mu b = true -> X b = true)
      (WD: SM_wd mu),
      match_var (restrict_sm mu X) e m te tle id.
Proof. 
  intros. inv MV.
  eapply match_var_not_lifted; try eassumption.
    rewrite restrict_sm_local'; eassumption.
  eapply match_var_not_local; try eassumption. 
Qed.

Lemma match_envs_restrict mu e le m lo hi te tle tlo thi: forall
        (ME : match_envs mu e le m lo hi te tle tlo thi) X
        (HX : forall b : block, vis mu b = true -> X b = true)
        (WD : SM_wd mu),
      match_envs (restrict_sm mu X) e le m lo hi te tle tlo thi.
Proof. 
  intros. inv ME; econstructor; try eassumption.
  intros. eapply match_var_restrict; eauto.
  intros. 
    rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; try assumption.
    apply (me_temps0 _ _ H).
  rewrite restrict_sm_locBlocksSrc; trivial.
  rewrite restrict_sm_locBlocksTgt; trivial.
  intros.
    rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; try assumption.
    apply (me_mapped0 _ _ _ H).
  intros.
    rewrite restrict_sm_all in H0. 
    destruct (restrictD_Some _ _ _ _ _ H0).
    apply (me_flat0 _ _ _ _ _ H H1).
Qed.

Lemma match_cont_restrict mu k tk m1 lo tlo: forall
        (CONT : match_cont mu k tk m1 lo tlo) X
        (HX : forall b : block, vis mu b = true -> X b = true)
        (WD: SM_wd mu),
      match_cont (restrict_sm mu X) k tk m1 lo tlo.
Proof. intros.
  induction CONT;
  econstructor; try eassumption.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; eassumption.
    eapply match_envs_restrict; eassumption.
Qed.

Lemma match_states_restrict mu c1 m1 c2 m2: forall
        (MS:match_states mu c1 m1 c2 m2) X
        (RC: REACH_closed m1 X)
        (HX : forall b : block, vis mu b = true -> X b = true)
      (WD: SM_wd mu),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros. inv MS.
   econstructor; eauto.
     eapply match_envs_restrict; try eassumption.
     eapply match_cont_restrict; try eassumption.
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
   econstructor; eauto.
     intros. specialize MCONT.
       eapply match_cont_restrict; try eassumption.
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; assumption.
   econstructor; eauto.
     intros. specialize MCONT.
       eapply match_cont_restrict; try eassumption.
     rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption.
     rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; assumption.
Qed.

Lemma MATCH_restrict: forall d mu c1 m1 c2 m2 X
  (MC: MATCH d mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m1 X), 
  MATCH d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [[MS [RC [PG (*[GF*) [Glob [SMV WD]]]]] MRR].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split; trivial.
split.
  eapply match_states_restrict; eassumption.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
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
assumption.
Qed.

Lemma MATCH_valid: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
Proof. intros. eapply MC. Qed.

Lemma MATCH_PG: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2),
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

(** The simulation diagrams *)

Remark addr_taken_seq_of_labeled_statement:
  forall ls, addr_taken_stmt (seq_of_labeled_statement ls) = addr_taken_lblstmt ls.
Proof.
  induction ls; simpl; congruence.
Qed.

Section FIND_LABEL.
Variable mu: SM_Injection.
Variable cenv: compilenv.
Variable m: mem.
Variables bound tbound: block.
Variable lbl: ident.
Hypothesis WD: SM_wd mu.

Lemma simpl_find_label:
  forall s k tk,
  match_cont mu k tk m bound tbound ->
  match find_label lbl s k with
  | None =>
      find_label lbl s tk = None
  | Some(s', k') =>
      exists tk', 
         find_label lbl s tk = Some(s', tk')
      /\ match_cont mu k' tk' m bound tbound
  end

with simpl_find_label_ls:
  forall ls k tk,
  match_cont mu k tk m bound tbound ->
  match find_label_ls lbl ls k with
  | None =>
      find_label_ls lbl ls tk = None
  | Some(s', k') =>
      exists tk', 
         find_label_ls lbl ls tk = Some(s', tk')
      /\ match_cont mu k' tk' m bound tbound
  end.

Proof.
  induction s; simpl; intros until tk; intros MC; auto.
  (* seq *)
  { exploit (IHs1 (Kseq s2 k) (Kseq s2 tk)); eauto.
    constructor; auto.
  destruct (find_label lbl s1 (Kseq s2 k)) as [[s' k']|]. 
  intros [ts' [P Q]]. exists ts'. simpl. rewrite P. auto.
  intros E. simpl. rewrite E. eapply IHs2; eauto. }
  (* ifthenelse *)
  exploit (IHs1 k tk); eauto.
  destruct (find_label lbl s1 k) as [[s' k']|]. 
  intros [ts' [P Q]]. exists ts'. simpl. rewrite P. auto. 
  intros E. simpl. rewrite E. eapply IHs2; eauto.
  (* loop *)
  exploit (IHs1 (Kloop1 s1 s2 k) (Kloop1 s1 s2 tk)); eauto with compat.
    constructor; eauto with compat.
  destruct (find_label lbl s1 (Kloop1 s1 s2 k)) as [[s' k']|]. 
  intros [ts' [P Q]]. exists ts'. simpl. rewrite P. auto. 
  intros E. simpl; rewrite E. eapply IHs2; eauto with compat. econstructor; eauto with compat.
  (* switch *)
  eapply simpl_find_label_ls; eauto. constructor; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists tk; auto.
  eapply IHs; eauto.
  (* goto *)
  induction ls; simpl; intros.
  (* default *)
  apply simpl_find_label; auto. 
  (* case *)
  exploit (simpl_find_label s (Kseq (seq_of_labeled_statement ls) k)).
    eauto. constructor. eauto. eauto. 
  destruct (find_label lbl s (Kseq (seq_of_labeled_statement ls) k)) as [[s' k']|].
  intros [ts' [P Q]]. exists ts'. simpl. rewrite P. auto. 
  intros E. simpl; rewrite E. eapply IHls; eauto.
Qed.

Lemma find_label_store_params:
  forall lbl s k params, find_label lbl (store_params cenv params s) k = find_label lbl s k.
Proof.
  induction params; simpl. auto.
  destruct a as [id ty]. destruct (VSet.mem id cenv); auto.
Qed.

End FIND_LABEL.  

(*TODO: move elsewhere *)

Lemma vals_def_defined vs : vals_def vs = vals_defined vs.
Proof.
induction vs; auto.
simpl.
destruct a; auto.
Qed.

Require Import val_casted.

(*END move*)

Lemma MATCH_atExternal: forall mu c1 m1 c2 m2 e vals1 ef_sig
       (MTCH: MATCH c1 mu c1 m1 c2 m2)
       (AtExtSrc: at_external (CL_eff_sem1 hf) c1 = Some (e, ef_sig, vals1)),
     Mem.inject (as_inj mu) m1 m2 /\
     mem_respects_readonly ge m1 /\
     mem_respects_readonly tge m2 /\
     exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
       at_external (CL_eff_sem2 hf) c2 = Some (e, ef_sig, vals2) /\
      (forall pubSrc' pubTgt',
       pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
       pubTgt' = (fun b : block => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
       forall nu : SM_Injection, nu = replace_locals mu pubSrc' pubTgt' ->
       MATCH c1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2).
Proof. intros. 
destruct MTCH as [[MC [RC [PG [Glob [SMV WD]]]]] [MRR1 MRR2]].
    inv MC; simpl in AtExtSrc; inv AtExtSrc.
    destruct tfd; simpl in *; inv H0.
    split; trivial. 
    split; trivial. 
    split; trivial. 
    destruct (observableEF_dec hf e0); inv H1.
    destruct (vals_def vargs) eqn:Heqv; inv H0.
    exists tvargs; split; trivial.
    eapply val_list_inject_forall_inject; try eassumption.
    split; trivial.
    intros. simpl. 
    rewrite vals_def_defined in *. 
    eapply vals_inject_defined in Heqv; eauto.
    rewrite Heqv; auto.
    exploit replace_locals_wd_AtExternal; try eassumption.
                apply val_list_inject_forall_inject in AINJ.
                apply forall_vals_inject_restrictD in AINJ. eassumption.
    intros WDnu.
    split. 
    { split. 2: split; trivial. 
           subst.
           split. econstructor; eauto.
             intros. eapply match_cont_replace_locals. eauto.
             rewrite replace_locals_as_inj. trivial.
             rewrite replace_locals_as_inj, replace_locals_vis. trivial.
          rewrite replace_locals_as_inj, replace_locals_vis, replace_locals_frgnBlocksSrc.
            intuition.
            (*sm_valid*)
            red. rewrite replace_locals_DOM, replace_locals_RNG. apply SMV.
    }
    { clear - WDnu MINJ H1 WD RC H H0.
      eapply inject_shared_replace_locals; try eassumption.
      subst; trivial. }
Qed.

Lemma MATCH_afterExternal: forall
  mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig' 
(MemInjMu : Mem.inject (as_inj mu) m1 m2)
(MatchMu : MATCH st1 mu st1 m1 st2 m2)
(AtExtSrc : at_external (CL_eff_sem1 hf) st1 = Some (e, ef_sig, vals1))
(AtExtTgt : at_external (CL_eff_sem2 hf) st2 = Some (e', ef_sig', vals2))
(ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
(pubSrc' : block -> bool)
(pubSrcHyp : pubSrc' =
            (fun b : block =>
             locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
(pubTgt' : block -> bool)
(pubTgtHyp : pubTgt' =
            (fun b : block =>
             locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
nu (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
nu' ret1 m1' ret2 m2'
(INC : extern_incr nu nu')
(GSep: globals_separate (Genv.globalenv prog) nu nu')
(*SEP : sm_inject_separated nu nu' m1 m2*)
(WDnu' : SM_wd nu')
(SMvalNu' : sm_valid nu' m1' m2')
(MemInjNu' : Mem.inject (as_inj nu') m1' m2')
(RValInjNu' : val_inject (as_inj nu') ret1 ret2)
(FwdSrc : mem_forward m1 m1')
(FwdTgt : mem_forward m2 m2')
(RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge))
(RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks tge))
(frgnSrc' : block -> bool)
(frgnSrcHyp : frgnSrc' =
             (fun b : block =>
              DomSrc nu' b &&
              (negb (locBlocksSrc nu' b) &&
               REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
(frgnTgt' : block -> bool)
(frgnTgtHyp : frgnTgt' =
             (fun b : block =>
              DomTgt nu' b &&
              (negb (locBlocksTgt nu' b) &&
               REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
mu'
(Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
(UnchPrivSrc : Mem.unchanged_on
                (fun (b : block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1')
(UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists st1' st2' : CL_core,
  after_external (CL_eff_sem1 hf) (Some ret1) st1 = Some st1' /\
  after_external (CL_eff_sem2 hf) (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros. 
 destruct MatchMu as [[MC [RC [PG [GF [SMV WDmu]]]]] MRR].
 (*assert (PGR: meminj_preserves_globals (Genv.globalenv prog)
                  (restrict (as_inj mu) (vis mu))).
      eapply restrict_preserves_globals; try eassumption.
        unfold vis; intuition.*)
 inv MC; simpl in *; inv AtExtSrc.
  destruct tfd; inv H0.
  inv AtExtTgt. 
  destruct (observableEF_dec hf e0); inv H1; inv H0. 
  rename H1 into H0.
  rename H2 into H1.
  destruct (vals_def vargs) eqn:Heqv; inv H1.
  assert (Htvals: vals_def tvargs = true).
  { rewrite vals_def_defined in *.
    eapply vals_inject_defined in Heqv; eauto. }
  rewrite Htvals in H0; inv H0.
  rename o into OBS.  
  eexists; eexists.
    split. reflexivity.
    split. reflexivity.
  simpl in *.
inv FUNTY. 
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
    subst. clear - INC GSep (*SEP*) PG GF WDmu WDnu'.
    apply meminj_preserves_genv2blocks in PG.
    destruct PG as [PGa [PGb PGc]].
    apply meminj_preserves_genv2blocks.
    split; intros.
      specialize (PGa _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char1 in H.
          rewrite H. trivial.
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      apply foreign_in_extern; eassumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char2 in H.
          rewrite H. intuition.
      destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
      apply foreign_in_extern; eassumption.
    eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
      remember (as_inj mu b1) as d.
      destruct d; apply eq_sym in Heqd.
        destruct p. 
        apply extern_incr_as_inj in INC; trivial.
        rewrite replace_locals_as_inj in INC.
        rewrite (INC _ _ _ Heqd) in H0. trivial.
        simpl in H.
        unfold globals_separate in GSep.
        rewrite replace_locals_as_inj in GSep. 
        generalize (GSep _ _ _ Heqd H0).
        destruct H as [gv  H]; apply find_var_info_isGlobal in H.
        intros HH. 
        congruence.
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  clear MRR; intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H1); clear H1.
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
          eapply SMV. unfold DOM, DomSrc. rewrite Heql. intuition.
        apply (H VB) in H2.
        rewrite (H0 H2) in H4. clear H H0.
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
    destruct IHL. inv H.
    apply andb_true_iff in H. simpl in H. 
    destruct H as[DomNu' Rb']. 
    clear INC INCvisNu' UnchLOOR UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ MemInjNu' RET
               _ Rb' (fun b => true)) as [b2 [d1 [AI' _]]]; trivial.
           assert (REACH m1' (mapped (as_inj nu')) b = true).
             eapply REACH_cons; try eassumption.
             apply REACH_nil. eapply mappedI_true; eassumption.
           specialize (RC' _ H). 
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
     intros. specialize (GF _ H).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in GF.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ GF). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ GF). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ GF). intuition.
exploit (eff_after_check1 mu); try eassumption; try reflexivity.
  eapply val_list_inject_forall_inject.
  eapply val_list_inject_incr; try eassumption.
    apply restrict_incr.
intros [WDnu [SMVnu [MinjNu VinjNu]]].
split.
{ (*MATCH'*)
  clear MRR; split.
  { unfold vis in *.
    rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.
    econstructor; try eassumption.
    intros. 
     rewrite replace_locals_locBlocksSrc, replace_locals_pubBlocksSrc in *.
     eapply match_cont_incr_bounds. 
     eapply match_cont_replace_externs; try eapply forward_nextblock.
     (*About match_cont_extern_invariantPriv.*)
     eapply match_cont_extcallPriv. 
       Focus 3. eassumption.
       Focus 3. eassumption.
       eapply match_cont_replace_locals; eassumption. 
             eapply mem_unchanged_on_sub; try eassumption.
                unfold privBlocksSrc. rewrite replace_locals_locBlocksSrc, replace_locals_pubBlocksSrc.
                intros. apply andb_true_iff in H; destruct H. 
                  rewrite H. split; simpl; trivial. rewrite H in H0. simpl in *. apply negb_true_iff in H0; trivial.
       xomega.
       instantiate (1:= m2). xomega.
       eassumption. 
       eassumption.
       eassumption.
       intros. unfold vis in H.
          remember (locBlocksSrc nu' b) as d.
          destruct d; simpl in *; trivial.
          apply andb_true_iff. split. 
            apply frgnBlocksSrc_extBlocksSrc in H; trivial.
            unfold DomSrc; rewrite H; intuition. 
          apply REACH_nil. unfold exportedSrc.
            rewrite (frgnSrc_shared _ WDnu' _ H). intuition.
      assumption.
      assumption.
      eapply forward_nextblock. assumption.
      eapply forward_nextblock. assumption.
    rewrite replace_externs_as_inj; assumption.
    rewrite replace_externs_as_inj, replace_externs_vis.
    inv RValInjNu'; econstructor; eauto.
      eapply restrictI_Some; trivial.
      destruct (as_inj_DomRng _ _ _ _ H WDnu'). rewrite H0; simpl.
      destruct (locBlocksSrc nu' b1); simpl; trivial.
      apply REACH_nil. apply orb_true_iff; left. 
        apply getBlocks_char; eexists; left. reflexivity. }
  { unfold vis.
    rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
    destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
    intuition. }
}
destruct MRR as [MRR1 MRR2].
clear - FwdSrc FwdTgt MRR1 MRR2 RDO1 RDO2.
split.
 apply mem_respects_readonly_forward' with (m:=m1); eassumption.
 eapply mem_respects_readonly_forward'; eassumption. 
Qed.

Lemma match_globalenvs_init':
  forall (R: list_norepet (map fst (prog_defs prog))) m j,
  Genv.init_mem prog = Some m ->
  meminj_preserves_globals ge j ->
  match_globalenvs j (Mem.nextblock m).
Proof.
  intros.
  destruct H0 as [A [B C]].
  constructor.
  intros b D. (*intros [[id E]|[[gv E]|[fptr E]]]; eauto.*)
  cut (exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b).
  intros [id ID].
  solve[eapply A; eauto].
  eapply valid_init_is_global; eauto.
  intros. symmetry. solve [eapply (C _ _ _ _ GV); eauto].
  intros. eapply Genv.find_symbol_not_fresh; eauto.
  intros. eapply Genv.find_funct_ptr_not_fresh ; eauto.
  intros. eapply Genv.find_var_info_not_fresh; eauto.
Qed.

(*TODO: move*)
Lemma genv_next_symbol_exists' b (ge0 : Genv.t fundef type) l :
  list_norepet (map fst l) -> 
  (Plt b (Genv.genv_next ge0) ->
    exists id, ~List.In id (map fst l) /\ Genv.find_symbol ge0 id = Some b) -> 
  Plt b (Genv.genv_next (Genv.add_globals ge0 l)) ->
  exists id, Genv.find_symbol (Genv.add_globals ge0 l) id = Some b.
Proof.
revert ge0 b.
induction l; simpl; auto.
intros ge0 b ? ? H2.
destruct (H0 H2) as [? [? ?]].
solve[eexists; eauto].
intros ge0 b H H2 H3.
inv H.
destruct a; simpl in *.
eapply IHl; eauto.
intros Hplt.
destruct (ident_eq b (Genv.genv_next ge0)). 
* subst b.
exists i.
unfold Genv.add_global, Genv.find_symbol; simpl.
rewrite PTree.gss; auto.
* unfold Genv.add_global, Genv.find_symbol; simpl.
destruct H2 as [x H2].
unfold Genv.add_global in Hplt; simpl in Hplt; xomega.
exists x.
destruct H2 as [A B].
split; auto.
rewrite PTree.gso; auto.
Qed.

Lemma genv_next_symbol_exists b :
  list_norepet (map fst (prog_defs prog)) -> 
  Plt b (Genv.genv_next ge) -> 
  exists id, Genv.find_symbol ge id = Some b.
Proof.
intros Hnorepet H.
exploit genv_next_symbol_exists'; eauto.
simpl; xomega.
Qed.

Lemma genv_next_symbol_exists2 b :
  list_norepet (map fst (prog_defs prog)) -> 
  Psucc b = Genv.genv_next ge -> 
  exists id, Genv.find_symbol ge id = Some b.
Proof.
intros Hnorepet H.
apply genv_next_symbol_exists; auto.
xomega.
Qed.

Lemma match_globalenvs_init2:
  forall (R: list_norepet (map fst (prog_defs prog))) j,
  meminj_preserves_globals ge j ->
  match_globalenvs j (Genv.genv_next ge).
Proof.
  intros.
  destruct H as [A [B C]].
  constructor.
  intros b D. 
  cut (exists id, Genv.find_symbol (Genv.globalenv prog) id = Some b).
  intros [id ID].
  solve[eapply A; eauto].
  exploit genv_next_symbol_exists; eauto.
  intros. symmetry. solve [eapply (C _ _ _ _ GV); eauto].
  intros. eapply Genv.genv_symb_range; eauto.
  intros. eapply Genv.genv_funs_range; eauto.
  intros. eapply Genv.genv_vars_range; eauto.
Qed.

Lemma MATCH_initial: forall v
  (vals1 : list val) c1 (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (CSM_Ini :initial_core (CL_eff_sem1 hf) ge v vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (GFI: globalfunction_ptr_inject ge j)
  (LNR: list_norepet (map fst (prog_defs prog)))
  (J: forall b1 b2 d, j b1 = Some (b2, d) ->
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (RdOnly1: mem_respects_readonly ge m1)
  (RdOnly2: mem_respects_readonly tge m2) 
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b)
  (Disj: forall b f, Genv.find_funct_ptr (Genv.globalenv prog) b = Some (Internal f) ->
                     list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))),
exists c2,
  initial_core (CL_eff_sem2 hf) tge v vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof. intros.
  inversion CSM_Ini.
  unfold CL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0.
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  revert H1. case_eq (type_of_fundef (Internal f)); try solve[intros; congruence].
  intros targs tres tyof.
  case_eq (val_casted_list_func vals1 targs); try solve[simpl; intros; congruence].
  case_eq (tys_nonvoid targs); try solve[simpl; intros; congruence].
  case_eq (vals_defined vals1); try solve[simpl; intros; congruence].
  intros DEF TNV VALCAST; inversion 1; subst.

  simpl; revert H1; case_eq
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  intros l _.
  2: simpl; solve[inversion 2].
  simpl. inversion 1.

  exists (CL_Callstate (Internal f) vals2 Kstop).
  split. simpl.
  subst. inv Heqzz. 
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
  assert (Hlen: Zlength vals2 = Zlength vals1).
  { apply forall_inject_val_list_inject in VInj. clear - VInj.
    induction VInj; auto. rewrite !Zlength_cons, IHVInj; auto. }
  rewrite Hlen.
  assert (H: val_casted_list vals2 targs).
  { cut (val_casted_list vals1 targs).
    cut (val_list_inject j vals1 vals2).
    apply val_casted_list_inj; auto.
    apply forall_inject_val_list_inject; auto.
    apply val_casted_list_funcP; auto. }
  assert (vals_defined vals2=true) as ->.
  { eapply vals_inject_defined; eauto.
    eapply forall_inject_val_list_inject; eauto. }
  simpl; revert H0; case_eq
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  rewrite H2. intros. simpl. rewrite <-val_casted_list_funcP in H. 
    assert (type_of_params (fn_params f) = targs) as ->.
    { inv tyof; auto. }
    rewrite H, TNV; auto.
  intros CONTRA. solve[elimtype False; auto].
  intros CONTRA. solve[elimtype False; auto].

  split. 2: split; assumption.

  split. econstructor; try rewrite initial_SM_as_inj; try eassumption; auto.
          intros. econstructor.
          eapply match_globalenvs_init2. assumption. 
            eapply restrict_preserves_globals. rewrite initial_SM_as_inj. assumption.
          unfold vis, initial_SM; simpl; intros.
            apply REACH_nil. unfold ge in H. rewrite H. intuition. 

  { destruct PG as [XX [Y Z]].
    unfold Ple. rewrite <-Pos.leb_le.
    destruct (Pos.leb (Genv.genv_next ge) (Mem.nextblock m1)) eqn:?; auto.
    rewrite Pos.leb_nle in Heqb0.
    assert (Heqb': (Genv.genv_next ge > Mem.nextblock m1)%positive) by xomega.
    assert (exists b0, Psucc b0 = Genv.genv_next ge).
    { destruct (Genv.genv_next ge). 
      exists ((b0~1)-1)%positive. simpl. auto.
      exists (Pos.pred (b0~0))%positive. rewrite Pos.succ_pred. auto. xomega.
      xomega. }
    destruct H as [b0 H].
    generalize H as H'; intro.
    apply genv_next_symbol_exists2 in H.
    destruct H as [id H].
    apply XX in H.
    apply J in H.
    destruct H as [H H3].
    specialize (HDomS _ H).
    unfold Mem.valid_block in HDomS. clear - Heqb' HDomS H'. xomega.
    auto. }

  { destruct PG as [XX [Y Z]].
    unfold Ple. rewrite <-Pos.leb_le.
    destruct (Pos.leb (Genv.genv_next ge) (Mem.nextblock m2)) eqn:?; auto.
    rewrite Pos.leb_nle in Heqb0.
    assert (Heqb': (Genv.genv_next ge > Mem.nextblock m2)%positive) by xomega.
    assert (exists b0, Psucc b0 = Genv.genv_next ge).
    { destruct (Genv.genv_next ge). 
      exists ((b0~1)-1)%positive. simpl. auto.
      exists (Pos.pred (b0~0))%positive. rewrite Pos.succ_pred. auto. xomega.
      xomega. }
    destruct H as [b0 H].
    generalize H as H'; intro.
    apply genv_next_symbol_exists2 in H.
    destruct H as [id H].
    apply XX in H.
    apply J in H.
    destruct H as [H H3].
    specialize (HDomT _ H3).
    unfold Mem.valid_block in HDomT. clear - Heqb' HDomT H'. xomega.
    auto. }

  unfold vis, initial_SM; simpl.
  apply forall_inject_val_list_inject.
  eapply restrict_forall_vals_inject; try eassumption.
  intros. apply REACH_nil. rewrite H; intuition.
  apply val_casted_list_funcP; auto.
  { intros. inv H. clear - Disj Heqzz. apply (Disj _ _ Heqzz). }
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _ Inj
              VInj J RCH PG GDE_lemma HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  intuition. 
  rewrite initial_SM_as_inj. assumption.
Qed.

Lemma FreelistEffect_PropagateLeft mu e le m lo hi te tle tlo thi: forall
        (MENV : match_envs mu e le m lo hi te tle tlo thi)
        m2 b2 ofs
        (FEffTgt : FreelistEffect m2 (blocks_of_env te) b2 ofs = true)
        (LBT : locBlocksTgt mu b2 = false)
        m' (FL : Mem.free_list m (blocks_of_env e) = Some m')
        (SMV : sm_valid mu m m2)
        (WD : SM_wd mu),
      exists b1 delta,
        foreign_of mu b1 = Some (b2, delta) /\
        FreelistEffect m (blocks_of_env e) b1 (ofs - delta) = true /\
        Mem.perm m b1 (ofs - delta) Max Nonempty.
Proof. intros.
           exploit FreelistEffect_Dtrue2; eauto. intros [bbb [l [h [INL FREE]]]].           
           apply FreeEffectD in FREE. destruct FREE as [? [VB Arith2]]; subst.
           destruct (blocks_of_envD _ _ _ _ INL) as [? [? [id ID]]]; subst.
           exploit me_mapped; try eassumption. intros [b [RES EE]].
           rewrite restrict_vis_foreign_local in RES; trivial.
           destruct (joinD_Some _ _ _ _ _ RES); clear RES.
           Focus 2. destruct H as [_ ?].
                    destruct (local_DomRng _ WD _ _ _ H).
                    rewrite LBT in H1; discriminate.
           exists b, 0; split; trivial.
             assert (INE: In (b,0, h) (blocks_of_env e)).
                unfold blocks_of_env in INL. apply in_map_iff in INL.
                destruct INL as [[i [bb ty]] [BOB INelem]].
                unfold block_of_binding in BOB. inv BOB.
                apply in_map_iff. unfold block_of_binding. 
                exists (x, (b, ty)). split; trivial.
                apply PTree.elements_complete in INelem.
                apply PTree.elements_correct.
                exploit me_flat. eassumption. apply INelem.
                apply foreign_in_all in H; eassumption.
                intros [? _].
                destruct (ident_eq x i); subst. trivial.
                exploit me_inj. eassumption. apply EE. apply H0. assumption. 
                  trivial. intros; contradiction.               
             rewrite Zminus_0_r.
             split. eapply FreelistEffect_I; try eassumption.
                     apply foreign_in_all in H; trivial.
                     eapply SMV. eapply as_inj_DomRng; eassumption.
             eapply Mem.perm_implies. 
               eapply Mem.perm_max. 
                 eapply free_list_perm'; eassumption.
                 constructor.
Qed. 

Lemma MATCH_effcore_diagram: forall st1 m1 st1' m1' 
         (U1 : block -> Z -> bool)
         (CS: effstep (CL_eff_sem1 hf) ge U1 st1 m1 st1' m1') st2 mu m2
         (MTCH: MATCH' st1 mu st1 m1 st2 m2)
         (DISJ: forall vf f, Genv.find_funct ge vf = Some (Internal f) -> 
                list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))),
   exists st2' m2' U2, effstep_plus (CL_eff_sem1 hf) tge U2 st2 m2 st2' m2'
/\ exists mu', MATCH' st1' mu' st1' m1' st2' m2' /\
               intern_incr mu mu' /\
               globals_separate ge mu mu' /\
    sm_inject_separated mu mu' m1 m2 /\
    sm_locally_allocated mu mu' m1 m2 m1' m2' /\
    (forall 
       (U1Hyp: forall b ofs, U1 b ofs = true -> vis mu b = true)
       b ofs, U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. 
intros.
assert (SymbPres := symbols_preserved).
destruct CS; intros; 
  destruct MTCH as [MS [RC [PG [GLOB [SMV WD]]]]];
  inv MS; simpl in *; try (monadInv TRS).

{ (* assign *)
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
  { rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. }

  (* not liftable *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR. 
  exploit eval_simpl_lvalue. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. 
      destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. 
  intros [tb [tofs [E F]]]. 
  exploit eval_simpl_expr. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. 
      destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. 
  intros [tv2 [A B]].
  exploit sem_cast_inject; eauto. intros [tv [C D]].
  exploit assign_loc_inject. eassumption. 
     eapply val_inject_incr; try eassumption. rewrite restrict_sm_all. apply restrict_incr.
     eapply val_inject_incr; try eassumption. rewrite restrict_sm_all. apply restrict_incr.
     eassumption.
  intros [tm' [X [Y Z]]]. 
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor. eexact E. eexact A. 
    repeat rewrite typeof_simpl_expr. eexact C. auto. eexact X.
  exists mu.
  split. 
    split. (*math_states*)
      econstructor; eauto with compat. clear MENVR.
      eapply match_envs_intern_invariant; eauto. apply intern_incr_refl.  
      eapply match_cont_intern_invariant; eauto. apply intern_incr_refl.  
      erewrite assign_loc_nextblock; eauto.
      erewrite assign_loc_nextblock; eauto.
    intuition.
      inv H2; try congruence. unfold Mem.storev in H4.
      eapply REACH_Store; try eassumption.
      rewrite restrict_sm_all in F; inv F.  apply (restrictD_Some _ _ _ _ _ H7).
        intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
        destruct Hoff; try contradiction. subst.   
        rewrite restrict_sm_all in D; inv D.
        apply (restrictD_Some _ _ _ _ _ H6).
      rewrite restrict_sm_all in F; inv F. destruct (restrictD_Some _ _ _ _ _ H11).
      eapply REACH_Storebytes; try eassumption.
             intros bb off n Hbb. inv D.
             destruct (Mem.loadbytes_inject _ _ _ _ _ _ _ _ _ INJR H7 H13)
                as [bytes2 [LoadBytes2 MapBytes]].
             clear - Hbb MapBytes.
               induction MapBytes; inv Hbb.
               inv H. rewrite restrict_sm_all in H4. apply (restrictD_Some _ _ _ _ _ H4).
               apply (IHMapBytes H0).
    split; intros.
      eapply assign_loc_forward. apply H2. apply SMV; trivial.
      eapply assign_loc_forward. apply X. eapply SMV; trivial.
      split. apply intern_incr_refl.
      split. apply gsep_refl.
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (assign_loc_freshloc _ _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (assign_loc_freshloc _ _ _ _ _ _ X). intuition.
      apply extensionality; intros; rewrite (assign_loc_freshloc _ _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (assign_loc_freshloc _ _ _ _ _ _ X). intuition.
  inv F. rewrite restrict_sm_all in H6. 
  intuition.
        unfold assign_loc_Effect in H3. unfold assign_loc_Effect.
                inv H2; rewrite H4 in H3. 
              (*by value*)
                inv X; rewrite H2 in H4; inv H4.
                destruct (eq_block tb b); try subst tb; simpl in *; try discriminate.
                eapply visPropagateR; try eassumption.
              (*by copy*)
                inv X; rewrite H2 in H4; inv H4.
                destruct (eq_block b tb); try subst tb; simpl in *; try discriminate.
                eapply visPropagateR; try eassumption.
        unfold assign_loc_Effect in H3. unfold assign_loc_Effect.
             inv H2; rewrite H5 in H3. 
              (*by value*)
                inv X; rewrite H2 in H5; inv H5. rewrite H2.
                destruct (eq_block tb b); try subst tb; simpl in *; try discriminate.
                destruct (restrictD_Some _ _ _ _ _ H6).
                exists loc, delta.
                   split. eapply restrict_vis_foreign; eassumption.
                   assert (WR:Mem.perm m loc (Int.unsigned ofs) Cur Writable).
                      eapply Mem.store_valid_access_3; try eassumption. 
                      specialize (size_chunk_pos chunk); intros. omega.
                   specialize (Mem.address_inject _ _ _ loc ofs b delta Writable MINJ WR H5). 
                   intros.
                   destruct (eq_block loc loc); simpl. 
                     clear e0. rewrite H10 in H3. 
                               destruct (zle (Int.unsigned ofs + delta) ofs0); simpl in H6; try discriminate.
                               destruct (zle (Int.unsigned ofs) (ofs0 - delta)); simpl.
                               Focus 2. exfalso. clear - l g. omega.
                               destruct (zlt ofs0 (Int.unsigned ofs + delta + Z.of_nat (size_chunk_nat chunk))); try discriminate.
                               destruct (zlt (ofs0 - delta) (Int.unsigned ofs + Z.of_nat (size_chunk_nat chunk))); simpl.
                               Focus 2. exfalso. clear - l1 g. omega.
                               split; trivial. rewrite <- size_chunk_conv in l2. 
                               eapply Mem.perm_implies. 
                                  eapply Mem.perm_max.
                                    eapply Mem.store_valid_access_3; eauto.
                                  apply perm_any_N.
                   elim n; trivial.
              (*by copy*) 
                inv X; rewrite H2 in H5; inv H5. rewrite H2. 
                   destruct (eq_block b tb); subst; simpl in *; try discriminate.                   
                   destruct (restrictD_Some _ _ _ _ _ H6).
                   intros. exists loc, delta.
                   split. eapply restrict_vis_foreign; eassumption.
                   assert (WR:Mem.perm m loc (Int.unsigned ofs) Cur Writable).
                      eapply Mem.storebytes_range_perm; try eassumption.
                         rewrite (Mem.loadbytes_length _ _ _ _ _ H10).
                         specialize (sizeof_pos (typeof a1)); intros.
                         rewrite nat_of_Z_eq.
                         omega. omega.
                   specialize (Mem.address_inject _ _ _ loc ofs tb delta Writable MINJ WR H5). intros.
                   destruct (eq_block loc loc); simpl. 
                     clear e0. rewrite H18 in H3. 
                               destruct (zle (Int.unsigned ofs + delta) ofs0); simpl in H3; try discriminate.
                               destruct (zle (Int.unsigned ofs) (ofs0 - delta)); simpl.
                               Focus 2. exfalso. clear - l g. omega.
                               specialize (sizeof_pos (typeof a1)); intros.
                               destruct (zlt ofs0 (Int.unsigned ofs + delta + sizeof (typeof a1))); try discriminate.
                               destruct (zlt (ofs0 - delta) (Int.unsigned ofs + sizeof (typeof a1))); simpl.
                               Focus 2. exfalso. clear - l1 g. omega.
                               split; trivial.
                               eapply Mem.perm_implies. 
                                  eapply Mem.perm_max.
                                    eapply Mem.storebytes_range_perm; eauto.
                                     split. omega. specialize (Mem.loadbytes_length _ _ _ _ _ H10); intros. rewrite H20. rewrite nat_of_Z_eq. assumption. omega. 
                                  apply perm_any_N.
                   elim n; trivial. }
     
{ (* set temporary *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR.
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
    rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. 
  exploit eval_simpl_expr. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. 
  intros [tv [A B]].
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor. eauto.
  eexists; split.  
    split. 
      econstructor; eauto with compat. 
      eapply match_envs_set_temp; eauto.
      rewrite restrict_sm_all in B; trivial.
    intuition. 
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* call *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR.
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
    rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. 
  exploit eval_simpl_expr. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. eauto with compat.
  intros [tvf [A B]].
  exploit eval_simpl_exprlist. apply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. eauto with compat.
  intros [CASTED [tvargs [C D]]].
  exploit match_cont_find_funct.
    eapply match_cont_restrict. eassumption. intros. apply H4. trivial. eassumption. eassumption.
  intros [tfd [P Q]].
  eexists; eexists; eexists; split.
    apply effstep_plus_one. eapply clight_effstep_call with (fd := tfd).
    eauto. eauto. eauto. eauto. subst; auto.
  rewrite restrict_sm_all in D.
  subst.
  exists mu; split.
    split. 
      econstructor; eauto. 
      intros. econstructor; eauto.
      intros; subst; auto.
      specialize (DISJ _ _ H2); auto.
    intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* builtin *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR.
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
    rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. 
  exploit eval_simpl_exprlist; try eapply MENVR; eauto with compat.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
  intros [CASTED [tvargs [C D]]].
  rewrite restrict_sm_all in D.
  (*exploit external_call_mem_inject; eauto.*)
  exploit (inlineable_extern_inject _ _ GDE_lemma); 
    try eapply D; try eassumption. 
(*  apply match_globalenvs_preserves_globals; eauto with compat.*)
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [GSEP [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]]].
  eexists; exists tm'; eexists.
  split. eapply effstep_plus_one. econstructor; eauto.
  exists mu'.
  split. (*MATCH*)
    exploit (intern_incr_meminj_preserves_globals_as_inj ge _ WD).
      split; assumption.
      eapply WD'.
      assumption.
    intros [PG' GLOB'].   
    split. 
      assert (LoHi: Ple lo hi). inv MENV; trivial.
      assert (TLoHi: Ple tlo thi). inv MENV; trivial.
      econstructor; eauto with compat.
     (* eapply external_call_symbols_preserved; eauto. 
        exact symbols_preserved. exact varinfo_preserved.
        econstructor; eauto with compat.*)
      eapply match_envs_set_opttemp; eauto. 
      clear MENVR.
      eapply match_envs_intern_invariant; try eassumption.
        intros. eapply Mem.load_unchanged_on; try eassumption.
          intros. red. apply restrictI_None. left; trivial.
        (*intros. eapply intern_as_inj_preserved1; try eassumption. red; xomega.*)
        intros. rewrite H2. apply eq_sym. 
                eapply intern_as_inj_preserved2; try eassumption. red; xomega.
        eapply match_cont_intern_invariant; try eassumption.
        intros. eapply Mem.load_unchanged_on; try eassumption.
                intros. apply restrictI_None. left; trivial. 
        intros. eapply intern_as_inj_preserved1; try eassumption. red; xomega.
        intros. rewrite H2. apply eq_sym. 
                eapply intern_as_inj_preserved2; try eassumption. red; xomega.
      (*  inv MENV; xomega. inv MENV; xomega. *)
      eapply Ple_trans; eauto. eapply external_call_nextblock; eauto.
      eapply Ple_trans; eauto. eapply external_call_nextblock; eauto.
    intuition.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  clear - H0 D WD MINJ. 
  intros. eapply BuiltinEffect_Propagate; eassumption. }

{ (* sequence *)
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor.
  exists mu; split.
    split. econstructor; eauto with compat. econstructor; eauto with compat.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* skip sequence *)
  inv MCONT. eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor.
  exists mu; split.
    split. econstructor; eauto. 
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* continue sequence *)
  inv MCONT. eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor.
  exists mu; split.
    split. econstructor; eauto.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }
 
{ (* break sequence *)
  inv MCONT. eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor.
  exists mu; split.
    split. econstructor; eauto.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* ifthenelse *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR.
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
    rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. 
  exploit eval_simpl_expr. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. eauto with compat.
  intros [tv [A B]].
  eexists; eexists; eexists; split.
    apply effstep_plus_one. apply clight_effstep_ifthenelse with (v1 := tv) (b := b). auto.
    eapply bool_val_inject; eauto.
  exists mu; split.
    split. destruct b; econstructor; eauto with compat.
           intuition.  
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* loop *)
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor.
  exists mu; split.
    split. econstructor; eauto with compat. econstructor; eauto with compat.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* skip-or-continue loop *)
  inv MCONT. eexists; eexists; eexists; split.
  apply effstep_plus_one. econstructor. destruct H; simpl in *; intuition congruence. 
  exists mu; split.
    split. econstructor; eauto with compat. econstructor; eauto with compat.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* break loop1 *)
  inv MCONT. eexists; eexists; eexists; split. apply effstep_plus_one. 
    eapply clight_effstep_break_loop1.
  exists mu; split.
    split. econstructor; eauto.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* skip loop2 *)
  inv MCONT. eexists; eexists; eexists; split. 
  apply effstep_plus_one. eapply clight_effstep_skip_loop2. 
  exists mu; split.
    split. econstructor; eauto. 
           simpl; auto.
           intuition.
  apply intern_incr_refl.
  apply gsep_refl. 
  apply sm_inject_separated_same_sminj.
  apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition. }

{ (* break loop2 *)
  inv MCONT. eexists; eexists; eexists; split. 
  apply effstep_plus_one. eapply clight_effstep_break_loop2.
  exists mu; split.
    split. econstructor; eauto.
           intuition.
  split. apply intern_incr_refl.
  split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* return none *)
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  eexists; eexists; eexists; split. apply effstep_plus_one. econstructor; eauto. 
  exists mu; split.
    split. econstructor; eauto. 
           intros. eapply match_cont_call_cont. eapply match_cont_free_env; eauto.
    intuition.
        eapply REACH_closed_freelist; eassumption.
  split; intros;  
      eapply freelist_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      extensionality b; rewrite (freshloc_free_list _ _ _ H); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ P); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ H); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ P); intuition.
  intros U1Vis b2 ofs FEff2.
         split. 
           apply FreelistEffect_exists_FreeEffect in FEff2.
           destruct FEff2 as [bb [low [high [NIB FEF]]]].
           apply FreeEffectD in FEF. destruct FEF as [? [VB Arith2]]; subst.
           apply blocks_of_envD in NIB. destruct NIB as [? [? [id ID]]]; subst.
           exploit me_mapped; try eassumption. intros [b [RES EE]].
           eapply visPropagateR; try eassumption.
         intros. eapply FreelistEffect_PropagateLeft; eassumption. }

{ (* return some *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR.
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
    rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. 
  exploit eval_simpl_expr. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. eauto with compat.
  intros [tv [A B]].
  exploit sem_cast_inject; eauto. intros [tv' [C D]].
  exploit match_envs_free_blocks; try eapply MINJ.
    eassumption. eassumption. 
  intros [tm' [P Q]].
  eexists; eexists; eexists; split. apply effstep_plus_one. econstructor; eauto.
      eauto.
  exists mu; split.
    split. econstructor; eauto.  
           intros. eapply match_cont_call_cont. eapply match_cont_free_env; eauto.
           rewrite restrict_sm_all in D; trivial.
         intuition.
        eapply REACH_closed_freelist; eassumption.
  split; intros;  
      eapply freelist_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption. 
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      extensionality b; rewrite (freshloc_free_list _ _ _ H1); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ P); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ H1); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ P); intuition.
  intros ? b2 ofs FEff2.
         split. 
           apply FreelistEffect_exists_FreeEffect in FEff2.
           destruct FEff2 as [bb [low [high [NIB FEF]]]].
           apply FreeEffectD in FEF. destruct FEF as [? [VB Arith2]]; subst.
           apply blocks_of_envD in NIB. destruct NIB as [? [? [id ID]]]; subst.
           exploit me_mapped; try eassumption. intros [b [RES EE]].
           rewrite restrict_sm_all, restrict_nest, vis_restrict_sm in RES.
           eapply visPropagateR; try eassumption. rewrite vis_restrict_sm. trivial.
         intros. eapply FreelistEffect_PropagateLeft; eassumption. }

{ (* skip call *)
  exploit match_envs_free_blocks; eauto. intros [tm' [P Q]].
  eexists; eexists; eexists; split. apply effstep_plus_one. econstructor; eauto.
  eapply match_cont_is_call_cont; eauto.
  auto.
  exists mu; split.
    split. econstructor; eauto. 
           intros. eapply match_cont_free_env; eauto.
         intuition.
        eapply REACH_closed_freelist; eassumption.
  split; intros;  
      eapply freelist_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption. 

  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      extensionality b; rewrite (freshloc_free_list _ _ _ H0); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ P); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ H0); intuition.
      extensionality b; rewrite (freshloc_free_list _ _ _ P); intuition.
  intros ? b2 ofs FEff2.
         split. 
           apply FreelistEffect_exists_FreeEffect in FEff2.
           destruct FEff2 as [bb [low [high [NIB FEF]]]].
           apply FreeEffectD in FEF. destruct FEF as [? [VB Arith2]]; subst.
           apply blocks_of_envD in NIB. destruct NIB as [? [? [id ID]]]; subst.
           exploit me_mapped; try eassumption. intros [b [RES EE]].
           eapply visPropagateR; try eassumption.
         intros. eapply FreelistEffect_PropagateLeft; eassumption. }

{ (* switch *)
  exploit match_envs_restrict; try eassumption. instantiate (1:=vis mu); trivial.
  intros MENVR.
  assert (INJR: Mem.inject (as_inj (restrict_sm mu (vis mu))) m m2).
    rewrite restrict_sm_all; trivial.
    eapply inject_restrict; try eassumption. 
  exploit eval_simpl_expr. eapply MENVR. eassumption.
    rewrite restrict_sm_all, restrict_nest, vis_restrict_sm. 
      apply match_cont_match_globalenvs in MCONT. destruct MCONT as [bnd [X _]]; exists bnd; trivial.
      rewrite vis_restrict_sm. trivial.
     apply restrict_sm_WD; try assumption. trivial.
     eassumption. eauto with compat.
  intros [tv [A B]]. inv B. clear INJR.
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor; eauto.
  exists mu; split.
    split. econstructor; eauto. 
           econstructor; eauto. 
           eauto.
       intuition.
  apply intern_incr_refl.
  apply gsep_refl. 
  apply sm_inject_separated_same_sminj.
  apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition. }

{ (* skip-break switch *)
  inv MCONT. 
  eexists; eexists; eexists; split. 
    apply effstep_plus_one. eapply clight_effstep_skip_break_switch. destruct H; simpl in *; intuition congruence. 
  exists mu; split.
    split. econstructor; eauto with compat.
       intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* continue switch *)
  inv MCONT. 
  eexists; eexists; eexists; split. 
    apply effstep_plus_one. eapply clight_effstep_continue_switch.
  exists mu; split.
    split. econstructor; eauto with compat.
       intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* label *)
  eexists; eexists; eexists; split. apply effstep_plus_one. econstructor.
  exists mu; split.
    split. econstructor; eauto.
       intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* goto *)
  exploit (simpl_find_label mu m lo tlo lbl (fn_body tf) (call_cont k) (call_cont tk)).
    eapply match_cont_call_cont. eauto.  
  rewrite H. intros [tk' [A B]]. 
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor; eauto. simpl. 
  exists mu; split.
    split. econstructor; eauto.
           intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }

{ (* internal function *)
  inv H. 
  assert (list_norepet (var_names (fn_params f ++ fn_vars f))).
    unfold var_names. rewrite map_app. auto.
  exploit match_envs_alloc_variables; eauto.
  intros [mu' [te [tm0 [A [B [C [D [E [F [WD' [SMV' [LocAlloc RC']]]]]]]]]]]].
  exploit store_params_correct_eff.
    eauto.
    eapply list_norepet_append_left; eauto.
    apply val_casted_list_params. unfold type_of_function in FUNTY. congruence.
    apply (val_list_inject_incr (restrict (as_inj mu) (vis mu)) 
                                (restrict (as_inj mu') (vis mu'))); try eassumption.
      eapply intern_incr_restrict; eassumption. 
    eexact B. eexact C.
    intros. instantiate (1 := fn_temps f). auto.
  destruct (create_undef_temps (fn_temps f))!id as [v|] eqn:?; auto.
  exploit create_undef_temps_inv; eauto. intros [P Q]. 
    assert (l : list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))).
    { apply DISJ0; auto. }
    elim (l id id). auto.
  auto. auto. auto. auto. auto.
  intros [tm1 [P [Q [R [S [SMV'' [RC'' HH]]]]]]].
  generalize (vars_and_temps_properties (cenv_for f) (fn_params f) (fn_vars f) (fn_temps f)).
  intros [X [Y Z]]. auto. auto. 
  exists (CL_State f (fn_body f) tk te (create_undef_temps (fn_temps f))).
  eexists; eexists; split.
    eapply effstep_plus_one. econstructor. econstructor; eauto.
  eexists mu'; split.  
    split. econstructor; eauto.
      eapply match_cont_intern_invariant; eauto. 
      intros. transitivity (Mem.load chunk m1 b 0). 
      eapply bind_parameters_load; eauto. intros. 
      exploit alloc_variables_range. eexact H1. eauto. 
      unfold empty_env. rewrite PTree.gempty. intros [?|?]. congruence. 
      red; intros; subst b'. xomega. 
      eapply alloc_variables_load; eauto.
      rewrite (bind_parameters_nextblock _ _ _ _ _ H2). xomega.
      rewrite S; xomega.
    exploit @intern_incr_meminj_preserves_globals_as_inj; try eapply D.
      eassumption. split; eassumption. eassumption. 
    intros [PG' GLOB'].           
    intuition.
    split; auto.
    split. solve[eapply intern_incr_globals_separate; eauto].
    split. (*sm_inject_separated goal*)
    { clear - LocAlloc E F SMV. 
      split; intros. split. remember (DomSrc mu b1) as q. 
      destruct q; simpl in *; trivial. apply eq_sym in Heqq. rewrite E in H0. 
      congruence. apply SMV. apply Heqq. 
      remember (DomTgt mu b2) as q. destruct q; simpl in *; trivial. 
      apply eq_sym in Heqq. rewrite (F _ _ _ H0) in H0. congruence. apply SMV. apply Heqq.
      rewrite sm_locally_allocatedChar in LocAlloc. destruct LocAlloc as [LAS [LAT _]].
      split; intros. rewrite LAS, H in H0. simpl in H0. eapply freshloc_charT. eassumption.
      rewrite LAT, H in H0. simpl in H0. eapply freshloc_charT. eassumption. }
    split. (*sm_locally_allocated goal*)   
    { apply  bind_parameters_nextblock in H2.
      rewrite sm_locally_allocatedChar. rewrite sm_locally_allocatedChar in LocAlloc.
      rewrite (nextblock_eq_freshloc _ _ _ S).
      rewrite (nextblock_eq_freshloc _ _ _ H2).
      apply LocAlloc. }
    intros. intuition. }

{ (* return *)
  inv MCONT. 
  eexists; eexists; eexists; split.
    apply effstep_plus_one. econstructor. 
  exists mu; split.
    split. econstructor; eauto with compat.
           eapply match_envs_set_opttemp; eauto.
    intuition.
  split. apply intern_incr_refl.
      split. apply gsep_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition. }
Qed.

(** The simulation proof *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs prog)))
         (DISJ: forall vf f, Genv.find_funct ge vf = Some (Internal f) -> 
                list_disjoint (var_names (fn_params f)) (var_names (fn_temps f))),
  SM_simulation.SM_simulation_inject (CL_eff_sem1 hf) (CL_eff_sem1 hf) ge tge.
Proof.
intros.
 eapply simulations_lemmas.inj_simulation_plus with
  (match_states:=MATCH)(measure:= fun _ => O).
(*genvs_dom_eq*)
  apply GDE_lemma.
(*ginfos_preserved*)
 split; red; intros.
   apply gvar_info_refl.
   rewrite symbols_preserved. trivial.
(*MATCH_wd*)
  apply MATCH_wd. 
(*MATCH_reachclosed*)
  apply MATCH_RC.
(*(*MATCH_restrict*)
  apply MATCH_restrict.*)
(*MATCH_valid*)
  apply MATCH_valid.
(*MATCH_dival
  apply MATCH_dival.*)
(*MATCH_preserves_globals*)
  apply MATCH_PG.
(* init*) { 
  intros. eapply MATCH_initial; try eassumption. 
  intros b f Hfind. 
  specialize (DISJ (Vptr b Int.zero) f). simpl in DISJ.
  destruct (Int.eq_dec Int.zero Int.zero); auto.
  elimtype False; apply n; auto. }
{ (* halted *)
    intros. destruct H as [[MC [RC [PG [Glob [VAL WD]]]]] MRR].
    inv MC; simpl in H0. inv H0. inv H0.
    destruct k; simpl in *; inv H0.
    destruct (negb (is_vundef v)) eqn:Heqv; inv H1.
    inv MCONT.
    exists tv. 
    assert (Htv: negb (is_vundef tv) = true).
    { clear - Heqv RINJ.
      inv RINJ; auto.
      simpl in Heqv. congruence. }
    rewrite Htv.
    intuition. }
{ (*at_external *) 
    apply MATCH_atExternal. }
{ (*after_external *)
  apply MATCH_afterExternal. }
{ (*effcore_diagram *)
  intros. destruct H0 as [MTCH [MRR1 MRR2]].
    exploit MATCH_effcore_diagram; eauto. 
    intros [st2' [m2' [U2 [CS2 [mu' HU]]]]].
    exists st2', m2', mu'.
    split. eapply HU.
    split. eapply HU.
    split. eapply HU.
    split.
      split. eapply HU. clear HU.
      split.
      apply effstep_corestep in H.
             eapply (mem_respects_readonly_fwd _ m1). eassumption.
             eapply corestep_fwd; eassumption.
             eapply corestep_rdonly; eassumption.
        apply effstep_plus_corestep_plus in CS2.
             eapply (mem_respects_readonly_fwd _ m2). eassumption.
             eapply corestep_plus_fwd; eassumption.
             eapply corestep_plus_rdonly. eassumption. 
    exists U2. split. left; assumption. apply HU. }
Qed.

End PRESERVATION.
