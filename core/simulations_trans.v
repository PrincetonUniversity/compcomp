Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import semantics.
Require Import semantics_lemmas.

Require Import structured_injections.
Require Import reach.
Require Import effect_semantics.


Require Import simulations.
Require Import simulations_lemmas.
Require Import Wellfounded.
Require Import Relations.
Require Import internal_diagram_trans.
Require Import interpolants.
Require Import interpolation_proofs.

Require Import full_composition.

(*Require Import mem_interpolation_defs. I think this is required/name hasn't changed (?)*)


(** * Transitivity of Structured Simulations *)

Module EFFAX : EffectInterpolationAxioms := EffectInterpolations.

Import SM_simulation.

Lemma empty_inj: Mem.inject (Mem.flat_inj 1%positive) Mem.empty Mem.empty.
Proof.
  split.
    split. intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          rewrite Zplus_0_r. assumption.
       intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          apply Z.divide_0_r.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
     intros. unfold Mem.flat_inj.
          remember (plt b 1).
          destruct s; trivial. xomega.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
    intros b; intros.
      destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
    intros.
      destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
Qed.

Lemma empty_fwd: forall m, mem_forward Mem.empty m.
Proof. intros m b Vb.
   unfold Mem.valid_block in Vb. simpl in Vb. exfalso. xomega.
Qed.

(* fID satisfies (fID .*. f) = f and it's pure *)  
Definition filter_id (j:meminj): meminj:=
  fun b =>
    match j b with
        | Some _ => Some (b, 0)
        | None => None
    end.


Lemma initial_inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
       (forall b1, (exists b3 d, compose_meminj j1 j2 b1 = Some(b3,d))
                   <-> (exists b2 d1, j1 b1 = Some(b2,d1))) /\
       (forall b2 b3 d2, j2 b2 =Some(b3,d2) ->
                   exists b1 d, compose_meminj j1 j2 b1 = Some(b3,d)) /\
      (forall b1 b2 ofs2, j1 b1 = Some(b2,ofs2) -> (b1=b2 /\ ofs2=0)) /\
      (forall b2 b3 ofs3, j2 b2 = Some (b3, ofs3) ->
               Mem.flat_inj 1%positive b2 = Some (b3, ofs3) \/
               (b2 = Mem.nextblock Mem.empty /\
                    compose_meminj j1 j2 (Mem.nextblock Mem.empty) = Some (b3, ofs3)) \/
               (exists m : positive,
                   b2 = (Mem.nextblock Mem.empty + m)%positive /\
                   compose_meminj j1 j2 (Mem.nextblock Mem.empty + m)%positive =
                   Some (b3, ofs3))) (*/\ pure_composition j1 j2 m1 m2*).
Proof. 
  intros. 
  rename j into l.
  (* The constructions *)
  remember (filter_id l) as j;
  remember l as k;
  remember m1 as m2.
  
  (*The proof *)
  exists m2, j, k.
  split.
  { subst. unfold compose_meminj, filter_id.
    extensionality b.
    destruct (l b) eqn:lmap; trivial.
    rewrite lmap. destruct p; auto. }
  split.
  (*Mem.inject j m2 m2*) (* this uses the hyp Inj *)
  {constructor.
   + { constructor.
       + subst; intros.
         unfold filter_id in H; destruct (l b1); try solve [inversion H].
         inversion H; subst. replace (ofs + 0) with ofs by omega.
         auto.
       + subst; intros.
         unfold filter_id in H; destruct (l b1); try solve [inversion H].
         inversion H; subst. unfold Pos.divide; exists 0; omega. 
       + subst k j; intros.
         unfold filter_id in H; destruct (l b1) eqn:lmap; try solve [inversion H].
         inversion H; subst b1 delta. replace (ofs + 0) with ofs by omega.
         subst m2; destruct (ZMap.get ofs (Mem.mem_contents m1) !! b2) eqn:cont; try constructor.
         (*TRY*)
         destruct Inj. destruct mi_inj.
         destruct p; eapply mi_memval in lmap; eauto.
         rewrite cont in lmap. inversion lmap.
         econstructor; unfold filter_id. rewrite H3; reflexivity.
         rewrite Int.add_unsigned.
         rewrite Int.unsigned_repr_eq.
         rewrite Zmod_0_l.  replace (Int.unsigned i + 0) with (Int.unsigned i) by omega.
         symmetry; apply Int.repr_unsigned. }
   + subst; intros. apply Inj in H. 
     unfold filter_id. rewrite H; auto.
   + subst; intros. destruct Inj.
     destruct (valid_block_dec m1 b'); trivial.
     apply mi_freeblocks in n. 
     unfold filter_id in H; destruct (l b) eqn:lmap; try solve [inversion H].
     inversion H; subst. rewrite n in lmap; inversion lmap.
   + subst; intros.
     unfold Mem.meminj_no_overlap, filter_id. intros.
     destruct (l b1); inversion H0.
     destruct (l b2); inversion H1.
     subst. left; exact H.
   + subst; intros. unfold filter_id in H. destruct (l b) eqn: lmap; inversion H.
     subst. split; try omega. replace (Int.unsigned ofs + 0) with (Int.unsigned ofs) by omega.
     apply Int.unsigned_range_2. }
  split.
  (*Mem.inject k m2 m3*)
  { exact Inj. }
  split.
  {intros; subst. unfold compose_meminj, filter_id. 
   destruct (l b1) eqn:lmap. 
   + rewrite lmap. destruct p. split; intros.
     - exists b1, 0; reflexivity.
     - exists b, (0 + z); reflexivity.
   + split; intros H; destruct H as [b3 [d H]]; inversion H.
  }
  split.
  { intros. subst. unfold compose_meminj, filter_id. 
    exists b2, d2; rewrite H, H. f_equal; omega. }
  split.
  { subst; intros.
    unfold filter_id in H; destruct (l b1); try solve [inversion H].
    inversion H; subst. auto. }
  { intros; subst. 
    unfold Mem.empty in *; simpl in *.
    destruct (Pcompare b2 1%positive Eq) eqn:eqn.
    + subst. destruct b2; try solve[inversion eqn].
      right; left; split; auto; subst.
      unfold compose_meminj, filter_id. rewrite H, H. f_equal; omega.
    + destruct b2; inversion eqn. (*Impossible: b2 < 1 *)
    + assert (Gtb: Pgt b2 1) by apply eqn.
      right; right.
      apply Pos.gt_iff_add in Gtb. destruct Gtb as [m b2eq].
      exists m. split. 
      - subst; auto.
      - simpl in b2eq. rewrite b2eq.
        unfold compose_meminj, filter_id.
        rewrite H, H. f_equal; omega. }
  (* OLD version*)
  (*destruct (EFFAX.interpolate_II_strongHeqMKI _ _ _ 
     empty_inj _ (empty_fwd m1) _ _ empty_inj _ (empty_fwd m3) _ Inj)
  as [m2 [j1 [j2 [J [X [Y [Inc1 [Inc2 [Inj12 [_ [Inj23 AA]]]]]]]]]]].
intros b; intros. 
  destruct (compose_meminjD_Some _ _ _ _ _ H) as [? [? [? [? [? ?]]]]].
    subst. destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.

         exfalso. xomega.
(*intros b; intros.
   unfold Mem.valid_block; simpl; split; intros N; xomega.*)
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
subst. exists m2, j1, j2.
split; trivial.
split; trivial.
split; trivial.
destruct AA as [_ (* [Pure*) [_ [_ [XX YY]]]].
split. intros.
  split; intros. destruct H as [b3 [d COMP]].
    destruct (compose_meminjD_Some _ _ _ _ _ COMP) as
        [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear COMP.
    exists b2, d1; trivial.
  intros. destruct H as [b2 [d1 J1]].
    destruct (X _ _ _ J1) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H1. exfalso. xomega.
split. intros.
    destruct (Y _ _ _ H) as [FL | COMP]; trivial.
    destruct (flatinj_E _ _ _ _ FL) as [? [? ?]].
      subst. clear -H2. exfalso. xomega.
split. intros.
  destruct (XX _ _ _ H) as [AA | [AA | AA]].
    apply flatinj_E in AA.
      destruct AA as [? [? ?]]; subst. intuition.
    destruct AA as [? [? ?]]; subst. intuition.
    destruct AA as [mm [[? ?] ?]]; subst. intuition.
    auto.
    (*split; auto.*)*)
Qed.

Lemma compose_sm_sharedSrc mu12 mu23: forall
     (HP: forall b, pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true)
     (HF: forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true)
     (WD12: SM_wd mu12) (WD23: SM_wd mu23),
  sharedSrc (compose_sm mu12 mu23) = sharedSrc mu12.
Proof. intros. 
  rewrite (sharedSrc_iff_frgnpub mu12); trivial.
  rewrite (sharedSrc_iff_frgnpub (compose_sm mu12 mu23)).
     trivial.
  eapply compose_sm_wd; eassumption.
Qed.
 
Lemma compose_sm_exportedSrc mu12 mu23 vals: forall
     (HP: forall b, pubBlocksTgt mu12 b = true -> pubBlocksSrc mu23 b = true)
     (HF: forall b, frgnBlocksTgt mu12 b = true -> frgnBlocksSrc mu23 b = true)
     (WD12: SM_wd mu12) (WD23: SM_wd mu23),
  exportedSrc (compose_sm mu12 mu23) vals = exportedSrc mu12 vals.
Proof. intros. unfold exportedSrc.  
  rewrite compose_sm_sharedSrc; trivial. 
Qed. 

Lemma compose_sm_sharedTgt mu12 mu23:
  sharedTgt (compose_sm mu12 mu23) = sharedTgt mu23.
Proof. intros. reflexivity. Qed.

Lemma compose_sm_exportedTgt mu12 mu23 vals:
  exportedTgt (compose_sm mu12 mu23) vals = exportedTgt mu23 vals.
Proof. intros. reflexivity. Qed.

Lemma well_founded_sem_compose_ord_eq_eq: forall {D12 D23:Type}
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop)  (C2:Type)
  (WF12: well_founded ord12) (WF23: well_founded ord23),
  well_founded (sem_compose_ord_eq_eq ord12 ord23 C2). 
Proof. 
  intros. intro. destruct a as [[d12 c2] d23].
  revert d12. 
  destruct c2. 
  2: constructor; intros. 2: inv H.
  revert c. 
  induction d23 using (well_founded_induction WF23).
  intros.
  induction d12 using (well_founded_induction WF12).
  constructor; intros. inv H1.
  generalize (H0 d0). simpl. intros.
  apply H1. auto.
  generalize (H d1). 
  intros. 
  specialize (H1 H4). auto. 
Qed.

Lemma forall_val_inject_split: forall j1 j2 vals1 vals3 
  (V: Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3),
  exists vals2, Forall2 (val_inject j1) vals1 vals2
             /\ Forall2 (val_inject j2) vals2 vals3.
Proof. intros.
  induction V; simpl.
    exists nil; simpl. split; econstructor.
  destruct IHV as [vals [Vals1 Vals2]].
    destruct (val_inject_split _ _ _ _ H) as [z [VV1 VV2]].
    exists (z::vals).
    split; econstructor; eauto.
Qed.

(** ** Transitivity Proper *)

Section Eff_sim_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3).

Lemma load_store_init_data_inject m1 m2 j1 
       (J: forall b, isGlobalBlock g1 b = true -> j1 b = Some(b,0))
       (PG1 : meminj_preserves_globals g1 j1) 
       (Inj12 : Mem.inject j1 m1 m2)
       (FindVars: forall i b, Genv.find_symbol g1 i = Some b -> Genv.find_symbol g2 i = Some b):
      forall il k b
      (LDI: Genv.load_store_init_data g1 m1 b k il)
      (G: isGlobalBlock g1 b = true),
   Genv.load_store_init_data g2 m2 b k il.
Proof. 
  induction il; simpl in *; intros. trivial.
  assert (Inj: forall ofs v1 chunk, Mem.load chunk m1 b ofs = Some v1 ->
      exists v2 : val,
      Mem.load chunk m2 b ofs = Some v2 /\ val_inject j1 v1 v2).
  { intros. specialize (Mem.load_inject j1 m1 m2 _ _ _ _ _ _ Inj12 H (J _ G)). rewrite Zplus_0_r; trivial. }
  destruct a.
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { destruct LDI; split; eauto.
      destruct (Inj _ _ _ H) as [v [A B]]. inv B; trivial. }
  { apply IHil; assumption. }
  { destruct LDI as [[b' [FS LD]] LSI].
    split; eauto. 
    destruct (Inj _ _ _ LD) as [v [A B]]. inv B.
    rewrite J in H1.
      inv H1. rewrite Int.add_zero in A.
      exists b2; eauto.
    eapply find_symbol_isGlobal; eassumption. } 
Qed.


Theorem eff_sim_trans: forall 
        (SIM12: @SM_simulation_inject _ _ _ _ _ _ Sem1 Sem2 g1 g2)
        (SIM23: @SM_simulation_inject _ _ _ _ _ _ Sem2 Sem3 g2 g3),
        @SM_simulation_inject _ _ _ _ _ _ Sem1 Sem3 g1 g3.
Proof. (*follows structure of forward_simulations_trans.injinj*)

  intros.
  destruct SIM12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 
      match_sm_wd12 genvs_dom_eq12 ginfos_pres12 match_genv12
      match_visible12 (*match_junk_inv12 match_restrict12*)
      match_sm_valid12 core_initial12 effcore_diagram12
      core_halted12 core_at_external12 eff_after_external12].  
  destruct SIM23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23 
      match_sm_wd23 genvs_dom_eq23 ginfos_pres23 match_genv23
      match_visible23 (*match_junk_inv23 match_restrict23*)
      match_sm_valid23 core_initial23 effcore_diagram23
      core_halted23 core_at_external23 eff_after_external23].
  eapply Build_SM_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d mu c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists mu1, exists mu2,                                 
          X=Some c2 /\ mu = compose_sm mu1 mu2 /\
          (locBlocksTgt mu1 = locBlocksSrc mu2 /\
           extBlocksTgt mu1 = extBlocksSrc mu2 /\
           (forall b, pubBlocksTgt mu1 b = true -> pubBlocksSrc mu2 b = true) /\
           (forall b, frgnBlocksTgt mu1 b = true -> frgnBlocksSrc mu2 b = true)) /\ 
          match_core12 d1 mu1 c1 m1 c2 m2 /\ match_core23 d2 mu2 c2 m2 c3 m3 /\
          (*pure_comp_ext mu1 mu2 m1 m2 /\*) full_ext mu1 mu2
      end).
{ (*well_founded*)
  eapply wf_clos_trans. 
  eapply well_founded_sem_compose_ord_eq_eq; assumption. }
{ (*match_sm_wd*) clear - match_sm_wd12 match_sm_wd23.
  intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 IFDL]]]]]]]]]; subst.
  specialize (match_sm_wd12 _ _ _ _ _ _ MC12).
  specialize (match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct INV as [INVa [INVb [INVc INVd]]].
  eapply (compose_sm_wd); eauto. }
{ (*genvs_domain_eq*)
  clear - genvs_dom_eq12 genvs_dom_eq23. eapply genvs_domain_eq_trans; eassumption. }
{ (* ginfos_preserved *) 
  clear - ginfos_pres12 ginfos_pres23.
  destruct ginfos_pres12 as [GvarInfo12 GfindSymb12].
  destruct ginfos_pres23 as [GvarInfo23 GfindSymb23].
  split; red; intros.
    specialize (GvarInfo12 b). specialize (GvarInfo23 b). unfold gvar_info_eq in *.
    destruct (Genv.find_var_info g1 b); destruct (Genv.find_var_info g3 b); trivial.
    destruct (Genv.find_var_info g2 b); try contradiction. 
    destruct GvarInfo12 as [A [B C]]. rewrite A, B, C. assumption.
    destruct (Genv.find_var_info g2 b); try contradiction.
    destruct (Genv.find_var_info g2 b); try contradiction.
  apply GfindSymb23. apply GfindSymb12. assumption. }
{ (*match_genv*)
  clear - genvs_dom_eq12 match_sm_wd12 match_genv12 match_genv23.
  intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct MC as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 IFDL]]]]]]]]]; subst.
  destruct (match_genv12 _ _ _ _ _ _ MC12) as [GE12a GE12b].
  destruct (match_genv23 _ _ _ _ _ _ MC23) as [GE23a GE23b].
  split. apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in GE12a.
         apply meminj_preserves_genv2blocks in GE23a.
         rewrite compose_sm_extern.
         solve [eapply meminj_preserves_globals_ind_compose; eassumption].
  apply GE12b. }
{ (*match_reach_closed*)
    clear - match_sm_wd12 match_visible12.
    intros. rename c2 into c3. rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 IFDL]]]]]]]]]; subst.
    simpl. rewrite vis_compose_sm. eapply match_visible12. eassumption. }
(*{ (*match_restrict'*)
  clear - match_sm_wd12 match_restrict12 match_restrict23 match_visible12 match_visible23.
    intros. rename c2 into c3. rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [XX [J [INV [MC12 [MC23 pure]]]]]]]]];
      subst; simpl.
    exists c2, m2, (restrict_sm mu12 X), mu23. (* (restrict_sm mu23 X').*)
    intuition;
    try (solve [unfold restrict_sm; destruct mu12, mu23; simpl; auto]).
    unfold compose_sm; f_equal; 
    try (solve [unfold restrict_sm; destruct mu12, mu23; simpl; auto]).
    { rewrite restrict_compose, restrict_sm_local.
      extensionality b.
      unfold compose_meminj, restrict.
      destruct (X b) eqn: Xb; auto.  }
    { rewrite restrict_compose, restrict_sm_extern.
      extensionality b.
      unfold compose_meminj, restrict.
      destruct (X b) eqn: Xb; auto. }

    (*full_ext*)
    (*Destructing mu12. THIS SHOULD BE A LEMMA*)
    generalize pure; clear pure.
    unfold restrict_sm, restrict, full_ext, full_comp.
    destruct mu12; simpl; intros.
    destruct (X b0) eqn:Xb0; eauto; inversion H4. (*Solves two goals*) }*)
{ (*sm_valid*)
    clear - match_sm_valid12 match_sm_valid23.
    intros. rename c2 into c3.  rename m2 into m3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 IFDL]]]]]]]]]; subst.
    specialize (match_sm_valid12 _ _ _ _ _ _ MC12).
    specialize (match_sm_valid23 _ _ _ _ _ _ MC23).
    unfold sm_valid, compose_sm. destruct mu12; destruct mu23; simpl in *.
    split; intros. eapply match_sm_valid12. apply H.
    eapply match_sm_valid23. apply H. }
{ (*initial_core*)
  clear - genvs_dom_eq12 ginfos_pres12 core_initial12 genvs_dom_eq23 ginfos_pres23 core_initial23.
   intros. rename m2 into m3. rename v into v3. rename vals2 into vals3. 
    (*assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). 
      eapply forall_valinject_hastype; eassumption.*)
    destruct (initial_inject_split _ _ _ H0) 
       as [m2 [j1 [j2 [J [Inj12 [Inj23 [X [Y [XX YY (*Pure*)]]]]]]]]].
    subst.
    destruct (forall_val_inject_split _ _ _ _ H1)
       as [vals2 [ValsInj12 ValsInj23]].
    assert (PG1: meminj_preserves_globals g1 j1).
      clear - X Y XX YY H2 H3.
      apply meminj_preserves_genv2blocks.
      apply meminj_preserves_genv2blocks in H2.
      destruct H2 as [AA [BB CC]].
      split; intros.
         specialize (AA _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         destruct (XX _ _ _ J1); subst. trivial.
      split; intros.
         specialize (BB _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. trivial.
      destruct (XX _ _ _ H0); subst. trivial.
  assert (GFI1: globalfunction_ptr_inject g1 j1).
    { clear - X Y XX YY H2 H3.
      intros b f Hfind.
      destruct (H3 b f Hfind); split; auto.
      apply compose_meminjD_Some in H. 
      destruct H as [b1 [ofs1 [ofs [U [R S]]]]]. rewrite S.
      rewrite U. apply XX in U. destruct U. subst b ofs1. rewrite <-S. auto. }
  assert (PG2: meminj_preserves_globals g2 j2).
  {
    clear - XX YY X Y PG1 H2 genvs_dom_eq12.
    apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in H2.
      destruct H2 as [AA [BB CC]].
     apply meminj_preserves_genv2blocks in PG1.
      destruct PG1 as [AA1 [BB1 CC1]].
      destruct genvs_dom_eq12.
      split; intros.
         apply H in H1.
         specialize (AA1 _ H1). specialize (AA _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         rewrite J1 in AA1. inv AA1. simpl in D. subst. trivial.
      split; intros.
         apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         rewrite J1 in BB1. inv BB1. simpl in D. subst. trivial.
      apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1). rename b2 into b3.
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX _ _ _ J1); subst. simpl in D. subst.
         clear BB1 XX.
         destruct (YY _ _ _ H2) as [XX | [XX | XX]].
           apply flatinj_E in XX. destruct XX as [? [? ?]]; subst. trivial.
           destruct XX as [? ?]; subst.
             apply (CC _ _ _ H1 H4).
           destruct XX as [mm [? ?]]; subst.
             apply (CC _ _ _ H1 H4). }
  assert (GFI2: globalfunction_ptr_inject g2 j2).
  { clear - XX YY X Y PG1 H2 H3 genvs_dom_eq12 GFI1.
    intros b f Hfind2.
    generalize genvs_dom_eq12 as GDE. intro.
    destruct genvs_dom_eq12 as [U [W R]].
    specialize (R b).
    destruct R.
    assert (exists f, Genv.find_funct_ptr g1 b = Some f).
    { apply H0. eauto. }
    destruct H1 as [f0 Hfind1].
    unfold globalfunction_ptr_inject in H3.
    destruct (H3 b f0 Hfind1); split; auto.
    apply compose_meminjD_Some in H1. 
    destruct H1 as [b1 [ofs1 [ofs [UU [R S]]]]]. rewrite S.
    destruct (GFI1 b f0 Hfind1).
    rewrite H1 in UU.
    inv UU.
    rewrite R.
    f_equal; auto. 
    rewrite <-(genvs_domain_eq_isGlobal _ _ GDE); auto. }

  assert (MRR2: mem_respects_readonly g2 m2). 
    { red; intros b gv'; intros.
      clear YY H0 H1 H2 H3 H4 H5 core_initial23 core_initial12 X Y.
      destruct ginfos_pres12 as [GVars12 FS12].
      destruct ginfos_pres23 as [GVars23 FS23].
      specialize (find_var_info_isGlobal _ _ _ H10); intros GB.
      specialize (meminj_preserves_globals_isGlobalBlock _ _ PG2 _ GB); intros J2b.
      rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in GB. 
      specialize (meminj_preserves_globals_isGlobalBlock _ _ PG1 _ GB); intros J1b.
      specialize (GVars12 b); red in GVars12. rewrite H10 in GVars12.
      remember (Genv.find_var_info g1 b) as fvi. symmetry in Heqfvi.
      destruct fvi; inv GVars12; try contradiction.
      destruct H1 as [GVrd GVvol]; rename H0 into GVInit.
      rewrite <- GVrd, <- GVvol, <- GVInit in *.
      destruct (H6 _ _ Heqfvi H11) as [LDinit1 [VB1 NPerm1]].
      split. eapply load_store_init_data_inject; try eassumption.
             intros. eapply meminj_preserves_globals_isGlobalBlock; eassumption.
      split. eapply Mem.valid_block_inject_2; eassumption.
      intros z N. 
      specialize (GVars23 b); red in GVars23. rewrite H10 in GVars23.
      remember (Genv.find_var_info g3 b) as fvi3. symmetry in Heqfvi3.
      destruct fvi3; inv GVars23; try contradiction.
      destruct H1 as [GVrd3 GVvol3]; rename H0 into GVInit3.
      rewrite GVrd, GVvol, GVInit, GVrd3, GVvol3, GVInit3 in *.
      destruct (H7 _ _ Heqfvi3 H11) as [LDinit3 [VB3 NPerm3]].
      eapply (NPerm3 z). exploit (Mem.perm_inject j2); try eassumption. 
      rewrite Zplus_0_r; trivial. }

  destruct (core_initial12 _ _ _ _ _ vals2 _ 
       DomS (fun b => match j2 b with None => false
                      | Some (b3,d) => DomT b3 end) H Inj12)
     as [d12 [c2 [Ini2 MC12]]]; try assumption.
    { intros. destruct (X b1) as [_ J1Comp]. 
              destruct J1Comp as [b3 [dd COMP]]. exists b2, d; trivial.
              specialize (H4 _ _ _ COMP).
              destruct (compose_meminjD_Some _ _ _ _ _ COMP)
                as [bb2 [dd1 [dd2 [J1 [J2 D]]]]]; subst; clear COMP.
              rewrite J1 in H10; inv H10. rewrite J2. apply H4. }
    { intros.
        assert (Q: forall b,  isGlobalBlock g2 b || getBlocks vals2 b = true ->
                   exists jb d, j2 b = Some (jb, d) /\ 
                           isGlobalBlock g3 jb || getBlocks vals3 jb = true).
          intros b' Hb'. apply orb_true_iff in Hb'. 
          destruct Hb' as [Hb' | Hb'].
            rewrite (meminj_preserves_globals_isGlobalBlock _ _ PG2 _ Hb').
              exists b', 0.
              rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in Hb'.
              rewrite Hb'. intuition.
          destruct (getBlocks_inject _ _ _  ValsInj23 _ Hb') as [bb [ofs [J2 GB2]]].
              exists bb, ofs. intuition.
        destruct (REACH_inject _ _ _ Inj23 
            (fun b' : block => isGlobalBlock g2 b' || getBlocks vals2 b')
            (fun b' : block => isGlobalBlock g3 b' || getBlocks vals3 b')
            Q _ H10) as [b3 [d2 [J2 R3]]].
        rewrite J2.
        destruct (Y _ _ _ J2) as [b1 [d COMP]].
        apply (H4 _ _ _ COMP). }
    { intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption. }
  destruct (core_initial23 _ _ _ _ _ vals3 _ 
        (fun b => match j2 b with None => false | Some (b3,d) => DomT b3 end) DomT Ini2 Inj23)
        as [d23 [c3 [Ini3 MC23]]]; try assumption. 
    { intros b2 b3 d2 J2. rewrite J2.
         destruct (Y _ _ _ J2) as [b1 [d COMP]].
         destruct (H4 _ _ _ COMP). split; trivial. }
    { intros b2 Hb2. remember (j2 b2) as d.
        destruct d; inv Hb2; apply eq_sym in Heqd. destruct p.
        eapply Mem.valid_block_inject_1; eassumption. }
  remember (initial_SM DomS
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) (REACH m1 (fun b => isGlobalBlock g1 b || getBlocks vals1 b))
                  (REACH m2 (fun b => isGlobalBlock g2 b || getBlocks vals2 b))
            j1) as mu1.
  remember (initial_SM
            (fun b : block =>
             match j2 b with
             | Some (b3, _) => DomT b3
             | None => false
             end) DomT (REACH m2 (fun b => isGlobalBlock g2 b || getBlocks vals2 b))
                       (REACH m3 (fun b => isGlobalBlock g3 b || getBlocks vals3 b))
             j2) as mu2.
  exists (d12,Some c2,d23).
  exists c3. 
  split; trivial. 
  exists c2, m2, mu1, mu2.
  split. auto.
  split. subst. unfold initial_SM, compose_sm; simpl.
           f_equal.
  split. subst; simpl. repeat (split; trivial).
  split; trivial.
  split; trivial.
  subst.
  
  (* FULL *)
  { unfold full_ext, full_comp, initial_SM; simpl.
    intros. move X at bottom. 
    assert (H7':exists (b2 : block) (d1 : Z), j1 b0 = Some (b2, d1)) by (exists b1, delta1; auto).
    apply X in H7'.
    destruct H7' as [b2 [delta2 HH]].
    clear - HH H10.
    unfold compose_meminj in HH; rewrite H10 in HH; simpl.
    destruct (j2 b1) eqn:result2.
    destruct p as [b2' delta2']; exists b2', delta2'; auto.
    inversion HH.
  }
 }
{ (*effcore_diagram*)
   clear - match_sm_wd12 match_sm_valid12 effcore_diagram12 
                         match_sm_wd23 match_sm_valid23 effcore_diagram23
                         genvs_dom_eq23 match_genv23.
   intros. rename st2 into st3. rename m2 into m3.
   destruct cd as [[d12 cc2] d23].
   destruct H0 as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 full]]]]]]]]]; subst.
   eapply effcore_diagram_trans;  eassumption.
}
{ (*halted*)
  clear - match_sm_wd12 core_halted12 match_sm_wd23 core_halted23.
  intros. rename c2 into c3. rename m2 into m3.  
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [mu12 [mu23 [X [J [INV [MC12 [MC23 full]]]]]]]]]; subst.
  destruct (core_halted12 _ _ _ _ _ _ _ MC12 H0) as
     [v2 [MInj12 [MRR1 [MRR2 [RValsInject12 HaltedMid]]]]]. 
  destruct (core_halted23 _ _ _ _ _ _ _ MC23 HaltedMid) as
     [v3 [MInj23 [_ [MRR3 [RValsInject23 HaltedTgt]]]]].
  exists v3.
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  destruct INV as [INVa [INVb [INVc INVd]]].
  split. rewrite compose_sm_as_inj; trivial.
           eapply Mem.inject_compose; eassumption.
  split; trivial.
  split. trivial.   
  split. rewrite compose_sm_as_inj; trivial.
         rewrite restrict_compose, vis_compose_sm; simpl.
         eapply val_inject_compose; try eassumption.
         eapply val_inject_incr; try eassumption.
         apply restrict_incr.
  assumption. }
{ (*at_external*)
  clear - match_sm_wd12 core_at_external12 match_sm_wd23 core_at_external23.
  intros. rename c2 into c3. rename m2 into m3.
  rename H0 into AtExtSrc. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 [MC23 full]]]]]]]]]. 
  subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExtSrc)
    as [MInj12 [MRR1 [MRR2 [vals2 [ArgsInj12 [AtExt2 SH12]]]]]]; 
     clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [MInj23 [_ [MRR3 [vals3 [ArgsInj23 [AtExtTgt SH23]]]]]]; 
     clear core_at_external23.
  rewrite compose_sm_as_inj; try eauto.   
    split. eapply Mem.inject_compose; eassumption.
    split; trivial.
    split; trivial.
    exists vals3.
    rewrite restrict_compose, vis_compose_sm; simpl.
    split. eapply forall_val_inject_compose; try eassumption.
           eapply forall_vals_inject_restrictD; eassumption.
    split. assumption.
    destruct GLUEINV as [GlueL [GlueE [GlueP GlueF]]].                    
    rewrite compose_sm_exportedSrc; eauto.                    
    rewrite compose_sm_exportedTgt.
    intros. destruct (SH12 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC12 INJJ12].
            destruct (SH23 _ _ (eq_refl _) (eq_refl _) _ (eq_refl _)) as [MCC23 INJJ23].
            assert (HNU: nu = compose_sm
                 (replace_locals mu12 (fun b : block => locBlocksSrc mu12 b && REACH m1 (exportedSrc mu12 vals1) b)
                                      (fun b : block => locBlocksTgt mu12 b && REACH m2 (exportedTgt mu12 vals2) b))
                 (replace_locals mu23 (fun b : block => locBlocksSrc mu23 b && REACH m2 (exportedSrc mu23 vals2) b)
                                      (fun b : block => locBlocksTgt mu23 b && REACH m3 (exportedTgt mu23 vals3) b))).
              subst nu. unfold compose_sm; simpl. f_equal. 
              rewrite replace_locals_locBlocksSrc. trivial.
              rewrite replace_locals_locBlocksTgt. trivial.
              subst pubSrc'. rewrite replace_locals_pubBlocksSrc. trivial. 
              subst pubTgt'. rewrite replace_locals_pubBlocksTgt. trivial.
              do 2 rewrite replace_locals_local. trivial.
              rewrite replace_locals_extBlocksSrc. trivial.
              rewrite replace_locals_extBlocksTgt. trivial.
              rewrite replace_locals_frgnBlocksSrc. trivial.
              rewrite replace_locals_frgnBlocksTgt. trivial.
              do 2 rewrite replace_locals_extern. trivial.
            split. exists st2, m2.
                   eexists; eexists; split. trivial. split. eassumption. 
                   rewrite replace_locals_locBlocksTgt, replace_locals_locBlocksSrc,
                           replace_locals_extBlocksTgt, replace_locals_extBlocksSrc,
                           replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc,
                           replace_locals_frgnBlocksTgt, replace_locals_frgnBlocksSrc.
                   intuition. 
                   rewrite GlueL in H. apply andb_true_iff in H. destruct H. 
                     apply andb_true_iff. split; trivial.
                     eapply REACH_mono; try eassumption.
                     unfold exportedSrc, exportedTgt, sharedTgt. rewrite sharedSrc_iff_frgnpub; trivial.
                     intros. do 2 (rewrite orb_true_iff in H1).
                             destruct H1. rewrite H1; trivial.
                             destruct H1. apply GlueF in H1. intuition. apply GlueP in H1. intuition. eauto.
        (* Full here *)
        { unfold full_ext, full_comp, replace_locals; simpl.
          destruct mu12; destruct mu23; simpl.
          exact full.
        }

        rewrite HNU. rewrite compose_sm_shared.
              eapply Mem.inject_compose; eassumption.
            rewrite replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc. 
              intros. rewrite GlueL in H. apply andb_true_iff in H. destruct H. 
                     apply andb_true_iff. split; trivial.
                     eapply REACH_mono; try eassumption.
                     unfold exportedSrc, exportedTgt, sharedTgt. rewrite sharedSrc_iff_frgnpub; trivial.
                     intros. do 2 (rewrite orb_true_iff in H1).
                             destruct H1. rewrite H1; trivial.
                             destruct H1. apply GlueF in H1. intuition. apply GlueP in H1. intuition. eauto.
            rewrite replace_locals_frgnBlocksTgt, replace_locals_frgnBlocksSrc. trivial.
            apply match_sm_wd12 in MC12. 
              apply replace_locals_wd; trivial.
              intros. apply andb_true_iff in H; destruct H. 
                apply forall_vals_inject_restrictD in ArgsInj12.
                exploit (REACH_local_REACH mu12); try eassumption.
                intros [b2 [d [LOC RCH2]]].
                exists b2, d. rewrite LOC, RCH2. 
                destruct (local_DomRng _ MC12 _ _ _ LOC). rewrite H2; split; trivial.
              intros. apply andb_true_iff in H; destruct H.
                rewrite H; trivial.
            apply match_sm_wd23 in MC23. 
              apply replace_locals_wd; trivial.
              intros. apply andb_true_iff in H; destruct H. 
                apply forall_vals_inject_restrictD in ArgsInj23.
                exploit (REACH_local_REACH mu23); try eassumption.
                intros [b2 [d [LOC RCH2]]].
                exists b2, d. rewrite LOC, RCH2. 
                destruct (local_DomRng _ MC23 _ _ _ LOC). rewrite H2; split; trivial.
              intros. apply andb_true_iff in H; destruct H.
                rewrite H; trivial. 
  eapply GLUEINV. 
  eapply GLUEINV. }
{ (*after_external*)
  clear - match_sm_wd12 match_sm_valid12 core_at_external12 
          eff_after_external12  match_visible12 (*match_restrict12*)
          match_sm_wd23 match_sm_valid23 core_at_external23 
          eff_after_external23 genvs_dom_eq23 match_genv12 match_genv23
          ginfos_pres23 ginfos_pres12 genvs_dom_eq12.
  intros. rename st2 into st3. rename m2 into m3. 
          rename vals2 into vals3'. rename m2' into m3'.
          rename UnchLOOR into UnchLOOR13. rename RDO2 into RDO3.
  destruct cd as [[d12 cc2] d23].
  destruct MatchMu as [st2 [m2 [mu12 [mu23 [Hst2 [HMu [GLUEINV [MC12 [MC23 full]]]]]]]]].
  assert (WDmu12:= match_sm_wd12 _ _ _ _ _ _ MC12).
  assert (WDmu23:= match_sm_wd23 _ _ _ _ _ _ MC23).
  remember (fun b => locBlocksSrc mu12 b || frgnBlocksSrc mu12 b || mapped (as_inj (compose_sm mu12 mu23)) b ) as RESTR.
  assert (NormMC12: match_core12 d12 mu12 st1 m1 st2 m2) by assumption.
  (*assert (NormMC12: match_core12 d12 (restrict_sm mu12 RESTR) st1 m1 st2 m2).
     apply match_restrict12. apply MC12.
     subst RESTR. clear. intuition.
     subst RESTR.
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu' 
              SMvalNu' WDnu' (*SEP*) INC m3' ret2 m1' ret1 (*nu'*) NuHyp (*nu*)
              (* GlobalsSeparate: SMvalNu' WDnu' INC m3' ret2 m1' ret1 NuHyp *)
              pubTgtHyp pubTgt' pubSrcHyp pubSrc' ValInjMu AtExtTgt 
              AtExtSrc eff_after_external23 core_at_external23 
              eff_after_external12 core_at_external12 HasTy1 HasTy2. 
     subst. intros b Hb. 
    (* generalize (match_visible12 _ _ _ _ _ _ MC12); unfold REACH_closed; intros.
     apply H. apply Hb.*)
     
      rewrite REACHAX in Hb.
      destruct Hb as [L HL].
      generalize dependent b.
      induction L; simpl; intros; inv HL.
      apply H.
      specialize (IHL _ H1); clear H1.
        apply orb_true_iff in IHL. apply orb_true_iff.
        destruct IHL.
          left. eapply (match_visible12 _ _ _ _ _ _ MC12).
                eapply REACH_cons; try eassumption.
                apply REACH_nil. apply H.
          right. eapply (inject_REACH_closed _ _ _ MemInjMu).
                eapply REACH_cons; try eassumption.
                apply REACH_nil. apply H.*)
  (*remember (restrict_sm mu12 RESTR) as nmu12.*)
  remember mu12 as nmu12.
  assert (HmuNorm: mu = compose_sm nmu12 mu23).
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu' 
              SMvalNu' WDnu' (*SEP*) INC ret2 ret1 (*nu'*) NuHyp (*nu*)
              (* GlobalsSeparate: SMvalNu' WDnu' INC ret2 m1' ret1 NuHyp*)
              pubTgtHyp pubTgt' pubSrcHyp pubSrc' ValInjMu AtExtTgt 
              AtExtSrc eff_after_external23 core_at_external23 
              eff_after_external12 core_at_external12 HasTy1 HasTy2. 
      subst nmu12 mu RESTR. unfold compose_sm; simpl.
          auto.
          (*rewrite restrict_sm_extern.
          rewrite (restrict_sm_local' _ WDmu12).
          Focus 2. clear. intuition.
          unfold restrict_sm; simpl. 
          destruct mu12; simpl in *.
          f_equal. 
          extensionality b. unfold compose_meminj, restrict, mapped, as_inj, join; simpl.
          remember (extern_of b) as d.
          specialize (disjoint_extern_local _ WDmu12 b); simpl; intros DD.
          destruct d; trivial; apply eq_sym in Heqd.
            destruct p as [b2 d1].
            destruct DD; try congruence.
            rewrite H.
            destruct (extern_DomRng _ WDmu12 _ _ _ Heqd); simpl in *.
            assert (EE:= extBlocksSrc_locBlocksSrc _ WDmu12 _ H0); simpl in *.
            rewrite EE; simpl.
            remember (frgnBlocksSrc b) as q.
            destruct q; apply eq_sym in Heqq; simpl in *. reflexivity.
            remember (StructuredInjections.extern_of mu23 b2) as w.
            destruct w; trivial. destruct p. rewrite <- Heqw. trivial.  
         remember (locBlocksSrc b) as q. 
         destruct q; simpl; trivial.
         remember (frgnBlocksSrc b) as w.
         destruct w; trivial; simpl; apply eq_sym in Heqw.
         remember (local_of b) as t.
         destruct t; simpl; trivial.
         destruct p; apply eq_sym in Heqt.
         destruct (local_DomRng _ WDmu12 _ _ _ Heqt); simpl in *. congruence.*)  
  clear MC12. 
  assert (WDnmu12:= match_sm_wd12 _ _ _ _ _ _ NormMC12).
  clear HMu.
  assert (WDmu: SM_wd (compose_sm nmu12 mu23)).
    eapply compose_sm_wd; try eassumption.
      subst. unfold restrict_sm, restrict; simpl. destruct mu12; simpl in *. apply GLUEINV.
      subst. unfold restrict_sm, restrict; simpl. destruct mu12; simpl in *. apply GLUEINV.
  clear (*match_restrict12*) match_visible12.
  assert (mu12_valid:= match_sm_valid12 _ _ _ _ _ _ NormMC12).
  assert (mu23_valid:= match_sm_valid23 _ _ _ _ _ _ MC23).
  rename ret2 into ret3.  
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ NormMC12 AtExtSrc)
   as [MInj12 [MRR1 [MRR2 [vals2 [ArgsInj12 (*[ArgsHT2*) [AtExt2 _](*]*)]]]]]; clear core_at_external12.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
   as [MInj23 [_ [MRR3 [vals3 [ArgsInj23 (*[ArgsHT3*) [AtExt3 _](*]*)]]]]]; clear core_at_external23.
  
  (** Prove uniqueness of e, ef_sig, vals3. We do this by hand, instead of 
     rewrite AtExtTgt in AtExt3; inv Atext3 in order to avoid the subst
     that's inherent in inv AtExt3. Probably there's a better way to do this... *)
  assert (e' = e /\ ef_sig' = ef_sig /\ vals3'=vals3).
     rewrite AtExtTgt in AtExt3. inv AtExt3. intuition.
  destruct H as [HH1 [HH2 HH3]].
  rewrite HH1, HH2, HH3 in *. clear HH1 HH2 HH3 e' ef_sig' vals3' AtExt3.

  specialize (eff_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ MInj12 
        NormMC12 AtExtSrc AtExt2 ArgsInj12
        _ (eq_refl _) _ (eq_refl _) _ (eq_refl _)). 
  specialize (eff_after_external23 _ _ _ _ _ _ _ _ _ 
      _ _ _ MInj23 MC23 AtExt2 AtExtTgt ArgsInj23 _ (eq_refl _) 
      _ (eq_refl _) _ (eq_refl _)).
  assert (LeakedCompSrc: locBlocksSrc mu = locBlocksSrc nmu12 /\
                         extBlocksSrc mu = extBlocksSrc nmu12 /\
                        exportedSrc mu vals1 = exportedSrc nmu12 vals1). 
     subst. clear - WDnmu12 WDmu. simpl.
        (*rewrite restrict_sm_locBlocksSrc.
        rewrite restrict_sm_extBlocksSrc.
         rewrite restrict_sm_frgnBlocksSrc, restrict_sm_pubBlocksSrc.*)
        unfold exportedSrc. 
        rewrite sharedSrc_iff_frgnpub; trivial. simpl. 
        rewrite sharedSrc_iff_frgnpub; trivial.
        intuition.
  destruct LeakedCompSrc as [LSa [LSb LSc]]. 
    rewrite LSa, LSc in *. clear LSa LSb LSc.
  assert (LeakedCompTgt: locBlocksTgt mu = locBlocksTgt mu23 
                       /\ extBlocksTgt mu = extBlocksTgt mu23 
                       /\ exportedTgt mu vals3 = exportedTgt mu23 vals3).
     subst. clear - WDmu23 WDmu. simpl.  
        unfold exportedTgt, sharedTgt. simpl. intuition. 
  destruct LeakedCompTgt as [LTa [LTb LTc]]. 
    rewrite LTa, LTc in *. clear LTa LTb LTc.
   remember (fun b => locBlocksTgt nmu12 b && 
             REACH m2 (exportedTgt nmu12 vals2) b) as pubTgtMid'.
   remember (fun b => locBlocksSrc mu23 b && 
             REACH m2 (exportedSrc mu23 vals2) b) as pubSrcMid'.
   assert (MID: forall b, pubTgtMid' b = true -> pubSrcMid' b = true).
        clear eff_after_external12 match_sm_valid23 eff_after_external23.
        rewrite HeqpubTgtMid', HeqpubSrcMid'. 
        destruct GLUEINV as [GlueA [GlueB [GlueC GlueD]]].
        subst.
        clear UnchLOOR13 UnchPrivSrc (*SEP*) INC MemInjMu ArgsInj12 MInj12.
        (*rewrite restrict_sm_locBlocksTgt.*) (*sm_extern_normalize_exportedTgt; trivial.*)
           rewrite GlueA. intros b Hb. rewrite andb_true_iff in *.
        destruct Hb. split; trivial.
        eapply REACH_mono; try eassumption.
        unfold exportedTgt, exportedSrc, sharedTgt.
        (*rewrite restrict_sm_frgnBlocksTgt, restrict_sm_pubBlocksTgt.*)
        rewrite sharedSrc_iff_frgnpub; trivial.
        intros. repeat rewrite orb_true_iff in *.
        intuition.
  assert (NU: nu = compose_sm (replace_locals nmu12 pubSrc' pubTgtMid')
              (replace_locals mu23 pubSrcMid' pubTgt')).
     clear frgnSrcHyp frgnTgtHyp eff_after_external23.
     subst. unfold compose_sm; simpl.
     rewrite replace_locals_extern, replace_locals_local,
             replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt,
            replace_locals_extBlocksSrc, replace_locals_extBlocksTgt.
     rewrite replace_locals_extern, replace_locals_local.
     (*rewrite restrict_sm_extBlocksSrc, restrict_sm_locBlocksSrc,
             restrict_sm_local, restrict_sm_extern.*)
     f_equal. 

  clear NuHyp.
  (*produce all the hypothesis necessary for applying interpolation*)
  assert (MinjNu12: Mem.inject (as_inj (replace_locals nmu12 pubSrc' pubTgtMid')) m1 m2).
     rewrite replace_locals_as_inj. assumption.
  assert (MinjNu23: Mem.inject (as_inj (replace_locals mu23 pubSrcMid' pubTgt')) m2 m3).
     rewrite replace_locals_as_inj. assumption.
  assert (ArgsInj12R: Forall2
    (val_inject
       (as_inj
          (restrict_sm mu12
             (fun b : block =>
              locBlocksSrc mu12 b || frgnBlocksSrc mu12 b
              || mapped (as_inj (compose_sm mu12 mu23)) b)))) vals1 vals2).
      clear - ArgsInj12 Heqnmu12 HeqRESTR.
      rewrite restrict_sm_all. subst. (*rewrite restrict_sm_all in ArgsInj12.
       rewrite restrict_nest in ArgsInj12. *)
       eapply val_list_inject_forall_inject.
       apply forall_inject_val_list_inject in ArgsInj12.
       eapply val_list_inject_incr; try eassumption.
       red; intros. destruct (restrictD_Some _ _ _ _ _ H); clear H.
          unfold vis in H1. (*rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc in H1.*)
          apply restrictI_Some; intuition.
    (*intros. rewrite effect_properties.vis_restrict_sm in H.
      unfold vis in H. intuition. 
  clear ArgsInj12.*) 
  assert (ArgsInj12': Forall2 (val_inject (as_inj nmu12) )
                vals1 vals2).
       move ArgsInj12 at bottom. 
       clear - ArgsInj12.
       induction ArgsInj12; econstructor.
       eapply val_inject_restrictD; eauto.
       assumption.

  assert (WDnu12: SM_wd (replace_locals nmu12 pubSrc' pubTgtMid')).
       subst.
       eapply replace_locals_wd; try eassumption.
         intros. apply andb_true_iff in H.
           destruct H as [locB R].
           destruct (REACH_local_REACH _ WDnmu12 _ _ _ _ 
              MInj12 (*ArgsInj12R*) ArgsInj12' _ R locB) as [b2 [d1 [LOC12 R2]]].
           exists b2, d1; split; trivial.
           rewrite andb_true_iff, R2.
           split; trivial.
           eapply local_locBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H. 
  assert (ArgsInj23R: Forall2 (val_inject (as_inj mu23)) vals2 vals3).
       eapply val_list_inject_forall_inject.
       apply forall_inject_val_list_inject in ArgsInj23.
       eapply val_list_inject_incr; try eassumption.
       apply restrict_incr.
  clear ArgsInj23.
  assert (WDnu23: SM_wd (replace_locals mu23 pubSrcMid' pubTgt')).
       subst. 
       eapply replace_locals_wd; try eassumption.
       destruct GLUEINV as [GIa [GIb [GIc GId]]]. subst. 
       intros b2; intros. apply andb_true_iff in H.
           destruct H as [locB R].
           destruct (REACH_local_REACH _ WDmu23 _ _ _ _ 
              MInj23 ArgsInj23R _ R locB) as [b3 [d2 [LOC23 R3]]].
           exists b3, d2; split; trivial.
           rewrite andb_true_iff, R3.
           split; trivial.
           eapply local_locBlocks; eassumption.
         intros. apply andb_true_iff in H. apply H.
  assert (nu12_valid: sm_valid (replace_locals nmu12 pubSrc' pubTgtMid') m1 m2).
     split. rewrite replace_locals_DOM. eapply mu12_valid.
     rewrite replace_locals_RNG. eapply mu12_valid.
  assert (nu23_valid: sm_valid (replace_locals mu23 pubSrcMid' pubTgt') m2 m3).
     split. rewrite replace_locals_DOM. eapply mu23_valid.
     rewrite replace_locals_RNG. eapply mu23_valid.
  rewrite NU in INC(*, SEP*). red in MRR3. red in FwdSrc. unfold readonly in FwdSrc.
(*  destruct (EFFAX.effect_interp_II _ _ _ MinjNu12 _ FwdSrc
      _ _ MinjNu23 _ FwdTgt nu' WDnu' SMvalNu' MemInjNu'
      INC (*Pure*) nu12_valid nu23_valid)
     as [m2' [nu12' [nu23' [X [Incr12 [Incr23 (*[Pure'*) [MInj12'
        [Fwd2 [MInj23' [nu12'valid
        [nu23'valid [GLUEINV' [full' [UnchMidA [UnchMidB [Pure12 Pure23]]]]]]]]]]]]]]]]; simpl in *.*)
  (*remember (fun b => match Genv.find_var_info g1 b with 
                        None => false
                      | Some gv => gvar_readonly gv && negb (gvar_volatile gv) end) as B.*)
  destruct (EFFAX.effect_interp_II _ _ _ MinjNu12 _ FwdSrc
      _ _ MinjNu23 _ FwdTgt nu' WDnu' SMvalNu' MemInjNu'
      INC (*Pure*) nu12_valid nu23_valid) with (B:=ReadOnlyBlocks g1)
     as [m2' [nu12' [nu23' [X [Incr12 [Incr23 (*[Pure'*) [MInj12'
        [Fwd2 [RDO2 [MInj23' [nu12'valid
        [nu23'valid [GLUEINV' [full' [UnchMidA [UnchMidB [Pure12 Pure23]]]]]]]]]]]]]]]]]; simpl in *.
    (*discharge the unchOn application conditions*)
       subst; apply UnchPrivSrc.
       subst. apply UnchLOOR13. 
    (*discharge the GLUE application condition*)
      rewrite replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
            replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
            replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
            replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt.
      destruct GLUEINV as [GLUEa [GLUEb [GLUEc GLUEd]]].
      repeat (split; trivial).
      (*subst. rewrite restrict_sm_locBlocksTgt; trivial.
      subst. rewrite restrict_sm_extBlocksTgt; trivial.
      subst. rewrite restrict_sm_frgnBlocksTgt; trivial.*)
      (* NORM HERE*)
      { unfold full_ext, full_comp, replace_locals; simpl.
        subst nmu12.  
        destruct mu12; destruct mu23; simpl.
        exact full.
        }
      { (*RDOnly_inj12*)
         unfold ReadOnlyBlocks. subst nmu12. clear - NormMC12 match_genv12 ginfos_pres12 WDmu12 MRR1 MRR2.
         red; intros. remember (Genv.find_var_info g1 b) as d.
         destruct d; inversion Hb; clear Hb. symmetry in Heqd.
         specialize (find_var_info_isGlobal _ _ _ Heqd). intros GB1.
         rewrite replace_locals_extern, replace_locals_as_inj.
         destruct (match_genv12 _ _ _ _ _ _ NormMC12).
         destruct ginfos_pres12 as [GP12a GP12b].
         destruct (gvar_infos_eqD _ _ GP12a _ _ Heqd) as [gv2 [FV2 [gvInit12 [gvRDO12 gvVol12]]]].
          split. apply (meminj_preserves_globals_isGlobalBlock _ _ H _ GB1).
          split. intros; symmetry.
                 apply effect_properties.match_genv_meminj_preserves_extern_iff_all in H; trivial.
                 eapply H; eassumption.
          intros. split. eapply MRR1; eassumption.  
                  rewrite gvRDO12, gvVol12 in *. eapply MRR2; eassumption. }
       { (*RDOnly_inj23*)
         unfold ReadOnlyBlocks.
         clear - NormMC12 match_genv12 ginfos_pres12 genvs_dom_eq12 WDmu12 MRR1
                         MC23 match_genv23 ginfos_pres23 WDmu23 MRR2 MRR3.
         red; intros. remember (Genv.find_var_info g1 b) as d.
         destruct d; inversion Hb; clear Hb. symmetry in Heqd.
         specialize (find_var_info_isGlobal _ _ _ Heqd). intros GB1.
         rewrite replace_locals_extern, replace_locals_as_inj.
         destruct (match_genv23 _ _ _ _ _ _ MC23).
         assert (GB2: isGlobalBlock g2 b = true).
           rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12); trivial.
         destruct ginfos_pres12 as [GP12a GP12b].
         destruct (gvar_infos_eqD _ _ GP12a _ _ Heqd) as [gv2 [FV2 [gvInit12 [gvRDO12 gvVol12]]]].
         destruct ginfos_pres23 as [GP23a GP23b].
         destruct (gvar_infos_eqD _ _ GP23a _ _ FV2) as [gv3 [FV3 [gvInit23 [gvRDO23 gvVol23]]]].
          split. apply (meminj_preserves_globals_isGlobalBlock _ _ H _ GB2).
          split. intros; symmetry.
                 apply effect_properties.match_genv_meminj_preserves_extern_iff_all in H; trivial.
                 eapply H; eassumption.
          intros. rewrite gvRDO12, gvVol12 in *. 
                  split. eapply MRR2; eassumption.  
                  rewrite gvRDO23, gvVol23 in *. eapply MRR3; eassumption. }
       { (*RDOnly_fwd1*) assumption. }
       { (*RDOnly_fwd3*)
         rewrite (gvar_infos_eq_ReadOnlyBlocks g1 g2); try eapply ginfos_pres12.
         rewrite (gvar_infos_eq_ReadOnlyBlocks g2 g3); try eapply ginfos_pres23.
         assumption. }
       { (*BSep*) 
         unfold ReadOnlyBlocks; subst nmu12; simpl; intros.
         remember (Genv.find_var_info g1 b2) as q. 
         destruct q; trivial. symmetry in Heqq.
         rewrite <- NU in H.
         specialize (find_var_info_isGlobal _ _ _ Heqq);
         rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12),
                 (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23),
                 (GSep _ _ _ H H0). discriminate. }
     { (*full_ext *)  
        unfold full_ext, full_comp, replace_locals.
        destruct nmu12, mu23; simpl. exact full. }    
 
      (*discharge the Norm Hypothesis*)
      (*rewrite Heqnmu12. do 2 rewrite replace_locals_extern.
      (*rewrite restrict_sm_extern.*)
      intros. (*destruct (restrictD_Some _ _ _ _ _ H) as [EX12 RR]; clear H.*)
      subst RESTR nmu12.
     clear UnchLOOR13 UnchPrivSrc Mu'Hyp mu' frgnTgtHyp frgnTgt'
              frgnSrcHyp frgnSrc' FwdTgt FwdSrc RValInjNu' MemInjNu' 
              SMvalNu' WDnu' (*SEP*) INC m3' m1' ret1 (*nu'*) 
              pubTgtHyp pubSrcHyp ValInjMu AtExtTgt 
              AtExtSrc eff_after_external23 
              eff_after_external12 MinjNu23 HasTy1 HasTy2. 
      destruct (extern_DomRng _ WDmu12 _ _ _ EX12).
      rewrite (extBlocksSrc_locBlocksSrc _ WDmu12 _ H) in RR; simpl in *.
      remember (frgnBlocksSrc mu12 b1) as d.
      destruct d; apply eq_sym in Heqd.
        destruct (frgnSrc _ WDmu12 _ Heqd) as [bb2 [dd1 [Frg1 FT2]]]; clear Heqd.
        apply foreign_in_extern in Frg1. rewrite Frg1 in EX12; inv EX12.
        destruct GLUEINV as [_ [_ [_ FF]]]. apply FF in FT2.
        destruct (frgnSrc _ WDmu23 _ FT2) as [b3 [d2 [Frg2 FT3]]]; clear FT2.
        rewrite (foreign_in_extern _ _ _ _ Frg2). exists b3, d2; trivial.
      simpl in RR. destruct (mappedD_true _ _ RR) as [[bb dd] M]; clear RR.
        destruct (joinD_Some _ _ _ _ _ M) as [EXT | [EXT LOC]]; clear M;
          rewrite compose_sm_extern in EXT.
          destruct (compose_meminjD_Some _ _ _ _ _ EXT) as [bb2 [dd1 [dd2 [E1 [E2 D]]]]].
          rewrite EX12 in E1. inv E1. rewrite E2. exists bb, dd2; trivial.
        rewrite compose_sm_local in LOC.
          destruct (compose_meminjD_Some _ _ _ _ _ LOC) as [bb2 [dd1 [dd2 [E1 [E2 D]]]]].
          destruct (disjoint_extern_local _ WDmu12 b1); congruence.*)
  assert (UnchMidC : Mem.unchanged_on (local_out_of_reach (replace_locals mu23 pubSrcMid' pubTgt') m2) m3 m3').
    clear - WDmu23 HeqpubTgtMid' HeqpubSrcMid' MinjNu12 UnchLOOR13 WDnu12 NU pubSrcHyp Heqnmu12 HeqRESTR GLUEINV.
    subst nmu12.
    remember (replace_locals (*restrict_sm mu12 RESTR*) mu12 pubSrc' pubTgtMid') as kappa12.
    remember (replace_locals mu23 pubSrcMid' pubTgt') as kappa23.
    assert (GluePubKappa : forall b : block,
          pubBlocksTgt kappa12 b = true -> pubBlocksSrc kappa23 b = true).
       clear UnchLOOR13 WDnu12 MinjNu12.
       subst kappa12 kappa23. rewrite replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt.
       subst. (*rewrite restrict_sm_locBlocksTgt;*) intros; trivial.
              apply andb_true_iff in H. destruct H.
              destruct GLUEINV as [Ga [Gb [Gc Gd]]]. rewrite Ga in H.
              rewrite H; simpl.
              eapply REACH_mono; try eassumption.
              unfold exportedTgt, exportedSrc, sharedTgt. rewrite sharedSrc_iff_frgnpub.
              (*rewrite restrict_sm_frgnBlocksTgt, restrict_sm_pubBlocksTgt.*)
              intros. do 2 rewrite orb_true_iff in H1.
                do 2 rewrite orb_true_iff. intuition.
           assumption.
    clear Heqkappa12 Heqkappa23 GLUEINV.
    subst.
    unfold local_out_of_reach.
    split; intros; rename b into b3.
      destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl. 
        split; simpl; trivial.
        intros b1; intros; simpl in *. 
        remember (pubBlocksSrc kappa12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePubKappa in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MinjNu12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
    destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl. 
        split; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc kappa12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePubKappa in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MinjNu12. eapply pub_in_all; try eassumption. apply N.
          rewrite H in PubTgt2. discriminate.
    

  (*next, prepare for application of eff_after_external12*)
  destruct GLUEINV' as [WDnu12' [WDnu23' [GLUEa' [GLUEb' [GLUEc' GLUEd']]]]].
  assert (H: exists ret2, val_inject (as_inj nu12') ret1 ret2 /\ 
                       val_inject (as_inj nu23') ret2 ret3 (*/\
                       Val.has_type ret2 (proj_sig_res ef_sig)*)). 
    subst. 
    rewrite compose_sm_as_inj in RValInjNu'; trivial.
    destruct (val_inject_split _ _ _ _ RValInjNu')
      as [ret2 [RValInjNu12' RValInjNu23']].  
    exists ret2. repeat (split; trivial).
    (*eapply valinject_hastype; eassumption.*)
  destruct H as [ret2 [RValInjNu12' (*[*)RValInjNu23' (*RetType2]*)]].
  subst. 
  assert (HasTy12: Val.has_type ret2 (proj_sig_res (AST.ef_sig e))). 
  { clear - HasTy2 RValInjNu23'. inv RValInjNu23'; auto. constructor. }
  (* OLD VERSION: assert (GSep2: globals_separate g2
                           (replace_locals
                              (restrict_sm mu12
                                 (fun b : block =>
                                  locBlocksSrc mu12 b || frgnBlocksSrc mu12 b
                                  || mapped (as_inj (compose_sm mu12 mu23)) b))
                              (fun b : block =>
                               locBlocksSrc
                                 (restrict_sm mu12
                                    (fun b0 : block =>
                                     locBlocksSrc mu12 b0
                                     || frgnBlocksSrc mu12 b0
                                     || mapped
                                          (as_inj (compose_sm mu12 mu23)) b0))
                                 b &&
                               REACH m1
                                 (exportedSrc
                                    (restrict_sm mu12
                                       (fun b0 : block =>
                                        locBlocksSrc mu12 b0
                                        || frgnBlocksSrc mu12 b0
                                        || mapped
                                             (as_inj (compose_sm mu12 mu23))
                                             b0)) vals1) b)
                              (fun b : block =>
                               locBlocksTgt
                                 (restrict_sm mu12
                                    (fun b0 : block =>
                                     locBlocksSrc mu12 b0
                                     || frgnBlocksSrc mu12 b0
                                     || mapped
                                          (as_inj (compose_sm mu12 mu23)) b0))
                                 b &&
                               REACH m2
                                 (exportedTgt
                                    (restrict_sm mu12
                                       (fun b0 : block =>
                                        locBlocksSrc mu12 b0
                                        || frgnBlocksSrc mu12 b0
                                        || mapped
                                             (as_inj (compose_sm mu12 mu23))
                                             b0)) vals2) b)) nu12') by ad_it. *)
  assert (GSep2: globals_separate g2
    (replace_locals mu12
       (fun b : block =>
        locBlocksSrc mu12 b && REACH m1 (exportedSrc mu12 vals1) b)
       (fun b : block =>
        locBlocksTgt mu12 b && REACH m2 (exportedTgt mu12 vals2) b)) nu12').
  { unfold globals_separate in *.
  intros. 
  destruct (isGlobalBlock g2 b2) eqn:Globb2; try trivial.
  rewrite <- Globb2.
  rewrite (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23).
  eapply GSep.
  Lemma compose_sm_None1:
      forall mu mu' b,
        as_inj mu b = None ->
        as_inj (compose_sm mu mu') b = None.
      intros.
      unfold compose_sm.
      unfold as_inj, join in *.
      destruct (extern_of mu b) eqn: extofb; try solve[ destruct p; simpl H; inversion H]; simpl.
      unfold compose_meminj.
      rewrite extofb, H; trivial.
     Qed.
  apply (compose_sm_None1 _ _ _ H).

  assert (extern_of nu23' b2 = Some (b2, 0)).
  {
  eapply Incr23.
  rewrite replace_locals_extern.
  eapply meminj_preserves_globals_isGlobalBlock.
  apply match_genv23 in MC23.
  destruct MC23 as [MPG global_frgn].
  eapply MPG.
  exact Globb2.
  }
  assert (extern_of nu12' b1 = Some (b2, d)).
  {
    unfold as_inj, join in H0; simpl in H0.
    destruct (extern_of nu12' b1) eqn:extofb1.
    + destruct p.
      exact H0.
    + apply WDnu23' in H1.
      destruct H1 as [extS23' extTgt23'].
      rewrite <- GLUEb' in extS23'.
      apply (local_locBlocks _ WDnu12') in H0; destruct H0 as
      [locS [locT [extS [extT ?]]]].
      rewrite extT in extS23'.
      discriminate extS23'.
  }
  unfold compose_sm, compose_meminj, as_inj, join; simpl.
  rewrite H2.
  rewrite H1.
  reflexivity. }
  
  specialize (eff_after_external12 nu12' ret1 
     m1' ret2 m2' HasTy1 HasTy12 Incr12 GSep2 WDnu12' nu12'valid MInj12' RValInjNu12'
     FwdSrc Fwd2 (*RetType2*)).
  rewrite (gvar_infos_eq_ReadOnlyBlocks g1 g2) in RDO2; try eapply ginfos_pres12.
  destruct (eff_after_external12 RDO1 RDO2 _ (eq_refl _) 
      _ (eq_refl _) _ (eq_refl _))
    as [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear eff_after_external12.
   (*discharge unchangedOn-application conditions*)
      apply UnchPrivSrc.
      apply UnchMidB.

  (*next, apply eff_after_external23*)

  specialize (eff_after_external23 nu23'). 
  assert (GSep3: globals_separate g3
     (replace_locals mu23
        (fun b : block =>
         locBlocksSrc mu23 b && REACH m2 (exportedSrc mu23 vals2) b)
        (fun b : block =>
         locBlocksTgt mu23 b && REACH m3 (exportedTgt mu23 vals3) b)) nu23').
  { eapply match_genv12 in MC12'.
    eapply match_genv12 in NormMC12.
    move NormMC12 at bottom;
      move MC12' at bottom.
    destruct NormMC12 as [MPG isGlob].
    destruct MC12' as [MPG' isGlob']. 
    intros b1 b2 d map23 map23'.
    assert (extern_of nu23' b1 = Some (b2, d)).
    { unfold as_inj in map23'; apply joinD_Some in map23'.
      destruct map23' as [ext23' | [ext23' loc23']].
      + exact ext23'.
      + destruct Incr23 as [extinc [loceq [rest]]]; clear rest.
        rewrite <- loceq in loc23'.
        unfold as_inj, join in map23. 
        destruct (extern_of
              (replace_locals mu23
                 (fun b : block =>
                  locBlocksSrc mu23 b && REACH m2 (exportedSrc mu23 vals2) b)
                 (fun b : block =>
                  locBlocksTgt mu23 b && REACH m3 (exportedTgt mu23 vals3) b))
              b1); try solve [destruct p; inversion map23].
        rewrite loc23' in map23; inversion map23. }
    assert (extmap23':=H).
    apply Pure23 in H. destruct H as [extmap | [extmap [b1' [d' newmap]]]].
    + unfold as_inj, join in map23; rewrite extmap in map23. inversion map23.
    + assert (newmap':=newmap). apply Pure12 in newmap'. 
      destruct newmap' as [extmap12' | [extmap12' [b3 [d2 mapnu']]]].
      - assert (extmap12: extern_of mu12 b1' = Some (b1, d')).
        { unfold replace_locals in extmap12'; destruct mu12; exact extmap12'. }
        eapply GSep.
        * unfold as_inj, join. rewrite compose_sm_extern, compose_sm_local.
          unfold compose_meminj. instantiate(1:= b1').
          rewrite extmap12'. rewrite extmap.
          rewrite replace_locals_local, replace_locals_local.

          destruct (local_of mu12 b1') eqn:locmap12;
          trivial. exfalso.          
          { rewrite replace_locals_extern in extmap12'.
            destruct Incr12 as [ext_inc [loceq rest]]; clear rest; 
            rewrite replace_locals_local in loceq;
            rewrite replace_locals_extern in ext_inc.
            rewrite loceq in locmap12.
            destruct p.
            eapply WDnu12' in locmap12. destruct locmap12 as [locS locT].
            eapply WDnu12' in newmap. destruct newmap as [extS extT].
            destruct WDnu12'. destruct (disjoint_extern_local_Src b1') as [locS' | extS'].
            + rewrite locS' in locS; inversion locS.
            + rewrite extS' in extS; inversion extS. }
       *  unfold as_inj, join. 
          unfold compose_sm; simpl. unfold compose_meminj.
          rewrite newmap. rewrite extmap23'. reflexivity.
      - eapply GSep.
        * unfold as_inj, join. rewrite compose_sm_extern, compose_sm_local.
          unfold compose_meminj. instantiate(1:= b1').
          rewrite extmap12'.
          rewrite replace_locals_local, replace_locals_local.
          destruct (local_of mu12 b1') eqn:locmap12;
          trivial. exfalso.
          
          { rewrite replace_locals_extern in extmap12'.
            destruct Incr12 as [ext_inc [loceq rest]]; clear rest; 
            rewrite replace_locals_local in loceq;
            rewrite replace_locals_extern in ext_inc.
            rewrite loceq in locmap12.
            destruct p.
            eapply WDnu12' in locmap12. destruct locmap12 as [locS locT].
            eapply WDnu12' in newmap. destruct newmap as [extS extT].
            destruct WDnu12'. destruct (disjoint_extern_local_Src b1') as [locS' | extS'].
            + rewrite locS' in locS; inversion locS.
            + rewrite extS' in extS; inversion extS. }
       * assert (b3 = b2).
          { rewrite compose_sm_extern in mapnu'. unfold compose_meminj in mapnu'.
            rewrite newmap, extmap23' in mapnu'. inversion mapnu'.
            reflexivity. }
          unfold as_inj, join. rewrite mapnu'. subst; reflexivity. }
  (*
    apply exter_incr_globals_separate.
    rewrite replace_locals_extern.
    extensionality b.
    destruct ( extern_of mu23 b) eqn: extof; symmetry; try destruct p.
    unfold extern_incr in Incr23; destruct Incr23 as [EXT [? ?]].
    unfold inject_incr in EXT.
    move EXT at bottom.
    rewrite replace_locals_extern in EXT.
    apply EXT in extof.
    exact extof.
    
    
    (*TRY*)
    eapply intern_incr_globals_separate; eauto.
    unfold intern_incr.
    (*apply match_genv12 in MC12'.
    apply match_genv12 in NormMC12.*)
    generalize Incr23; unfold extern_incr.
    rewrite replace_locals_locBlocksSrc, replace_locals_locBlocksTgt, replace_locals_extBlocksSrc, replace_locals_extBlocksTgt, replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt, replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt, replace_locals_local, replace_locals_extern.
    intros extInc;
    destruct extInc as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
    repeat (split; try assumption).
    rewrite H0. apply inject_incr_refl.
    ad_it.
    rewrite H3; intros b HH; apply HH.
    rewrite H4; intros b HH; apply HH.
    
    
    
    

    unfold globals_separate in *.
    rewrite replace_locals_as_inj; intros.
    destruct (isGlobalBlock g3 b2) eqn:Globb3; [rewrite <- Globb3 |try trivial].
    eapply GSep.
    unfold as_inj.
  repeat rewrite compose_sm_extern.
  repeat rewrite compose_sm_local.
  repeat rewrite replace_locals_extern.
  repeat rewrite replace_locals_local.
  repeat rewrite <- compose_sm_extern.
  repeat rewrite <- compose_sm_local.
  remember (compose_sm
           (restrict_sm mu12
              (fun b : block =>
               locBlocksSrc mu12 b || frgnBlocksSrc mu12 b
               || mapped
                    (join (extern_of (compose_sm mu12 mu23))
                       (local_of (compose_sm mu12 mu23))) b)) mu23) as NU.
  fold (as_inj NU).
  rewrite HeqNU; clear HeqNU.
  
  erewrite compose_sm_as_inj; eauto; destruct GLUEINV as [GLUEa [GLUEb [GLUEc GLUEd]]].
  2: rewrite restrict_sm_locBlocksTgt; assumption.
  2: rewrite restrict_sm_extBlocksTgt; assumption.
  eapply match_genv12 in NormMC12.
  destruct NormMC12 as [GSep1 glo_frgn].
  
  

  Lemma compose_sm_None2:
      forall mu mu' b b' delta,
        SM_wd mu ->
        as_inj mu b = Some (b', delta) ->
        as_inj mu' b' = None ->
        as_inj (compose_sm mu mu') b = None.
      intros.
      unfold compose_sm, compose_meminj;
      unfold as_inj, join in *; simpl.
      destruct (extern_of mu b) eqn: extofb. 
      destruct p. inversion H0.
      destruct ( extern_of mu' b') eqn:extofb'. destruct p; inversion H1.
      destruct (local_of mu b) eqn:localofb; try reflexivity.
      destruct p.
      apply H in localofb; apply H in extofb.
      destruct localofb; destruct extofb.
      inversion H.
      destruct (disjoint_extern_local_Src b).
      rewrite H2 in H8; discriminate H8.
      rewrite H6 in H8; discriminate H8.
      rewrite H0.
      destruct (extern_of mu' b'); try (destruct p; inv H1).
      rewrite H1; reflexivity.
  Qed.
  assert (H':=H).
  rewrite replace_locals_as_inj in H'.
  unfold compose_sm, as_inj; simpl.
  rewrite replace_locals_extern.
  rewrite replace_locals_local.
  rewrite replace_locals_extern.
  rewrite replace_locals_local.
  repeat rewrite <- compose_sm_extern.
  repeat rewrite <- compose_sm_local.
  instantiate(1:= b2).
  assert (H'':= H').
  apply as_injD_None in H''.
  destruct H'' as [extof localof].
  Lemma local_None: forall mu b,
                      local_of mu b = None -> pubBlocksSrc mu b = false.
  Ad_itted.
  Lemma extern_None: forall mu b,
                      extern_of mu b = None -> frgnBlocksSrc mu b = false.
  Ad_itted.
  apply local_None in localof.
  apply extern_None in extof.
  destruct GLUEINV as [GLUEa [GLUEb [GLUEc GLUEd]]].
  assert (pubBlocksTgt mu12 b1 = false).
  destruct (pubBlocksTgt mu12 b1) eqn:pub12; try reflexivity.
  apply GLUEc in pub12.
  rewrite pub12 in localof; discriminate localof.
  assert (frgnBlocksTgt mu12 b1 = false).
  destruct (frgnBlocksTgt mu12 b1) eqn:frgn12; try reflexivity.
  apply GLUEd in frgn12.
  rewrite frgn12 in extof; discriminate extof.
  
  apply match_genv12 in NormMC12.
  destruct NormMC12 as [GSep1 glo_frgn].
  rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq23) in Globb3.
  rewrite <- (genvs_domain_eq_isGlobal _ _ genvs_dom_eq12) in Globb3.
  assert (extern_of mu12 b2 = Some (b2, 0)).
  { rewrite restrict_sm_extern in GSep1.
  apply (meminj_preserves_globals_isGlobalBlock _ _ GSep1) in Globb3.
  unfold restrict in Globb3.
  destruct ( locBlocksSrc mu12 b2 || frgnBlocksSrc mu12 b2
               || mapped (as_inj (compose_sm mu12 mu23)) b2) eqn:WYMCI; try solve[ inversion Globb3].
  rewrite Globb3; reflexivity. }
  destruct (extern_of (restrict_sm mu12
              (fun b : block =>
               locBlocksSrc mu12 b || frgnBlocksSrc mu12 b
               || mapped
                    (join (extern_of (compose_sm mu12 mu23))
                       (local_of (compose_sm mu12 mu23))) b)) b2) eqn:SMTH; try destruct p.
  assert (SMTH':=SMTH).
  rewrite restrict_sm_extern in SMTH.
  unfold restrict in SMTH.
  destruct (locBlocksSrc mu12 b2 || frgnBlocksSrc mu12 b2
             || mapped
                  (join (extern_of (compose_sm mu12 mu23))
                     (local_of (compose_sm mu12 mu23))) b2); try solve [inversion SMTH]. 
  rewrite H3 in SMTH; inv SMTH.
  simpl in SMTH'. 
  simpl; unfold compose_meminj, join; simpl.
  unfold compose_meminj, join in SMTH'; simpl in SMTH'.
  rewrite SMTH'.
  simpl.
  clear SMTH'. 
  apply as_injD_None in H'.
  destruct H' as [extof' localof'].
  

  rewrite H3.
  unfold join.
  
  
  

  apply glo_frgn in Globb3. rewrite restrict_sm_frgnBlocksSrc in Globb3.



  apply local_ofD_None in localof.
  
  destruct extof as [frgn21 unk12].
  destruct localof as [pu21 priv12].
  
  assert (extern_of mu23 b1 = None) by ad_it.
  assert (local_of mu23 b1 = None) by adm_it.
  assert (extern_of mu12 b1 = None) by ad_it.
  assert (local_of mu12 b1 = None) by ad_it.
  unfold compose_meminj, mapped, replace_locals; simpl.
  repeat (
      try rewrite H1;
      try rewrite H2;
      try rewrite H3;
      try rewrite H4).
  destruct (as_inj
    (replace_locals
        (restrict_sm mu12
           (fun b : block =>
            locBlocksSrc mu12 b || frgnBlocksSrc mu12 b
            || mapped (as_inj (compose_sm mu12 mu23)) b))
        (fun b : block =>
         locBlocksSrc
           (restrict_sm mu12
              (fun b0 : block =>
               locBlocksSrc mu12 b0 || frgnBlocksSrc mu12 b0
               || mapped (as_inj (compose_sm mu12 mu23)) b0)) b &&
         REACH m1
           (exportedSrc
              (restrict_sm mu12
                 (fun b0 : block =>
                  locBlocksSrc mu12 b0 || frgnBlocksSrc mu12 b0
                  || mapped (as_inj (compose_sm mu12 mu23)) b0)) vals1) b)
        (fun b : block =>
         locBlocksTgt
           (restrict_sm mu12
              (fun b0 : block =>
               locBlocksSrc mu12 b0 || frgnBlocksSrc mu12 b0
               || mapped (as_inj (compose_sm mu12 mu23)) b0)) b &&
         REACH m2
           (exportedTgt
              (restrict_sm mu12
                 (fun b0 : block =>
                  locBlocksSrc mu12 b0 || frgnBlocksSrc mu12 b0
                  || mapped (as_inj (compose_sm mu12 mu23)) b0)) vals2) b)) b1) eqn:WHF.
destruct p.
  
  eapply (compose_sm_None2 _ _ _ ); eauto.
  2: eapply (compose_sm_None1 _ _ _ ); eauto.
  
  
  } *)
  destruct (eff_after_external23 ret2 m2' 
       ret3 m3' HasTy12 HasTy2 Incr23 GSep3 WDnu23' nu23'valid
       MInj23' RValInjNu23' Fwd2 FwdTgt (*RetTypeTgt*) RDO2 RDO3
     _ (eq_refl _) _ (eq_refl _) _ (eq_refl _)) as
     [d23' [c22' [c3' [AftExt22 [AftExt3 MC23']]]]];
    subst; clear eff_after_external23.
    (*discharge unchangedOn application conditions*)
      apply UnchMidA.
      apply UnchMidC.

  (*finally, instantiate the existentials, and establish conclusion*)
  rewrite AftExt22 in AftExt2. inv AftExt2.
  clear GLUEINV.
  exists (d12', Some c2', d23').
  exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2'. exists m2'.
  exists (replace_externs nu12'
            (fun b => DomSrc nu12' b && (negb (locBlocksSrc nu12' b) 
                                     && REACH m1' (exportedSrc nu12' (ret1::nil)) b))
            (fun b => DomTgt nu12' b && (negb (locBlocksTgt nu12' b) 
                                     && REACH m2' (exportedTgt nu12' (ret2::nil)) b))).
  exists (replace_externs nu23'
            (fun b => DomSrc nu23' b && (negb (locBlocksSrc nu23' b) 
                                     && REACH m2' (exportedSrc nu23' (ret2::nil)) b))
            (fun b => DomTgt nu23' b && (negb (locBlocksTgt nu23' b) 
                                     && REACH m3' (exportedTgt nu23' (ret3::nil)) b))).
  split. reflexivity.
  unfold compose_sm. simpl.
         repeat rewrite replace_externs_extBlocksSrc, replace_externs_extBlocksTgt, 
                 replace_externs_locBlocksSrc, replace_externs_locBlocksTgt,
                 replace_externs_pubBlocksSrc, replace_externs_pubBlocksTgt,  
                 replace_externs_frgnBlocksSrc, replace_externs_frgnBlocksTgt.
        rewrite replace_externs_extern, replace_externs_local.
        rewrite replace_externs_extern, replace_externs_local.
  split. f_equal; trivial. 
         unfold exportedSrc; simpl.
           rewrite sharedSrc_iff_frgnpub; trivial.
           rewrite sharedSrc_iff_frgnpub; trivial.
  clear UnchLOOR13 UnchPrivSrc (*SEP*) INC MID UnchMidB Incr12 
        (*Sep12*) WDnu12 nu12_valid MinjNu12 UnchMidC UnchMidA (*Sep23*)
        Incr23 nu23_valid WDnu23 MinjNu23 MemInjMu ValInjMu.
  split. 
    clear MC23' MC12'.
    repeat (split; trivial). unfold DomTgt, DomSrc.
    rewrite GLUEa', GLUEb'.
         intros. do 2 rewrite andb_true_iff.
                 do 2 rewrite andb_true_iff in H.
                 destruct H as [HH1 [HH2 HH3]].
                 split; trivial. split; trivial.
                 eapply REACH_mono; try eassumption.
                 unfold exportedTgt, exportedSrc; intros.
                 apply orb_true_iff. apply orb_true_iff in H.
                 destruct H.
                   left; trivial.
                   right. unfold sharedTgt in H.
                          rewrite sharedSrc_iff_frgnpub.
                          apply orb_true_intro. 
                          apply orb_prop in H.
                          destruct H.
                            left. intuition.
                            right. intuition.
               assumption.
   intuition.
   (* NORM HERE*)
   { unfold full_ext, full_comp, replace_externs; simpl.
     destruct nu12'; destruct nu23'; simpl.
     exact full'.
   }
}
Qed.

End Eff_sim_trans. 