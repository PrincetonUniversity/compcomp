Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.
Require Import Axioms.


Require Import reach.
Require Import effect_simulations.
Require Import effect_simulations_lemmas.
Require Import mem_lemmas.
Require Import mem_interpolation_defs.
Require Import mem_interpolation_II.
Load mem_interpolation_II3.
Require Import FiniteMaps.
Require Import StructuredInjections.

Require Import pure.
Require Import full_composition.


Lemma EFF_interp_II_strong: 
  forall m1 m2 nu12 
         (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
         (Fwd1: mem_forward m1 m1') nu23 m3
         (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
         (Fwd3: mem_forward m3 m3')
         nu' (WDnu' : SM_wd nu')
         (SMvalNu' : sm_valid nu' m1' m3')
         (MemInjNu' : Mem.inject (as_inj nu') m1' m3')
         (ExtIncr: extern_incr (compose_sm nu12 nu23) nu')
         (SMV12: sm_valid nu12 m1 m2)
         (SMV23: sm_valid nu23 m2 m3)
         (UnchPrivSrc: Mem.unchanged_on 
                         (fun b ofs => locBlocksSrc (compose_sm nu12 nu23) b = true /\ 
                                       pubBlocksSrc (compose_sm nu12 nu23) b = false) m1 m1') 
         (UnchLOOR13: Mem.unchanged_on (local_out_of_reach (compose_sm nu12 nu23) m1) m3 m3')
         (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                     locBlocksTgt nu12 = locBlocksSrc nu23 /\
                     extBlocksTgt nu12 = extBlocksSrc nu23 /\
                     (forall b, pubBlocksTgt nu12 b = true -> 
                                pubBlocksSrc nu23 b = true) /\
                     (forall b, frgnBlocksTgt nu12 b = true -> 
                                frgnBlocksSrc nu23 b = true))
         (Norm12: forall b1 b2 d1, extern_of nu12 b1 = Some(b2,d1) ->
                                   exists b3 d2, extern_of nu23 b2 = Some(b3, d2))
         (full: full_ext nu12 nu23),
  exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                                          extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                                          Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                                          Mem.inject (as_inj nu23') m2' m3' /\
                                          sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                                          (SM_wd nu12' /\ SM_wd nu23' /\
                                           locBlocksTgt nu12' = locBlocksSrc nu23' /\
                                           extBlocksTgt nu12' = extBlocksSrc nu23' /\
                                           (forall b, pubBlocksTgt nu12' b = true -> 
                                                      pubBlocksSrc nu23' b = true) /\
                                           (forall b, frgnBlocksTgt nu12' b = true -> 
                                                      frgnBlocksSrc nu23' b = true)) /\
                                          (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                                            exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\ 
                                          Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\ 
                                                                         pubBlocksSrc nu23 b = false) m2 m2' /\
                                          Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' /\
                                          (*             Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3' /\*)
                                          (forall b1 b2 d1, as_inj nu12' b1 = Some(b2,d1) -> 
                                                            as_inj nu12 b1 = Some(b2,d1) \/
                                                            exists b3 d, as_inj nu' b1 = Some(b3,d)) /\
                                          (forall b2 b3 d2, as_inj nu23' b2 = Some(b3,d2) -> 
                                                            as_inj nu23 b2 = Some(b3,d2) \/
                                                            exists b1 d, as_inj nu' b1 = Some(b3,d)).
(*                   (forall b1 b2 ofs2, as_inj nu12' b1 = Some(b2,ofs2) -> 
                     (as_inj nu12 b1 = Some (b2,ofs2)) \/
                     (b1 = Mem.nextblock m1 /\ b2 = Mem.nextblock m2 /\ ofs2 = 0) \/ 
                     (exists m, (b1 = Mem.nextblock m1 + m /\ b2=Mem.nextblock m2 + m)%positive /\ ofs2=0)) /\
                   (forall b2 b3 ofs3, as_inj nu23' b2 = Some(b3,ofs3) -> 
                     (as_inj nu23 b2 = Some (b3,ofs3)) \/
                     (b2 = Mem.nextblock m2 /\ as_inj nu' (Mem.nextblock m1) = Some(b3,ofs3)) \/
                     (exists m, (b2 = Mem.nextblock m2 + m)%positive /\ 
                            as_inj nu' ((Mem.nextblock m1+m)%positive) = Some(b3,ofs3))). *)
Proof. intros. 
       remember (extern_of nu12) as j;
         remember (extern_of nu23) as k;
         remember (extern_of nu') as l';
         remember (Mem.nextblock m2) as sizeM2;
         remember (extBlocksSrc nu') as extS12;
         remember (bconcat (extBlocksTgt nu12) (extBlocksSrc nu') sizeM2) as extT12;
         remember (bconcat (extBlocksSrc nu23) (extBlocksSrc nu') sizeM2) as extS23;
         remember (extBlocksTgt nu') as extT23;
         remember (mkInjections (Mem.nextblock m2) j k l') as output;
         remember (join (j) (restrict (local_of nu12) (pubBlocksSrc nu12))) as jp;
         destruct output as [j' k'].
       remember (change_ext nu12 extS12 extT12 j') as nu12';
         remember (change_ext nu23 extS23 extT23 k') as nu23'.
       exists (mem_add jp m2 m1'), nu12', nu23'.
       split.
       
       (*Compose_sm*)
       { rewrite Heqnu12', Heqnu23'. (*clear - ExtIncr full. *)
         destruct ExtIncr as [extincr [? [? [? [? [? [? [? [? ? ]]]]]]]]].
         unfold compose_sm, change_ext; destruct nu12, nu23, nu'; simpl in *; f_equal; auto.
         eapply (MKIcomposition j k (extern_of1)); subst; eauto.
         
         (* Proving 
          * forall (b : block) (p : block * Z),
          * extern_of0 b = Some p -> (b < Mem.nextblock m2)%positive *)
         intros b p H.  destruct p.
         eapply SMV23. eapply as_inj_DomRng.
         unfold as_inj, join; simpl; rewrite H; eauto.
         apply GlueInvNu.
       }
       split.
       (* extern_incr12 *)
       { unfold extern_incr; simpl.
         subst; destruct nu12;
         unfold extern_incr; simpl.
         destruct ExtIncr as [extincr [? [extS [extT [? [? [? [? [? ? ]]]]]]]]].
         simpl in *.
         intuition.
         eapply MKI_incr12; eauto.
         apply bconcat_larger1; exact H11.
       }
       split.
       (* extern_incr12 *)
       { unfold extern_incr; simpl.
         subst; destruct nu23;
         unfold extern_incr; simpl.
         destruct ExtIncr as [extincr [? [extS [extT [? [? [? [? [? ? ]]]]]]]]].
         simpl in *.
         intuition.
         eapply MKI_incr23; eauto.
         apply bconcat_larger1; auto.
       }
       split.
       (* Mem.inject *)
       { constructor.
         + constructor.
         - { intros b1 b2 delta ofs k0 per H H0.
             unfold Mem.perm; rewrite (mem_add_accx jp m1' m2); unfold mem_add_acc.
             (* New trying things*)
             unfold as_inj in H; apply joinD_Some in H; destruct H as [extmap | [extNone locmap]].
             + subst nu12'; rewrite ext_change_ext in extmap.
               eapply MKI_Some12 in extmap; eauto. 
               destruct extmap as [jmap | [jmap [b2' [d' [lmap' [b2eq deltaeq]]]]]].
             - assert (Mem.valid_block m2 b2).
               { apply SMV12. unfold RNG, DomTgt. subst j; apply GlueInvNu in jmap. 
                 destruct jmap as [extS extT]; rewrite extT; apply orb_true_r. }
               destruct (valid_dec m2 b2); try solve[contradict n; auto].
               erewrite source_SomeI. apply H0.
               * eapply meminj_no_overlap_inject_incr.
                 eapply (no_overlap_forward _ _ _ _ SMV12); eauto.
                 apply GlueInvNu.
                 apply MInj12.
                 subst jp. apply inject_incr_join.
                 subst j; apply inject_incr_refl.
                 eapply inject_incr_trans; [eapply restrict_incr | apply inject_incr_refl].
                 apply disjoint_extern_local; eauto.
                 apply GlueInvNu.
               *  subst jp; unfold join; rewrite jmap; auto.
               * eapply any_Max_Nonempty; eauto.
             - destruct (valid_dec m2 b2); (*first discharge the impossible case*)
               try solve[subst b2; contradict v; unfold Mem.valid_block; xomega].
               subst b2 delta. rewrite Pos.add_sub; auto.
               replace (ofs + 0) with ofs by omega; trivial.
             + subst nu12'; rewrite loc_change_ext in locmap.
               rewrite ext_change_ext in extNone.
               assert (Mem.valid_block m2 b2).
               { apply SMV12. unfold RNG, DomTgt. apply GlueInvNu in locmap. 
                 destruct locmap as [locS locT]; rewrite locT; apply orb_true_l. }
               destruct (valid_dec m2 b2); try solve[contradict n; auto].
               destruct (source jp m1' b2 (ofs + delta)) eqn:sour.
               - destruct p; symmetry in sour.
                 destruct (source_SomeE _ _ _ _ _ sour) 
                               as [b1' [delta' [ofs1 [pairs [bval [jpmap [mperm ofss]]]]]]].
                 inversion pairs; subst b z jp.
                 (*b2 is local so j can't map to it *)
                 unfold join in jpmap.
                 destruct (j b1') eqn:jmap; try destruct p.
                 {inversion jpmap; subst b z j.
                 apply GlueInvNu in jmap; destruct jmap as [extS extT].
                 apply GlueInvNu in locmap; destruct locmap as [locS locT].
                 destruct GlueInvNu as [SMWD12 rest]; clear rest.
                 destruct SMWD12. destruct (disjoint_extern_local_Tgt b2) as [LT | ET];
                 [rewrite LT in locT | rewrite ET in extT]; discriminate. }
                 apply restrictD_Some in jpmap; destruct jpmap as [locmap' pubtrue].
                 Lemma no_overlap_no_doublemap: 
                   forall j b1 b1' b2 d d' m,
                     Mem.meminj_no_overlap j m ->
                     j b1 = Some (b2, d) ->
                     j b1' = Some (b2, d') ->
                     forall ofs ofs',
                       Mem.perm m b1 ofs Max Nonempty ->
                       Mem.perm m b1' ofs' Max Nonempty ->
                       ofs + d = ofs' + d' ->
                       b1' = b1 /\ ofs = ofs' /\ d = d'.
                   intros.
                   destruct (peq b1 b1'). 
                   { subst b1. rewrite H1 in H0; inversion H0. 
                     subst d'; assert (ofs = ofs') by xomega. intuition. }
                   destruct (H b1 b2 d b1' b2 d' ofs ofs') as [H5 | H5]; eauto;
                   contradiction H5; auto.
                 Qed.
                 edestruct (no_overlap_no_doublemap (local_of nu12) b1 b1') as 
                     [b1_eq [ofs_eq d_eq]]; eauto.
                 { eapply meminj_no_overlap_inject_incr.
                   eapply no_overlap_forward. 
                   apply SMV12.
                   apply GlueInvNu.
                   auto.
                   apply MInj12.
                   apply local_in_all. apply GlueInvNu. }
                 eapply any_Max_Nonempty; eauto.
                 subst b1' ofs1; auto.
               - destruct MInj12.
                 destruct mi_inj.
                 eapply mi_perm0.
                 apply local_in_all; eauto.
                 apply GlueInvNu. 
                 apply UnchPrivSrc.
                 unfold compose_sm; simpl.
                 assert (locmap':=locmap).
                 apply GlueInvNu in locmap'; destruct locmap' as [locS locT].
                 rewrite locS; simpl; split; auto.
                 destruct (pubBlocksSrc nu12 b1) eqn:pubTrue; trivial.
                 assert (pubS:=pubTrue).
                 apply GlueInvNu in pubTrue. destruct pubTrue as [b2' [z [locmap' pubT]]].
                 rewrite locmap in locmap'; inversion locmap'; subst b2 delta. clear locmap'.
                 assert (jp b1 = Some (b2', z)).
                 { subst jp. unfold join. 
                   rewrite (inject_incr_inv j j'); eauto.
                   unfold restrict. rewrite pubS.
                   auto.
                   eapply MKI_incr12; eauto. }
                 symmetry in sour.
                 eapply any_Max_Nonempty in H0.
                 contradict H0.
                 replace ofs with ((ofs + z) - z) by omega.
                 eapply source_NoneE; eauto.
                 (*The three remaining goals follow the same logic*)
                 assert (Mem.valid_block m1 b1).
                 { destruct SMV12 as [Dv Rv]; clear Rv.
                   apply Dv. unfold DOM, DomSrc.
                   rewrite locS; auto.
                 }
                 apply Fwd1 in H0; destruct H0 as [H0 ?].
                 apply H0.

                 destruct SMV12 as [Dv Rv]; clear Rv.
                 apply Dv. unfold DOM, DomSrc.
                 apply GlueInvNu in locmap; destruct locmap as [locS locT].
                 rewrite locS; auto.
                 
                 auto.
               }
         - intros. unfold Z.divide.
           subst nu12'; unfold as_inj, join in H. rewrite ext_change_ext, loc_change_ext in H.
           destruct (j' b1) eqn:jmap'. 
           destruct p0. destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ jmap') as 
                          [jmap | [jmap [b2' [d' [lmap [b2eq deq]]]]]].
           inversion H; subst b z.
           subst j. destruct MInj12. destruct mi_inj.
           eapply (mi_align b1 b2); eauto. 
           unfold as_inj, join; rewrite jmap; trivial.
           Lemma forward_range:
             forall m m' b ofs size p,
               mem_forward m m' ->
               Mem.valid_block m b ->
               Mem.range_perm m' b ofs (ofs + size) Max p ->
               Mem.range_perm m b ofs (ofs + size) Max p.
             unfold Mem.range_perm; intros.
             apply H; auto.
           Qed.
           eapply forward_range; eauto.
           clear H. 
           Lemma mapped_valid: forall mu m1 m2 b1 b2 d,
                                 SM_wd mu ->
                                 as_inj mu b1 = Some (b2, d) ->
                                 sm_valid mu m1 m2 ->
                                 Mem.valid_block m1 b1.
             intros. destruct H1 as [H1 H2]; apply H1.
             unfold DOM, DomSrc.
             apply joinD_Some in H0; destruct H0 as [map | [extNone map]];
             apply H in map; destruct map as [src tgt]; rewrite src; auto.
             apply orb_true_r.
           Qed.
           eapply mapped_valid.
           destruct GlueInvNu as [SMWD12 rest]; apply SMWD12. 
           unfold as_inj, join; rewrite jmap; auto. 
           eauto.
           
           (* This should be folded in a lemma *)
           inversion Heqoutput.
           unfold add_inj, shiftT in H2. subst j'. rewrite jmap in jmap'.
           unfold filter_id in jmap'. rewrite lmap in jmap'.
           inversion jmap'. subst z. symmetry in H; inversion H; subst delta.
           exists 0; xomega.
           (*Done *)
           
           destruct MInj12. destruct mi_inj.
           eapply (mi_align b1 b2); eauto.
           unfold as_inj. 
           rewrite join_com. 
           unfold join; rewrite H; trivial.
           apply disjoint_extern_local.
           apply GlueInvNu.
           eapply forward_range; eauto.
           eapply mapped_valid.
           destruct GlueInvNu as [SMWD12 rest]; apply SMWD12. 
           unfold as_inj. 
           rewrite join_com. 
           unfold join; rewrite H; trivial.
           apply disjoint_extern_local.
           apply GlueInvNu.
           eauto.
         - intros. rewrite mem_add_contx.          
           subst nu12'. unfold as_inj in H. rewrite ext_change_ext, loc_change_ext in H.
           apply joinD_Some in H; destruct H as [ jmap' | [jmap' locmap] ].
           apply (MKI_Some12 _ _ _ _ _ _ Heqoutput) in jmap'.
           destruct jmap' as [jmap | [jmap [b2' [d' [lmap [b2eq deq]]]]]].
           destruct MInj12; destruct mi_inj. 
           assert (b1val: Mem.valid_block m1 b1).
           { eapply mapped_valid. destruct GlueInvNu as [SMWD12 rest]; apply SMWD12.
             subst j; unfold as_inj, join; rewrite jmap. reflexivity.
             eauto. }
           apply Fwd1 in b1val. destruct b1val as [b1val' mpermm].
           apply mpermm in H0.
           inversion (mi_memval b1 ofs b2 delta).
           constructor.
           apply mi_memval.


       + intros. unfold as_inj; subst nu12'; rewrite ext_change_ext, loc_change_ext.
         assert (H0: ~ Mem.valid_block m1 b). 
         { clear - H Fwd1. unfold not, Mem.valid_block in *.
           intros; apply H. apply (Pos.lt_le_trans _ _ _ H0).
           apply forward_nextblock; assumption. }
         destruct MInj12, MemInjNu'.
         apply mi_freeblocks in H0; destruct (as_injD_None _ _ H0) as [ext loc].
         apply mi_freeblocks0 in H; destruct (as_injD_None _ _ H) as [ext' loc'].
         unfold join.
         erewrite MKI_None12; subst; eauto; subst.
       + unfold as_inj; subst nu12'.
         intros b b' delta map; destruct (as_in_SomeE _ _ _ _ map) as [ext | loc].
         rewrite ext_change_ext in ext. 
         destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ ext).
         destruct MInj12.
         unfold Mem.valid_block; rewrite mem_add_nbx; unfold mem_add_nb.
         eapply Pos.lt_trans; try eapply (Pos.lt_add_diag_r (Mem.nextblock m2)).
         apply (mi_mappedblocks b b' delta).
         unfold as_inj, join; subst; rewrite H; auto.
         destruct H as [jmap [b2' [d' [lmap' [eq1 eq2]]]]].
         destruct MemInjNu'. unfold Mem.valid_block; rewrite mem_add_nbx.
         unfold mem_add_nb. subst b'.
         destruct WDnu'.
         subst l'.
         apply extern_DomRng in lmap'; destruct lmap' as [extS extT].
         destruct SMvalNu' as [DOMv RNGv].
         assert (Plt b m1'.(Mem.nextblock)).
         apply DOMv. unfold DOM, DomSrc. rewrite extS; apply orb_true_r.
         xomega.

         unfold Mem.valid_block; rewrite mem_add_nbx.
         unfold mem_add_nb.
         rewrite loc_change_ext in loc.
         destruct GlueInvNu as [WDnu12 rest];clear rest; destruct WDnu12.
         apply local_DomRng in loc; destruct loc as [locS locT].
         destruct SMV12 as [DOMv RNGv].
         assert (Plt b' m2.(Mem.nextblock)).
         apply RNGv. unfold RNG, DomTgt. rewrite locT; apply orb_true_l.
         xomega.
       + idtac.
         Lemma no_overlap_asinj: 
           forall mu m, 
             SM_wd mu -> 
             Mem.meminj_no_overlap (extern_of mu) m ->
             Mem.meminj_no_overlap (local_of mu) m ->
             Mem.meminj_no_overlap (as_inj mu) m.
           unfold Mem.meminj_no_overlap.
           intros mu m SMWD NOO_ext NOO_loc.
           intros.
           apply as_in_SomeE in H0.
           apply as_in_SomeE in H1.
           destruct H0 as [ext1 | loc1];
           destruct H1 as [ext2 | loc2].
           eapply NOO_ext; eauto.
           destruct SMWD. apply extern_DomRng in ext1; apply local_DomRng in loc2.
           destruct (peq b1' b2'); auto; subst b1'.
           destruct loc2; destruct ext1.
           destruct (disjoint_extern_local_Tgt b2'). 
           rewrite H6 in H1; inversion H1.
           rewrite H6 in H5; inversion H5.
           destruct SMWD. apply extern_DomRng in ext2; apply local_DomRng in loc1.
           destruct (peq b1' b2'); auto; subst b1'.
           destruct loc1; destruct ext2.
           destruct (disjoint_extern_local_Tgt b2'). 
           rewrite H6 in H1; inversion H1.
           rewrite H6 in H5; inversion H5.
           eapply NOO_loc; eauto.
         Qed.
         Lemma no_overlap_ext:
           forall mu m,
             Mem.meminj_no_overlap (as_inj mu) m ->
             Mem.meminj_no_overlap (extern_of mu) m.
           unfold Mem.meminj_no_overlap; intros.
           eapply H; eauto.
           unfold as_inj, join; rewrite H1; auto.
           unfold as_inj, join; rewrite H2; auto.
         Qed.
         Lemma no_overlap_loc:
           forall mu m,
             SM_wd mu ->
             Mem.meminj_no_overlap (as_inj mu) m ->
             Mem.meminj_no_overlap (local_of mu) m.
           unfold Mem.meminj_no_overlap; intros.
           eapply H0; eauto.
           unfold as_inj; rewrite (join_com _ _ (disjoint_extern_local _ H)); unfold join.
           rewrite H2; auto.
           unfold as_inj; rewrite (join_com _ _ (disjoint_extern_local _ H)); unfold join.
           rewrite H3; auto.
         Qed.
         apply no_overlap_asinj.
         admit.
         subst nu12'; rewrite ext_change_ext.
         admit. (* from construction*)
         subst nu12'; rewrite loc_change_ext.
         admit.
       + intros.
         subst nu12'. apply as_in_SomeE in H; destruct H as [ext1 | loc1];
         [ rewrite ext_change_ext in ext1 | rewrite loc_change_ext in loc1].
         - eapply MKI_Some12 in ext1; eauto. 
           destruct ext1 as [jmap | [jmap [b3 [d [lmap' [beq deq]]]]]].
           assert (map12: as_inj nu12 b = Some (b', delta)).
           { unfold as_inj, join ; subst j; rewrite jmap; eauto. }
           destruct MInj12. eapply mi_representable; eauto. 
           destruct H0; [left | right].
           eapply Fwd1.
           Lemma valid_from_map: 
             forall mu m1 m2 b1 b2 d,
               SM_wd mu -> 
               as_inj mu b1 = Some (b2,d) ->
               sm_valid mu m1 m2 ->
               Mem.valid_block m1 b1.
             intros mu m1 m2 b1 b2 d SMWD map smv. 
             apply as_in_SomeE in map.
             destruct SMWD, smv as [DOMv RNGv], map as [ext1 | loc1];
             apply DOMv; unfold DOM, DomSrc.
             apply extern_DomRng in ext1; destruct ext1 as [extS extT].
             rewrite extS; apply orb_true_r.
             apply local_DomRng in loc1; destruct loc1 as [locS locT].
             rewrite locS; apply orb_true_l.
             Qed.
           eapply valid_from_map. 
           destruct GlueInvNu as [SMWD12 rest]; apply SMWD12.
           apply map12.
           eassumption.
           assumption.

           eapply Fwd1.
           eapply valid_from_map. 
           destruct GlueInvNu as [SMWD12 rest]; apply SMWD12.
           apply map12.
           eassumption.
           assumption.

           destruct ofs as [ofs range].
           subst delta; split; simpl. 
           xomega. 
           split.
           xomega.
           unfold Int.max_unsigned.
           xomega.
         - assert (map12: as_inj nu12 b = Some (b', delta)).
           { unfold as_inj. rewrite join_com. unfold join; rewrite loc1; auto.
             apply disjoint_extern_local; apply GlueInvNu. }
           destruct MInj12. eapply mi_representable; eauto. 
           destruct H0; [left | right].
           eapply Fwd1; eauto.
           eapply (valid_from_map nu12); eauto.
           destruct GlueInvNu as [SMWD12 rest]; apply SMWD12.
           eapply Fwd1; eauto.
           eapply (valid_from_map nu12); eauto.
           destruct GlueInvNu as [SMWD12 rest]; apply SMWD12.
           }
       split.
       (* mem_forward *)
       { apply (mem_add_forward j' m1' m2 jp m1); auto.
         + destruct SMV12 as [DOMv RNGv].
           intros; apply DOMv; unfold DOM, DomSrc. 
           destruct GlueInvNu as [SMWD12 rest]; clear rest.
           subst j. destruct SMWD12. destruct p; subst jp. 
           apply joinD_Some in H; destruct H as [ext1 | [jnone resloc]].
           - apply extern_DomRng in ext1.
             destruct ext1 as [extS extT]; rewrite extS; apply orb_true_r.
           - apply restrictD_Some in resloc; destruct resloc as [loc1 pucTrue].
             apply local_DomRng in loc1; destruct loc1 as [locS locT]; rewrite locS; auto.
         (*+ apply (MKI_range_eq _ _ _ _ _ _ Heqoutput).*)
         + unfold mi_perm; destruct MInj12; destruct mi_inj; auto. 
           intros; eapply mi_perm0; eauto. 
           subst j jp; unfold as_inj, join. 
           apply joinD_Some in H; destruct H as [ext1 | [ext1 loc1]].
           - rewrite ext1; auto.
           - apply restrictD_Some in loc1; destruct loc1 as [loc1 pubTrue].
             rewrite ext1; rewrite loc1; auto.
       }
       split.
       (* Mem.inject *)
       { admit. }
       split.
       (* sm_valid 12'*)
       { unfold sm_valid.
         split; intros.
         apply SMvalNu'. generalize H; unfold DOM, DomSrc.
         subst nu12'. unfold change_ext; destruct nu12.
         simpl. rewrite HeqextS12.
         intros H0.
         apply orb_true_iff in H0; destruct H0. 
         destruct ExtIncr as [extincr [intincr [? [? [locS [? [? [? [? ? ]]]]]]]]]; simpl in *.
         rewrite <- locS. rewrite H0; auto.
         rewrite H0; apply orb_true_r.
         
         (* Valid block *)
         { subst nu12'. unfold RNG, DomTgt, change_ext in H. destruct nu12; simpl in H.
           unfold Mem.valid_block. rewrite mem_add_nbx. unfold mem_add_nb.
           apply orb_true_iff in H; destruct H.
           + destruct SMV12 as [DOMtrue RNGtrue].
             unfold RNG, DomTgt in RNGtrue; move RNGtrue at bottom; simpl in RNGtrue.
             Lemma pos_lt_inc1: forall a b c, (a < b -> a < (b +c ))%positive.
               intros a b c H.
               apply Pos.lt_iff_add; apply Pos.lt_iff_add in H.
               destruct H as [r H].
               exists (r + c)%positive.
               rewrite Pos.add_assoc; rewrite H; auto.
             Qed.
             apply pos_lt_inc1. apply RNGtrue. rewrite H; auto.
           + subst extT12; simpl in H.
             unfold bconcat, buni, bshift in H.
             apply orb_true_iff in H; destruct H.
           - destruct SMV23 as [DOMtrue RNGtrue].
             unfold DOM, DomSrc in DOMtrue; move DOMtrue at bottom; simpl in DOMtrue.
             apply pos_lt_inc1. apply DOMtrue. 
             destruct GlueInvNu as [SMWD12 [SMWD23 [? [extEq [? ?]]]]].
             simpl in extEq. move extEq at bottom. rewrite extEq in H.
             rewrite H; auto.
             apply orb_true_r.
           - destruct ((b2 ?= sizeM2)%positive) eqn:compara; try solve [inversion H].
             * apply Pos.compare_eq_iff in compara; subst b2.
               apply Pos.lt_iff_add. exists (Mem.nextblock m1'); subst sizeM2; auto. 
             * apply Pos.compare_gt_iff in compara.
               destruct SMvalNu' as [DOMtrue RNGtrue].
               unfold DOM, DomSrc in DOMtrue; move DOMtrue at bottom; simpl in DOMtrue.
               specialize (DOMtrue ((b2 - sizeM2)%positive)).
               rewrite H in DOMtrue. rewrite orb_true_r in DOMtrue.
               Lemma handy_lemma: forall a b c, (b<a -> a - b < c -> a < b +c )%positive.
                 intros a b c H1 H2.
                 destruct (Pos.add_lt_mono_r b (a-b) c) as [HH HH']; apply HH in H2; clear HH HH'.
                 rewrite (Pos.sub_add a b H1) in H2.
                 rewrite (Pos.add_comm c b) in H2; assumption.
               Qed.
               apply handy_lemma; subst sizeM2; try apply DOMtrue; auto.
         }
       }
       split.
       (* sm_valid 23'*)
       { unfold sm_valid.
         split; intros.
         subst nu23'. unfold DOM, DomSrc, change_ext in H. destruct nu23; simpl in H.
         subst extS23; simpl in H.
         (* Valid block *)
         { unfold DOM, DomSrc, change_ext in H.
           unfold Mem.valid_block. rewrite mem_add_nbx. unfold mem_add_nb.
           apply orb_true_iff in H; destruct H.
           + destruct SMV23 as [DOMtrue RNGtrue].
             unfold DOM, DomSrc in DOMtrue; move DOMtrue at bottom; simpl in DOMtrue.
             apply pos_lt_inc1. apply DOMtrue. rewrite H; auto.
           + unfold bconcat, buni, bshift in H.
             apply orb_true_iff in H; destruct H.
           - destruct SMV12 as [DOMtrue RNGtrue].
             unfold RNG, DomTgt in RNGtrue; move RNGtrue at bottom; simpl in RNGtrue.
             apply pos_lt_inc1. apply RNGtrue. 
             destruct GlueInvNu as [SMWD12 [SMWD23 [? [extEq [? ?]]]]].
             simpl in extEq. move extEq at bottom. rewrite <- extEq in H.
             rewrite H; auto.
             apply orb_true_r.
           - destruct ((b1 ?= sizeM2)%positive) eqn:compara; try solve [inversion H].
             * apply Pos.compare_eq_iff in compara; subst b1.
               apply Pos.lt_iff_add. exists (Mem.nextblock m1'); subst sizeM2; auto. 
             * apply Pos.compare_gt_iff in compara.
               destruct SMvalNu' as [DOMtrue RNGtrue].
               unfold DOM, DomSrc in DOMtrue; move DOMtrue at bottom; simpl in DOMtrue.
               specialize (DOMtrue ((b1 - sizeM2)%positive)).
               rewrite H in DOMtrue. rewrite orb_true_r in DOMtrue.
               apply handy_lemma; subst sizeM2; try apply DOMtrue; auto.
         }
         apply SMvalNu'. generalize H; unfold RNG, DomTgt.
         subst nu23'. unfold change_ext; destruct nu23.
         simpl. rewrite HeqextT23.
         intros H0.
         apply orb_true_iff in H0; destruct H0. 
         destruct ExtIncr as [extincr [intincr [? [? [locS [locT [? [? [? ? ]]]]]]]]]; simpl in *.
         rewrite <- locT. rewrite H0; auto.
         rewrite H0; apply orb_true_r.
       }
       split.
       split.
       (* SM_wd 12*)
       { subst nu12'; eapply MKI_wd12; eauto.
         + apply GlueInvNu.
         + subst extS12. intros.
           destruct (locBlocksSrc nu12 b) eqn:locBS12; auto.
           right. destruct ExtIncr as [? [? [extS [? [locS ?]]]]].
           simpl in locS; rewrite locS in locBS12.
           destruct WDnu'. destruct (disjoint_extern_local_Src b) as [locFalse | extFalse].
           rewrite locBS12 in locFalse; inversion locFalse.
           exact extFalse.
         + subst extT12. intros.
           destruct (locBlocksTgt nu12 b) eqn:locBT12; auto.
           right. 
           unfold bconcat, buni, bshift.
           destruct ExtIncr as [? [? [extS [? [locS [locT ?]]]]]].
           destruct GlueInvNu as [SMWD GlueInvNu].
           destruct SMWD. destruct (disjoint_extern_local_Tgt b) as [locFalse | extFalse].
           rewrite locBT12 in locFalse; inversion locFalse.
           rewrite extFalse; simpl.
           destruct SMV12 as [DOM12 RNG12].
           subst sizeM2;
             rewrite RNG12; auto.
           unfold RNG, DomTgt.
           rewrite locBT12; auto.
         + inversion Heqoutput. unfold add_inj, shiftT; intros.
           destruct (j b1) eqn:jb1. 
         - rewrite H in jb1. subst j. destruct GlueInvNu as [SMWD GlueInvNu].
           destruct SMWD. apply extern_DomRng in jb1. destruct jb1 as [extS12true extT12true].
           subst extS12 extT12. apply ExtIncr in extS12true.
           rewrite extS12true; split; trivial.
           apply bconcat_larger1; auto.
         - unfold filter_id in H. destruct (l' b1) eqn:lb1; inversion H.
           subst extS12 extT12. subst l'.
           destruct WDnu', p;
             apply extern_DomRng in lb1.
           destruct lb1 as [extStrue extTtrue].
           split; auto.
           subst sizeM2; apply bconcat_larger2; auto.
           + intros. subst extT12. apply bconcat_larger1; auto.
             destruct GlueInvNu as [SMWD12 GlueInvNu]; apply SMWD12 in H.
             exact H.
       }
       split.
       (* SM_wd 23*)
       { subst nu23'; eapply MKI_wd23; eauto.
         + apply GlueInvNu.
         + subst extS23; intros.
           destruct (locBlocksSrc nu23 b) eqn:locBS23; auto.
           right. 
           unfold bconcat, buni, bshift.
           destruct GlueInvNu as [SMWD12 [SMWD23 GlueInvNu]];
             destruct SMWD23; destruct (disjoint_extern_local_Src b) as [locSfalse | extSfalse].
           rewrite locBS23 in locSfalse; inversion locSfalse.
           rewrite extSfalse; simpl.
           destruct ExtIncr as [? [? [extS [extT [locS [locT ?]]]]]].
           destruct SMV23 as [DOM23 RNG23].
           subst sizeM2; rewrite DOM23; auto.
           unfold DOM, DomSrc. rewrite locBS23; auto.
         + subst extT23. intros.
           destruct (locBlocksTgt nu23 b) eqn:locBT23; auto.
           right. destruct ExtIncr as [? [? [extS [? [locS [locT ?]]]]]].
           simpl in locT; rewrite locT in locBT23.
           destruct WDnu'. destruct (disjoint_extern_local_Tgt b) as [locFalse | extFalse].
           rewrite locBT23 in locFalse; inversion locFalse.
           exact extFalse.
         + inversion Heqoutput. unfold add_inj, shiftS; intros.
           destruct (k b1) eqn:kb1. 
         - rewrite H in kb1. subst k. destruct GlueInvNu as [SMWD12 [SMWD23 GlueInvNu]].
           destruct SMWD23. apply extern_DomRng in kb1. destruct kb1 as [extS23true extT23true].
           subst extS23 extT23. destruct ExtIncr as [? [? [extS [extT [locS [locT ?]]]]]].
           simpl in extT; apply extT in extT23true.
           rewrite extT23true; split; trivial.
           apply bconcat_larger1; auto.
         - rename H into lb1. inversion lb1.
           destruct ((b1 ?= Mem.nextblock m2)%positive) eqn:ineq; try solve [inversion H2].
           subst extS23 extT23. subst l'.
           destruct WDnu'.
           apply extern_DomRng in lb1.
           destruct lb1 as [extStrue extTtrue].
           split; auto.             
           replace b1 with ((b1 - sizeM2) + sizeM2)%positive; 
             subst sizeM2. apply bconcat_larger2; auto.
           apply Pos.sub_add; destruct (Pos.compare_gt_iff b1 (Mem.nextblock m2)). 
           apply H; auto.
           + intros. subst extT23. destruct ExtIncr as [? [? [extS [extT [locS [locT ?]]]]]].
             apply extT; simpl; auto.
             destruct GlueInvNu as [SMWD12 [SMWD23 GlueInvNu]]; apply SMWD23 in H; auto.
       }
       split.
       (* locBlocksTgt = locBlocksSrc *)
       { subst. unfold change_ext; destruct nu12, nu23; simpl.  
         apply GlueInvNu.
       }
       (* locBlocksTgt = locBlocksSrc *)
       split.
       {
         destruct GlueInvNu as [? [? [? [extEq [? ?]]]]].
         subst nu23' nu12'; unfold change_ext; destruct nu23, nu12; subst extS23 extT12; simpl.
         simpl in extEq; rewrite extEq; auto.
       }
       split.
       (* pubBlocksTgt -> pubBlocksSrc *)
       { subst. unfold change_ext; destruct nu12, nu23; simpl.  
         apply GlueInvNu.
       }
       (* frgnBlocksTgt -> frgnBlocksSrc *)
       { subst. unfold change_ext; destruct nu12, nu23; simpl.  
         apply GlueInvNu.
       }
       split.
       (* Norm *)
       { subst nu12' nu23'. unfold change_ext; destruct nu12, nu23; simpl. 
         eapply MKI_norm; subst; eauto.
         
         
         (* Proveing 
          * forall (b : block) (p : block * Z),
          * extern_of0 b = Some p -> (b < Mem.nextblock m2)%positive *)
         intros b p H.  destruct p.
         eapply SMV23. eapply as_inj_DomRng.
         unfold as_inj, join; simpl. simpl in *; rewrite H; eauto.
         apply GlueInvNu.
       }
       split.
       (* Mem.unchanged_on *)
       { constructor; intros.
         + (* If [locBlocksSrc nu23 b] then b has no preimage in j *)
           assert (no_preimage: source jp m1' b ofs = None).
           { destruct (source jp m1' b ofs) eqn: preimage; trivial.
             symmetry in preimage; apply source_SomeE in preimage.
             destruct preimage as [b1 [delta [ofs1 [po [mvalid [jmap ?]]]]]].
             subst jp j.
             apply joinD_Some in jmap; destruct jmap as [jmap | restPub].
             destruct GlueInvNu as [SMWD12 [SMWD23 [loceq rest]]]; clear SMWD23 rest.
             apply SMWD12 in jmap; destruct jmap.
             destruct SMWD12. destruct (disjoint_extern_local_Tgt b).
             - rewrite loceq in H4.
               destruct H as [locTrue pubFalse]; rewrite locTrue in H4; inversion H4.
             - rewrite H3 in H4; inversion H4. 
               (*This last part follows from the public blocks. Becasue they change.*)
             - destruct restPub. 
               unfold restrict in H3. destruct H as [H5 H6].
               destruct (pubBlocksSrc nu12 b1) eqn:pubS12; try solve[inversion H3].
               destruct (local_of nu12 b1) eqn:loc12; inversion H3.
               destruct p1 as [bn dn]; inversion H3.
               destruct GlueInvNu as [SMWD12 [? [loc [ext [pub frg]]]]].
               assert (loc12':=loc12).
               apply SMWD12 in loc12.
               apply SMWD12 in pubS12. destruct pubS12 as [b2 [z [locmap pubT]]].
               destruct loc12 as [locS12 locT12].
               move pub at bottom. 
               apply pub in pubT.
               rewrite locmap in loc12'; inversion loc12'.
               subst bn dn.
               subst b2.
               rewrite pubT in H6; inversion H6. 
           }
           unfold Mem.perm. 
           rewrite (mem_add_accx jp m1' m2 b). unfold mem_add_acc.
           destruct (valid_dec m2 b) as [y | n]; try solve[contradict n; assumption].
           rewrite no_preimage; split; auto.
         + admit.
       }
       (* Mem.unchanged_on *) (*NOTE: hey both Mem.unchanged_on look very alike! *)
       split.
       { unfold local_out_of_reach.
         constructor; intros.
         + destruct H. 
           unfold Mem.perm.
           rewrite mem_add_accx; unfold mem_add_acc.
           destruct (valid_dec m2 b); try contradiction.
           destruct (source jp m1' b ofs) eqn:sour; try solve[split; trivial].
           destruct p0; simpl.
           symmetry in sour; apply source_SomeE in sour.
           destruct sour as [b1 [d [ofs1 [invertibles[ ineq [jpmap [mperm ofsets]]]]]]].
           subst jp.
           (* This will show that local_of nu12 maps b1->b (bc. locBlocksTgt nu12 b = true)*)
           unfold join in jpmap. destruct (j b1) eqn:jmap.
           destruct p0; simpl in *.
           subst j. apply GlueInvNu in jmap; destruct jmap as [extS extT].
           destruct GlueInvNu as [SMWD12 rest]; clear rest; destruct SMWD12.
           destruct (disjoint_extern_local_Tgt b2).
           inversion invertibles; inversion jpmap; subst.
           rewrite H in H2; inversion H2.
           rewrite extT in H2; inversion H2.
           apply restrictD_Some in jpmap; destruct jpmap as [locmap publ].
           assert (locmap':= locmap).
           apply H1 in locmap'.
           destruct locmap' as [notperm | notpub];
             try solve[rewrite notpub in publ; inversion publ].
           inversion invertibles; subst b0 z.
           move Fwd1 at bottom.
           unfold mem_forward in Fwd1.
           assert (Mem.valid_block m1 b1).
           { destruct SMV12 as [DOMv RNGv]; clear RNGv; apply DOMv.
             unfold DOM, DomSrc. apply GlueInvNu in locmap.
             destruct locmap as [locS locT]. rewrite locS; auto.
           }
           apply Fwd1 in H2; destruct H2 as [bval mperms].
           apply mperms in mperm. subst ofs. 
           contradict notperm; replace (ofs1 +d - d) with ofs1 by xomega.
           assumption.
         + admit.
       }
       split.
       { intros; subst;
         eapply destruct_sminj12; eauto.
         apply GlueInvNu.
       }
       { intros; subst;
         edestruct destruct_sminj23.
         destruct GlueInvNu as [? GIN]; apply GIN.
         auto.
         auto.
         eauto.
         eauto.
         - left; assumption.
         - right; destruct H0 as [b1 rest]; exists b1, d2; exact rest.
       }
Qed.

Lemma EFF_interp_II: forall m1 m2 nu12 
                             (MInj12 : Mem.inject (as_inj nu12) m1 m2) m1'
                             (Fwd1: mem_forward m1 m1') nu23 m3
                             (MInj23 : Mem.inject (as_inj nu23) m2 m3) m3'
                             (Fwd3: mem_forward m3 m3')
                              nu' (WDnu' : SM_wd nu')
                             (SMvalNu' : sm_valid nu' m1' m3')
                             (MemInjNu' : Mem.inject (as_inj nu') m1' m3')
                             
                             (ExtIncr: extern_incr (compose_sm nu12 nu23) nu')
                             (SMInjSep: sm_inject_separated (compose_sm nu12 nu23) nu' m1 m3)
                             (SMV12: sm_valid nu12 m1 m2)
                             (SMV23: sm_valid nu23 m2 m3)
                             (UnchPrivSrc: Mem.unchanged_on (fun b ofs => locBlocksSrc (compose_sm nu12 nu23) b = true /\ 
                                                      pubBlocksSrc (compose_sm nu12 nu23) b = false) m1 m1') 
                             (UnchLOOR13: Mem.unchanged_on (local_out_of_reach (compose_sm nu12 nu23) m1) m3 m3')

                             (GlueInvNu: SM_wd nu12 /\ SM_wd nu23 /\
                                         locBlocksTgt nu12 = locBlocksSrc nu23 /\
                                         extBlocksTgt nu12 = extBlocksSrc nu23 /\
                                         (forall b, pubBlocksTgt nu12 b = true -> 
                                                    pubBlocksSrc nu23 b = true) /\
                                         (forall b, frgnBlocksTgt nu12 b = true -> 
                                                    frgnBlocksSrc nu23 b = true))
                             (Norm12: forall b1 b2 d1, extern_of nu12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of nu23 b2 = Some(b3, d2))
                             (full: full_ext nu12 nu23),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\
                             Mem.inject (as_inj nu23') m2' m3' /\
                             sm_valid nu12' m1' m2' /\ sm_valid nu23' m2' m3' /\
                             (SM_wd nu12' /\ SM_wd nu23' /\
                              locBlocksTgt nu12' = locBlocksSrc nu23' /\
                              extBlocksTgt nu12' = extBlocksSrc nu23' /\
                              (forall b, pubBlocksTgt nu12' b = true -> 
                                         pubBlocksSrc nu23' b = true) /\
                              (forall b, frgnBlocksTgt nu12' b = true -> 
                                         frgnBlocksSrc nu23' b = true)) /\
                             (forall b1 b2 d1, extern_of nu12' b1 = Some(b2,d1) ->
                                     exists b3 d2, extern_of nu23' b2 = Some(b3, d2)) /\ 
                              Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\ 
                                                             pubBlocksSrc nu23 b = false) m2 m2' /\
                              Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' 
                          (* /\ Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3'*).
Proof. intros.
  destruct (EFF_interp_II_strong _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ 
              Fwd3 _ WDnu' SMvalNu' MemInjNu' ExtIncr
              SMV12 SMV23 UnchPrivSrc UnchLOOR13 GlueInvNu Norm12 full)
  as [m2' [nu12' [nu23' [A [B [C [D [E [F [G [H [I [J [K [L [M ]]]]]]]]]]]]]]]].
  exists m2', nu12', nu23'. intuition.
Qed.



