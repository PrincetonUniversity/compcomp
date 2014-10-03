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


Lemma EFF_interp_II_strong: forall m1 m2 nu12 
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
         destruct output as [j' k'].
       remember (change_ext nu12 extS12 extT12 j') as nu12';
         remember (change_ext nu23 extS23 extT23 k') as nu23'.
       exists (mem_add m2 m1'), nu12', nu23'.
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
       { destruct MInj12. constructor.
         + destruct mi_inj. constructor.
           - move mi_perm at bottom.
             intros. unfold Mem.perm. rewrite mem_add_accx; unfold mem_add_acc.
             subst nu12'. unfold change_ext, as_inj, join in H. destruct nu12; simpl in H.
             inversion Heqoutput; subst j'. unfold add_inj, shiftT in H.
              destruct (j b1) eqn:jb1. destruct p0. inversion H.
              subst j. unfold as_inj, join in mi_perm; simpl in *. 
              apply mi_perm.
              rewrite jb1 in mi_perm.
              apply SMV12.

             destruct (j' b1) eqn:jb1.
             * destruct p0. inversion H; inversion Heqoutput. subst b j'.
               unfold add_inj, shiftT in jb1.
             
 admit. }
       split.
       (* mem_forward *)
       { apply mem_add_forward. }
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
       { apply (mem_unchanged_on_sub _ _ _ _ (mem_add_unchanged m1' m2)).
         intros. destruct SMV23 as [DOMval RNGval].
         apply DOMval. unfold DOM, DomSrc.
         destruct H. rewrite H; auto.
       }
       split.
       { apply (mem_unchanged_on_sub _ _ _ _ (mem_add_unchanged m1' m2)).
         intros. 
         destruct SMV12 as [DOMval RNGval].
         apply RNGval. unfold RNG, DomTgt.
         destruct H. rewrite H; auto. 
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


