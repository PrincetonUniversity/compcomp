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

(****************************
 *       Util lemmas        *
 ****************************)
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
Lemma forward_range:
  forall m m' b ofs size p,
    mem_forward m m' ->
    Mem.valid_block m b ->
    Mem.range_perm m' b ofs (ofs + size) Max p ->
    Mem.range_perm m b ofs (ofs + size) Max p.
  unfold Mem.range_perm; intros.
  apply H; auto.
Qed.
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

(****************************
 *         Tactics          *
 ****************************)
Lemma locT_localmap: forall mu b2 b d,
                       SM_wd mu ->
                       local_of mu b = Some (b2, d) ->
                       locBlocksTgt mu b2 = true.
  intros.
  eapply H in H0. destruct H0 as [locS locT]; auto.
Qed.
Lemma locS_localmap: forall mu b p,
                       SM_wd mu ->
                       local_of mu b = Some p ->
                       locBlocksSrc mu b = true.
  intros. destruct p.
  eapply H in H0. destruct H0 as [locS locT]; auto.
Qed.
Lemma locS_externmap: forall mu b p,
                        SM_wd mu ->
                        extern_of mu b = Some p ->
                        locBlocksSrc mu b = false.
  intros. destruct (locBlocksSrc mu b) eqn:locS; trivial.
  destruct p; eapply H in H0. destruct H0 as [extS extT].
  destruct H as [H ?].
  destruct (H b); 
    [rewrite locS in H0 | rewrite extS in H0]; discriminate.
Qed.
Lemma locT_externmap: forall mu b b2 d,
                        SM_wd mu ->
                        extern_of mu b = Some (b2, d) ->
                        locBlocksTgt mu b2 = false.
  intros. destruct (locBlocksTgt mu b2) eqn:locT; trivial.
  eapply H in H0. destruct H0 as [extS extT].
  destruct H as [HS HT ?].
  destruct (HT b2) as [H | H];
    [rewrite locT in H | rewrite extT in H]; discriminate.
Qed.
Lemma validT_externmap: forall mu b2 b1 d m1 m2,
                          SM_wd mu ->
                          sm_valid mu m1 m2 ->
                          extern_of mu b1 = Some (b2,d) ->
                          Mem.valid_block m2 b2.
  intros. apply H0.  unfold RNG, DomTgt. eapply H in H1. 
  destruct H1. rewrite H2; apply orb_true_r.
Qed.

Lemma validT_localmap: forall mu b2 b1 d m1 m2,
                          SM_wd mu ->
                          sm_valid mu m1 m2 ->
                          local_of mu b1 = Some (b2,d) ->
                          Mem.valid_block m2 b2.
  intros. apply H0.  unfold RNG, DomTgt. eapply H in H1. 
  destruct H1. rewrite H2; apply orb_true_l.
Qed.
Lemma validS_externmap: forall mu b1 p m1 m2,
                          SM_wd mu ->
                          sm_valid mu m1 m2 ->
                          extern_of mu b1 = Some p ->
                          Mem.valid_block m1 b1.
  intros. apply H0.  unfold DOM, DomSrc. destruct p; eapply H in H1. 
  destruct H1. rewrite H1; apply orb_true_r.
Qed.

Lemma validS_localmap: forall mu b1 p m1 m2,
                          SM_wd mu ->
                          sm_valid mu m1 m2 ->
                          local_of mu b1 = Some p ->
                          Mem.valid_block m1 b1.
  intros. apply H0.  unfold DOM, DomSrc. destruct p; eapply H in H1. 
  destruct H1. rewrite H1; apply orb_true_l.
Qed.
Lemma loc_ext_map: forall mu b1 b1' b2 d d',
                     SM_wd mu ->
                     local_of mu b1 = Some (b2, d) ->
                     extern_of mu b1' = Some (b2, d') ->
                     False.
  intros. apply H in H0; apply H in H1; destruct H0, H1.
  destruct H as [HS HT ?]; destruct (HT b2).
  rewrite H2 in H; inversion H.
  rewrite H3 in H; inversion H.
Qed.


Ltac auto_sm:= 
               match goal with
                   | _ => solve [eapply locS_localmap; eassumption]
                   | _ => solve [eapply locT_localmap; eassumption]
                   | _ => solve [eapply locS_externmap; eassumption]
                   | _ => solve [eapply locT_externmap; eassumption]
                   | [ H: local_of ?mu _ = Some (?b2, _ )|- Mem.valid_block _ ?b2 ] => 
                     solve[eapply (validT_localmap mu b2); eassumption]
                   | [ H: local_of ?mu ?b1 = Some _ |- Mem.valid_block _ ?b1 ] => 
                     solve[eapply (validS_localmap mu b1); eassumption]
                   | [ H: extern_of ?mu _ = Some (?b2, _ )|- Mem.valid_block _ ?b2 ] => 
                     solve[eapply (validT_externmap mu b2); eassumption]
                   | [ H: extern_of ?mu ?b1 = Some _ |- Mem.valid_block _ ?b1 ] => 
                     solve[eapply (validS_externmap mu b1); eassumption]
                   | [|- as_inj ?mu ?b1 = _ ] => solve[apply (local_in_all mu); assumption]
                   | [loc: local_of ?mu _ = Some (?b2 , _),
                      ext: extern_of ?mu _ = Some (?b2 , _)|- False ] => 
                     solve[ eapply (loc_ext_map mu); eassumption]
               end.



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
         (Pure: pure_comp_ext nu12 nu23 m1 m2)
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
                                          pure_comp_ext nu12' nu23' m1' m2' /\
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
       (****************************
        * Preparing the hypothesis *
        ****************************)
       destruct GlueInvNu as [SMWD12 [SMWD23 GlueInv]].

       (***************************************
        * Construct the injections and memory *
        ***************************************)
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
       remember (as_inj nu12') as j12'.
       remember (mem_add nu12 nu23 j12' m1 m1' m2) as m2';
       exists m2', nu12', nu23'.
       
       (************************************************
        * Proving some properties of my construction   *
        ************************************************)
       
       (* compose_sm *)
       assert (compose: nu' = compose_sm nu12' nu23').
       { rewrite Heqnu12', Heqnu23'. (*clear - ExtIncr full. *)
         destruct ExtIncr as [extincr [? [? [? [? [? [? [? [? ? ]]]]]]]]].
         unfold compose_sm, change_ext; destruct nu12, nu23, nu'; simpl in *; f_equal; auto.
         eapply (MKIcomposition j k (extern_of1)); subst; eauto.
         intros b p H.  destruct p.
         eapply SMV23. eapply as_inj_DomRng.
         unfold as_inj, join; simpl; rewrite H; eauto.
         apply SMWD23. 
       }
       
       (* extern_incr nu12 nu12' *)
       assert (ExtIncr12: extern_incr nu12 nu12').
       { unfold extern_incr; simpl.
         subst nu12' j k extS12 extT12; destruct nu12;
         unfold extern_incr; simpl.
         destruct ExtIncr as [extincr [? [extS [extT [? [? [? [? [? ? ]]]]]]]]].
         simpl in *.
         intuition.
         eapply MKI_incr12; eauto.
         apply bconcat_larger1; exact H9.
       }

       (* extern_incr nu23 nu23' *)
       assert (ExtIncr23: extern_incr nu23 nu23').
       { unfold extern_incr; simpl.
         subst nu23' j k extS23 extT23; destruct nu23;
         unfold extern_incr; simpl.
         destruct ExtIncr as [extincr [? [extS [extT [? [? [? [? [? ? ]]]]]]]]].
         simpl in *.
         intuition.
         eapply MKI_incr23; eauto.
         apply bconcat_larger1; auto.
       }

       (* mem_forward m2 m2' *)
       assert (Fwd2: mem_forward m2 m2').
       { subst m2'. unfold mem_forward; split.
         + unfold Mem.valid_block in *.
           rewrite mem_add_nbx.
           unfold mem_add_nb.
           xomega.
         + intros ofs per. 
           unfold Mem.perm. rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2); unfold mem_add_acc.
           destruct (valid_dec m2 b); try contradiction.
           destruct (locBlocksSrc nu23 b) eqn: loc23.
           destruct (pubBlocksSrc nu23 b) eqn: pub23; trivial.
           destruct (source (local_of nu12) m1 b ofs) eqn:sour; trivial; destruct p.
           destruct (pubBlocksSrc nu12 b0) eqn: pub12; trivial.
           symmetry in sour. apply source_SomeE in sour.
           destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
           subst ofs; intros H0. eapply MInj12.
           apply local_in_all; eauto.
           eapply Fwd1; auto.
           inversion invertible; subst z b0; auto.
           
           destruct (source (as_inj nu12) m1 b ofs) eqn:sour;
             try solve[destruct (as_inj nu23 b); intros HH;try destruct p; trivial; inversion HH].
           destruct p.
           intros H0.
           symmetry in sour. apply source_SomeE in sour.
           destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
           subst ofs; eapply MInj12; eauto.
           eapply Fwd1; auto.
           inversion invertible; subst z b0; auto.
       }

       (* Mem.unchanged_on private m2 *)
       assert (UnchPrivSrc12 : Mem.unchanged_on
                   (fun (b : block) (_ : Z) =>
                      locBlocksSrc nu23 b = true /\ pubBlocksSrc nu23 b = false) m2 m2').
       { subst m2'. constructor. 
         + intros b ofs k0 p [locS pubS] bval; unfold Mem.perm.
           rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2); unfold mem_add_acc.
           rewrite locS, pubS.
           destruct (valid_dec m2 b); try solve[contradict bval;trivial].
           split; auto.
         + intros b ofs [locS pubS] mperm.
           rewrite (mem_add_contx nu12 nu23 j12' m1 m1' m2); unfold mem_add_cont.
           rewrite locS, pubS.
           destruct (valid_dec m2 b); try solve[trivial].
           (*Invalid case*) apply Mem.perm_valid_block in mperm; contradiction.
       }
       
       (*Mem.unchanged_on local_out_of_reach 12*)
       assert (UnchLOOR12: Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2').
       { subst m2'.
         unfold local_out_of_reach.
         constructor. 
         + intros b ofs k0 p [locT mapcondition] bval; unfold Mem.perm.
           rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2); 
                 unfold mem_add_acc.
           destruct (valid_dec m2 b); try solve[contradict bval;trivial].
           assert (locS: locBlocksSrc nu23 b = true ) by
               (destruct GlueInv as [glue1 rest]; rewrite glue1 in locT; trivial).
           rewrite locS.
           destruct (pubBlocksSrc nu23 b) eqn:pubS;
             destruct (source (local_of nu12) m1 b ofs) eqn:sour;
             try solve [split;auto].
           - symmetry in sour. apply source_SomeE in sour;
             destruct sour as [b0 [d0 [ofs0 [invert [bval' [map12 [mparm of_eq] ]]]]]].
             subst p0 ofs.
             apply mapcondition in map12. clear mapcondition.
             destruct map12 as [mperm1 | pubS1].
             * contradict mperm1. replace (ofs0 + d0 - d0) with ofs0 by omega; trivial.
             * rewrite pubS1; split; auto.
         + intros b ofs [locT mapcondition] mperm; unfold Mem.perm.
           rewrite (mem_add_contx nu12 nu23 j12' m1 m1' m2); 
                 unfold mem_add_cont.
           destruct (valid_dec m2 b).
           - assert (locS: locBlocksSrc nu23 b = true ) by
                 (destruct GlueInv as [glue1 rest]; rewrite glue1 in locT; trivial).
             rewrite locS.
             destruct (pubBlocksSrc nu23 b) eqn:pubS;
               destruct (source (local_of nu12) m1 b ofs) eqn:sour;
               try solve [split;auto].
             symmetry in sour. apply source_SomeE in sour;
              destruct sour as [b0 [d0 [ofs0 [invert [bval' [map12 [mparm of_eq] ]]]]]].
             subst p ofs.
             apply mapcondition in map12. clear mapcondition.
             destruct map12 as [mperm1 | pubS1].
             * contradict mperm1. replace (ofs0 + d0 - d0) with ofs0 by omega; trivial.
             * rewrite pubS1; split; auto.
           - (*Invalid case*) apply Mem.perm_valid_block in mperm; contradiction.
       }
       (*Mem.unchanged_on local_out_of_reach 23*)
       assert (UnchLOOR23: Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3').
       { unfold local_out_of_reach; split; intros.
         + move UnchLOOR13 at bottom; unfold local_out_of_reach in UnchLOOR13.
           apply UnchLOOR13; auto.
           destruct H; split.
           - unfold compose_sm; trivial.
           - unfold compose_sm; simpl; intros.
             unfold compose_meminj in H2. 
             destruct (local_of nu12 b0) eqn:maploc12; try solve[inversion H2].
             destruct p0. destruct (local_of nu23 b1) eqn:maploc23; try solve[inversion H2].
             destruct p0. inversion H2; subst b2 delta; clear H2.
             eapply H1 in maploc23.
             destruct maploc23.
             * left. intros mperm.
               apply H2. replace (ofs - z0) with ((ofs - (z + z0)) + z) by xomega. 
               eapply MInj12; eauto. 
               apply local_in_all; eauto. 
             * right. destruct (pubBlocksSrc nu12 b0) eqn:pubS12; trivial.
               apply SMWD12 in pubS12. destruct pubS12 as [b2 [ofs' [maploc12' pubT12]]].
               rewrite maploc12 in maploc12'; inversion maploc12'; subst b1 z.
               apply GlueInv in pubT12. rewrite pubT12 in H2; inversion H2.
         + move UnchLOOR13 at bottom; unfold local_out_of_reach in UnchLOOR13.
           apply UnchLOOR13; auto.
           destruct H; split.
           - unfold compose_sm; trivial.
           - unfold compose_sm; simpl; intros.
             unfold compose_meminj in H2. 
             destruct (local_of nu12 b0) eqn:maploc12; try solve[inversion H2].
             destruct p. destruct (local_of nu23 b1) eqn:maploc23; try solve[inversion H2].
             destruct p. inversion H2; subst b2 delta; clear H2.
             eapply H1 in maploc23.
             destruct maploc23.
             * left. intros mperm.
               apply H2. replace (ofs - z0) with ((ofs - (z + z0)) + z) by xomega. 
               eapply MInj12; eauto. 
               apply local_in_all; eauto. 
             * right. destruct (pubBlocksSrc nu12 b0) eqn:pubS12; trivial.
               apply SMWD12 in pubS12. destruct pubS12 as [b2 [ofs' [maploc12' pubT12]]].
               rewrite maploc12 in maploc12'; inversion maploc12'; subst b1 z.
               apply GlueInv in pubT12. rewrite pubT12 in H2; inversion H2.
       }
       
       (* pure_comp_ext nu12' nu23' m1' m2 *)
       assert (Pure': pure_comp_ext nu12' nu23' m1' m2').
       { unfold pure_comp_ext.
         subst nu12' nu23' m2'. rewrite ext_change_ext, ext_change_ext.
         split.
         + unfold pure_composition_locat.
           clear - Heqoutput Pure Heqj Heqj12' Heqk SMV12 
                   SMV23 SMWD23 SMWD12 MemInjNu' GlueInv.
           inversion Heqoutput. intros. 
           unfold add_inj in H.
           destruct (k b2) eqn:kmap.
           - destruct p. inversion H. subst b z. 
             rewrite Heqk in kmap. 
             unfold valid_location in H2.
             unfold Mem.perm in H2. rewrite mem_add_accx in H2.
             unfold mem_add_acc in H2. 
             assert (notloc: locBlocksSrc nu23 b2 = false) by auto_sm.
             rewrite notloc in H2.
             destruct (valid_dec m2 b2).
             destruct (source (as_inj nu12) m1 b2 delta) eqn:sour.
             * symmetry in sour; apply source_SomeE in sour.
               destruct sour as [b1 [delta0 [ofs1 [pair [bval1 [jmap12' [mperm' d_eq]]]]]]].
               exists b1, delta0.
               subst p j12'.
               
               assert (jmap: j b1 = Some (b2, delta0)).
               { apply as_in_SomeE in jmap12'. destruct jmap12'; subst j; trivial.
                 apply SMWD12 in H3; destruct H3 as [locS locT].
                 apply SMWD23 in kmap; destruct kmap as [extS extT].
                 destruct GlueInv as [loc rest]; rewrite loc in locT.
                 destruct SMWD23. destruct (disjoint_extern_local_Src b2) as [loc'| ext'].
                 rewrite locT in loc'; inversion loc'.
                 rewrite extS in ext'; inversion ext'.
                 }
               unfold add_inj. rewrite jmap; split; auto.
               unfold valid_location. 
               subst delta. replace (ofs1 + delta0 - delta0) with ofs1 by omega. auto.
             * unfold as_inj, join in H2; rewrite kmap in H2. 
               inversion H2.
             * contradict n. apply SMV23. unfold DOM, DomSrc. apply SMWD23 in kmap.
               destruct kmap as [extS extT]; rewrite extS; apply orb_true_r.
           - 
             apply shiftS_Some in H; destruct H as [ineq lmap'].
             apply pure_filter_Some in lmap'; destruct lmap' as [jNone lmap'].
              generalize H2; unfold valid_location; intros.
             unfold Mem.perm in H3.
             rewrite mem_add_accx in H3. unfold mem_add_acc in H3.
             destruct (valid_dec m2 b2).
             contradict v. clear - ineq. unfold Mem.valid_block. xomega.
             exists (b2 - Mem.nextblock m2)%positive, 0.
             split. unfold add_inj.
             rewrite jNone.
             unfold shiftT, filter_id. rewrite lmap'.
             replace (b2 - Mem.nextblock m2 + Mem.nextblock m2)%positive with b2; auto. 
             symmetry; apply Pos.sub_add; xomega.
             destruct (source j12' m1' b2 delta) eqn:sour; try solve [inversion H3]. destruct p.
             replace (delta - 0) with delta by omega; auto.
             symmetry in sour; apply source_SomeE in sour.
             destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
             inversion invertible; subst delta b z. clear invertible.
             {(*is external and b2 > nextblock m2... must be mapped by l shifted*)
               subst j12'. 
               apply as_in_SomeE in mapj; destruct mapj as [extmap | locmap].
               + rewrite ext_change_ext in extmap. eapply MKI_Some12 in extmap; eauto.
                 destruct extmap as [jmap | [jmap [b2' [d' [lmap'' [Heqb2 delta0]]]]]].
                 - contradict n; subst j; auto_sm.
                 - subst b2.
                   subst delta'.
                   rewrite Pos.add_sub; replace (ofs1 + 0) with ofs1 by omega; trivial.
               + rewrite loc_change_ext in locmap. contradict n; auto_sm.
               }
         + unfold pure_composition_block.
           inversion Heqoutput.
           subst j' k'.
           intros.
           unfold add_inj in H.
           destruct (k b2) eqn:kmap.
           - destruct p. inversion H. subst b z. 
             rewrite Heqk in kmap. 
             apply Pure in kmap; destruct kmap as [b1 [ofs12 jmap]].
             exists b1, ofs12.
             unfold add_inj. subst j; rewrite jmap; auto.
           - apply shiftS_Some in H; destruct H as [ineq lmap'].
             apply pure_filter_Some in lmap'; destruct lmap' as [jNone lmap'].
             exists (b2 - Mem.nextblock m2)%positive, 0.
             unfold add_inj.
             rewrite jNone.
             unfold shiftT, filter_id. rewrite lmap'.
             replace (b2 - Mem.nextblock m2 + Mem.nextblock m2)%positive with b2; auto. 
             symmetry; apply Pos.sub_add. xomega.
       }
       
       (* SM_wd 12 *)
       assert (SMWD12': SM_wd nu12').
       { subst nu12'. eapply MKI_wd12; eauto.
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
           destruct SMWD12. destruct (disjoint_extern_local_Tgt b) as [locFalse | extFalse].
           rewrite locBT12 in locFalse; inversion locFalse.
           rewrite extFalse; simpl.
           destruct SMV12 as [DOM12 RNG12].
           subst sizeM2;
             rewrite RNG12; auto.
           unfold RNG, DomTgt.
           rewrite locBT12; auto.
         + inversion Heqoutput. unfold add_inj, shiftT; intros.
           destruct (j b1) eqn:jb1. 
         - rewrite H in jb1. subst j.
           destruct SMWD12. apply extern_DomRng in jb1. destruct jb1 as [extS12true extT12true].
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
             apply SMWD12 in H.
             exact H.
       }

       
       (* SM_wd 23 *)
       assert (SMWD23': SM_wd nu23').
       { subst nu23'; eapply MKI_wd23; eauto.
         + subst extS23; intros.
           destruct (locBlocksSrc nu23 b) eqn:locBS23; auto.
           right. 
           unfold bconcat, buni, bshift.
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
         - rewrite H in kb1. subst k.
           destruct SMWD23. apply extern_DomRng in kb1. destruct kb1 as [extS23true extT23true].
           subst extS23 extT23. destruct ExtIncr as [? [? [extS [extT [locS [locT ?]]]]]].
           simpl in extT; apply extT in extT23true.
           rewrite extT23true; split; trivial.
           apply bconcat_larger1; auto.
         - rename H into lb1. inversion lb1.
           destruct ((b1 ?= Mem.nextblock m2)%positive) eqn:ineq; try solve [inversion H2].
           subst extS23 extT23. subst l'.
           destruct WDnu'.
           apply pure_filter_Some in lb1; destruct lb1 as [jmap lb1].
           apply extern_DomRng in lb1.
           destruct lb1 as [extStrue extTtrue].
           split; auto.             
           replace b1 with ((b1 - sizeM2) + sizeM2)%positive; 
             subst sizeM2. apply bconcat_larger2; auto.
           apply Pos.sub_add; destruct (Pos.compare_gt_iff b1 (Mem.nextblock m2)). 
           apply H; auto.
           + intros. subst extT23. destruct ExtIncr as [? [? [extS [extT [locS [locT ?]]]]]].
             apply extT; simpl; auto.
             apply SMWD23 in H; auto.
       }

       (****************************
        * Proving each condition   *
        ****************************)

       split.
       (*Compose_sm*)
       { exact compose. } 
       split.
       (* extern_incr12 *)
       { exact ExtIncr12. }
       split.
       (* extern_incr23 *)
       { exact ExtIncr23. }
       split.
       (* pure compositoin *)
       { exact Pure'. }
       split.
       (* Mem.inject 12*)
       { (* Prove no overlapping of nu12' first *)
         assert (no_overlap12': Mem.meminj_no_overlap j12' m1').
         { subst j12'.         
           apply no_overlap_asinj; auto.
           subst nu12'; rewrite ext_change_ext.
         (*Mem.meminj_no_overlap j' m1'*)
         + eapply MKI_no_overlap12; eauto.
           - subst j. apply no_overlap_ext.
             apply MInj12.
           - subst l'; apply no_overlap_ext; eapply MemInjNu'.
           - intros. apply SMV12. unfold DOM, DomSrc. subst j; apply SMWD12 in H.
             destruct H as [extS extT]; rewrite extS; apply orb_true_r.
           - intros. apply SMV12. unfold RNG, DomTgt. subst j; apply SMWD12 in H.
             destruct H as [extS extT]; rewrite extT; apply orb_true_r.
         (*Mem.meminj_no_overlap (local_of nu12') m1'*)
         + subst nu12'; rewrite loc_change_ext.
           eapply no_overlap_loc; eauto.
           eapply no_overlap_forward; eauto.
           apply MInj12. }
         
         (* Prove Mem.inject12*)
         constructor.
         + constructor.
         - { intros b1 b2 delta ofs k0 per H H0. subst m2'.
             unfold Mem.perm; rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2); 
             unfold mem_add_acc.
             (* New trying things*)
             unfold as_inj in H; apply joinD_Some in H; 
             destruct H as [extmap | [extNone locmap]].
             + subst nu12'; rewrite ext_change_ext in extmap.
               eapply MKI_Some12 in extmap; eauto. 
               destruct extmap as [jmap | [jmap [b2' [d' [lmap' [b2eq deltaeq]]]]]].
             - assert (Mem.valid_block m2 b2) by (subst j; auto_sm).
               destruct (valid_dec m2 b2); try solve[contradict n; auto].
               assert (locF: locBlocksSrc nu23 b2 = false).
               { destruct GlueInv as [loc rest]; rewrite <- loc.
                 subst j; auto_sm. }
               rewrite locF.
               erewrite source_SomeI. apply H0.
               * apply MInj12.
               * unfold as_inj, join. 
                 subst j. rewrite jmap; auto.
               * eapply Fwd1.
                 subst j; auto_sm.
                 eapply any_Max_Nonempty; eauto. 
             - destruct (valid_dec m2 b2); (*first discharge the impossible case*)
               try solve[subst b2; contradict v; unfold Mem.valid_block; xomega].
               subst b2 delta. 
               erewrite (source_SomeI j12' m1' ).
               eapply H0.
               exact no_overlap12'.
               subst j12'.
               unfold as_inj, join. rewrite ext_change_ext, loc_change_ext.
               assert (j' b1 = Some ((b1 + Mem.nextblock m2)%positive , 0)). 
               { inversion Heqoutput. unfold add_inj, shiftT, filter_id.
                 rewrite jmap, lmap'; auto. }
               rewrite H. auto.
                 eapply any_Max_Nonempty; eauto. 
             + subst nu12'; rewrite loc_change_ext in locmap.
               assert (locTrue: locBlocksSrc nu23 b2 = true).
               { destruct GlueInv as [loc rest]; rewrite <- loc; auto_sm. }
               rewrite locTrue.
               rewrite ext_change_ext in extNone.
               assert (Mem.valid_block m2 b2).
               { apply SMV12. unfold RNG, DomTgt. apply SMWD12 in locmap. 
                 destruct locmap as [locS locT]; rewrite locT; apply orb_true_l. }
               destruct (valid_dec m2 b2); try solve[contradict n; auto].

                (*prove that (k b2 = None) by contradiction*)
                 destruct (k b2) eqn: kmap. subst k.
                 { destruct p; apply Pure in kmap.
                   destruct kmap as [b1' [ofs12 extmap12]].
                   contradict extmap12. intros HH. auto_sm.
                 }
                 destruct ( pubBlocksSrc nu23 b2) eqn:pub23.
                 erewrite (source_SomeI (local_of nu12) m1); eauto.
                  destruct (pubBlocksSrc nu12 b1) eqn:pub12.
                 auto.

                 (* pubBlocksSrc nu23 b2 = true & pubBlocksSrc nu12 b1 = false *)
                  assert (Permb1: Mem.perm m1 b1 ofs k0 per).
                 { eapply UnchPrivSrc; eauto;
                   unfold compose_sm; simpl; apply SMWD12 in locmap; destruct locmap; auto.
                   eapply SMV12. unfold DOM, DomSrc. rewrite H1; auto. }
                 eapply MInj12; eauto.
                 auto_sm. (*local mapped*)
                 eapply (meminj_no_overlap_inject_incr (as_inj nu12)).
                 apply MInj12.
                 apply local_in_all; auto.
                 { apply Fwd1. 
                 eapply SMV12; apply SMWD12 in locmap; 
                 destruct locmap; auto; unfold DOM, DomSrc.
                 rewrite H1; auto.  eapply any_Max_Nonempty; eauto. }
                 
                 (* pubBlocksSrc nu23 b2 = false & "pubBlocksSrc nu12 b1 = false"/proved *)
                 destruct (pubBlocksSrc nu12 b1) eqn:pub12.
                 { (*this case yields contradiction*)
                   apply SMWD12 in pub12. destruct pub12 as [b2' [z [loc12 pubTgt]]].
                   rewrite locmap in loc12; inversion loc12; subst b2' z.
                   apply GlueInv in pubTgt.
                   rewrite pubTgt in pub23; discriminate pub23. }
                  assert (Permb1: Mem.perm m1 b1 ofs k0 per).
                 { eapply UnchPrivSrc; eauto;
                   unfold compose_sm; simpl; apply SMWD12 in locmap; destruct locmap; auto.
                   eapply SMV12. unfold DOM, DomSrc. rewrite H1; auto. }
                 eapply MInj12; eauto.
                 auto_sm.
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
           
           eapply forward_range; eauto.
           clear H. 
           
           eapply mapped_valid.
           apply SMWD12. 
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
           apply SMWD12.
           eapply forward_range; eauto.
           eapply mapped_valid.
           apply SMWD12. 
           unfold as_inj. 
           rewrite join_com. 
           unfold join; rewrite H; trivial.
           apply disjoint_extern_local.
           apply SMWD12.
           eauto.
         - (*mi_memval12*) (*HERE*)
           { intros b1 ofs b2 delta map12' mperm1'. subst m2'.
             unfold Mem.perm; rewrite (mem_add_contx nu12 nu23 j12' m1 m1' m2); unfold mem_add_cont.
             (* New trying things*)
             unfold as_inj in map12'; apply joinD_Some in map12'; destruct map12' as [extmap | [extNone locmap]].
             + subst nu12'; rewrite ext_change_ext in extmap.
               eapply MKI_Some12 in extmap; eauto. 
               destruct extmap as [jmap | [jmap [b2' [d' [lmap' [b2eq deltaeq]]]]]].
             - assert (Mem.valid_block m2 b2) by (subst j; auto_sm).
               destruct (valid_dec m2 b2); try solve[contradict n; auto].
               assert (locF: locBlocksSrc nu23 b2 = false).
               { destruct GlueInv as [loc rest]; rewrite <- loc.
                 subst j; auto_sm. }
               rewrite locF.
               erewrite source_SomeI.
               destruct MemInjNu'. destruct mi_inj.
               (*Prepare to use mi_memval of nu'*)
               assert (map13': exists b3 d3, as_inj nu' b1 = Some (b3, d3)).
               {assert (kmap:=jmap).
               apply Norm12 in kmap; destruct kmap as [b3 [d2 kmap]].
               exists b3, (delta + d2).
               unfold as_inj, join. destruct ExtIncr as [ext_incr other_incr]. 
               erewrite ext_incr; eauto.
               rewrite compose_sm_extern. subst j.
               unfold compose_meminj.
               rewrite jmap.
               subst k. rewrite kmap; auto.
               }
               destruct map13' as [b3 [d3 map13']].
               { (*memval_inject part*)
               apply (mi_memval b1 ofs b3 d3 map13') in mperm1'.
               instantiate(1:=b1).
               inversion mperm1'; try constructor.
               remember ( change_ext nu12 extS12 extT12 j') as nu12'.
               rewrite compose in H2.
               unfold as_inj in H2.
               { (*Two cases, whether b0 is external or local*)
                 destruct (joinD_Some _ _ _ _ _ H2) as [extcomp | [extcomp loccomp]].
                 + (* b0 is external*)
                   rewrite compose_sm_extern in extcomp.
                   apply compose_meminjD_Some in extcomp.
                   destruct extcomp as [b1' [ofs1' [ofs' [ext12 [ext23 eq]]]]].
                   subst nu12'; rewrite ext_change_ext in ext12.
                   unfold inject_memval, join .
                   subst j12'; unfold as_inj, join; rewrite ext_change_ext.
                   
                   rewrite ext12.
                   econstructor; auto.
                   rewrite ext12.
                   reflexivity.
                 + (* b0 is local / need to show it's public!*)
                   rewrite compose_sm_local in loccomp.
                   apply compose_meminjD_Some in loccomp.
                   destruct loccomp as [b1' [ofs1' [ofs' [loc12 [loc23 eq]]]]].
                   subst nu12'. rewrite loc_change_ext in loc12.
                   (* Now let us prove that j b0 = None, to prove jp b0 = b1', ofs1'*)
                   assert (jmap0': j' b0 = None). 
                   { remember ( change_ext nu12 extS12 extT12 j') as nu12'.
                     destruct SMWD12'. 
                     assert (forall b, local_of nu12 b = local_of nu12' b) by
                     (intros; subst nu12'; rewrite loc_change_ext; auto).
                     rewrite H4 in loc12.
                     apply local_DomRng in loc12.
                     destruct loc12 as [locS' locT'].
                     destruct (j' b0) eqn:jmap'; auto. destruct p.
                     assert (forall b, j' b = extern_of nu12' b) by
                     (intros; subst nu12'; rewrite ext_change_ext; auto).
                     rewrite H5 in jmap'. apply extern_DomRng in jmap'.
                     destruct jmap' as [extS' extT'].
                     destruct (disjoint_extern_local_Src b0) as [locS'' | extS''].
                     rewrite locS'' in locS'; inversion locS'.
                     rewrite extS'' in extS'; inversion extS'. }
                   unfold inject_memval, join. 
                   subst j12'; unfold as_inj, join; rewrite ext_change_ext, loc_change_ext.
                   rewrite jmap0'. rewrite loc12.
                   econstructor.
                   rewrite jmap0'; eauto.
                   auto. } }
               * apply MInj12.
               * unfold as_inj, join. 
                 subst j. rewrite jmap; auto.
               * eapply Fwd1.
                 subst j; auto_sm.
                 eapply any_Max_Nonempty; eauto. 
             - destruct (valid_dec m2 b2); (*first discharge the impossible case*)
               try solve[subst b2; contradict v; unfold Mem.valid_block; xomega].
               erewrite (source_SomeI j12' m1' ).
               subst b2 delta.
                (* replace (ofs + 0) with ofs by omega; trivial. *)
               unfold inject_memval.
               { (*memval_inject part*)
                  destruct MemInjNu'. destruct mi_inj.
               (*Prepare to use mi_memval of nu'*)
               assert (map13': exists b3 d3, as_inj nu' b1 = Some (b3, d3)). 
               { exists b2', d'. unfold as_inj, join.  subst l'.
                 rewrite lmap'; auto. }
               destruct map13' as [b3 [d3 map13']].
               apply (mi_memval b1 ofs b3 d3 map13') in mperm1'.
               instantiate(1:=b1).
               inversion mperm1'; try constructor.
               remember ( change_ext nu12 extS12 extT12 j') as nu12'.
               rewrite compose in H1.
               unfold as_inj in H1.
               { (*Two cases, whether b0 is external or local*)
                 destruct (joinD_Some _ _ _ _ _ H1) as [extcomp | [extcomp loccomp]].
                 + (* b0 is external*)
                   rewrite compose_sm_extern in extcomp.
                   apply compose_meminjD_Some in extcomp.
                   destruct extcomp as [b1' [ofs1' [ofs' [ext12 [ext23 eq]]]]].
                   subst nu12'; rewrite ext_change_ext in ext12.
                   unfold inject_memval, join .
                   subst j12'; unfold as_inj, join; rewrite ext_change_ext.
                   rewrite ext12.
                   econstructor; auto.
                   rewrite ext12.
                   reflexivity.
                 + (* b0 is local / need to show it's public!*)
                   rewrite compose_sm_local in loccomp.
                   apply compose_meminjD_Some in loccomp.
                   destruct loccomp as [b1' [ofs1' [ofs' [loc12 [loc23 eq]]]]].
                   subst nu12'. rewrite loc_change_ext in loc12.
                   (* Now let us prove that j b0 = None, to prove jp b0 = b1', ofs1'*)
                   assert (jmap0': j' b0 = None). 
                   {  remember ( change_ext nu12 extS12 extT12 j') as nu12'.
                     destruct SMWD12'. 
                     assert (forall b, local_of nu12 b = local_of nu12' b) by
                     (intros; subst nu12'; rewrite loc_change_ext; auto).
                     rewrite H3 in loc12.
                     apply local_DomRng in loc12.
                     destruct loc12 as [locS' locT'].
                     destruct (j' b0) eqn:jmap'; auto. destruct p.
                     assert (forall b, j' b = extern_of nu12' b) by
                     (intros; subst nu12'; rewrite ext_change_ext; auto).
                     rewrite H4 in jmap'. apply extern_DomRng in jmap'.
                     destruct jmap' as [extS' extT'].
                     destruct (disjoint_extern_local_Src b0) as [locS'' | extS''].
                     rewrite locS'' in locS'; inversion locS'.
                     rewrite extS'' in extS'; inversion extS'. }
                   unfold inject_memval, join. 
                   subst j12'; unfold as_inj, join; rewrite ext_change_ext, loc_change_ext.
                   rewrite jmap0'. rewrite loc12.
                   econstructor.
                   rewrite jmap0'; eauto.
                   auto. } }
               exact no_overlap12'.
               subst j12'.
               unfold as_inj, join. rewrite ext_change_ext, loc_change_ext.
               assert (j' b1 = Some ((b1 + Mem.nextblock m2)%positive , 0)).
               { inversion Heqoutput. unfold add_inj, shiftT, filter_id.
                 rewrite jmap, lmap'; auto. }
               rewrite H. subst delta b2. auto.
                 eapply any_Max_Nonempty; eauto. 
             + subst nu12'; rewrite loc_change_ext in locmap.
               assert (locTrue: locBlocksSrc nu23 b2 = true).
               { destruct GlueInv as [loc rest]; rewrite <- loc; auto_sm. }
               rewrite locTrue.
               rewrite ext_change_ext in extNone.
               assert (Mem.valid_block m2 b2).
               { apply SMV12. unfold RNG, DomTgt. apply SMWD12 in locmap. 
                 destruct locmap as [locS locT]; rewrite locT; apply orb_true_l. }
               destruct (valid_dec m2 b2); try solve[contradict n; auto].

                (*prove that (k b2 = None) by contradiction*)
                 destruct (k b2) eqn: kmap. subst k.
                 { destruct p; apply Pure in kmap.
                   destruct kmap as [b1' [ofs12 extmap12]].
                   contradict extmap12. intros HH. auto_sm.
                 }
                 destruct ( pubBlocksSrc nu23 b2) eqn:pub23.
                 erewrite (source_SomeI (local_of nu12) m1); eauto.
                 destruct (pubBlocksSrc nu12 b1) eqn:pub12.
                 { destruct (pubSrc _ SMWD23 _ pub23) as [b3 [d2 [Pub23 PubTgt3]]].
                   assert (Nu'b1: as_inj nu' b1 = Some (b3, delta+d2)).
                   { rewrite compose. rewrite Heqnu23'.
                     unfold as_inj, join, compose_sm, compose_meminj; simpl.
                     rewrite ext_change_ext, loc_change_ext, loc_change_ext.
                     rewrite extNone, locmap.
                     erewrite (pub_in_local nu23 b2); eauto. }
                   eapply (Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MemInjNu')) in mperm1'; 
                     eauto. 
                   inversion mperm1'; try econstructor.
                   apply inject_memval_memval_inject.
                   subst j12'; auto.
                   unfold inject_memval.
                   subst j12'.
                   rewrite compose in H2. rewrite compose_sm_as_inj in H2; eauto.
                   apply compose_meminjD_Some in H2. 
                   destruct H2 as [bb1 [ofs1' [ofs' [map12 [map23 ofseq]]]]].
                   rewrite map12. intros HH; inversion HH.
                   subst nu23'; unfold change_ext. 
                   destruct nu12, nu23; simpl; apply GlueInv.
                   subst nu23'; unfold change_ext. 
                   destruct nu12, nu23; simpl. 
                   subst extT12; subst extS23; simpl.
                   f_equal; apply GlueInv.
                 }
                 
                 (* pubBlocksSrc nu23 b2 = true & pubBlocksSrc nu12 b1 = false *)
                 assert (PK: Mem.perm m1 b1 ofs Cur Readable).
                 eapply UnchPrivSrc; eauto. unfold compose_sm; simpl; split; auto; auto_sm.
                 auto_sm. 
                 destruct UnchPrivSrc as [_ UPS].
                  rewrite UPS; try assumption; try (split; assumption).
                  eapply memval_inject_incr.
                    apply MInj12; eauto.
                    apply local_in_all; auto.
                    apply extern_incr_as_inj; eauto.
                    unfold compose_sm; simpl; split; auto; auto_sm.

                     eapply meminj_no_overlap_inject_incr.
                      apply MInj12.
                      apply local_in_all.
                      assumption.
                     eapply any_Max_Nonempty.
                      apply Fwd1; eauto.
                      auto_sm.
                      eapply any_Max_Nonempty; eauto.
                 
                 (* pubBlocksSrc nu23 b2 = false & "pubBlocksSrc nu12 b1 = false"/proved *)
                 destruct (pubBlocksSrc nu12 b1) eqn:pub12.
                 { (*this case yields contradiction*)
                   apply SMWD12 in pub12. destruct pub12 as [b2' [z [loc12 pubTgt]]].
                   rewrite locmap in loc12; inversion loc12; subst b2' z.
                   apply GlueInv in pubTgt.
                   rewrite pubTgt in pub23; discriminate pub23. }
                 assert (PK: Mem.perm m1 b1 ofs Cur Readable).
                 eapply UnchPrivSrc; eauto. unfold compose_sm; simpl; split; auto; auto_sm.
                 auto_sm. 
                 destruct UnchPrivSrc as [_ UPS].
                  rewrite UPS; try assumption; try (split; assumption).
                  eapply memval_inject_incr.
                    apply MInj12; eauto.
                    apply local_in_all; auto.
                    apply extern_incr_as_inj; eauto.
                    unfold compose_sm; simpl; split; auto; auto_sm.
           }
       + intros. unfold as_inj; subst nu12'; rewrite ext_change_ext, loc_change_ext.
         assert (H0: ~ Mem.valid_block m1 b). 
         { clear - H Fwd1. unfold not, Mem.valid_block in *.
           intros; apply H. apply (Pos.lt_le_trans _ _ _ H0).
           apply forward_nextblock; assumption. }
         destruct MInj12, MemInjNu'.
         apply mi_freeblocks in H0; destruct (as_injD_None _ _ H0) as [ext loc].
         apply mi_freeblocks0 in H; destruct (as_injD_None _ _ H) as [ext' loc'].
         unfold join.
         erewrite MKI_None12; eauto; subst j k l'; eauto.
       + unfold as_inj; subst nu12' m2'.
         intros b b' delta map; destruct (as_in_SomeE _ _ _ _ map) as [ext | loc].
         rewrite ext_change_ext in ext. 
         destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ ext).
         destruct MInj12.
         unfold Mem.valid_block; rewrite mem_add_nbx; unfold mem_add_nb.
         eapply Pos.lt_trans; try eapply (Pos.lt_add_diag_r (Mem.nextblock m2)).
         apply (mi_mappedblocks b b' delta).
         unfold as_inj, join; subst j k l'; rewrite H; auto.
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
         destruct SMWD12.
         apply local_DomRng in loc; destruct loc as [locS locT].
         destruct SMV12 as [DOMv RNGv].
         assert (Plt b' m2.(Mem.nextblock)).
         apply RNGv. unfold RNG, DomTgt. rewrite locT; apply orb_true_l.
         xomega.
       + subst j12'; exact no_overlap12'. (*Proven earlier*)
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
           
           eapply valid_from_map. 
           apply SMWD12.
           apply map12.
           eassumption.
           assumption.

           eapply Fwd1.
           eapply valid_from_map. apply SMWD12.
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
           { apply local_in_all; auto. }
           destruct MInj12. eapply mi_representable; eauto. 
           destruct H0; [left | right].
           eapply Fwd1; eauto.
           eapply (valid_from_map nu12); eauto.
           eapply Fwd1; eauto.
           eapply (valid_from_map nu12); eauto.
           }
       split.
       (* mem_forward *)
       { exact Fwd2. }
       split.
       (* Mem.inject 23*)
       { subst m2'; constructor.
         + constructor.
         - { intros b1 b2 delta ofs k0 p map23.
             unfold Mem.perm. rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2); unfold mem_add_acc.
             unfold as_inj in map23; apply joinD_Some in map23.
             destruct map23 as [extmap | [extmap locmap]].
             + subst nu23'.
               rewrite ext_change_ext in extmap.
               eapply MKI_Some23 in extmap; eauto. 
               destruct extmap as [kmap | [kmap [lmap' bGt]]].
               - assert (bavl: Mem.valid_block m2 b1).
                 { apply SMV23; eauto. 
                   unfold DOM; eapply as_inj_DomRng; eauto.
                   apply extern_in_all; subst k; eauto. }
                 destruct (valid_dec m2 b1); try solve[contradict n; auto].
                 
                 assert (locS: locBlocksSrc nu23 b1 = false) by (subst k; auto_sm).
                 rewrite locS.
                 destruct (source (as_inj nu12) m1 b1 ofs) eqn:sour.
                 * symmetry in sour. destruct (source_SomeE _ _ _ _ _ sour) 
                    as [b1' [delta' [ofs1 [pairs [bval [jpmap [mperm ofss]]]]]]].
                   subst ofs p0. 
                   replace (ofs1 + delta' + delta) with (ofs1 + (delta' + delta)) by omega.
                   eapply MemInjNu'.
                   (*as_inj nu' b1' = Some (b2, delta' + delta)*)
                   { apply as_in_SomeE in jpmap. destruct jpmap as [extmap | locmap].
                     + unfold as_inj, join.
                       rewrite compose, compose_sm_extern. unfold compose_meminj.
                       apply ExtIncr12 in extmap; rewrite extmap.
                       subst k; apply ExtIncr23 in kmap.
                       rewrite kmap. auto. 
                     + (*impossible case*) 
                       eapply SMWD12 in locmap; destruct locmap as [locS' locT'].
                       destruct GlueInv as [loc rest]; rewrite loc in locT'.
                       rewrite locT' in locS; inversion locS.
                   }
                 * subst k; rewrite (extern_in_all _ _ _ _ kmap).
                   intros H; inversion H.
               - assert (bval: ~ Mem.valid_block m2 b1).
                 { unfold Mem.valid_block, Plt, Pos.lt. intros HH. 
                   rewrite bGt in HH. inversion HH. }
                 destruct (valid_dec m2 b1); try solve [contradict bval; trivial].
                 destruct (source j12' m1' b1 ofs) eqn:sour; try solve[intros H; inversion H].
                 symmetry in sour. destruct (source_SomeE _ _ _ _ _ sour) 
                                   as [b1' [delta' [ofs1 [pairs [bval' [jpmap [mperm ofss]]]]]]].
                 subst ofs p0.
                 replace (ofs1 + delta' + delta) with (ofs1 + (delta' + delta)) by omega.
                 eapply MemInjNu'.
                 { (*as_inj nu' b1' = Some (b2, delta' + delta)*)
                   subst j12'. apply as_in_SomeE in jpmap.
                   destruct jpmap as [extmap | locmap].
                   + subst nu12'; rewrite ext_change_ext in extmap.
                     eapply MKI_Some12 in extmap; eauto.
                     destruct extmap as [jmap | [jmap [b2' [d' [lmap'' [b1eq deltaeq]]]]]].
                     - contradict n. subst j; auto_sm.
                     - subst b1 delta'. replace (0 + delta) with delta by omega.
                       unfold as_inj, join. 
                       rewrite compose, compose_sm_extern, ext_change_ext.
                       inversion Heqoutput.
                       unfold compose_meminj, add_inj, shiftT, filter_id.
                       rewrite jmap, lmap''.
                       rewrite ext_change_ext, kmap.
                       unfold pure_filter, shiftS.
                       rewrite bGt. rewrite Pos.add_sub, jmap. 
                       rewrite Pos.add_sub in lmap'.
                       rewrite lmap'; auto.
                   + contradict n. subst nu12'. rewrite loc_change_ext in locmap. auto_sm.
                 }
             + subst nu23' ; rewrite loc_change_ext in locmap.
               assert (bavl: Mem.valid_block m2 b1).
               { apply SMV23; eauto. 
                 unfold DOM; eapply as_inj_DomRng; eauto.
                 apply local_in_all; eauto. }
               destruct (valid_dec m2 b1); try solve [contradict n; trivial].
               assert (locS: locBlocksSrc nu23 b1 = true) by auto_sm.
               rewrite locS.
               destruct (pubBlocksSrc nu23 b1) eqn:pubS.
               - destruct (source (local_of nu12) m1 b1 ofs) eqn:sour.
                 
                 *  symmetry in sour. destruct (source_SomeE _ _ _ _ _ sour) 
                                     as [b1' [delta' [ofs1 [pairs [bval' [jpmap [mper ofss]]]]]]].
                   inversion pairs; subst ofs p0; clear sour.
                   replace (ofs1 + delta' + delta) with (ofs1 + (delta' + delta)) by omega.
                   destruct (pubBlocksSrc nu12 b1') eqn: pubS12.
                   intros mperm. eapply MemInjNu'.
                   apply local_in_all; auto. rewrite compose; unfold compose_sm; simpl.
                   rewrite loc_change_ext; unfold compose_meminj.
                   instantiate(1:=b1').
                   (*Attention*)
                   (*This thing behaeve weirdly! check what happens if you don't instantiate...*)
                   assert (locmap12': local_of nu12' b1' = Some (b1, delta')).
                   { move ExtIncr12 at bottom; unfold extern_incr in ExtIncr12.
                     destruct ExtIncr12 as [? [loc_inc ?]].
                     rewrite <- loc_inc; eauto. } 
                   rewrite locmap12'; rewrite locmap; auto.
                   assumption.

                   
                   intros. eapply UnchLOOR13. 
                   unfold local_out_of_reach; unfold compose_sm; simpl; split.
                   auto_sm.
                   intros b0; intros.
                   destruct (pubBlocksSrc nu12 b0) eqn:pubS12'; try (right; reflexivity).
                   unfold compose_meminj in H1. 
                   destruct (local_of nu12 b0) eqn:locmap12; try solve[inversion H1].
                   destruct p0.
                   destruct (eq_block b0 b1'); try subst b0.
                   rewrite pubS12 in pubS12'; discriminate.
                   left; intros N. 
                   apply local_in_all in locmap12; trivial.
                   apply local_in_all in locmap; trivial.
                   assert (MX: Mem.perm m2 b1 (ofs1 + delta') Max Nonempty).
                   {eapply Mem.perm_max; eapply Mem.perm_implies. eassumption. apply perm_any_N. }
                   destruct (Mem.inject_compose _ _ _ _ _ MInj12 MInj23). 
                   edestruct (mi_no_overlap b0 b2); try eassumption.
                   { destruct (local_of nu23 b) eqn:loc23; try solve[inversion H1]. 
                     destruct p0. instantiate (1:=delta0).
                     inversion H1; subst b3 delta0.
                     unfold compose_meminj; rewrite locmap12. 
                     erewrite (local_in_all nu23); eauto. }
                   instantiate(1:=delta' + delta). 
                   { instantiate(1:=b2). unfold compose_meminj.
                      erewrite (local_in_all nu12); eauto. 
                      rewrite locmap; auto. }
                   apply H2; auto.
                   apply H2; omega.
                   auto_sm.
                   replace  (ofs1 + (delta' + delta))  with  (ofs1 + delta' + delta) by omega. 
                   eapply MInj23.
                   eapply local_in_all; eauto.
                   auto.

                   
                 * (*This case is impossible NOT*)
                   intros.
                   eapply UnchLOOR13.
                   unfold local_out_of_reach; unfold compose_sm; simpl; split.
                   auto_sm.
                   intros b0; intros.
                   unfold compose_meminj in H0.
                   destruct (local_of nu12 b0) eqn:locmap12; try solve [inversion H0].
                   destruct p0.
                   destruct (local_of nu23 b) eqn:locmap23; try solve [inversion H0].
                   destruct p0; inversion H0. subst b2 delta0. clear H0.
                   
                   destruct (eq_block b b1); try subst b.
                   rewrite locmap in locmap23; inversion locmap23; subst delta.
                   
                   symmetry in sour; eapply (source_NoneE) in sour; eauto.
                   destruct (pubBlocksSrc nu12 b0) eqn:pubS12'; try (right; reflexivity).
                   left.
                   replace (ofs + z0 - (z + z0)) with (ofs - z) by omega; eauto.
                   assert (valid:Mem.valid_block m1 b0) by auto_sm; apply valid.
                   left; intros N. apply local_in_all in locmap12; trivial.
                   apply (Mem.perm_inject (as_inj nu12) _ _ _ _ _ _ _ _ locmap12 MInj12) in N.            
                   edestruct (Mem.mi_no_overlap _ _ _ MInj23 b).
                   exact n.
                   apply local_in_all; first [exact SMWD23 | exact locmap23].
                   apply local_in_all; first [exact SMWD23 | exact locmap].
                   exact N.
                   eapply any_Max_Nonempty. exact H.
                   apply H0; trivial.
                   apply H0; trivial.
                   omega.
                   auto_sm.
                   eapply MInj23. 
                   apply local_in_all; first [exact SMWD23 | exact locmap].
                   exact H.
               -
               {
               intros. eapply UnchLOOR23.
               unfold local_out_of_reach; split.
               auto_sm.
               intros bb2; intros.
               destruct (pubBlocksSrc nu23 bb2) eqn:pubS23; try (right; reflexivity).
               destruct (eq_block bb2 b1); try subst bb2.
                 rewrite pubS23 in pubS; discriminate.
               left; intros N. 
               apply local_in_all in H0; trivial.
               apply local_in_all in locmap; trivial.
                   assert (MX: Mem.perm m2 b1 ofs Max Nonempty).
                   {eapply Mem.perm_max; eapply Mem.perm_implies. eassumption. apply perm_any_N. }
                   destruct (Mem.mi_no_overlap _ _ _ MInj23 bb2 _ _ _ _ _ _ _ n H0 locmap N MX).
                   apply H1; trivial.
                   apply H1; clear H1. omega.
                   auto_sm.
                   eapply MInj23. apply local_in_all; eauto. apply H.
               }
             }
         - intros. unfold Z.divide.
           subst nu23'; unfold as_inj, join in H. rewrite ext_change_ext, loc_change_ext in H.
           destruct (k' b1) eqn:kmap'. 
           * destruct p0. destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ kmap') as 
                          [kmap | [kmap [ lmap bGt]]].
           inversion H; subst b z.
           subst k. destruct MInj23. destruct mi_inj.
           eapply (mi_align b1 b2); eauto. 
           unfold as_inj, join; rewrite kmap; trivial.
           eapply forward_range; eauto.
           eapply mapped_valid.
           apply SMWD23. 
           unfold as_inj, join; rewrite kmap; auto. 
           eauto.

           unfold Mem.range_perm, Mem.perm in H0.
           rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2) in H0; unfold mem_add_acc in H0.
           destruct (valid_dec m2 b1).
           { contradict v. unfold not, Mem.valid_block. clear - bGt.
             unfold Plt, Pos.lt. intros H; rewrite H in bGt; inversion bGt. }
           
           
           (* This should be folded in a lemma *)
          (* inversion Heqoutput. inversion H; subst b z.
           unfold add_inj, shiftS in H3. rewrite H3 in kmap'. rewrite kmap in kmap'.
           destruct (b1 ?= Mem.nextblock m2)%positive; try solve[inversion kmap'].
           apply pure_filter_Some in kmap'. destruct kmap' as [jmap lmap'].*)
           inversion H; subst b z. 
           eapply MemInjNu'.
           eapply extern_in_all. subst l'. 
           instantiate(1:=b2). instantiate(1:=(b1 - Mem.nextblock m2)%positive). 
            exact lmap.
            unfold Mem.range_perm.
            intros ofs0 H1. apply H0 in H1.
            destruct (source j12' m1' b1 ofs0) eqn:sour; try solve [inversion H1].

            
            symmetry in sour; apply source_SomeE in sour.
            destruct sour as [b1' [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
            subst p0 ofs0.
            subst j12'. unfold as_inj, join in mapj. 
            
            inversion Heqoutput.
            subst nu12'. rewrite ext_change_ext in mapj.
            rewrite H3 in mapj.
            unfold add_inj in mapj. 
            destruct ( j b1') eqn:jmap. destruct p0; inversion mapj; subst b1 delta'.
            {contradict n. 
            apply SMV12. unfold RNG, DomTgt.
            subst j. apply SMWD12 in jmap. destruct jmap as [extS extT]; rewrite extT.
            apply orb_true_r. }
            unfold filter_id, shiftT in mapj.
            { (*Show b1' = b1 - sizeM2 /\ delta' = 0 *)
              destruct (l' b1') eqn:lmap'. inversion mapj; subst b1 delta'.
              + rewrite Pos.add_sub; replace (ofs1 +0) with ofs1 by omega; eauto.
              + rewrite loc_change_ext in mapj.
                assert (Mem.valid_block m2 b1) by auto_sm.
                unfold Mem.valid_block, Plt, Pos.lt in H2.
                rewrite H2 in bGt; inversion bGt. }
           * eapply MInj23; try assumption.
             apply local_in_all; eauto; exact H.
             intros z; intros. specialize (H0 _ H1).
             apply Fwd2; eauto. auto_sm.
                
         - { (*mi_memval23*)
             intros b1 ofs b2 delta map23.
             unfold Mem.perm. 
             rewrite (mem_add_contx nu12 nu23 j12' m1 m1' m2); unfold mem_add_cont.
              rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2); unfold mem_add_acc.
             unfold as_inj in map23; apply joinD_Some in map23.
             destruct map23 as [extmap | [extmap locmap]].
             + subst nu23'.
               rewrite ext_change_ext in extmap.
               eapply MKI_Some23 in extmap; eauto. 
               destruct extmap as [kmap | [kmap [lmap' bGt]]].
               - assert (bavl: Mem.valid_block m2 b1).
                 { apply SMV23; eauto. 
                   unfold DOM; eapply as_inj_DomRng; eauto.
                   apply extern_in_all; subst k; eauto. }
                 destruct (valid_dec m2 b1); try solve[contradict n; auto].
                 
                 assert (locS: locBlocksSrc nu23 b1 = false) by (subst k; auto_sm).
                 rewrite locS.
                 destruct (source (as_inj nu12) m1 b1 ofs) eqn:sour.
                 * symmetry in sour. destruct (source_SomeE _ _ _ _ _ sour) 
                    as [b1' [delta' [ofs1 [pairs [bval [jpmap [mperm' ofss]]]]]]].
                   subst ofs p. 
                   replace (ofs1 + delta' + delta) with (ofs1 + (delta' + delta)) by omega.
                   (*Do the memval*)
                   destruct MemInjNu'. destruct mi_inj.
                   move mi_memval at bottom. 
                   intros mperm.
                   eapply (mi_memval _ _ b2 (delta' + delta)) in mperm.
                   inversion mperm; try constructor.
                   unfold inject_memval. 
                   subst j12'. 
                   remember (change_ext nu23 extS23 extT23 k') as nu23'.
                   
                   assert (maps: exists b2' ofs1 ofs2, as_inj nu12' b0 = Some (b2',ofs1)
                           /\ as_inj nu23' b2' = Some (b3, ofs2)
                           /\ delta0 = ofs1 + ofs2 ).
                   { apply as_in_SomeE in H1; rewrite compose in H1;
                     destruct H1 as [extmap | locmap].
                     + rewrite compose_sm_extern  in extmap.
                       apply compose_meminjD_Some in extmap.
                       destruct extmap as [b2' [ofs1' [ofs2' [ext12 [ext23 deltaeq ] ]]]].
                       exists b2', ofs1', ofs2'.
                       split. apply extern_in_all; auto.
                       split. apply extern_in_all; auto.
                       auto.
                     + rewrite compose_sm_local in locmap.
                       apply compose_meminjD_Some in locmap.
                       destruct locmap as [b2' [ofs1' [ofs2' [ext12 [ext23 deltaeq ] ]]]].
                       exists b2', ofs1', ofs2'.
                       split. apply local_in_all; auto.
                       split. apply local_in_all; auto.
                       auto.
                   }
                   destruct maps as [b2' [ofs1' [ofs2'  [map12' [map23' ofseq]]]]].
                   rewrite map12'.
                   econstructor. 
                   exact map23'.
                   subst ofs2 delta0. 
                   { (* Int arithmetics *)
                     rewrite Int.add_assoc. f_equal.
                     rewrite Int.add_unsigned.
                     apply Int.eqm_samerepr.
                     apply Int.eqm_add;
                     apply Int.eqm_unsigned_repr. }
                   {(*as_inj nu' b1' = Some (b2, delta' + delta)*)
                   subst j12'. apply as_in_SomeE in jpmap.
                   destruct jpmap as [extmap | locmap].
                   + rewrite compose; unfold as_inj, join, compose_sm, compose_meminj.
                     simpl. eapply ExtIncr12 in extmap; rewrite extmap.
                     subst k; eapply ExtIncr23 in kmap.
                     rewrite kmap; auto.
                   + apply SMWD12 in locmap; destruct locmap as [locS' locT'].
                     destruct GlueInv as [loc rest]; rewrite loc in locT'.
                     subst k; apply SMWD23 in kmap; destruct kmap as [extS extT].
                     destruct SMWD23 as [Src rest'].
                     destruct (Src b1) as [ locSTrue | extSTrue].
                     rewrite locSTrue in locT'; inversion locT'.
                     rewrite extSTrue in extS; inversion extS.
                   }
                 * subst k; rewrite (extern_in_all _ _ _ _ kmap).
                   intros H; inversion H.
               - assert (bval: ~ Mem.valid_block m2 b1). 
                 { unfold Mem.valid_block, Plt, Pos.lt; intros HH.
                   rewrite HH in bGt; inversion bGt. }
                 destruct (valid_dec m2 b1); try solve [contradict bval; trivial].
                 destruct (source j12' m1' b1 ofs) eqn:sour; try solve[intros H; inversion H].
                 symmetry in sour. destruct (source_SomeE _ _ _ _ _ sour) 
                                   as [b1' [delta' [ofs1 [pairs [bval' [jpmap [mperm ofss]]]]]]].
                 subst ofs p.
                 replace (ofs1 + delta' + delta) with (ofs1 + (delta' + delta)) by omega.
                 (*Do the memval*)
                 destruct MemInjNu'. destruct mi_inj.
                 move mi_memval at bottom. 
                 intros mperm'.
                 eapply (mi_memval _ _ b2 (delta' + delta)) in mperm'.
                 inversion mperm'; try constructor.
                 unfold inject_memval. 
                 subst j12'. 
                 remember (change_ext nu23 extS23 extT23 k') as nu23'.
                 assert (maps: exists b2' ofs1 ofs2, as_inj nu12' b0 = Some (b2',ofs1)
                           /\ as_inj nu23' b2' = Some (b3, ofs2)
                           /\ delta0 = ofs1 + ofs2 ).
                   { apply as_in_SomeE in H1; rewrite compose in H1;
                     destruct H1 as [extmap | locmap].
                     + rewrite compose_sm_extern  in extmap.
                       apply compose_meminjD_Some in extmap.
                       destruct extmap as [b2' [ofs1' [ofs2' [ext12 [ext23 deltaeq ] ]]]].
                       exists b2', ofs1', ofs2'.
                       split. apply extern_in_all; auto.
                       split. apply extern_in_all; auto.
                       auto.
                     + rewrite compose_sm_local in locmap.
                       apply compose_meminjD_Some in locmap.
                       destruct locmap as [b2' [ofs1' [ofs2' [ext12 [ext23 deltaeq ] ]]]].
                       exists b2', ofs1', ofs2'.
                       split. apply local_in_all; auto.
                       split. apply local_in_all; auto.
                       auto.
                   }
                 destruct maps as [b2' [ofs1' [ofs2' [map12' [map23' ofseq]]]]].
                 rewrite map12'.
                 econstructor. 
                 exact map23'.
                 subst ofs2 delta0. 
                 {  (* Int arithmetics *)
                     rewrite Int.add_assoc. f_equal.
                     rewrite Int.add_unsigned.
                     apply Int.eqm_samerepr.
                     apply Int.eqm_add;
                     apply Int.eqm_unsigned_repr. }
                 {(*as_inj nu' b1' = Some (b2, delta' + delta)*)
                   subst j12'. apply as_in_SomeE in jpmap.
                   destruct jpmap as [extmap | locmap].
                   + assert (extmap':=extmap).
                     eapply (MKI_Some12 j k l') in extmap';
                       try solve [subst nu12'; rewrite ext_change_ext; eauto].
                     destruct extmap' as [jmap | [jmap [b2' [d' [lmap2 [b2eq delteq]]]]]].
                   - contradict n; subst j; auto_sm.
                   - subst b1 delta'.
                     (* Now just rewrite in compose *)
                     rewrite compose; unfold as_inj, join, compose_sm, compose_meminj.
                     simpl. rewrite extmap.
                     rewrite ext_change_ext. inversion Heqoutput.
                     unfold add_inj, pure_filter, shiftS.
                     rewrite kmap, bGt, lmap'.
                     rewrite Pos.add_sub, jmap.
                     f_equal; omega.
                   + contradiction n. subst nu12'. rewrite loc_change_ext in locmap. auto_sm.
                 }
             + subst nu23' ; rewrite loc_change_ext in locmap.
               assert (bavl: Mem.valid_block m2 b1).
               { apply SMV23; eauto. 
                 unfold DOM; eapply as_inj_DomRng; eauto.
                 apply local_in_all; eauto. }
               destruct (valid_dec m2 b1); try solve [contradict n; trivial].
               assert (locS: locBlocksSrc nu23 b1 = true) by auto_sm.
               rewrite locS.
               destruct (pubBlocksSrc nu23 b1) eqn:pubS.
               - destruct (source (local_of nu12) m1 b1 ofs) eqn:sour.
                 
                 *  symmetry in sour. destruct (source_SomeE _ _ _ _ _ sour) 
                                     as [b1' [delta' [ofs1 [pairs [bval' [jpmap [mper ofss]]]]]]].
                   inversion pairs; subst ofs p; clear sour.
                   replace (ofs1 + delta' + delta) with (ofs1 + (delta' + delta)) by omega.
                   destruct (pubBlocksSrc nu12 b1') eqn: pubS12.
                   intros mperm. 
                   (*Do the memval*)
                   destruct MemInjNu'. destruct mi_inj.
                   move mi_memval at bottom. 
                   eapply (mi_memval _ _ b2 (delta' + delta)) in mperm.
                   inversion mperm; try constructor.
                   unfold inject_memval. 
                   subst j12'. 
                   remember (change_ext nu23 extS23 extT23 k') as nu23'.
                 
                 assert (maps: exists b2' ofs1 ofs2, as_inj nu12' b0 = Some (b2',ofs1)
                           /\ as_inj nu23' b2' = Some (b3, ofs2)
                           /\ delta0 = ofs1 + ofs2 ).
                   { apply as_in_SomeE in H2; rewrite compose in H2;
                     destruct H2 as [extmap' | locmap'].
                     + rewrite compose_sm_extern  in extmap'.
                       apply compose_meminjD_Some in extmap'.
                       destruct extmap' as [b2' [ofs1' [ofs2' [ext12 [ext23 deltaeq ] ]]]].
                       exists b2', ofs1', ofs2'.
                       split. apply extern_in_all; auto.
                       split. apply extern_in_all; auto.
                       auto.
                     + rewrite compose_sm_local in locmap'.
                       apply compose_meminjD_Some in locmap'.
                       destruct locmap' as [b2' [ofs1' [ofs2' [ext12 [ext23 deltaeq ] ]]]].
                       exists b2', ofs1', ofs2'.
                       split. apply local_in_all; auto.
                       split. apply local_in_all; auto.
                       auto.
                   }
                   destruct maps as [b2' [ofs1' [ofs2' [map12' [map23' ofseq]]]]].
                   rewrite map12'.
                   econstructor. 
                   exact map23'.
                   subst ofs2 delta0. 
                   { (* Int arithmetics *)
                     rewrite Int.add_assoc. f_equal.
                     rewrite Int.add_unsigned.
                     apply Int.eqm_samerepr.
                     apply Int.eqm_add;
                     apply Int.eqm_unsigned_repr. }
                   
                   (*Why did I have to prove this again?*)
                   apply local_in_all; auto.
                   rewrite compose, compose_sm_local, loc_change_ext.
                   unfold compose_meminj; subst nu12'. 
                   rewrite loc_change_ext, jpmap, locmap; auto.
                   
                   intros. 
                   destruct UnchLOOR13.
                   rewrite unchanged_on_contents.
                   eapply memval_inject_incr. 
                   replace (ofs1 + (delta' + delta)) with (ofs1 + delta' + delta) by omega.
                   eapply MInj23.
                   auto_sm.
                   exact H0.
                   apply extern_incr_as_inj; eauto.

                   unfold local_out_of_reach; unfold compose_sm; simpl; split.
                   auto_sm.
                   intros b0; intros.
                   destruct (pubBlocksSrc nu12 b0) eqn:pubS12'; try (right; reflexivity).
                   unfold compose_meminj in H1. 
                   destruct (local_of nu12 b0) eqn:locmap12; try solve[inversion H1].
                   destruct p.
                   destruct (eq_block b0 b1'); try subst b0.
                   rewrite pubS12 in pubS12'; discriminate.
                   left; intros N. 
                   apply local_in_all in locmap12; trivial.
                   apply local_in_all in locmap; trivial.
                   assert (MX: Mem.perm m2 b1 (ofs1 + delta') Max Nonempty).
                   {eapply Mem.perm_max; eapply Mem.perm_implies. eassumption. apply perm_any_N. }
                   destruct (Mem.inject_compose _ _ _ _ _ MInj12 MInj23). 
                   edestruct (mi_no_overlap b0 b2); try eassumption.
                   { destruct (local_of nu23 b) eqn:loc23; try solve[inversion H1]. 
                     destruct p. instantiate (1:=delta0).
                     inversion H1; subst b3 delta0.
                     unfold compose_meminj; rewrite locmap12. 
                     erewrite (local_in_all nu23); eauto. }
                   instantiate(1:=delta' + delta). 
                   { instantiate(1:=b2). unfold compose_meminj.
                      erewrite (local_in_all nu12); eauto. 
                      rewrite locmap; auto. }
                   apply H2; auto.
                   apply H2; omega.
                   replace  (ofs1 + (delta' + delta))  with  (ofs1 + delta' + delta) by omega. 
                   eapply MInj23.
                   eapply local_in_all; eauto.
                   auto.

                 * (*This case is impossible NOT*)
                   intros. 
                   destruct UnchLOOR13.
                   rewrite unchanged_on_contents.
                   eapply memval_inject_incr. 
                   eapply MInj23.
                   auto_sm.
                   exact H.
                   apply extern_incr_as_inj; eauto.
                   
                   unfold local_out_of_reach; unfold compose_sm; simpl; split.
                   auto_sm.
                   intros b0; intros.
                   unfold compose_meminj in H0.
                   destruct (local_of nu12 b0) eqn:locmap12; try solve [inversion H0].
                   destruct p.
                   destruct (local_of nu23 b) eqn:locmap23; try solve [inversion H0].
                   destruct p; inversion H0. subst b2 delta0. clear H0.
                   
                   destruct (eq_block b b1); try subst b.
                   rewrite locmap in locmap23; inversion locmap23; subst delta.
                   
                   symmetry in sour; eapply (source_NoneE) in sour; eauto.
                   destruct (pubBlocksSrc nu12 b0) eqn:pubS12'; try (right; reflexivity).
                   left.
                   replace (ofs + z0 - (z + z0)) with (ofs - z) by omega; eauto.
                   assert (valid:Mem.valid_block m1 b0) by auto_sm; apply valid.
                   left; intros N. apply local_in_all in locmap12; trivial.
                   apply (Mem.perm_inject (as_inj nu12) _ _ _ _ _ _ _ _ locmap12 MInj12) in N.            
                   edestruct (Mem.mi_no_overlap _ _ _ MInj23 b).
                   exact n.
                   apply local_in_all; first [exact SMWD23 | exact locmap23].
                   apply local_in_all; first [exact SMWD23 | exact locmap].
                   exact N.
                   eapply any_Max_Nonempty. exact H.
                   apply H0; trivial.
                   apply H0; trivial.
                   omega.
                   eapply MInj23. 
                   apply local_in_all; first [exact SMWD23 | exact locmap].
                   exact H.
               -
                 {intros. 
                   destruct UnchLOOR23.
                   rewrite unchanged_on_contents.
                   eapply memval_inject_incr. 
                   eapply MInj23.
                   auto_sm.
                   exact H.
                   apply extern_incr_as_inj; eauto.
                 
                   unfold local_out_of_reach; split.
                   destruct GlueInv as [loc rest].
                   unfold compose_sm; simpl; auto_sm.
                   intros bb2; intros.
                   destruct (pubBlocksSrc nu23 bb2) eqn:pubS23; try (right; reflexivity).
                   destruct (eq_block bb2 b1); try subst bb2.
                   rewrite pubS23 in pubS; discriminate.
                   left; intros N. 
                   apply local_in_all in H0; trivial.
                   apply local_in_all in locmap; trivial.
                   assert (MX: Mem.perm m2 b1 ofs Max Nonempty).
                   {eapply Mem.perm_max; eapply Mem.perm_implies. eassumption. apply perm_any_N. }
                   destruct (Mem.mi_no_overlap _ _ _ MInj23 bb2 _ _ _ _ _ _ _ n H0 locmap N MX).
                   apply H1; trivial.
                   apply H1; clear H1. omega.
                   eapply MInj23. apply local_in_all; eauto. apply H.
               }
             }
      + intros b H. unfold Mem.valid_block in H.
        rewrite (mem_add_nbx nu12 nu23 j12' m1 m1' m2) in H.
        unfold mem_add_nb in H.
        destruct (as_inj nu23' b) eqn:map; trivial.
        contradict H. unfold as_inj in map; destruct p.
        destruct (joinD_Some _ _ _ _ _ map) as [extmap | [extmap locmap]].
         - subst nu23'. rewrite ext_change_ext in extmap.
           inversion Heqoutput; subst k'.
           unfold add_inj in extmap. 
           destruct (k b) eqn:kmap.
           assert (Mem.valid_block m2 b).
           { eapply SMV23. unfold DOM, DomSrc.
             inversion extmap; subst p k. apply SMWD23 in kmap.
             destruct kmap as [extS extT]; rewrite extS; apply orb_true_r. }
           unfold Mem.valid_block in H. apply (Plt_trans _ _ _ H); xomega.
           apply shiftS_Some in extmap.
           destruct extmap.
           apply pure_filter_Some in H1; destruct H1.
           { assert (Mem.valid_block m1' (b - Mem.nextblock m2)%positive ) 
               by (subst l'; auto_sm).
           unfold Mem.valid_block in H3. clear - H H3. 
           unfold Plt in *. 
           apply Pos.lt_iff_add; apply Pos.lt_iff_add in H3. destruct H3 as  [r sum].
           exists r. 
           rewrite Pos.add_comm in *.
           rewrite <- sum.
           rewrite (Pos.add_comm (Mem.nextblock m2) (r + (b - Mem.nextblock m2))).
           rewrite <- Pos.add_assoc.
           rewrite Pos.sub_add; eauto.
           apply Pos.gt_lt_iff; auto. }
           
         - assert (Mem.valid_block m2 b).
           { eapply SMV23. unfold DOM, DomSrc. subst nu23'.
             rewrite loc_change_ext in locmap.
             apply SMWD23 in locmap.
             destruct locmap as [locS locT]; rewrite locS; apply orb_true_l. }
           unfold Mem.valid_block in H. apply (Plt_trans _ _ _ H); xomega.
       + intros b b' d H.
         unfold as_inj. 
         subst nu23'; destruct (joinD_Some _ _ _ _ _ H) as [extmap | [extmap locmap]].
         - rewrite ext_change_ext in extmap.
           inversion Heqoutput; subst k'.
            unfold add_inj in extmap. 
            destruct (k b) eqn:kmap.
           assert (Mem.valid_block m3 b').
           { eapply SMV23. unfold RNG, DomTgt.
             inversion extmap; subst p k. apply SMWD23 in kmap.
             destruct kmap as [extS extT]; rewrite extT; apply orb_true_r. }
           eapply Fwd3 in H0. destruct H0; auto.
           apply shiftS_Some in extmap.
           destruct extmap.
           apply pure_filter_Some in H2.
           destruct H2 as [? ?].
           apply SMvalNu'.
           unfold RNG, DomTgt.
           subst l'. apply WDnu' in H3; destruct H3. rewrite H4; apply orb_true_r.
         - assert (Mem.valid_block m3 b').
           { eapply SMV23. unfold RNG, DomTgt.
             rewrite loc_change_ext in locmap.
             apply SMWD23 in locmap.
             destruct locmap as [locS locT]; rewrite locT; apply orb_true_l. }
           eapply Fwd3 in H0. destruct H0; auto.
       + intros.
         eapply no_overlap_asinj; auto.
         - { (*no_overlap extern*)
             unfold Mem.meminj_no_overlap; intros.
             subst nu23'. rewrite ext_change_ext in H0, H1.
             inversion Heqoutput; subst k'.
             unfold add_inj in H0, H1. 
             destruct (k b1) eqn:kmap1; destruct (k b2) eqn:kmap2. 
             (*1. Good case old externs *)
             eapply MInj23.
             apply H.
             eapply extern_in_all; auto.
             inversion H0; subst k p; trivial.
             eapply extern_in_all; auto.
             inversion H1; subst k p0; trivial.
             apply Fwd2; eauto.
             subst k; auto_sm.
             apply Fwd2; eauto.
             subst k ; auto_sm.
             (*2.cross case: Dificult case *)
             { rewrite H0 in kmap1.
               apply shiftS_Some in H1. destruct H1.
               apply pure_filter_Some in H4. destruct H4.
               inversion H0; subst p; clear H0.
               rewrite Heqk in kmap1.
               assert(kmap1':=kmap1).
               unfold Mem.perm in H2, H3.
               rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2) in H2, H3; 
                 unfold mem_add_acc in H2,H3.
               assert (Mem.valid_block m2 b1) by auto_sm.
               destruct (valid_dec m2 b1); 
                 try solve[destruct n; eauto].
               destruct (valid_dec m2 b2).
               { (* impossible case. *)
               move v0 at bottom.
               unfold Mem.valid_block, Plt, Pos.lt in v0. 
               unfold Pos.gt in H1. rewrite H1 in v0; inversion v0. }
               destruct (source j12' m1' b2 ofs2) eqn:sour2; try solve[inversion H3].
               assert (locF: locBlocksSrc nu23 b1 = false) by auto_sm.
               rewrite locF in H2.
               assert (totmap23: as_inj nu23 b1 = Some (b1', delta1)) 
                 by (apply extern_in_all; trivial).
               rewrite totmap23 in H2.
               destruct (source (as_inj nu12) m1 b1 ofs1) eqn:sour1; try solve[inversion H2].
               symmetry in sour1, sour2. apply source_SomeE in sour1; apply source_SomeE in sour2.
               destruct sour1 as [b01 [d01 [ofs01 [invert1 [bval1' [map121 [mparm1 of_eq1] ]]]]]].
               subst p0 ofs1.
               destruct sour2 as [b02 [d02 [ofs02 [invert2 [bval2' [map122 [mparm2 of_eq2] ]]]]]].
               subst p ofs2.
               replace (ofs01 + d01 + delta1) with (ofs01 + (d01 + delta1)) by omega.
               replace (ofs02 + d02 + delta2) with (ofs02 + (d02 + delta2)) by omega.
               assert (H': b01<> (b2 - Mem.nextblock m2)%positive).
               { intros HH; subst b01.
                 unfold as_inj, join in map121. rewrite Heqj in H4; rewrite H4 in map121.
                 eapply SMWD12 in map121. destruct map121. destruct GlueInv as [loc rest].
                 rewrite loc in H8. rewrite locF in H8; inversion H8. }
               
               (*We prove (d02 = 0) /\ (b02 = (b2 - Mem.nextblock m2)%positive) *)
               subst j12' nu12'. unfold as_inj, join in map122.
               rewrite ext_change_ext in map122.
               inversion Heqoutput; subst j'.
               unfold add_inj, shiftT, filter_id in map122.
               destruct (j b02) eqn:jmap. 
               { (*First case is impossible *)
                 destruct p; inversion map122; subst b2 d02.
                 contradict n. subst j; auto_sm. }
               destruct (l' b02) eqn:lmap'; 
                 (*second case is impossible *)
                 try solve [rewrite loc_change_ext in map122; contradict n; auto_sm].
               inversion map122; subst b2 d02.
               eapply MemInjNu'.
               apply H'.
               {
               subst nu'.
               unfold as_inj, join.
               rewrite compose_sm_extern, ext_change_ext.
               rewrite compose_sm_local, loc_change_ext.
               rewrite ext_change_ext, loc_change_ext.
               assert (jmap11: j b01 = Some (b1, d01)).
                 { unfold as_inj in map121. 
                   apply joinD_Some in map121; destruct map121 as [extmap|[extmap locmap]].
                   subst j; exact extmap.
                   eapply SMWD12 in locmap. destruct locmap as [locS locT].
                   eapply SMWD23 in kmap1. destruct kmap1 as [extS extT].
                   destruct GlueInv as [loc rest]; rewrite loc in locT.
                   destruct SMWD23. 
                   destruct (disjoint_extern_local_Src b1) as [locS'|extS'].
                   rewrite locS' in locT; inversion locT.
                   rewrite extS' in extS; inversion extS. }
               unfold compose_meminj. unfold add_inj.
               rewrite jmap11. subst k. rewrite kmap1. auto. }
               { (*First show d02 = 0*)
                 replace (0 + delta2) with delta2 by omega.
                 unfold as_inj, join. 
                 subst l'; rewrite H6. auto. }
               auto.
               rewrite Pos.add_sub; auto. }
             (*3.cross case: Dificult case *)
             { rewrite H1 in kmap2.
               apply shiftS_Some in H0. destruct H0.
               apply pure_filter_Some in H4. destruct H4.
               inversion H1; subst p; clear H1.
               rewrite Heqk in kmap2.
               assert(kmap2':=kmap2).
               unfold Mem.perm in H2, H3.
               rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2) in H2, H3; 
                 unfold mem_add_acc in H2,H3.
               assert (Mem.valid_block m2 b2) by auto_sm.
               destruct (valid_dec m2 b2) eqn:bval2; 
                 try solve[destruct n; eauto].
               destruct (valid_dec m2 b1) eqn:bval1.
               { unfold Mem.valid_block, Plt, Pos.lt in v0. move v0 at bottom.
               unfold Pos.gt in H0. rewrite v0 in H0; inversion H0. }
               destruct (source j12' m1' b1 ofs1) eqn:sour1; try solve[inversion H2].
               assert (locF: locBlocksSrc nu23 b2 = false) by auto_sm.
               rewrite locF in H3.
               assert (totmap23: as_inj nu23 b2 = Some (b2', delta2)) 
                 by (apply extern_in_all; trivial).
               rewrite totmap23 in H3.
               destruct (source (as_inj nu12) m1 b2 ofs2) eqn:sour2; try solve[inversion H3].
               symmetry in sour1, sour2. apply source_SomeE in sour1; apply source_SomeE in sour2.
               destruct sour1 as [b01 [d01 [ofs01 [invert1 [bval1' [map121 [mparm1 of_eq1] ]]]]]].
               subst p ofs1.
               destruct sour2 as [b02 [d02 [ofs02 [invert2 [bval2' [map122 [mparm2 of_eq2] ]]]]]].
               subst p0 ofs2.
               replace (ofs01 + d01 + delta1) with (ofs01 + (d01 + delta1)) by omega.
               replace (ofs02 + d02 + delta2) with (ofs02 + (d02 + delta2)) by omega.

               (*We prove (d01 = 0) /\ (b01 = (b1 - Mem.nextblock m2)%positive) *)
               subst j12' nu12'. unfold as_inj, join in map121.
               rewrite ext_change_ext in map121.
               inversion Heqoutput; subst j'.
               unfold add_inj, shiftT, filter_id in map121.
               destruct (j b01) eqn:jmap. 
               { (*First case is impossible *)
                 destruct p; inversion map121. subst b1 d01.
                 exfalso. apply n. subst j; auto_sm. }
               destruct (l' b01) eqn:lmap';
                 (*second case is impossible *)
                 try solve [ rewrite loc_change_ext in map121; exfalso; apply n; auto_sm].
               inversion map121; subst b1 d01.
               assert (H': b01 <> b02). 
               { destruct (peq b01 b02); trivial.
                 subst b02. (*  *)
                 unfold as_inj in map122; apply joinD_Some in map122; 
                 destruct map122 as [extmap | [xtmap locmap]].
                 subst j; rewrite jmap in extmap; inversion extmap.
                 apply SMWD12 in locmap; destruct locmap as [locS locT].
                 rewrite Pos.add_sub in H6. rewrite Heql' in H6; apply WDnu' in H6.
                 destruct H6 as [extS' extT'].
                 destruct ExtIncr as [injinc [ ? [ ? [? [locSeq [locTeq ?]]]]]].
                 unfold compose_sm in locSeq; simpl in locSeq; rewrite locSeq in locS.
                 destruct WDnu'. destruct (disjoint_extern_local_Src b01) as [locST|extST].
                 rewrite locST in locS; inversion locS.
                 rewrite extST in extS'; inversion extS'. }
               eapply MemInjNu'.
               apply H'.
               { replace (0 + delta1) with delta1 by omega.
                 unfold as_inj, join. 
                 rewrite Pos.add_sub in H6;  subst l'; rewrite H6; auto. }
               {
               subst nu'.
               unfold as_inj, join.
               rewrite compose_sm_extern, ext_change_ext.
               rewrite compose_sm_local, loc_change_ext.
               rewrite ext_change_ext, loc_change_ext.
               assert (jmap12: j b02 = Some (b2, d02)).
               + unfold as_inj in map122; apply joinD_Some in map122;
                 destruct map122 as [extmap | [extmap locmap]].
                 - subst j; exact extmap.
                 - apply SMWD12 in locmap; destruct locmap as [locS locT].
                   subst k; apply SMWD23 in kmap2; destruct kmap2 as [extS extT].
                   destruct GlueInv as [loc rest]; rewrite loc in locT. destruct SMWD23. 
                   destruct(disjoint_extern_local_Src b2) as [locS'|extS'].
                   rewrite locS' in locT; inversion locT.
                   rewrite extS' in extS; inversion extS.
               + unfold compose_meminj. unfold add_inj.
                 rewrite jmap12. subst k. rewrite kmap2. auto. }
               auto. auto.
            } 
             { (*4. El caso de nu'*)
               apply shiftS_Some in H0; apply shiftS_Some in H1.
               destruct H0 as [bval1 pfmap1]; destruct H1 as [bval2 pfmap2].
               apply pure_filter_Some in pfmap1; apply pure_filter_Some in pfmap2.
               destruct pfmap1 as [jmpa1 lmap1']; destruct pfmap2 as [jmap2 lmap2'].
               
               unfold Mem.perm in H2, H3.
               rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2) in H2, H3; 
                 unfold mem_add_acc in H2,H3.
               destruct (valid_dec m2 b1).
               {contradict v. unfold Mem.valid_block. xomega. }
               destruct (valid_dec m2 b2).
               {contradict v. unfold Mem.valid_block. xomega. }
               destruct (source j12' m1' b1 ofs1) eqn:source1; try solve[inversion H2].
               destruct (source j12' m1' b2 ofs2) eqn:source2; try solve[inversion H3].
               assert (H': (b1 - Mem.nextblock m2)%positive <> (b2 - Mem.nextblock m2)%positive).
               { intros eq. apply H. clear - eq bval2 bval1.
                 remember (Mem.nextblock m2) as nb.
                 assert (b1 - nb + nb = b2 - nb + nb)%positive by (rewrite eq; auto).
                 rewrite Pos.sub_add in H; unfold Plt; try apply Pos.gt_lt_iff; auto.
                 rewrite Pos.sub_add in H; unfold Plt; try apply Pos.gt_lt_iff; auto. }
               eapply MemInjNu'.
               apply H'.
               unfold as_inj, join. subst l'; rewrite lmap1'; auto.
               unfold as_inj, join. subst l'; rewrite lmap2'; auto.
               { (*Use the source luke*)
                 (*also use Norm!*)
                 destruct p, p0.
                 symmetry in source1; apply source_SomeE in source1.
                 destruct source1 as 
                     [b02 [delta [ofs2' [invert [ineq [jmap [mperm ofseq]]]]]]].
                 inversion invert; subst b02 ofs2'.
                 (*now I prove that l' is the one mapping. *)
                 subst j12'; subst nu12'. unfold as_inj in jmap.
                 apply joinD_Some in jmap; destruct jmap as [extmap|[extmap locmap]].
                 + rewrite ext_change_ext in extmap.
                   rewrite H5 in extmap.
                   unfold add_inj, filter_id, shiftT in extmap.
                   destruct (j b) eqn:jmap.
                   - contradict n. inversion extmap; subst p. subst j; auto_sm.
                   - destruct (l' b) eqn:lmap; try solve [inversion extmap].
                   inversion extmap. subst ofs1 b1 delta. 
                   replace (z + 0) with z by omega; rewrite Pos.add_sub; trivial. 
                 + contradict n. rewrite loc_change_ext in locmap. auto_sm. }
               { (*Use the source luke*)
                 (*also use Norm!*)
                 assert (bval2': ~ Mem.valid_block m2 b2).
                 { unfold Mem.valid_block, Plt, Pos.lt, Pos.gt in *; intros HH.
                   rewrite bval2 in HH; inversion HH. }
                 destruct p, p0.
                 symmetry in source2; apply source_SomeE in source2.
                 destruct source2 as 
                     [b02 [delta [ofs2' [invert [ineq [jmap [mperm ofseq]]]]]]].
                 inversion invert; subst b02 ofs2'.
                 (*now I prove that l' is the one mapping. *)
                 subst j12'; subst nu12'. unfold as_inj in jmap.
                 apply joinD_Some in jmap; destruct jmap as [extmap|[extmap locmap]].
                 + rewrite ext_change_ext in extmap.
                   rewrite H5 in extmap.
                   unfold add_inj, filter_id, shiftT in extmap.
                   destruct (j b0) eqn:jmap.
                   - contradict bval2'. inversion extmap; subst p. subst j; auto_sm.
                   - destruct (l' b0) eqn:lmap; try solve [inversion extmap].
                   inversion extmap. subst ofs2 b2 delta. 
                   replace (z0 + 0) with z0 by omega; rewrite Pos.add_sub; trivial. 
                 + contradict bval2'. rewrite loc_change_ext in locmap. auto_sm. }
               }
             }
         - subst nu23'. rewrite loc_change_ext.
           unfold Mem.meminj_no_overlap; intros.
           eapply MInj23.
           apply H.
           eapply local_in_all; auto.
           eapply local_in_all; auto.
           apply Fwd2; eauto.
           auto_sm.
           apply Fwd2; eauto.
           auto_sm.
       + (*This prove seems identical to the 12 one*)
         intros.
         subst nu23'. apply as_in_SomeE in H; destruct H as [ext1 | loc1];
         [ rewrite ext_change_ext in ext1 | rewrite loc_change_ext in loc1].
         - eapply MKI_Some23 in ext1; eauto. 
           destruct ext1 as [kmap | [kmap [lmap bt]]].
           assert (map23: as_inj nu23 b = Some (b', delta)).
           { apply extern_in_all; subst k; trivial. }
           eapply MInj23; eauto.
           destruct H0; [left | right].
           eapply Fwd2.
           eapply valid_from_map. 
           apply SMWD23.
           apply map23.
           eassumption.
           assumption.

           eapply Fwd2.
           eapply valid_from_map. apply SMWD23.
           apply map23.
           eassumption.
           assumption.

           eapply MemInjNu'.
           apply extern_in_all; subst l'; eauto.
           unfold Mem.perm in H0.
           rewrite (mem_add_accx nu12 nu23 j12' m1 m1' m2) in H0; 
                 unfold mem_add_acc in H0.
           assert (bval: ~Mem.valid_block m2 b). 
             { unfold Mem.valid_block, Plt, Pos.lt; intros HH. 
               rewrite bt in HH; inversion HH. }
           destruct ( valid_dec m2 b); try solve [contradict bval; trivial].
           destruct H0 as [H | H].
           * destruct (source j12' m1' b (Int.unsigned ofs)) eqn:sour; 
             try solve[ inversion H ].
             left.
             (*Following is used twice... maybe factor it? *)
             symmetry in sour; apply source_SomeE in sour.
             destruct sour as 
                 [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
             subst p.
             (*now I prove that l' is the one mapping. *)
             subst j12'; subst nu12'. unfold as_inj in jmap.
             { apply joinD_Some in jmap; destruct jmap as [extmap|[extmap locmap]].
               + rewrite ext_change_ext in extmap.
                 inversion Heqoutput.
                 rewrite H1 in extmap.
                 unfold add_inj, filter_id, shiftT in extmap.
                   destruct (j b02) eqn:jmap.
                   - contradict bval. inversion extmap; subst p. subst j; auto_sm.
                   - destruct (l' b02) eqn:lmap'; try solve [inversion extmap].
                   inversion extmap. subst b delta'; rewrite ofseq.
                   replace (ofs2 + 0) with ofs2 by omega; rewrite Pos.add_sub; trivial. 
                 + contradict bval. rewrite loc_change_ext in locmap. auto_sm. }
           * destruct (source j12' m1' b (Int.unsigned ofs - 1)) eqn:sour; 
             try solve[ inversion H ].
             right. 
             (*Following is used twice... maybe factor it? *)
             symmetry in sour; apply source_SomeE in sour.
             destruct sour as 
                 [b02 [delta' [ofs2 [invert [ineq [jmap [mperm ofseq]]]]]]].
             subst p.
             (*now I prove that l' is the one mapping. *)
             subst j12'; subst nu12'. unfold as_inj in jmap.
             { apply joinD_Some in jmap; destruct jmap as [extmap|[extmap locmap]].
               + rewrite ext_change_ext in extmap.
                 inversion Heqoutput.
                 rewrite H1 in extmap.
                 unfold add_inj, filter_id, shiftT in extmap.
                   destruct (j b02) eqn:jmap.
                   - contradict bval. inversion extmap; subst p. subst j; auto_sm.
                   - destruct (l' b02) eqn:lmap'; try solve [inversion extmap].
                   inversion extmap. subst b delta'; rewrite ofseq.
                   replace (ofs2 + 0) with ofs2 by omega; rewrite Pos.add_sub; trivial. 
                 + contradict bval. rewrite loc_change_ext in locmap. auto_sm. }
         - assert (map23: as_inj nu23 b = Some (b', delta)).
           { apply local_in_all; auto. }
           destruct MInj23. eapply mi_representable; eauto. 
           destruct H0; [left | right].
           eapply Fwd2; eauto.
           eapply (valid_from_map nu23); eauto.
           eapply Fwd2; eauto.
           eapply (valid_from_map nu23); eauto.
       }
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
         { subst nu12' m2'. unfold RNG, DomTgt, change_ext in H. destruct nu12; simpl in H.
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
             destruct GlueInv as [? [extEq [? ?]]].
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
         subst nu23' m2'. unfold DOM, DomSrc, change_ext in H. destruct nu23; simpl in H.
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
             destruct GlueInv as [? [extEq [? ?]]].
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
       { exact SMWD12'. }
       split.
       (* SM_wd 23*)
       { exact SMWD23'. }
       split.
       (* locBlocksTgt = locBlocksSrc *)
       { subst nu12' nu23'. unfold change_ext; destruct nu12, nu23; simpl.  
         apply GlueInv.
       }
       (* locBlocksTgt = locBlocksSrc *)
       split.
       {
         destruct GlueInv as [? [extEq [? ?]]].
         subst nu23' nu12'; unfold change_ext; destruct nu23, nu12; subst extS23 extT12; simpl.
         simpl in extEq; rewrite extEq; auto.
       }
       split.
       (* pubBlocksTgt -> pubBlocksSrc *)
       { subst nu12' nu23'. unfold change_ext; destruct nu12, nu23; simpl.  
         apply GlueInv.
       }
       (* frgnBlocksTgt -> frgnBlocksSrc *)
       { subst nu12' nu23'. unfold change_ext; destruct nu12, nu23; simpl.  
         apply GlueInv.
       }
       split.
       (* Norm *)
       { subst nu12' nu23'. unfold change_ext; destruct nu12, nu23; simpl. 
         eapply MKI_norm; subst j k; eauto. 

         (* Proveing 
          * forall (b : block) (p : block * Z),
          * extern_of0 b = Some p -> (b < Mem.nextblock m2)%positive *)
         intros b p H.  destruct p.
         eapply SMV23. eapply as_inj_DomRng.
         unfold as_inj, join; simpl. simpl in *; erewrite H; eauto.
         assumption.
       }
       split.
       { exact UnchPrivSrc12. }
       (* Mem.unchanged_on *) (*NOTE: hey both Mem.unchanged_on look very alike! *)
       split.
       { exact UnchLOOR12.
       }
       split.
       { intros; subst nu12';
         eapply destruct_sminj12; eauto.
       }
       { clear SMWD12 SMWD12' SMWD23'.
         intros; subst nu23' j k l';
         edestruct destruct_sminj23; eauto.
         right; destruct H0 as [b1 rest]; exists b1, d2; exact rest.
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
                             (Pure: pure_comp_ext nu12 nu23 m1 m2)
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
              Pure SMV12 SMV23 UnchPrivSrc UnchLOOR13 GlueInvNu Norm12 full)
  as [m2' [nu12' [nu23' [A [B [C [D [E [F [G [H [I [J [K [L [M ]]]]]]]]]]]]]]]].
  exists m2', nu12', nu23'. intuition.
Qed.



