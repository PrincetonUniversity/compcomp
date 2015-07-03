Require Import Events. (*is needed for some definitions (loc_unmapped etc*)
Require Import Memory.
Require Import Coqlib.
Require Import Integers.
Require Import Values.
Require Import Maps.
Require Import Axioms.

Require Import structured_injections.
Require Import reach.
Require Import simulations.
Require Import simulations_lemmas.
Require Import mem_lemmas.
Require Import mem_interpolation_defs.
Require Import mem_interpolation_II.
Require Import FiniteMaps.

(*<<<<<<< HEAD:core/interpolation_II.v

(*Inserts the new injection entries into extern component, but not into foreign*)
Definition insert_as_extern (mu: SM_Injection) (j: meminj) (DomJ TgtJ:block->bool)
          : SM_Injection:=
  match mu with 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local extBSrc extBTgt fSrc fTgt extern => 
    Build_SM_Injection locBSrc locBTgt pSrc pTgt local
      (fun b => orb (extBSrc b) (DomJ b))
      (fun b => orb (extBTgt b) (TgtJ b))
      fSrc
      fTgt
      (join extern (fun b => match local b with Some _ => None
                                              | None => j b end))
  end.

Definition convertL (nu12: SM_Injection) (j12':meminj) FreshSrc FreshMid:= 
  insert_as_extern nu12 j12' FreshSrc FreshMid. 

Definition convertR (nu23: SM_Injection) (j23':meminj) FreshMid FreshTgt:= 
  insert_as_extern nu23 j23' FreshMid FreshTgt.

Lemma convertL_local: forall nu12 j12' FreshSrc FreshMid,
            local_of (convertL nu12 j12' FreshSrc FreshMid) =
            local_of nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_pub: forall nu12 j12' FreshSrc FreshMid,
            pub_of (convertL nu12 j12' FreshSrc FreshMid) =
            pub_of nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_priv: forall nu12 j12' FreshSrc FreshMid,
            priv_of (convertL nu12 j12' FreshSrc FreshMid) =
            priv_of nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_extern: forall nu12 j12' FreshSrc FreshMid,
            extern_of (convertL nu12 j12' FreshSrc FreshMid) =
            join (extern_of nu12)
                 (fun b => match (local_of nu12) b with Some _ => None | None => j12' b end).
Proof. intros. destruct nu12; simpl. reflexivity. Qed. 

Lemma convertL_locBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            locBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            locBlocksSrc nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_locBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            locBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            locBlocksTgt nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_extBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            extBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            fun b => orb (extBlocksSrc nu12 b) (FreshSrc b).
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_extBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            extBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            fun b => orb (extBlocksTgt nu12 b) (FreshMid b).
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_DomSrc: forall nu12 j12' FreshSrc FreshMid,
            DomSrc (convertL nu12 j12' FreshSrc FreshMid) =
            (fun b => orb (DomSrc nu12 b) (FreshSrc b)).
Proof. intros. destruct nu12. unfold DomSrc; simpl in *. 
       extensionality b. rewrite orb_assoc. reflexivity. Qed. 

Lemma convertL_DomTgt: forall nu12 j12' FreshSrc FreshMid,
            DomTgt (convertL nu12 j12' FreshSrc FreshMid) =
            (fun b => orb (DomTgt nu12 b) (FreshMid b)).
Proof. intros. destruct nu12. unfold DomTgt; simpl in *. 
       extensionality b. rewrite orb_assoc. reflexivity. Qed. 

Lemma convertL_pubBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            pubBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            pubBlocksSrc nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_pubBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            pubBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            pubBlocksTgt nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_frgnBlocksSrc: forall nu12 j12' FreshSrc FreshMid,
            frgnBlocksSrc (convertL nu12 j12' FreshSrc FreshMid) =
            frgnBlocksSrc nu12.
Proof. intros. destruct nu12. simpl. reflexivity. Qed. 

Lemma convertL_frgnBlocksTgt: forall nu12 j12' FreshSrc FreshMid,
            frgnBlocksTgt (convertL nu12 j12' FreshSrc FreshMid) =
            frgnBlocksTgt nu12.
Proof. intros. destruct nu12. reflexivity. Qed. 

Lemma convertL_foreign: forall nu12 j12' FreshSrc FreshMid (WD12:SM_wd nu12),
            foreign_of (convertL nu12 j12' FreshSrc FreshMid) =
            foreign_of nu12. 
Proof. intros. destruct nu12; simpl in *. extensionality b.
  remember (frgnBlocksSrc b) as d.
  destruct d; trivial. apply eq_sym in Heqd.
  destruct (frgnSrc _ WD12 _ Heqd) as [b2 [z [Frg _]]]. simpl in Frg.
  rewrite Heqd in Frg; unfold join. rewrite Frg; trivial. Qed.

Lemma convertR_local: forall nu23 j23' FreshMid FreshTgt,
            local_of (convertR nu23 j23' FreshMid FreshTgt) =
            local_of nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed.
 
Lemma convertR_pub: forall nu23 j23' FreshMid FreshTgt,
            pub_of (convertR nu23 j23' FreshMid FreshTgt) =
            pub_of nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed. 

Lemma convertR_priv: forall nu23 j23' FreshMid FreshTgt,
            priv_of (convertR nu23 j23' FreshMid FreshTgt) =
            priv_of nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed. 

Lemma convertR_extern: forall nu23 j23' FreshMid FreshTgt,
            extern_of (convertR nu23 j23' FreshMid FreshTgt) =
            join (extern_of nu23)
                 (fun b => match (local_of nu23) b with Some _ => None | None => j23' b end).
Proof. intros. destruct nu23; simpl. reflexivity. Qed.

Lemma convertR_foreign: forall nu23 j23' FreshMid FreshTgt (WD23:SM_wd nu23),
            foreign_of (convertR nu23 j23' FreshMid FreshTgt) =
            foreign_of nu23.
Proof. intros. destruct nu23; simpl in *. extensionality b.
  remember (frgnBlocksSrc b) as d.
  destruct d; trivial. apply eq_sym in Heqd.
  destruct (frgnSrc _ WD23 _ Heqd) as [b2 [z [Frg _]]]. simpl in Frg.
  rewrite Heqd in Frg; unfold join. rewrite Frg; trivial. Qed.

Lemma convertR_locBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            locBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            locBlocksSrc nu23.
Proof. intros. destruct nu23. reflexivity. Qed. 

Lemma convertR_locBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            locBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            locBlocksTgt nu23.
Proof. intros. destruct nu23. reflexivity. Qed. 

Lemma convertR_extBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            extBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            fun b => orb (extBlocksSrc nu23 b) (FreshMid b).
Proof. intros. destruct nu23. reflexivity. Qed. 

Lemma convertR_extBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            extBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            fun b => orb (extBlocksTgt nu23 b) (FreshTgt b).
Proof. intros. destruct nu23. reflexivity. Qed. 

Lemma convertR_DomSrc: forall nu23 j23' FreshMid FreshTgt,
            DomSrc (convertR nu23 j23' FreshMid FreshTgt) =
            (fun b => orb (DomSrc nu23 b) (FreshMid b)).
Proof. intros. destruct nu23; simpl. unfold DomSrc; simpl.
       extensionality b. rewrite orb_assoc. reflexivity. Qed. 

Lemma convertR_DomTgt: forall nu23 j23' FreshMid FreshTgt,
            DomTgt (convertR nu23 j23' FreshMid FreshTgt) =
            (fun b => orb (DomTgt nu23 b) (FreshTgt b)).
Proof. intros. destruct nu23; simpl. unfold DomTgt; simpl.
       extensionality b. rewrite orb_assoc. reflexivity. Qed. 

Lemma convertR_pubBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            pubBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            pubBlocksSrc nu23.
Proof. intros. destruct nu23. reflexivity. Qed. 

Lemma convertR_pubBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            pubBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            pubBlocksTgt nu23.
Proof. intros. destruct nu23. reflexivity. Qed. 

Lemma convertR_frgnBlocksSrc: forall nu23 j23' FreshMid FreshTgt,
            frgnBlocksSrc (convertR nu23 j23' FreshMid FreshTgt) =
            frgnBlocksSrc nu23.
Proof. intros. destruct nu23. simpl. reflexivity. Qed. 

Lemma convertR_frgnBlocksTgt: forall nu23 j23' FreshMid FreshTgt,
            frgnBlocksTgt (convertR nu23 j23' FreshMid FreshTgt) =
            frgnBlocksTgt nu23.
Proof. intros. destruct nu23; simpl. reflexivity. Qed. 

Definition FreshDom (j j': meminj) b :=
  match j' b with
     None => false
   | Some(b',z) => match j b with
                     None => true  
                   | Some _ => false
                   end
  end.

Definition AccessEffProperty nu23 nu12 (j12' :meminj) (m1 m1' m2 : mem)
           (AM:ZMap.t (Z -> perm_kind -> option permission)):Prop :=
  forall b2, 
    (Mem.valid_block m2 b2 -> forall k ofs2,
       if (locBlocksSrc nu23 b2) 
       then if (pubBlocksSrc nu23 b2)
            then match source (local_of nu12) m1 b2 ofs2 with
                   Some(b1,ofs1) => if pubBlocksSrc nu12 b1 
                                    then PMap.get b2 AM ofs2 k = 
                                         PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                                    else PMap.get b2 AM ofs2 k = 
                                         PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 | None =>  PMap.get b2 AM ofs2 k = 
                            PMap.get b2 m2.(Mem.mem_access) ofs2 k
                 end
            else PMap.get b2 AM ofs2 k = 
                 PMap.get b2 m2.(Mem.mem_access) ofs2 k
       else match source (as_inj nu12) m1 b2 ofs2 with
                   Some(b1,ofs1) =>  PMap.get b2 AM ofs2 k = 
                                     PMap.get b1 m1'.(Mem.mem_access) ofs1 k
                 | None => match (*j23*) (as_inj nu23) b2 with 
                             None => PMap.get b2 AM ofs2 k  = PMap.get b2 m2.(Mem.mem_access) ofs2 k
                           | Some (b3,d3) =>  PMap.get b2 AM ofs2 k = None (* mem_interpolation_II.v has PMap.get b2 m2.(Mem.mem_access) ofs2 k here 
                                            -- see the comment in the proof script below to see where None is needed*)
                           end

                 
               end)
     /\ (~ Mem.valid_block m2 b2 -> forall k ofs2,
           match source j12' m1' b2 ofs2 with 
              Some(b1,ofs1) => PMap.get b2 AM ofs2 k =
                               PMap.get b1 m1'.(Mem.mem_access) ofs1 k
            | None =>  PMap.get b2 AM ofs2 k = None
          end).

Definition ContentEffProperty nu23 nu12 (j12':meminj) (m1 m1' m2:Mem.mem)
                               (CM:ZMap.t (ZMap.t memval)):=
  forall b2, 
  (Mem.valid_block m2 b2 -> forall ofs2,
    if locBlocksSrc nu23 b2
    then if (pubBlocksSrc nu23 b2)
         then match source (local_of nu12) m1 b2 ofs2 with
             Some(b1,ofs1) =>
                 if pubBlocksSrc nu12 b1 
                 then ZMap.get ofs2 (PMap.get b2 CM) = 
                            inject_memval j12' 
                              (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
                 else ZMap.get ofs2 (PMap.get b2 CM) = 
                           ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))   
           | None => ZMap.get ofs2 (PMap.get b2 CM) =
                     ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
            end
         else ZMap.get ofs2 (PMap.get b2 CM) =
              ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
    else match source (as_inj nu12) m1 b2 ofs2 with
             Some(b1,ofs1) => ZMap.get ofs2 (PMap.get b2 CM) = 
                              inject_memval j12' 
                                (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
           | None => ZMap.get ofs2 (PMap.get b2 CM) = 
                     ZMap.get ofs2 (PMap.get b2 m2.(Mem.mem_contents))
         end)
  /\ (~ Mem.valid_block m2 b2 -> forall ofs2,
         match source j12' m1' b2 ofs2 with
                None => ZMap.get ofs2 (PMap.get b2 CM) = Undef
              | Some(b1,ofs1) =>
                   ZMap.get ofs2 (PMap.get b2 CM) =
                     inject_memval j12' 
                       (ZMap.get ofs1 (PMap.get b1 m1'.(Mem.mem_contents)))
         end)
   /\ fst CM !! b2 = Undef.

Lemma effect_interp_OK: forall m1 m2 nu12 
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
                             (Norm12: forall b1 b2 d1, extern_of  nu12 b1 = Some(b2,d1) ->
                                             exists b3 d2, extern_of nu23 b2 = Some(b3, d2))
               prej12' j23' n1' n2'
               (HeqMKI: mkInjections m1 m1' m2 (as_inj nu12) (as_inj nu23) (as_inj nu') = 
                            (prej12', j23', n1', n2'))
               j12' (Hj12': j12'= removeUndefs (as_inj nu12) (as_inj nu') prej12')
               m2'
               (NB: m2'.(Mem.nextblock)=n2')
               (CONT:  ContentEffProperty nu23 nu12 j12' m1 m1' m2 
                                           (m2'.(Mem.mem_contents)))
               (ACCESS: AccessEffProperty nu23 nu12 (*(as_inj nu23)*) j12' m1 m1' m2 
                                               (m2'.(Mem.mem_access))),

     Mem.unchanged_on (fun b ofs => locBlocksSrc nu23 b = true /\ 
                                    pubBlocksSrc nu23 b = false) m2 m2' /\
     Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2' /\
(*     Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3' /\*)
     exists (nu12' nu23':SM_Injection), 
           nu12'  = (convertL nu12 (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    (*FreshSrc:*) (fun b => andb (DomSrc nu' b) (negb (DomSrc nu12 b)))
                    (*FreshMid:*) (FreshDom (as_inj nu23) j23'))
       /\ nu23' = (convertR nu23 j23'
                      (*FreshMid:*) (FreshDom (as_inj nu23) j23')
                      (*FreshTgt:*) (fun b => andb (DomTgt nu' b) (negb (DomTgt nu23 b))))
                      /\ nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             sm_inject_separated nu12 nu12' m1 m2 /\ 
                             sm_inject_separated nu23 nu23' m2 m3 /\
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
                             mem_forward m2 m2' /\
                             Mem.inject (as_inj nu12') m1' m2' /\
                             Mem.inject (as_inj nu23') m2' m3'.
Proof. intros.
  assert (VBj12_1: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu12) b1 = Some (b2, ofs2) -> Mem.valid_block m1 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12).
  assert (VBj12_2: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu12) b1 = Some (b2, ofs2) -> Mem.valid_block m2 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  assert (VBj23_1: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu23) b1 = Some (b2, ofs2) -> Mem.valid_block m2 b1).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23).
  assert (VBj23_2: forall (b1 b2 : block) (ofs2 : Z),
                   (as_inj nu23) b1 = Some (b2, ofs2) -> Mem.valid_block m3 b2).
      intros. apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
  assert (VB12: forall (b3 b4 : block) (ofs3 : Z), 
                 (as_inj nu12) b3 = Some (b4, ofs3) -> 
                (b3 < Mem.nextblock m1 /\ b4 < Mem.nextblock m2)%positive).
      intros. split. apply (VBj12_1 _ _ _ H). apply (VBj12_2 _ _ _ H).
  assert (preinc12:= mkInjections_1_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1).
  assert (inc12:= inc_RU _ _ preinc12 (as_inj nu')).
  assert (presep12:= mkInjections_1_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI).
  assert (sep12: inject_separated (as_inj nu12) (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1 m2).
       intros b; intros. eapply presep12. apply H. 
       eapply RU_D. apply preinc12. apply H0.
  assert (InjIncr: inject_incr (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu')).
    subst. eapply extern_incr_inject_incr; eassumption. 
  assert (InjSep: inject_separated (compose_meminj (as_inj nu12) (as_inj nu23)) (as_inj nu') m1 m3).
    subst. clear CONT ACCESS HeqMKI.
    apply sm_inject_separated_mem in SMInjSep.  
    rewrite compose_sm_as_inj in SMInjSep.
      assumption.
      eapply GlueInvNu.
      eapply GlueInvNu.
      eapply GlueInvNu.
      eapply GlueInvNu.
      assumption.
  assert (inc23:= mkInjections_2_injinc _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1).
  assert (sep23:= mkInjections_2_injsep _ _ _ _ _ _ _ _ _ _ HeqMKI 
                  VBj12_1 _ InjSep).
  assert (NB1:= forward_nextblock _ _ Fwd1).
  assert (XX: n1' = Mem.nextblock m1'). 
    destruct (mkInjections_0  _ _ _ _ _ _ _ _ _ _ HeqMKI)
      as [[NN [N1 [N2 [JJ1 JJ2]]]] | [n [NN [N1 [N2 N3]]]]].
    subst. eapply Pos.le_antisym; assumption. assumption.
 subst.
  assert (VBj': forall b1 b3 ofs3, (as_inj nu') b1 = Some (b3, ofs3) -> 
                (b1 < Mem.nextblock m1')%positive).
      intros. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MemInjNu').
  assert (ID:= RU_composememinj _ _ _ _ _ _ _ _ _ _ HeqMKI 
               InjIncr _ InjSep VBj12_1 VBj12_2 VBj23_1 VBj').
destruct GlueInvNu as [WDnu12 [WDnu23 [GlueLoc [GlueExt [GluePub GlueFrgn]]]]].
assert (Fwd2: mem_forward m2 m2').
  split; intros; rename b into b2.
  (*valid_block*)
     clear - H NB1 HeqMKI. unfold Mem.valid_block in *.
     destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI)
     as [HH | HH].
       destruct HH as [_ [_ [XX _]]]. rewrite XX in H. assumption.
       destruct HH as [n [NN [_ [_ X]]]]. rewrite <- X.
        xomega. 
  (*max*)
     destruct (ACCESS b2) as [Val2 _].
     specialize (Val2 H Max ofs).
     remember (locBlocksSrc nu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
     (*case locBlocksSrc nu23 b2 = false*)
       remember (pubBlocksSrc nu23 b2) as q.
       destruct q; apply eq_sym in Heqq.
         remember (source (local_of nu12) m1 b2 ofs) as src.
         destruct src.
           apply source_SomeE in Heqsrc.
           destruct Heqsrc as [b1 [delta [ofs1 [PBO [ValB1 [J1 [P1 Off2]]]]]]].
           subst.
           remember (pubBlocksSrc nu12 b1) as w.
           destruct w; 
             rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2; trivial.
           eapply MInj12.
             apply local_in_all; eassumption.
             eapply Fwd1.
               apply ValB1.
               apply H0. 
         rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; apply H0.
       rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; apply H0.
     (*case locBlocksSrc nu23 b2 = false*)
       remember (source (as_inj nu12) m1 b2 ofs) as src.
       destruct src.
         apply source_SomeE in Heqsrc.
         destruct Heqsrc as [b1 [delta [ofs1 [PBO [Bounds [J1 [P1 Off2]]]]]]].
         subst.
         rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2.
         eapply MInj12. apply J1. 
           eapply Fwd1.
             apply Bounds.
             apply H0. 
       remember (as_inj nu23 b2) as jb.
         destruct jb; apply eq_sym in Heqjb.
           destruct p0.
           unfold Mem.perm in H0. rewrite Val2 in H0. simpl in H0. contradiction.
         rewrite (perm_subst _ _ _ _ _ _ _ Val2) in H0; clear Val2. apply H0.
       
(*First unchOn condition - corresponds to UnchLOM2 loc_unmapped.*)
assert (UNCHA: Mem.unchanged_on
  (fun (b : block) (_ : Z) =>
   locBlocksSrc nu23 b = true /\ pubBlocksSrc nu23 b = false) m2 m2').
 split; intros. rename b into b2. rename H0 into ValB2.
        destruct H as [locBSrc pubBSrc].
        destruct (ACCESS b2) as [Val _].
        specialize (Val ValB2 k ofs).
        rewrite locBSrc, pubBSrc in Val.
        rewrite (perm_subst _ _ _ _ _ _ _ Val). split; auto. 
  apply (cont_split _ _ _ _ _ (CONT b)); intros; clear CONT.
      (*case Mem.valid_block m2 b*)
          specialize (H2 ofs).
          destruct H as [locBSrc pubBSrc].
          rewrite locBSrc, pubBSrc in H2. simpl in H2.
          apply H2.
      (*case invalid*)
          apply Mem.perm_valid_block in H0. contradiction.
split; trivial.
assert (UNCHB: Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2'). 
 (*Second unchOn condition - corresponds to Unch2*)
  split; intros. rename b into b2. rename H0 into ValB2. 
     destruct H as [locTgt2 HP].
     destruct (ACCESS b2) as [Val _].
     specialize (Val ValB2 k ofs).
     remember (locBlocksSrc nu23 b2) as d.
     destruct d; apply eq_sym in Heqd.
     (*case locBlocksSrc nu23 b2 = true*)
       remember (pubBlocksSrc nu23 b2) as q.
       destruct q; apply eq_sym in Heqq.
       (*case pubBlocksSrc nu23 b2 = true*)
          remember (source (local_of nu12) m1 b2 ofs) as ss.
          destruct ss.
            destruct p0.
            destruct (source_SomeE _ _ _ _ _ Heqss)
               as [b1 [d1 [ofs1 [PP [VB [JJ [PERM Off2]]]]]]]; clear Heqss.
            subst. apply eq_sym in PP. inv PP.
            remember (pubBlocksSrc nu12 b) as w.
            destruct w; apply eq_sym in Heqw;
              rewrite (perm_subst _ _ _ _ _ _ _ Val); clear Val.
              destruct (HP _ _ JJ).  
                assert (Arith: z + d1 - d1 = z) by omega. 
                rewrite Arith in H. contradiction.
              rewrite H in Heqw. discriminate.
            split; intros; trivial.
          rewrite (perm_subst _ _ _ _ _ _ _ Val); clear Val.
             split; intros; trivial.
       (*case pubBlocksSrc nu23 b2 = false*)
          rewrite (perm_subst _ _ _ _ _ _ _ Val); clear Val.
             solve[split; intros; trivial].
     (*case locBlocksSrc nu23 b2 = false*)
        rewrite GlueLoc in locTgt2. rewrite locTgt2 in Heqd. discriminate.
  destruct H as [locTgt2 HP]. rename b into b2.
  apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
  (* case Mem.valid_block m2 b*)
          specialize (H1 ofs).
          assert (locSrc2: locBlocksSrc nu23 b2 = true).
            rewrite GlueLoc in locTgt2. assumption.
          rewrite locSrc2 in *.
          remember (pubBlocksSrc nu23 b2) as d.
          destruct d; apply eq_sym in Heqd.
          (*case pubBlocksSrc nu23 b2 = true*)
            remember (source (local_of nu12) m1 b2 ofs) as ss.
            destruct ss.
              destruct p.
              destruct (source_SomeE _ _ _ _ _ Heqss)
               as [b1 [d1 [ofs1 [PP [VB [JJ [PERM Off2]]]]]]]; clear Heqss.
              subst. inv PP.
              destruct (HP _ _ JJ); clear HP.
                 assert (Arith : ofs1 + d1 - d1 = ofs1) by omega. 
                 rewrite Arith in H3. contradiction.
              rewrite H3 in H1. trivial.
            apply H1.
          (*case pubBlocksSrc nu23 b2 = true*)
            apply H1.
       (*invalid*)
          exfalso. 
          apply Mem.perm_valid_block in H0. contradiction.
split; trivial.

assert (UNCHC: Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3').
  (*third UnchOn condition - corresponds to UnchLOOR3*)
   clear - UnchLOOR13 WDnu12 GluePub MInj12.
   unfold local_out_of_reach.
   split; intros; rename b into b3.
      destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl. 
        split; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc nu12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePub in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MInj12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
   destruct H as[locTgt3 LOOR23].
      eapply UnchLOOR13; trivial; simpl. 
        split; trivial.
        intros b1; intros; simpl in *.
        remember (pubBlocksSrc nu12 b1) as d.
        destruct d; try (right; reflexivity).
        left. apply eq_sym in Heqd.
        destruct (compose_meminjD_Some _ _ _ _ _ H)
          as [b2 [d1 [d2 [LOC1 [LOC2 D]]]]]; subst; clear H.
        destruct (pubSrc _ WDnu12 _ Heqd) as [bb2 [dd1 [Pub12 PubTgt2]]].
        rewrite (pub_in_local _ _ _ _ Pub12) in LOC1. inv LOC1.
        apply GluePub in PubTgt2.
        destruct (LOOR23 _ _ LOC2); clear LOOR23.
          intros N. apply H.
          assert (Arith : ofs - (d1 + d2) + d1 = ofs - d2) by omega.
          rewrite <- Arith.
          eapply MInj12. eapply pub_in_all; try eassumption. apply N.
        rewrite H in PubTgt2. discriminate.
(*split; trivial.*)
assert (VBj23': forall b2 b3 d2, j23' b2 = Some(b3,d2) -> Mem.valid_block m2' b2).
    assert (Val2: forall b2 b3 d2, as_inj nu23 b2 = Some(b3,d2) -> Mem.valid_block m2 b2).
       intros. eapply SMV23. eapply as_inj_DomRng; eassumption.
    intros.
    destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI Val2 _ _ _ H) as [MK | [MK | MK]].
       destruct MK. apply Fwd2. apply H1.
       destruct MK. subst. apply H1.
       destruct MK as [m Hm]; subst. apply Hm.
assert (Val12: (forall (b1 b2 : block) (ofs2 : Z),
  as_inj nu12 b1 = Some (b2, ofs2) ->
  (b1 < Mem.nextblock m1)%positive /\ (b2 < Mem.nextblock m2)%positive)).
   intros. split; eapply SMV12. eapply as_inj_DomRng; eassumption.
                eapply as_inj_DomRng; eassumption.
assert (Val23: (forall (b2 b3 : block) (ofs3 : Z),
  as_inj nu23 b2 = Some (b3, ofs3) -> (b2 < Mem.nextblock m2)%positive)).
   intros. eapply SMV23. eapply as_inj_DomRng; eassumption.
assert (NOVj12':= RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ 
                  MInj23 _ _ _ _ _ HeqMKI).
exists (convertL nu12 (removeUndefs (as_inj nu12) (as_inj nu') prej12')
          (*FreshSrc:*) (fun b => andb (DomSrc nu' b) (negb (DomSrc nu12 b)))
          (*FreshMid:*) (FreshDom (as_inj nu23) j23')).
exists (convertR nu23 j23'
          (*FreshMid:*) (FreshDom (as_inj nu23) j23')
          (*FreshTgt:*) (fun b => andb (DomTgt nu' b) (negb (DomTgt nu23 b)))).
split; trivial.
split; trivial.
remember (removeUndefs (as_inj nu12) (as_inj nu') prej12') as j12'.
assert (ConvertL_J12': 
    as_inj
     (convertL nu12 j12'
        (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
        (FreshDom (as_inj nu23) j23')) = j12').
    extensionality b.
    intros. unfold as_inj.
     rewrite convertL_extern, convertL_local.
     remember (j12' b) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p. unfold join.
       remember (extern_of nu12 b) as q.
       destruct q; apply eq_sym in Heqq.
         destruct p. apply extern_in_all in Heqq.
            rewrite (inc12 _ _ _ Heqq) in Heqd. apply Heqd.
       remember (local_of nu12 b) as w.
       destruct w; apply eq_sym in Heqw.
         destruct p. 
         apply local_in_all in Heqw.
            rewrite (inc12 _ _ _ Heqw) in Heqd. apply Heqd.
            assumption.
      rewrite Heqd. trivial.
     assert (A:= inject_incr_inv _ _ inc12 _ Heqd).
       destruct (joinD_None _ _ _ A).
       unfold join. rewrite H, H0, Heqd. trivial.
rewrite ConvertL_J12' in *.
 rewrite convertL_extern, convertL_frgnBlocksTgt, 
         convertL_pubBlocksTgt, convertL_locBlocksTgt, 
         convertL_extBlocksTgt.
assert (Inj12': Mem.inject j12' m1' m2'). 
    clear ConvertL_J12'.
    assert (Perm12': forall b1 b2 delta ofs k p,
             j12' b1 = Some (b2, delta) ->
             Mem.perm m1' b1 ofs k p -> Mem.perm m2' b2 (ofs + delta) k p).
        intros.
        apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
        (*case valid_block m2 b2*)
          specialize (H2 k (ofs+delta)).
          remember (as_inj nu12 b1) as AsInj1.
          destruct AsInj1; apply eq_sym in HeqAsInj1.
          Focus 2. clear H2. destruct (sep12 _ _ _ HeqAsInj1 H).
                   contradiction.  
          destruct p0.
          rewrite (inc12 _ _ _ HeqAsInj1) in H.  inv H.
          assert (Val_b1:= VBj12_1 _ _ _ HeqAsInj1). 
          assert (PMAX: Mem.perm m1 b1 ofs Max Nonempty).
                    apply Fwd1. assumption.
                    eapply Mem.perm_implies. eapply Mem.perm_max. 
                               apply H0. apply perm_any_N.
          remember (locBlocksSrc nu23 b2) as Locb2.
          destruct Locb2; apply eq_sym in HeqLocb2.
          (*case locBlocksSrc nu23 b2 = true*)
            (*First, establish that local_of nu12 b1 = Some (b2, delta) etc*)
            destruct (joinD_Some _ _ _ _ _ HeqAsInj1) as [EXT12 | [NoEXT12 LOC12]].
              destruct (extern_DomRng _ WDnu12 _ _ _ EXT12) as [? ?].
              rewrite GlueExt in H3.
              destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence.
            destruct (local_DomRng _ WDnu12 _ _ _ LOC12) as [locBSrc1 locBTgt2].
            assert (NOV_LocNu12: Mem.meminj_no_overlap (local_of nu12) m1).
               eapply meminj_no_overlap_inject_incr.
                 apply MInj12. apply local_in_all; assumption.               
            remember (pubBlocksSrc nu23 b2) as PubB2.
            destruct PubB2; apply eq_sym in HeqPubB2.
            (*case pubBlocksSrc nu23 b2 = true*)
              remember (pubBlocksSrc nu12 b1) as PubSrcb1.
              destruct PubSrcb1; apply eq_sym in HeqPubSrcb1.
              (*case pubBlocksSrc nu12 b1 = true*)
                destruct (pubSrc _ WDnu12 _  HeqPubSrcb1) as [bb2 [dd1 [PUB12 TGT2]]].
                rewrite (pub_in_local _ _ _ _ PUB12) in LOC12. inv LOC12.
                rewrite (source_SomeI (local_of nu12) _  _ b1) in H2; trivial.
                  rewrite HeqPubSrcb1 in *.
                  rewrite (perm_subst _ _ _ _ _ _ _ H2). apply H0.
                  apply pub_in_local; assumption.
              (*case pubBlocksSrc nu12 b1 = false*)
                assert (PK: Mem.perm m1 b1 ofs k p).
                  eapply UnchPrivSrc.
                    simpl. split; assumption.
                    assumption.
                    assumption.
                rewrite (source_SomeI (local_of nu12) _  _ b1) in H2; trivial.     
                rewrite HeqPubSrcb1 in H2.
                rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
                eapply MInj12; eassumption. 
            (*case pubBlocksSrc nu23 b2 = false*)
               rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
               eapply MInj12. apply local_in_all; eassumption.
               eapply UnchPrivSrc; simpl; trivial.
               split; trivial.
               remember (pubBlocksSrc nu12 b1) as q.
               destruct q; trivial.
               apply eq_sym in Heqq.
               destruct (pubSrc _ WDnu12 _ Heqq) as [bb2 [dd1 [PUB12 Pub2]]].
               apply pub_in_local in PUB12. rewrite PUB12 in LOC12. inv LOC12.
               apply GluePub in Pub2. rewrite Pub2 in HeqPubB2; discriminate.
          (*case locBlocksSrc nu23 b2 = false*)
             destruct (joinD_Some _ _ _ _ _ HeqAsInj1) as [EXT1 | [NoEXT1 LOC1]].
             Focus 2. destruct (local_DomRng _ WDnu12 _ _ _ LOC1).
                      rewrite GlueLoc in H3. congruence. 
             destruct (extern_DomRng _ WDnu12 _ _ _ EXT1) as [HeqLocb1 HeqExtTgtb2].
             remember (source (as_inj nu12) m1 b2 (ofs + delta)) as ss.
             destruct ss.
             (*case source = Some*)
               destruct (source_SomeE _ _ _ _ _ Heqss)
                 as [bb1 [dd1 [ofs11 [PP [VB [ JJ [PERM Off2]]]]]]].
               clear Heqss. subst.       
               rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
               destruct (eq_block bb1 b1); subst.
                 rewrite JJ in HeqAsInj1. inv HeqAsInj1.  
                 assert (Arith: ofs11 = ofs) by omega. 
                 subst; assumption.
              destruct (Mem.mi_no_overlap _ _ _ MInj12
                           bb1 _ _ _ _ _ _ _ n JJ HeqAsInj1 PERM PMAX).
                exfalso. apply H; trivial. 
                exfalso. apply H. rewrite Off2. trivial.
             (*case source = None*)
               remember (as_inj nu23 b2) as AsInj2.
               destruct AsInj2; apply eq_sym in HeqAsInj2.
               (*case as_inj nu23 b2 = Some(..)*)
                 destruct p0 as [b3 d2].                
                 exfalso.
                 eapply (source_NoneE _ _ _ _ Heqss _ 
                        _ Val_b1 HeqAsInj1).
                 assert (Arith: ofs + delta - delta = ofs) by omega.
                 rewrite Arith. apply PMAX.
               (*case as_inj nu23 b2 = None*)
                  rewrite (perm_subst _ _ _ _ _ _ _ H2); clear H2.
                  remember (frgnBlocksSrc nu23 b2) as FrgnSrc2.
                  destruct FrgnSrc2; apply eq_sym in HeqFrgnSrc2.
                    destruct (frgnSrc _ WDnu23 _ HeqFrgnSrc2) as [b3 [d2 [FRG2 FrgTgt3]]].
                    rewrite (foreign_in_all _ _ _ _ FRG2) in HeqAsInj2. inv HeqAsInj2.
                  remember (frgnBlocksSrc nu12 b1) as FrgnSrc1.
                  destruct FrgnSrc1; apply eq_sym in HeqFrgnSrc1.
                    destruct (frgnSrc _ WDnu12 _ HeqFrgnSrc1) as [bb2 [dd1 [FRG1 FrgTgt2]]].
                    rewrite (foreign_in_extern _ _ _ _ FRG1) in EXT1. inv EXT1.
                    apply GlueFrgn in FrgTgt2. rewrite FrgTgt2 in HeqFrgnSrc2. inv HeqFrgnSrc2.
                 (*case frgnBlocksSrc nu12 b1 = frgnBlocksSrc nu23 b2 = false*)                    
                   exfalso.
                   eapply (source_NoneE _ _ _ _ Heqss _ 
                        _ Val_b1 HeqAsInj1).
                   assert (Arith: ofs + delta - delta = ofs) by omega.
                   rewrite Arith. apply PMAX. 
        (*case ~ valid_block m2 b2*)
            specialize (H2 k (ofs+delta)).
            rewrite (source_SomeI j12' _  _ b1) in H2.
              rewrite (perm_subst _ _ _ _ _ _ _ H2). apply H0.
              subst. apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ 
                    MInj23 _ _ _ _ _ HeqMKI).
              assumption.
              eapply Mem.perm_implies. eapply Mem.perm_max. 
                    apply H0. apply perm_any_N.
    assert (INJ:Mem.mem_inj j12' m1' m2'). 
      split. apply Perm12'.
      (*valid_access*) 
          intros. rewrite Heqj12' in H.
          clear Heqj12'.
          unfold removeUndefs in H.
          remember (as_inj nu12 b1) as d.
          destruct d; apply eq_sym in Heqd.
            destruct p0 as [bb2 dd]. inv H.
            eapply MInj12. eassumption.
            assert (MR: Mem.range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p).
               intros z. intros. specialize (H0 _ H).
               eapply Fwd1. eapply VBj12_1. apply Heqd. apply H0.
               eassumption.
          remember (as_inj nu' b1) as q.
          destruct q; apply eq_sym in Heqq; try inv H.
          destruct p0.
            destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ 
                      HeqMKI VB12 VBj23_1 _ _ _ H2)
            as [HX | [HX | HX]].
              destruct HX as [J12 [Val1 Val2]]. rewrite J12 in Heqd. inv Heqd. 
              destruct HX as [? [? [? [? D]]]]. subst. apply Z.divide_0_r.
              destruct HX as [? [? [? [? [? D]]]]]. subst. apply Z.divide_0_r.  
      (*memval  j12' m1' m2'.*)
          intros. 
          apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
         (*case Mem.valid_block m2 b2*)
            specialize (H2 (ofs + delta)).
            remember (as_inj nu12 b1) as AsInj1.
            destruct AsInj1; apply eq_sym in HeqAsInj1.
            Focus 2. clear H2. destruct (sep12 _ _ _ HeqAsInj1 H).
                     contradiction.  
            destruct p.
            rewrite (inc12 _ _ _ HeqAsInj1) in H.  inv H.
            assert (Val_b1:= VBj12_1 _ _ _ HeqAsInj1). 
            assert (PMAX: Mem.perm m1 b1 ofs Max Nonempty).
                    apply Fwd1. assumption.
                    eapply Mem.perm_implies. eapply Mem.perm_max. 
                               apply H0. apply perm_any_N.
            remember (locBlocksSrc nu23 b2) as Myb2.
            destruct Myb2; apply eq_sym in HeqMyb2.
            (*case locBlocksSrc nu23 b2 = true*)
              (*First, establish that local_of nu12 b1 = Some (b2, delta) etc*)
              destruct (joinD_Some _ _ _ _ _ HeqAsInj1) as [EXT12 | [NoEXT12 LOC12]].
                destruct (extern_DomRng _ WDnu12 _ _ _ EXT12) as [? ?].
                rewrite GlueExt in H4.
                destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence.
              destruct (local_DomRng _ WDnu12 _ _ _ LOC12) as [locBSrc1 locBTgt2].
              remember (pubBlocksSrc nu23 b2) as PubB2.
              destruct PubB2; apply eq_sym in HeqPubB2.
              (*case pubBlocksSrc nu23 b2 = true*)
                destruct (pubSrc _ WDnu23 _ HeqPubB2) as [b3 [d2 [Pub23 PubTgt3]]].
                assert (AsInj23: as_inj nu23 b2 = Some (b3, d2)) by (apply pub_in_all; assumption).
                assert (NOVlocal12: Mem.meminj_no_overlap (local_of nu12) m1).
                  eapply meminj_no_overlap_inject_incr.
                  apply MInj12. apply local_in_all; assumption.
                rewrite (source_SomeI (local_of nu12) _  _ b1) in H2; trivial.
                remember (pubBlocksSrc nu12 b1) as PubSrcb1.
                destruct PubSrcb1; apply eq_sym in HeqPubSrcb1; rewrite H2; clear H2.
                (*case pubBlocksSrc nu12 b1 = true*)
                  destruct (pubSrc _ WDnu12 _  HeqPubSrcb1) as [bb2 [dd1 [PUB12 TGT2]]].
                  rewrite (pub_in_local _ _ _ _ PUB12) in LOC12. inv LOC12.
                  assert (Nu'b1: as_inj nu' b1 = Some (b3, delta+d2)).
                      rewrite ID. eapply compose_meminjI_Some; try eassumption.
                             apply inc12. eassumption. apply (inc23 _ _ _ AsInj23). 
                  assert (MV:= Mem.mi_memval _ _ _
                                 (Mem.mi_inj _ _ _ MemInjNu') _ _ _ _ Nu'b1 H0).
                  inv MV; try constructor. 
                           simpl. 
                           rewrite ID in H4.
                           destruct (compose_meminjD_Some _ _ _ _ _ H4)
                              as [bb2 [dd1 [dd2 [JJ1 [JJ2 Delta]]]]].
                           rewrite JJ1. econstructor. 
                             apply JJ1. reflexivity.
               (*case pubBlocksSrc nu12 b1 = false*)
                  assert (PK: Mem.perm m1 b1 ofs Cur Readable).
                    solve[eapply UnchPrivSrc; eauto].
                  destruct UnchPrivSrc as [_ UPS].
                  rewrite UPS; try assumption; try (split; assumption).
                  eapply memval_inject_incr.
                    apply MInj12; assumption.
                    apply inc12.
              (*case pubBlocksSrc nu23 b2 = false*)
                rewrite H2; clear H2.
                remember (pubBlocksSrc nu12 b1) as PubSrcb1.
                destruct PubSrcb1; apply eq_sym in HeqPubSrcb1.
                  destruct (pubSrc _ WDnu12 _  HeqPubSrcb1) as [bb2 [dd1 [PUB12 TGT2]]].
                  rewrite (pub_in_local _ _ _ _ PUB12) in LOC12. inv LOC12.
                  apply GluePub in TGT2. rewrite TGT2 in HeqPubB2. inv HeqPubB2.
                (*as the b1 is not public we can again aply Unch11*)
                assert (PK: Mem.perm m1 b1 ofs Cur Readable).
                  solve [eapply UnchPrivSrc; eauto].
                destruct UnchPrivSrc as [_ UPS].
                  rewrite UPS; try assumption; try (split; assumption).
                  eapply memval_inject_incr.
                    apply MInj12; assumption.
                    apply inc12.
            (*case locBlocksSrc nu23 b2 = false*)
              rewrite (source_SomeI (as_inj nu12) _  _ b1) in H2; try eassumption. 
                   Focus 2. eapply MInj12.
              rewrite H2; clear H2.
              assert (EXT1: extern_of nu12 b1 = Some (b2, delta)).
                destruct (joinD_Some _ _ _ _ _ HeqAsInj1); trivial.
                destruct H.
                destruct (local_DomRng _ WDnu12 _ _ _ H2).
                rewrite GlueLoc in H5. congruence. 
              destruct (Norm12 _ _ _ EXT1) as [b3 [d2 EXT2]]. 
               assert (Nu'b1: as_inj nu' b1 = Some (b3, delta+d2)).
                      rewrite ID. eapply compose_meminjI_Some; try eassumption.
                             apply inc12. eassumption. 
                             apply inc23. apply (extern_in_all _ _ _ _ EXT2).
                  assert (MV:= Mem.mi_memval _ _ _
                                 (Mem.mi_inj _ _ _ MemInjNu') _ _ _ _ Nu'b1 H0).
                  inv MV; try constructor. 
                           simpl. 
                           rewrite ID in H4.
                           destruct (compose_meminjD_Some _ _ _ _ _ H4)
                              as [bb2 [dd1 [dd2 [JJ1 [JJ2 Delta]]]]].
                           rewrite JJ1. econstructor. 
                             apply JJ1. reflexivity.
         (*case ~ Mem.valid_block m2 b2*)
            specialize (H2 (ofs + delta)).
            assert (J12: as_inj nu12 b1 = None).
               remember (as_inj nu12 b1) as d. 
               destruct d; apply eq_sym in Heqd; trivial.
                     destruct p. rewrite (inc12 _ _ _ Heqd) in H. inv H.
                     exfalso. apply H1. apply (VBj12_2 _ _ _ Heqd).
            assert (MX: Mem.perm m1' b1 ofs Max Nonempty).
                  eapply Mem.perm_max. eapply Mem.perm_implies.
                  apply H0. apply perm_any_N.
            rewrite (source_SomeI _ _  _ b1) in H2; try eassumption.
            rewrite H2; clear H2.
            remember (ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1'))) as v.
            remember (j23' b2) as j23'b2.
                   destruct j23'b2; apply eq_sym in Heqj23'b2.
                   (*j23' b2 = Some p*)
                       destruct p as [b3 delta3].
                       assert (COMP': as_inj nu' b1 = Some(b3, delta+delta3)).
                            rewrite ID. eapply compose_meminjI_Some; eassumption.
                       assert (MV:= Mem.mi_memval _ _ _ 
                           (Mem.mi_inj _ _ _ MemInjNu') _ _  _ _ COMP' H0).
                       subst.
                       inv MV; try constructor. 
                       simpl. rewrite ID in H5. 
                       apply compose_meminjD_Some in H5.
                       destruct H5 as [bb1 [off1 [off [JJ1 [JJ2 Delta]]]]].
                       subst. 
                       rewrite JJ1. econstructor. apply JJ1. trivial.
                   (*j23' b2 = None - we do a slightly different proof than in interp6 mem_interpolationII etc*)
                       subst.
                       unfold removeUndefs in H. rewrite J12 in H.
                       remember (as_inj nu' b1) as d.
                       destruct d; try inv H. 
                       destruct p.
                       assert (VB2: Mem.valid_block m2' b2).
                           destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [XX | XX].
                             destruct XX as [? [? [? [? ?]]]]. subst. rewrite J12 in H4. discriminate.
                             destruct XX as [nn [? [? [? ?]]]]. 
                               destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ H4) as [XX | [XX | XX]].
                                 rewrite XX in J12; discriminate.
                                 destruct XX as [? [? ?]]; subst. unfold Mem.valid_block. rewrite <- H6. xomega.
                                 destruct XX as [mm [[? ?] ?]]; subst.
                                 assert (Mem.valid_block m1' (Mem.nextblock m1 + mm)%positive).
                                   eapply VBj'. rewrite <- Heqd. reflexivity.
                                 clear - H2 H6 H7. unfold Mem.valid_block in *.
                                     rewrite <- H6. rewrite <- H2 in H7. clear H2 H6. xomega.
                       destruct (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1 VBj12_2 VBj23_1 VBj' _ VB2 Heqj23'b2) as [[XXa XXb] | [[XXa XXb] | [nn [XXa XXb]]]].
                         contradiction.
                         assert (b1 = Mem.nextblock m1).
                           destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [ZZ | ZZ].
                             destruct ZZ as [? [? [? [? ?]]]]. subst. rewrite J12 in H4. discriminate.
                             destruct ZZ as [nn [? [? [? ?]]]]. subst. 
                               destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ H4) as [AA | [AA | AA]].
                                 rewrite AA in J12; discriminate.
                                 destruct AA as [? [? ?]]; subst. trivial.
                                 destruct AA as [mm [[? ?] ?]]; subst. clear - H8. exfalso. rewrite Pos.add_comm in H8. apply eq_sym in H8. eapply Pos.add_no_neutral. apply H8.
                           subst. rewrite XXb in Heqd. discriminate. 
                         assert (b1 = (Mem.nextblock m1 + nn)%positive). clear Heqd.
                           destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI) as [ZZ | ZZ].
                             destruct ZZ as [? [? [? [? ?]]]]. subst. rewrite J12 in H4. discriminate.
                             destruct ZZ as [kk [? [? [? ?]]]]. subst. 
                               destruct (mkInjections_3 _ _ _ _ _ _ _ _ _ _ HeqMKI _ _ _ H4) as [AA | [AA | AA]].
                                 rewrite AA in J12; discriminate.
                                 destruct AA as [? [? ?]]; subst. clear - H8. exfalso. rewrite Pos.add_comm in H8. eapply Pos.add_no_neutral. apply H8.
                                 destruct AA as [mm [[? ?] ?]]; subst.
                                    assert (nn=mm); subst; trivial. clear - H8. eapply Pos.add_reg_l. eassumption.
                           subst. rewrite XXb in Heqd. discriminate. 
   split. apply INJ.
   (* mi_freeblocks*)  intros b1 Hb1. 
        remember (j12' b1) as d.
        destruct d; apply eq_sym in Heqd; trivial. destruct p.
        remember (as_inj nu12 b1) as dd.
        destruct dd; apply eq_sym in Heqdd.
            destruct p.
            exfalso. apply Hb1. apply Fwd1. apply (VBj12_1 _ _ _ Heqdd).
        remember (as_inj nu' b1) as ddd.
        destruct ddd; apply eq_sym in Heqddd.
            destruct p. exfalso. apply Hb1. apply (VBj' _ _ _ Heqddd).
        rewrite Heqj12' in Heqd.
        unfold removeUndefs in Heqd. rewrite Heqdd, Heqddd in Heqd.
        inv Heqd.
  (*mi_mappedblock*) intros.
     rewrite Heqj12' in H.
        unfold removeUndefs in H.
        remember (as_inj nu12 b) as dd.
        destruct dd; apply eq_sym in Heqdd.
            destruct p. inv H. apply Fwd2. apply (VBj12_2 _ _ _ Heqdd).
        remember (as_inj nu' b) as ddd.
        destruct ddd; apply eq_sym in Heqddd.
          destruct p. 
          destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ 
                      HeqMKI Val12 VBj23_1 _ _ _ H)
          as [MK | [MK | MK]].
            destruct MK as [J12 [Val1 Val2]]. apply Fwd2. apply Val2.
            destruct MK as [_ [_ [_ [_ D]]]]. apply D.
            destruct MK as [? [_ [_ [_ [_ D]]]]]. apply D.
        inv H.
  (*no_overlap*)
       rewrite Heqj12'. 
       apply (RU_no_overlap _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ _ _ _ _ HeqMKI).
  (*representable*)
       intros.
       rewrite Heqj12' in H.
       unfold removeUndefs in H.
       remember (as_inj nu12 b) as d.
       destruct d; apply eq_sym in Heqd.
          destruct p. inv H.
          destruct H0.
          (*location ofs*)
            eapply MInj12. apply Heqd. 
            left. apply Fwd1. apply (VBj12_1 _ _ _ Heqd). apply H.
          (*location ofs -1*)
            eapply MInj12. apply Heqd. 
            right. apply Fwd1. apply (VBj12_1 _ _ _ Heqd). apply H.
       remember (as_inj nu' b) as dd.
       destruct dd; apply eq_sym in Heqdd.
          destruct p.
          destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ 
                     HeqMKI VB12  VBj23_1 _ _ _ H).
              destruct H1. rewrite H1 in Heqd. discriminate.
              destruct H1 as [HH | HH]. 
              destruct HH as [A [B [C [D E]]]]; subst.
                 split. omega. 
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
              destruct HH as [M [A [B [C [D E]]]]]; subst.
                 split. omega. 
                        rewrite Zplus_0_r. apply Int.unsigned_range_2.
       inv H. 
assert (ConvertR_J23': as_inj
     (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
        (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))) = j23').
   clear ConvertL_J12'. unfold as_inj.
   rewrite convertR_extern, convertR_local.
   extensionality b. unfold join.
   remember (extern_of nu23 b) as d.
   destruct d; apply eq_sym in Heqd.
         destruct p. apply extern_in_all in Heqd.
         rewrite (inc23 _ _ _ Heqd). trivial.
   remember (local_of nu23 b) as q.
   destruct q; trivial; apply eq_sym in Heqq.
         destruct p.
         apply local_in_all in Heqq; trivial.
         rewrite (inc23 _ _ _ Heqq). trivial.
   destruct (j23' b); trivial. destruct p; trivial.
rewrite ConvertR_J23' in *. 
  rewrite convertR_extern, convertR_frgnBlocksSrc, 
          convertR_pubBlocksSrc, convertR_locBlocksSrc, 
          convertR_extBlocksSrc.
 
assert (Inj23':Mem.inject j23' m2' m3').
  clear ConvertL_J12' ConvertR_J23'.
  assert (Perm23': forall b1 b2 delta ofs k p,
                j23' b1 = Some (b2, delta) -> 
                Mem.perm m2' b1 ofs k p -> Mem.perm m3' b2 (ofs + delta) k p).
      intros b2 b3; intros. 
      apply (valid_split _ _ _ _ (ACCESS b2)); intros; clear ACCESS.
      (*valid*)
        specialize (H2 k ofs).
        assert (FF: as_inj nu23 b2 = Some (b3, delta)).
           remember (as_inj nu23 b2) as dd.
           destruct dd; apply eq_sym in Heqdd.
             rewrite (inject_incr_coincide _ _ inc23 _ _ H _ Heqdd). trivial.
           destruct (sep23 _ _ _ Heqdd H). exfalso. apply (H3 H1).
        (*rewrite FF in H2.*)
        remember (locBlocksSrc nu23 b2) as LocB2.
        destruct LocB2; apply eq_sym in HeqLocB2.
        (*case locBlocksSrc nu23 b2 = true*)
          assert (extern_of nu23 b2 = None /\ local_of nu23 b2 = Some (b3, delta)).
            destruct (joinD_Some _ _ _ _ _ FF).
              destruct (extern_DomRng _ WDnu23 _ _ _ H3) as [? ?].
              destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence. 
            assumption.
          destruct H3 as [NoEXT23 LOC23].
          remember (pubBlocksSrc nu23 b2) as PubB2.
          destruct PubB2; apply eq_sym in HeqPubB2.
          (*case pubBlocksSrc nu23 b2 = true*)
            destruct (pubSrc _ WDnu23 _ HeqPubB2) as [b33 [d33 [PUB23 pubTGT3]]].
            rewrite (pub_in_local _ _ _ _ PUB23) in LOC23. inv LOC23.
            remember (source (local_of nu12) m1 b2 ofs) as d.
            destruct d. 
            (*source (local_of nu12)  m1 b2 ofs = Some p0*)
              destruct p0. 
              destruct (source_SomeE _ _ _ _ _ Heqd)
                 as [b1 [d1 [ofs1 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqd.
              subst. inv PP.
              rewrite <- Zplus_assoc.
                assert (J: as_inj nu' b1 = Some (b3, d1 + delta)).
                  rewrite ID.
                  eapply compose_meminjI_Some.
                     apply inc12. apply local_in_all; eassumption.
                     apply inc23. assumption.
              remember (pubBlocksSrc nu12 b1) as d.
              destruct d; apply eq_sym in Heqd;
                rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0; clear H2.                
                eapply MemInjNu'. apply J. apply H0.
              apply UnchLOOR13.
                 split. eapply (pub_locBlocks _ WDnu23). eassumption.
                 intros bb1; intros. simpl. 
                 remember (pubBlocksSrc nu12 bb1) as d.
                 destruct d; try (right; reflexivity).
                 apply eq_sym in Heqd0. left. intros N.
                 destruct (eq_block bb1 b1); subst; simpl.
                   rewrite Heqd0 in Heqd. discriminate.
                 assert (compose_meminj (as_inj nu12) (as_inj nu23) b1 = Some (b3, d1+delta)).
                   eapply compose_meminjI_Some; try eassumption. apply local_in_all; eassumption.
                 destruct (compose_meminjD_Some _ _ _ _ _ H2) as [bb2 [dd1 [dd2 [LC1 [LC2 DD]]]]]; clear H2.
                   apply local_in_all in LC1; trivial. 
                   apply local_in_all in LC2; trivial.  subst.
                   assert (compose_meminj (as_inj nu12) (as_inj nu23) bb1 = Some (b3, dd1 + dd2)).
                    eapply compose_meminjI_Some; try eassumption.
                 destruct (Mem.mi_no_overlap _ _ _ (Mem.inject_compose _ _ _ _ _ MInj12 MInj23) bb1 _ _ _ _ _ _ _ n H2 H3 N PERM).
                   apply H4; trivial.
                   apply H4; clear H4. omega.
                eapply VBj23_2; eassumption.
              rewrite Zplus_assoc. eapply MInj23; eassumption.
            (*source (pub_of nu12) m1 b2 ofs = None*)
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0; clear H2.
              assert (MX: Mem.perm m2 b2 ofs Max Nonempty).
                  eapply Mem.perm_max. eapply Mem.perm_implies.
                     apply H0. apply perm_any_N.
              assert (SRC:= source_NoneE _ _ _ _ Heqd); clear Heqd.
              apply UnchLOOR13.
                 split. eapply (pub_locBlocks _ WDnu23); eassumption.
                 intros bb1; intros. simpl. 
                 remember (pubBlocksSrc nu12 bb1) as d.
                 destruct d; try (right; reflexivity).
                 apply eq_sym in Heqd. left.
                 simpl in H2. 
                 destruct (compose_meminjD_Some _ _ _ _ _ H2) as [bb2 [dd1 [dd2 [LC1 [LC2 DD]]]]]; clear H2.
                 subst.
                 destruct (eq_block bb2 b2); subst.
                   rewrite (pub_in_local _ _ _ _ PUB23) in LC2. inv LC2.
                   assert (Mem.valid_block m1 bb1).
                     eapply VBj12_1. apply local_in_all; eassumption.
                   assert (Arith: ofs + dd2 - (dd1 + dd2) = ofs - dd1) by omega.
                   rewrite Arith. apply (SRC _ _ H2 LC1).
                 intros N. apply local_in_all in LC1; trivial.
                   apply (Mem.perm_inject (as_inj nu12) _ _ _ _ _ _ _ _ LC1 MInj12) in N.
                   apply local_in_all in LC2; trivial.              
                   destruct (Mem.mi_no_overlap _ _ _ MInj23 bb2 _ _ _ _ _ _ _ n LC2 FF N MX).
                   apply H2; trivial.
                   apply H2; clear H2. omega.
                eapply VBj23_2; eassumption.
              eapply MInj23; eassumption.
          (*case pubBlocksSrc nu23 b2 = false -- HERE IS THE SPOT THAT MOTIVATED THE NEW DEFINIEION LOCAL_OUT_OF_REACH*)
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0; clear H2.
              apply UNCHC.
                 split. eapply (local_locBlocks _ WDnu23). eassumption.
                 intros bb2; intros.
                 remember (pubBlocksSrc nu23 bb2) as d.
                 destruct d; try (right; reflexivity).
                 apply eq_sym in Heqd. left.
                 destruct (eq_block bb2 b2); subst.
                   rewrite Heqd in HeqPubB2; discriminate.
                 intros N. apply local_in_all in H2; trivial.
                   assert (MX: Mem.perm m2 b2 ofs Max Nonempty).
                     eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. apply perm_any_N.
                   destruct (Mem.mi_no_overlap _ _ _ MInj23 bb2 _ _ _ _ _ _ _ n H2 FF N MX).
                   apply H3; trivial.
                   apply H3; clear H3. omega.
                eapply VBj23_2; eassumption.
              eapply MInj23; eassumption.
        (*case locBlocksSrc nu23 b2 = false*)
          remember (source (as_inj nu12) m1 b2 ofs) as ss.
          destruct ss.
            destruct (source_SomeE _ _ _ _ _ Heqss)
                 as [b1 [d1 [ofs1 [PP [VB [ JJ [PERM Off2]]]]]]]. clear Heqss.
            subst.
            rewrite (perm_subst _ _ _ _ _ _ _ H2) in H0. clear H2.
            rewrite <- Zplus_assoc.
            eapply MemInjNu'; try eassumption. 
              rewrite ID. eapply compose_meminjI_Some.
                     apply inc12. apply JJ.
                     apply inc23. assumption. 
          (*source (as_inj nu12) m1 b2 ofs = None*)
            rewrite FF in H2.
            unfold Mem.perm in H0. rewrite H2 in H0. simpl in H0. contradiction.
            (*This case motivated setting perm m2' = None. In particular, assumption
              UnchLOOR13 does not help any more, in contrast to the development in 
              mem_interpolation.v*)     
      (*invalid*)
          assert (MX: Mem.perm m2' b2 ofs Max Nonempty).
              eapply Mem.perm_max. eapply Mem.perm_implies. 
                apply H0. apply perm_any_N.
          assert (Max2':= H2 Max ofs).
          specialize (H2 k ofs).
          assert (J23: as_inj nu23 b2 = None).
              remember (as_inj nu23 b2) as d.
              destruct d; trivial. apply eq_sym in Heqd. destruct p0.
              assert (X:= VBj23_1 _ _ _ Heqd).
              exfalso.  apply (H1 X).
          remember (source j12' m1' b2 ofs) as d.
          destruct d. destruct p0.
              rewrite (perm_subst _ _ _ _ _ _ _ H2) in *; clear H2.
              rewrite (perm_subst _ _ _ _ _ _ _ Max2') in *; clear Max2'.
              destruct (source_SomeE _ _ _ _ _ Heqd)
                as [b1 [d1 [ofs1 [PP [VB [ JJ' [PERM Off2]]]]]]]; clear Heqd.
              subst. apply eq_sym in PP. inv PP.
              rewrite <- Zplus_assoc.
              assert (Jb: as_inj nu' b= Some (b3, d1 + delta)).
                  rewrite ID.
                  eapply compose_meminjI_Some; eassumption.  
              eapply MemInjNu'. apply Jb. apply H0.  
          unfold Mem.perm in MX. rewrite Max2' in MX.  inv MX. 
  assert (MI: Mem.mem_inj j23' m2' m3').
      split.
      (*mi_perm *) apply Perm23'.
      (*valid_access*)
        intros b2 b3; intros.
          destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H)
            as [HH | [HH | HH]].
          destruct HH. eapply MInj23; try eassumption.
             intros z; intros. specialize (H0 _ H3).
              eapply Fwd2; try eassumption.
          destruct HH as [? [? ?]].
            assert (ZZ: compose_meminj j12' j23'  (Mem.nextblock m1) = Some (b3, delta)).
                   rewrite ID in H2; trivial. 
            rewrite Heqj12' in ZZ. subst.
            destruct (compose_meminjD_Some _ _ _ _ _ ZZ) as
                  [b2 [dd1 [dd2 [JJ1 [JJ2 XX]]]]]; subst; clear ZZ.
            assert (J12': prej12' (Mem.nextblock m1) = Some(Mem.nextblock m2, 0)).
               remember (as_inj nu12 (Mem.nextblock m1)) as q.
               destruct q; apply eq_sym in Heqq.
                 destruct p0. rewrite (inc12 _ _ _ Heqq) in JJ1. inv JJ1. 
                   apply VBj12_1 in Heqq. exfalso. unfold Mem.valid_block in Heqq. xomega.
                 unfold removeUndefs in JJ1. rewrite Heqq in JJ1. rewrite H2 in JJ1. 
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ JJ1).
                   destruct H1. rewrite H1 in Heqq. discriminate.
                   destruct H1. destruct H1 as [_ [? [? [? ?]]]]. subst. assumption.
                   destruct H1 as [mm [? [? [? [? ?]]]]]; subst.
                     apply eq_sym in H1. rewrite Pos.add_comm in H1.
                     apply Pos.add_no_neutral in H1. intuition.
            assert (PRE: prej12' (Mem.nextblock m1) = Some (b2, dd1)). 
              unfold removeUndefs in JJ1.
              remember (as_inj nu12 (Mem.nextblock m1)).
              destruct o; apply eq_sym in Heqo.
                destruct p0. apply VBj12_1 in Heqo. exfalso. unfold Mem.valid_block in Heqo. xomega.
              rewrite H2 in JJ1. assumption.
            rewrite J12' in PRE. inv PRE. simpl in *. clear JJ2. 
            destruct (ACCESS (Mem.nextblock m2)) as [_ ZZ].
            assert (NVB2: ~ Mem.valid_block m2 (Mem.nextblock m2)).
                       unfold Mem.valid_block. xomega. 
            assert (MR: Mem.range_perm m1' (Mem.nextblock m1) ofs (ofs + size_chunk chunk) Max p).
               intros z; intros.          
               specialize (ZZ NVB2 Max z).
               remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' (Mem.nextblock m2) z).
               destruct o.
               Focus 2. specialize (H0 _ H1). unfold Mem.perm in H0. rewrite ZZ in H0. simpl in H0. intuition. 
               destruct (source_SomeE _ _ _ _ _ Heqo)
                        as [b1 [dd1 [ofs1 [PPP [VB [ JJ' [PERM Off2]]]]]]]; clear Heqo.
               subst. specialize (H0 _ H1).
               rewrite (perm_subst _ _ _ _ _ _ _ ZZ) in H0; clear ZZ.
               assert (prej12'  b1 = Some (Mem.nextblock m2, dd1)).
                 unfold removeUndefs in JJ'.
                 remember (as_inj nu12 b1).
                 destruct o; apply eq_sym in Heqo.
                   destruct p0. inv JJ'. apply VBj12_2 in Heqo. contradiction.
                 remember (as_inj nu' b1).
                 destruct o. destruct p0. assumption. inv JJ'.
               assert (b1 = Mem.nextblock m1).
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ H4).
                 destruct H5. apply VBj12_2 in H5. contradiction.
                 destruct H5. destruct H5; trivial.
                 destruct H5 as [mm1 [? [? [? [? ?]]]]]. subst.
                   apply eq_sym in H6. rewrite Pos.add_comm in H6.
                   apply Pos.add_no_neutral in H6. intuition.
               subst. rewrite J12' in H4. inv H4. rewrite Zplus_0_r. assumption.     
             eapply MemInjNu'; eassumption.
          destruct HH as [mm [? [? ?]]]. subst. clear H3.
            assert (ZZ: compose_meminj (removeUndefs (as_inj nu12) (as_inj nu') prej12') j23' ((Mem.nextblock m1+ mm)%positive) = Some (b3, delta)).
                   rewrite <- ID; trivial. 
               destruct (compose_meminjD_Some _ _ _ _ _ ZZ) as
                  [b2 [dd1 [dd2 [JJ1 [JJ2 XX]]]]]. subst; clear ZZ.
            assert (J12': prej12' ((Mem.nextblock m1+ mm)%positive) = Some((Mem.nextblock m2+ mm)%positive, 0)).
               remember (as_inj nu12 ((Mem.nextblock m1+ mm)%positive)) as q.
               destruct q; apply eq_sym in Heqq.
                 destruct p0. rewrite (inc12 _ _ _ Heqq) in JJ1. inv JJ1. 
                   apply VBj12_1 in Heqq. exfalso. unfold Mem.valid_block in Heqq. xomega.
                 unfold removeUndefs in JJ1. rewrite Heqq in JJ1. rewrite H2 in JJ1. 
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ JJ1).
                   destruct H1. rewrite H1 in Heqq. discriminate.
                   destruct H1. destruct H1 as [? [? [? [? ?]]]]. subst.
                     rewrite Pos.add_comm in H1.
                     apply Pos.add_no_neutral in H1. intuition.
                   destruct H1 as [mm2 [? [? [? [? ?]]]]]; subst.
                     apply Pos.add_reg_l in H1. subst. 
                   assumption.
            assert (PRE: prej12' ((Mem.nextblock m1+ mm)%positive) = Some (b2, dd1)). 
              unfold removeUndefs in JJ1.
              remember (as_inj nu12 ((Mem.nextblock m1+ mm)%positive)).
              destruct o; apply eq_sym in Heqo.
                destruct p0. apply VBj12_1 in Heqo. exfalso. unfold Mem.valid_block in Heqo. xomega.
              rewrite H2 in JJ1. assumption.
            rewrite J12' in PRE. inv PRE. simpl in *. clear JJ2.  
            destruct (ACCESS ((Mem.nextblock m2+ mm)%positive)) as [_ ZZ].
            assert (NVB2: ~ Mem.valid_block m2 ((Mem.nextblock m2+ mm)%positive)).
                       unfold Mem.valid_block. xomega. 
            assert (MR: Mem.range_perm m1' ((Mem.nextblock m1+ mm)%positive) ofs (ofs + size_chunk chunk) Max p).
               intros z; intros.          
               specialize (ZZ NVB2 Max z).
               remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                      (Mem.nextblock m2 + mm)%positive z).
               destruct o.
               Focus 2. specialize (H0 _ H1). unfold Mem.perm in H0. rewrite ZZ in H0. simpl in H0. intuition. 
               destruct (source_SomeE _ _ _ _ _ Heqo)
                        as [bb1 [dd1 [ofs11 [PPP [VB [ JJ' [PERM Off2]]]]]]]. clear Heqo.
               subst. specialize (H0 _ H1).
               rewrite (perm_subst _ _ _ _ _ _ _ ZZ) in H0. clear ZZ.
               assert (prej12'  bb1 = Some ((Mem.nextblock m2+ mm)%positive, dd1)).
                 unfold removeUndefs in JJ'.
                 remember (as_inj nu12 bb1).
                 destruct o; apply eq_sym in Heqo.
                   destruct p0. inv JJ'. apply VBj12_2 in Heqo. contradiction.
                 remember (as_inj nu' bb1).
                 destruct o. destruct p0. assumption. inv JJ'.
               assert (bb1 = (Mem.nextblock m1+ mm)%positive).
                 destruct (mkInjections_3V  _ _ _ _ _ _ _ _ _ _ HeqMKI VB12 VBj23_1 _ _ _ H3).
                 destruct H4. apply VBj12_2 in H4. contradiction.
                 destruct H4. destruct H4 as [? [? ?]]; subst. 
                   rewrite Pos.add_comm in H5.
                   apply Pos.add_no_neutral in H5. intuition.
                 destruct H4 as [mm1 [? [? [? [? ?]]]]]. subst.
                   apply Pos.add_reg_l in H5. subst. trivial.
               subst. rewrite J12' in H3. inv H3. rewrite Zplus_0_r. assumption.
             eapply MemInjNu'; eassumption.
      (*memval j23' m2' m3'*) intros b2 ofs2 b3 delta3 Jb2 Perm2.
          assert (Perm2Max: Mem.perm m2' b2 ofs2  Max Nonempty).
             eapply Mem.perm_max. eapply Mem.perm_implies.
                        apply Perm2. constructor.
          destruct (ACCESS b2) as [Valid Invalid].
          apply (cont_split _ _ _ _ _ (CONT b2)); intros; clear CONT.
          (*case Mem.valid_block m2 b2*)
             assert (ValidMax := Valid H Max ofs2).
             specialize (Valid H Cur ofs2). clear Invalid.
             specialize (H0 ofs2).
             assert (J23: as_inj nu23 b2 = Some (b3, delta3)).
                 remember (as_inj nu23 b2) as d. destruct d; apply eq_sym in Heqd.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. apply Jb2.
                    destruct (sep23 _ _ _ Heqd Jb2). exfalso. apply (H2 H).
             rewrite J23 in Valid, ValidMax. (*rewrite Jb2 in H0.*)
             remember (locBlocksSrc nu23 b2) as LocB2.
             destruct LocB2; apply eq_sym in HeqLocB2.
               assert (LOC23: local_of nu23 b2 = Some (b3, delta3)).
                  destruct (joinD_Some _ _ _ _ _ J23) as [EXT | [EXT LOC]]; trivial.
                  destruct (extern_DomRng _ WDnu23 _ _ _ EXT).
                  destruct (disjoint_extern_local_Src _ WDnu23 b2); congruence. 
               remember (pubBlocksSrc nu23 b2) as PubB2.
               destruct PubB2; apply eq_sym in HeqPubB2.
                 remember (source (local_of nu12) m1 b2 ofs2) as ss.
                 destruct ss.
                 (*source (local_of nu12) m1 b2 ofs2  = Some p *)
                   destruct (source_SomeE _ _ _ _ _ Heqss)
                     as [b1 [delta2 [ofs1 [PP [Valb1 [ Jb1 [Perm1 Off]]]]]]].
                   clear Heqss; subst.
                     assert (J': as_inj nu' b1 = Some (b3, delta2 + delta3)).
                       rewrite ID. eapply compose_meminjI_Some; try eassumption.
                        apply inc12. apply local_in_all; eassumption.
                   remember (pubBlocksSrc nu12 b1) as d.
                   destruct d; apply eq_sym in Heqd.
                   (*case pubBlocksSrc nu12 b1 = true*)
                     rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2; clear Valid.
                     rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max; clear ValidMax.
                     rewrite H0 in *; clear H0. simpl in *.
                     assert (Perm1'Max: Mem.perm m1' b1 ofs1 Max Nonempty).
                       eapply Mem.perm_max; eassumption. 
                     specialize (Mem.mi_memval _ _ _
                          (Mem.mi_inj _ _ _ MemInjNu') _ _  _ _ J' Perm2). 
                     intros MemVal13'. 
                     rewrite <- Zplus_assoc.
                     inv MemVal13'; simpl in *; try econstructor.
                        rewrite ID in H3.        
                        destruct (compose_meminjD_Some _ _ _ _ _ H3) 
                           as [bb2 [dd2 [dd3 [RR [JJ23  DD]]]]]; subst; clear H3.
                        rewrite RR. econstructor. eassumption.
                          rewrite Int.add_assoc. decEq. unfold Int.add. 
                          apply Int.eqm_samerepr. auto with ints.
                   (*case pubBlocksSrc nu12 b1 = false*)
                     rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2; clear Valid. 
                     rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max; clear ValidMax.
                     rewrite H0 in *; clear H0. simpl in *.
                     destruct UnchLOOR13 as [UP3 UV3].
                     rewrite UV3. 
                       eapply memval_inject_incr. eapply MInj23. assumption. assumption. assumption.
                     split; simpl. eapply local_locBlocks; eassumption.
                       intros. destruct (compose_meminjD_Some _ _ _ _ _ H0) as [bb2 [dd1 [dd2 [LC12 [LC23 DD]]]]]; clear H0.
                         subst. 
                         destruct (eq_block b0 b1); subst. 
                           right; assumption.
                         remember (pubBlocksSrc nu12 b0) as d.
                         destruct d; try (right; reflexivity).
                         left; apply eq_sym in Heqd.
                         intros N.
                         assert (compose_meminj (as_inj nu12) (as_inj nu23) b0 = Some(b3,dd1+dd2)).
                            apply local_in_all in LC12; trivial.
                            apply local_in_all in LC23; trivial.
                            eapply compose_meminjI_Some; eassumption.
                         assert (compose_meminj (as_inj nu12) (as_inj nu23) b1 = Some(b3,delta2+delta3)).
                            apply local_in_all in Jb1; trivial.
                            eapply compose_meminjI_Some; eassumption.
                         destruct (Mem.mi_no_overlap _ _ _ (Mem.inject_compose _ _ _ _ _ MInj12 MInj23)
                                  _ _ _ _ _ _ _ _ n H0 H2 N Perm1).
                           apply H3; trivial.
                           apply H3; clear H3. omega.
                     eapply MInj23; eassumption.
                 (*case source  j12 m1 b2 ofs2  = None *)
                   rewrite H0. clear H0.
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid. 
                   rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max. clear ValidMax. 
                   assert (LOOR: local_out_of_reach 
                                (compose_sm nu12 nu23) m1 b3 (ofs2+delta3)).
                     split; simpl. eapply (local_DomRng _ WDnu23); eassumption.
                     intros. 
                     destruct (compose_meminjD_Some _ _ _ _ _ H0) as [bb2 [dd1 [dd2 [LC12 [LC23 D]]]]]; clear H0.
                     rewrite D in *; clear delta D. 
                     destruct (eq_block bb2 b2); subst.
                     (*case bb2=b2*)
                         rewrite LC23 in LOC23. inv LOC23. 
                         assert (Arith: ofs2 + delta3 - (dd1 + delta3) = ofs2 - dd1) by omega. 
                         rewrite Arith. left.
                         apply (source_NoneE _ _ _ _ Heqss). 
                             apply local_in_all in LC12; trivial. apply (VBj12_1 _ _ _ LC12).
                             assumption.
                     (*case bb2<>b2*)
                         remember (pubBlocksSrc nu12 b0) as d.
                         destruct d; try (right; reflexivity).
                         left; apply eq_sym in Heqd.
                         intros N.
                         assert (NN2: Mem.perm m2 bb2
                                     (ofs2 + (delta3 - dd2)) Max Nonempty).
                             assert (Arith: ofs2 + delta3 - (dd1 + dd2) + dd1 = 
                                      ofs2 + (delta3 - dd2)) by omega. 
                             rewrite <- Arith.
                             eapply MInj12; try eassumption.
                               apply local_in_all; assumption.
                         apply local_in_all in LC23; trivial.
                         destruct (Mem.mi_no_overlap _ _ _ 
                                 MInj23 _ _ _ _ _ _ _ _ n LC23 J23 NN2 Perm2Max).
                                     apply H0; trivial.
                                     apply H0. omega.                         
                   assert (Perm3: Mem.perm m3 b3 (ofs2+delta3) Cur Readable).
                     eapply MInj23. apply J23. apply Perm2.
                   destruct UnchLOOR13 as [Uperm UVal]. 
                   rewrite (UVal _ _ LOOR Perm3).
                   eapply memval_inject_incr. 
                     apply (Mem.mi_memval _ _ _ 
                            (Mem.mi_inj _ _ _  MInj23) _ _ _ _ J23 Perm2). 
                     apply inc23.
               (*case pubBlocksSrc nu23 b2 = false*)
                 rewrite H0. clear H0.
                 rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2. clear Valid. 
                 rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max. clear ValidMax. 
                 assert (LOOR: local_out_of_reach nu23 m2 b3 (ofs2+delta3)).
                  split; simpl. eapply (local_DomRng _ WDnu23); eassumption.
                     intros bb2; intros.
                     destruct (eq_block bb2 b2); subst.
                     (*case bb2=b2*) right; assumption.
                     (*case bb2<>b2*)
                         remember (pubBlocksSrc nu23 bb2) as d.
                         destruct d; try (right; reflexivity).
                         left; apply eq_sym in Heqd.
                         intros N.
                         apply local_in_all in H0; trivial.
                         destruct (Mem.mi_no_overlap _ _ _ 
                                 MInj23 _ _ _ _ _ _ _ _ n H0 J23 N Perm2Max).
                                     apply H2; trivial.
                                     apply H2. omega.                         
                   assert (Perm3: Mem.perm m3 b3 (ofs2+delta3) Cur Readable).
                     eapply MInj23. apply J23. apply Perm2.
                   destruct UNCHC as [Uperm UVal]. 
                   rewrite (UVal _ _ LOOR Perm3).
                   eapply memval_inject_incr. 
                     apply (Mem.mi_memval _ _ _ 
                            (Mem.mi_inj _ _ _  MInj23) _ _ _ _ J23 Perm2). 
                     apply inc23.                     
             (*case locBlocksSrc nu23 b2 = false*)
                 remember (source (as_inj nu12) m1 b2 ofs2) as ss.
                 destruct ss.
                 (*source (local_of nu12) m1 b2 ofs2  = Some p *)
                   destruct (source_SomeE _ _ _ _ _ Heqss)
                     as [b1 [delta2 [ofs1 [PP [Valb1 [ Jb1 [Perm1 Off]]]]]]].
                   clear Heqss; subst.
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in Perm2; clear Valid. 
                   rewrite (perm_subst _ _ _ _ _ _ _ ValidMax) in Perm2Max; clear ValidMax. 
                   rewrite H0; clear H0; simpl in *.
                   assert (J': as_inj nu' b1 = Some (b3, delta2 + delta3)).
                       rewrite ID. eapply compose_meminjI_Some; try eassumption.
                        apply inc12. eassumption.
                   specialize (Mem.mi_memval _ _ _
                          (Mem.mi_inj _ _ _ MemInjNu') _ _  _ _ J' Perm2). 
                   intros MemVal13'. 
                   rewrite <- Zplus_assoc.
                   inv MemVal13'; simpl in *; try econstructor.
                      rewrite ID in H3.        
                        destruct (compose_meminjD_Some _ _ _ _ _ H3) 
                           as [bb2 [dd2 [dd3 [RR [JJ23  DD]]]]]; subst; clear H3.
                        rewrite RR. econstructor. eassumption.
                          rewrite Int.add_assoc. decEq. unfold Int.add. 
                          apply Int.eqm_samerepr. auto with ints.
                 (*case source  j12 m1 b2 ofs2  = None *)
                   rewrite H0; clear H0.
                   unfold Mem.perm in Perm2Max, Perm2. 
                   rewrite Valid in Perm2; clear Valid. 
                   simpl in Perm2. contradiction.
          (*case ~ Mem.valid_block m2 b2*)
             specialize (H0 ofs2). clear Valid.
             assert (InvalidMax := Invalid H Max ofs2). 
             specialize (Invalid H Cur ofs2).
             assert (J23: as_inj nu23 b2 = None).
                 remember (as_inj nu23 b2) as d. 
                 destruct d; apply eq_sym in Heqd; trivial.
                    destruct p. rewrite (inc23 _ _ _ Heqd) in Jb2. inv Jb2.
                          exfalso. apply H. apply (VBj23_1 _ _ _ Heqd).
             remember (source j12' m1' b2 ofs2) as ss.
             destruct ss.
             (*source f m1' b2 ofs2  = Some p *)
                 destruct p. rewrite H0 in *. clear H0.
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid) in Perm2; clear Invalid. 
                 rewrite (perm_subst _ _ _ _ _ _ _ InvalidMax) in Perm2Max; clear InvalidMax. 
                 destruct (source_SomeE _ _ _ _ _ Heqss)
                    as [b1 [delta2 [ofs1 [PP [VB [RR1 [Perm1' Off2]]]]]]].
                 clear Heqss.
                 inv PP.
                 assert (JB: as_inj nu' b1 = Some (b3, delta2 + delta3)).
                       rewrite ID. eapply compose_meminjI_Some; try eassumption.
                 specialize (Mem.mi_memval _ _ _ 
                       (Mem.mi_inj _ _ _  MemInjNu') _ _  _ _ JB Perm2). 
                 intros MemVal13'.                    
                 rewrite <- Zplus_assoc. 
                 inv MemVal13'; simpl in *; try econstructor.
                 rewrite ID in H3.                     
                 destruct (compose_meminjD_Some _ _ _ _ _ H3)
                       as [bb2 [dd2 [ddd3 [RRR [JJJ23  DD]]]]]; subst.
                    rewrite RRR. econstructor. apply JJJ23.
                    rewrite Int.add_assoc. decEq. unfold Int.add. 
                       apply Int.eqm_samerepr. auto with ints.  
             (*source  j12' m1' b1 ofs  = None *) 
                 unfold Mem.perm in Perm2. rewrite Invalid in Perm2. inv Perm2.
   split; trivial.
   (*mi_freeblocks*)
       intros. remember (j23' b) as d.
       destruct d; apply eq_sym in Heqd; trivial.
       destruct p. exfalso.

       destruct (mkInjections_0 _ _ _ _ _ _ _ _ _ _ HeqMKI)
        as [HH | HH].
       destruct HH as [? [? [? [?  ?]]]]; subst.
         apply H. apply Fwd2. apply (VBj23_1 _ _ _ Heqd).
       destruct HH as [N [? [? [? ?]]]]. 
         destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ Heqd)
            as [HH | [HH | HH]].
         destruct HH. apply H. apply Fwd2. apply H5. 
         destruct HH as [? [? ?]]; subst.
            apply (H H6).    
         destruct HH as [M [BM [J' B]]]; subst.
            apply (H B). 
   (*mi_mappedblocks*)
      intros. 
      destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI 
        VBj23_1 _ _ _ H)as [HH | [HH | HH]].
      destruct HH. apply Fwd3. apply (VBj23_2 _ _ _  H0).
      destruct HH as [? [? ?]]; subst.
        eapply MemInjNu'. apply H1.
         destruct HH as [M [BM [J' B]]]; subst.
           eapply MemInjNu'. apply J'.
   (*no_overlap*)
      intros b; intros.
      destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI
        VBj23_1 _ _ _ H0) as [HH | [HH | HH]].
      destruct HH as [j23b vbb].
         destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ 
               HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2]. 
            eapply MInj23. 
               apply H. 
               apply j23b. 
               apply j23b2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b). apply H2.
               apply Fwd2. apply (VBj23_1 _ _ _ j23b2). apply H3.
            destruct KK as [BM [J' B']]; subst.
              left. assert (as_inj nu23 (Mem.nextblock m2) = None).
                     remember (as_inj nu23 (Mem.nextblock m2)) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd). 
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst. 
                    destruct (sep23 _ _ _ H4 H1). apply H6. 
                    eapply MInj23. apply j23b.
            destruct KK as [M [BM [J' B']]].
            left. assert (as_inj nu23 b2 = None).
                     remember (as_inj nu23 b2) as d.
                     destruct d; trivial.
                     destruct p. apply eq_sym in Heqd.
                     specialize (VBj23_1 _ _ _ Heqd).
                     clear - VBj23_1 BM. subst.
                     unfold Mem.valid_block in VBj23_1. xomega.
                  intros N; subst. 
                    destruct (sep23 _ _ _ H4 H1). apply H6. 
                    eapply MInj23. apply j23b.
         destruct HH as [NBb [j'b NBb']]; subst.
           destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ 
                HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].  
             left. assert (as_inj nu23 (Mem.nextblock m2) = None).
                      remember (as_inj nu23 (Mem.nextblock m2)) as d. 
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                     destruct (sep23 _ _ _ H4 H0).
                     apply H6. eapply MInj23. apply j23b2.
            destruct KK as [BM [J' B']]; subst.
              exfalso. apply H; trivial.
            destruct KK as [M [BM [J' B']]]. subst.
          (*first case where both blocks are in m2' but not in m2*)
              assert (j23_None1: as_inj nu23 (Mem.nextblock m2) = None).
                 remember (as_inj nu23 (Mem.nextblock m2)) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2: as_inj nu23 ((Mem.nextblock m2 + M)%positive) = None).
                 remember (as_inj nu23 ((Mem.nextblock m2 + M)%positive)) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 exfalso. unfold Mem.valid_block in VBj23_1. xomega.      
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : Mem.nextblock m1 <> (Mem.nextblock m1 + M)%positive). 
                 apply add_no_neutral2. 
              destruct (ACCESS (Mem.nextblock m2)) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).
                           
              remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    m1' (Mem.nextblock m2) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p. 
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2 + M)%positive) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                         (Mem.nextblock m2 + M)%positive ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p. 
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3. 
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

                     destruct (source_SomeE _ _ _ _ _ Heqd) 
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (as_inj nu12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1. 
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (as_inj nu' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p. 
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ 
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst. 
                       destruct (source_SomeE _ _ _ _ _ Heqd0) as 
                           [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                       clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                       unfold removeUndefs in JJ2'.
                       remember (as_inj nu12 b2) as r.
                       destruct r; apply eq_sym in Heqr.
                           destruct p. inv JJ2'. 
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                       remember (as_inj nu' b2) as rr.
                       destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                       destruct p. 
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H7)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                              exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) M).
                                 rewrite Pos.add_comm. apply H10.
                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           apply Pos.add_reg_l in nbm. apply eq_sym in nbm.  subst. 
                           eapply MemInjNu'. 
                              apply NEQ. 
                              assumption.
                              assumption. 
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       exfalso. apply (add_no_neutral2 (Mem.nextblock m2) MM1).
                         apply H6.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2.
         destruct HH as [M1 [? [j'b1 NBb1]]]; subst.
           destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ 
                HeqMKI VBj23_1 _ _ _ H1) as [KK | [KK | KK]].
            destruct KK as [j23b2 vbb2].  
             left. assert (as_inj nu23 (Mem.nextblock m2 + M1)%positive = None).
                      remember (as_inj nu23 (Mem.nextblock m2 + M1)%positive) as d. 
                      destruct d; trivial. destruct p.
                      apply eq_sym in Heqd.
                      specialize (VBj23_1 _ _ _ Heqd).
                      clear - VBj23_1.
                      unfold Mem.valid_block in VBj23_1. xomega.
                   intros N; subst.
                     destruct (sep23 _ _ _ H4 H0).
                     apply H6. eapply MInj23. apply j23b2.
            destruct KK as [BM [J' B']]; subst.
          (*second case where both blocks are in m2' but not in m2*)
              assert (j23_None1: as_inj nu23 (Mem.nextblock m2 + M1)%positive = None).
                 remember (as_inj nu23 (Mem.nextblock m2 + M1)%positive) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2: as_inj nu23 (Mem.nextblock m2) = None).
                 remember (as_inj nu23 (Mem.nextblock m2)) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 exfalso. unfold Mem.valid_block in VBj23_1. xomega.      
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : (Mem.nextblock m1 + M1)%positive <> Mem.nextblock m1). 
                rewrite Pos.add_comm. apply Pos.add_no_neutral. 
              destruct (ACCESS (Mem.nextblock m2 + M1)%positive) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).
                           
              remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')
                    m1' ((Mem.nextblock m2 +M1)%positive) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p. 
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  (Mem.nextblock m2)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1'
                         (Mem.nextblock m2) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p. 
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3. 
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

                     destruct (source_SomeE _ _ _ _ _ Heqd) 
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (as_inj nu12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1. 
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (as_inj nu' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p. 
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ 
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst. 
                       exfalso. rewrite Pos.add_comm in H6. 
                        apply Pos.add_no_neutral in H6. apply H6.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       apply Pos.add_reg_l in H6. apply eq_sym in H6. subst.
                       destruct (source_SomeE _ _ _ _ _ Heqd0) as 
                           [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                       clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                       unfold removeUndefs in JJ2'.
                       remember (as_inj nu12 b2) as r.
                       destruct r; apply eq_sym in Heqr.
                           destruct p. inv JJ2'. 
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                       remember (as_inj nu' b2) as rr.
                       destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                       destruct p. 
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H6)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst. 
                           eapply MemInjNu'. 
                              apply NEQ. 
                              assumption.
                              assumption. 
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.

                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) MM2).
                                 rewrite Pos.add_comm. rewrite <- nbm. trivial.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2. 
            destruct KK as [M2 [BM [J2' B2']]]; subst.
          (*third case where both blocks are in m2' but not in m2*)
              assert (j23_None1: as_inj nu23 (Mem.nextblock m2 + M1)%positive = None).
                 remember (as_inj nu23 (Mem.nextblock m2 + M1)%positive) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              assert (j23_None2:  as_inj nu23 (Mem.nextblock m2 + M2)%positive = None).
                 remember (as_inj nu23 (Mem.nextblock m2 + M2)%positive) as d. 
                 destruct d; trivial. 
                 apply eq_sym in Heqd. destruct p. 
                 specialize (VBj23_1 _ _ _ Heqd). clear - VBj23_1.
                 unfold Mem.valid_block in VBj23_1. xomega.
              destruct (sep23 _ _ _ j23_None1 H0) as [NV2_1 NV3_1].
              destruct (sep23 _ _ _ j23_None2 H1) as [NV2_2 NV3_2].
              assert (Max3_1:= Perm23' _ _ _ _ _ _ H0 H2).
              assert (Max3_2:= Perm23' _ _ _ _ _ _ H1 H3).
              assert (NEQ : (Mem.nextblock m1 + M1)%positive <> (Mem.nextblock m1 + M2)%positive). 
                intros NN. apply Pos.add_cancel_l in NN. subst. 
                apply H; trivial. 
              destruct (ACCESS (Mem.nextblock m2 + M1)%positive) as [_ Invalid1].
              specialize (Invalid1 NV2_1 Max ofs1).
                           
              remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') 
                    m1' ((Mem.nextblock m2 +M1)%positive) ofs1) as d.
              destruct d.
              (*source j12' ofs1 = Some*)
                 destruct p. 
                 rewrite (perm_subst _ _ _ _ _ _ _ Invalid1) in H2.
                 clear Invalid1.
                 destruct (ACCESS  ((Mem.nextblock m2 + M2)%positive)) as [_ Invalid2].
                 specialize (Invalid2 NV2_2 Max ofs2).

                 remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12')  m1'
                         ((Mem.nextblock m2 + M2)%positive) ofs2) as d.
                 destruct d.
                 (*source j12' ofs2 = Some*)
                     destruct p. 
                     rewrite (perm_subst _ _ _ _ _ _ _ Invalid2) in H3. 
                     clear Invalid2.
                     rename b into b1. rename z into z1. rename b0 into b2.
                     rename z0 into z2.

                     destruct (source_SomeE _ _ _ _ _ Heqd) 
                         as [bb1 [dd1 [ofs11 [PP [VB [ JJ' [PERM Off1]]]]]]].
                     clear Heqd. subst. apply eq_sym in PP. inv PP.
                     unfold removeUndefs in JJ'.
                     remember (as_inj nu12 b1) as q.
                     destruct q; apply eq_sym in Heqq.
                       destruct p. inv JJ'. exfalso. apply NV2_1. 
                           apply (VBj12_2 _ _ _ Heqq).
                     remember (as_inj nu' b1) as qq.
                     destruct qq; inv JJ'. apply eq_sym in Heqqq.
                     destruct p. 
                     destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ 
                              HeqMKI VB12 VBj23_1 _ _ _ H5) as [HH | [HH |HH]].
                     destruct HH as [HH _]. rewrite HH in Heqq; discriminate.
                     destruct HH as [? [? [? [? ?]]]]; subst. 
                       exfalso. rewrite Pos.add_comm in H6. 
                        apply Pos.add_no_neutral in H6. apply H6.
                     destruct HH as [MM1 [? [? [? [? ?]]]]]; subst.
                       apply Pos.add_reg_l in H6. apply eq_sym in H6. subst.
                       destruct (source_SomeE _ _ _ _ _ Heqd0) as 
                           [bb2 [dd2 [ofs22 [PP2 [VB2 [ JJ2' [PERM2 Off2]]]]]]].
                       clear Heqd0. subst. apply eq_sym in PP2. inv PP2.
                       unfold removeUndefs in JJ2'.
                       remember (as_inj nu12 b2) as r.
                       destruct r; apply eq_sym in Heqr.
                           destruct p. inv JJ2'. 
                           exfalso. apply NV2_2. apply (VBj12_2 _ _ _ Heqr).
                       remember (as_inj nu' b2) as rr.
                       destruct rr; inv JJ2'. apply eq_sym in Heqrr.
                       destruct p. 
                       destruct (mkInjections_3V _ _ _ _ _ _ _ _
                                         _ _ HeqMKI VB12 VBj23_1 _ _ _ H6)
                           as [KK | [KK | KK]].
                         destruct KK as [KK _]. rewrite KK in Heqr; discriminate.
                         destruct KK as [? [? [? [? ?]]]]. subst.
                           exfalso. apply (Pos.add_no_neutral (Mem.nextblock m2) M2).
                                 rewrite Pos.add_comm. trivial.
                            
                         destruct KK as [MM2 [BB2 [nbm
                                           [zz [X2 Y2]]]]]. subst.
                           apply Pos.add_cancel_l in nbm. subst.
                           eapply MemInjNu'. 
                              apply NEQ. 
                              assumption.
                              assumption. 
                              rewrite Zplus_0_r. apply PERM.
                              rewrite Zplus_0_r. apply PERM2.
                 (*source j12' ofs2 = None*)
                    unfold Mem.perm in H3. rewrite Invalid2 in H3. inv H3.
                 (*source j12' ofs1 = None*)
                    unfold Mem.perm in H2. rewrite Invalid1 in H2. inv H2. 

   (*mi_representable*) intros. rename b into b2.
       destruct (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI VBj23_1 _ _ _ H)
       as [HH | [ HH | HH]].
       (*first case*)
         destruct HH as [j23b2 Val2].
         destruct (ACCESS b2) as [Valid _]. 
         rewrite j23b2 in Valid.
         specialize (Valid Val2).
         remember (locBlocksSrc nu23 b2) as MyB2.
         destruct MyB2; apply eq_sym in HeqMyB2.
         (*case locBlocksSrc nu23 b2 = true*)
           remember (pubBlocksSrc nu23 b2) as PubB2.
           destruct PubB2; apply eq_sym in HeqPubB2.
           (*case pubBlocksSrc nu23 b2 = true*)
             destruct H0.
             (*location ofs*)
               specialize (Valid Max (Int.unsigned ofs)).
               remember (source (local_of nu12) m1 b2 (Int.unsigned ofs)) as d.
               destruct d.  
               (*source ... m1 b2 (Int.unsigned ofs) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd) 
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs) Max Nonempty). 
                   remember (pubBlocksSrc nu12 b) as PubB1.
                   destruct PubB1; apply eq_sym in HeqPubB1;
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                      rewrite Off1. eapply MInj12. apply local_in_all; eassumption. apply PERM. 
                      assumption. 
                 eapply MInj23. apply j23b2. 
                   left. assumption. 
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                 eapply MInj23. apply j23b2. 
                 left. apply H0. 
             (*location ofs -1*)
               specialize (Valid Max (Int.unsigned ofs -1)).
               remember (source (local_of nu12) m1 b2 (Int.unsigned ofs -1)) as d.
               destruct d.  
               (*source .. m1 b2 (Int.unsigned ofs-1) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd) 
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs -1) Max Nonempty). 
                   remember (pubBlocksSrc nu12 b) as PubB1.
                   destruct PubB1; apply eq_sym in HeqPubB1;
                   rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                      rewrite Off1. eapply MInj12. apply local_in_all; eassumption. apply PERM. 
                      assumption. 
                 eapply MInj23. apply j23b2. 
                   right. assumption. 
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
                 eapply MInj23. apply j23b2. 
                 right. apply H0. 
           (*case pubBlocksSrc nu23 b2 = false*)
             destruct H0.
             (*location ofs*)
               specialize (Valid Max (Int.unsigned ofs)).
               rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
               eapply MInj23. apply j23b2. 
               left. apply H0. 
             (*location ofs-1*)
               specialize (Valid Max (Int.unsigned ofs-1)).
               rewrite (perm_subst _ _ _ _ _ _ _ Valid) in H0; clear Valid.
               eapply MInj23. apply j23b2. 
               right. apply H0. 
         (*case locBlocksSrc nu23 b2 = false*)
             destruct H0.
             (*location ofs*)
               specialize (Valid Max (Int.unsigned ofs)).
               remember (source (as_inj nu12) m1 b2 (Int.unsigned ofs)) as d.
               destruct d.  
               (*source ... m1 b2 (Int.unsigned ofs) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd) 
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs) Max Nonempty).
                   rewrite Off1. eapply MInj12; eassumption. 
                 eapply MInj23. apply j23b2. 
                   left. assumption. 
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 unfold Mem.perm in H0; rewrite Valid in H0; simpl in H0. contradiction.
             (*location ofs-1*)
               specialize (Valid Max (Int.unsigned ofs-1)).
               remember (source (as_inj nu12) m1 b2 (Int.unsigned ofs-1)) as d.
               destruct d.  
               (*source ... m1 b2 (Int.unsigned ofs) = Some p*)
                 destruct p.
                 destruct (source_SomeE _ _ _ _ _ Heqd) 
                   as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
                 clear Heqd. subst. apply eq_sym in PP. inv PP.
                 assert (PP2: Mem.perm m2 b2 (Int.unsigned ofs-1) Max Nonempty).
                   rewrite Off1. eapply MInj12; eassumption. 
                 eapply MInj23. apply j23b2. 
                   right. assumption. 
               (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
                 unfold Mem.perm in H0; rewrite Valid in H0; simpl in H0. contradiction.
       (*second case*)
         destruct HH as [? [j'b2 Val2']]. subst.
         destruct (ACCESS (Mem.nextblock m2)) as [_ InValid].
         assert (NVB2: ~Mem.valid_block m2 (Mem.nextblock m2)).
            unfold Mem.valid_block; xomega.
         specialize (InValid NVB2).
         destruct H0.
         (*location ofs*)
           specialize (InValid Max (Int.unsigned ofs)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' (Mem.nextblock m2)
                            (Int.unsigned ofs)) as d.
           destruct d.  
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd) 
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros. 
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI 
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [_ [? [? ?]]]]; subst.
                    rewrite Zplus_0_r in *. subst.
                    eapply MemInjNu'. apply j'b2. left; apply PERM. 
                destruct KK as [m [_ [? _]]]. 
                    exfalso. clear -H3. apply (add_no_neutral2 _ _ H3).
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
         (*location ofs -1*)
           specialize (InValid Max (Int.unsigned ofs-1)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' (Mem.nextblock m2)
                            (Int.unsigned ofs-1)) as d.
           destruct d.  
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd) 
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros. 
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI 
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [_ [? [? ?]]]]; subst.
                    rewrite Zplus_0_r in *. subst.
                    eapply MemInjNu'. apply j'b2. right; apply PERM. 
                destruct KK as [m [_ [? _]]]. 
                    exfalso. clear -H3. apply (add_no_neutral2 _ _ H3).
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
       (*third case*)
         destruct HH as [m [? [j'b2 Val2']]]; subst.
         destruct (ACCESS ((Mem.nextblock m2+m)%positive)) as [_ InValid].
         assert (NVB2: ~Mem.valid_block m2 ((Mem.nextblock m2+m)%positive)).
            unfold Mem.valid_block; xomega.
         destruct H0.
         (*location ofs*)
           specialize (InValid NVB2 Max (Int.unsigned ofs)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' 
                            ((Mem.nextblock m2+m)%positive)
                            (Int.unsigned ofs)) as d.
           destruct d.  
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd) 
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros. 
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI 
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [? [? [? ?]]]]; subst.
                    exfalso. clear -H4. apply eq_sym in H4. 
                    apply (add_no_neutral2 _ _ H4).
                destruct KK as [mm [? [? [? [? ?]]]]]. subst.
                   assert (mm = m).
                      clear -H4. 
                      apply Pos.add_reg_l in H4. 
                      subst; trivial.
                   rewrite Zplus_0_r in *. subst.
                   eapply MemInjNu'. apply j'b2. left. apply PERM.
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.
         (*location ofs -1*)
           specialize (InValid NVB2 Max (Int.unsigned ofs-1)).
           remember (source (removeUndefs (as_inj nu12) (as_inj nu') prej12') m1' 
                            ((Mem.nextblock m2+m)%positive)
                            (Int.unsigned ofs-1)) as d.
           destruct d.  
           (*source .. = Some p*)
             destruct p.
             destruct (source_SomeE _ _ _ _ _ Heqd) 
                 as [b1 [delta1 [ofs1 [PP [VB [ J12 [PERM Off1]]]]]]].
             clear Heqd. subst. apply eq_sym in PP. inv PP.
             unfold removeUndefs in J12.
             case_eq (as_inj nu12 b); intros. 
                destruct p; rewrite H1 in J12. inv J12.
                exfalso. apply NVB2. apply (VBj12_2 _ _ _ H1).
             rewrite H1 in J12.
             case_eq (as_inj nu' b); intros.
                destruct p; rewrite H2 in J12.
                destruct (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI 
                    VB12 VBj23_1 _ _ _ J12) as [KK | [KK |KK]].
                destruct KK as [KK _]; rewrite KK in H1; discriminate.
                destruct KK as [? [? [? [? ?]]]]; subst.
                    exfalso. clear -H4. apply eq_sym in H4. 
                    apply (add_no_neutral2 _ _ H4).
                destruct KK as [mm [? [? [? [? ?]]]]]. subst.
                   assert (mm = m).
                      clear -H4. 
                      apply Pos.add_reg_l in H4. 
                      subst; trivial.
                   rewrite Zplus_0_r in *. subst.
                   eapply MemInjNu'. apply j'b2. right. apply PERM.
             rewrite H2 in J12. inv J12.
           (*source  j12 m1 b2 (Int.unsigned ofs-1) = None0*)
             unfold Mem.perm in H0. rewrite InValid in H0.
             contradiction.

specialize (mkInjections_3V _ _ _ _ _ _ _ _ _ _ HeqMKI Val12 Val23).
intros mkiVal3.
specialize (mkInjections_4Val _ _ _ _ _ _ _ _ _ _ HeqMKI Val23). intros mkiVal4.
specialize (mkInjections_5 _ _ _ _ _ _ _ _ _ _ HeqMKI VBj12_1 VBj12_2 VBj23_1 VBj'). intros mkiVal5.
clear CONT ACCESS HeqMKI.
assert (GOAL1: nu' =
compose_sm
  (convertL nu12 j12'
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23'))
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b)))).
  destruct ExtIncr as [AA [BB [CC [DD [EE [FF [GG [HH [II JJ]]]]]]]]]; simpl in *.
  unfold compose_sm; simpl in *. clear ConvertL_J12'. clear ConvertR_J23'.
  rewrite convertL_extern, convertL_local, convertL_frgnBlocksSrc, 
          convertL_pubBlocksSrc, convertL_locBlocksSrc, convertL_extBlocksSrc.
  rewrite convertR_extern, convertR_local, convertR_frgnBlocksTgt, 
          convertR_pubBlocksTgt, convertR_locBlocksTgt, convertR_extBlocksTgt.
  destruct nu' as [locBSrc' locBTgt' pSrc' pTgt' local' extBSrc' extBTgt' fSrc' fTgt' extern'].
  simpl in *. unfold as_inj in *; simpl in *.
  f_equal; simpl; subst; simpl in *; trivial.
  (*1/3*) 
     extensionality b. 
     specialize (disjoint_extern_local_Src _ WDnu' b). intros.
     unfold DomSrc, DomTgt in *; simpl in *.
     specialize (CC b).  
     clear - CC H.    
     remember (locBlocksSrc nu12 b) as q.
     remember (extBlocksSrc nu12 b) as t.
     destruct q; destruct t; simpl in *; intuition.
     rewrite andb_true_r. trivial.
     rewrite andb_true_r. trivial.
  (*2/3*)
     extensionality b.
     specialize (disjoint_extern_local_Tgt _ WDnu' b). intros.
     unfold DomSrc, DomTgt in *; simpl in *.
     specialize (DD b).
     clear - DD H. 
     remember (locBlocksTgt nu23 b) as q.
     remember (extBlocksTgt nu23 b) as t.
     destruct q; destruct t; simpl in *; intuition.
     rewrite andb_true_r. trivial.
     rewrite andb_true_r. trivial.
  (*3/3*)
     clear Inj12' NOVj12' Inj23' UNCHC MemInjNu' Fwd2 MInj23 Fwd1 MInj12 UnchPrivSrc UnchLOOR13 VBj'
           Fwd1 Fwd3 SMV12 SMV23 SMvalNu' InjSep VBj23_2 sep23 NB1 SMInjSep
           VBj23' Val12 Val23 mkiVal3 m3 m1' m3'.
     extensionality b1.
     remember (extern' b1) as d.
     destruct d; apply eq_sym in Heqd.
     (*case externNu' b1 = Some p*)
       destruct p as [b3 delta].
       assert (J: join extern' (compose_meminj (local_of nu12) (local_of nu23)) b1 = Some (b3, delta)).
         apply join_incr_left. apply Heqd.
       rewrite ID in J; clear ID.
       destruct (compose_meminjD_Some _ _ _ _ _ J) 
        as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear J.
       apply eq_sym. 
       eapply compose_meminjI_Some with (b2:=b2).
       (*condition 1*)
         remember (extern_of nu12 b1) as q.
         destruct q; apply eq_sym in Heqq.
         (*case extern_of nu12 b1 = Some p*)
           destruct p as [bb2 dd1].
           unfold join. rewrite Heqq.
           apply extern_in_all in Heqq.
           apply inc12 in Heqq. unfold as_inj in Heqq. simpl in *. 
             rewrite Heqq in J1. apply J1.
         (*case extern_of nu12 b1 = Some p*)
           unfold join. rewrite Heqq.
           remember (local_of nu12 b1) as w.
           destruct w; trivial; apply eq_sym in Heqw.
           destruct p as [bb dd].
           assert (locBlocksSrc nu12 b1 = true).
             eapply local_locBlocks; eassumption.
           assert (locBlocksSrc nu12 b1 = false).
             eapply (extern_DomRng' _ WDnu'). simpl. apply Heqd.
           rewrite H0 in H. inv H.
       (*condition 2*)      
         unfold join.
         remember (extern_of nu23 b2) as q.
         destruct q; apply eq_sym in Heqq.
           destruct p.
           rewrite (inject_incr_coincide _ _ inc23 _ _ J2 _ 
               (extern_in_all _ _ _ _ Heqq)). trivial.
         remember (local_of nu23 b2) as w.
         destruct w; apply eq_sym in Heqw; trivial.
         destruct p. 
         assert (E:= inject_incr_coincide _ _ inc23 _ _ J2 _ 
               (local_in_all _ WDnu23 _ _ _ Heqw)); inv E.
         assert (locBlocksTgt nu23 b = true).
           eapply local_locBlocks; eassumption.
         assert (locBlocksTgt nu23 b = false).
           eapply (extern_DomRng' _ WDnu'). simpl. apply Heqd.
         rewrite H0 in H. inv H.
     (*externNu' b1 = None*)
        unfold as_inj in inc12. simpl in inc12.
        remember (compose_meminj (local_of nu12) (local_of nu23) b1) as q.
        destruct q; apply eq_sym in Heqq.
        (*case compose_meminj (local_of nu12) (local_of nu23) b1 = Some p*)
          destruct p as [b3 delta].
          destruct (compose_meminjD_Some _ _ _ _ _ Heqq) 
            as [b2 [d1 [d2 [Loc12 [Loc23 D]]]]]; subst; clear Heqq.
          apply eq_sym.
          destruct (disjoint_extern_local _ WDnu12 b1).
            unfold compose_meminj, join. rewrite H, Loc12. trivial.
          rewrite H in Loc12. inv Loc12.
        (*case compose_meminj (local_of nu12) (local_of nu23) b1 = None*)
          assert (compose_meminj
            (removeUndefs (join (extern_of nu12) (local_of nu12))
               (join extern' (compose_meminj (local_of nu12) (local_of nu23))) prej12')
            j23' b1 = None).
              rewrite <- ID. unfold join. rewrite Heqd. trivial.
          clear ID.
          remember (extern_of nu12 b1) as w.
          destruct w; apply eq_sym in Heqw.
          (*case extern_of nu12 b1 = Some p*)
            destruct p as [b2 d1].
            assert (R: removeUndefs (join (extern_of nu12) (local_of nu12))
                        (join extern' (compose_meminj (local_of nu12) (local_of nu23)))
                         prej12' b1 = Some (b2, d1)).
                apply inc12. apply extern_in_all. apply Heqw.
            destruct (compose_meminjD_None _ _ _ H); clear H.
               rewrite H0 in R. inv R.
            destruct H0 as [bb2 [dd1 [XX J23']]].
            rewrite R in XX. apply eq_sym in XX. inv XX.
            apply eq_sym.
            apply compose_meminjI_None. right.  
            exists b2, d1; split. apply join_incr_left. assumption.          
            remember (extern_of nu23 b2) as t.
            destruct t; apply eq_sym in Heqt.
               destruct p as [b3 d2].
               apply extern_in_all in Heqt. apply inc23 in Heqt.
               rewrite Heqt in J23'. discriminate.
            unfold join. rewrite Heqt, J23'.
              destruct (local_of nu23 b2); trivial.
          (*case extern_of nu12 b1 = None*)
            destruct (compose_meminjD_None _ _ _ Heqq); clear Heqq.
            (*case local_of nu12 b1 = None*)
              clear inc12.
              destruct (compose_meminjD_None _ _ _ H); clear H.
              (*case removeUndefs ... = None*)
                apply eq_sym.
                apply compose_meminjI_None. left.
                apply joinI_None. assumption.
                rewrite H0. apply H1.
              (*case removeUndefs ... = Some*)
                destruct H1 as [b2 [d1 [R J23']]]. 
                apply eq_sym.
                apply compose_meminjI_None. right.
                exists b2, d1; split.
                  unfold join. rewrite Heqw. rewrite H0. apply R.
                assert (as_inj nu23 b2 = None).
                  apply (inject_incr_inv _ _ inc23 _ J23').
                destruct (joinD_None _ _ _ H).
                unfold join. rewrite H1, H2. apply J23'.
            (*case local_of nu12 b1 = Some*)
              destruct H0 as [b2 [d1 [Loc1 Loc2]]].
              apply eq_sym.
              apply compose_meminjI_None. left.
              destruct (disjoint_extern_local _ WDnu12 b1).
                unfold join. rewrite H0, Loc1. trivial.
              rewrite H0 in Loc1. inv Loc1.
split; trivial.
assert (GOAL2: extern_incr nu12
  (convertL nu12 (removeUndefs (as_inj nu12) (as_inj nu') prej12')
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23'))).
  split. rewrite convertL_extern. apply join_incr_left.
  split. rewrite convertL_local. trivial.
  split. rewrite convertL_extBlocksSrc. intuition.
  split. rewrite convertL_extBlocksTgt. intuition. 
  split. rewrite convertL_locBlocksSrc. trivial.
  split. rewrite convertL_locBlocksTgt. trivial. 
  split. rewrite convertL_pubBlocksSrc. trivial.
  split. rewrite convertL_pubBlocksTgt. trivial.
  split. rewrite convertL_frgnBlocksSrc. trivial. 
  rewrite convertL_frgnBlocksTgt. trivial. 
split. rewrite <- Heqj12' in GOAL2. assumption.
assert (GOAL3: (extern_incr nu23
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))))).
  clear GOAL1 GOAL2 ConvertL_J12' ConvertR_J23'.
  split. rewrite convertR_extern. apply join_incr_left.
  split. rewrite convertR_local. trivial.
  split. rewrite convertR_extBlocksSrc. intuition.
  split. rewrite convertR_extBlocksTgt. intuition. 
  split. rewrite convertR_locBlocksSrc. trivial.
  split. rewrite convertR_locBlocksTgt. trivial. 
  split. rewrite convertR_pubBlocksSrc. trivial.
  split. rewrite convertR_pubBlocksTgt. trivial.
  split. rewrite convertR_frgnBlocksSrc. trivial.
  rewrite convertR_frgnBlocksTgt. trivial. 
split. assumption.
assert (GOAL4: sm_inject_separated nu12
  (convertL nu12 j12'
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23')) m1 m2).
  split. rewrite ConvertL_J12'; clear ConvertL_J12' GOAL1 ConvertR_J23'.
         intros.
         destruct (sep12 _ _ _ H H0) as [NV1 NV2].
         split.
           remember (DomSrc nu12 b1) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV12 in Heqq. contradiction.
         remember (DomTgt nu12 b2) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV12 in Heqq. contradiction.
  rewrite convertL_DomSrc, convertL_DomTgt.
  split; intros; rewrite H in H0; simpl in *.
         rewrite andb_true_r in H0.
         eapply SMInjSep. apply H. apply H0.
       unfold FreshDom in H0.
           remember (j23' b2) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p.
              remember (as_inj nu23 b2) as w.
              destruct w; apply eq_sym in Heqw. inv H0.
              eapply sep23; eassumption.
           inv H0.
split. assumption.
assert (GOAL5: sm_inject_separated nu23
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))) m2 m3).
  split. rewrite ConvertR_J23'; clear ConvertL_J12' GOAL1 ConvertR_J23'. 
         intros.
         destruct (sep23 _ _ _ H H0) as [NV1 NV2].
         split.
           remember (DomSrc nu23 b1) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV23 in Heqq. contradiction.
         remember (DomTgt nu23 b2) as q.
           destruct q; trivial; apply eq_sym in Heqq.
           apply SMV23 in Heqq. contradiction.
  rewrite convertR_DomSrc, convertR_DomTgt.
  split; intros; rewrite H in H0; simpl in H0.
         unfold FreshDom in H0.
           remember (j23' b1) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p.
              remember (as_inj nu23 b1) as w.
              destruct w; apply eq_sym in Heqw. inv H0.
              eapply sep23; eassumption.
           inv H0.
           rewrite andb_true_r in H0.
           eapply SMInjSep. apply H. apply H0.
split. assumption.
assert (GOAL6: sm_valid
  (convertL nu12 j12'
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23')) m1' m2').
  split. unfold DOM. rewrite convertL_DomSrc.
         clear ConvertL_J12' GOAL1 ConvertR_J23'. 
         intros.
         remember (DomSrc nu12 b1) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd1. 
           eapply SMV12. apply Heqd.
         rewrite andb_true_r in H.
           eapply SMvalNu'. apply H.
  unfold RNG. rewrite convertL_DomTgt.
         intros.
         remember (DomTgt nu12 b2) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd2. 
           eapply SMV12. apply Heqd.
         unfold FreshDom in H.
           remember (j23' b2) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p. 
              remember (as_inj nu23 b2) as w.
              destruct w; apply eq_sym in Heqw. inv H.
              apply (VBj23' _ _ _ Heqq).
            inv H.
split. assumption.
split. (*This is GOAL7: sm_valid
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b))) m2' m3').*)
  split. unfold DOM. rewrite convertR_DomSrc.
         clear ConvertL_J12' GOAL1 ConvertR_J23'. 
         intros.
         remember (DomSrc nu23 b1) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd2. 
           eapply SMV23. apply Heqd.
         unfold FreshDom in H.
           remember (j23' b1) as q.
           destruct q; apply eq_sym in Heqq.
              destruct p. 
              remember (as_inj nu23 b1) as w.
              destruct w; apply eq_sym in Heqw. inv H.
              apply (VBj23' _ _ _ Heqq). 
            inv H.
  unfold RNG. rewrite convertR_DomTgt.
         intros.
         remember (DomTgt nu23 b2) as d.
         destruct d; apply eq_sym in Heqd; simpl in H.
           apply Fwd3. 
           eapply SMV23. apply Heqd.
         rewrite andb_true_r in H.
           eapply SMvalNu'. apply H.
split. (*Glue invariant*) 
  split. (*This is GOAL8: SM_wd
  (convertL nu12 f
     (fun b : block => DomSrc nu' b && negb (DomSrc nu12 b))
     (FreshDom (as_inj nu23) j23'))).*)
   clear ConvertL_J12' ConvertR_J23'. 
   split. 
   (*1/8*) rewrite convertL_locBlocksSrc, convertL_extBlocksSrc.
           intros. unfold DomSrc.
           specialize (disjoint_extern_local_Src _ WDnu12 b); intros.
           remember (locBlocksSrc nu12 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             rewrite H. right. simpl. rewrite andb_false_r. trivial.
           left; trivial.
   (*2/8*) rewrite convertL_locBlocksTgt, convertL_extBlocksTgt.
           intros. 
           specialize (disjoint_extern_local_Tgt _ WDnu12 b); intros.
           remember (locBlocksTgt nu12 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             rewrite H. right. rewrite orb_false_l.
             unfold FreshDom.
             remember (j23' b) as q.
             destruct q; trivial; apply eq_sym in Heqq.
             destruct p. 
             remember (as_inj nu23 b) as t.
             destruct t; trivial; apply eq_sym in Heqt.
             assert (DomSrc nu23 b = false).
                eapply GOAL5. apply Heqt.
                destruct (joinD_None _ _ _ Heqt).
                apply joinI. rewrite convertR_extern, convertR_local.
                unfold join; simpl. rewrite H0, H1. left; eassumption.
             unfold DomSrc in H0. rewrite GlueLoc in Heqd. rewrite Heqd in H0.
               discriminate.
           left; trivial.
   (*3/8*) rewrite convertL_local, convertL_locBlocksSrc, convertL_locBlocksTgt.
           apply WDnu12. 
   (*4/8*) rewrite convertL_extern, convertL_extBlocksSrc, convertL_extBlocksTgt.
           intros. 
            destruct (joinD_Some _ _ _ _ _ H); clear H.
              destruct (extern_DomRng _ WDnu12 _ _ _ H0) as [? ?].
              intuition.
            destruct H0.
            remember (local_of nu12 b1) as d. 
            destruct d; apply eq_sym in Heqd. inv H0.
              destruct (sep12 b1 b2 z); trivial.
                apply joinI_None; trivial.
            remember (DomSrc nu12 b1) as q.
            destruct q; apply eq_sym in Heqq.
              exfalso. apply H1. apply SMV12. apply Heqq.
            remember (DomTgt nu12 b2) as w.
            destruct w; apply eq_sym in Heqw.
              exfalso. apply H2. apply SMV12. apply Heqw.
            simpl. 
            unfold DomSrc in Heqq. apply orb_false_iff in Heqq. destruct Heqq.
            unfold DomTgt in Heqw. apply orb_false_iff in Heqw. destruct Heqw.
            rewrite H4, H6; simpl.
            rewrite andb_true_r. clear GOAL1.
            rewrite GlueLoc, GlueExt in *.
            remember (as_inj nu23 b2) as ww.
            destruct ww; apply eq_sym in Heqww.
               destruct p.
               destruct (as_inj_DomRng _ _ _ _ Heqww WDnu23). 
               unfold DomSrc in H7. rewrite H5, H6 in H7. discriminate. 
            remember (as_inj nu' b1) as qq.
            destruct qq; apply eq_sym in Heqqq.
               destruct p.
               assert (DomSrc nu' b1 = true).
                  eapply as_inj_DomRng. eassumption.
                  assumption.
               rewrite H7. split; trivial.
               rewrite ID in Heqqq.
               destruct (compose_meminjD_Some _ _ _ _ _ Heqqq)
                  as [b22 [dd1 [dd2 [FF [JJ DD]]]]]; clear Heqqq.
               clear ID. rewrite FF in H0. inv H0.
               unfold FreshDom. rewrite JJ, Heqww. trivial.
            rewrite Heqj12' in H0.
            unfold removeUndefs in H0. rewrite Heqqq in H0.
               assert (AI: as_inj nu12 b1 = None). apply joinI_None; eassumption.
               rewrite AI in H0. inv H0.
   (*5/8*) rewrite convertL_pubBlocksSrc, convertL_pubBlocksTgt, convertL_local.
            apply WDnu12.
   (*6/8*) rewrite convertL_frgnBlocksSrc, convertL_frgnBlocksTgt.
            rewrite convertL_extern; trivial. intros. 
            destruct (frgnSrcAx _ WDnu12 _ H) as [b2 [d [EXT FT]]]. 
             unfold join. rewrite EXT. exists b2, d. split; trivial.
   (*7/8*) rewrite convertL_pubBlocksTgt, convertL_locBlocksTgt.
           apply WDnu12.
   (*8/8*) rewrite convertL_frgnBlocksTgt, convertL_extBlocksTgt.
           intros. rewrite (frgnBlocksExternTgt _ WDnu12 _ H). trivial.
split. (*This is GOAL9: SM_wd
  (convertR nu23 j23' (FreshDom (as_inj nu23) j23')
     (fun b : block => DomTgt nu' b && negb (DomTgt nu23 b)))).*)
   clear ConvertL_J12' ConvertR_J23'.
   split.
   (*1/8*) rewrite convertR_locBlocksSrc, convertR_extBlocksSrc.
          intros.
           specialize (disjoint_extern_local_Src _ WDnu23 b); intros.
           remember (locBlocksSrc nu23 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             rewrite H. right. rewrite orb_false_l.
             unfold FreshDom.
             remember (j23' b) as q.
             destruct q; trivial; apply eq_sym in Heqq.
             destruct p. 
             remember (as_inj nu23 b) as t.
             destruct t; trivial; apply eq_sym in Heqt.
             assert (DomSrc nu23 b = false).
                eapply GOAL5. apply Heqt.
                destruct (joinD_None _ _ _ Heqt).
                apply joinI. rewrite convertR_extern, convertR_local.
                unfold join; simpl. rewrite H0, H1. left; eassumption.
             unfold DomSrc in H0. rewrite Heqd, H in H0.
               discriminate.
           left; trivial.
   (*2/8*) rewrite convertR_locBlocksTgt, convertR_extBlocksTgt.
           intros. specialize (disjoint_extern_local_Tgt _ WDnu23 b). intros.
           remember (locBlocksTgt nu23 b) as d.
           destruct d; apply eq_sym in Heqd.
             destruct H. inv H.
             right; rewrite H. simpl.
             assert (DomTgt nu23 b = true).
               unfold DomTgt; rewrite Heqd. trivial.
             rewrite H0; simpl. rewrite andb_false_r. trivial.
           left; trivial.
   (*3/8*) rewrite convertR_locBlocksTgt, convertR_locBlocksSrc, convertR_local.
           apply WDnu23. 
   (*4/8*) rewrite convertR_extBlocksTgt, convertR_extBlocksSrc, convertR_extern.
           intros. 
           destruct (joinD_Some _ _ _ _ _ H) as [EXT23 | [EXT23 LOC23]]; clear H.
              destruct (extern_DomRng _ WDnu23 _ _ _ EXT23).
              rewrite H, H0; simpl. split; trivial.
           remember ( local_of nu23 b1) as q.
           destruct q; try inv LOC23; apply eq_sym in Heqq.
           assert (AI: as_inj nu23 b1 = None). 
              apply joinI_None; assumption.
           destruct GOAL5 as [? _].
           destruct (H b1 b2 z AI); clear H.
              apply joinI. rewrite convertR_extern, convertR_local.
              unfold join. rewrite EXT23, Heqq. left; trivial.
           unfold FreshDom. rewrite LOC23, AI, H1; simpl.
           assert (DomTgt nu' b2 = true).
             destruct (mkiVal4 _ _ _ LOC23) as [[MK _] | [MK | MK]].
             (*1/3*) congruence. 
             (*2/3*) destruct MK as [? [? ?]].
                   eapply as_inj_DomRng; eassumption.
             (*3/3*) destruct MK as [mm [? [? ?]]].
                   eapply as_inj_DomRng; eassumption.
           rewrite H. intuition.  
   (*5/8*) rewrite convertR_pubBlocksTgt, convertR_pubBlocksSrc, convertR_local.
           apply WDnu23. 
   (*6/8*) rewrite convertR_frgnBlocksTgt, convertR_frgnBlocksSrc.
           rewrite convertR_extern; trivial. intros.
           destruct (frgnSrcAx _ WDnu23 _ H) as [b2 [d [EXT FT]]].
           exists b2, d; unfold join. rewrite EXT; split; trivial.
   (*7/8*) rewrite convertR_locBlocksTgt, convertR_pubBlocksTgt.
            apply WDnu23.
   (*8/8*) rewrite convertR_frgnBlocksTgt, convertR_extBlocksTgt.
            intros. rewrite (frgnBlocksExternTgt _ WDnu23 _ H); trivial.
  split. assumption. 
  split. rewrite GlueExt. trivial. 
  split. assumption. 
  intros. apply GlueFrgn; trivial.
split. intros. (*Proof of NORM*) clear GOAL1 ConvertR_J23'.
   subst.
   destruct (joinD_Some _ _ _ _ _ H) as [EXT | [EXT LOC]]; clear H.
      destruct (Norm12 _ _ _ EXT) as [b3 [d2 EXT2]].
      exists b3, d2. apply joinI; left. assumption. 
   remember (local_of nu12 b1) as q.
   destruct q; apply eq_sym in Heqq. inv LOC.
   assert (AsInj12: as_inj nu12 b1 = None).
     apply joinI_None; assumption.
   destruct (sep12 _ _ _ AsInj12 LOC).
   remember (extern_of nu23 b2) as d.
   destruct d; apply eq_sym in Heqd.
     destruct p. exfalso. apply H0. eapply VBj23_1. apply extern_in_all; eassumption. 
   remember (local_of nu23 b2) as w.
   destruct w; apply eq_sym in Heqw.
     destruct p. exfalso. apply H0. eapply VBj23_1. apply local_in_all; eassumption.
   unfold join. rewrite Heqd, Heqw.
   unfold removeUndefs in LOC. rewrite AsInj12 in LOC.
   remember (as_inj nu' b1) as t.
   destruct t; try inv LOC. destruct p; apply eq_sym in Heqt. 
   remember (j23' b2) as u.
   destruct u; apply eq_sym in Hequ.
     destruct p. exists b0, z0; trivial.  
   destruct (mkiVal3 _ _ _ H2) as [[X _] | [X | X]]; clear mkiVal3.
      rewrite X in AsInj12. discriminate.
      destruct X as [B1 [B2 [D2 [VB1 VB2]]]].
      exfalso. destruct (mkiVal5 _ VB2 Hequ) as [[Ya Yb] | [[Ya Yb] | [mm [Ya Yb]]]].
        subst. clear - Ya. unfold Mem.valid_block in Ya. xomega.
        subst. rewrite Heqt in Yb. discriminate.
        subst. clear - Ya. rewrite Pos.add_comm in Ya. apply eq_sym in Ya.
                    eapply Pos.add_no_neutral. apply Ya.
      destruct X as [m [B1 [B2 [D1 [VB1 VB2]]]]].
      exfalso. destruct (mkiVal5 _ VB2 Hequ) as [[Ya Yb] | [[Ya Yb] | [mm [Ya Yb]]]].
        subst. clear - Ya. unfold Mem.valid_block in Ya. xomega.
        subst.  clear - Ya. rewrite Pos.add_comm in Ya. 
                    eapply Pos.add_no_neutral. apply Ya.
        subst. assert (mm=m). clear - Ya. xomega. subst.
               rewrite Heqt in Yb. discriminate.      
repeat (split; trivial).
=======*)

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
Lemma meminj_no_overlap_inject_incr: 
   forall j m (NOV: Mem.meminj_no_overlap j m) k (K:inject_incr k j),
  Mem.meminj_no_overlap k m.
Proof. intros.
  intros b; intros.
  apply K in H0. apply K in H1.
  eapply (NOV _ _ _ _ _ _ _ _  H H0 H1 H2 H3).
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

(*<<<<<<< HEAD:core/interpolation_II.v
Definition ContentsMap_EFF_FUN  (NB2' b:block) : ZMap.t memval.
Proof.
destruct (plt b NB2').
  apply (CM_block_EFF_existsT b).
apply (ZMap.init Undef).
Defined.

Lemma ContentsMap_EFF_existsT: 
      forall (NB2':block) , 
      { M : PMap.t (ZMap.t memval) |
        fst M = ZMap.init Undef /\
        forall b, PMap.get b M =
           ContentsMap_EFF_FUN NB2' b}.
Proof. intros.
  apply (pmap_construct_c _ (ContentsMap_EFF_FUN NB2') 
              NB2' (ZMap.init Undef)). 
    intros. unfold ContentsMap_EFF_FUN. simpl.
    remember (plt n NB2') as d.
    destruct d; clear Heqd; trivial.   
      exfalso. xomega.
Qed.

Definition mkEFF 
            (NB2':block)
            (Hyp1: (Mem.nextblock m2 <= NB2')%positive)
            (Hyp2: forall (b1 b2 : block) (delta : Z),
                       j12' b1 = Some (b2, delta) -> (b2 < NB2')%positive)
           : Mem.mem'.
Proof.
destruct (mkAccessMap_EFF_existsT NB2' Hyp1 Hyp2) as [AM [ADefault PAM]].
destruct (ContentsMap_EFF_existsT NB2') as [CM [CDefault PCM]].  
eapply Mem.mkmem with (nextblock:=NB2')
                      (mem_access:=AM)
                      (mem_contents:=CM).
  (*access_max*)
  intros. rewrite PAM. unfold AccessMap_EFF_FUN.
     destruct (plt b (Mem.nextblock m2)).
     (*valid_block m2 b*)
        destruct (locBlocksSrc nu23 b).
          destruct (pubBlocksSrc nu23 b).
            destruct (source (local_of nu12) m1 b ofs).
              destruct p0.
              destruct (pubBlocksSrc nu12 b0). apply m1'. apply m2.
            apply m2.
          apply m2.               
        destruct (source (as_inj nu12) m1 b ofs). 
            destruct p0. apply m1'.
        destruct (j23 b). destruct p0. reflexivity. apply m2.
     (*invalid_block m2 b*)
        destruct (source j12' m1' b ofs).
          destruct p. apply m1'. 
        reflexivity.
  (*nextblock_noaccess*)
    intros. rewrite PAM.
    unfold AccessMap_EFF_FUN.
    destruct (plt b (Mem.nextblock m2)).
      exfalso. apply H; clear - Hyp1 p. xomega.
    remember (source j12' m1' b ofs) as src.
    destruct src; trivial.
      destruct p.
      exfalso. apply H. clear - Heqsrc Hyp2.
      apply source_SomeE in Heqsrc.
      destruct Heqsrc as [b1 [delta [ofs1
          [PBO [Bounds [J1 [P1 Off2]]]]]]]; subst.
        apply (Hyp2 _ _ _ J1).
  (*contents_default*)
    intros. 
    rewrite PCM; clear PCM.
    unfold ContentsMap_EFF_FUN.
    destruct (plt b NB2').
     remember (CM_block_EFF_existsT b). 
     destruct s. apply a.
    reflexivity.
Defined.

Lemma mkEff_nextblock: forall N Hyp1 Hyp2,
         Mem.nextblock (mkEFF N Hyp1 Hyp2) = N.
Proof. intros. unfold mkEFF. 
  remember (mkAccessMap_EFF_existsT N Hyp1 Hyp2).
  destruct s as [X1 X2].
  destruct X2. simpl in *.
  remember (ContentsMap_EFF_existsT N).
  destruct s as [Y1 Y2].
  destruct Y2; simpl in *. reflexivity.
=======*)



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


Lemma load_eq_unchanged_on (P : block -> Z -> Prop) m m' 
         (U: Mem.unchanged_on P m m') b (B: Mem.valid_block m b)
         chunk ofs (OFS: forall i : Z, ofs <= i < ofs + size_chunk chunk -> P b i):
  Mem.load chunk m b ofs = Mem.load chunk m' b ofs.
Proof. intros.
Transparent Mem.load.
    unfold Mem.load.
    destruct U.
    destruct (Mem.valid_access_dec m chunk b ofs Readable).
    { destruct (Mem.valid_access_dec m' chunk b ofs Readable).
         erewrite Mem.getN_exten. reflexivity.
         rewrite <- size_chunk_conv.
         intros. rewrite unchanged_on_contents. trivial. apply (OFS _ H).
       apply v. trivial.
      elim n; clear n unchanged_on_contents.
        unfold Mem.valid_access, Mem.range_perm in *.
        destruct v; split; trivial; intros. apply unchanged_on_perm; trivial. apply (OFS _ H1).
        apply H; trivial.
    }

   { destruct (Mem.valid_access_dec m' chunk b ofs Readable); trivial.
      elim n; clear n unchanged_on_contents.
        unfold Mem.valid_access, Mem.range_perm in *.
        destruct v; split; trivial; intros. apply unchanged_on_perm; trivial. apply (OFS _ H1).
        apply H; trivial. }
Opaque Mem.load.
Qed.

Lemma RDOnly_fwd_Dperm m1 m1' B b ofs:
      forall (H_fwd : RDOnly_fwd m1 m1' B)
             (HeqisB : B b = true)
             (NPerm12 : forall z, ~ Mem.perm m1 b z Max Writable),
     Mem.perm m1 b ofs Cur Readable = Mem.perm m1' b ofs Cur Readable.
Proof. intros. apply prop_ext.
       destruct (H_fwd _ HeqisB 1 ofs) as [_ P].
                     intros. assert (i=0) by omega. subst i; rewrite Zplus_0_r. apply NPerm12.
       specialize (P 0); rewrite Zplus_0_r in P. apply P. omega. 
Qed. 

Lemma RDOnly_fwd_Dcont' m1 m1' B b ofs:
      forall (H_fwd : RDOnly_fwd m1 m1' B)
             (HeqisB : B b = true)
             (P1: Mem.perm m1' b ofs Cur Readable)
             (NPerm12 : forall z, ~ Mem.perm m1 b z Max Writable),
     ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m1) !! b.
Proof. intros.
        destruct (H_fwd _ HeqisB 1 ofs) as [LD1 _].
                     intros. assert (i=0) by omega. subst i; rewrite Zplus_0_r. apply NPerm12.
                   destruct (Mem.range_perm_loadbytes m1' b ofs 1) as [bytes HBytes].
                     red; intros. assert (ofs0=ofs) by omega. subst ofs0. assumption.
                   rewrite HBytes in *. symmetry in LD1.
                   specialize (Mem.loadbytes_length _ _ _ _ _ HBytes); intros LEN.
                   assert (NN: nat_of_Z 1 = 1%nat). simpl; xomega. rewrite NN in *; clear NN.
                   destruct bytes; simpl in LEN; try omega.
                   destruct bytes; simpl in LEN; try omega.
                   apply loadbytes_D in HBytes. simpl in HBytes; destruct HBytes.
                   inversion H0; clear H0. rewrite <- H2; clear H2.
                   apply loadbytes_D in LD1. simpl in LD1; destruct LD1.
                   inversion H1; clear H1. trivial.
Qed.

Lemma RDOnly_fwd_Dcont m1 m1' B b ofs:
      forall (H_fwd : RDOnly_fwd m1 m1' B)
             (HeqisB : B b = true)
             (P1: Mem.perm m1 b ofs Cur Readable)
             (NPerm12 : forall z, ~ Mem.perm m1 b z Max Writable),
     ZMap.get ofs (Mem.mem_contents m1') !! b = ZMap.get ofs (Mem.mem_contents m1) !! b.
Proof. intros. eapply RDOnly_fwd_Dcont'; try eassumption.
  erewrite <- RDOnly_fwd_Dperm; eauto.
Qed.

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
         (*Pure: pure_comp_ext nu12 nu23 m1 m2*)
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
         B (RDOnly12: RDOnly_inj m1 m2 nu12 B) (RDOnly23: RDOnly_inj m2 m3 nu23 B)
           (RDOnly_fwd1: RDOnly_fwd m1 m1' B) (RDOnly_fwd3: RDOnly_fwd m3 m3' B)
           (BSep : forall (b1 b2 : block) (d : Z),
                 as_inj (compose_sm nu12 nu23) b1 = None ->
                 as_inj nu' b1 = Some (b2, d) -> B b2 = false)
         (full: full_ext nu12 nu23),
  exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\ 
                                          extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                                          (*pure_comp_ext nu12' nu23' m1' m2' /\*)
                                          Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\ RDOnly_fwd m2 m2' B /\
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
                                          (*(forall b1 b2 d1, as_inj nu12' b1 = Some(b2,d1) -> 
                                                            as_inj nu12 b1 = Some(b2,d1) \/
                                                            exists b3 d, as_inj nu' b1 = Some(b3,d)) /\
                                          (forall b2 b3 d2, as_inj nu23' b2 = Some(b3,d2) -> 
                                                            as_inj nu23 b2 = Some(b3,d2) \/
                                                            exists b1 d, as_inj nu' b1 = Some(b3,d)).*)
                         
                                          (forall b1 b2 d, extern_of nu12' b1 = Some (b2, d) ->
                                                           extern_of nu12 b1 = Some (b2, d) \/
                                                           extern_of nu12 b1 = None /\
                                                           exists b3 d2, extern_of nu' b1 = Some (b3, d2)) /\
                                          (forall b2 b3 d2, extern_of nu23' b2 = Some (b3, d2) ->
                                                            extern_of nu23 b2 = Some (b3, d2) \/
                                               extern_of nu23 b2 = None /\
                                                            exists b1 d, extern_of nu12' b1 = Some (b2, d)).

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
        * Construct the injections            *
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
       
       (************************************************
        * Proving some properties of my injections     *
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

        (***************************************
        * Construct the memory                *
        ***************************************)
       assert (finite12: mi_mappedblocks (as_inj nu12) m2).
       { unfold mi_mappedblocks. intros. apply SMV12. unfold RNG. 
         destruct (as_inj_DomRng _ _ _ _ H SMWD12); auto. }
       
       assert (finite12': mi_mappedblocks' j12' (mem_add_nb m1' m2)).
       { unfold mi_mappedblocks'. intros. subst j12' nu12'.
         unfold as_inj, join in H. rewrite ext_change_ext, loc_change_ext in H.
         inversion Heqoutput; subst j'. 
         unfold add_inj, filter_id, shiftT in H.
         destruct (j b) eqn:jmap.
         + destruct p; inversion H; subst b' delta j.
           eapply SMWD12 in jmap; destruct jmap.
           eapply Pos.lt_le_trans. apply SMV12. unfold RNG, DomTgt.
           rewrite H1; apply orb_true_r. 
           unfold mem_add_nb; xomega.
         + destruct (l' b) eqn:lmap'.
           - inversion H. 
             assert (Plt b (Mem.nextblock m1')).
             { destruct p. subst l'; apply WDnu' in lmap'.
               destruct lmap'. apply SMvalNu'.
               unfold DOM, DomSrc. rewrite H0; apply orb_true_r. }
             unfold mem_add_nb; xomega.
           - unfold mem_add_nb; eapply Pos.lt_le_trans.
             apply SMV12. unfold RNG, DomTgt.
             apply SMWD12 in H; destruct H.
             rewrite H0; auto.
             xomega. }
       
       assert (INCR: inject_incr (as_inj nu12) j12').
       { subst j12'; apply extern_incr_as_inj; auto. }
         
       destruct (mem_interpolation 
                   nu12 nu23 j12' m1 m1' m2 m3 B
                   (finite12: mi_mappedblocks (as_inj nu12) m2)
                   (finite12': mi_mappedblocks' j12' (mem_add_nb m1' m2))
                   (SMWD12: SM_wd nu12)
                   (INCR: inject_incr (as_inj nu12) j12')) 
                as [m2' [property_cont [property_acc property_nb]]].
       clear finite12 finite12' INCR.
       exists m2', nu12', nu23'.

       (************************************************
        * Proving some properties of my memory m2'     *
        ************************************************)

       (* Mem.unchanged_on private m2 *)
       assert (UnchPrivSrc12 : Mem.unchanged_on
                   (fun (b : block) (_ : Z) =>
                      locBlocksSrc nu23 b = true /\ pubBlocksSrc nu23 b = false) m2 m2').
       { constructor. 
         + intros b ofs k0 p [locS pubS] bval; unfold Mem.perm.
           rewrite property_acc; unfold mem_add_acc.
           rewrite locS, pubS.
           destruct (valid_dec m2 b); try solve[contradict bval;trivial].
           (*destruct (Mem.perm_dec m2 b ofs Max Writable).
             split; auto.*)
           destruct (B b). split; auto.
           split; auto.
         + intros b ofs [locS pubS] mperm.
           rewrite property_cont; unfold mem_add_cont.
           rewrite locS, pubS.
           destruct (valid_dec m2 b); try solve[trivial].
           { (*destruct (Mem.perm_dec m2 b ofs Max Writable); trivial.*)
             (*remember (B b) as d. symmetry in Heqd.
             destruct d; simpl; trivial.
             destruct (RDOnly12 _ Heqd) as [EXTb _].
             assert (LT: locBlocksTgt nu12 b = false). eapply extern_DomRng'; eassumption.
             destruct GlueInv as [GL _]; rewrite GL in LT.
             rewrite LT in locS; discriminate.*)
             destruct (B b); trivial. }
           (*Invalid case*) apply Mem.perm_valid_block in mperm; contradiction.
       }
       (*Mem.unchanged_on local_out_of_reach 12*)
       assert (UnchLOOR12: Mem.unchanged_on (local_out_of_reach nu12 m1) m2 m2').
       { unfold local_out_of_reach.
         constructor. 
         + intros b ofs k0 p [locT mapcondition] bval; unfold Mem.perm.
           rewrite property_acc; 
                 unfold mem_add_acc.
           destruct (valid_dec m2 b); try solve[contradict bval;trivial].
           (*destruct (Mem.perm_dec m2 b ofs Max Writable). 2: split; auto.*)
           destruct (B b). split; auto.
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
           rewrite property_cont; 
                 unfold mem_add_cont.
           destruct (valid_dec m2 b).
           - (*destruct (Mem.perm_dec m2 b ofs Max Writable); trivial. rename p into PWR.*)
             destruct (B b); trivial.
             (*remember (B b) as d. symmetry in Heqd.
             destruct d; simpl; trivial.
             { destruct (RDOnly12 _ Heqd) as [EXTb _].
               assert (LT: locBlocksTgt nu12 b = false). eapply extern_DomRng'; eassumption.
               rewrite LT in locT; discriminate. }             *)
             assert (locS: locBlocksSrc nu23 b = true ) by
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
       (* mem_forward m2 m2' *)
       assert (Fwd2: mem_forward m2 m2').
       { assert (FwdCore: forall b, Mem.valid_block m2 b ->
                    Mem.valid_block m2' b /\
                   (forall ofs p, Mem.perm m2' b ofs Max p -> Mem.perm m2 b ofs Max p)).
         { intros.
           split. unfold Mem.valid_block in *.
                  rewrite property_nb.
                  unfold mem_add_nb.
                  xomega.
           intros ofs per. 
             unfold Mem.perm. rewrite property_acc; unfold mem_add_acc.
             destruct (valid_dec m2 b); try contradiction.
             (*destruct (Mem.perm_dec m2 b ofs Max Writable).*)
             destruct (B b). auto.
             { (*rename p into P.*)
               destruct (locBlocksSrc nu23 b) eqn: loc23.
               destruct (pubBlocksSrc nu23 b) eqn: pub23; trivial.
               destruct (source (local_of nu12) m1 b ofs) eqn:sour; trivial; destruct p.
               destruct (pubBlocksSrc nu12 b0) eqn: pub12; trivial.
               symmetry in sour. apply source_SomeE in sour.
               destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
               subst ofs; intros H0. eapply MInj12. apply local_in_all; eauto.
               inversion invertible; clear invertible. subst b0 z.
               destruct (Fwd1 _ leq) as [VB' Perms1 (*FwdMax1]*)].
               eapply Perms1. assumption.
           
               destruct (source (as_inj nu12) m1 b ofs) eqn:sour;
                 try solve[destruct (as_inj nu23 b); intros HH;try destruct p; trivial; inversion HH].
               destruct p.
               intros H0.
               symmetry in sour. apply source_SomeE in sour.
               destruct sour as [b1 [delta' [ofs1 [invertible [leq [mapj [mperm ofs_add]]]]]]].
               subst ofs; eapply MInj12; eauto.
               inversion invertible; clear invertible. subst b0 z.
               destruct (Fwd1 _ leq) as [VB' Perms1 (*FwdMax1]*)].
               eapply Perms1. assumption. }
             (*{ intros; trivial. }*)
         }
         red; intros. destruct (FwdCore _ H) as [FwdVB FWDPerm]; clear FwdCore.
          split; trivial.
          (*readonly-part of mem_forward
          (*Santiago: this is the goal we need to prove, and some initial steps.
              An alternative to do*)
          red; intros.
          assert (Perms: forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
                   forall k p, Mem.perm m2 b ofs' k p <-> Mem.perm m2' b ofs' k p).
            intros. unfold Mem.perm. rewrite property_acc. clear property_cont property_acc.
            unfold mem_add_acc.
            destruct (valid_dec m2 b); try contradiction. clear v.
            destruct (Mem.perm_dec m2 b ofs' Max Writable).
               elim (NWR _ H0); trivial.
            split; intros; trivial.
          split; trivial. 
          specialize (property_cont b). clear property_acc. (*; specialize (property_acc b).*)
             Transparent Mem.load. unfold Mem.load.
               destruct (Mem.valid_access_dec m2 chunk b ofs Readable).
               Focus 2. destruct (Mem.valid_access_dec m2' chunk b ofs Readable); trivial.
                        elim n; clear n. destruct v. split; trivial.
                        red; intros. specialize (H0 _ H2).
                        eapply (Perms _ H2); trivial. 
               destruct (Mem.valid_access_dec m2' chunk b ofs Readable). 
                 { f_equal. f_equal. apply Mem.getN_exten. rewrite <- size_chunk_conv; intros.
                   rewrite property_cont; clear property_cont. unfold mem_add_cont.
                   destruct (valid_dec m2 b); try contradiction. clear v1.
                   specialize (NWR _ H0).
                   destruct (Mem.perm_dec m2 b i Max Writable); try contradiction. trivial.
                 }
                 { elim n; clear n. destruct v. split; trivial.
                        red; intros. apply (Perms _ H2).
                        apply (H0 _ H2). }
             Opaque Mem.load.*)
       }

       assert (RDOnly_fwd2: RDOnly_fwd m2 m2' B).
         { red; intros. red; intros.
           destruct (RDOnly12 _ Hb) as [Map12 [J12b Perm12]].
           destruct (RDOnly23 _ Hb) as [Map23 [J23b Perm23]].
           destruct (RDOnly_fwd1 _ Hb n ofs) as [LD1 Perm1]. 
              intros. apply Perm12. (*
           destruct (RDOnly_fwd3 _ Hb n ofs) as [LD3 Perm3].
              intros. apply Perm23.*)
           assert (VB2: Mem.valid_block m2 b).
             eapply (Mem.valid_block_inject_1 (as_inj nu23)). eapply extern_in_all; eassumption. eassumption.
           split.
           { remember (Mem.loadbytes m2' b ofs n) as d; symmetry in Heqd.
             destruct d.
             { apply loadbytes_D in Heqd; destruct Heqd as [RP2' L].
               assert (RP2: Mem.range_perm m2 b ofs (ofs + n) Cur Readable).
                 red; intros. specialize (RP2' _ H). unfold Mem.perm in RP2'.
                 rewrite property_acc in RP2'. unfold mem_add_acc in RP2'.
                 rewrite Hb in RP2'. destruct (valid_dec m2 b); try contradiction; trivial.
               destruct (Mem.range_perm_loadbytes _ _ _ _  RP2) as [l2 L2].
               rewrite L2.
               apply loadbytes_D in L2; destruct L2 as [_ L2].
               subst l l2; f_equal.
               apply Mem.getN_exten. intros. rewrite property_cont.
               unfold mem_add_cont. rewrite Hb. destruct (valid_dec m2 b); try contradiction; trivial. }
             { remember (Mem.loadbytes m2 b ofs n) as q; symmetry in Heqq.
               destruct q; trivial. 
               apply loadbytes_D in Heqq; destruct Heqq as [RP2 L2].
               assert (RP2': Mem.range_perm m2' b ofs (ofs + n) Cur Readable).
                 red; intros. specialize (RP2 _ H). unfold Mem.perm.
                 rewrite property_acc. unfold mem_add_acc.
                 rewrite Hb. destruct (valid_dec m2 b); try contradiction; trivial.
               destruct (Mem.range_perm_loadbytes _ _ _ _  RP2') as [l2 L2'].
               rewrite L2' in Heqd. discriminate.
             }
           }
           intros. unfold Mem.perm. rewrite property_acc; unfold mem_add_acc.
              destruct (valid_dec m2 b); try contradiction. rewrite Hb. split; auto.
    }
(*
   { destruct (Mem.valid_access_dec m' chunk b ofs Readable); trivial.
      elim n; clear n unchanged_on_contents.
        unfold Mem.valid_access, Mem.range_perm in *.
        destruct v; split; trivial; intros. apply unchanged_on_perm; trivial. apply (OFS _ H1).
        apply H; trivial. }


           intros. specialize (Perm1 _ H k0 p). specialize (Perm3 _ H k0 p). 
             unfold Mem.perm; rewrite property_acc. clear property_cont property_acc.
             unfold mem_add_acc. red in SMV12.
           apply extern_in_all in Map12.
           apply extern_in_all in Map23.
           assert (VB1: Mem.valid_block m1 b).
             eapply (Mem.valid_block_inject_1 (as_inj nu12)); eassumption.
           assert (VB2: Mem.valid_block m2 b).
             eapply (Mem.valid_block_inject_1 (as_inj nu23)); eassumption.
           assert (VB3: Mem.valid_block m3 b).
             eapply (Mem.valid_block_inject_2 (as_inj nu23)); eassumption.  
           destruct (valid_dec m2 b); try contradiction. clear v.
           rewrite Hb; split; auto. }*)
       
       (*(* pure_comp_ext nu12' nu23' m1' m2 *)
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
       }*)
       
       

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
       (*split.
       (* pure compositoin *)
       { exact Pure'. }*)
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
         - { intros b1 b2 delta ofs k0 per H H0.
             unfold Mem.perm; rewrite property_acc; 
             unfold mem_add_acc.
             (* New trying things*)
             unfold as_inj in H; apply joinD_Some in H; 
             destruct H as [extmap | [extNone locmap]].
             + subst nu12'; rewrite ext_change_ext in extmap.
               eapply MKI_Some12 in extmap; eauto. 
               destruct extmap as [jmap | [jmap [b2' [d' [lmap' [b2eq deltaeq]]]]]].
             - assert (Mem.valid_block m2 b2) by (subst j; auto_sm).
               destruct (valid_dec m2 b2); try solve[contradict n; auto]. clear v.
               (*destruct (Mem.perm_dec m2 b2 (ofs + delta) Max Writable). rename p into PW.*)
               remember (B b2) as isB; symmetry in HeqisB. 
               destruct isB.
               { subst j. apply extern_in_all in jmap.  
                 destruct (RDOnly12 _ HeqisB) as [AIb [AIunique Perm12]].
                   specialize (AIunique _ _ jmap). subst b2.
                   apply extern_in_all in AIb. rewrite jmap in AIb; inversion AIb. subst delta; clear AIb. 
                 eapply Mem.perm_inject; try eassumption.
                 destruct (RDOnly_fwd1 _ HeqisB 1 ofs) as [LDBeq PERMeq]; clear RDOnly_fwd1.
                   intros. apply Perm12.
                 specialize (PERMeq 0). rewrite Zplus_0_r in PERMeq.
                   apply PERMeq; trivial. omega. }
               assert (locF: locBlocksSrc nu23 b2 = false).
               { destruct GlueInv as [loc rest]; rewrite <- loc.
                 subst j; auto_sm. }
               rewrite locF.
               erewrite source_SomeI. apply H0.
               * apply MInj12.
               * unfold as_inj, join. 
                 subst j. rewrite jmap; auto.
               * assert (VB1: Mem.valid_block m1 b1). subst j; auto_sm. 
                 destruct (Fwd1 _ VB1) as [VB1' MaxP1 (*RDO1]*)].
                 apply MaxP1. eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
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
               destruct (valid_dec m2 b2); try solve[contradict n; auto]. clear v.
               (*destruct (Mem.perm_dec m2 b2 (ofs + delta) Max Writable). rename p into PW.*)
               remember (B b2) as isB; symmetry in HeqisB.
               destruct isB.
               { subst j.
                 destruct (RDOnly12 _ HeqisB) as [AIb [AIunique Perm12]].
                 assert (E: extBlocksTgt nu12 b2 = false).  eapply local_locBlocks; eassumption.
                 assert (NE:  extBlocksTgt nu12 b2 = true). eapply extern_DomRng; eassumption.
                 rewrite E in NE; discriminate. }
               (*prove that (k b2 = None) by contradiction*)
                 destruct (k b2) eqn: kmap. subst k.
                 { apply SMWD12 in locmap; destruct locmap as [locS locT].
                   destruct GlueInv as [loc rest]; rewrite loc in locT.
                   destruct p; apply SMWD23 in kmap; destruct kmap as [extS extT].
                   destruct SMWD23. destruct (disjoint_extern_local_Src b2) as [locS'|extS'].
                   + rewrite locT in locS'; inversion locS'.
                   + rewrite extS in extS'; inversion extS'. }
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
           { intros b1 ofs b2 delta map12' mperm1'. 
             unfold Mem.perm; rewrite property_cont; unfold mem_add_cont.
             (* New trying things*)
             unfold as_inj in map12'; apply joinD_Some in map12'; destruct map12' as [extmap | [extNone locmap]].
             + subst nu12'; rewrite ext_change_ext in extmap.
               eapply MKI_Some12 in extmap; eauto. 
               destruct extmap as [jmap | [jmap [b2' [d' [lmap' [b2eq deltaeq]]]]]].
             - assert (Mem.valid_block m2 b2) by (subst j; auto_sm).
               destruct (valid_dec m2 b2); try solve[contradict n; auto]. clear v.
               (*destruct (Mem.perm_dec m2 b2 (ofs + delta) Max Writable).*)
               remember (B b2) as isB. symmetry in HeqisB.
               destruct isB.
               { (*case B b2= true*)
                 subst j. apply extern_in_all in jmap.
                 clear - RDOnly12 HeqisB jmap RDOnly_fwd1 mperm1' MInj12 SMWD12' ExtIncr12.
                   destruct (RDOnly12 _ HeqisB) as [EXT12 [Unique12 NPerm12]].
                   specialize (Unique12 _ _ jmap); subst b1. 
                   rewrite (extern_in_all _ _ _ _ EXT12) in jmap; inversion jmap.
                   subst delta; clear RDOnly12 jmap.
                 rewrite (RDOnly_fwd_Dcont' _ _ _ _ _ RDOnly_fwd1 HeqisB mperm1').
                   apply extern_in_all in EXT12.
                   eapply memval_inject_incr.
                     eapply MInj12; try eassumption. erewrite RDOnly_fwd_Dperm; try eassumption. eapply NPerm12.
                    apply extern_incr_as_inj; eassumption.
                 eapply NPerm12.
               }
               { (*case B b2 = false *)
                 assert (locF: locBlocksSrc nu23 b2 = false).
                 { destruct GlueInv as [loc rest]; rewrite <- loc.
                   subst j; auto_sm. }
                 rewrite locF.
                 erewrite source_SomeI.
                 destruct MemInjNu'. destruct mi_inj.
                 (*Prepare to use mi_memval of nu'*)
                 assert (map13': exists b3 d3, as_inj nu' b1 = Some (b3, d3)).
                 { assert (kmap:=jmap).
                   apply Norm12 in kmap; destruct kmap as [b3 [d2 kmap]].
                   exists b3, (delta + d2).
                   unfold as_inj, join. destruct ExtIncr as [ext_incr other_incr]. 
                   erewrite ext_incr; eauto.
                   rewrite compose_sm_extern. subst j.
                   unfold compose_meminj.
                   rewrite jmap.
                   subst k. rewrite kmap; auto. }
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
                 * assert (VB1: Mem.valid_block m1 b1). subst j; auto_sm.
                   destruct (Fwd1 _ VB1) as [VB1' MaxP1 (*RDO1]*)].
                   apply MaxP1. eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
               }
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
               destruct (valid_dec m2 b2); try solve[contradict n; auto]. clear v.
               (*destruct (Mem.perm_dec m2 b2 (ofs + delta) Max Writable).*)
               remember (B b2) as isB; symmetry in HeqisB.
               destruct isB.
               { destruct (RDOnly23 _ HeqisB) as [EXT23 _].
                 rewrite (locBlocksSrc_externNone _ SMWD23 _ locTrue) in EXT23. discriminate.
               }
               (*prove that (k b2 = None) by contradiction*)
                 destruct (k b2) eqn: kmap. subst k.
                 { apply SMWD12 in locmap; destruct locmap as [locS locT].
                   destruct GlueInv as [loc rest]; rewrite loc in locT.
                   destruct p; apply SMWD23 in kmap; destruct kmap as [extS extT].
                   destruct SMWD23. destruct (disjoint_extern_local_Src b2) as [locS'|extS'].
                   + rewrite locT in locS'; inversion locS'.
                   + rewrite extS in extS'; inversion extS'. }
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
       + unfold as_inj; subst nu12'.
         intros b b' delta map; destruct (as_in_SomeE _ _ _ _ map) as [ext | loc].
         rewrite ext_change_ext in ext. 
         destruct (MKI_Some12 _ _ _ _ _ _ Heqoutput _ _ _ ext).
         destruct MInj12.
         unfold Mem.valid_block; rewrite property_nb; unfold mem_add_nb.
         eapply Pos.lt_trans; try eapply (Pos.lt_add_diag_r (Mem.nextblock m2)).
         apply (mi_mappedblocks b b' delta).
         unfold as_inj, join; subst j k l'; rewrite H; auto.
         destruct H as [jmap [b2' [d' [lmap' [eq1 eq2]]]]].
         destruct MemInjNu'. unfold Mem.valid_block; rewrite property_nb.
         unfold mem_add_nb. subst b'.
         destruct WDnu'.
         subst l'.
         apply extern_DomRng in lmap'; destruct lmap' as [extS extT].
         destruct SMvalNu' as [DOMv RNGv].
         assert (Plt b m1'.(Mem.nextblock)).
         apply DOMv. unfold DOM, DomSrc. rewrite extS; apply orb_true_r.
         xomega.

         unfold Mem.valid_block; rewrite property_nb.
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
           assert (VB: Mem.valid_block m1 b). eapply (valid_from_map nu12 m1 m2); eassumption.
           destruct (Fwd1 _ VB) as [VB1' Perm1 (*RDO1]*)].
           destruct MInj12. eapply mi_representable; eauto. 
           destruct H0; [left | right].
           apply Perm1; eassumption.
           apply Perm1; eassumption.
           (*
           eapply valid_from_map. 
           apply SMWD12.
           apply map12.
           eassumption.
           assumption.

           eapply Fwd1.
           eapply valid_from_map. apply SMWD12.
           apply map12.
           eassumption.
           assumption.*)

           destruct ofs as [ofs range].
           subst delta; split; simpl. 
           xomega. 
           split.
           xomega.
           unfold Int.max_unsigned.
           xomega.
         - assert (map12: as_inj nu12 b = Some (b', delta)).
           { apply local_in_all; auto. }
           assert (VB: Mem.valid_block m1 b). eapply (valid_from_map nu12 m1 m2); eassumption.
           destruct (Fwd1 _ VB) as [VB1' Perm1 (*RDO1]*)].
           destruct MInj12. eapply mi_representable; eauto. 
           destruct H0; [left | right].
           eapply Perm1; eauto.
           eapply Perm1; eauto.
           }
       split.
       (* mem_forward *)
       { exact Fwd2. }
       split. (*RDOnly_fwd2*) trivial.
       split.
       (* Mem.inject 23*)
       { constructor.
         + constructor.
         - { intros b1 b2 delta ofs k0 p map23.
             unfold Mem.perm. rewrite property_acc; unfold mem_add_acc.
             unfold as_inj in map23; apply joinD_Some in map23.
             destruct map23 as [extmap | [extmap locmap]].
             + subst nu23'.
               rewrite ext_change_ext in extmap.
               eapply MKI_Some23 in extmap; eauto. 
               destruct extmap as [kmap | [kmap [lmap' [jmapN bGt]]]].
               - assert (bavl: Mem.valid_block m2 b1).
                 { apply SMV23; eauto. 
                   unfold DOM; eapply as_inj_DomRng; eauto.
                   apply extern_in_all; subst k; eauto. }
                 destruct (valid_dec m2 b1); try solve[contradict n; auto].
                 clear v. 
                 remember (B b1) as isB; symmetry in HeqisB.
                 destruct isB.
                 { intros. subst k.  
                   destruct (RDOnly23 _ HeqisB) as [AIb [AIunique Perm23]]. 
                     rewrite kmap in AIb; inversion AIb. subst b2 delta; clear AIb.
                   apply extern_in_all in kmap.
                   eapply (RDOnly_fwd3 _ HeqisB 1 ofs); simpl.
                     intros. assert (i = 0) by omega. subst i. apply Perm23. (* rewrite Perm12.*) omega.
                     eapply Mem.perm_inject; eassumption. }

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
               clear v. 
               remember (B b1) as isB; symmetry in HeqisB.
               destruct isB.
                 { intros.
                   destruct (RDOnly23 _ HeqisB) as [AIb [AIunique Perm23]].
                   assert (E: extBlocksSrc nu23 b1 = false).  eapply local_locBlocks; eassumption.
                   assert (NE: extBlocksSrc nu23 b1 = true). eapply extern_DomRng; eassumption.
                   rewrite E in NE; discriminate. }
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
               - intros. eapply UnchLOOR23.
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
         - intros. unfold Z.divide.
           subst nu23'; unfold as_inj, join in H. rewrite ext_change_ext, loc_change_ext in H.
           destruct (k' b1) eqn:kmap'. 
           * destruct p0. destruct (MKI_Some23 _ _ _ _ _ _ Heqoutput _ _ _ kmap') as 
                          [kmap | [kmap [lmap [jmapN bGt]]]].
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
           rewrite property_acc in H0; unfold mem_add_acc in H0.
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
             rewrite property_cont; unfold mem_add_cont.
              rewrite property_acc; unfold mem_add_acc.
             unfold as_inj in map23; apply joinD_Some in map23.
             destruct map23 as [extmap | [extmap locmap]].
             + subst nu23'.
               rewrite ext_change_ext in extmap.
               eapply MKI_Some23 in extmap; eauto. 
               destruct extmap as [kmap | [kmap [lmap' [jmapN bGt]]]].
               - assert (bavl: Mem.valid_block m2 b1).
                 { apply SMV23; eauto. 
                   unfold DOM; eapply as_inj_DomRng; eauto.
                   apply extern_in_all; subst k; eauto. }
                 destruct (valid_dec m2 b1); try solve[contradict n; auto]. clear v.
                 remember (B b1) as isB; symmetry in HeqisB.
                 destruct isB.
                 { (*case B b1= true*)
                   intros; subst k. apply extern_in_all in kmap.
                   clear - RDOnly23 HeqisB kmap RDOnly_fwd3 H MInj23 SMWD23' ExtIncr23.
                   destruct (RDOnly23 _ HeqisB) as [EXT23 [_ NPerm23]].
                   apply extern_in_all in EXT23.
                   rewrite EXT23 in kmap; inversion kmap.
                   subst b2 delta; clear RDOnly23 kmap.                   
                   rewrite (RDOnly_fwd_Dcont _ _ _ _ _ RDOnly_fwd3 HeqisB).
                     2: eapply MInj23; eassumption.
                     2: eapply NPerm23.
                   eapply memval_inject_incr.
                     eapply MInj23; eassumption.
                     apply extern_incr_as_inj; eassumption.
                 }
                 { (*case B b1 = false*)
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
                 }
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
               destruct (valid_dec m2 b1); try solve [contradict n; trivial]. clear v.
                 remember (B b1) as isB; symmetry in HeqisB.
                 destruct isB.
                 { intros. 
                   destruct (RDOnly23 _ HeqisB) as [AIb [_ Perm12]].
                   assert (LF: locBlocksSrc nu23 b1 = false). eapply extern_DomRng'; eassumption.
                   assert (LT: locBlocksSrc nu23 b1 = true). eapply local_DomRng; eassumption.
                   rewrite LT in LF; discriminate. }
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
        rewrite property_nb in H.
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
             { (*1. Good case old externs *)
               eapply MInj23.
               apply H.
               eapply extern_in_all; auto.
               inversion H0; subst k p; trivial.
               eapply extern_in_all; auto.
               inversion H1; subst k p0; trivial.
               apply Fwd2; eauto.
               subst k; auto_sm.
               apply Fwd2; eauto.
               subst k ; auto_sm. }
             { (*2.cross case: Dificult case *)
               rewrite H0 in kmap1.
               apply shiftS_Some in H1. destruct H1.
               apply pure_filter_Some in H4. destruct H4.
               inversion H0; subst p; clear H0.
               rewrite Heqk in kmap1.
               assert(kmap1':=kmap1).
               unfold Mem.perm in H2, H3.
               rewrite property_acc in H2, H3; 
                 unfold mem_add_acc in H2,H3.
               assert (Mem.valid_block m2 b1) by auto_sm.
               destruct (valid_dec m2 b1); 
                 try solve[destruct n; eauto]. clear H0.
               apply extern_in_all in kmap1'.
               
               destruct (valid_dec m2 b2).
               { (* impossible case. *)
                 move v0 at bottom.
                 unfold Mem.valid_block, Plt, Pos.lt in v0. 
                 unfold Pos.gt in H1. rewrite H1 in v0; inversion v0. }
               clear H1.

               destruct (source j12' m1' b2 ofs2) eqn:sour2; try solve[inversion H3]. destruct p.
               assert (locF: locBlocksSrc nu23 b1 = false) by auto_sm.
               rewrite locF in H2.
               assert (totmap23: as_inj nu23 b1 = Some (b1', delta1)) 
                 by (apply extern_in_all; trivial).
               rewrite totmap23 in H2.

               symmetry in sour2. apply source_SomeE in sour2.
               destruct sour2 as [b02 [d02 [ofs02 [invert2 [bval2' [map122 [mparm2 of_eq2] ]]]]]].
               inversion invert2; clear invert2. subst b02 ofs02. subst ofs2. 

               remember (B b1) as isB1. symmetry in HeqisB1. destruct isB1.
               { destruct (RDOnly23 _ HeqisB1) as [EXT2 [Unique2 _]].
                 rewrite (extern_in_all _ _ _ _ EXT2) in totmap23. inversion totmap23. subst b1' delta1. clear totmap23 kmap1'.
                 clear UnchLOOR23 UnchLOOR12 UnchPrivSrc12 property_nb property_acc property_cont UnchPrivSrc .
                 destruct (eq_block b1 b2'); try subst b2'. 2: left; trivial. right.
                 subst l'. 
                 erewrite BSep in HeqisB1. discriminate.
                 2: eapply extern_in_all; eassumption. 
                 subst j. rewrite compose_sm_as_inj; eauto; try eapply GlueInv.
                   apply compose_meminjI_None. left.
                   apply joinI_None. assumption.
                   remember (local_of nu12 (b2 - Mem.nextblock m2)%positive) as l12.
                   destruct l12; trivial. symmetry in Heql12; destruct p.
                   assert (LocS: locBlocksSrc nu' (b2 - Mem.nextblock m2)%positive = true).
                     rewrite <- (extern_incr_locBlocksSrc _ _ ExtIncr). eapply SMWD12. eassumption.
                   rewrite (locBlocksSrc_externNone _ WDnu' _ LocS) in H6. discriminate. }  
               
               destruct (source (as_inj nu12) m1 b1 ofs1) eqn:sour1; try solve[inversion H2].
               symmetry in sour1. apply source_SomeE in sour1.
               destruct sour1 as [b01 [d01 [ofs01 [invert1 [bval1' [map121 [mparm1 of_eq1] ]]]]]].
               subst p ofs1.
               replace (ofs01 + d01 + delta1) with (ofs01 + (d01 + delta1)) by omega.
               replace (z + d02 + delta2) with (z + (d02 + delta2)) by omega.
               assert (H': b01<> (b2 - Mem.nextblock m2)%positive).
               { intros HH; subst b01.
                 unfold as_inj, join in map121. rewrite Heqj in H4; rewrite H4 in map121.
                 eapply SMWD12 in map121. destruct map121. destruct GlueInv as [loc rest].
                 rewrite loc in H1. rewrite locF in H1; inversion H1. }
               
               (*We prove (d02 = 0) /\ (b = (b2 - Mem.nextblock m2)%positive) *)
               subst j12' nu12'. unfold as_inj, join in map122.
               rewrite ext_change_ext in map122.
               inversion Heqoutput; subst j'.
               unfold add_inj, shiftT, filter_id in map122.
               destruct (j b) eqn:jmap. 
               { (*First case is impossible *)
                 destruct p; inversion map122; subst b2 d02.
                 contradict n. subst j; auto_sm. }

               destruct (l' b) eqn:lmap'; 
                 (*second case is impossible *)
                 try solve [rewrite loc_change_ext in map122; contradict n; auto_sm].
               inversion map122; subst b2 d02.
               eapply MemInjNu'.
               apply H'.
               { subst nu'.
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
               assumption.     
               { rewrite Pos.add_sub; auto. }
               (*{ remember (B b1) as isB1. symmetry in HeqisB1. destruct isB1. 2: auto.
                 destruct (RDOnly12 _ HeqisB1) as [EXT1 [Unique1 NW1]].
                 specialize (Unique1 _ _ map121). subst b01. rewrite (extern_in_all _ _ _ _ EXT1) in map121. inversion map121; subst d01. clear map121.
                 eapply (RDOnly_fwd1 _ HeqisB1 AST.Mint8unsigned ofs01); simpl.
                    intros. assert (ofs'=ofs01) by omega. subst ofs01. apply NW1. omega.
                    assumption. }                 
               { rewrite Pos.add_sub; auto. }
               remember (B b1) as isB1. symmetry in HeqisB1. destruct isB1. 2: inversion H2.
                 destruct (RDOnly12 _ HeqisB1) as [EXT1 [Unique1 NW1]].
                 destruct (RDOnly23 _ HeqisB1) as [EXT2 [Unique2 NW2]].
                 rewrite (extern_in_all _ _ _ _ EXT2) in totmap23. inversion totmap23. subst b1' delta1. clear totmap23 kmap1' kmap1.
                 destruct (eq_block b1 b2'); try subst b2'. 2: left; trivial. right.
                 destruct p.
                 clear locF NW1 NW2 H1 H0 UnchLOOR12 UnchLOOR23 property_nb property_acc property_cont GlueInv UnchLOOR13.
                 rewrite Zplus_0_r. intros N.
                 left. intros N. subst b2'.
                 assert (Mem.valid_block m2 
                 subst j k. specialize (Norm12 _ _ _ 
                 assert (VB3: Mem.valid_block m3 b1).
                 specialize (Unique2 _ _ totmap23). totmap123). subst b01. rewrite (extern_in_all _ _ _ _ EXT1) in map121. inversion map121; subst d01. clear map121.
                 eapply (RDOnly_fwd1 _ HeqisB1 AST.Mint8unsigned ofs01); simpl.
                    intros. assert (ofs'=ofs01) by omega. subst ofs01. apply NW1. omega.
                    assumption.*) }
             (*3.cross case: Dificult case *)
             { rewrite H1 in kmap2.
               apply shiftS_Some in H0. destruct H0.
               apply pure_filter_Some in H4. destruct H4.
               inversion H1; subst p; clear H1.
               rewrite Heqk in kmap2.
               assert(kmap2':=kmap2).
               unfold Mem.perm in H2, H3.
               rewrite property_acc in H2, H3; 
                 unfold mem_add_acc in H2,H3.
               assert (Mem.valid_block m2 b2) by auto_sm.
               destruct (valid_dec m2 b2) eqn:bval2; 
                 try solve[destruct n; eauto]. clear bval2 v.
               destruct (valid_dec m2 b1) eqn:bval1.
               { unfold Mem.valid_block, Plt, Pos.lt in v. move v at bottom.
                 unfold Pos.gt in H0. rewrite v in H0; inversion H0. }
               clear bval1.
               destruct (source j12' m1' b1 ofs1) eqn:sour1; try solve[inversion H2].
               assert (locF: locBlocksSrc nu23 b2 = false) by auto_sm.
               rewrite locF in H3.
               assert (totmap23: as_inj nu23 b2 = Some (b2', delta2)) 
                 by (apply extern_in_all; trivial).
               rewrite totmap23 in H3.
               remember (B b2) as isB; symmetry in HeqisB.
               destruct isB.
               { destruct p.
                 destruct (eq_block b1' b2'); try subst b2'. 2: left; trivial. right.
                 destruct (RDOnly23 _ HeqisB) as [EXT2 [Unique2 _]].
                 rewrite EXT2 in kmap2. inversion kmap2; clear kmap2 kmap2'. subst b1' delta2.
                 subst l' j k.
                 erewrite BSep in HeqisB. discriminate.
                 2: eapply extern_in_all; eapply H6.
                 rewrite compose_sm_as_inj; eauto; try eapply GlueInv.
                   apply compose_meminjI_None. left.
                   apply joinI_None. assumption.
                   remember (local_of nu12 (b1 - Mem.nextblock m2)%positive) as l12.
                   destruct l12; trivial. symmetry in Heql12; destruct p.
                   assert (LocS: locBlocksSrc nu' (b1 - Mem.nextblock m2)%positive = true).
                     rewrite <- (extern_incr_locBlocksSrc _ _ ExtIncr). eapply SMWD12. eassumption.
                   rewrite (locBlocksSrc_externNone _ WDnu' _ LocS) in H6. discriminate. }  
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
               rewrite property_acc in H2, H3; 
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
           destruct ext1 as [kmap | [kmap [lmap [jmapN bt]]]].
           assert (map23: as_inj nu23 b = Some (b', delta)).
           { apply extern_in_all; subst k; trivial. }
           eapply MInj23; eauto.
           destruct H0; [left | right].
           destruct (Fwd2 b) as [VB' Max2Perm].
             eapply (valid_from_map nu23); eauto.  
             apply Max2Perm; assumption.
           destruct (Fwd2 b) as [VB' Max2Perm].
             eapply (valid_from_map nu23); eauto.  
             apply Max2Perm; assumption.

           eapply MemInjNu'.
           apply extern_in_all; subst l'; eauto.
           unfold Mem.perm in H0.
           rewrite property_acc in H0; 
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
           destruct (Fwd2 b) as [VB' Max2Perm].
             eapply (valid_from_map nu23); eauto.   
             apply Max2Perm; assumption.
           destruct (Fwd2 b) as [VB' Max2Perm].
             eapply (valid_from_map nu23); eauto.   
             apply Max2Perm; assumption.
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
         { subst nu12'. unfold RNG, DomTgt, change_ext in H. destruct nu12; simpl in H.
           unfold Mem.valid_block. rewrite property_nb. unfold mem_add_nb.
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
         subst nu23'. unfold DOM, DomSrc, change_ext in H. destruct nu23; simpl in H.
         subst extS23; simpl in H.
         (* Valid block *)
         { unfold DOM, DomSrc, change_ext in H.
           unfold Mem.valid_block. rewrite property_nb. unfold mem_add_nb.
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
       { intros; subst nu12'. 
         rewrite ext_change_ext in H. apply (MKI_Some12 _ _ _ _ _ _ Heqoutput) in H.
         destruct H.
         + left; trivial.
         + destruct H as [jmap [b2' [d' [lmap rest]]]].
           right; split; trivial; exists b2', d'. trivial.
       }
       { clear SMWD12 SMWD12' SMWD23'.
         intros; subst nu23' j k l'. 
         rewrite ext_change_ext in H.
         eapply (MKI_Some23 _ _ _ _ _ _ Heqoutput) in H.
         destruct H as [extmap23 | [extmap23 [extmap' [extmap12 rest]]]].
         + left; trivial.
         + right; split; trivial.
           exists (b2 - Mem.nextblock m2)%positive, 0.
           subst nu12'. rewrite ext_change_ext.
           inversion Heqoutput.
           unfold add_inj.
           rewrite extmap12. (*NEW: this is the key to not using sm_inject_separated*)
           unfold filter_id, shiftT; rewrite extmap'. 
           replace (b2 - Mem.nextblock m2 + Mem.nextblock m2)%positive with b2; auto. 
           symmetry; apply Pos.sub_add. apply Pos.gt_lt_iff. apply rest.
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
                             (*Pure: pure_comp_ext nu12 nu23 m1 m2*)
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
         B (RDOnly12: RDOnly_inj m1 m2 nu12 B) (RDOnly23: RDOnly_inj m2 m3 nu23 B)
           (RDOnly_fwd1: RDOnly_fwd m1 m1' B) (RDOnly_fwd3: RDOnly_fwd m3 m3' B)
           (BSep : forall (b1 b2 : block) (d : Z),
                 as_inj (compose_sm nu12 nu23) b1 = None ->
                 as_inj nu' b1 = Some (b2, d) -> B b2 = false)
                             (full: full_ext nu12 nu23),
     exists m2', exists nu12', exists nu23', nu'=compose_sm nu12' nu23' /\
                             extern_incr nu12 nu12' /\ extern_incr nu23 nu23' /\
                             Mem.inject (as_inj nu12') m1' m2' /\ mem_forward m2 m2' /\ RDOnly_fwd m2 m2' B /\
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
                              (forall b1 b2 d, extern_of nu12' b1 = Some (b2, d) ->
                                               extern_of nu12 b1 = Some (b2, d) \/
                                               extern_of nu12 b1 = None /\
                                               exists b3 d2, extern_of nu' b1 = Some (b3, d2)) /\
                              (forall b2 b3 d2, extern_of nu23' b2 = Some (b3, d2) ->
                                               extern_of nu23 b2 = Some (b3, d2) \/
                                               extern_of nu23 b2 = None /\
                                               exists b1 d, extern_of nu12' b1 = Some (b2, d)).

                          (* /\ Mem.unchanged_on (local_out_of_reach nu23 m2) m3 m3'.*)
Proof. intros.
  destruct (EFF_interp_II_strong _ _ _ MInj12 _ Fwd1 _ _ MInj23 _ 
              Fwd3 _ WDnu' SMvalNu' MemInjNu' ExtIncr
              (*Pure*) SMV12 SMV23 UnchPrivSrc UnchLOOR13 GlueInvNu Norm12 B)
  as [m2' [nu12' [nu23' [A [BB [C [D [E [F [G [H [I [J [K [L [M ]]]]]]]]]]]]]]]]; try assumption.
  exists m2', nu12', nu23'. intuition.
Qed.

