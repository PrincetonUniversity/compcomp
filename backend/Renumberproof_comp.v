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

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Postorder.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Renumber.

Require Import mem_lemmas.
Require Import semantics.
Require Import semantics_lemmas.
Require Import reach.
Require Import effect_semantics.
Require Import structured_injections.
Require Import simulations.
Require Import effect_properties.
Require Import simulations_lemmas.

Require Export Axioms.
Require Import RTL_coop.
Require Import BuiltinEffects.
Require Import RTL_eff.
Require Import Op_comp.

Require Import RTL2RTL_proof_comp.

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

(*NEW*) Variable hf : I64Helpers.helper_functions.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof (@Genv.find_symbol_transf _ _ _ transf_fundef prog).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (@Genv.find_var_info_transf _ _ _ transf_fundef prog).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id]. 
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
      rewrite <- symbols_preserved in Hid.
      exists id; assumption.
     rewrite symbols_preserved in Hid.
      exists id; assumption.
     split; intros b. 
       split; intros; destruct H as [id Hid].
       rewrite <- varinfo_preserved in Hid.
       exists id; assumption.
       rewrite varinfo_preserved in Hid.
       exists id; assumption.
    intros. split.
      intros [f H].
        apply function_ptr_translated in H. 
        eexists; eassumption.
     intros [f H].
         apply (@Genv.find_funct_ptr_rev_transf
           _ _ _ transf_fundef prog) in H.
         destruct H as [? [? _]]. eexists; eassumption.
Qed.

(** Effect of an injective renaming of nodes on a CFG. *)

Section RENUMBER.

Variable f: PTree.t positive.

Hypothesis f_inj: forall x1 x2 y, f!x1 = Some y -> f!x2 = Some y -> x1 = x2.

Lemma renum_cfg_nodes:
  forall c x y i,
  c!x = Some i -> f!x = Some y -> (renum_cfg f c)!y = Some(renum_instr f i).
Proof.
  set (P := fun (c c': code) =>
              forall x y i, c!x = Some i -> f!x = Some y -> c'!y = Some(renum_instr f i)).
  intros c0. change (P c0 (renum_cfg f c0)). unfold renum_cfg. 
  apply PTree_Properties.fold_rec; unfold P; intros.
  (* extensionality *)
  eapply H0; eauto. rewrite H; auto. 
  (* base *)
  rewrite PTree.gempty in H; congruence.
  (* induction *)
  rewrite PTree.gsspec in H2. unfold renum_node. destruct (peq x k). 
  inv H2. rewrite H3. apply PTree.gss. 
  destruct f!k as [y'|] eqn:?. 
  rewrite PTree.gso. eauto. red; intros; subst y'. elim n. eapply f_inj; eauto. 
  eauto. 
Qed.

End RENUMBER.

Definition pnum (f: function) := postorder (successors_map f) f.(fn_entrypoint).

Definition reach (f: function) (pc: node) := reachable (successors_map f) f.(fn_entrypoint) pc.

Lemma transf_function_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  reach f pc ->
  (transf_function f).(fn_code)!(renum_pc (pnum f) pc) = Some(renum_instr (pnum f) i).
Proof.
  intros. 
  destruct (postorder_correct (successors_map f) f.(fn_entrypoint)) as [A B].
  fold (pnum f) in *. 
  unfold renum_pc. destruct (pnum f)! pc as [pc'|] eqn:?.
  simpl. eapply renum_cfg_nodes; eauto.
  elim (B pc); auto. unfold successors_map. rewrite PTree.gmap1. rewrite H. simpl. congruence.
Qed.

Ltac TR_AT :=
  match goal with
  | [ A: (fn_code _)!_ = Some _ , B: reach _ _ |- _ ] =>
        generalize (transf_function_at _ _ _ A B); simpl renum_instr; intros
  end.

Lemma reach_succ:
  forall f pc i s,
  f.(fn_code)!pc = Some i -> In s (successors_instr i) ->
  reach f pc -> reach f s.
Proof.
  unfold reach; intros. econstructor; eauto. 
  unfold successors_map. rewrite PTree.gmap1. rewrite H. auto. 
Qed.
  
Lemma regset_find_function_translated:
  forall j ros rs1 rs2 fd,
  meminj_preserves_globals ge j ->
  globalfunction_ptr_inject ge j ->
  regset_inject j rs1 rs2 ->
  find_function ge ros rs1 = Some fd ->
  find_function tge ros rs2 = Some (transf_fundef fd).
Proof.
  unfold find_function; intros; destruct ros; simpl.
  apply functions_translated.
   destruct (Genv.find_funct_inv _ _ H2) as [b Hb].
    specialize (H1 r). rewrite Hb in *. inv H1.
    rewrite Genv.find_funct_find_funct_ptr in H2.
    destruct (H0 _ _ H2). rewrite H1 in H6. inv H6.
    rewrite Int.add_zero.  
    rewrite Genv.find_funct_find_funct_ptr. assumption.
  
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i).
  apply function_ptr_translated; auto.
  congruence.
Qed.

(*NEW, as in Linearize*) 
Definition sp_mapped mu sp1 sp2:=
  val_inject (local_of mu) sp1 sp2 /\
  (forall b z, sp1 = Vptr b z -> exists b', as_inj mu b = Some(b',0)).
 
Lemma sp_mapped_intern_incr mu mu' sp1 sp2: 
       sp_mapped mu sp1 sp2 -> intern_incr mu mu' -> SM_wd mu' ->
       sp_mapped mu' sp1 sp2.
Proof. intros.
  destruct H. split; intros.
    eapply val_inject_incr; try eassumption.
    eapply H0.
  destruct (H2 _ _ H3).
  exists x; eapply intern_incr_as_inj; try eassumption.
Qed.

Lemma sp_mapped_extern_incr mu mu' sp1 sp2: 
       sp_mapped mu sp1 sp2 -> extern_incr mu mu' -> SM_wd mu' ->
       sp_mapped mu' sp1 sp2.
Proof. intros.
  destruct H. split; intros.
    eapply val_inject_incr; try eassumption.
      assert (local_of mu = local_of mu') by eapply H0.
      rewrite H3; apply inject_incr_refl.
  destruct (H2 _ _ H3).
  exists x; eapply extern_incr_as_inj; try eassumption.
Qed.
Inductive match_frames mu: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs (*NEW*) tsp trs
        (REACH: reach f pc)
        (*NEW*) (AGREE: regset_inject (restrict (as_inj mu) (vis mu)) rs trs)
        (*NEW*) (SPlocal: sp_mapped mu sp tsp),
      match_frames mu (Stackframe res f sp pc rs)
                      (Stackframe res (transf_function f) tsp (renum_pc (pnum f) pc) trs).

Lemma match_frames_intern_incr mu mu' s ts:
     match_frames mu s ts ->
     intern_incr mu mu' -> SM_wd mu' ->
     match_frames mu' s ts.
Proof. intros. inv H; econstructor; eauto.
  eapply regset_incr; try eassumption.
    eapply intern_incr_restrict; try eassumption.
    eapply sp_mapped_intern_incr; eassumption.
Qed.

Lemma list_match_frames_intern_incr mu mu': forall s ts,
     list_forall2 (match_frames mu) s ts ->
     intern_incr mu mu' -> SM_wd mu' ->
     list_forall2 (match_frames mu') s ts.
Proof. intros.
  induction H; econstructor; eauto.
  eapply match_frames_intern_incr; eassumption.
Qed.

Lemma match_frames_extern_incr mu mu' s ts:
     match_frames mu s ts ->
     extern_incr mu mu' -> SM_wd mu' ->
     match_frames mu' s ts.
Proof. intros. inv H; econstructor; eauto.
  eapply regset_incr; try eassumption.
    eapply extern_incr_restrict; try eassumption.
    eapply sp_mapped_extern_incr; eassumption.
Qed.

Lemma list_match_frames_extern_incr mu mu': forall s ts,
     list_forall2 (match_frames mu) s ts ->
     extern_incr mu mu' -> SM_wd mu' ->
     list_forall2 (match_frames mu') s ts.
Proof. intros.
  induction H; econstructor; eauto.
  eapply match_frames_extern_incr; eassumption.
Qed.

Inductive match_states (*NEW*) mu: RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' (*NEW*) tsp trs tm
        (STACKS: list_forall2 (match_frames mu) stk stk')
        (REACH: reach f pc)
        (*NEW*) (AGREE: regset_inject (restrict (as_inj mu) (vis mu)) rs trs)
        (*NEW*) (SPlocal: sp_mapped mu sp tsp),
      match_states mu (RTL_State stk f sp pc rs) m
                      (RTL_State stk' (transf_function f) tsp (renum_pc (pnum f) pc) trs) tm
  | match_callstates: forall stk f args m stk' (*NEW*) targs tm
        (STACKS: list_forall2 (match_frames mu) stk stk')
        (ARGS: val_list_inject (restrict (as_inj mu) (vis mu)) args targs),
      match_states mu (RTL_Callstate stk f args) m
                      (RTL_Callstate stk' (transf_fundef f) targs) tm
  | match_returnstates: forall stk v m stk' (*NEW*) tv tm
        (STACKS: list_forall2 (match_frames mu) stk stk')
        (RV: val_inject (restrict (as_inj mu) (vis mu)) v tv),
      match_states mu (RTL_Returnstate stk v) m
                      (RTL_Returnstate stk' tv) tm.

Definition MATCH mu c1 m1 c2 m2:Prop :=
  match_states (restrict_sm mu (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma MATCH_wd: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma MATCH_restrict: forall mu c1 m1 c2 m2 X
  (MC: MATCH mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m1 X), 
  MATCH (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
  rewrite restrict_sm_nest; intuition.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
  unfold vis in HX. intuition.
split. rewrite restrict_sm_all.
  eapply restrict_preserves_globalfun_ptr; try eassumption.
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
split. assumption.
  rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.
Qed.

Lemma MATCH_valid: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2), sm_valid mu m1 m2.
Proof. intros. eapply MC. Qed.

Lemma MATCH_PG: forall mu c1 m1 c2 m2 
  (MC: MATCH mu c1 m1 c2 m2),
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

Lemma replace_locals_frames mu pubSrc' pubTgt': forall a b,
      match_frames (restrict_sm mu (vis mu)) a b->
      match_frames (restrict_sm (replace_locals mu pubSrc' pubTgt') (vis mu)) a b.
Proof. intros.
induction H; econstructor; eauto.
  rewrite restrict_sm_all, vis_restrict_sm, replace_locals_vis,
          replace_locals_as_inj, restrict_nest. 
  rewrite restrict_sm_all, vis_restrict_sm, restrict_nest in AGREE. trivial.
  trivial. trivial.
  destruct SPlocal.
  split; intros.
    rewrite restrict_sm_local, replace_locals_local.
    rewrite restrict_sm_local in H. trivial. 
  subst. rewrite restrict_sm_all, replace_locals_as_inj in *.
    eapply H0. reflexivity.
Qed.

Lemma replace_locals_forall_frames mu pubSrc' pubTgt': forall s ts,
      list_forall2 (match_frames (restrict_sm mu (vis mu))) s ts ->
      list_forall2 (match_frames (restrict_sm (replace_locals mu pubSrc' pubTgt') (vis mu))) s ts.
Proof. intros.
induction H; econstructor; eauto. clear IHlist_forall2.
eapply replace_locals_frames; eassumption.
Qed.

Lemma MATCH_effcore_diagram: forall 
       st1 m1 st1' m1' U1
       (CS: effstep (rtl_eff_sem hf) ge U1 st1 m1 st1' m1')
       st2 mu m2 
       (MTCH: MATCH mu st1 m1 st2 m2),
exists st2' m2' U2 mu',
   effstep (rtl_eff_sem hf) tge U2 st2 m2 st2' m2'
  /\ intern_incr mu mu'
  /\ sm_inject_separated mu mu' m1 m2
  /\ sm_locally_allocated mu mu' m1 m2 m1' m2'
  /\ MATCH mu' st1' m1' st2' m2'
  /\ SM_wd mu' /\ sm_valid mu' m1' m2'
  /\ (forall (U1Vis: forall b ofs, U1 b ofs = true -> vis mu b = true)
       b ofs, U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros.
  destruct MTCH as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (GDE:= GDE_lemma).
  assert (SymbPres := symbols_preserved).

  induction CS; intros; try (inv MS); try TR_AT. 

{ (* nop *)
  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Inop; eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  constructor; auto. eapply reach_succ; eauto. simpl; auto. }

{ (* op *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit (eval_operation_inject'' _ _ ge (as_inj (restrict_sm mu (vis mu)))); try eapply H.
    eapply val_inject_incr; try eapply SPlocal. 
      apply local_in_all.
      apply restrict_sm_WD. assumption. trivial.
    eapply restrict_sm_preserves_globals. assumption.
      unfold vis. intuition.
    eapply regset_get_list. rewrite restrict_sm_all. eassumption.
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eassumption.
  intros [v2 [EVALOP' VINJ]].
  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Iop; eauto.
    instantiate (1 := v2). rewrite <- EVALOP'.
     apply eval_operation_preserved. exact symbols_preserved. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite restrict_sm_all in VINJ.
    eapply regset_set; try eassumption. }

{ (* load *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
      eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis; intuition.
  assert (SA: forall (id : ident) (ofs : int),
      val_inject (as_inj (restrict_sm mu (vis mu))) (symbol_address ge id ofs) (symbol_address ge id ofs)).
    intros. eapply symbol_address_inject; try eapply PGR. 
  exploit (eval_addressing_inj ge SA); try eassumption.
     eapply val_inject_incr; try eapply SPlocal. 
       eapply local_in_all; try eassumption.
     rewrite restrict_sm_all. eapply regset_get_list; try eassumption.
  intros [a' [EA' VA]].
  exploit (Mem.loadv_inject (as_inj (restrict_sm mu (vis mu)))).
    rewrite restrict_sm_all. eapply inject_restrict; eassumption.
    eexact H1. 
    apply VA. 
  intros [v' [C D]]. 
  eexists; eexists; eexists; exists mu; split.
    assert (eval_addressing tge tsp addr trs ## args = Some a').
      rewrite <- EA'. apply eval_addressing_preserved. exact symbols_preserved. 
    eapply rtl_effstep_exec_Iload; eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  constructor; auto. eapply reach_succ; eauto. simpl; auto.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    rewrite restrict_sm_all in D.
    eapply regset_set; try eassumption. }

{ (* store *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
      eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis; intuition.
  assert (SA: forall (id : ident) (ofs : int),
      val_inject (as_inj (restrict_sm mu (vis mu))) (symbol_address ge id ofs) (symbol_address ge id ofs)).
    intros. eapply symbol_address_inject; try eapply PGR. 
  exploit (eval_addressing_inj ge SA); try eassumption.
     eapply val_inject_incr; try eapply SPlocal. 
       eapply local_in_all; try eassumption.
     rewrite restrict_sm_all. eapply regset_get_list; try eassumption.
  intros [a' [EA' VA]]. 
  exploit (Mem.storev_mapped_inject (as_inj mu));
    try eassumption.
    rewrite restrict_sm_all in VA.
      eapply val_inject_incr; try eapply VA. apply restrict_incr.
    eapply val_inject_incr; try eapply AGREE. apply restrict_incr.
  intros [m2' [C D]].
  eexists; eexists; eexists; exists mu; split.
    assert (eval_addressing tge tsp addr trs ## args = Some a').
      rewrite <- EA'. apply eval_addressing_preserved. exact symbols_preserved.
    eapply rtl_effstep_exec_Istore; eauto.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; apply extensionality; intros bb; 
      try rewrite (storev_freshloc _ _ _ _ _ H1); 
      try rewrite (storev_freshloc _ _ _ _ _ C); intuition. 
  destruct a; inv H1.
  rewrite restrict_sm_all in VA. inv VA.
  destruct (restrictD_Some _ _ _ _ _ H5).
  simpl in C.
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.store_valid_block_1; try eassumption.
        eapply SMV; assumption.
  split; intuition.
  split; intuition. 
    constructor; auto. eapply reach_succ; eauto. simpl; auto.
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.  
    eapply REACH_Store; try eassumption. 
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (AGREE src). 
                   rewrite H6 in AGREE; inv AGREE.   
                   destruct (restrictD_Some _ _ _ _ _ H10); trivial.
    intros. apply StoreEffectD in H6. destruct H6 as [z [HI Ibounds]].
            apply eq_sym in HI. inv HI. 
            eapply visPropagateR; eassumption.
    eapply StoreEffect_PropagateLeft; try eassumption.
     econstructor. eassumption. trivial.
     apply C. }

{ (* call *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit regset_find_function_translated; try eassumption.
    eapply regset_incr; try eapply AGREE. apply restrict_incr. 
  intros TFD.
  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Icall with (fd := transf_fundef fd); eauto.
    apply sig_preserved.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  constructor. constructor; auto. constructor. eapply reach_succ; eauto. simpl; auto.
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
      assumption.
      rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
        eapply regset_get_list; eassumption. }

{ (* tailcall *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit regset_find_function_translated; try eassumption.
    eapply regset_incr. eassumption. apply restrict_incr.
  intros TFD.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  destruct SPlocal as [SPL1 SPL2]. inv SPL1. 
  destruct (SPL2 _ _ (eq_refl _)) as [spb SPB]; clear SPL2.
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply restrictD_Some. rewrite restrict_sm_all in SPB; eassumption.
  simpl in H3; rewrite Zplus_0_r in H3.
  rewrite (local_in_all _ WDR _ _ _ H5) in SPB; inv SPB.

  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Itailcall with (fd := transf_fundef fd); eauto.
    apply sig_preserved.
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; apply extensionality; intros bb; 
          try rewrite (freshloc_free _ _ _ _ _ H2);
          try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
  split.
    split; intuition. 
      constructor. auto.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
          eapply regset_get_list; eassumption.
      eapply REACH_closed_free; try eassumption.
  split; trivial. 
  split; trivial. 
  intros.
    apply local_in_all in H5; trivial.
    rewrite restrict_sm_all in H5.
    destruct (restrictD_Some _ _ _ _ _ H5).
    split. apply FreeEffectD in H6.
           destruct H6; subst. 
           eapply visPropagate; try eassumption.
    eapply FreeEffect_PropagateLeft; try eassumption. }

{ (* builtin *)
    rewrite restrict_sm_all, vis_restrict_sm, restrict_nest in AGREE; trivial. 
  inv H. 
  exploit (inlineable_extern_inject ge tge); try eassumption.
    eapply regset_get_list; eassumption.
  intros [mu' [v' [m'' [TEC [ResInj [MINJ' [UNMAPPED [LOOR [INC [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]]]. 
 
  eexists; eexists; eexists; exists mu'; split.
    eapply rtl_effstep_exec_Ibuiltin; eauto.
  split. assumption.
  split. assumption.
  split. assumption.
  split. 
    split.
      constructor; auto.
        eapply list_match_frames_intern_incr; try eassumption.
          eapply restrict_sm_intern_incr; eassumption.
          apply restrict_sm_WD; trivial.
        eapply reach_succ; eauto.
        simpl; auto.
        rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; trivial.
          eapply regset_set; try eassumption. 
          eapply regset_incr; try eassumption.
          eapply intern_incr_restrict; eassumption.
        eapply sp_mapped_intern_incr; try eassumption.
           eapply restrict_sm_intern_incr; eassumption.
           apply restrict_sm_WD; trivial.
      intuition.
      apply intern_incr_as_inj in INC; trivial.
        apply sm_inject_separated_mem in SEP; trivial.
        eapply meminj_preserves_incr_sep; eassumption. 
      red; intros b fb Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
          rewrite <- FRG. eapply Glob; eassumption.
  split; trivial.
  split; trivial.
  intros.
    eapply BuiltinEffect_Propagate; try eassumption.
    apply regset_get_list; eassumption. }
        
{ (* cond *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  exploit eval_condition_inject; try eassumption.
    eapply val_list_inject_incr.
    Focus 2. eapply  regset_get_list; try eassumption.
    apply restrict_incr.
  intros EC. 
  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Icond; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  replace (if b then renum_pc (pnum f) ifso else renum_pc (pnum f) ifnot)
     with (renum_pc (pnum f) (if b then ifso else ifnot)).
  constructor; auto.
    eapply reach_succ; eauto.
    simpl. destruct b; auto. 
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
    destruct b; auto. }

{ (* jumptbl *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (Vinj:= AGREE arg). 
  rewrite H0 in Vinj. inv Vinj.
  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Ijumptable; eauto.
       rewrite list_nth_z_map. rewrite H1. simpl; eauto.  
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  constructor; auto. eapply reach_succ; eauto.
    simpl. eapply list_nth_z_in; eauto. 
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial. }

{ (* return *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AGREE; trivial.
  assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; try eassumption. trivial.
  destruct SPlocal as [SPL1 SPL2]; inv SPL1.
  destruct (SPL2 _ _ (eq_refl _)) as [spb SPB]; clear SPL2.
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply restrictD_Some. rewrite restrict_sm_all in SPB; eassumption.
  simpl in H2; rewrite Zplus_0_r in H2.
  rewrite (local_in_all _ WDR _ _ _ H4) in SPB; inv SPB.
  eexists; eexists; eexists; exists mu; split.
    eapply rtl_effstep_exec_Ireturn; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
      repeat split; apply extensionality; intros bb; 
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H2); intuition.
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  split.
    split. 
      constructor; auto.
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
        destruct or; simpl. apply AGREE. constructor.
    intuition.    
      eapply REACH_closed_free; try eassumption.
  split; trivial.
  split; trivial.
  intros.
    apply local_in_all in H4; trivial.
    rewrite restrict_sm_all in H4.
    destruct (restrictD_Some _ _ _ _ _ H4).
    split. apply FreeEffectD in H5.
           destruct H5; subst. 
           eapply visPropagate; try eassumption.
    eapply FreeEffect_PropagateLeft; try eassumption. }

{ (* internal function *)
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in ARGS; trivial.
  edestruct alloc_parallel_intern as 
     [mu' [tm' [b' [Alloc' [MInj' [IntInc [mu'SP [Ai' [SEP [LocAlloc [WD' [SMV' RC']]]]]]]]]]]]; 
     eauto; try apply Zle_refl.
  eexists; eexists; eexists; exists mu'; split.
    eapply rtl_effstep_exec_function_internal; eauto.
  split. assumption. 
  split. assumption. 
  split. assumption. 
  split. 
    split. constructor; auto.
      { (*matchframes*)
        eapply list_match_frames_intern_incr; try eassumption.
        eapply restrict_sm_intern_incr; eassumption.
         apply restrict_sm_WD; trivial. }
      unfold reach. constructor.
      { (*regset_inject*)
        rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
         simpl. eapply regset_incr.
              eapply regset_init_regs; try eassumption. 
              apply intern_incr_restrict; eassumption. }
      { (*sp_mapped*)
        destruct (joinD_Some _ _ _ _ _ mu'SP) as [EXT | [EXT LOC]]; clear mu'SP.
        assert (EE: extern_of mu = extern_of mu') by eapply IntInc.
        rewrite <- EE in EXT; clear EE.
        elim (Mem.fresh_block_alloc _ _ _ _ _ H).
        eapply SMV. 
          eapply as_inj_DomRng; trivial.
          apply extern_in_all; eassumption.
        split. rewrite restrict_sm_local.
          econstructor. apply restrictI_Some; try eassumption.
            unfold vis. destruct (local_DomRng _ WD' _ _ _ LOC) as [lS lT]; rewrite lS; trivial.
          rewrite Int.add_zero. trivial. 
        intros b zz BB; inv BB. rewrite restrict_sm_all.
          eexists. apply restrictI_Some. apply local_in_all; eassumption.
           unfold vis. destruct (local_DomRng _ WD' _ _ _ LOC) as [lS' lT']. rewrite lS'; trivial. }
     intuition.
     apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
       intros. apply as_inj_DomRng in H1.
               split; eapply SMV; eapply H1.
       assumption.
       apply intern_incr_as_inj; eassumption.
       apply sm_inject_separated_mem. assumption.
       assumption.
     red; intros. destruct (GFP _ _ H1). split; trivial.
          eapply intern_incr_as_inj; eassumption.
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
       rewrite <-FF. eapply Glob; eassumption.
  intuition. }

{ (* nonobservable external function *) 
  rewrite  vis_restrict_sm, restrict_sm_all, restrict_nest in *; trivial.
  specialize (EFhelpers _ _ OBS); intros. 
  exploit (inlineable_extern_inject ge tge); try eassumption.
  intros [mu' [v' [m'' [TEC [ResInj [MINJ' [UNMAPPED
      [LOOR [INC [SEP [LOCALLOC [WD' [SMV' RC']]]]]]]]]]]]]. 
 
  eexists; eexists; eexists; exists mu'; split.
    eapply rtl_effstep_exec_function_external; eauto.
  split. assumption.
  split. assumption.
  split. assumption.
  split.
    split. constructor; auto.
      eapply list_match_frames_intern_incr; try eassumption.
        eapply restrict_sm_intern_incr; eassumption.
        apply restrict_sm_WD; trivial.
      rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; trivial.
    intuition.
    eapply (intern_incr_meminj_preserves_globals_as_inj _ mu); trivial.
      split; assumption.
      red; intros ? ? Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
    eapply (intern_incr_meminj_preserves_globals_as_inj _ mu); try eassumption. 
      split; eassumption.
  split. assumption.
  split. assumption.
  intros. eapply BuiltinEffect_Propagate; try eassumption. }  

{ (* return *)
  inv STACKS. inv H1.
  eexists; eexists; eexists; exists mu; split.  
    eapply rtl_effstep_exec_return; eauto. 
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj. 
  split. rewrite sm_locally_allocatedChar.
         repeat split; extensionality bb; 
          try rewrite freshloc_irrefl; intuition. 
  split; intuition.
  split; intuition. 
  constructor; auto.
  apply regset_set; assumption. }
Qed.  

Lemma MATCH_atExternal: forall mu c1 m1 c2 m2 e vals1 ef_sig
       (MTCH: MATCH mu c1 m1 c2 m2)
       (AtExtSrc: at_external (rtl_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
     Mem.inject (as_inj mu) m1 m2 /\
     exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
       at_external (rtl_eff_sem hf) c2 = Some (e, ef_sig, vals2) /\
      (forall pubSrc' pubTgt',
       pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
       pubTgt' = (fun b : block => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
       forall nu : SM_Injection, nu = replace_locals mu pubSrc' pubTgt' ->
       MATCH nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2).
Proof. intros. 
destruct MTCH as [MC [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
inv MC; simpl in AtExtSrc; inv AtExtSrc.
destruct f; simpl in *; inv H0.
destruct (observableEF_dec hf e0); inv H1.
split; trivial.
rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in ARGS; trivial.
exploit val_list_inject_forall_inject; try eassumption. intros ARGS'.
exists targs.
split; trivial.
split; trivial.
specialize (forall_vals_inject_restrictD _ _ _ _ ARGS'); intros.
exploit replace_locals_wd_AtExternal; try eassumption. 
intuition. 
(*MATCH*)
    split; subst; rewrite replace_locals_vis. 
      econstructor; repeat rewrite restrict_sm_all, vis_restrict_sm, replace_locals_vis, replace_locals_as_inj in *; eauto.
      eapply replace_locals_forall_frames; eassumption.
    rewrite restrict_nest; trivial.
    subst. rewrite replace_locals_frgnBlocksSrc, replace_locals_as_inj in *.
           intuition.
   (*sm_valid*)
     red. rewrite replace_locals_DOM, replace_locals_RNG. apply SMV.
(*Shared*)
  eapply inject_shared_replace_locals; try eassumption.
  subst; trivial.
Qed.

Lemma match_frames_restrict_sm mu X s ts: forall
     (MS: match_frames mu s ts)
     (HX: forall b : block, vis mu b = true -> X b = true)
     (WD: SM_wd mu),
     match_frames (restrict_sm mu X) s ts.
Proof. intros.
  inv MS; econstructor; eauto.
    rewrite restrict_sm_all, vis_restrict_sm.
    rewrite restrict_nest; trivial.
  destruct SPlocal; split.
    rewrite restrict_sm_local. eapply val_inject_incr; try eassumption.
      red; intros. eapply restrictI_Some; try eassumption.
      apply HX. unfold vis. destruct (local_DomRng _ WD _ _ _ H1).
      rewrite H2; trivial.
    rewrite restrict_sm_all. intros; subst.
      destruct (H0 _ _ (eq_refl _)) as [? ?]; clear H0.
      inv H. 
      eexists. eapply restrictI_Some; try eassumption.
      rewrite (local_in_all _ WD _ _ _ H3) in H1. inv H1.
      apply HX. unfold vis. destruct (local_DomRng _ WD _ _ _ H3).
      rewrite H; trivial.
Qed.

Lemma match_frames_forall_restrict_sm mu X s ts: forall
      (H: list_forall2 (match_frames mu) s ts)
      (HX: forall b : block, vis mu b = true -> X b = true)
      (WD: SM_wd mu),
     list_forall2 (match_frames (restrict_sm mu X)) s ts.
Proof. intros.
  induction H; econstructor; eauto.
  eapply match_frames_restrict_sm; eauto.
Qed.

Lemma match_frames_replace_externs mu FS FT s ts: forall
     (MS: match_frames mu s ts)
     (HFS: forall b, vis mu b = true -> 
          locBlocksSrc mu b || FS b = true),
     match_frames (replace_externs mu FS FT) s ts.
Proof. intros MS HFS. inv MS; econstructor; eauto.
  eapply regset_incr; try eassumption.
    rewrite replace_externs_as_inj, replace_externs_vis.
    red; intros. destruct (restrictD_Some _ _ _ _ _ H).
      apply HFS in H1. 
      apply restrictI_Some; trivial.
    destruct SPlocal; split; intros. 
     rewrite replace_externs_local; trivial. 
     rewrite replace_externs_as_inj; eauto. 
Qed.

Lemma match_frames_forall_replace_externs mu FS FT s ts:
      list_forall2 (match_frames mu) s ts ->
     (forall b, vis mu b = true -> locBlocksSrc mu b || FS b = true) ->
     list_forall2 (match_frames (replace_externs mu FS FT)) s ts.
Proof. intros.
  induction H; econstructor; eauto.
  eapply match_frames_replace_externs; eauto.
Qed.

Lemma match_frames_replace_locals mu PS PT s ts: forall
      (MS: match_frames mu s ts),
      match_frames (replace_locals mu PS PT) s ts.
Proof. intros. inv MS; econstructor; eauto.
  rewrite replace_locals_as_inj, replace_locals_vis. trivial.
  destruct SPlocal; split; intros. 
     rewrite replace_locals_local; trivial. 
     rewrite replace_locals_as_inj; eauto. 
Qed.

Lemma match_frames_forall_replace_locals mu PS PT s ts: forall
      (MS: list_forall2 (match_frames mu) s ts),
      list_forall2 (match_frames (replace_locals mu PS PT)) s ts.
Proof. intros.
  induction MS; econstructor; eauto.
  eapply match_frames_replace_locals; eauto.
Qed.

Lemma match_frames_forall_extern_incr mu nu s ts: forall
      (MS: list_forall2 (match_frames mu) s ts)
      (EXT: extern_incr mu nu) (WDnu: SM_wd nu),
      list_forall2 (match_frames nu) s ts.
Proof. intros.
  induction MS; econstructor; eauto.
  eapply match_frames_extern_incr; eauto.
Qed.

Lemma match_frames_restrict_sm_incr mu nu X Y s ts: forall
     (MS: match_frames (restrict_sm mu X) s ts)
     (INC: inject_incr (as_inj mu) (as_inj nu))
     (HX: forall b, vis mu b = true -> X b = true)
     (HY: forall b, vis nu b = true -> Y b = true)
     (H_mu_nu: forall b, vis mu b = true -> vis nu b = true)
     (HXY: inject_incr (restrict (local_of mu) X) (restrict (local_of nu) Y)),
     match_frames (restrict_sm nu Y) s ts.
Proof. intros.
  inv MS; econstructor; eauto.
    rewrite restrict_sm_all, vis_restrict_sm.
    rewrite restrict_sm_all, vis_restrict_sm in AGREE.
    eapply regset_incr; try eassumption.
    rewrite restrict_nest; trivial.
    rewrite restrict_nest; trivial.
      red; intros b tb delta Hb.
         destruct (restrictD_Some _ _ _ _ _ Hb).
         eapply restrictI_Some. apply INC; eassumption.
         apply H_mu_nu. trivial.
  destruct SPlocal; split.
    rewrite restrict_sm_local in *. eapply val_inject_incr; try eassumption.
    rewrite restrict_sm_all in *. intros; subst.
      destruct (H0 _ _ (eq_refl _)) as [? ?]; clear H0.
      inv H. 
      eexists. eapply restrictI_Some.
        eapply INC. eapply restrictD_Some. eassumption.
      rewrite restrict_sm_local in H3.
      specialize (HXY _ _ _ H3). 
      eapply (restrictD_Some _ _ _ _ _ HXY).
Qed.

Lemma match_frames_forall_restrict_sm_incr mu nu X Y s ts: forall
     (MS: list_forall2 (match_frames (restrict_sm mu X)) s ts)
     (INC: inject_incr (as_inj mu) (as_inj nu))
     (HX: forall b, vis mu b = true -> X b = true)
     (HY: forall b, vis nu b = true -> Y b = true)
     (H_mu_nu: forall b, vis mu b = true -> vis nu b = true)
     (HXY: inject_incr (restrict (local_of mu) X) (restrict (local_of nu) Y)),
     list_forall2 (match_frames (restrict_sm nu Y)) s ts.
Proof. intros.
  induction MS; econstructor; eauto.
  eapply match_frames_restrict_sm_incr; eauto.
Qed.

Lemma MATCH_afterExternal: forall
      (GDE : genvs_domain_eq ge tge)
      mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH mu st1 m1 st2 m2)
      (AtExtSrc : at_external (rtl_eff_sem hf) st1 = Some (e, ef_sig, vals1))
      (AtExtTgt : at_external (rtl_eff_sem hf) st2 = Some (e', ef_sig', vals2))
      (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
      (pubSrc' : block -> bool)
      (pubSrcHyp : pubSrc' =
                 (fun b : block => 
                 locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
      (pubTgt' : block -> bool)
      (pubTgtHyp: pubTgt' =
                 (fun b : block => 
                 locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
       nu (NuHyp: nu = replace_locals mu pubSrc' pubTgt')
       nu' ret1 m1' ret2 m2' 
       (INC: extern_incr nu nu')
       (SEP: sm_inject_separated nu nu' m1 m2)
       (WDnu': SM_wd nu')
       (SMvalNu': sm_valid nu' m1' m2')
       (MemInjNu': Mem.inject (as_inj nu') m1' m2')
       (RValInjNu': val_inject (as_inj nu') ret1 ret2)
       (FwdSrc: mem_forward m1 m1')
       (FwdTgt: mem_forward m2 m2')
       (frgnSrc' : block -> bool)
       (frgnSrcHyp: frgnSrc' =
             (fun b : block => DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
       (frgnTgt' : block -> bool)
       (frgnTgtHyp: frgnTgt' =
            (fun b : block => DomTgt nu' b &&
             (negb (locBlocksTgt nu' b) && REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
       mu' (Mu'Hyp: mu' = replace_externs nu' frgnSrc' frgnTgt')
       (UnchPrivSrc: Mem.unchanged_on
               (fun b z => locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
       (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
  exists st1' st2',
  after_external (rtl_eff_sem hf) (Some ret1) st1 =Some st1' /\
  after_external (rtl_eff_sem hf) (Some ret2) st2 = Some st2' /\
  MATCH mu' st1' m1' st2' m2'.
Proof. intros.
simpl.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H0. simpl.
 simpl in AtExtTgt. inv AtExtTgt.
 destruct (observableEF_dec hf e0); inv H0; inv H1.
 eexists. eexists.
    split. reflexivity.
    split. reflexivity.
 simpl in *.
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
assert (PHnu': meminj_preserves_globals (Genv.globalenv prog) (as_inj nu')).
    subst. clear - INC SEP PG Glob WDmu WDnu'.
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
      destruct (frgnSrc _ WDmu _ (Glob _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      apply foreign_in_extern; eassumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char2 in H.
          rewrite H. intuition.
      destruct (frgnSrc _ WDmu _ (Glob _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
      apply foreign_in_extern; eassumption.
    eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
      remember (as_inj mu b1) as d.
      destruct d; apply eq_sym in Heqd.
        destruct p. 
        apply extern_incr_as_inj in INC; trivial.
        rewrite replace_locals_as_inj in INC.
        rewrite (INC _ _ _ Heqd) in H0. trivial.
      destruct SEP as [SEPa _].
        rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in SEPa. 
        destruct (SEPa _ _ _ Heqd H0).
        destruct (as_inj_DomRng _ _ _ _ PGb WDmu).
        congruence.
assert (RR1: REACH_closed m1'
  (fun b : Values.block =>
   locBlocksSrc nu' b
   || DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
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
          eapply VAL. unfold DOM, DomSrc. rewrite Heql. intuition.
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
  (*case DomSrc nu' b' &&
    (negb (locBlocksSrc nu' b') &&
     REACH m1' (exportedSrc nu' (ret1 :: nil)) b') = true*)
    destruct IHL. congruence.
    apply andb_true_iff in H. simpl in H. 
    destruct H as [DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchLOOR UnchPrivSrc.
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
     intros. specialize (Glob _ H).
       assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
          rewrite replace_locals_frgnBlocksSrc in FSRC.
       rewrite FSRC in Glob.
       rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ Glob). 
       apply andb_true_iff; simpl.
        split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ Glob). intuition.
          apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ Glob). intuition.
split.
(*match_states*) (*rewrite replace_externs_vis in *. *)
  clear INCvisNu' UnchLOOR SEP UnchPrivSrc.
  econstructor; try eassumption. 
  { (*list_match_frames*)
    eapply match_frames_forall_restrict_sm_incr. 
      eassumption.
      rewrite replace_externs_as_inj. 
        red; intros. eapply extern_incr_as_inj. eassumption. eassumption. 
          rewrite replace_locals_as_inj. trivial. 
      trivial. trivial.
      rewrite replace_externs_vis. intros.
        exploit extern_incr_vis; try eassumption.
        rewrite replace_locals_vis; intros. rewrite H0 in H.
        clear H0.
        unfold vis in H. remember (locBlocksSrc nu' b) as q.    
        destruct q; simpl in *; trivial.
        apply andb_true_iff; split.
          unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H). intuition. 
          apply REACH_nil. unfold exportedSrc. rewrite sharedSrc_iff_frgnpub, H; trivial. intuition.
      rewrite replace_externs_local, replace_externs_vis.
        assert (LOC: local_of mu = local_of nu').
          red in INC. rewrite replace_locals_local in INC. eapply INC.
        rewrite <- LOC in *. 
        red; intros. destruct (restrictD_Some _ _ _ _ _ H); clear H.
        apply restrictI_Some; trivial.
        destruct (local_DomRng _ WDmu _ _ _ H0).
        assert (LS: locBlocksSrc mu = locBlocksSrc nu').
          red in INC. rewrite replace_locals_locBlocksSrc in INC. eapply INC.
        rewrite <- LS, H. trivial. }
  { rewrite restrict_sm_all, vis_restrict_sm,
       replace_externs_as_inj, replace_externs_vis. 
        rewrite restrict_nest; trivial.
        inv RValInjNu'; econstructor; try reflexivity.
        apply restrictI_Some; trivial.
        remember (locBlocksSrc nu' b1) as q.
        destruct q; simpl; trivial.
        apply andb_true_iff; split.
          eapply as_inj_DomRng; eassumption.
          apply REACH_nil. unfold exportedSrc. 
            apply orb_true_iff; left.
            solve[rewrite getBlocks_char; eexists; left; reflexivity]. } 
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
unfold vis in *.
  rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
  replace_externs_as_inj in *.
intuition.
(*as in selectionproofEFF*)
  red; intros. destruct (GFP _ _ H1). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed. 

Lemma MATCH_initial: forall v 
  (vals1 : list val) c1 (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (Ini : initial_core (rtl_eff_sem hf) ge v vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (J: forall b1 b2 d, j b1 = Some (b2, d) -> 
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (GFI: globalfunction_ptr_inject ge j)
  (GDE: genvs_domain_eq ge tge)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core (rtl_eff_sem hf) tge v vals2 = Some c2 /\
  MATCH 
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2. 
Proof. intros.
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1
           (sig_args (funsig (Internal f))) && val_casted.vals_defined vals1). 
  2: solve[intros Heq; rewrite Heq in H1; inv H1].
  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  intros l _. 
  2: simpl; solve[rewrite andb_comm; inversion 2]. 
  simpl. rewrite andb_comm. simpl. intros H1.
  intros Heq; rewrite Heq in H1; inv H1.

  exploit function_ptr_translated; eauto. intros FP.
  exists (RTL_Callstate nil (transf_fundef (Internal f)) vals2).
  split.
    subst. inv Heqzz. unfold tge in FP. inv FP. rewrite H1. simpl.
    simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.

    assert (Zlength vals2 = Zlength vals1) as ->. 
    { apply forall_inject_val_list_inject in VInj. clear - VInj. 
      induction VInj; auto. rewrite !Zlength_cons, IHVInj; auto. }

    change (fn_sig f) with (funsig (Internal (transf_function f))).
    assert (val_casted.val_has_type_list_func vals2 
             (sig_args (funsig (Internal (transf_function f))))=true) as ->.
    { eapply val_casted.val_list_inject_hastype; eauto.
      eapply forall_inject_val_list_inject; eauto.
      destruct (val_casted.vals_defined vals1); auto.
      rewrite andb_comm in Heq; simpl in Heq. solve[inv Heq].
      simpl. simpl in Heq. apply andb_true_iff in Heq; eapply Heq. }
    assert (val_casted.vals_defined vals2=true) as ->.
    { eapply val_casted.val_list_inject_defined.
      eapply forall_inject_val_list_inject; eauto.
      destruct (val_casted.vals_defined vals1); auto.
      rewrite andb_comm in Heq; inv Heq. }
  simpl; revert H0; case_eq 
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  solve[simpl; auto].
  intros CONTRA. solve[elimtype False; auto].
  intros CONTRA. solve[elimtype False; auto].

  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    eapply match_callstates; try eassumption.
    constructor.
    { rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
      rewrite initial_SM_as_inj.
        unfold vis, initial_SM; simpl.
        apply forall_inject_val_list_inject.
        eapply restrict_forall_vals_inject. assumption.
          intros. apply REACH_nil. 
          rewrite orb_true_iff. right. trivial. }
  rewrite initial_SM_as_inj.
  intuition.
Qed.

Theorem transl_program_correct:
  SM_simulation.SM_simulation_inject 
    (rtl_eff_sem hf) (rtl_eff_sem hf) ge tge.
Proof.
intros.
assert (GDE:= GDE_lemma).
 eapply simulations_lemmas.inj_simulation_plus with
  (match_states:=fun x mu st m st' m' => MATCH mu st m st' m')
  (measure:=fun x => O).
(*genvs_dom_eq*)
  assumption.
(*match_wd*)
  intros; apply H.
(*match_visible*)
  intros. apply H.
(*match_restrict*)
  intros x. apply MATCH_restrict.
(*match_valid*)
  intros. apply H.
(*match_genv*)
  intros x. eapply MATCH_PG. 
(*initial_core*)
  intros; exploit (MATCH_initial _ _ _ m1 j vals2 m2 DomS DomT H); eauto.
(*halted*)
  { intros. destruct H as [MTCH CD]; subst.
    destruct CD as [RC [PG [GFP [Glob [VAL [WD INJ]]]]]].
    revert H0. simpl. destruct c1; try solve[inversion 1]. inversion 1.
    revert H1. destruct stack; try solve[inversion 1].
    intros. inv H1. 
    inv MTCH.
    exists tv.
    split; trivial.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in RV; trivial.
    split; trivial.
    simpl. inv STACKS. trivial. }
(*atExternal*)
  { apply MATCH_atExternal. } 
(*afterExternal*)
  { apply MATCH_afterExternal. assumption. }
(*effcorediagram*)
{ intros. exploit MATCH_effcore_diagram; try eassumption.
  intros [st2' [m2' [U2 [mu' [CS' [INC [SEP
     [LocAlloc [MTCH' [WD' [SMV' HU2]]]]]]]]]]].
  exists st2', m2', mu'.
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  exists U2.
  split. left. apply effstep_plus_one. trivial.
  assumption. }
Qed.

End PRESERVATION.



 

  

