
(** Correctness of instruction selection *)

Require Import Coqlib.
Require Import Values.
Require Import Memory.
Require Export Axioms.
Require Import Errors.
Require Import Events.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Export Maps.

Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.
Require Import SelectDiv.
Require Import SelectLongNEW.
Require Import SelectionNEW.
Require Import SelectOpproof.
Require Import SelectDivproof.
Require Import BuiltinEffects.
Require Import SelectLongproofEFF.

Require Import mem_lemmas.
Require Import core_semantics.
Require Import core_semantics_lemmas.
Require Import effect_semantics.
Require Import StructuredInjections.
Require Import reach.
Require Import effect_simulations.
Require Import effect_properties.
Require Import effect_simulations_lemmas.

Require Import Cminor_coop.
Require Import Cminor_eff.
Require Import CminorSel_coop.
Require Import CminorSel_eff.
Require Import Floats.

Require Import I64Helpers.
(*Require Import Selectionproof.*)

Open Local Scope cminorsel_scope.

(** * Correctness of the instruction selection functions for expressions *)

Section SILENT.

(*NEW*) Variable hf : I64Helpers.helper_functions.

Lemma silent_addimm (ge: Genv.t fundef unit) n: 
       forall e, silent hf ge e -> silent hf ge (addimm n e). 
Proof. intros e.
  unfold addimm. intros. 
  destruct (Int.eq n Int.zero); simpl; auto. 
  destruct (addimm_match e); simpl; auto. 
Qed. 

Lemma silent_add ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
       silent hf ge (add e1 e2). 
Proof. intros.
  unfold add. 
  destruct (add_match e1 e2); simpl in *;
    try eapply silent_addimm; eauto; intuition;
  split; trivial; try apply H; try apply H1. 
Qed.  

Lemma silent_shlimm ge i: forall e, silent hf ge e ->
   silent hf ge (shlimm e i).
Proof. intros. unfold shlimm.
    destruct (Int.eq i Int.zero); simpl; eauto. 
    destruct (shlimm_match e); simpl; auto. 
      destruct (Int.ltu (Int.add i n1) Int.iwordsize); simpl; auto.
      destruct (shift_is_scale i); simpl; auto.
    destruct (shift_is_scale i); simpl; auto.  
Qed.

Lemma silent_splitlong ge f: forall e, silent hf ge e ->
    (forall h l, silent hf ge h -> silent hf ge l -> silent hf ge (f h l)) -> 
   silent hf ge (splitlong e f).
Proof. intros. unfold splitlong.
    destruct (splitlong_match e); simpl in *; eauto.
    destruct H as [? [? _]]. 
    apply H0; simpl; eauto. 
    split; eauto. apply H0; simpl; eauto.
Qed.

Lemma silent_shrimm ge i: forall e, silent hf ge e ->
   silent hf ge (shrimm e i).
Proof. intros. unfold shrimm.
    destruct (Int.eq i Int.zero); simpl; intuition. 
    destruct (shrimm_match e); simpl; eauto.
    destruct H. 
      destruct (Int.ltu (Int.add i n1) Int.iwordsize); simpl; repeat split; auto.
Qed.

Lemma silent_shruimm ge i: forall e, silent hf ge e ->
   silent hf ge (shruimm e i).
Proof. intros. unfold shruimm.
    destruct (Int.eq i Int.zero); simpl; repeat split; eauto. 
    destruct (shruimm_match e); simpl; repeat split; auto. 
    destruct H.
      destruct (Int.ltu (Int.add i n1) Int.iwordsize); simpl; repeat split; auto.
Qed.

Lemma silent_shrximm ge i: forall e, silent hf ge e ->
   silent hf ge (shrximm e i).
Proof. intros. unfold shrximm.
    destruct (Int.eq i Int.zero); simpl; repeat split; eauto. 
Qed.

Lemma silent_mulimm_base ge n: forall e, silent hf ge e ->
      silent hf ge (mulimm_base n e).
Proof. intros.
    unfold mulimm_base. destruct (Int.one_bits n); simpl; eauto.
    destruct l; simpl; repeat split; auto.
      eapply silent_shlimm; eauto. 
    destruct l; simpl; split; eauto. 
     eapply silent_add.
      eapply silent_shlimm; simpl; eauto. 
      eapply silent_shlimm; simpl; eauto.
Qed.  

Lemma silent_mulimm ge n: forall e, silent hf ge e ->
       silent hf ge (mulimm n e). 
Proof. intros e.
  unfold mulimm. intros. 
  destruct (Int.eq n Int.zero); simpl; auto. 
  destruct (Int.eq n Int.one); simpl; auto. 
  destruct (mulimm_match e); simpl; auto.
  simpl in *. destruct H as [H _]. 
    eapply silent_addimm.
    eapply silent_mulimm_base; eauto.
    eapply silent_mulimm_base; eauto.  
Qed. 

Lemma silent_mul ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
       silent hf ge (mul e1 e2). 
Proof. intros; unfold mul. 
  destruct (mul_match e1 e2); simpl in *;
    try solve [apply silent_mulimm; eauto]. 
   intuition.
Qed.  

Lemma silent_sub ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
       silent hf ge (sub e1 e2). 
Proof. intros; unfold sub. 
  destruct (sub_match e1 e2); simpl in *;
   try solve [apply silent_addimm; simpl in *; intuition].
   auto. 
Qed.  

Lemma silent_lift_expr ge: forall e p, silent hf ge e ->
       silent hf ge (lift_expr p e)
with silent_lift_exprlist ge: forall al p, silentExprList hf ge al ->
   silentExprList hf ge (lift_exprlist p al)
with silent_lift_condexpr ge: forall con p, silentCondExpr hf ge con ->
   silentCondExpr hf ge (lift_condexpr p con).
Proof.
  induction e; intros; simpl in *; auto.
    destruct H as [HC [HE1 HE2]]. 
    split; eauto. 
  
    destruct H. split; eauto. 
  
    destruct (le_gt_dec p n); simpl; trivial. 

    destruct H as [? ?]. 
    split; auto. 

    destruct H. split. auto.
    destruct (Genv.find_symbol ge i); simpl in *; trivial.

  induction al; intros; simpl in *; auto.
    destruct H.  split; eauto.

  induction con; intros; simpl in *; auto. 
    destruct H as [Hcon [HC1 HC2]].
    split. auto. split; auto.

    destruct H. split; auto.
Qed. 

Lemma silent_lift ge: forall e, silent hf ge e ->
       silent hf ge (lift e). 
Proof. intros; unfold lift.  
  apply silent_lift_expr; trivial. 
Qed.  

Lemma silent_mull_base ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (mull_base hf e1 e2).
Proof. intros.
  unfold mull_base.
  unfold splitlong2; simpl. 
  destruct (splitlong2_match e1 e2).
    destruct H as [? [? _]].
    destruct H0 as [? [? _]]. 
    repeat split; eauto. 
     simpl. constructor.
     (*apply obs_ef. econstructor. *)
     apply silent_add; simpl. 
                apply silent_add; simpl; auto.
                apply silent_mul; simpl; auto. 
                apply silent_lift; trivial. 
                apply silent_lift; trivial. 
                apply silent_mul; simpl; auto. 
                apply silent_lift; trivial. 
                apply silent_lift; trivial. 
    destruct H as [? [? _]].
      repeat split; eauto.
     simpl. constructor.
     (*apply obs_ef. econstructor. *)
      apply silent_lift; trivial. 
      apply silent_add; simpl. 
      apply silent_add. split; eauto. simpl. trivial. 
       simpl; trivial. 
      apply silent_mul; simpl. 
                apply silent_lift; trivial. 
                apply silent_lift; trivial. 
        split; trivial.
      apply silent_mul; simpl. 
                apply silent_lift; trivial. 
                apply silent_lift; trivial. 
        split; trivial.
    destruct H0 as [? [? _]].
      repeat split; eauto.
     simpl. constructor.
     (*apply obs_ef. econstructor. *)
      apply silent_lift; trivial. 
      apply silent_add; simpl. 
      apply silent_add. split; eauto. simpl. trivial. 
       simpl; trivial. 
      apply silent_mul; simpl. split; trivial.
                apply silent_lift; trivial. 
                apply silent_lift; trivial. 
      apply silent_mul; simpl. split; trivial.
                apply silent_lift; trivial. 
                apply silent_lift; trivial. 
    repeat split; eauto. 
      apply silent_lift; trivial. 
     simpl. constructor.
     (*apply obs_ef. econstructor. *)   
Qed. 

Lemma silent_divsmul ge z1 z2: silent hf ge (divs_mul z1 z2).
Proof.
     unfold divs_mul. apply silent_add.
     apply silent_shrimm.
     destruct (zlt z2 Int.half_modulus); simpl. auto. auto.
     apply silent_shruimm; simpl; eauto.
Qed.

Lemma silent_divumul ge z1 z2: silent hf ge (divu_mul z1 z2).
Proof.
     unfold divu_mul. apply silent_shruimm. simpl. auto.
Qed.

Lemma silent_divsimm ge n: forall e, silent hf ge e ->
      silent hf ge (divsimm e n).
Proof. intros. unfold divsimm.
  destruct (Int.is_power2 n); simpl.
    destruct (Int.ltu i (Int.repr 31)); simpl. 
     eapply silent_shrximm; eauto.
     repeat split; auto.      
   destruct (divs_mul_params (Int.signed n)); simpl.
     destruct p; simpl. split; trivial.
     apply silent_divsmul; auto.
   repeat split; auto.  
Qed.

Lemma silent_modsimm ge n: forall e, silent hf ge e ->
      silent hf ge (modsimm e n).
Proof. intros. unfold modsimm.
  destruct (Int.is_power2 n); simpl.
    destruct (Int.ltu i (Int.repr 31)); simpl. 
     repeat split; auto.      
     apply silent_mulimm. apply silent_shrximm; simpl. auto.
   repeat split; auto.  
   destruct (divs_mul_params (Int.signed n)); simpl.
     destruct p; simpl. repeat split; auto. 
     apply silent_mulimm.
     apply silent_divsmul. 
   repeat split; auto.  
Qed.

Lemma silent_andimm ge n: forall e, silent hf ge e ->
      silent hf ge (andimm n e).
Proof. intros. unfold andimm.
  destruct (Int.eq n Int.zero); simpl. trivial. 
  destruct (Int.eq n Int.mone); simpl; trivial. 
  destruct (andimm_match e); simpl; trivial. 
  split; trivial. 
Qed.

Lemma silent_orimm ge n: forall e, silent hf ge e ->
      silent hf ge (orimm n e).
Proof. intros. unfold orimm.
  destruct (Int.eq n Int.zero); simpl. trivial. 
  destruct (Int.eq n Int.mone); simpl; trivial. 
  destruct (orimm_match e); simpl; trivial. 
  split; trivial. 
Qed.

Lemma silent_xorimm ge n: forall e, silent hf ge e ->
      silent hf ge (xorimm n e).
Proof. intros. unfold xorimm.
  destruct (Int.eq n Int.zero); simpl. trivial. 
  destruct (xorimm_match e); simpl; trivial. 
  split; trivial. 
Qed.

Lemma silent_moduimm ge n: forall e, silent hf ge e ->
      silent hf ge (moduimm e n).
Proof. intros. unfold moduimm.
  destruct (Int.is_power2 n); simpl.      
    apply silent_andimm; auto.
   destruct (divu_mul_params (Int.unsigned n)); simpl.
     destruct p; simpl. repeat split; auto. 
     apply silent_mulimm.
     apply silent_divumul. 
   repeat split; auto.  
Qed.

Lemma silent_divuimm ge n: forall e, silent hf ge e ->
      silent hf ge (divuimm e n).
Proof. intros. unfold divuimm.
  destruct (Int.is_power2 n); simpl.
    apply silent_shruimm; auto.
   destruct (divu_mul_params (Int.unsigned n)); simpl.
     destruct p; simpl. split; trivial.
     unfold divu_mul. apply silent_shruimm. simpl. auto.
   repeat split; auto.  
Qed.

Lemma silent_divfimm ge n: forall e, silent hf ge e ->
      silent hf ge (divfimm e n).
Proof. intros. unfold divfimm.
  destruct (Float.exact_inverse n); simpl.
   repeat split; auto.  
   repeat split; auto.  
Qed.

Lemma silent_divu ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (divu e1 e2).
Proof. intros. unfold divu.
  destruct (divu_match e2); simpl in *. 
  apply silent_divuimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_divs ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (divs e1 e2).
Proof. intros. unfold divs.
  destruct (divs_match e2); simpl in *. 
  apply silent_divsimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_modu ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (modu e1 e2).
Proof. intros. unfold modu.
  destruct (modu_match e2); simpl in *. 
  apply silent_moduimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_mods ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (mods e1 e2).
Proof. intros. unfold mods.
  destruct (mods_match e2); simpl in *. 
  apply silent_modsimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_and ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (and e1 e2).
Proof. intros. unfold and.
  destruct (and_match e1 e2); simpl in *. 
  apply silent_andimm; auto. 
  apply silent_andimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_or ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (or e1 e2).
Proof. intros. unfold or.
  destruct (or_match e1 e2); simpl in *. 
  apply silent_orimm; auto. 
  apply silent_orimm; auto. 
  destruct (Int.eq (Int.add n1 n2) Int.iwordsize); simpl.
    destruct (same_expr_pure t1 t2); simpl; auto.
    destruct H; destruct H0; repeat split; eauto.
    destruct H; destruct H0; repeat split; eauto.
  destruct (Int.eq (Int.add n1 n2) Int.iwordsize); simpl.
    destruct (same_expr_pure t1 t2); simpl; auto.
    destruct H; destruct H0; repeat split; eauto.
    destruct H; destruct H0; repeat split; eauto.
  repeat split; auto.
Qed.

Lemma silent_xor ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (xor e1 e2).
Proof. intros. unfold xor.
  destruct (xor_match e1 e2); simpl in *. 
  apply silent_xorimm; auto. 
  apply silent_xorimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_shl ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (shl e1 e2).
Proof. intros. unfold shl.
  destruct (shl_match e2); simpl in *. 
  apply silent_shlimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_shr ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (shr e1 e2).
Proof. intros. unfold shr.
  destruct (shr_match e2); simpl in *. 
  apply silent_shrimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_shru ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (shru e1 e2).
Proof. intros. unfold shru.
  destruct (shru_match e2); simpl in *. 
  apply silent_shruimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_divf ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (divf e1 e2).
Proof. intros. unfold divf.
  destruct (divf_match e2); simpl in *. 
  apply silent_divfimm; auto. 
  repeat split; auto.
Qed.

Lemma silent_addl ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (addl hf e1 e2).
Proof. intros. unfold addl.
  destruct (is_longconst e1); simpl in *. 
    destruct (is_longconst e2); simpl in *. repeat split; trivial.
    destruct (Int64.eq i Int64.zero); trivial.
    split. simpl. constructor.
       (*apply obs_ef. econstructor. *)
    repeat split; trivial. 
   destruct (is_longconst e2).
    destruct (Int64.eq i Int64.zero); trivial.
    split. constructor.
       (*apply obs_ef. econstructor. *)
      (*destruct ef; try inv H. *)
    repeat split; trivial.
  split. constructor.
       (*apply obs_ef. econstructor. *)
    repeat split; trivial.
Qed.

Lemma silent_negl ge: forall e, silent hf ge e ->
      silent hf ge (negl hf e).
Proof. intros. unfold negl.
  destruct (is_longconst e). repeat split; trivial.
    split. constructor.
       (*apply obs_ef. econstructor. *)
    repeat split; trivial. 
Qed.

Lemma silent_subl ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (subl hf e1 e2).
Proof. intros. unfold subl.
  destruct (is_longconst e1).
    destruct (is_longconst e2); repeat split; trivial.
    destruct (Int64.eq i Int64.zero); trivial.
    apply silent_negl; auto. 
    split. constructor.
       (*apply obs_ef. econstructor. *)
    repeat split; trivial. 
  destruct (is_longconst e2).
    destruct (Int64.eq i Int64.zero). repeat split; trivial.
    split. constructor.
       (*apply obs_ef. econstructor. *) 
    repeat split; trivial. 
  split. constructor.
       (*apply obs_ef. econstructor. *)
    repeat split; trivial. 
Qed.

Lemma divsdummy: Val.divls (Vlong Int64.one) (Vlong Int64.one) 
        = Some (Vlong (Int64.divs Int64.one Int64.one)). 
Proof. 
 assert (Int64.eq Int64.one Int64.zero = false). 
   apply Int64.eq_false. discriminate. 
 simpl. rewrite H; simpl. 
 assert (Int64.eq Int64.one (Int64.repr Int64.min_signed) = false). 
   apply Int64.eq_false. discriminate. 
 rewrite H0; simpl. trivial.
Qed. 

Lemma silent_divl (ge: Genv.t fundef unit) 
                  (HC: i64_helpers_correct ge hf) e1 e2:
      silent hf ge e1 -> silent hf ge e2 -> silent hf ge (divl hf e1 e2).
Proof. intros. unfold divl, binop_long.
  assert (IMPL: forall x y z : val,
        Val.divls x y = Some z ->
        helper_implements ge hf (i64_sdiv hf) sig_ll_l (x :: y :: nil) z)
      by eapply HC. 
  destruct (IMPL _ _ _ divsdummy) 
     as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
  destruct (is_longconst e1); simpl in *.
    destruct (is_longconst e2); simpl in *. repeat split; trivial.
    split. repeat split; trivial. 
    unfold fundef. rewrite FOUND, PTR.
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
    split. repeat split; trivial.
    unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma silent_lowlong ge: forall e, silent hf ge e ->
   silent hf ge (lowlong e).
Proof. intros. unfold lowlong.
    destruct (lowlong_match e); simpl in *; eauto. eapply H.
Qed.
        
Lemma silent_shllimm ge (HC:i64_helpers_correct ge hf) i e:
      silent hf ge e -> silent hf ge (shllimm hf e i).
Proof. intros. unfold shllimm.
    destruct (Int.eq i Int.zero); simpl; eauto. 
    destruct (Int.ltu i Int.iwordsize); simpl; auto. 
      apply silent_splitlong. trivial. 
        intros; simpl.  
          split. apply silent_or. apply silent_shlimm; trivial.
          apply silent_shruimm; trivial.
          split; trivial. apply silent_shlimm; trivial.
    destruct (Int.ltu i Int64.iwordsize'); simpl.
       split. apply silent_shlimm. apply silent_lowlong; trivial.
       split; trivial.
    split. repeat split; trivial.
    assert (IMPL: forall x y : val,
        helper_implements ge hf (i64_shl hf) sig_li_l 
          (x :: y :: nil) (Val.shll x y)) by eapply HC.
   destruct (IMPL Vundef Vundef)
     as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
   unfold fundef; rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma silent_mullimm ge (HC: i64_helpers_correct ge hf) n e:
      silent hf ge e -> silent hf ge (mullimm hf e n). 
Proof. intros. unfold mullimm. 
  destruct (Int64.eq n Int64.zero); simpl; auto. 
  destruct (Int64.eq n Int64.one); simpl; auto. 
  destruct (Int64.is_power2 n); simpl; auto.
    eapply silent_shllimm; trivial. 
    apply silent_mull_base; simpl; trivial. auto. 
Qed. 

Lemma silent_mull ge (HC: i64_helpers_correct ge hf) e1 e2: 
      silent hf ge e1 -> silent hf ge e2 -> silent hf ge (mull hf e1 e2).
Proof. intros. unfold mull.
  destruct (is_longconst e1); simpl in *. 
    destruct (is_longconst e2); simpl in *. repeat split; trivial.
    apply silent_mullimm; auto. 
  destruct (is_longconst e2); simpl in *. 
    apply silent_mullimm; auto. 
    apply silent_mull_base; trivial. 
Qed.

Lemma silent_highlong ge e: 
      silent hf ge e -> silent hf ge (highlong e).
Proof. intros; unfold highlong.
  destruct (highlong_match e); simpl in *. 
    eapply H. 
    split; trivial. 
Qed. 

Lemma silent_shrlimm ge (HC:i64_helpers_correct ge hf) i e:
      silent hf ge e -> silent hf ge (shrlimm hf e i).
Proof. intros. unfold shrlimm.
    destruct (Int.eq i Int.zero); simpl; eauto. 
    destruct (Int.ltu i Int.iwordsize); simpl; auto. 
      apply silent_splitlong. trivial. 
        intros; simpl.  
          split. apply silent_shrimm; trivial. 
          split; trivial. 
          apply silent_or. apply silent_shruimm; trivial.
          apply silent_shlimm; trivial.
    destruct (Int.ltu i Int64.iwordsize'); simpl; auto.
       split. apply silent_highlong; trivial.
       split. apply silent_shrimm; simpl; auto.
       split; trivial. apply silent_shrimm; simpl; auto. 
    split. repeat split; trivial.
    assert (IMPL: forall x y : val,
        helper_implements ge hf (i64_sar hf) sig_li_l 
          (x :: y :: nil) (Val.shrl x y)) by eapply HC.
    destruct (IMPL Vundef Vundef)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
    unfold fundef; rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma silent_shrluimm ge (HC: i64_helpers_correct ge hf) n e:
       silent hf ge e -> silent hf ge (shrluimm hf e n).
Proof. intros; unfold shrluimm.
  destruct (Int.eq n Int.zero); simpl; trivial.
  destruct (Int.ltu n Int.iwordsize); simpl.
    apply silent_splitlong; trivial.
    intros. unfold makelong. simpl. 
       split. apply silent_shruimm; trivial.
       split; trivial. 
       apply silent_or. apply silent_shruimm; trivial.
       apply silent_shlimm; trivial.
  destruct (Int.ltu n Int64.iwordsize'); simpl.
    repeat split; trivial.
    apply silent_shruimm; trivial.
    apply silent_highlong; trivial.
  split. repeat split; trivial.
    assert (IMPL: forall x y : val,
        helper_implements ge hf (i64_shr hf) sig_li_l 
          (x :: y :: nil) (Val.shrlu x y)) by eapply HC.
    destruct (IMPL Vundef Vundef)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
    unfold fundef; rewrite FOUND, PTR.  
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma divlu_dummy:
      Val.divlu (Vlong Int64.one) (Vlong Int64.one) = 
      Some (Vlong (Int64.divu Int64.one Int64.one)).
Proof.
assert (Int64.eq Int64.one Int64.zero = false). 
  apply Int64.eq_false. discriminate. 
simpl; rewrite H. trivial. 
Qed.

Lemma silent_divlu ge (HC:i64_helpers_correct ge hf) e1 e2:
      silent hf ge e1 -> silent hf ge e2 -> silent hf ge (divlu hf e1 e2).
Proof. intros. unfold divlu.
    assert (IMPL: forall x y z : val,
        Val.divlu x y = Some z ->
        helper_implements ge hf (i64_udiv hf) sig_ll_l (x :: y :: nil) z) by eapply HC.
    destruct (IMPL _ _ _ divlu_dummy)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
  destruct (is_longconst e1); simpl in *. 
    destruct (is_longconst e2); simpl in *.
    repeat split; trivial.
    split. repeat split; trivial.
    unfold fundef; rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
  destruct (is_longconst e2); simpl in *. 
    destruct (Int64.is_power2 i); simpl. 
      apply silent_shrluimm; trivial.
    split. repeat split; trivial.
    unfold fundef; rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
  split. repeat split; trivial.
    unfold fundef; rewrite FOUND, PTR.  
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma modls_dummy:
      Val.modls (Vlong Int64.one) (Vlong Int64.one) = 
      Some (Vlong (Int64.mods Int64.one Int64.one)).
Proof.
unfold Val.modls. 
assert (Int64.eq Int64.one Int64.zero = false). 
  apply Int64.eq_false. discriminate. 
simpl; rewrite H. simpl. trivial. 
Qed.

Lemma silent_modl ge (HC:i64_helpers_correct ge hf) e1 e2:
       silent hf ge e1 -> silent hf ge e2 -> silent hf ge (modl hf e1 e2).
Proof. intros. unfold modl.
  unfold binop_long.
  assert (IMPL: forall x y z : val,
        Val.modls x y = Some z ->
        helper_implements ge hf (i64_smod hf) sig_ll_l (x :: y :: nil) z)
        by eapply HC.
  destruct (IMPL _ _ _ modls_dummy)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
  destruct (is_longconst e1); simpl in *; auto. 
    destruct (is_longconst e2); simpl in *; auto.
    split. repeat split; trivial.
    unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
  split. repeat split; trivial.
    unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma silent_andl ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (andl e1 e2).
Proof. intros. unfold andl. unfold splitlong2.
  remember (splitlong2_match e1 e2) as s. 
  destruct s; simpl in *.
    destruct H as [H1 [L1 _]].
    destruct H0 as [H2 [L2 _]].
    repeat split; trivial.
    apply silent_and; trivial.
    apply silent_and; trivial.
  clear Heqs. destruct H as [H1 [L1 _]].
    repeat split; trivial.
    apply silent_and; simpl; auto. apply silent_lift; trivial.
    apply silent_and; simpl; auto. apply silent_lift; trivial.
  clear Heqs. destruct H0 as [H2 [L2 _]].
    repeat split; trivial.
    apply silent_and; simpl; auto. apply silent_lift; trivial.
    apply silent_and; simpl; auto. apply silent_lift; trivial.
  repeat split; trivial. apply silent_lift; trivial.
Qed. 

Lemma modlu_dummy:
      Val.modlu (Vlong Int64.one) (Vlong Int64.one) = 
      Some (Vlong (Int64.mods Int64.one Int64.one)).
Proof.
unfold Val.modlu. 
assert (Int64.eq Int64.one Int64.zero = false). 
  apply Int64.eq_false. discriminate. 
simpl; rewrite H. simpl. trivial. 
Qed.

Lemma silent_modlu ge (HC: i64_helpers_correct ge hf) e1 e2:
      silent hf ge e1 -> silent hf ge e2 -> silent hf ge (modlu hf e1 e2).
Proof. intros. unfold modlu.
  assert (IMPL: forall x y z : val,
        Val.modlu x y = Some z ->
        helper_implements ge hf (i64_umod hf) sig_ll_l (x :: y :: nil) z)
    by eapply HC.
  destruct (IMPL _ _ _ modlu_dummy)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
  destruct (is_longconst e1); simpl in *; auto. 
    destruct (is_longconst e2); simpl in *; auto. 
      split. repeat split; trivial.
      unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
    destruct (is_longconst e2); simpl in *; auto.   
      destruct (Int64.is_power2 i); simpl in *; auto.
        apply silent_andl; simpl; auto.
        split. repeat split; trivial.
      unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
  split. repeat split; trivial.
    unfold fundef. rewrite FOUND, PTR.
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma silent_orl ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (orl e1 e2).
Proof. intros. unfold orl. unfold splitlong2.
  remember (splitlong2_match e1 e2) as s. 
  destruct s; simpl in *; clear Heqs.
    destruct H as [H1 [L1 _]].
    destruct H0 as [H2 [L2 _]].
    repeat split; trivial.
    apply silent_or; trivial.
    apply silent_or; trivial.
  destruct H as [H1 [L1 _]].
    repeat split; trivial.
    apply silent_or; simpl; auto. apply silent_lift; trivial.
    apply silent_or; simpl; auto. apply silent_lift; trivial.
  destruct H0 as [H2 [L2 _]].
    repeat split; trivial.
    apply silent_or; simpl; auto. apply silent_lift; trivial.
    apply silent_or; simpl; auto. apply silent_lift; trivial.
  repeat split; trivial. apply silent_lift; trivial.
Qed. 

Lemma silent_xorl ge: forall e1 e2, silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (xorl e1 e2).
Proof. intros. unfold xorl. unfold splitlong2.
  remember (splitlong2_match e1 e2) as s. 
  destruct s; simpl in *; clear Heqs.
    destruct H as [H1 [L1 _]].
    destruct H0 as [H2 [L2 _]].
    repeat split; trivial.
    apply silent_xor; trivial.
    apply silent_xor; trivial.
  destruct H as [H1 [L1 _]].
    repeat split; trivial.
    apply silent_xor; simpl; auto. apply silent_lift; trivial.
    apply silent_xor; simpl; auto. apply silent_lift; trivial.
  destruct H0 as [H2 [L2 _]].
    repeat split; trivial.
    apply silent_xor; simpl; auto. apply silent_lift; trivial.
    apply silent_xor; simpl; auto. apply silent_lift; trivial.
  repeat split; trivial. apply silent_lift; trivial.
Qed. 

Lemma silent_shll ge (HC:i64_helpers_correct ge hf) e1 e2:
       silent hf ge e1 -> silent hf ge e2 -> silent hf ge (shll hf e1 e2).
Proof. intros. unfold shll. 
  destruct (is_intconst e2); simpl in *; auto. 
    apply silent_shllimm; trivial. 
  split. repeat split; trivial.
    assert (IMPL: forall x y : val,
        helper_implements ge hf (i64_shl hf) sig_li_l 
          (x :: y :: nil) (Val.shll x y)) by eapply HC.
    destruct (IMPL Vundef Vundef)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
    unfold fundef; rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed. 

Lemma silent_shrl ge (HC:i64_helpers_correct ge hf) e1 e2:
      silent hf ge e1 -> silent hf ge e2 -> silent hf ge (shrl hf e1 e2).
Proof. intros. unfold shrl. 
  destruct (is_intconst e2); simpl in *; auto. 
    apply silent_shrlimm; trivial. 
  split. repeat split; trivial.
  assert (IMPL: forall x y : val,
        helper_implements ge hf (i64_sar hf) sig_li_l 
          (x :: y :: nil) (Val.shrl x y)) by eapply HC.
  destruct (IMPL Vundef Vundef)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
  unfold fundef; rewrite FOUND, PTR.  
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed. 

Lemma silent_shrlu ge (HC:i64_helpers_correct ge hf) e1 e2:
      silent hf ge e1 -> silent hf ge e2 -> silent hf ge (shrlu hf e1 e2).
Proof. intros. unfold shrlu. 
  destruct (is_intconst e2); simpl in *; auto.   
    apply silent_shrluimm; trivial. 
  split. repeat split; trivial.
  assert (IMPL: forall x y : val,
        helper_implements ge hf (i64_shr hf) sig_li_l 
          (x :: y :: nil) (Val.shrlu x y)) by eapply HC.
  destruct (IMPL Vundef Vundef)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]]. 
  unfold fundef; rewrite FOUND, PTR.  
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
Qed.

Lemma silent_compXimm  ge C cc c n e: silent hf ge e ->
   silent hf ge (compimm C cc c e n).
Proof. intros. unfold compimm.
  destruct (compimm_match c e); simpl in *; auto.
    destruct (Int.eq_dec n Int.zero); simpl in *; auto.
      destruct (Int.eq_dec n Int.one); simpl in *; auto.
    destruct (Int.eq_dec n Int.zero); simpl in *; auto.
      destruct (Int.eq_dec n Int.one); simpl in *; auto.
    destruct (Int.eq_dec n Int.zero); simpl in *; auto.
    destruct H.  
      destruct (Int.eq_dec n Int.zero); simpl in *; auto.
Qed.      

Lemma silent_comp ge c e1 e2: silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (comp c e1 e2).
Proof. intros. unfold comp. 
  destruct (comp_match e1 e2); simpl in *; auto. 
    apply silent_compXimm; auto.
    apply silent_compXimm; auto.
Qed.   

Lemma silent_compu ge c e1 e2: silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (compu c e1 e2).
Proof. intros. unfold compu. 
  destruct (compu_match e1 e2); simpl in *; auto. 
    apply silent_compXimm; auto.
    apply silent_compXimm; auto.
Qed.   

Lemma silent_cmpl_eq_zero ge e: silent hf ge e ->
      silent hf ge (cmpl_eq_zero e).
Proof. intros. unfold cmpl_eq_zero.
  apply silent_splitlong; trivial.
  intros; simpl. apply silent_comp; simpl; auto. 
  apply silent_or; trivial.
Qed.  

Lemma silent_cmpl_ne_zero ge e: silent hf ge e ->
      silent hf ge (cmpl_ne_zero e).
Proof. intros. unfold cmpl_ne_zero.
  apply silent_splitlong; trivial.
  intros; simpl. apply silent_comp; simpl; auto. 
  apply silent_or; trivial.
Qed.  

Lemma silent_cmpl_gen ge C D e1 e2: silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (cmpl_gen C D e1 e2).
Proof. intros. unfold cmpl_gen.
  unfold splitlong2. 
  destruct (splitlong2_match e1 e2); simpl in *; auto. 
  destruct H as [HH1 [HL1 _]]. destruct H0 as [HH2 [HL2 _]]. 
    repeat split; auto. 
  destruct H as [HH1 [HL1 _]]. repeat split; auto. 
    apply silent_lift; trivial.
    apply silent_lift; trivial.
    apply silent_lift; trivial.
  destruct H0 as [HH2 [HL2 _]]. repeat split; auto. 
    apply silent_lift; trivial.
    apply silent_lift; trivial.
    apply silent_lift; trivial. 
  repeat split; auto. 
    apply silent_lift; trivial.
Qed.  

Lemma silent_cmplu_gen ge C D e1 e2: silent hf ge e1 -> 
      silent hf ge e2 -> silent hf ge (cmplu_gen C D e1 e2).
Proof. intros. unfold cmplu_gen.
  unfold splitlong2. 
  destruct (splitlong2_match e1 e2); simpl in *; auto. 
  destruct H as [HH1 [HL1 _]]. destruct H0 as [HH2 [HL2 _]]. 
    repeat split; auto. 
  destruct H as [HH1 [HL1 _]]. repeat split; auto. 
    apply silent_lift; trivial.
    apply silent_lift; trivial.
    apply silent_lift; trivial.
  destruct H0 as [HH2 [HL2 _]]. repeat split; auto. 
    apply silent_lift; trivial.
    apply silent_lift; trivial.
    apply silent_lift; trivial. 
  repeat split; auto. 
    apply silent_lift; trivial.
Qed.  

Lemma silent_cmpl ge c e1 e2: silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (cmpl c e1 e2).
Proof. intros. unfold cmpl. 
  destruct c; simpl; auto.
    destruct (is_longconst_zero e2); simpl in *; auto. 
      apply silent_cmpl_eq_zero; auto. 
      apply silent_cmpl_eq_zero; auto. 
        apply silent_xorl; trivial.
    destruct (is_longconst_zero e2); simpl in *; auto. 
      apply silent_cmpl_ne_zero; auto. 
      apply silent_cmpl_ne_zero; auto. 
        apply silent_xorl; trivial.
    destruct (is_longconst_zero e2); simpl in *; auto. 
      apply silent_comp; simpl; auto. apply silent_highlong; trivial. 
      apply silent_cmpl_gen; auto. 
      apply silent_cmpl_gen; auto. 
      apply silent_cmpl_gen; auto. 
    destruct (is_longconst_zero e2); simpl in *; auto. 
      apply silent_comp; simpl; auto. apply silent_highlong; trivial. 
      apply silent_cmpl_gen; auto. 
Qed.   

Lemma silent_cmplu ge c e1 e2: silent hf ge e1 -> silent hf ge e2 ->
      silent hf ge (cmplu c e1 e2).
Proof. intros. unfold cmplu. 
  destruct c; simpl; auto.
    destruct (is_longconst_zero e2); simpl in *; auto. 
      apply silent_cmpl_eq_zero; auto. 
      apply silent_cmpl_eq_zero; auto. 
        apply silent_xorl; trivial.
    destruct (is_longconst_zero e2); simpl in *; auto. 
      apply silent_cmpl_ne_zero; auto. 
      apply silent_cmpl_ne_zero; auto. 
        apply silent_xorl; trivial.
    apply silent_cmplu_gen; auto. 
    apply silent_cmplu_gen; auto. 
    apply silent_cmplu_gen; auto. 
    apply silent_cmplu_gen; auto. 
Qed.   

Lemma silent_binop ge (HC:i64_helpers_correct ge hf) e1 e2 b
   (Silent1: silent hf ge e1) (Silent2: silent hf ge e2):
   silent hf ge (sel_binop hf b e1 e2).
Proof. intros.
destruct b; simpl; try solve [repeat split; auto].
apply silent_add; trivial.
apply silent_sub; trivial.
apply silent_mul; trivial.
apply silent_divs; trivial.
apply silent_divu; trivial.
apply silent_mods; trivial.
apply silent_modu; auto.
apply silent_and; auto.
apply silent_or; auto.
apply silent_xor; auto.
apply silent_shl; auto.
apply silent_shr; auto.
apply silent_shru; auto.
apply silent_divf; auto.
apply silent_addl; auto.
apply silent_subl; auto.
apply silent_mull; auto.
apply silent_divl; auto.
apply silent_divlu; auto.
apply silent_modl; auto.
apply silent_modlu; auto.
apply silent_andl; auto.
apply silent_orl; auto.
apply silent_xorl; auto.
apply silent_shll; auto.
apply silent_shrl; auto.
apply silent_shrlu; auto.
apply silent_comp; auto.
apply silent_compu; auto.
apply silent_cmpl; auto.
apply silent_cmplu; auto.
Qed.

Lemma silent_cast8unsigned ge e: silent hf ge e ->
   silent hf ge (cast8unsigned e).
Proof. intros. unfold cast8unsigned.
  destruct (cast8unsigned_match e); simpl; auto. 
Qed.

Lemma silent_cast16unsigned ge e: silent hf ge e ->
   silent hf ge (cast16unsigned e).
Proof. intros. unfold cast16unsigned.
  destruct (cast16unsigned_match e); simpl; auto. 
Qed.

Lemma silent_notl ge e: silent hf ge e ->
   silent hf ge (notl e).
Proof. intros. unfold notl.
  apply silent_splitlong; trivial.
  intros; simpl; auto.  
Qed.

Lemma silent_intoflong ge e: silent hf ge e ->
   silent hf ge (intoflong e).
Proof. intros. unfold intoflong.
  apply silent_lowlong; trivial.
Qed.

Lemma longoffloat_dummy: exists x z, 
  Val.longoffloat x = Some z.
Proof.
unfold Val.longoffloat, Float.longoffloat, Float.Zoffloat.
exists (Vfloat Float.zero). simpl.
assert (Float.zero = Fappli_IEEE.B754_zero 53 1024 false).
  reflexivity.
rewrite H. 
eexists; reflexivity. 
Qed. 

Lemma longuoffloat_dummy: exists x z, 
  Val.longuoffloat x = Some z.
Proof.
unfold Val.longuoffloat, Float.longuoffloat, Float.Zoffloat.
exists (Vfloat Float.zero). simpl.
assert (Float.zero = Fappli_IEEE.B754_zero 53 1024 false).
  reflexivity.
rewrite H. 
eexists; reflexivity. 
Qed. 

Lemma floatoflong_dummy: exists x z, 
  Val.floatoflong x = Some z.
Proof.
unfold Val.floatoflong, Float.floatoflong.
exists (Vlong Int64.zero).
eexists; reflexivity. 
Qed. 

Lemma floatoflongu_dummy: exists x z, 
  Val.floatoflongu x = Some z.
Proof.
unfold Val.floatoflongu, Float.floatoflongu. 
exists (Vlong Int64.zero). 
eexists; reflexivity. 
Qed. 

Lemma singleoflong_dummy: exists x z, 
  Val.singleoflong x = Some z.
Proof.
unfold Val.singleoflong, Float.singleoflong.
exists (Vlong Int64.zero). 
eexists; reflexivity. 
Qed. 

Lemma singleoflongu_dummy: exists x z, 
  Val.singleoflongu x = Some z.
Proof.
unfold Val.singleoflongu, Float.singleoflongu.
exists (Vlong Int64.zero). 
eexists; reflexivity. 
Qed. 

Lemma free_has_effect m b lo sz: 
      ~ Mem.free m b (Int.unsigned lo - 4)
         (Int.unsigned lo + Int.unsigned sz) = Some m.
Proof. intros N.
  specialize (Int.unsigned_range sz). intros.
  apply (Mem.perm_free_2 _ _ _ _ _ N (Int.unsigned lo - 4) Cur Freeable). omega.
  eapply (Mem.free_range_perm _ _ _ _ _ N). omega. 
Qed.

Lemma silent_unop ge (HC:i64_helpers_correct ge hf) u e: 
      silent hf ge e -> silent hf ge (sel_unop hf u e).
Proof. intros.
destruct u; simpl; try solve [repeat split; auto].
apply silent_cast8unsigned; trivial. 
apply silent_cast16unsigned; trivial. 
apply silent_negl; trivial. 
apply silent_notl; trivial.
apply silent_intoflong; trivial.
split. repeat split; trivial.
assert (IMPL:forall x z : val,
        Val.longoffloat x = Some z ->
        helper_implements ge hf (i64_dtos hf) sig_f_l (x :: nil) z)
     by eapply HC.
destruct longoffloat_dummy as [x [z XZ]].
destruct (IMPL _ _ XZ)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
      simpl in *. auto. 
split. split; trivial.
assert (IMPL:forall x z : val,
        Val.longuoffloat x = Some z ->
        helper_implements ge hf (i64_dtou hf) sig_f_l (x :: nil) z)
     by eapply HC.
destruct longuoffloat_dummy as [x [z XZ]].
destruct (IMPL _ _ XZ)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
      simpl in *. auto. 
split. split; trivial.
assert (IMPL:forall x z : val,
        Val.floatoflong x = Some z ->
        helper_implements ge hf (i64_stod hf) sig_l_f (x :: nil) z)
     by eapply HC.
destruct floatoflong_dummy as [x [z XZ]].
destruct (IMPL _ _ XZ)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
      simpl in *. auto. 
split. split; trivial.
assert (IMPL:forall x z : val,
        Val.floatoflongu x = Some z ->
        helper_implements ge hf (i64_utod hf) sig_l_f (x :: nil) z)
     by eapply HC.
destruct floatoflongu_dummy as [x [z XZ]].
destruct (IMPL _ _ XZ)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
      simpl in *. auto.  
split. split; trivial.
assert (IMPL:forall x z : val,
        Val.singleoflong x = Some z ->
        helper_implements ge hf (i64_stof hf) sig_l_s (x :: nil) z)
     by eapply HC.
destruct singleoflong_dummy as [x [z XZ]].
destruct (IMPL _ _ XZ)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
      simpl in *. auto.
split. split; trivial.
assert (IMPL:forall x z : val,
        Val.singleoflongu x = Some z ->
        helper_implements ge hf (i64_utof hf) sig_l_s (x :: nil) z)
     by eapply HC.
destruct singleoflongu_dummy as [x [z XZ]].
destruct (IMPL _ _ XZ)
      as [b [ef [FOUND [PTR [SIG [EXE OBS]]]]]].
unfold fundef. rewrite FOUND, PTR. 
      destruct ef; simpl; try reflexivity; try solve[inv SIG].
      eapply EFhelpersE; eassumption. 
      eapply EFhelpersB; eassumption. 
      simpl in *. auto. 
Qed.

Lemma silent_addressing ge ch e a el: silent hf ge e ->
      (a, el) = addressing ch e -> silentExprList hf ge el.
Proof. intros. unfold addressing in H0.
  destruct (addressing_match e); inv H0; simpl in *; auto. 
Qed.    

Lemma sel_expr_silent ge (HC:i64_helpers_correct ge hf) e:
      silent hf ge (sel_expr hf e).
Proof. intros.
  induction e; simpl; trivial.
  destruct c; simpl; auto.
  unfold addrsymbol. remember (symbol_is_external i) as ext.
    destruct ext; simpl; trivial.
    destruct (Int.eq i0 Int.zero); simpl; eauto.
  apply silent_unop; trivial. 
  apply silent_binop; trivial. 
  unfold load. remember (addressing m (sel_expr hf e)) as a. 
    destruct a; simpl.
    eapply silent_addressing; eauto.
Qed. 

Lemma sel_exprlist_silent ge (HC:i64_helpers_correct ge hf) al:
      silentExprList hf ge (sel_exprlist hf al).
Proof. induction al; simpl; trivial.
  split; auto.
  apply sel_expr_silent; trivial.
Qed.

Lemma sel_condexpr_silent ge (HC:i64_helpers_correct ge hf) a: 
      silentCondExpr hf ge (condexpr_of_expr (sel_expr hf a)).
Proof. intros.
  specialize (sel_expr_silent ge HC a). intros.
  remember (sel_expr hf a) as e. clear Heqe.
  induction e; simpl in *; auto.
  destruct o; simpl; auto. 
  destruct H as [HH1 [HH2 HH3]]; auto.
  destruct H as [HH1 HH3]; auto. 
Qed.

End SILENT.

Section PRESERVATION.

Variable prog: Cminor.program.
Let ge := Genv.globalenv prog.
Variable hf: helper_functions.
Let tprog := transform_program (sel_fundef hf ge) prog.
Let tge := Genv.globalenv tprog.

Hypothesis HELPERS: i64_helpers_correct ge hf.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog. apply Genv.find_symbol_transf.
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: Cminor.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (sel_fundef hf ge f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (sel_fundef hf ge) _ _ H).
Qed.

Definition globalfunction_ptr_inject (j:meminj):=
  forall b f, Genv.find_funct_ptr ge b = Some f -> 
              j b = Some(b,0) /\ isGlobalBlock ge b = true.  

Lemma restrict_preserves_globalfun_ptr: forall j X
  (PG : globalfunction_ptr_inject j)
  (Glob : forall b, isGlobalBlock ge b = true -> X b = true),
globalfunction_ptr_inject (restrict j X).
Proof. intros.
  red; intros. 
  destruct (PG _ _ H). split; trivial.
  apply restrictI_Some; try eassumption.
  apply (Glob _ H1).
Qed.

Lemma restrict_GFP_vis: forall mu
  (GFP : globalfunction_ptr_inject (as_inj mu))
  (Glob : forall b, isGlobalBlock ge b = true -> 
                    frgnBlocksSrc mu b = true),
  globalfunction_ptr_inject (restrict (as_inj mu) (vis mu)).
Proof. intros.
  unfold vis. 
  eapply restrict_preserves_globalfun_ptr. eassumption.
  intuition.
Qed.

(*From Cminorgenproof*)
Remark val_inject_function_pointer:
  forall v fd j tv,
  Genv.find_funct ge v = Some fd ->
  globalfunction_ptr_inject j ->
  val_inject j v tv ->
  tv = v.
Proof.
  intros. exploit Genv.find_funct_inv; eauto. intros [b EQ]. subst v.
  inv H1.
  rewrite Genv.find_funct_find_funct_ptr in H.
  destruct (H0 _ _ H).
  rewrite H1 in H4; inv H4.
  rewrite Int.add_zero. trivial.
Qed.

(*
Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  Genv.find_funct tge v' = Some (sel_fundef hf ge f).
Proof.  
  intros. inv H0.
  exact (Genv.find_funct_transf (sel_fundef hf ge) _ _ H).
  simpl in H. discriminate.
Qed.
*)

Lemma functions_translated:
  forall (v v': val) (f: Cminor.fundef) j,
  Genv.find_funct ge v = Some f ->
  val_inject j v v' ->
  globalfunction_ptr_inject j ->
  Genv.find_funct tge v' = Some (sel_fundef hf ge f).
Proof.  
  intros. 
  exploit val_inject_function_pointer; eauto.
  intros; subst. 
  exact (Genv.find_funct_transf (sel_fundef hf ge) _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (sel_fundef hf ge f) = Cminor.funsig f.
Proof.
  intros. destruct f; reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, sel_program. 
  apply Genv.find_var_info_transf.
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. intuition.
Qed.

Lemma builtin_implements_preserved:
  forall id sg vargs vres,
  builtin_implements ge id sg vargs vres ->
  builtin_implements tge id sg vargs vres.
Proof.
  unfold builtin_implements; intros.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
Qed.

Lemma helper_implements_preserved:
  forall id sg vargs vres,
  helper_implements ge hf id sg vargs vres ->
  helper_implements tge hf id sg vargs vres.
Proof.
  intros. destruct H as (b & ef & A & B & C & D & E).
  exploit function_ptr_translated; eauto. simpl. intros. 
  exists b; exists ef. 
  split. rewrite symbols_preserved. auto.
  split. auto.
  split. auto.
  split. intros. eapply external_call_symbols_preserved; eauto. 
         exact symbols_preserved. exact varinfo_preserved.
  trivial.
Qed.

(*
Lemma helpers_correct_preserved:
  forall h, i64_helpers_correct ge h -> i64_helpers_correct tge h.
Proof.
  unfold i64_helpers_correct; intros.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.*)
Lemma helpers_correct_preserved:
  i64_helpers_correct tge hf.
Proof.
  unfold i64_helpers_correct; intros.
  unfold i64_helpers_correct in HELPERS.
  repeat (match goal with [ H: _ /\ _ |- _ /\ _ ] => destruct H; split end);
  intros; try (eapply helper_implements_preserved; eauto);
  try (eapply builtin_implements_preserved; eauto).
Qed.

Section CMCONSTR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Lemma eval_condexpr_of_expr:
  forall a le v b,
  eval_expr tge sp e m le a v ->
  Val.bool_of_val v b ->
  eval_condexpr tge sp e m le (condexpr_of_expr a) b.
Proof.
  intros until a. functional induction (condexpr_of_expr a); intros.
(* compare *)
  inv H. econstructor; eauto. 
  simpl in H6. inv H6. apply Val.bool_of_val_of_optbool. auto.
(* condition *)
  inv H. econstructor; eauto. destruct va; eauto.
(* let *)
  inv H. econstructor; eauto.
(* default *)
  econstructor. constructor. eauto. constructor. 
  simpl. inv H0. auto. auto. 
Qed.

Lemma eval_load:
  forall le a v chunk v',
  eval_expr tge sp e m le a v ->
  Mem.loadv chunk m v = Some v' ->
  eval_expr tge sp e m le (load chunk a) v'.
Proof.
  intros. generalize H0; destruct v; simpl; intro; try discriminate.
  unfold load. 
  generalize (eval_addressing _ _ _ _ _ chunk _ _ _ _ H (refl_equal _)).
  destruct (addressing chunk a). intros [vl [EV EQ]]. 
  eapply eval_Eload; eauto. 
Qed.

Lemma eval_addressing': forall (ge : genv) (sp : val) (e : env) 
         (m : mem) 
         (le : letenv) (chunk : memory_chunk) (a : expr) 
         (v : val) (b : block) (ofs : int),
       eval_expr ge sp e m le a v ->
       v = Vptr b ofs -> silent hf ge a ->
       let (mode, args) := addressing chunk a in
       exists vl : list val,
         eval_exprlist ge sp e m le args vl /\
         Op.eval_addressing ge sp mode vl = Some v /\
         silentExprList hf ge args.
Proof.
  intros until v. unfold addressing; case (addressing_match a); intros; InvEval.
  inv H. exists vl; auto.
  exists (v :: nil); split. constructor; auto. constructor. 
  subst; simpl. rewrite Int.add_zero; auto. 
Qed. 

Lemma eval_coopstore:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  forall (SIL1: silent hf tge a1) (SIL2: silent hf tge a2),
  CMinSel_corestep hf tge (CMinSel_State f (store chunk a1 a2) k sp e) m
        (CMinSel_State f Sskip k sp e) m'.
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing' _ _ _ _ _ chunk _ _ _ _ H (refl_equal _) SIL1).
  destruct (addressing chunk a1). intros [vl [EV [EQ SILArgs]]]. 
  eapply cminsel_corestep_store; eauto. 
Qed.

Lemma eval_effstore:
  forall chunk a1 a2 v1 v2 f k m',
  eval_expr tge sp e m nil a1 v1 ->
  eval_expr tge sp e m nil a2 v2 ->
  Mem.storev chunk m v1 v2 = Some m' ->
  forall (SIL1: silent hf tge a1) (SIL2: silent hf tge a2),
  cminsel_effstep hf tge (StoreEffect v1 (encode_val chunk v2))
        (CMinSel_State f (store chunk a1 a2) k sp e) m
        (CMinSel_State f Sskip k sp e) m'.
(*(Sstore chunk addr al b)
effsstep tge (State f (store chunk a1 a2) k sp e m)
        E0 (State f Sskip k sp e m').*)
Proof.
  intros. generalize H1; destruct v1; simpl; intro; try discriminate.
  unfold store.
  generalize (eval_addressing' _ _ _ _ _ chunk _ _ _ _ H (refl_equal _) SIL1).
  destruct (addressing chunk a1). intros [vl [EV [EQ SILArgs]]]. 
  eapply cminsel_effstep_store; eauto. 
Qed.
(** Correctness of instruction selection for operators *)

Lemma eval_sel_unop:
  forall le op a1 v1 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_unop op v1 = Some v ->
  exists v', eval_expr tge sp e m le (sel_unop hf op a1) v' /\ Val.lessdef v v'.
Proof.
  assert (THELPERS:= helpers_correct_preserved).
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_cast8unsigned; auto.
  apply eval_cast8signed; auto.
  apply eval_cast16unsigned; auto.
  apply eval_cast16signed; auto.
  apply eval_negint; auto.
  apply eval_notint; auto.
  apply eval_negf; auto.
  apply eval_absf; auto.
  apply eval_singleoffloat; auto.
  eapply eval_intoffloat; eauto.
  eapply eval_intuoffloat; eauto.
  eapply eval_floatofint; eauto.
  eapply eval_floatofintu; eauto.
  eapply eval_negl; eauto.
  eapply eval_notl; eauto.
  eapply eval_intoflong; eauto.
  eapply eval_longofint; eauto.
  eapply eval_longofintu; eauto.
  eapply eval_longoffloat; eauto.
  eapply eval_longuoffloat; eauto.
  eapply eval_floatoflong; eauto.
  eapply eval_floatoflongu; eauto.
  eapply eval_singleoflong; eauto.
  eapply eval_singleoflongu; eauto.
Qed.

Lemma eval_sel_binop:
  forall le op a1 a2 v1 v2 v,
  eval_expr tge sp e m le a1 v1 ->
  eval_expr tge sp e m le a2 v2 ->
  eval_binop op v1 v2 m = Some v ->
  exists v', eval_expr tge sp e m le (sel_binop hf op a1 a2) v' /\ Val.lessdef v v'.
Proof.
  assert (THELPERS:= helpers_correct_preserved).
  destruct op; simpl; intros; FuncInv; try subst v.
  apply eval_add; auto.
  apply eval_sub; auto.
  apply eval_mul; auto.
  eapply eval_divs; eauto.
  eapply eval_divu; eauto.
  eapply eval_mods; eauto.
  eapply eval_modu; eauto.
  apply eval_and; auto.
  apply eval_or; auto.
  apply eval_xor; auto.
  apply eval_shl; auto.
  apply eval_shr; auto.
  apply eval_shru; auto.
  apply eval_addf; auto.
  apply eval_subf; auto.
  apply eval_mulf; auto.
  apply eval_divf; auto.
  eapply eval_addl; eauto.
  eapply eval_subl; eauto.
  eapply eval_mull; eauto.
  eapply eval_divl; eauto.
  eapply eval_divlu; eauto.
  eapply eval_modl; eauto.
  eapply eval_modlu; eauto.
  eapply eval_andl; eauto.
  eapply eval_orl; eauto.
  eapply eval_xorl; eauto.
  eapply eval_shll; eauto.
  eapply eval_shrl; eauto.
  eapply eval_shrlu; eauto.
  apply eval_comp; auto.
  apply eval_compu; auto.
  apply eval_compf; auto.
  exists v; split; auto. eapply eval_cmpl; eauto.
  exists v; split; auto. eapply eval_cmplu; eauto.
Qed.

End CMCONSTR.

(** Recognition of calls to built-in functions *)

Lemma expr_is_addrof_ident_correct:
  forall e id,
  expr_is_addrof_ident e = Some id ->
  e = Cminor.Econst (Cminor.Oaddrsymbol id Int.zero).
Proof.
  intros e id. unfold expr_is_addrof_ident. 
  destruct e; try congruence.
  destruct c; try congruence.
  predSpec Int.eq Int.eq_spec i0 Int.zero; congruence.
Qed.

Lemma classify_call_correct:
  forall sp e m a v fd,
  Cminor.eval_expr ge sp e m a v ->
  Genv.find_funct ge v = Some fd ->
  match classify_call hf ge a with
  | Call_default => True
  | Call_imm id => exists b, Genv.find_symbol ge id = Some b /\ v = Vptr b Int.zero
  | Call_builtin ef => fd = External ef /\ (*NEW*) ~ observableEF hf ef
  end.
Proof.
  unfold classify_call; intros. 
  destruct (expr_is_addrof_ident a) as [id|] eqn:?. 
  exploit expr_is_addrof_ident_correct; eauto. intros EQ; subst a.
  inv H. inv H2. 
  destruct (Genv.find_symbol ge id) as [b|] eqn:?. 
  rewrite Genv.find_funct_find_funct_ptr in H0. 
  rewrite H0. 
  destruct fd. exists b; auto. 
  remember (observableEF_dec hf e0) as d. 
  destruct d; simpl in *. 
    rewrite andb_false_r. exists b; auto.
  rewrite andb_true_r.
  destruct (ef_inline e0). auto. exists b; auto.
  simpl in H0. discriminate.
  auto.
Qed.

(** Compatibility of evaluation functions with the "less defined than" relation. *)

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, Some ?x = Some v /\ _ ] => exists x; split; auto
  | _ => idtac
  end.

(*Lemma eval_unop_lessdef:
  forall op v1 v1' v,
  eval_unop op v1 = Some v -> Val.lessdef v1 v1' ->
  exists v', eval_unop op v1' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until v; intros EV LD. inv LD. 
  exists v; auto.
  destruct op; simpl in *; inv EV; TrivialExists.
Qed.*)

(** Lenb: replace eval_unop_lessdef with eval_unop from
    Cminorgenproof; this requires the addition of 
    Require Import Float above*)
(* Compatibility of [eval_unop] with respect to [val_inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  val_inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.intoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.intuoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.longoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.longuoffloat f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
Qed.

(*Lemma eval_binop_lessdef:
  forall op v1 v1' v2 v2' v m m',
  eval_binop op v1 v2 m = Some v -> 
  Val.lessdef v1 v1' -> Val.lessdef v2 v2' -> Mem.extends m m' ->
  exists v', eval_binop op v1' v2' m' = Some v' /\ Val.lessdef v v'.
Proof.
  intros until m'; intros EV LD1 LD2 ME.
  assert (exists v', eval_binop op v1' v2' m = Some v' /\ Val.lessdef v v').
  inv LD1. inv LD2. exists v; auto. 
  destruct op; destruct v1'; simpl in *; inv EV; TrivialExists.
  destruct op; simpl in *; inv EV; TrivialExists.
  destruct op; try (exact H). 
  simpl in *. TrivialExists. inv EV. apply Val.of_optbool_lessdef. 
  intros. apply Val.cmpu_bool_lessdef with (Mem.valid_pointer m) v1 v2; auto.
  intros; eapply Mem.valid_pointer_extends; eauto.
Qed.
*)
(** Lenb: same for binops
    Compatibility of [eval_binop] with respect to [val_inject]. *)

(*Lenb: fom Cminorgenproof: *)
Remark val_inject_val_of_bool:
  forall f b, val_inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; constructor.
Qed.

(*Lenb: fom Cminorgenproof: *)
Remark val_inject_val_of_optbool:
  forall f ob, val_inject f (Val.of_optbool ob) (Val.of_optbool ob).
Proof.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed.

(*Lenb: fom Cminorgenproof: *)
Ltac TrivialExistsCMINORGEN :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ val_inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ val_inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ val_inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.
Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  val_inject f v1 tv1 ->
  val_inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ val_inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
    repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
      apply Int.sub_add_l.
      simpl. destruct (eq_block b1 b0); auto.
      subst b1. rewrite H in H0; inv H0.   
      rewrite dec_eq_true. rewrite Int.sub_shifted. auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero); inv H. TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int.eq i0 Int.zero); inv H. TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int.iwordsize); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int64.eq i0 Int64.zero); inv H. TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H; TrivialExistsCMINORGEN.
  inv H0; try discriminate; inv H1; try discriminate. simpl in *. 
    destruct (Int64.eq i0 Int64.zero); inv H. TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. simpl. destruct (Int.ltu i0 Int64.iwordsize'); auto.
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. 
    apply val_inject_val_of_optbool.
(* cmpu *)
  inv H. econstructor; split; eauto. 
  unfold Val.cmpu. 
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  replace (Val.cmpu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  destruct b; simpl; constructor.
  symmetry. eapply val_cmpu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  simpl; auto.
(* cmpf *)
  inv H; inv H0; inv H1; TrivialExistsCMINORGEN. apply val_inject_val_of_optbool.
(* cmpl *)
  unfold Val.cmpl in *. inv H0; inv H1; simpl in H; inv H.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
(* cmplu *)
  unfold Val.cmplu in *. inv H0; inv H1; simpl in H; inv H.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
Qed.

(** * Semantic preservation for instruction selection. *)

(** Relationship between the local environments. *)
(*
Definition env_lessdef (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ Val.lessdef v1 v2.
*)
Definition env_inject j (e1 e2: env) : Prop :=
  forall id v1, e1!id = Some v1 -> exists v2, e2!id = Some v2 /\ val_inject j v1 v2.
(*
Lemma set_var_lessdef:
  forall e1 e2 id v1 v2,
  env_lessdef e1 e2 -> Val.lessdef v1 v2 ->
  env_lessdef (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.
*)
Lemma set_var_inject:
  forall j e1 e2 id v1 v2,
  env_inject j e1 e2 -> val_inject j v1 v2 ->
  env_inject j (PTree.set id v1 e1) (PTree.set id v2 e2).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  exists v2; split; congruence.
  auto.
Qed.
(*
Lemma set_params_lessdef:
  forall il vl1 vl2, 
  Val.lessdef_list vl1 vl2 ->
  env_lessdef (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_lessdef; auto.
Qed.
*)
Lemma set_params_inject:
  forall j il vl1 vl2, 
  val_list_inject j vl1 vl2 ->
  env_inject j (set_params vl1 il) (set_params vl2 il).
Proof.
  induction il; simpl; intros.
  red; intros. rewrite PTree.gempty in H0; congruence.
  inv H; apply set_var_inject; auto.
Qed.
(*
Lemma set_locals_lessdef:
  forall e1 e2, env_lessdef e1 e2 ->
  forall il, env_lessdef (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_lessdef; auto.
Qed.*)
Lemma set_locals_inject:
  forall j e1 e2, env_inject j e1 e2 ->
  forall il, env_inject j (set_locals il e1) (set_locals il e2).
Proof.
  induction il; simpl. auto. apply set_var_inject; auto.
Qed.

Lemma lessdef_inject: forall v j
   (Hv: forall b1, getBlocks (v::nil) b1 = true -> 
                   j b1 = Some(b1,0))
   v' (LD: Val.lessdef v v'), val_inject j v v'.
Proof. intros.
  destruct v; try econstructor.
  inv LD; try constructor.
  inv LD; try constructor.
  inv LD; try constructor.
  inv LD. econstructor.
  apply Hv. rewrite getBlocks_char. exists i; left. reflexivity.
  apply eq_sym. apply Int.add_zero. 
Qed.
(*
Lemma inject_lessdef: forall v j
   (Hv: forall b1, getBlocks (v::nil) b1 = true -> 
                   j b1 = Some(b1,0))
   v' (INJ: val_inject j v v'), Val.lessdef v v'.
Proof. intros.
  inv INJ; try econstructor.
  rewrite (Hv b1) in H. inv H.
    rewrite Int.add_zero. constructor.
  rewrite getBlocks_char. exists ofs1; left. reflexivity.
Qed.
*)
(** Semantic preservation for expressions. *)

(*NEW*)
Definition sp_preserved (j:meminj) (sp sp':val) := 
    exists b i b', sp = Vptr b i /\ sp' = Vptr b' i /\ 
                j b = Some(b',0).

Lemma sel_expr_inject:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall j e' le m',
  (*Lenb: these conditions are modified*)
  env_inject j e e' -> Mem.inject j m m' ->
  (*Lenb: these conditions are new here*)
  forall (PG: meminj_preserves_globals ge j)
     (GD: genvs_domain_eq ge tge)
     (NoRepet: list_norepet (map fst (prog_defs prog)))
     sp' (SP: sp_preserved j sp sp'),
  exists v', CminorSel.eval_expr tge sp' e' m' le (sel_expr hf a) v' /\ 
             val_inject j v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  fold (symbol_address ge i i0).
    destruct (eval_addrsymbol tge sp' e' m' le i i0) as [v' [? ?]].
    exists v'; split; trivial.
    eapply lessdef_inject; trivial. intros.
    rewrite getBlocks_char in H3. destruct H3.
    destruct H3; try contradiction.
    unfold symbol_address in H3. 
    remember (Genv.find_symbol ge i) as d.
    destruct d; apply eq_sym in Heqd; inv H3.
      apply meminj_preserves_genv2blocks in PG.
      destruct PG. apply H3. unfold genv2blocks. simpl. exists i; assumption.
    unfold symbol_address in *. rewrite <- symbols_preserved. assumption.
  destruct (eval_addrstack tge sp' e' m' le i) as [v' [EV' LV']].
    exists v'; split; trivial.
    destruct SP as [b [ofs [b' [SP [SP' J]]]]]. subst.
    simpl in LV'. simpl. inv LV'.
    econstructor. eassumption. rewrite Int.add_zero. trivial.  
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_compat; eauto. intros [v' [C D]].
  (*WAS: exploit eval_unop_lessdef; eauto. intros [v' [C D]].*)
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. 
  inv D; inv F; try econstructor. eassumption. trivial.
  (*WAS:eapply Val.lessdef_trans; eauto. *)
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_compat; eauto. intros [v' [E F]].
  (*WAS: exploit eval_binop_lessdef; eauto. intros [v' [E F]].*)
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto.
  inv F; inv Q; try econstructor. eassumption. trivial.
  (*WAS: eapply Val.lessdef_trans; eauto. *)
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_inject; eauto. intros [v' [C D]].
  (*WAS:exploit Mem.loadv_extends; eauto. intros [v' [C D]].*)
  exists v'; split; auto. eapply eval_load; eauto.
Qed.
(*
Lemma sel_expr_correct:
  forall sp e m a v,
  Cminor.eval_expr ge sp e m a v ->
  forall e' le m',
  env_lessdef e e' -> Mem.extends m m' ->
  exists v', eval_expr tge sp e' m' le (sel_expr hf a) v' /\ Val.lessdef v v'.
Proof.
  induction 1; intros; simpl.
  (* Evar *)
  exploit H0; eauto. intros [v' [A B]]. exists v'; split; auto. constructor; auto.
  (* Econst *)
  destruct cst; simpl in *; inv H. 
  exists (Vint i); split; auto. econstructor. constructor. auto. 
  exists (Vfloat f); split; auto. econstructor. constructor. auto.
  exists (Val.longofwords (Vint (Int64.hiword i)) (Vint (Int64.loword i))); split.
  eapply eval_Eop. constructor. EvalOp. simpl; eauto. constructor. EvalOp. simpl; eauto. constructor. auto.
  simpl. rewrite Int64.ofwords_recompose. auto.
  rewrite <- symbols_preserved. fold (symbol_address tge i i0). apply eval_addrsymbol.
  apply eval_addrstack.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [v1' [A B]].
  exploit eval_unop_lessdef; eauto. intros [v' [C D]].
  exploit eval_sel_unop; eauto. intros [v'' [E F]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [v1' [A B]].
  exploit IHeval_expr2; eauto. intros [v2' [C D]].
  exploit eval_binop_lessdef; eauto. intros [v' [E F]].
  exploit eval_sel_binop. eexact A. eexact C. eauto. intros [v'' [P Q]].
  exists v''; split; eauto. eapply Val.lessdef_trans; eauto. 
  (* Eload *)
  exploit IHeval_expr; eauto. intros [vaddr' [A B]].
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  exists v'; split; auto. eapply eval_load; eauto.
Qed.
*)
Lemma sel_exprlist_inject:
  forall sp e m a v,
  Cminor.eval_exprlist ge sp e m a v ->
  forall j e' le m',
  (*Lenb: these conditions are modified*)
  env_inject j e e' -> Mem.inject j m m' ->
  (*Lenb: these conditions are new here*)
  forall (PG: meminj_preserves_globals ge j)
     (GD: genvs_domain_eq ge tge)
     (NoRepet: list_norepet (map fst (prog_defs prog)))
     sp' (SP: sp_preserved j sp sp'),
  exists v', CminorSel.eval_exprlist tge sp' e' m' le (sel_exprlist hf a) v' /\ 
             val_list_inject j v v'.
Proof.
  induction 1; intros; simpl. 
  exists (@nil val); split; auto. constructor.
  exploit sel_expr_inject; eauto. intros [v1' [A B]].
(*  exploit sel_expr_correct; eauto. intros [v1' [A B]].*)
  exploit IHeval_exprlist; eauto. intros [vl' [C D]].
  exists (v1' :: vl'); split; eauto. constructor; eauto.
Qed.

(** Semantic preservation for functions and statements. *)

Inductive match_cont (*NEW:*)(j:meminj): Cminor.cont -> CminorSel.cont -> Prop :=
  | match_cont_stop:
      match_cont j Cminor.Kstop Kstop
  | match_cont_seq: forall s k k',
      match_cont j k k' ->
      match_cont j (Cminor.Kseq s k) (Kseq (sel_stmt hf ge s) k')
  | match_cont_block: forall k k',
      match_cont j k k' ->
      match_cont j (Cminor.Kblock k) (Kblock k')
  (*sp' and sp_preserved_condition are new*)
  | match_cont_call: forall id f sp e k sp' e' k',
      match_cont j k k' -> 
      (*env_lessdef e e' ->*)
      env_inject j e e' -> sp_preserved j sp sp' ->
      match_cont j (Cminor.Kcall id f sp e k) (Kcall id (sel_function hf ge f) sp' e' k').

Inductive match_states (j:meminj) : CMin_core -> mem -> CMinSel_core -> mem -> Prop :=
  | match_state: forall f s k s' k' sp e m sp' e' m',
      s' = sel_stmt hf ge s ->
      match_cont j k k' ->
      (*      env_lessdef e e' -> Mem.extends m m' ->*)
      env_inject j e e' -> Mem.inject j m m' -> sp_preserved j sp sp' ->
      match_states j
        (CMin_State f s k sp e) m
        (CMinSel_State (sel_function hf ge f) s' k' sp' e') m'
  | match_callstate: forall f args args' k k' m m',
      match_cont j k k' ->
      (*      Val.lessdef_list args args' -> Mem.extends m m' ->*)
      val_list_inject j args args' -> Mem.inject j m m' -> 
      match_states j
        (CMin_Callstate f args k) m
        (CMinSel_Callstate (sel_fundef hf ge f) args' k') m'
  | match_returnstate: forall v v' k k' m m',
      match_cont j k k' ->
      (*Val.lessdef v v' -> Mem.extends m m' ->*)
      val_inject j v v' -> Mem.inject j m m' ->
      match_states j
        (CMin_Returnstate v k) m
        (CMinSel_Returnstate v' k') m'
  | match_builtin_1: forall ef args args' optid f sp e k m al sp' e' k' m',
      match_cont j k k' ->
      (*Val.lessdef_list args args' -> env_lessdef e e' -> Mem.extends m m' -> *)
      val_list_inject j args args' -> env_inject j e e' -> Mem.inject j m m' -> 
      sp_preserved j sp sp' ->
      CminorSel.eval_exprlist tge sp' e' m' nil al args' ->
      (*NEW*) ~ observableEF hf ef ->
      match_states j
        (CMin_Callstate (External ef) args (Cminor.Kcall optid f sp e k)) m
        (CMinSel_State (sel_function hf ge f) (Sbuiltin optid ef al) k' sp' e') m'
  | match_builtin_2: forall v v' optid f sp e k m sp' e' m' k',
      match_cont j k k' ->
      (*Val.lessdef v v' -> env_lessdef e e' -> Mem.extends m m' ->*)
      val_inject j v v' -> env_inject j e e' -> Mem.inject j m m' -> sp_preserved j sp sp' ->
      match_states j
        (CMin_Returnstate v (Cminor.Kcall optid f sp e k)) m
        (CMinSel_State (sel_function hf ge f) Sskip k' sp' (set_optvar optid v' e')) m'.

Definition MATCH (d:CMin_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict (as_inj mu) (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma env_inject_sub: forall j e e' (E: env_inject j e e')
          j' (I: inject_incr j j'), env_inject j' e e'.
Proof. intros.
  red. intros. destruct (E _ _ H) as [v2 [X Y]]. 
  exists v2; intuition.
  eapply val_inject_incr; eassumption.
Qed.

Lemma match_cont_sub: forall j k k' (K: match_cont j k k')
          j' (I: inject_incr j j'), match_cont j' k k'.
Proof. intros.
  induction K; try econstructor; try eassumption.
  eapply env_inject_sub; eassumption.
  destruct H0 as [b [i [b' [X [Y J]]]]].
    exists b, i, b'. apply I in J. intuition.
Qed.

Remark call_cont_commut:
  forall (*New: j*) j k k', match_cont j k k' -> match_cont j (Cminor.call_cont k) (call_cont k').
Proof.
  induction 1; simpl; auto. constructor. constructor; auto.
Qed.

Remark find_label_commut:
  forall j lbl s k k',
  match_cont j k k' ->
  match Cminor.find_label lbl s k, find_label lbl (sel_stmt hf ge s) k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => s1' = sel_stmt hf ge s1 /\ match_cont j k1 k1'
  | _, _ => False
  end.
Proof.
  induction s; intros; simpl; auto.
(* store *)
  unfold store. destruct (addressing m (sel_expr hf e)); simpl; auto.
(* call *)
  destruct (classify_call hf ge e); simpl; auto.
(* tailcall *)
  destruct (classify_call hf ge e); simpl; auto.
(* seq *)
  exploit (IHs1 (Cminor.Kseq s2 k)). constructor; eauto. 
  destruct (Cminor.find_label lbl s1 (Cminor.Kseq s2 k)) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt hf ge s1) (Kseq (sel_stmt hf ge s2) k')) as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* ifthenelse *)
  exploit (IHs1 k); eauto. 
  destruct (Cminor.find_label lbl s1 k) as [[sx kx] | ];
  destruct (find_label lbl (sel_stmt hf ge s1) k') as [[sy ky] | ];
  intuition. apply IHs2; auto.
(* loop *)
  apply IHs. constructor; auto.
(* block *)
  apply IHs. constructor; auto.
(* return *)
  destruct o; simpl; auto. 
(* label *)
  destruct (ident_eq lbl l). auto. apply IHs; auto.
Qed.

(*Lenb: changed type of s from Cminor.state to CMin_core, 
  adapted the constructor names,
  and removed one _ in each clause*)
Definition measure (s: CMin_core) : nat :=
  match s with
  | CMin_Callstate _ _ _ => 0%nat
  | CMin_State _ _ _ _ _ => 1%nat
  | CMin_Returnstate _ _ => 2%nat
  end.

Lemma Match_restrict: forall d mu c1 m1 c2 m2 X
          (MC: MATCH d mu c1 m1 c2 m2)
          (HX: forall b, vis mu b = true -> X b = true)
          (RC: REACH_closed m1 X),
          MATCH d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RCLocs [PG [GFun [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
  rewrite restrict_sm_all.
  rewrite restrict_nest; intuition.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RCLocs.
split. clear -PG HX Glob.
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


Lemma Match_genv: forall d mu c1 m1 c2 m2
                  (MC:MATCH d mu c1 m1 c2 m2),
          meminj_preserves_globals ge (extern_of mu) /\
          (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
Proof.
  intros.
  assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
  split; trivial.
  rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
Qed.


Lemma MATCH_atExternal: forall mu c1 m1 c2 m2 e vals1 ef_sig
       (MTCH: MATCH c1 mu c1 m1 c2 m2)
       (AtExtSrc: at_external (cmin_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
     Mem.inject (as_inj mu) m1 m2 /\
     exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
       at_external (cminsel_eff_sem hf) c2 = Some (e, ef_sig, vals2) /\
      (forall pubSrc' pubTgt',
       pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
       pubTgt' = (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
       forall nu : SM_Injection, nu = replace_locals mu pubSrc' pubTgt' ->
       MATCH c1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2).
Proof. intros.
  destruct MTCH as [MC [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  destruct c1; inv AtExtSrc. destruct f; inv H0.
  split; trivial.
  inv MC; simpl in *.
  destruct (observableEF_dec hf e0); inv H1.
  exists args'.
    specialize (val_list_inject_forall_inject _ _ _ H7); intros.
    specialize (forall_vals_inject_restrictD _ _ _ _ H); intros.
    exploit replace_locals_wd_AtExternal; try eassumption.
    intros WDnu.
    intuition.   
    assert (SMVnu: sm_valid nu m1 m2).
      red. subst nu. rewrite replace_locals_DOM, replace_locals_RNG. apply SMV.
    subst nu; split; repeat rewrite replace_locals_as_inj, replace_locals_vis. 
        constructor; trivial.
        rewrite replace_locals_frgnBlocksSrc. intuition.
        subst; trivial.
    eapply inject_shared_replace_locals; try eassumption.
      subst; trivial.

  destruct (observableEF_dec hf e0); inv H1. contradiction.
Qed.

(*FreshS/T: fresh blocks in src/tgt language*)
Definition sm_add_intern (mu: SM_Injection) j FreshS FreshT : SM_Injection :=
  Build_SM_Injection (fun b => locBlocksSrc mu b || FreshS b)
                     (fun b => locBlocksTgt mu b || FreshT b) 
                     (pubBlocksSrc mu) (pubBlocksTgt mu)
                     (join (local_of mu) (fun b => match extern_of mu b with
                                             None => j b | Some _ => None end))
                     (extBlocksSrc mu) (extBlocksTgt mu)
                     (frgnBlocksSrc mu) (frgnBlocksTgt mu) (extern_of mu).

Lemma sm_add_intern_wd: forall mu j FreshS FreshT (WD: SM_wd mu)
      (HFreshS: forall b, FreshS b =true -> DomSrc mu b = false)
      (HFreshT: forall b, FreshT b =true -> DomTgt mu b = false)
      (JDomTgt: forall b1 b2 d, j b1 = Some (b2,d) -> 
           as_inj mu b1 = Some(b2,d) \/
           (FreshS b1 = true /\ FreshT b2 = true)),
      SM_wd (sm_add_intern mu j FreshS FreshT).
Proof. intros.
  split; try eapply WD; eauto; intros.
destruct mu; simpl.
  remember (FreshS b) as f.
  destruct f; simpl; apply eq_sym in Heqf.
     apply HFreshS in Heqf; unfold DomSrc in Heqf; simpl in *.
     apply orb_false_iff in Heqf.
     destruct Heqf as [A B]; rewrite A, B; simpl. right; trivial.
  destruct (disjoint_extern_local_Src _ WD b); simpl in *; rewrite H; simpl.
     left; trivial. right; trivial.
destruct mu; simpl.
  remember (FreshT b) as f.
  destruct f; simpl; apply eq_sym in Heqf.
     apply HFreshT in Heqf; unfold DomTgt in Heqf; simpl in *.
     apply orb_false_iff in Heqf.
     destruct Heqf as [A B]; rewrite A, B; simpl. right; trivial.
  destruct (disjoint_extern_local_Tgt _ WD b); simpl in *; rewrite H; simpl.
     left; trivial. right; trivial.
destruct mu; simpl in *.
  remember (j b1) as d.
  destruct d; apply eq_sym in Heqd. 
    destruct p.
    destruct (JDomTgt _ _ _ Heqd); simpl in *. unfold join in H.
      destruct (joinD_Some _ _ _ _ _ H0) as [EXT | [NEXT LOC]]; clear H0; simpl in *.
        destruct (disjoint_extern_local _ WD b1); simpl in H0. congruence.
        rewrite H0, EXT in H. congruence. 
      rewrite LOC in H. inv H. 
        destruct (local_DomRng _ WD _ _ _ LOC); simpl in *.
        rewrite H, H0. split; trivial. destruct (joinD_Some _ _ _ _ _ H) as [LOC | [NLOC X]]; clear H.
      destruct (local_DomRng _ WD _ _ _ LOC); simpl in *.
        rewrite H, H1. split; trivial.
    destruct (extern_of b1); try inv X. rewrite H1 in Heqd. inv Heqd.
      intuition.
  destruct (joinD_Some _ _ _ _ _ H).
    destruct (local_DomRng _ WD _ _ _ H0); simpl in *; clear H0. 
      intuition.
    destruct H0. rewrite Heqd in H1. destruct (extern_of b1); inv H1.
simpl in *. destruct (pubSrc _ WD _ H) as [b2 [d [Hb1 Hb2]]]; simpl in *.
    exists b2, d. apply pub_in_local in Hb1.
      unfold join. rewrite Hb1, Hb2. split; trivial.
simpl in *. rewrite (pubBlocksLocalTgt _ WD _ H). intuition.
Qed.

Lemma sm_add_intern_incr: forall mu j FreshS FreshT
        (INC : inject_incr (as_inj mu) j) mu'
        (Heqmu' : mu' = sm_add_intern mu j FreshS FreshT),
     intern_incr mu mu'.
Proof. intros. subst.
  split; simpl; intuition.
  red; intros. unfold join. rewrite H. trivial.
Qed.

Lemma sm_add_intern_as_inj: forall mu j FreshS FreshT,
   as_inj (sm_add_intern mu j FreshS FreshT) = 
   join (as_inj mu) (fun b => match extern_of mu b with
                              None => j b | Some _ => None end).
Proof. intros.
  extensionality b.
  destruct mu; unfold as_inj, join; simpl.
  unfold join. 
  destruct (extern_of b); trivial.
    destruct p; trivial.
Qed.

Lemma sm_add_intern_incr2: forall mu j FreshS FreshT
        (INC : inject_incr (as_inj mu) j) mu'
        (Heqmu' : mu' = sm_add_intern mu j FreshS FreshT),
     inject_incr j (as_inj mu').
Proof. intros. subst. rewrite sm_add_intern_as_inj.
  red; intros. unfold join.
  remember (as_inj mu b) as d.
  destruct d; apply eq_sym in Heqd.
    destruct p. rewrite (INC _ _ _ Heqd) in H. trivial.
  destruct (joinD_None _ _ _ Heqd). rewrite H0. trivial.
Qed.

Lemma sm_add_intern_DomSrc: forall mu j FreshS FreshT,
       DomSrc (sm_add_intern mu j FreshS FreshT) = fun b => DomSrc mu b || FreshS b.
Proof. intros. extensionality b. destruct mu. unfold DomSrc; simpl.
       repeat rewrite <- orb_assoc. rewrite (orb_comm (FreshS b)). trivial.
Qed.
Lemma sm_add_intern_DomTgt: forall mu j FreshS FreshT,
       DomTgt (sm_add_intern mu j FreshS FreshT) = fun b => DomTgt mu b || FreshT b.
Proof. intros. extensionality b. destruct mu. unfold DomTgt; simpl.
       repeat rewrite <- orb_assoc. rewrite (orb_comm (FreshT b)). trivial.
Qed.

Lemma sm_add_intern_sep: forall mu j FreshS FreshT
        (HFreshS: forall b, FreshS b =true -> DomSrc mu b = false)
        (HFreshT: forall b, FreshT b =true -> DomTgt mu b = false)
        (JDomTgt: forall b1 b2 d, j b1 = Some (b2,d) -> 
           as_inj mu b1 = Some(b2,d) \/
           (FreshS b1 = true /\ FreshT b2 = true))
         mu'
        (Heqmu' : mu' = sm_add_intern mu j FreshS FreshT)
        m1 m2 (WD: SM_wd mu)
        (HFreshSm1: forall b, FreshS b =true -> ~Mem.valid_block m1 b)
        (HFreshTm2: forall b, FreshT b =true -> ~Mem.valid_block m2 b),
      sm_inject_separated mu mu' m1 m2.
Proof. intros. subst.
  split; intros.
    destruct (joinD_None _ _ _ H).
    destruct (joinD_Some _ _ _ _ _ H0) as [XX | [NEXT XX]]; clear H0; simpl in *; try congruence.
    unfold join in XX. rewrite H2, H1 in XX.
    destruct (JDomTgt _ _ _ XX) as [X | [X Y]]; try congruence. intuition.
  split; intros. rewrite sm_add_intern_DomSrc in H0. rewrite H in H0; simpl in H0.    
     apply HFreshSm1; trivial.
   rewrite sm_add_intern_DomTgt in H0. rewrite H in H0; simpl in H0.    
     apply HFreshTm2; trivial.
Qed.

Lemma sm_add_localloc: forall mu j m1 m2 m1' m2' mu'
        (Heqmu' : mu' = sm_add_intern mu j (freshloc m1 m1') (freshloc m2 m2')),
     sm_locally_allocated mu mu' m1 m2 m1' m2'.
Proof. intros.
  rewrite sm_locally_allocatedChar.
  subst; simpl.
  rewrite sm_add_intern_DomSrc, sm_add_intern_DomTgt.
  intuition.
Qed.

Lemma MATCH_init_cores: forall v 
  (vals1 : list val) (c1 : CMin_core) (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (CSM_Ini :initial_core (cmin_eff_sem hf) ge v vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (R : list_norepet (map fst (prog_defs prog)))
  (J: forall b1 b2 d, j b1 = Some (b2, d) -> 
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (InitMem : exists m0 : mem, Genv.init_mem prog = Some m0 
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m1) 
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))
  (GDE: genvs_domain_eq ge tge)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists c2 : CMinSel_core,
  initial_core (cminsel_eff_sem hf) tge v vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2. 
Proof. intros.
  inversion CSM_Ini.
  unfold  CMin_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0 => 0
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0 => 0
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  intros l _.
  2: solve[simpl; rewrite andb_comm; inversion 2].

  exploit function_ptr_translated; eauto. intros FIND.
  exists (CMinSel_Callstate (sel_fundef hf ge (Internal f)) vals2 Kstop).
  split.
  simpl. 
  inv Heqzz. unfold tge in FIND. inv FIND. rewrite H2.
  unfold CMinSel_initial_core.
  case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.

  assert (Zlength vals2 = Zlength vals1) as ->. 
  { apply forall_inject_val_list_inject in VInj. clear - VInj. 
    induction VInj; auto. rewrite !Zlength_cons, IHVInj; auto. }

  assert (val_casted.val_has_type_list_func vals2
           (sig_args (funsig (Internal (sel_function hf ge f))))=true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H1; simpl in H1. 
    solve[rewrite andb_comm in H1; inv H1].
    assert (sig_args (funsig (Internal (sel_function hf ge f))) 
          = sig_args (Cminor.funsig (Internal f))) as ->.
    { simpl. auto. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (Cminor.funsig (Internal f)))); auto. inv H1. }
  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    simpl in H1; rewrite <-andb_assoc, andb_comm in H1; inv H1. }

  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0 => 0
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0 => 0
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  
  solve[simpl; auto].
  intros CONTRA. solve[elimtype False; auto].
  intros CONTRA. solve[elimtype False; auto].
  destruct InitMem as [m0 [INIT_MEM [A B]]].

destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
    VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
   as [AA [BB [CC [DD [EE [FF GG]]]]]].
  intuition.
  split.
    revert H1.
    destruct (val_casted.val_has_type_list_func vals1
             (sig_args (Cminor.funsig (Internal f))) && val_casted.vals_defined vals1); 
      try solve[inversion 1]. 
    simpl. inversion 1; subst. clear H1.
    eapply match_callstate.
      constructor. rewrite initial_SM_as_inj.
      unfold vis, initial_SM; simpl.
      apply forall_inject_val_list_inject.
      eapply restrict_forall_vals_inject; try eassumption.
        intros. apply REACH_nil. rewrite H; intuition.
      rewrite initial_SM_as_inj. unfold vis, initial_SM; simpl.
        eapply inject_mapped; try eassumption. 
    rewrite initial_SM_as_inj in GG.
      unfold vis, initial_SM in FF; simpl in FF.
      eapply restrict_mapped_closed; eassumption.
     apply restrict_incr.
   intuition. 
    rewrite match_genv_meminj_preserves_extern_iff_all. assumption.
    apply BB.
    apply EE.
    rewrite initial_SM_as_inj.
    red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         specialize (H0 _ _ _ INIT_MEM H). 
         destruct (valid_init_is_global _ R _ INIT_MEM _ H0) as [id Hid]. 
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock. 
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
    rewrite initial_SM_as_inj. assumption. 
Qed.

Lemma MATCH_AfterExternal: 
forall mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
  (MemInjMu : Mem.inject (as_inj mu) m1 m2)
  (MatchMu : MATCH st1 mu st1 m1 st2 m2)
  (AtExtSrc : at_external (cmin_eff_sem hf) st1 = Some (e, ef_sig, vals1))
  (AtExtTgt : at_external (cminsel_eff_sem hf) st2 = Some (e', ef_sig', vals2))
  (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
  (pubSrc' : Values.block -> bool)
  (pubSrcHyp : pubSrc' =
              (fun b : Values.block =>
               locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
  (pubTgt' : Values.block -> bool)
  (pubTgtHyp : pubTgt' =
              (fun b : Values.block =>
               locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
  nu
  (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
  nu' ret1 m1' ret2 m2' 
  (INC : extern_incr nu nu')
  (SEP : sm_inject_separated nu nu' m1 m2)
  (WDnu' : SM_wd nu')
  (SMvalNu' : sm_valid nu' m1' m2')
  (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
  (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
  (FwdSrc : mem_forward m1 m1')
  (FwdTgt : mem_forward m2 m2')
  (frgnSrc' : Values.block -> bool)
  (frgnSrcHyp : frgnSrc' =
               (fun b : Values.block =>
               DomSrc nu' b &&
               (negb (locBlocksSrc nu' b) &&
                REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
  (frgnTgt' : Values.block -> bool)
  (frgnTgtHyp : frgnTgt' =
               (fun b : Values.block =>
                DomTgt nu' b &&
                (negb (locBlocksTgt nu' b) &&
                 REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
  mu' 
  (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
  (UnchPrivSrc : Mem.unchanged_on
                (fun (b : Values.block) (_ : Z) =>
                 locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1
                m1')
  (UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists (st1' : CMin_core) (st2' : CMinSel_core),
  after_external (cmin_eff_sem hf) (Some ret1) st1 = Some st1' /\
  after_external (cminsel_eff_sem hf) (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 inv MC; simpl in *; try congruence.
 simpl in *.
 destruct f; inv AtExtSrc.
 simpl in *.
 remember (observableEF_dec hf e0) as obs. 
 destruct obs; inv H3.
  apply eq_sym in AtExtTgt. inv AtExtTgt.
  exists (CMin_Returnstate ret1 k). eexists.
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
    subst. clear - INC SEP PG GFP Glob WDmu WDnu'.
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
  specialize (IHL _ H4); clear H4.
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
        apply (H2 VB) in H5.
        rewrite (H3 H5) in H7. clear H2 H3.
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
    apply andb_true_iff in H2. simpl in H2. 
    destruct H2 as[DomNu' Rb']. 
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
           specialize (RC' _ H2). 
           destruct (mappedD_true _ _ RC') as [[? ?] ?].
           eapply as_inj_DomRng; eassumption.
    eapply REACH_cons; try eassumption.
(*assert (RRR: REACH_closed m1' (exportedSrc nu' (ret1 :: nil))).
    intros b Hb. apply REACHAX in Hb.
       destruct Hb as [L HL].
       generalize dependent b.
       induction L ; simpl; intros; inv HL; trivial.
       specialize (IHL _ H1); clear H1.
       unfold exportedSrc.
       eapply REACH_cons; eassumption.*)
    
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
     intros. specialize (Glob _ H2).
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
  unfold vis in *.
(*  rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc in *.*)
  econstructor; try eassumption.
    eapply match_cont_sub; try eassumption.
      rewrite (*restrict_sm_all, *)replace_externs_as_inj.
      rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc in *.
      clear RRC RR1 RC' PHnu' INCvisNu' H0 UnchLOOR UnchPrivSrc H1 H.
      destruct INC. rewrite replace_locals_extern in H.
        rewrite replace_locals_frgnBlocksTgt, replace_locals_frgnBlocksSrc,
                replace_locals_pubBlocksTgt, replace_locals_pubBlocksSrc,
                replace_locals_locBlocksTgt, replace_locals_locBlocksSrc,
                replace_locals_extBlocksTgt, replace_locals_extBlocksSrc,
                replace_locals_local in H0.
        destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
        red; intros. destruct (restrictD_Some _ _ _ _ _ H9); clear H9.
          apply restrictI_Some.
            apply joinI.
            destruct (joinD_Some _ _ _ _ _ H10).
              apply H in H9. left; trivial.
            destruct H9. right. rewrite H0 in H12.
              split; trivial.
              destruct (disjoint_extern_local _ WDnu' b); trivial. congruence.
          rewrite H3, H7 in H11.
            remember (locBlocksSrc nu' b) as d.
            destruct d; trivial; simpl in *.
            apply andb_true_iff.
            split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H11). intuition.
               apply REACH_nil. unfold exportedSrc. 
                 apply frgnSrc_shared in H11; trivial. rewrite H11; intuition.
      rewrite replace_externs_as_inj. rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc. 
       eapply restrict_val_inject; try eassumption.
       intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H2. trivial.
  rewrite replace_externs_as_inj. 
    eapply inject_mapped; try eassumption.
      rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc.
      eapply restrict_mapped_closed; try eassumption.
unfold vis.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
intuition.
  red; intros. destruct (GFP _ _ H4). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed. 

Lemma MATCH_diagram: forall st1 m1 st1' m1'
      (CS: corestep (cmin_eff_sem hf) ge st1 m1 st1' m1')
      st2 mu m2 (MC: MATCH st1 mu st1 m1 st2 m2)
      (R: list_norepet (map fst (prog_defs prog))),
  exists st2' m2',
    (corestep_plus (cminsel_eff_sem hf) tge st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
       corestep_star (cminsel_eff_sem hf) tge st2 m2 st2' m2')
  /\ exists mu',
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH st1' mu' st1' m1' st2' m2' /\
     SM_wd mu' /\
     sm_valid mu' m1' m2'.
Proof.
  intros.
  assert (THELPERS:= helpers_correct_preserved); clear HELPERS.
  assert (SymbPres:= symbols_preserved).
  assert (GDE:= GDE_lemma).
   inv CS; simpl in *.
{ (*skip seq*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *; inv H8. 
      eexists. eexists.
      split. left.  
         apply corestep_plus_one.
           econstructor; eauto. 
      simpl. exists mu; intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition. }
{ (*skip block*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists. eexists.
      split. left.  
         apply corestep_plus_one. 
           econstructor; eauto. 
      simpl. exists mu; intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition. }
{ (* skip call *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. 
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      destruct H13 as [spp [i [spp' [X [X' Jsp]]]]]. inv X.
      rename spp into sp. rename spp' into sp'.
      destruct (restrictD_Some _ _ _ _ _ Jsp).
      exploit (free_parallel_inject (as_inj mu)); try eassumption. intros [m2' [A B]].
      (*WAS: exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].*)
      simpl in A. rewrite Zplus_0_r in A.
      eexists. eexists.
      split. left.  
         apply corestep_plus_one.  
           econstructor; eauto. inv H10; trivial.
      simpl. exists mu.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      assert (RC': REACH_closed m1' (vis mu)).
        eapply REACH_closed_free; eassumption.
      intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  A).
        rewrite (freshloc_free _ _ _ _ _  H0).
        repeat split; extensionality b; intuition.
      econstructor.
        econstructor; eauto. 
            eapply free_free_inject; try eassumption.
          simpl; rewrite Zplus_0_r. assumption.
        (*another proof of this Mem.inject fact is this:
            eapply inject_mapped; try eassumption.
            eapply restrict_mapped_closed; try eassumption.
            eapply inject_REACH_closed; eassumption.
            apply restrict_incr.*)
      intuition. (*
        eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Jsp). 
        eapply free_free_inject; eassumption. *) }
{ (* assign *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.  
      exploit sel_expr_inject; eauto.
      (*WAS: exploit sel_expr_corect; eauto.*) intros [v' [A B]].
      eexists; eexists. 
      split. left.
         apply corestep_plus_one. 
           econstructor; eauto. 
           apply sel_expr_silent; trivial.
      simpl. exists mu. intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
        econstructor; trivial. 
          red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
            inv H0. exists v'; auto.
            eauto.
          (*WAS:apply set_var_lessdef; auto.*)
      intuition. }
{ (* store *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.  
      (*WAS:exploit sel_expr_correct.*)
      exploit sel_expr_inject. eexact H. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [vaddr' [A B]].
      (*WAS: exploit sel_expr_correct.*) 
      exploit sel_expr_inject. eexact H0. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [v' [C D]].
      (*WAS:exploit Mem.storev_extends; eauto. intros [m2' [P Q]].*)
      exploit Mem.storev_mapped_inject; eauto. intros [m2' [P Q]]. 
      eexists; eexists. 
      split. left.
         apply corestep_plus_one. 
            eapply eval_coopstore; eauto. 
            apply sel_expr_silent; trivial.
            apply sel_expr_silent; trivial.
      simpl. exists mu.
      assert (SMV': sm_valid mu m1' m2').
        split; intros; 
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
      intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
          try rewrite (storev_freshloc _ _ _ _ _ P);
          try rewrite (storev_freshloc _ _ _ _ _ H1); intuition.
      econstructor.
        econstructor; trivial. 
      intuition.
      destruct vaddr; inv H1.
        eapply REACH_Store; try eassumption. 
          inv B. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.   
                  inv D. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
      assert (VaddrMu: val_inject (as_inj mu) vaddr vaddr').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr. 
      assert (VMu: val_inject (as_inj mu) v v').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr. 
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _ 
          INJ H1 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
      rewrite Hmm1 in P. inv P. assumption. }
{ (* Scall *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
     exploit sel_exprlist_inject; eauto.
     (*WAS: exploit sel_exprlist_correct; eauto.*) intros [vargs' [C D]].
     exploit classify_call_correct; eauto. 
     destruct (classify_call hf ge a) as [ | id | ef].  
     (* indirect *)
       exploit sel_expr_inject; eauto. 
       (*exploit sel_expr_correct; eauto.*) intros [vf' [A B]].
       eexists; eexists. 
       split. left. 
         apply corestep_plus_one.  
            econstructor. 
               simpl. apply sel_expr_silent; trivial.
               apply sel_exprlist_silent; trivial.
            econstructor; eauto. apply C. 
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
             apply sig_function_translated.
       simpl. exists mu. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
         intuition. 
     (* direct *)
       intros [b [U V]]. subst. 
       destruct H14 as [spb [i [spb' [SP [SP' Jsp]]]]]. subst.
       assert (Jb:  restrict (as_inj mu) (vis mu) b = Some (b, 0)).
         apply meminj_preserves_genv2blocks in PGR.
         destruct PGR as [PGR1 _]. eapply PGR1.
         unfold genv2blocks. simpl. exists id; trivial.
       eexists; eexists. 
       split. left. rewrite <- symbols_preserved in U. 
         apply corestep_plus_one. 
            econstructor. 
              simpl. trivial.
              apply sel_exprlist_silent; trivial.
            econstructor; eauto. apply C. 
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
            apply sig_function_translated. 
       simpl. exists mu. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
           exists spb, i, spb'. intuition.
         intuition. 
     (* turned into Sbuiltin *)
       intros [EQ OBS]. subst fd.  
       eexists; eexists. 
       split. right. split. omega.
           eapply corestep_star_zero. 
       exists mu. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
           try rewrite freshloc_irrefl; intuition.
       econstructor.
         eapply match_builtin_1; try eassumption. 
         intuition. }
{ (* Stailcall *) 
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      assert (GFPR: globalfunction_ptr_inject (restrict (as_inj mu) (vis mu))). 
            eapply restrict_GFP_vis; eassumption.
      exploit sel_expr_inject; eauto. intros [vf' [A B]].
      exploit sel_exprlist_inject; eauto. intros [vargs' [C D]].
      destruct H15 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
            apply eq_sym in X; inv X.
      destruct (restrictD_Some _ _ _ _ _ Hsp).
      exploit (free_parallel_inject (as_inj mu)); eauto. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *. 
      eexists; eexists. 
      split. left.
        apply corestep_plus_one. 
        exploit classify_call_correct; eauto.    
        destruct (classify_call hf ge a) as [ | id | ef]; intros.
            econstructor. 
              simpl. apply sel_expr_silent; trivial.
              apply sel_exprlist_silent; trivial.
            econstructor; eauto. apply C. 
            eapply functions_translated; eauto. 
            apply sig_function_translated.
            eassumption.
        destruct H5 as [b [U V]].  
            econstructor; eauto. 
              simpl; trivial.
              apply sel_exprlist_silent; trivial.
            econstructor; eauto.
            rewrite symbols_preserved; eauto.
            eapply functions_translated; eauto. subst vf; auto.
            rewrite Genv.find_funct_find_funct_ptr in H1.
               destruct (GFPR _ _ H1).
               inv B. rewrite H9 in H5; inv H5. eauto.
            apply sig_function_translated.
        simpl. econstructor; auto.
                 simpl. apply sel_expr_silent; trivial.
                 apply sel_exprlist_silent; trivial.
                 econstructor; auto. 
           eassumption. 
            eapply functions_translated; eauto.
            apply sig_function_translated.
       exists mu. simpl.
       assert (SMV': sm_valid mu m1' m2').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
       intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H3).
        repeat split; extensionality bb; intuition.
       assert (RC': REACH_closed m1' (vis mu)).
         eapply REACH_closed_free; eassumption.
       constructor.
         constructor; auto. 
           apply call_cont_commut; auto.
           eapply inject_restrict; eassumption.
         intuition. }
{  (* Sbuiltin *) 
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_exprlist_inject; eauto. intros [vargs' [P Q]].
      exploit (inlineable_extern_inject _ _ GDE); 
        try eapply Q; try eassumption.
      intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
      eexists; eexists. 
      split. left.
        apply corestep_plus_one. 
          econstructor.
              apply sel_exprlist_silent; trivial. 
              eauto. eassumption. assumption.
      exists mu'; intuition.
      split.
        econstructor. eauto. 
          eapply match_cont_sub; try eassumption.
             apply intern_incr_restrict; eassumption.
          assert (EE: env_inject (restrict (as_inj mu') (vis mu')) e e').
            eapply env_inject_sub; try eassumption. 
              apply intern_incr_restrict; eassumption.
            destruct optid; simpl; trivial.
              eapply set_var_inject; try eassumption.
          eapply inject_restrict; assumption.
          destruct H14 as [bsp [i [bsp' [? [? Hsp]]]]]; subst.
            exists bsp, i, bsp'. split; trivial. split; trivial.
            eapply intern_incr_restrict; eassumption.
        intuition.
        eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
        red. intros b fbb Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
        assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. eapply Glob; eassumption. }
{ (* Seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [Glob [SMV [WD INJ]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      eexists; eexists. 
      split. left.
        apply corestep_plus_one. 
            econstructor. 
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality bb; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
         intuition. }
{ (* Sifthenelse *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
      assert (Val.bool_of_val v' b). 
        inv H0; inv B; econstructor.
      exists (CMinSel_State (sel_function hf ge f) 
           (if b then sel_stmt hf ge s1 else sel_stmt hf ge s2) k' (Vptr spb' i) e').
      exists m2.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto. 
              apply sel_condexpr_silent; trivial.
            eapply eval_condexpr_of_expr; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. destruct b; trivial.
         exists spb, i, spb'. split; trivial. split; trivial.
       intuition. }
{ (* Sloop *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sblock *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sexit0_block *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sswitch *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      exploit sel_expr_inject; eauto. intros [v' [A B]]. inv B.
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
            apply sel_expr_silent; trivial.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
       intuition. }
{ (* Sreturn None *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      destruct H12 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *. 
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto. 
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp). 
        eapply free_free_inject; try eassumption.
          simpl.  rewrite Zplus_0_r. apply P. }
{ (* Sreturn Some *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *. 
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
            apply sel_expr_silent; trivial.
      exists mu; simpl.
      assert (SMV': sm_valid mu m1' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H0).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto. 
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp). 
        eapply free_free_inject; try eassumption. 
          simpl. rewrite Zplus_0_r. apply P. }
{ (* Slabel *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
       intuition. }
{ (* Sgoto *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      exploit (find_label_commut (restrict (as_inj mu) (vis mu)) lbl 
              (Cminor.fn_body f) (Cminor.call_cont k)).
        apply call_cont_commut; eauto.
      rewrite H. 
      destruct (find_label lbl (sel_stmt hf ge (Cminor.fn_body f)) (call_cont k'0))
          as [[s'' k'']|] eqn:?; intros; try contradiction.
      destruct H. 
      eexists; eexists.
      split. left. 
        apply corestep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
       intuition. }
{ (* internal function *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.   
      (*WAS: exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. intros [m2' [A B]]. *)
      exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl. 
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [A [B C]]]]]]]].
      eexists; eexists.
      split. left.
        apply corestep_plus_one. 
            econstructor; eauto.
      simpl.
      assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
      exists mu'. simpl. intuition.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H6).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; eassumption.
         eapply intern_incr_vis; eassumption.
  split.
    econstructor; eauto.  
      eapply match_cont_sub; try eassumption.
      eapply env_inject_sub; try eassumption. 
      apply set_locals_inject. apply set_params_inject. assumption.
    eapply inject_restrict; eassumption. 
    red. exists sp, Int.zero, b'. intuition.
      apply restrictI_Some; trivial. unfold vis.
      destruct (joinD_Some _ _ _ _ _ A) as [EXT | [EXT LOC]].
         assert (E: extern_of mu = extern_of mu') by eapply IntInc'.
         rewrite <- E in EXT.
         assert (DomSrc mu sp = true). eapply extern_DomRng'; eassumption.
         congruence.
      destruct (local_DomRng _ H1 _ _ _ LOC). rewrite H6; trivial.
  intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m:=m1)(tm:=m2); try eassumption. 
      intros. apply as_inj_DomRng in H6.
              split; eapply SMV; eapply H6.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H6). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
      apply Glob in H6. rewrite <-FF; trivial. }
(*No external call cases -- Cminor does not have 
  unobservable external calls*)
{ (* return *) 
  destruct MC as [SMC PRE].
  inv SMC.
  { inv H1.
    eexists; eexists. 
    split. left. eapply corestep_plus_one.
          econstructor. 
    exists mu; simpl. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition. }
  { (* return of an external call turned into a Sbuiltin *)
  eexists; eexists.
  split. right; split. omega.
         eapply corestep_star_zero.
  exists mu; simpl. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition. } }
Qed.

Lemma MATCH_effcore_diagram: 
  forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
      (CS: effstep (cmin_eff_sem hf) ge U1 st1 m1 st1' m1')
      st2 mu m2 
      (EffSrc: forall b ofs, U1 b ofs = true -> vis mu b = true)
      (MC: MATCH st1 mu st1 m1 st2 m2)
      (R: list_norepet (map fst (prog_defs prog))),
  exists st2' m2' (U2 : block -> Z -> bool),
    (effstep_plus (cminsel_eff_sem hf) tge U2 st2 m2 st2' m2' \/
      (measure st1' < measure st1)%nat /\
       effstep_star (cminsel_eff_sem hf) tge U2 st2 m2 st2' m2')
  /\ exists mu',
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH st1' mu' st1' m1' st2' m2' /\
     SM_wd mu' /\
     sm_valid mu' m1' m2' /\
    (forall b2 ofs,
      U2 b2 ofs = true ->
      visTgt mu b2 = true /\
      (locBlocksTgt mu b2 = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b2, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof.
  intros. 
  assert (THELPERS:= helpers_correct_preserved); clear HELPERS.
  assert (SymbPres:= symbols_preserved).
  assert (GDE:= GDE_lemma).
  induction CS; simpl in *.
{ (*skip seq*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists. eexists. eexists.
      split. left.
        apply effstep_plus_one.
          econstructor.   
      simpl. exists mu; intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition. }
{ (*skip block*)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists. eexists. eexists.
      split. left.
        apply effstep_plus_one.
          econstructor. 
      simpl. exists mu; intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
        try rewrite freshloc_irrefl; intuition.
      econstructor.
        econstructor; eauto.
        intuition. }
{ (* skip call *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      destruct H13 as [spp [i [spp' [X [X' Jsp]]]]]. inv X.
      rename spp into sp. rename spp' into sp'.
      destruct (restrictD_Some _ _ _ _ _ Jsp).
      exploit (free_parallel_inject (as_inj mu)); try eassumption. intros [m2' [A B]].
      (*WAS: exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].*)
      simpl in A. rewrite Zplus_0_r in A.
      eexists. eexists. eexists.
      split. left.  
         apply effstep_plus_one.  
           econstructor; eauto. inv H10; trivial. 
      simpl. exists mu.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      assert (RC': REACH_closed m' (vis mu)).
        eapply REACH_closed_free; eassumption.
      intuition. 
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  A).
        rewrite (freshloc_free _ _ _ _ _  H0).
        repeat split; extensionality b; intuition.
      econstructor.
        econstructor; eauto. eapply free_free_inject; try eassumption.
          simpl; rewrite Zplus_0_r. assumption.
        (*another proof of this Mem.inject fact is this:
            eapply inject_mapped; try eassumption.
            eapply restrict_mapped_closed; try eassumption.
            eapply inject_REACH_closed; eassumption.
            apply restrict_incr.*)
      intuition. (*
        eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Jsp). 
        eapply free_free_inject; eassumption. *)
      apply FreeEffectD in H3. destruct H3 as [? [VB Arith2]]; subst.
        eapply visPropagateR; eassumption.
      eapply FreeEffect_PropagateLeft; eassumption. }
{ (* assign *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.  
      exploit sel_expr_inject; eauto.
      (*WAS: exploit sel_expr_corect; eauto.*) intros [v' [A B]].
      eexists; eexists. eexists.
      split. left.
         apply effstep_plus_one. 
           econstructor; eauto.
           apply sel_expr_silent; trivial.
      simpl. exists mu. intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      split.
        econstructor; trivial. 
          red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
            inv H0. exists v'; auto.
            eauto.
          (*WAS:apply set_var_lessdef; auto.*)
      intuition. }
{ (* store *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.  
      (*WAS:exploit sel_expr_correct.*)
      exploit sel_expr_inject. eexact H. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [vaddr' [A B]].
      (*WAS: exploit sel_expr_correct.*) 
      exploit sel_expr_inject. eexact H0. eauto. eauto. assumption. assumption.
          assumption. eassumption. intros [v' [C D]].
      (*WAS:exploit Mem.storev_extends; eauto. intros [m2' [P Q]].*)
      exploit Mem.storev_mapped_inject; eauto. intros [m2' [P Q]]. 
      eexists; eexists. exists (StoreEffect vaddr' (encode_val chunk v')).
      split. left.
         apply effstep_plus_one.
          eapply eval_effstore; eauto.
          apply sel_expr_silent; trivial.
          apply sel_expr_silent; trivial.
      simpl. exists mu.
      assert (SMV': sm_valid mu m' m2').
        split; intros; 
          eapply storev_valid_block_1; try eassumption;
          eapply SMV; assumption.
      intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
        repeat split; extensionality b; 
          try rewrite (storev_freshloc _ _ _ _ _ P);
          try rewrite (storev_freshloc _ _ _ _ _ H1); intuition.
      econstructor.
        econstructor; trivial. 
      intuition.
      destruct vaddr; inv H1.
        eapply REACH_Store; try eassumption. 
          inv B. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros. rewrite getBlocks_char in H1. destruct H1.
                  destruct H1; try contradiction. subst.   
                  inv D. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
      assert (VaddrMu: val_inject (as_inj mu) vaddr vaddr').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr. 
      assert (VMu: val_inject (as_inj mu) v v').
        eapply val_inject_incr; try eassumption.
        apply restrict_incr. 
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _ 
          INJ H1 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
        rewrite Hmm1 in P. inv P. assumption.
      apply StoreEffectD in H2. destruct H2 as [i [VADDR' _]]. subst.
        inv B; inv H1. eapply visPropagateR; eassumption.
      eapply StoreEffect_PropagateLeft; eassumption. }
{ (* Scall *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
     exploit sel_exprlist_inject; eauto.
     (*WAS: exploit sel_exprlist_correct; eauto.*) intros [vargs' [C D]].
     exploit classify_call_correct; eauto. 
     destruct (classify_call hf ge a) as [ | id | ef].  
     (* indirect *)
       exploit sel_expr_inject; eauto. 
       (*exploit sel_expr_correct; eauto.*) intros [vf' [A B]].
       eexists; eexists. eexists.
       split. left. 
         apply effstep_plus_one. 
            econstructor. 
              simpl. apply sel_expr_silent; trivial.
              apply sel_exprlist_silent; trivial.
            econstructor; eauto. apply C. 
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption. 
             apply sig_function_translated. 
       simpl. exists mu. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality b; 
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
         intuition. 
     (* direct *)
       intros [b [U V]]. subst. 
       destruct H15 as [spb [i [spb' [SP [SP' Jsp]]]]]. subst.
       assert (Jb:  restrict (as_inj mu) (vis mu) b = Some (b, 0)).
         apply meminj_preserves_genv2blocks in PGR.
         destruct PGR as [PGR1 _]. eapply PGR1.
         unfold genv2blocks. simpl. exists id; trivial.
       eexists; eexists. eexists.
       split. left. rewrite <- symbols_preserved in U. 
         apply effstep_plus_one.
            econstructor. 
            simpl. trivial.
            apply sel_exprlist_silent; trivial.
            econstructor; eauto. apply C. 
            eapply functions_translated; eauto.
            eapply restrict_GFP_vis; eassumption.
            apply sig_function_translated.
       simpl. exists mu. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
           try rewrite freshloc_irrefl; intuition.
       constructor.
         constructor; eauto. constructor; eauto.
           exists spb, i, spb'. intuition.
         intuition. 
     (* turned into Sbuiltin *)
       intros [EQ OBS]. subst fd.  
       eexists; eexists; exists EmptyEffect. 
       split. right. split. omega.
           eapply effstep_star_zero. 
       exists mu. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
           try rewrite freshloc_irrefl; intuition.
       econstructor.
         eapply match_builtin_1; try eassumption. 
         intuition. }
{ (* Stailcall *) 
      destruct MC as [SMC PRE].
      inv SMC. simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      assert (GFPR: globalfunction_ptr_inject (restrict (as_inj mu) (vis mu))). 
            eapply restrict_GFP_vis; eassumption.
      exploit sel_expr_inject; eauto. intros [vf' [A B]].
      exploit sel_exprlist_inject; eauto. intros [vargs' [C D]].
      destruct H16 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
            apply eq_sym in X; inv X.
      destruct (restrictD_Some _ _ _ _ _ Hsp).
      exploit (free_parallel_inject (as_inj mu)); eauto. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *. 
      eexists; eexists. eexists.
      split. left. simpl in *.
        apply effstep_plus_one. 
        exploit classify_call_correct; eauto.    
        destruct (classify_call hf ge a) as [ | id | ef]; intros.
            econstructor.
            simpl. apply sel_expr_silent; trivial.
            apply sel_exprlist_silent; trivial.
            econstructor; eauto. apply C. 
            eapply functions_translated; eauto. 
            apply sig_function_translated.
            eassumption.
        destruct H5 as [b [U V]].  
            econstructor; eauto.
              simpl. trivial.
              apply sel_exprlist_silent; trivial.
             econstructor; eauto.
            rewrite symbols_preserved; eauto.
            eapply functions_translated; eauto. subst vf; auto.
            rewrite Genv.find_funct_find_funct_ptr in H1.
               destruct (GFPR _ _ H1).
               inv B. rewrite H9 in H5; inv H5. eauto.   
            apply sig_function_translated.
        destruct H5 as [FD OBS]; subst fd. 
          econstructor; eauto.
           simpl. apply sel_expr_silent; trivial.
           apply sel_exprlist_silent; trivial.  
           econstructor; auto. eassumption.
           eapply functions_translated; eauto.
       exists mu. simpl.
       assert (SMV': sm_valid mu m' m2').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
       intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        rewrite (freshloc_free _ _ _ _ _  P).
        rewrite (freshloc_free _ _ _ _ _  H3).
        repeat split; extensionality bb; intuition.
       assert (RC': REACH_closed m' (vis mu)).
         eapply REACH_closed_free; eassumption.
       constructor.
         constructor; auto. 
           apply call_cont_commut; auto.
           eapply inject_restrict; eassumption.
         intuition.
         apply FreeEffectD in H5. destruct H5 as [? [VB Arith2]]; subst.
           eapply visPropagateR; eassumption.
      eapply FreeEffect_PropagateLeft; eassumption.  }
{ (* Sbuiltin *) 
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_exprlist_inject; eauto. intros [vargs' [P Q]].
      exploit (inlineable_extern_inject _ _ GDE_lemma);
          try eapply Q; try eassumption.
      intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
      eexists; eexists; eexists. 
      split. left.
        apply effstep_plus_one. 
          econstructor.
            apply sel_exprlist_silent; trivial. 
          eauto. eassumption. assumption.
      exists mu'. split; trivial. split; trivial. split; trivial.
      split.
        split. 
          econstructor. eauto. 
            eapply match_cont_sub; try eassumption.
              apply intern_incr_restrict; eassumption.
           assert (EE: env_inject (restrict (as_inj mu') (vis mu')) e e').
             eapply env_inject_sub; try eassumption. 
               apply intern_incr_restrict; eassumption.
             destruct optid; simpl; trivial.
               eapply set_var_inject; try eassumption.
           eapply inject_restrict. assumption. intuition.
           destruct H14 as [bsp [i [bsp' [? [? Hsp]]]]]; subst.
             exists bsp, i, bsp'. split; trivial. split; trivial.
             eapply intern_incr_restrict; eassumption.
         intuition.
         eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
         red; intros b fb Hb. destruct (GFP _ _ Hb).
           split; trivial.
           eapply intern_incr_as_inj; eassumption.
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
            rewrite <- FRG. eapply Glob; eassumption.
       split; trivial. split; trivial.
       eapply BuiltinEffect_Propagate; eassumption. }
{ (* Seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      eexists; eexists. exists EmptyEffect.
      split. left.
        apply effstep_plus_one. 
            econstructor. 
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality bb; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
         intuition. }
{ (* Sifthenelse *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
      assert (Val.bool_of_val v' b). 
        inv H0; inv B; econstructor.
      exists (CMinSel_State (sel_function hf ge f) 
           (if b then sel_stmt hf ge s1 else sel_stmt hf ge s2) k' (Vptr spb' i) e').
      exists m2. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
            apply sel_condexpr_silent; trivial.
            eapply eval_condexpr_of_expr; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. destruct b; trivial.
         exists spb, i, spb'. split; trivial. split; trivial.
       intuition. }
{ (* Sloop *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sblock *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sexit0_block *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sexit_seq *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *. inv H8.
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. econstructor; eauto. 
       intuition. }
{ (* Sswitch *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      exploit sel_expr_inject; eauto. intros [v' [A B]]. inv B.
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
            apply sel_expr_silent; trivial.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
       intuition. }
{ (* Sreturn None *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      destruct H12 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *. 
      eexists; eexists. eexists.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto. 
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp). 
        eapply free_free_inject; try eassumption.
          simpl.  rewrite Zplus_0_r. apply P.
        apply FreeEffectD in H0. destruct H0 as [? [VB Arith2]]; subst.
          eapply visPropagateR; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
          eapply FreeEffect_PropagateLeft; eassumption. }
{ (* Sreturn Some *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      (*WAS:exploit Mem.free_parallel_extends; eauto.*)
      exploit sel_expr_inject; eauto. intros [v' [A B]].
      destruct H13 as [spb [i [spb' [X [Y Hsp]]]]]; subst.
        apply eq_sym in X; inv X.
      exploit free_parallel_inject; try eassumption. intros [m2' [P Q]].
      simpl in *. rewrite Zplus_0_r in *. 
      eexists; eexists. eexists.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
            apply sel_expr_silent; trivial.
      exists mu; simpl.
      assert (SMV': sm_valid mu m' m2').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.
      intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
         rewrite (freshloc_free _ _ _ _ _  P).
         rewrite (freshloc_free _ _ _ _ _  H0).
         repeat split; extensionality bb; intuition.
       constructor.
         constructor; auto. 
           apply call_cont_commut; auto.
         intuition.
         eapply REACH_closed_free; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp). 
        eapply free_free_inject; try eassumption. 
          simpl. rewrite Zplus_0_r. apply P.
        apply FreeEffectD in H1. destruct H1 as [? [VB Arith2]]; subst.
          eapply visPropagateR; eassumption.
        destruct (restrictD_Some _ _ _ _ _ Hsp).
        eapply FreeEffect_PropagateLeft; eassumption. }
{ (* Slabel *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      eexists; eexists. exists EmptyEffect.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
       intuition. }
{ (* Sgoto *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition. 
      exploit (find_label_commut (restrict (as_inj mu) (vis mu)) 
          lbl (Cminor.fn_body f) (Cminor.call_cont k)).
        apply call_cont_commut; eauto.
      rewrite H. 
      destruct (find_label lbl (sel_stmt hf ge (Cminor.fn_body f)) (call_cont k'0))
          as [[s'' k'']|] eqn:?; intros; try contradiction.
      destruct H0. 
      eexists; eexists. eexists.
      split. left. 
        apply effstep_plus_one. 
            econstructor; eauto.
      exists mu; simpl; intuition. 
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
       intuition. }
{ (* internal function *)
      destruct MC as [SMC PRE].
      inv SMC; simpl in *.
      destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.   
      (*WAS: exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl. intros [m2' [A B]]. *)
      exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl. 
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [A [B C]]]]]]]].
      eexists; eexists. eexists.
      split. left.
        apply effstep_plus_one. 
            econstructor; eauto.
      simpl.
      assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
      exists mu'. simpl. intuition.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H6).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; eassumption.
         eapply intern_incr_vis; eassumption.
  split.
    econstructor; eauto.  
      eapply match_cont_sub; try eassumption.
      eapply env_inject_sub; try eassumption. 
      apply set_locals_inject. apply set_params_inject. assumption.
    eapply inject_restrict; eassumption.
    red. exists sp, Int.zero, b'. intuition.
      apply restrictI_Some; trivial. unfold vis.
      destruct (joinD_Some _ _ _ _ _ A) as [EXT | [EXT LOC]].
         assert (E: extern_of mu = extern_of mu') by eapply IntInc'.
         rewrite <- E in EXT.
         assert (DomSrc mu sp = true). eapply extern_DomRng'; eassumption.
         congruence.
      destruct (local_DomRng _ H1 _ _ _ LOC). rewrite H6; trivial.
  intuition. 
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros. apply as_inj_DomRng in H6.
              split; eapply SMV; eapply H6.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H6). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
      apply Glob in H6. rewrite <-FF; trivial. }
(*No external call cases -- Cminor does not have 
  unobservable external calls*)
{ (* return *) 
  destruct MC as [SMC PRE].
  inv SMC.
  { inv H1.
    eexists; eexists. exists EmptyEffect.
    split. left. eapply effstep_plus_one.
          econstructor.
    exists mu; simpl. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition. }
  { (* return of an external call turned into a Sbuiltin *)
   eexists; eexists. exists EmptyEffect.
   split. right; split. omega.
         eapply effstep_star_zero.
   exists mu; simpl. intuition.
       apply intern_incr_refl. 
       apply sm_inject_separated_same_sminj.
       apply sm_locally_allocatedChar.
        repeat split; extensionality b'; 
           rewrite freshloc_irrefl; intuition.
       econstructor.
         econstructor; eauto. 
         destruct optid; simpl.
           eapply set_var_inject; auto.
         assumption.
       intuition. } }
Qed. 

Theorem transl_program_correct:
  forall (TRANSL: sel_program prog = OK tprog)
         (R: list_norepet (map fst (prog_defs prog)))
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
SM_simulation.SM_simulation_inject (cmin_eff_sem hf)
   (cminsel_eff_sem hf) ge tge.
Proof.
intros.
assert (GDE: genvs_domain_eq ge tge).
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros. 
     split; intros; destruct H as [id Hid].
       rewrite <- symbols_preserved in Hid.
       exists id; trivial.
     rewrite symbols_preserved in Hid.
       exists id; trivial.
    rewrite varinfo_preserved. split; intros; trivial.
 eapply effect_simulations_lemmas.inj_simulation_star with
  (match_states:=MATCH) (measure:=measure).
(*genvs_dom_eq*)
  assumption.
(*match_wd*)
  intros; apply H.
(*match_visible*)
  intros. apply H.
(*match_restrict*)
  apply Match_restrict.
(*match_valid*)
  intros. apply H.
(*match_genv*)
  apply Match_genv.
(*initial_core*)
  { intros.
    apply (MATCH_init_cores _ _ _); eauto.
    destruct init_mem as [m0 INIT].
    exists m0; split; auto.
    unfold meminj_preserves_globals in H2.    
    destruct H2 as [A [B C]].

    assert (P: forall p q, {Ple p q} + {Plt q p}).
      intros p q.
      case_eq (Pos.leb p q).
      intros TRUE.
      apply Pos.leb_le in TRUE.
      left; auto.
      intros FALSE.
      apply Pos.leb_gt in FALSE.
      right; auto.

    cut (forall b, Plt b (Mem.nextblock m0) -> 
           exists id, Genv.find_symbol ge id = Some b). intro D.
    
    split.
    destruct (P (Mem.nextblock m0) (Mem.nextblock m1)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H2.
    assert (Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - H7; unfold Mem.valid_block in H7.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H2.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H7; unfold Mem.valid_block in H7.
    xomega.
    
    intros b LT.    
    unfold ge. 
    apply valid_init_is_global with (b0 := b) in INIT.
    eapply INIT; auto.
    apply R.
    apply LT. }
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GFP [GF [VAL [WD INJ]]]]]]]. 
    destruct c1; inv H0. destruct k; inv H1.
    inv MC. exists v'.
    split. assumption.
    split. assumption.
    simpl. inv H1. trivial. }
(* at_external*)
  { apply MATCH_atExternal. }
(* after_external*)
  { apply MATCH_AfterExternal. }
(* core_diagram*)
  { intros. exploit MATCH_diagram; eauto.
    intros [st2' [m2' [CS2 [mu' MU']]]].
    exists st2', m2', mu'. intuition. }
(* effcore_diagram*)
  { intros. exploit MATCH_effcore_diagram; eauto. 
    intros [st2' [m2' [U2 [CS2 [mu' [? [? [? [? [? [? ?]]]]]]]]]]].
    exists st2', m2', mu'.
    repeat (split; try assumption).
    exists U2. split; assumption. }
Qed.

End PRESERVATION.
