Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.

(*LENB: again, we import the modified Asm*)
Require Import Asm_comp. 
Require Import Asm_coop. 

Require Import mem_lemmas. (*for mem_forward*)
Require Import semantics.
Require Import effect_semantics.
Require Import BuiltinEffects.
Require Import load_frame.

Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Section ASM_EFF.
Variable hf : I64Helpers.helper_functions.

Section EFFSEM.
Definition effect_instr (ge:genv) (c: code) (i: instruction) (rs: regset) (m: mem) 
           : (block -> Z -> bool)  :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 => EmptyEffect
  | Pmov_ri rd n => EmptyEffect
  | Pmov_ra rd id => EmptyEffect
  | Pmov_rm rd a => EmptyEffect
  | Pmov_mr a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mint32 (rs r1)))
  | Pmovsd_ff rd r1 => EmptyEffect
  | Pmovsd_fi rd n => EmptyEffect
  | Pmovsd_fm rd a => EmptyEffect
  | Pmovsd_mf a r1 => (StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64al32 (rs r1)))
  | Pfld_f r1 => EmptyEffect
  | Pfld_m a => EmptyEffect
  | Pfstp_f rd => EmptyEffect
  | Pfstp_m a => StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat64al32 (rs ST0))
  | Pxchg_rr r1 r2 => EmptyEffect

  (** Moves with conversion *)
  | Pmovb_mr a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mint8unsigned (rs r1))
  | Pmovw_mr a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mint16unsigned (rs r1))
  | Pmovzb_rr rd r1 => EmptyEffect
  | Pmovzb_rm rd a => EmptyEffect
  | Pmovsb_rr rd r1 => EmptyEffect
  | Pmovsb_rm rd a => EmptyEffect
  | Pmovzw_rr rd r1 => EmptyEffect
  | Pmovzw_rm rd a => EmptyEffect
  | Pmovsw_rr rd r1 => EmptyEffect
  | Pmovsw_rm rd a => EmptyEffect
  | Pcvtss2sd_fm rd a => EmptyEffect
  | Pcvtsd2ss_ff rd r1 => EmptyEffect
  | Pcvtsd2ss_mf a r1 => StoreEffect (eval_addrmode ge a rs) (encode_val Mfloat32 (rs r1))
  | Pcvttsd2si_rf rd r1 => EmptyEffect
  | Pcvtsi2sd_fr rd r1 => EmptyEffect

  (** Integer arithmetic *)
  | Plea rd a => EmptyEffect
  | Pneg rd => EmptyEffect
  | Psub_rr rd r1 => EmptyEffect
  | Pimul_rr rd r1 => EmptyEffect
  | Pimul_ri rd n => EmptyEffect
  | Pimul_r r1 => EmptyEffect
  | Pmul_r r1 => EmptyEffect
  | Pdiv r1 =>  EmptyEffect
  | Pidiv r1 => EmptyEffect
  | Pand_rr rd r1 => EmptyEffect
  | Pand_ri rd n => EmptyEffect
  | Por_rr rd r1 => EmptyEffect
  | Por_ri rd n => EmptyEffect
  | Pxor_r rd => EmptyEffect
  | Pxor_rr rd r1 => EmptyEffect
  | Pxor_ri rd n => EmptyEffect
  | Psal_rcl rd => EmptyEffect
  | Psal_ri rd n => EmptyEffect
  | Pshr_rcl rd => EmptyEffect
  | Pshr_ri rd n => EmptyEffect
  | Psar_rcl rd => EmptyEffect
  | Psar_ri rd n => EmptyEffect
  | Pshld_ri rd r1 n => EmptyEffect
  | Pror_ri rd n => EmptyEffect
  | Pcmp_rr r1 r2 => EmptyEffect
  | Pcmp_ri r1 n => EmptyEffect
  | Ptest_rr r1 r2 => EmptyEffect
  | Ptest_ri r1 n => EmptyEffect
  | Pcmov c rd r1 => EmptyEffect
  | Psetcc c rd => EmptyEffect

  (** Arithmetic operations over floats *)
  | Paddd_ff rd r1 => EmptyEffect
  | Psubd_ff rd r1 => EmptyEffect
  | Pmuld_ff rd r1 => EmptyEffect
  | Pdivd_ff rd r1 => EmptyEffect
  | Pnegd rd => EmptyEffect
  | Pabsd rd => EmptyEffect
  | Pcomisd_ff r1 r2 => EmptyEffect
  | Pxorpd_f rd => EmptyEffect

  (** Branches and calls *)
  | Pjmp_l lbl => EmptyEffect
  | Pjmp_s id => EmptyEffect
  | Pjmp_r r => EmptyEffect
  | Pjcc cond lbl => EmptyEffect
  | Pjcc2 cond1 cond2 lbl => EmptyEffect
  | Pjmptbl r tbl => EmptyEffect
  | Pcall_s id => EmptyEffect
  | Pcall_r r => EmptyEffect
  | Pret => EmptyEffect
  (** Pseudo-instructions *)
  | Plabel lbl => EmptyEffect
  | Pallocframe sz ofs_ra ofs_link => EmptyEffect
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with
      | None => EmptyEffect 
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with
          | None => EmptyEffect 
          | Some sp =>
              match rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => EmptyEffect
                  | Some m' => (FreeEffect m 0 sz stk) 
                  end
              | _ => EmptyEffect
              end
          end
      end
  | Pbuiltin ef args res =>
     (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)
  | Pannot ef args =>
      EmptyEffect 
  end.

Variable ge: genv.

Inductive asm_effstep: (block -> Z -> bool) -> 
                       state -> mem -> state -> mem -> Prop :=
  | asm_effexec_step_internal:
      forall b ofs f i rs m rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge (fn_code f) i rs m = Next rs' m' ->
      asm_effstep (effect_instr ge (fn_code f) i rs m) (State rs lf) m (State rs' lf) m'
  | asm_effexec_step_builtin:
      forall b ofs f ef args res rs m t vl rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      external_call' ef ge (map rs args) m t vl m' ->
      ~ observableEF hf ef ->
      rs' = nextinstr_nf 
             (set_regs res vl
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_effstep (effect_instr ge (fn_code f) (Pbuiltin ef args res) rs m) 
                  (State rs lf) m (State rs' lf) m'
  | asm_effexec_step_to_external:
      forall b ef args rs m lf,
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_effstep EmptyEffect (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_effexec_step_external:
      forall b callee args res rs m t rs' m' lf
      (OBS: EFisHelper hf callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      asm_effstep  (BuiltinEffect ge callee args m)
         (Asm_CallstateOut callee args rs lf) m (State rs' lf) m'
  (*NOTE [loader]*)
  | asm_exec_initialize_call: 
      forall m args tys retty m1 stk m2 fb z,
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 -> 
      let rs0 := (Pregmap.init Vundef) 
                  #PC <- (Vptr fb Int.zero)
                  #RA <- Vzero 
                  # ESP <- (Vptr stk Int.zero) in
      asm_effstep EmptyEffect 
               (Asm_CallstateIn fb args tys retty) m 
               (State rs0 (mk_load_frame stk retty)) m2.

End EFFSEM.

Section ASM_EFFSEM.
Lemma exec_load_unchanged_on: forall g chunk m a rs rd rs' m' P,
   exec_load g chunk m a rs rd = Next rs' m' ->
   Mem.unchanged_on P m m'.
Proof. intros.
  unfold exec_load in H. 
  remember (Mem.loadv chunk m (eval_addrmode g a rs)) as d.
  destruct d; inv H. apply Mem.unchanged_on_refl.
Qed.

Lemma exec_store_unchanged_on: forall g chunk m a rs rs1 pregs rs' m',
  exec_store g chunk m a rs rs1 pregs = Next rs' m' ->
  Mem.unchanged_on (fun b z => StoreEffect (eval_addrmode g a rs) 
                     (encode_val chunk (rs rs1)) b z = false)
                   m m'.
Proof. intros. unfold exec_store in H.
  remember (Mem.storev chunk m (eval_addrmode g a rs) (rs rs1)) as d.
  destruct d; inv H. apply eq_sym in Heqd.
  eapply StoreEffect_Storev; eassumption. 
Qed.

Lemma goto_label_unchanged_on: forall c0 l rs m rs' m' P,
      goto_label c0 l rs m = Next rs' m' -> 
   Mem.unchanged_on P m m'.
Proof. intros.
  unfold goto_label in H.
   destruct (label_pos l 0 c0); inv H.
   destruct (rs PC); inv H1. 
   apply Mem.unchanged_on_refl. 
Qed. 

Lemma exec_instr_unchanged_on g c i rs m rs' m': forall
      (EI: exec_instr g c i rs m = Next rs' m'),
     Mem.unchanged_on (fun b ofs => effect_instr g c i rs m b ofs = false) m m'.
Proof. intros.
    destruct i; 
    try solve [inv EI;
                try solve [apply Mem.unchanged_on_refl];
                try solve [eapply exec_load_unchanged_on; eauto];
                try solve [eapply exec_store_unchanged_on; eauto];
                try solve [eapply goto_label_unchanged_on; eauto]].  
    inv EI. 
      destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
      destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
      destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (eval_testcond c0 rs); inv H0.
        destruct b; inv H1; apply Mem.unchanged_on_refl.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (eval_testcond c0 rs); inv H0.
        destruct b; inv H1. eapply goto_label_unchanged_on; eauto.
      apply Mem.unchanged_on_refl.
    inv EI.
      destruct (eval_testcond c1 rs); inv H0.
        destruct b; inv H1.
          destruct (eval_testcond c2 rs); inv H0.
            destruct b; inv H1. eapply goto_label_unchanged_on; eauto.
            apply Mem.unchanged_on_refl.
          destruct (eval_testcond c2 rs); inv H0.
            apply Mem.unchanged_on_refl.
    inv EI.
      destruct (rs r); inv H0.
        destruct (list_nth_z tbl (Int.unsigned i)); inv H1.
        eapply goto_label_unchanged_on; eauto.
    inv EI.
      remember (Mem.alloc m 0 sz) as d. 
      destruct d; apply eq_sym in Heqd; inv H0.
      remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as q.
      apply eq_sym in Heqq; destruct q; inv H1.
      remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as w.
      destruct w; apply eq_sym in Heqw; inv H0.
      simpl. 
      split; intros. 
        split; intros. 
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_alloc_1; eassumption.
      apply (Mem.perm_store_2 _ _ _ _ _ _ Heqw) in H1.
        apply (Mem.perm_store_2 _ _ _ _ _ _ Heqq) in H1.
        eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst. apply Mem.fresh_block_alloc in Heqd. contradiction.
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ Heqw).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ Heqq).
        assert (BB: b0 <> b). intros N. subst. apply Mem.fresh_block_alloc in Heqd. apply Mem.perm_valid_block in H0. contradiction.
        rewrite PMap.gso; trivial. 
        rewrite PMap.gso; trivial. 
        eapply EmptyEffect_alloc; eassumption.
    inv EI.
      remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as d.
      destruct d; inv H0.
      remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q.
      destruct q; inv H1.
      remember (rs ESP) as w.
      destruct w; inv H0.
      remember (Mem.free m b 0 sz) as t.
      destruct t; inv H1; apply eq_sym in Heqt.
      eapply unchanged_on_validblock.
      Focus 2. eapply FreeEffect_free; eassumption.
      intuition. unfold effect_instr in H0.
        rewrite <- Heqw, <- Heqd, <- Heqq, Heqt in H0. trivial.
Qed.

Lemma asmstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      asm_effstep g M c m c' m' ->
      (asm_step hf g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. 
intros.
destruct H.
  split. eapply asm_exec_step_internal; eassumption.
  clear -H2. eapply exec_instr_unchanged_on; eassumption.

split. eapply asm_exec_step_builtin; eassumption.
       simpl.
         inv H2.
         eapply BuiltinEffect_unchOn; eassumption. 
split. econstructor; eauto.
       apply Mem.unchanged_on_refl. 
split. econstructor; eauto. 
       inv H1.
       exploit @BuiltinEffect_unchOn. 
         eapply EFhelpers; eassumption.
         eapply H3. 
       unfold BuiltinEffect; simpl.
         destruct callee; simpl; trivial; contradiction.
split. econstructor; eassumption. 
  { assert (sp_fresh: ~Mem.valid_block m stk).
    { eapply Mem.fresh_block_alloc; eauto. }
    eapply mem_unchanged_on_sub_strong.
    eapply unchanged_on_trans with (m2 := m1).
    solve[eapply Mem.alloc_unchanged_on; eauto].
    solve[eapply store_args_unch_on; eauto].
    solve[apply alloc_forward in H0; auto].
    simpl. intros b ofs H2 _ H3. subst. 
    solve[apply sp_fresh; auto]. } 
Qed.       

Lemma asmstep_effax2: forall  g c m c' m',
      asm_step hf g c m c' m' ->
      exists M, asm_effstep g M c m c' m'.
Proof.
intros. (*unfold corestep, Asm_coop_sem in H; simpl in H.*)
  inv H.
  destruct i;
    try solve [eexists; econstructor; try eassumption].
  eexists. eapply asm_effexec_step_builtin; try eassumption. trivial.
  eexists. econstructor; eassumption.
  eexists. econstructor; eauto.
  eexists. econstructor; eauto.
Qed.


Lemma exec_store_valid: forall g chunk m a rs rs1 pregs rs' m' b z,
  exec_store g chunk m a rs rs1 pregs = Next rs' m' ->
  StoreEffect (eval_addrmode g a rs) (encode_val chunk (rs rs1)) b z =
              true ->
  Mem.valid_block m b.
Proof. intros. unfold exec_store in H.
  apply StoreEffectD in H0. destruct H0 as [i [VADDR ARITH]]; subst.
  rewrite VADDR in H.
  remember (Mem.storev chunk m (Vptr b i) (rs rs1)) as d.
  destruct d; inv H; apply eq_sym in Heqd.
  simpl in Heqd.
  apply Mem.store_valid_access_3 in Heqd.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; try eassumption. constructor.
Qed.


Lemma exec_instr_valid_block ge fn i rs1 m1 rs2 m2: forall
      (EI: exec_instr ge fn i rs1 m1 = Next rs2 m2) b z
      (EFFI: effect_instr ge fn i rs1 m1 b z = true),
      Mem.valid_block m1 b.
Proof. intros.
  destruct i; simpl in *; try solve [intuition].
  eapply exec_store_valid; eassumption.
  eapply exec_store_valid; eassumption.
  eapply exec_store_valid; eassumption.
  eapply exec_store_valid; eassumption.
  eapply exec_store_valid; eassumption.
  eapply exec_store_valid; eassumption.
  destruct (Mem.loadv Mint32 m1 (Val.add (rs1 ESP) (Vint ofs_ra))); inv EFFI.
    destruct (Mem.loadv Mint32 m1 (Val.add (rs1 ESP) (Vint ofs_link))); inv H0.
    destruct (rs1 ESP); inv H1.
    remember (Mem.free m1 b0 0 sz) as d. apply eq_sym in Heqd.
    destruct d; inv H0.
    eapply FreeEffect_validblock; eassumption.
  eapply BuiltinEffect_valid_block; eassumption.
Qed.

Lemma asm_effstep_valid: forall (M : block -> Z -> bool) g c m c' m',
      asm_effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof.
intros.
  induction H; try (solve [inv H0]).
  eapply exec_instr_valid_block; eassumption.
  inv H0.
  eapply BuiltinEffect_valid_block; eassumption.
  eapply BuiltinEffect_valid_block; eassumption.
Qed.

Program Definition Asm_eff_sem : 
  @EffectSem genv state.
eapply Build_EffectSem with (sem := Asm_coop_sem hf).
apply asmstep_effax1.
apply asmstep_effax2.
apply asm_effstep_valid. 
Defined.

Require Import semantics_lemmas.

Lemma Asm_eff_sem_det : corestep_fun Asm_eff_sem.
Proof.
intros m m' m'' ge c c' c'' step1 step2.
simpl in step1, step2.
eapply asm_step_det in step1; eauto.
destruct step1; subst; auto.
Qed.

End ASM_EFFSEM.

End ASM_EFF.
