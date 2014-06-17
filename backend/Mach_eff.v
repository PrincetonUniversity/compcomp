Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.

Require Import Mach. 
Require Import Mach_coop. 

Require Import mem_lemmas. (*for mem_forward*)
Require Import core_semantics.
Require Import effect_semantics.
Require Import BuiltinEffects.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Section MACH_EFFSEM.
Variable hf : I64Helpers.helper_functions.
Variable return_address_offset: function -> code -> int -> Prop.

Inductive mach_effstep (ge:genv): (block -> Z -> bool) -> 
                        Mach_core -> mem -> Mach_core -> mem -> Prop :=
  | Mach_effexec_Mlabel:
      forall s f sp lbl c rs m lf,
      mach_effstep ge EmptyEffect 
        (Mach_State s f sp (Mlabel lbl :: c) rs lf) m
        (Mach_State s f sp c rs lf) m
  | Mach_effexec_Mgetstack:
      forall s f sp ofs ty dst c rs m v lf,
      load_stack m sp ty ofs = Some v ->
      mach_effstep ge EmptyEffect 
        (Mach_State s f sp (Mgetstack ofs ty dst :: c) rs lf) m
        (Mach_State s f sp c (rs#dst <- v) lf) m
  | Mach_effexec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs' lf,
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      mach_effstep ge 
        (StoreEffect (Val.add sp (Vint ofs)) (encode_val (chunk_of_type ty) (rs src)))
        (Mach_State s f sp (Msetstack src ofs ty :: c) rs lf) m
        (Mach_State s f sp c rs' lf) m'
  | Mach_effexec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs' args0 tys0 sp0,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (parent_sp0 sp0 s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      mach_effstep ge EmptyEffect 
                   (Mach_State s fb sp (Mgetparam ofs ty dst :: c) rs 
                                       (mk_load_frame sp0 args0 tys0)) m
                   (Mach_State s fb sp c rs' (mk_load_frame sp0 args0 tys0)) m
  | Mach_effexec_Mop:
      forall s f sp op args res c rs m v rs' lf,
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      mach_effstep ge EmptyEffect 
        (Mach_State s f sp (Mop op args res :: c) rs lf) m
        (Mach_State s f sp c rs' lf) m
  | Mach_effexec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs' lf,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      mach_effstep ge EmptyEffect 
        (Mach_State s f sp (Mload chunk addr args dst :: c) rs lf) m
        (Mach_State s f sp c rs' lf) m
  | Mach_effexec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs' lf,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      mach_effstep ge (StoreEffect a (encode_val chunk (rs src)))
        (Mach_State s f sp (Mstore chunk addr args src :: c) rs lf) m
        (Mach_State s f sp c rs' lf) m'
  (*NOTE [loader]*)
  | Mach_effexec_Minitialize_call: 
      forall m args tys m1 stk m2 fb z,
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 -> 
      mach_effstep ge EmptyEffect 
        (Mach_CallstateIn fb args tys) m
        (Mach_Callstate nil fb (Regmap.init Vundef) (mk_load_frame stk args tys)) m2
  | Mach_effexec_Mcall_internal:
      forall s fb sp sig ros c rs m f f' ra callee lf,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      (*NEW: check that the block f' actually contains a function:*)
      Genv.find_funct_ptr ge f' = Some (Internal callee) ->
      mach_effstep ge EmptyEffect 
        (Mach_State s fb sp (Mcall sig ros :: c) rs lf) m
        (Mach_Callstate (Stackframe fb sp (Vptr fb ra) c :: s) f' rs lf) m
  | Mach_effexec_Mcall_external:
      forall s fb sp sig ros c rs m f f' ra callee args lf,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      (*NEW: check that the block f' actually contains a (external) function, 
             and perform the "extra step":*)
      Genv.find_funct_ptr ge f' = Some (External callee) ->
      extcall_arguments rs m sp (ef_sig callee) args ->
      mach_effstep ge EmptyEffect
         (Mach_State s fb sp (Mcall sig ros :: c) rs lf) m
         (Mach_CallstateOut (Stackframe fb sp (Vptr fb ra) c :: s) f' callee args rs lf) m
  | Mach_effexec_Mtailcall_internal:
      forall s fb stk soff sig ros c rs m f f' m' callee sp0 args0 tys0,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      (*NEW: check that the block f' actually contains a function:*)
      Genv.find_funct_ptr ge f' = Some (Internal callee) ->
      mach_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Mach_State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs (mk_load_frame sp0 args0 tys0)) m
        (Mach_Callstate s f' rs (mk_load_frame sp0 args0 tys0)) m'
  | Mach_effexec_Mtailcall_external:
      forall s fb stk soff sig ros c rs m f f' m' callee args sp0 args0 tys0,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      (*NEW: check that the block f' actually contains a function:*)
       Genv.find_funct_ptr ge f' = Some (External callee) ->
      extcall_arguments rs m' (parent_sp0 sp0 s) (ef_sig callee) args ->
      mach_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
         (Mach_State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs (mk_load_frame sp0 args0 tys0)) m
         (Mach_CallstateOut s f' callee args rs (mk_load_frame sp0 args0 tys0)) m'
  | Mach_effexec_Mbuiltin:
      forall s f sp rs m ef args res b t vl rs' m' lf,
      external_call' ef ge rs##args m t vl m' ->
      observableEF hf ef = false ->
      rs' = set_regs res vl (undef_regs (destroyed_by_builtin ef) rs) ->
      mach_effstep ge (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (rs##args)) m)
         (Mach_State s f sp (Mbuiltin ef args res :: b) rs lf) m
         (Mach_State s f sp b rs' lf) m'
(*NO SUPPORT FOR ANNOT YET
  | Mach_effexec_Mannot:
      forall s f sp rs m ef args b vargs t v m',
      annot_arguments rs m sp args vargs ->
      external_call' ef ge vargs m t v m' ->
      mach_effstep (Mach_State s f sp (Mannot ef args :: b) rs) m
         t (Mach_State s f sp b rs) m'*)
  | Mach_effexec_Mgoto:
      forall s fb f sp lbl c rs m c' lf,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      mach_effstep ge EmptyEffect 
        (Mach_State s fb sp (Mgoto lbl :: c) rs lf) m
        (Mach_State s fb sp c' rs lf) m
  | Mach_effexec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs' lf,
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      mach_effstep ge EmptyEffect 
        (Mach_State s fb sp (Mcond cond args lbl :: c) rs lf) m
        (Mach_State s fb sp c' rs' lf) m
  | Mach_effexec_Mcond_false:
      forall s f sp cond args lbl c rs m rs' lf,
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      mach_effstep ge EmptyEffect 
        (Mach_State s f sp (Mcond cond args lbl :: c) rs lf) m
        (Mach_State s f sp c rs' lf) m
  | Mach_effexec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs' lf,
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      mach_effstep ge EmptyEffect 
        (Mach_State s fb sp (Mjumptable arg tbl :: c) rs lf) m
        (Mach_State s fb sp c' rs' lf) m
  | Mach_effexec_Mreturn:
      forall s fb stk soff c rs m f m' sp0 args0 tys0,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      mach_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Mach_State s fb (Vptr stk soff) (Mreturn :: c) rs (mk_load_frame sp0 args0 tys0)) m
        (Mach_Returnstate s (sig_res (fn_sig f)) rs (mk_load_frame sp0 args0 tys0)) m'
  | Mach_effexec_function_internal:
      forall s fb rs m f m1 m2 m3 stk rs' sp0 args0 tys0,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Int.zero in
      store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp0 sp0 s) = Some m2 ->
      store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      mach_effstep ge EmptyEffect 
        (Mach_Callstate s fb rs (mk_load_frame sp0 args0 tys0)) m
        (Mach_State s fb sp f.(fn_code) rs' (mk_load_frame sp0 args0 tys0)) m3

  | Mach_effexec_function_external:
      forall cs f' rs m t rs' callee args res m' lf
      (OBS: observableEF hf callee = false),
      Genv.find_funct_ptr ge f' = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = set_regs (loc_result (ef_sig callee)) res rs ->
      mach_effstep ge (BuiltinEffect ge callee args m)
      (Mach_CallstateOut cs f' callee args rs lf) m
      (Mach_Returnstate cs (sig_res (ef_sig callee)) rs' lf) m'
(*
  | Mach_effexec_function_external:
      forall s fb rs m t rs' ef args res m' lf
      (OBS: observableEF hf ef = false),
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call' ef ge args m t res m' ->
      rs' = set_regs (loc_result (ef_sig ef)) res rs ->
      mach_effstep ge (BuiltinEffect ge ef args m)
         (Mach_Callstate s fb rs lf) m
         (Mach_Returnstate s (sig_res (ef_sig ef)) rs' lf) m'*)

  | Mach_effexec_return:
      forall s f sp ra c retty rs m lf,
      mach_effstep ge EmptyEffect 
        (Mach_Returnstate (Stackframe f sp ra c :: s) retty rs lf) m
        (Mach_State s f sp c rs lf) m.
(*Require Import Axioms.
Lemma BuiltinEffect_decode: forall F V (ge: Genv.t F V) ef args,
 BuiltinEffect ge ef args =
 BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef))
           args).
Proof. intros.
  unfold BuiltinEffect. apply extensionality; intros m. 
  destruct ef; trivial.
  unfold free_Effect in *.
    destruct args; trivial.
    destruct v; trivial.
    destruct args; trivial. simpl.
    remember (Mem.load Mint32 m b (Int.unsigned i - 4)) as d. 
    destruct d; simpl; trivial.
    destruct v0; simpl; trivial.
    apply extensionality; intros bb. 
    apply extensionality; intros z. 
    destruct ( zlt 0 (Int.unsigned i0)); simpl. 
      destruct (zle (Int.unsigned i - 4) z); simpl.
       destruct (zlt z (Int.unsigned i + Int.unsigned i0)); simpl. 
       exfalso. specialize (Int.unsigned_range i). intros [A B]. omega.
Qed.
         subst.
         eapply mem_unchanged_on_sub.
           eapply BuiltinEffect_unchOn. eassumption. 
         simpl. unfold BuiltinEffect. intros.
           destruct ef; simpl; trivial. 
*)
Lemma machstep_effax1: forall (M : block -> Z -> bool) ge c m c' m',
      mach_effstep ge M c m c' m' ->
      (corestep (Mach_coop_sem hf return_address_offset) ge c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. 
intros.
  induction H.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         unfold store_stack in H.
         eapply StoreEffect_Storev; eassumption. 
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         eapply StoreEffect_Storev; eassumption. 
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
  split. eapply Mach_exec_Mcall_internal; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mcall_external; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mtailcall_internal; eassumption.
         eapply FreeEffect_free; eassumption.
  split. eapply Mach_exec_Mtailcall_external; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep, coopsem; simpl. econstructor; eassumption.
         inv H.
         eapply BuiltinEffect_unchOn; eassumption.
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mcond_true; eassumption.
         apply Mem.unchanged_on_refl.
  split. eapply Mach_exec_Mcond_false; eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; try eassumption.
         apply Mem.unchanged_on_refl.
  split. econstructor; eassumption.
         eapply FreeEffect_free; eassumption.
  split. econstructor; eassumption. subst sp.
    subst. 
    unfold store_stack, Val.add in *. 
    rewrite Int.add_zero_l in *.
    simpl in *. 
    remember (Int.unsigned (fn_link_ofs f)) as z1.
    remember (Int.unsigned (fn_retaddr_ofs f)) as z2.
    remember (parent_ra s) as v2. 
    clear Heqz1 H Heqz2 Heqv2.
    split; intros.
    { split; intros.
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_store_1; try eassumption.
        eapply Mem.perm_alloc_1; eassumption.
      apply (Mem.perm_store_2 _ _ _ _ _ _ H2) in H4.
        apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H4.
        eapply Mem.perm_alloc_4; try eassumption.
         intros N; subst. apply Mem.fresh_block_alloc in H0. 
         contradiction. }
    { rewrite (Mem.store_mem_contents _ _ _ _ _ _ H2).
        rewrite (Mem.store_mem_contents _ _ _ _ _ _ H1).
        assert (BB: b <> stk). 
        { intros N. subst. 
          apply Mem.fresh_block_alloc in H0. 
          apply Mem.perm_valid_block in H3. contradiction. }
        rewrite PMap.gso; trivial. 
        rewrite PMap.gso; trivial. 
        eapply EmptyEffect_alloc; eassumption. }
  { split. unfold corestep, coopsem; simpl. econstructor; try eassumption.
    inv H0.
     destruct callee; simpl in *; try discriminate. 
      admit. (*ia64: todo*) 
      admit. (*ia64: todo*)
      inv H2. destruct args; inv H0.
      admit. (*holds todo*)

      inv H2. destruct args; inv H0. 
       split; intros. unfold free_Effect in H0. 
        destruct (eq_block b0 b); simpl in *. subst b0.
          destruct args. rewrite H1 in H0. 
          destruct (eq_block b b); simpl in *. clear e.
          destruct (zlt 0 (Int.unsigned sz)); simpl in *.
          destruct (zle (Int.unsigned lo - 4) ofs); simpl in *.
          destruct (zlt ofs (Int.unsigned lo + Int.unsigned sz)); simpl in *. discriminate.
          split; intros. eapply Mem.perm_free_1; try eassumption. 
             right. right. omega.
          eapply Mem.perm_free_3; try eassumption. 
          split; intros. eapply Mem.perm_free_1; try eassumption. 
             right. left. omega. 
          eapply Mem.perm_free_3; try eassumption. 
           omega. 
          split; intros. eapply Mem.perm_free_1; try eassumption. 
             left. trivial. 
          eapply Mem.perm_free_3; try eassumption. 
SearchAbout Mem.free.
          split; intros.
      destruct (zlt 0 (Int.unsigned sz)); simpl; trivial.
      destruct (zle (Int.unsigned i - 4) ofs); simpl; trivial.
      destruct (zlt ofs (Int.unsigned i + Int.unsigned sz)); simpl; trivial. admit.
eapply free_Effect_unchOn. 
       simpl. eapply extcall_free_sem_intro. Search extcall_free_sem. econstructor. SearchAbout free_Effect.
        remember (type_of_chunk chunk) as toc. 
        destruct toc; destruct args; inv H4.
      inv H1.  apply Mem.unchanged_on_refl.
      split. destruct args; inv H0. 
        remember (type_of_chunk chunk) as toc. 
        destruct toc; destruct args; inv H4. apply Mem.unchanged_on_refl. split.  SearchAbout EmptyEffect.
      apply ; trivial. simpl in *.  inv H2; simpl in *.
     eapply mem_unchanged_on_sub. 
     eapply BuiltinEffect_unchOn; try eapply H2. eassumption.
     unfold BuiltinEffect; simpl. intros.
     destruct callee; simpl; trivial. simpl in *.
      destruct args; simpl. trivial.
      destruct v0; simpl; trivial. simpl in *.
      destruct args; simpl; trivial. inv H2. rewrite H4.
      destruct (eq_block b b0); simpl; trivial; subst.
      destruct (zlt 0 (Int.unsigned sz)); simpl; trivial.
      destruct (zle (Int.unsigned i - 4) ofs); simpl; trivial.
      destruct (zlt ofs (Int.unsigned i + Int.unsigned sz)); simpl; trivial. admit.
    unfold memcpy_Effect. unfold memcpy_Effect in H0. inv H2.
       destruct args. inv H1. inv H1.
       destruct args. inv H12. inv H12.
       destruct args; simpl in *; trivial. 
      destruct (eq_block b bdst); simpl; trivial; subst.
      destruct (zle (Int.unsigned odst) ofs); simpl; trivial.
      destruct (zlt ofs (Int.unsigned odst + sz)); simpl; trivial.
      destruct (valid_block_dec m bdst); simpl; trivial. exfalso. omega.
           inv H0. constructor.  }
  split. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
Qed.

Lemma  machstep_effax2 ge c m c' m':
      corestep (Mach_coop_sem hf return_address_offset) ge c m c' m' ->
      exists M, mach_effstep ge M c m c' m'.
Proof.
  intros. unfold corestep, coopsem in H; simpl in H.
  inv H.
    eexists. eapply Mach_effexec_Mlabel; eassumption.
    eexists. eapply Mach_effexec_Mgetstack; try eassumption; trivial.
    eexists. eapply Mach_effexec_Msetstack; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mgetparam; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mop; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mload; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mstore; try eassumption; trivial.
    eexists. eapply Mach_effexec_Minitialize_call; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcall_internal; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcall_external; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mtailcall_internal; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mtailcall_external; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mbuiltin; try eassumption; trivial.
(*    eexists. eapply Mach_effexec_Mannot; try eassumption; trivial.*)
    eexists. eapply Mach_effexec_Mgoto; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcond_true; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mcond_false; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mjumptable; try eassumption; trivial.
    eexists. eapply Mach_effexec_Mreturn; try eassumption; trivial.
    eexists. eapply Mach_effexec_function_internal; try eassumption; trivial.
    eexists. eapply Mach_effexec_function_external; try eassumption; trivial.
    eexists. eapply Mach_effexec_return; try eassumption; trivial.
Qed.

Lemma mach_effstep_valid: forall (M : block -> Z -> bool) ge c m c' m',
      mach_effstep ge M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof.
intros.
  induction H; try (solve [inv H0]).

  unfold store_stack in H.
  apply StoreEffectD in H0. destruct H0 as [i [VADDR ARITH]]; subst.
  destruct sp; inv H. unfold Val.add in VADDR. inv VADDR.
  apply Mem.store_valid_access_3 in H1.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; try eassumption. constructor.

  apply StoreEffectD in H0. destruct H0 as [ofs [VADDR ARITH]]; subst.
  inv H1. apply Mem.store_valid_access_3 in H2.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; try eassumption. constructor.

  eapply FreeEffect_validblock; eassumption.
  eapply FreeEffect_validblock; eassumption.
  eapply BuiltinEffect_valid_block; eassumption.
  eapply FreeEffect_validblock; eassumption.
  eapply BuiltinEffect_valid_block; eassumption.
Qed.

Program Definition Mach_eff_sem : 
  @EffectSem genv Mach_core.
eapply Build_EffectSem with 
 (sem := Mach_coop_sem hf return_address_offset).
apply machstep_effax1.
apply machstep_effax2.
apply mach_effstep_valid. 
Defined.

End MACH_EFFSEM.