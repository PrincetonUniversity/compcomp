Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Export Maps.
Require Import Events.
Require Import Globalenvs.

Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Import LTL. (*for undef_regs etc*)

Require Import mem_lemmas. (*for mem_forward*)
Require Import semantics.
Require Import effect_semantics.

Require Import Linear.
Require Import Linear_coop.
Require Import BuiltinEffects.

Section LINEAR_EFF.
Variable hf : I64Helpers.helper_functions.

Inductive linear_effstep (ge:genv): (block -> Z -> bool) -> Linear_core -> mem -> Linear_core -> mem -> Prop :=
  | lin_effexec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs' lf,
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lgetstack sl ofs ty dst :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_effexec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs' lf,
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lsetstack src sl ofs ty :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_effexec_Lop:
      forall s f sp op args res b rs m v rs' lf,
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lop op args res :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_effexec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs' lf,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lload chunk addr args dst :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_effexec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs' lf,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      linear_effstep ge (StoreEffect a (encode_val chunk (rs (R src))))
        (Linear_State s f sp (Lstore chunk addr args src :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m'
  | lin_effexec_Lcall:
      forall s f sp sig ros b rs m f' lf,
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lcall sig ros :: b) rs lf) m
        (Linear_Callstate (Stackframe f sp rs b:: s) f' rs lf) m
  | lin_effexec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m' rs0 f0,
      let lf := mk_load_frame rs0 f0 in
      rs' = return_regs (parent_locset0 rs0 s) rs ->
      find_function ge ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      linear_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Linear_State s f (Vptr stk Int.zero) (Ltailcall sig ros :: b) rs lf) m
        (Linear_Callstate s f' rs' lf) m'
  | lin_effexec_Lbuiltin:
      forall s f sp rs m ef args res b t vl rs' m' lf,
      external_call' ef ge (reglist rs args) m t vl m' ->
      ~ observableEF hf ef ->
      rs' = Locmap.setlist (map R res) vl (undef_regs (destroyed_by_builtin ef) rs) ->
      linear_effstep ge (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (reglist rs args)) m)
         (Linear_State s f sp (Lbuiltin ef args res :: b) rs lf) m
         (Linear_State s f sp b rs' lf) m'

(* annotations are observable, so now handled by atExternal
  | lin_effexec_Lannot:
      forall s f sp rs m ef args b t v m',
      external_call' ef ge (map rs args) m t v m' ->
      linear_effstep (Linear_State s f sp (Lannot ef args :: b) rs lf) m
         (Linear_State s f sp b rs lf) m'*)

  | lin_effexec_Llabel:
      forall s f sp lbl b rs m lf,
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Llabel lbl :: b) rs lf) m
        (Linear_State s f sp b rs lf) m
  | lin_effexec_Lgoto:
      forall s f sp lbl b rs m b' lf,
      find_label lbl f.(fn_code) = Some b' ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lgoto lbl :: b) rs lf) m
        (Linear_State s f sp b' rs lf) m
  | lin_effexec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b' lf,
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lcond cond args lbl :: b) rs lf) m
        (Linear_State s f sp b' rs' lf) m
  | lin_effexec_Lcond_false:
      forall s f sp cond args lbl b rs m rs' lf,
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Lcond cond args lbl :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_effexec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs' lf,
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      linear_effstep ge EmptyEffect 
        (Linear_State s f sp (Ljumptable arg tbl :: b) rs lf) m
        (Linear_State s f sp b' rs' lf) m
  | lin_effexec_Lreturn:
      forall s f stk b rs m m' rs0 f0,
      let lf := mk_load_frame rs0 f0 in
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      linear_effstep ge (FreeEffect m 0 (f.(fn_stacksize)) stk)
        (Linear_State s f (Vptr stk Int.zero) (Lreturn :: b) rs lf) m
        (Linear_Returnstate s (sig_res (fn_sig f)) (return_regs (parent_locset0 rs0 s) rs) lf) m'
  | lin_effexec_function_internal0:
      forall s f rs m rs0 f0,
      linear_effstep ge EmptyEffect 
                     (Linear_CallstateIn s (Internal f) rs (mk_load_frame rs0 f0)) m
                     (Linear_Callstate s (Internal f) rs (mk_load_frame (call_regs rs0) f0)) m
  | lin_effexec_function_internal:
      forall s f rs m rs' m' stk lf,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      linear_effstep ge EmptyEffect 
        (Linear_Callstate s (Internal f) rs lf) m
        (Linear_State s f (Vptr stk Int.zero) f.(fn_code) rs' lf) m'

  | lin_effexec_function_external:
      forall s ef args res rs1 rs2 m t m' lf
      (OBS: EFisHelper hf ef),
      args = map rs1 (loc_arguments (ef_sig ef)) ->
      external_call' ef ge args m t res m' ->
      rs2 = Locmap.setlist (map R (loc_result (ef_sig ef))) res rs1 ->
      linear_effstep ge (BuiltinEffect ge ef args m)
          (Linear_Callstate s (External ef) rs1 lf) m
          (Linear_Returnstate s (sig_res (ef_sig ef)) rs2 lf) m'

  | lin_effexec_return:
      forall s f sp lf c retty rs m rs_init,
      linear_effstep ge EmptyEffect 
        (Linear_Returnstate (Stackframe f sp lf c :: s) retty rs rs_init) m
        (Linear_State s f sp c rs rs_init) m.

Lemma linearstep_effax1: forall (M : block -> Z -> bool) g c m c' m',
      linear_effstep g M c m c' m' ->
      (corestep (Linear_memsem hf) g c m c' m' /\
       Mem.unchanged_on (fun (b : block) (ofs : Z) => M b ofs = false) m m').
Proof. 
intros.
  induction H.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         eapply StoreEffect_Storev; eassumption. 
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         eapply FreeEffect_free; eassumption.
  split. unfold corestep; simpl. econstructor; eassumption.
         inv H.
         eapply BuiltinEffect_unchOn; eassumption.
(*  split. unfold corestep; simpl. econstructor; eassumption.
         inv H. eapply ec_builtinEffectPolymorphic; eassumption.
  split. unfold corestep; simpl. econstructor; eassumption.
         inv H. eapply ec_builtinEffectPolymorphic; eassumption.*)
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl.
         eapply lin_exec_Lcond_true; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl.
         eapply lin_exec_Lcond_false; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         eapply FreeEffect_free; eassumption. 
  split. unfold corestep; simpl. econstructor; eassumption.
         eapply Mem.unchanged_on_refl.
  split. unfold corestep; simpl. econstructor; eassumption.
         eapply Mem.alloc_unchanged_on; eassumption.
  split. unfold corestep; simpl. 
         eapply lin_exec_function_external; eassumption.
         inv H0.
       exploit @BuiltinEffect_unchOn. 
         eapply EFhelpers; eassumption.
         eapply H2. 
       unfold BuiltinEffect; simpl.
         destruct ef; simpl; trivial; contradiction.
  split. unfold corestep; simpl. econstructor; eassumption.
         apply Mem.unchanged_on_refl.
Qed.

Lemma linearstep_effax2 g c m c' m':
      corestep (Linear_memsem hf) g c m c' m' ->
      exists M, linear_effstep g M c m c' m'.
Proof.
intros. unfold corestep in H; simpl in H.
  inv H.
    eexists. eapply lin_effexec_Lgetstack; try eassumption. trivial.
    eexists. eapply lin_effexec_Lsetstack; try eassumption. trivial. 
    eexists. eapply lin_effexec_Lop; try eassumption; trivial.
    eexists. eapply lin_effexec_Lload; try eassumption; trivial.
    eexists. eapply lin_effexec_Lstore; try eassumption; trivial.
    eexists. eapply lin_effexec_Lcall; try eassumption; trivial.    
    eexists. eapply lin_effexec_Ltailcall; try eassumption; trivial. 
    eexists. eapply lin_effexec_Lbuiltin; try eassumption; trivial. 
(*    eexists. eapply linear_effstep_Lannot; eassumption.*)
    eexists. eapply lin_effexec_Llabel; try eassumption; trivial.
    eexists. eapply lin_effexec_Lgoto; try eassumption; trivial.
    eexists. eapply lin_effexec_Lcond_true; try eassumption; trivial.
    eexists. eapply lin_effexec_Lcond_false; try eassumption; trivial.
    eexists. eapply lin_effexec_Ljumptable; try eassumption; trivial.
    eexists. eapply lin_effexec_Lreturn; eassumption.
    eexists. eapply lin_effexec_function_internal0; eassumption.
    eexists. eapply lin_effexec_function_internal; try eassumption; trivial.
    eexists. eapply lin_effexec_function_external; try eassumption; trivial.
    eexists. eapply lin_effexec_return.
Qed.

Lemma linear_effstep_curWR: forall (M : block -> Z -> bool) g c m c' m',
      linear_effstep g M c m c' m' ->
      forall b z, M b z = true -> Mem.perm m b z Cur Writable.
Proof.
intros.
induction H; try (solve [inv H0]).
+ eapply storev_curWR; eassumption.
+ eapply free_curWR; eassumption. 
+ inv H. eapply nonobs_extcall_curWR; eassumption.
+ eapply free_curWR; eassumption.  
+ erewrite helpers_EmptyEffect in H0; try eassumption.
  inv H0.
Qed.

Lemma linear_effstep_valid: forall (M : block -> Z -> bool) g c m c' m',
      linear_effstep g M c m c' m' ->
       forall b z, M b z = true -> Mem.valid_block m b.
Proof. intros. eapply Mem.perm_valid_block. eapply linear_effstep_curWR; eassumption. Qed.

Program Definition Linear_eff_sem : 
  @EffectSem genv Linear_core.
Proof.
eapply Build_EffectSem with (sem := Linear_memsem hf)(effstep:=linear_effstep).
apply linearstep_effax1.
apply linearstep_effax2.
apply linear_effstep_curWR.
Defined.

End LINEAR_EFF.