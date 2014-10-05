Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.

(*LENB: We don't import CompCert's original Asm.v, but the modified one*)
Require Import Asm_comp. 

Require Import mem_lemmas. (*for mem_forward*)
Require Import semantics.
Require Import val_casted.
Require Import BuiltinEffects.
Require Import load_frame.

Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
    load_frame.

Section ASM_COOP.
Variable hf : I64Helpers.helper_functions.

Section RELSEM.
Variable ge: genv.

Inductive state: Type :=
  | State: 
      forall (rs: regset)
             (loader: load_frame),     (**r program loader frame *)
        state

  (*Auxiliary state: for marshalling arguments INTO memory*)
  | Asm_CallstateIn: 
      forall (f: block)                (**r pointer to function to call *)
             (args: list val)          (**r arguments passed to initial_core *)
             (tys: list typ)           (**r argument types *)
             (retty: option typ),      (**r return type *)       
        state

  (*Auxiliary state: for marshalling arguments OUT OF memory*)
  | Asm_CallstateOut: 
      forall (f: external_function)    (**r external function to be called *)
             (vals: list val)          (**r at_external arguments *)
             (rs: regset)              (**r register state *)
             (loader: load_frame),     (**r program loader frame *)
        state.

Inductive asm_step: state -> mem -> state -> mem -> Prop :=
  | asm_exec_step_internal:
      forall b ofs (f:function) i rs m rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge (fn_code f) i rs m = Next rs' m' ->
      asm_step (State rs lf) m (State rs' lf) m'
  | asm_exec_step_builtin:
      forall b ofs f ef args res rs m t vl rs' m' lf,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some (Pbuiltin ef args res) ->
      external_call' ef ge (map rs args) m t vl m' ->
      ~ observableEF hf ef ->
      rs' = nextinstr_nf 
             (set_regs res vl
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      asm_step (State rs lf) m (State rs' lf) m'
  | asm_exec_step_to_external:
      forall b ef args rs m lf,
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      asm_step (State rs lf) m (Asm_CallstateOut ef args rs lf) m
  | asm_exec_step_external:
      forall b callee args res rs m t rs' m' lf
      (OBS: EFisHelper hf callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = (set_regs (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      asm_step (Asm_CallstateOut callee args rs lf) m (State rs' lf) m'
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
      asm_step (Asm_CallstateIn fb args tys retty) m 
               (State rs0 (mk_load_frame stk retty)) m2.

Lemma asm_step_det c m c' m' c'' m'' :
  asm_step c m c' m' ->   
  asm_step c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros H H0.
(* determ *)
  inv H; inv H0; Equalities.
  split. constructor. auto.
  discriminate.
  discriminate.
  case_eq (is_I64_helper'_dec hf ef0); intros X _.
  assert (t=t0).
  { eapply EC'_i64_helper_determ in H4; eauto. } subst t0.
  inv H4; inv H10.
  eapply external_call_deterministic in H; eauto. destruct H; subst. split; auto.
  assert (t=t0).
  { eapply EC'_determ in H10; eauto. }
  inv H10; inv H4.
  eapply external_call_deterministic in H0; eauto. destruct H0; subst. auto. split; auto.
  eapply extcall_arguments_determ in H3; eauto. subst. auto.
  case_eq (is_I64_helper'_dec hf callee); intros X _.
  assert (t=t0).
  { eapply EC'_i64_helper_determ in H3; eauto. eapply EFhelpers; eauto. } subst t0.
  inv H3; inv H12.
  eapply external_call_deterministic in H; eauto. destruct H; subst. split; auto.
  assert (t=t0).
  { eapply EC'_determ in H12; eauto. } subst t0.
  inv H3; inv H12.
  eapply external_call_deterministic in H; eauto. destruct H; subst. auto. 
  rewrite H11 in H2; inversion H2. subst m2. inversion H2. rewrite H0 in H12.
  rewrite H12 in H3; inversion H3. subst m''. split; auto. 
  f_equal; auto.
  unfold rs0, rs1; rewrite H4; auto.
Qed.

End RELSEM.

Definition Asm_at_external (c: state):
          option (external_function * signature * list val) :=
  match c with
    Asm_CallstateOut ef args rs lf =>
      if observableEF_dec hf ef
      then Some(ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) args)
      else None
  | _ => None
  end.

Definition Asm_after_external (vret: option val)(c: state) : option state :=
  match c with 
    Asm_CallstateOut ef args rs lf => 
      match vret with
         None => Some (State ((set_regs (loc_external_result (ef_sig ef)) 
                               (encode_long (sig_res (ef_sig ef)) Vundef) rs) #PC <- (rs RA))
                      lf)
       | Some res => Some (State ((set_regs (loc_external_result (ef_sig ef)) 
                               (encode_long (sig_res (ef_sig ef)) res) rs) #PC <- (rs RA))
                          lf) 
      end
  | _ => None
  end.

Definition Asm_initial_core (ge:genv) (v: val) (args:list val): 
           option state :=
  match v with
     | Vptr b i => 
          if Int.eq_dec i Int.zero 
          then match Genv.find_funct_ptr ge b with
                 | None => None
                 | Some f => 
                    match f with Internal fi =>
                     let tyl := sig_args (funsig f) in
                     if val_has_type_list_func args (sig_args (funsig f))
                        && vals_defined args
                        && zlt (4*(2*(Zlength args))) Int.max_unsigned
                     then Some (Asm_CallstateIn b args tyl (sig_res (funsig f)))
                     else None
                   | External _ => None
                   end
               end
          else None
     | _ => None
    end.

Definition Asm_halted (q : state): option val :=
    match q with
      State rs (mk_load_frame b retty) => 
        if Val.cmp_bool Ceq (rs#PC) Vzero 
                  then match retty 
                       with Some Tlong =>
                          match decode_longs (Tlong::nil) ((rs#EDX)::(rs#EAX)::nil) with
                                | v :: nil => Some v
                                | _ => None
                          end
                       | Some Tfloat => Some(rs#ST0)
                       | Some Tsingle => Some(rs#ST0)
                       | Some _ => Some(rs#EAX)
                       | None => Some(rs#EAX)
                       end 
                  else None
    | _ => None
    end.

Section ASM_CORESEM.
Lemma Asm_at_external_halted_excl :
       forall q, Asm_at_external q = None \/ Asm_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma Asm_after_at_external_excl : forall retv q q',
      Asm_after_external retv q = Some q' -> Asm_at_external q' = None.
  Proof. intros.
    destruct q; simpl in *; try inv H.
    destruct retv; inv H1; simpl; trivial.
  Qed.

Lemma Asm_corestep_not_at_external:
       forall ge m q m' q', asm_step ge q m q' m' -> 
              Asm_at_external q = None.
  Proof. intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec hf callee); simpl; trivial. 
  exfalso. eapply EFhelpers; eassumption. 
Qed.

Lemma Asm_corestep_not_halted : forall ge m q m' q', 
       asm_step ge q m q' m' -> 
       Asm_halted q = None.
  Proof. intros. inv H; simpl in *.
    rewrite H0; simpl. trivial. destruct lf; auto.
    rewrite H0; simpl. trivial. destruct lf; auto.
    rewrite H0; simpl. trivial. destruct lf; auto.
    trivial.
    auto.
  Qed.
 
Definition Asm_core_sem : CoreSemantics genv state mem.
  eapply (@Build_CoreSemantics _ _ _ 
            Asm_initial_core
            Asm_at_external
            Asm_after_external
            Asm_halted
            asm_step).
    apply Asm_corestep_not_at_external.
    apply Asm_corestep_not_halted.
    apply Asm_at_external_halted_excl.
Defined.
End ASM_CORESEM.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Section ASM_COOPSEM.

Lemma exec_load_forward: forall g chunk m a rs rd rs' m',
   exec_load g chunk m a rs rd = Next rs' m' ->
   mem_forward m m'.
Proof. intros. unfold exec_load in H.
  remember (Mem.loadv chunk m (eval_addrmode g a rs)) as d.
  destruct d; inv H. apply  mem_forward_refl.
Qed.

Lemma exec_store_forward: forall g chunk m a rs rs1 pregs rs' m',
  exec_store g chunk m a rs rs1 pregs = Next rs' m' ->
  mem_forward m m'.
Proof. intros. unfold exec_store in H.
  remember (Mem.storev chunk m (eval_addrmode g a rs) (rs rs1)) as d.
  destruct d; inv H.
  remember (eval_addrmode g a rs) as addr.
  destruct addr; simpl in *; inv Heqd.
  apply eq_sym in H0. eapply store_forward; eassumption.
Qed.

Lemma goto_label_forward: forall c0 l rs m rs' m',
      goto_label c0 l rs m = Next rs' m' -> mem_forward m m'.
Proof. intros.
   unfold goto_label in H. 
   destruct (label_pos l 0 c0); inv H.
   destruct (rs PC); inv H1. 
   apply mem_forward_refl.
Qed.

Lemma exec_instr_forward g c i rs m rs' m': forall 
      (EI: exec_instr g c i rs m = Next rs' m'),
      mem_forward m m'.
Proof. intros.
   destruct i; simpl in *; inv EI; try apply mem_forward_refl;
   try (eapply exec_load_forward; eassumption);
   try (eapply exec_store_forward; eassumption).

   destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply mem_forward_refl.

   destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H0.
   destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H1.
   apply mem_forward_refl.

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1; apply mem_forward_refl.
   apply mem_forward_refl.

   eapply goto_label_forward; eassumption. 

   destruct (eval_testcond c0 rs); inv H0.
   destruct b; inv H1.
   eapply goto_label_forward; eassumption. 
   apply mem_forward_refl.

   destruct (eval_testcond c1 rs); inv H0.
   destruct b. 
     destruct (eval_testcond c2 rs); inv H1.
     destruct b; inv H0. 
     eapply goto_label_forward; eassumption.
     apply mem_forward_refl.

     destruct (eval_testcond c2 rs); inv H1.
     apply mem_forward_refl.
     destruct (rs r); inv H0.
     destruct (list_nth_z tbl (Int.unsigned i)); inv H1. 
     eapply goto_label_forward; eassumption.
  remember (Mem.alloc m 0 sz) as d; apply eq_sym in Heqd.
    destruct d; inv H0.
    remember (Mem.store Mint32 m0 b (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as q.
    apply eq_sym in Heqq; destruct q; inv H1.
    remember (Mem.store Mint32 m1 b (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as w.
    destruct w; apply eq_sym in Heqw; inv H0.
    eapply mem_forward_trans.
      eapply alloc_forward; eassumption. 
    eapply mem_forward_trans.
      eapply store_forward; eassumption. 
      eapply store_forward; eassumption.
  destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))); inv H0.  
    destruct (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))); inv H1.  
    destruct (rs ESP); inv H0.
    remember (Mem.free m b 0 sz) as t.
    destruct t; inv H1; apply eq_sym in Heqt. 
    eapply free_forward; eassumption. 
Qed.

Lemma Asm_forward : forall g c m c' m'
         (CS: asm_step g c m c' m'), 
         mem_forward m m'.
  Proof. intros.
   inv CS; try apply mem_forward_refl. clear - H2.
   eapply exec_instr_forward; eassumption.
   inv H2. eapply external_call_mem_forward; eassumption.
   inv H1. eapply external_call_mem_forward; eassumption.
   inv H1. unfold store_args in H3. 
     eapply mem_forward_trans.
     eapply alloc_forward; eauto.
     eapply store_args_fwd; eauto.
Qed.
   
Program Definition Asm_coop_sem : 
  CoopCoreSem genv state.
apply Build_CoopCoreSem with (coopsem := Asm_core_sem).
  apply Asm_forward.
Defined.

End ASM_COOPSEM.

End ASM_COOP.
