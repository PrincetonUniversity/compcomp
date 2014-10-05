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

(** Correctness proof for Asm generation: machine-independent framework *)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Locations.
Require Import Mach.
Require Import Mach_coop.
Require Import Asm_comp.
Require Import Asmgen_comp.
Require Import Conventions.
Require Import Axioms.

Require Import mem_lemmas. (*for valid_block_dec, mem_forward etc*)
Require Import semantics.
Require Import semantics_lemmas.
Require Import structured_injections.
Require Import effect_semantics.
Require Import reach.
Require Import Asm_coop.
Require Import Asm_eff.
Require Import load_frame.

(** * Processor registers and register states *)

Hint Extern 2 (_ <> _) => congruence: asmgen.

Lemma ireg_of_eq:
  forall r r', ireg_of r = OK r' -> preg_of r = IR r'.
Proof.
  unfold ireg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma freg_of_eq:
  forall r r', freg_of r = OK r' -> preg_of r = FR r'.
Proof.
  unfold freg_of; intros. destruct (preg_of r); inv H; auto.
Qed.

Lemma preg_of_injective:
  forall r1 r2, preg_of r1 = preg_of r2 -> r1 = r2.
Proof.
  destruct r1; destruct r2; simpl; intros; reflexivity || discriminate.
Qed.

Lemma preg_of_data:
  forall r, data_preg (preg_of r) = true.
Proof.
  intros. destruct r; reflexivity.
Qed.
Hint Resolve preg_of_data: asmgen.

Lemma data_diff:
  forall r r',
  data_preg r = true -> data_preg r' = false -> r <> r'.
Proof.
  congruence.
Qed.
Hint Resolve data_diff: asmgenEFF.

Lemma preg_of_not_SP:
  forall r, preg_of r <> SP.
Proof.
  intros. unfold preg_of; destruct r; simpl; congruence. 
Qed.

Lemma preg_of_not_PC:
  forall r, preg_of r <> PC.
Proof.
  intros. apply data_diff; auto with asmgen.
Qed.

Hint Resolve preg_of_not_SP preg_of_not_PC: asmgen.

Lemma nextinstr_pc:
  forall rs, (nextinstr rs)#PC = Val.add rs#PC Vone.
Proof.
  intros. apply Pregmap.gss. 
Qed.

Lemma nextinstr_inv:
  forall r rs, r <> PC -> (nextinstr rs)#r = rs#r.
Proof.
  intros. unfold nextinstr. apply Pregmap.gso. red; intro; subst. auto.
Qed.

Lemma nextinstr_inv1:
  forall r rs, data_preg r = true -> (nextinstr rs)#r = rs#r.
Proof.
  intros. apply nextinstr_inv. red; intro; subst; discriminate.
Qed.

Lemma nextinstr_set_preg:
  forall rs m v,
  (nextinstr (rs#(preg_of m) <- v))#PC = Val.add rs#PC Vone.
Proof.
  intros. unfold nextinstr. rewrite Pregmap.gss. 
  rewrite Pregmap.gso. auto. apply sym_not_eq. apply preg_of_not_PC. 
Qed.

Lemma undef_regs_other:
  forall r rl rs, 
  (forall r', In r' rl -> r <> r') ->
  undef_regs rl rs r = rs r.
Proof.
  induction rl; simpl; intros. auto. 
  rewrite IHrl by auto. rewrite Pregmap.gso; auto.
Qed.

Fixpoint preg_notin (r: preg) (rl: list mreg) : Prop :=
  match rl with
  | nil => True
  | r1 :: nil => r <> preg_of r1
  | r1 :: rl => r <> preg_of r1 /\ preg_notin r rl
  end.

Remark preg_notin_charact:
  forall r rl,
  preg_notin r rl <-> (forall mr, In mr rl -> r <> preg_of mr).
Proof.
  induction rl; simpl; intros.
  tauto.
  destruct rl.
  simpl. split. intros. intuition congruence. auto. 
  rewrite IHrl. split. 
  intros [A B]. intros. destruct H. congruence. auto. 
  auto.
Qed.

Lemma undef_regs_other_2:
  forall r rl rs,
  preg_notin r rl ->
  undef_regs (map preg_of rl) rs r = rs r.
Proof.
  intros. apply undef_regs_other. intros. 
  exploit list_in_map_inv; eauto. intros [mr [A B]]. subst.
  rewrite preg_notin_charact in H. auto.
Qed.

Lemma set_pregs_other_2:
  forall r rl vl rs,
  preg_notin r rl ->
  set_regs (map preg_of rl) vl rs r = rs r.
Proof.
  induction rl; simpl; intros. 
  auto.
  destruct vl; auto.
  assert (r <> preg_of a) by (destruct rl; tauto).
  assert (preg_notin r rl) by (destruct rl; simpl; tauto).
  rewrite IHrl by auto. apply Pregmap.gso; auto. 
Qed.

(** * Agreement between Mach registers and processor registers *)

Definition sp_spec (mu: SM_Injection) (v:val) :=
  exists b ofs tb, v = Vptr b ofs /\ local_of mu b = Some(tb,0).

Lemma sp_spec_ptr: forall mu b ofs (SP: sp_spec mu (Vptr b ofs)), 
      exists tb, local_of mu b = Some(tb,0).
Proof. intros.
  destruct SP. inv H.
  destruct H0 as [tb [TB LOC]]. inv TB.
  exists tb; trivial.
Qed.

Lemma sp_spec_intern_incr mu mu': forall 
   (INC: intern_incr mu mu') v
   (ZLOC: sp_spec mu v), sp_spec mu' v.
Proof. intros.
destruct ZLOC as [b [ofs [tb [SP LOC]]]]; subst.
  apply INC in LOC. 
    exists b, ofs, tb; split; trivial.
Qed.

(*NEW: added parameter j:meminj and changed lessdef into val_inject*)
Record agree mu (ms: Mach.regset) (sp: val) (rs: Asm_comp.regset) : Prop := mkagree {
  (*Modified*) agree_sp_local: val_inject (local_of mu) sp (rs#SP);
  agree_mregs: forall r: mreg, val_inject (as_inj mu) (ms r) (rs#(preg_of r))
}.

(*NEW*)
Lemma agree_intern_incr ms sp rs: forall mu mu' (WD': SM_wd mu')
         (A:agree mu ms sp rs) (INC: intern_incr mu mu'),
      agree mu' ms sp rs.
Proof. intros. inv A.
  split; auto.
    eapply val_inject_incr; try eassumption. eapply INC.
  intros. apply intern_incr_as_inj in INC; trivial. 
          eapply (val_inject_incr _ _ _ _ INC). auto.
Qed.

Lemma preg_val:
  forall mu ms sp rs r, agree mu ms sp rs -> 
         val_inject (as_inj mu) (ms r) rs#(preg_of r).
Proof.
  intros. destruct H. auto.
Qed.

Lemma preg_vals:
  forall mu ms sp rs, agree mu ms sp rs ->
  forall l, val_list_inject (as_inj mu) (map ms l) (map rs (map preg_of l)).
Proof.
  induction l; simpl. constructor. constructor. eapply preg_val; eauto. auto.
Qed.

Lemma sp_as_inj:
  forall mu ms sp rs, agree mu ms sp rs -> SM_wd mu ->
         val_inject (as_inj mu) sp rs#SP.
Proof. intros. apply agree_sp_local in H.
       eapply val_inject_incr; try eassumption.
       eapply local_in_all; trivial.
Qed.

Lemma ireg_val:
  forall mu ms sp rs r r',
  agree mu ms sp rs ->
  ireg_of r = OK r' ->
  val_inject (as_inj mu) (ms r) rs#r'.
Proof.
  intros. rewrite <- (ireg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma freg_val:
  forall mu ms sp rs r r',
  agree mu ms sp rs ->
  freg_of r = OK r' ->
  val_inject (as_inj mu) (ms r) (rs#r').
Proof.
  intros. rewrite <- (freg_of_eq _ _ H0). eapply preg_val; eauto.
Qed.

Lemma agree_exten:
  forall mu ms sp rs rs',
  agree mu ms sp rs ->
  (forall r, data_preg r = true -> rs'#r = rs#r) ->
  agree mu ms sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H0; auto.
  intros. rewrite H0; auto. apply preg_of_data.
Qed.

(** Preservation of register agreement under various assignments. *)

Lemma agree_set_mreg:
  forall mu ms sp rs r v rs',
  agree mu ms sp rs ->
  val_inject (as_inj mu) v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> rs'#r' = rs#r') ->
  agree mu (Regmap.set r v ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  rewrite H1; auto. apply sym_not_equal. apply preg_of_not_SP.
  intros. unfold Regmap.set. destruct (RegEq.eq r0 r). congruence. 
  rewrite H1. auto. apply preg_of_data.
  red; intros; elim n. eapply preg_of_injective; eauto.
Qed.

Lemma agree_set_other:
  forall mu ms sp rs r v,
  agree mu ms sp rs ->
  data_preg r = false ->
  agree mu ms sp (rs#r <- v).
Proof.
  intros. apply agree_exten with rs. auto.
  intros. apply Pregmap.gso. congruence.
Qed.

Lemma agree_nextinstr:
  forall mu ms sp rs,
  agree mu ms sp rs -> agree mu ms sp (nextinstr rs).
Proof.
  intros. unfold nextinstr. apply agree_set_other. auto. auto.
Qed.

Lemma agree_set_mregs:
  forall mu sp rl vl vl' ms rs,
  agree mu ms sp rs ->
  val_list_inject (as_inj mu) vl vl' ->
  agree mu (Mach.set_regs rl vl ms) sp (set_regs (map preg_of rl) vl' rs).
Proof.
  induction rl; simpl; intros. 
  auto.
  inv H0. auto. apply IHrl; auto. 
  eapply agree_set_mreg. eexact H. 
  rewrite Pregmap.gss. auto.
  intros. apply Pregmap.gso; auto. 
Qed.

Lemma agree_undef_nondata_regs:
  forall mu ms sp rl rs,
  agree mu ms sp rs ->
  (forall r, In r rl -> data_preg r = false) ->
  agree mu ms sp (undef_regs rl rs).
Proof.
  induction rl; simpl; intros. auto.
  apply IHrl. apply agree_exten with rs; auto.
  intros. apply Pregmap.gso. red; intros; subst.
  assert (data_preg a = false) by auto. congruence.
  intros. apply H0; auto.
Qed.

Lemma agree_undef_regs:
  forall mu ms sp rl rs rs',
  agree mu ms sp rs ->
  (forall r', data_preg r' = true -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree mu (Mach.undef_regs rl ms) sp rs'.
Proof.
  intros. destruct H. split; auto.
  (*NEW:*) rewrite H0; try assumption. auto. 
           (*WAS:rewrite <- agree_sp0. apply H0; auto. *)
    rewrite preg_notin_charact. intros. apply not_eq_sym. apply preg_of_not_SP.
   
  intros. destruct (In_dec mreg_eq r rl).
  rewrite Mach.undef_regs_same; auto.
  rewrite Mach.undef_regs_other; auto. rewrite H0; auto. 
  apply preg_of_data.
  rewrite preg_notin_charact. intros; red; intros. elim n. 
  exploit preg_of_injective; eauto. congruence.
Qed.

Lemma agree_set_undef_mreg:
  forall mu ms sp rs r v rl rs',
  agree mu ms sp rs ->
  val_inject (as_inj mu) v (rs'#(preg_of r)) ->
  (forall r', data_preg r' = true -> r' <> preg_of r -> preg_notin r' rl -> rs'#r' = rs#r') ->
  agree mu (Regmap.set r v (Mach.undef_regs rl ms)) sp rs'.
Proof.
  intros. apply agree_set_mreg with (rs'#(preg_of r) <- (rs#(preg_of r))); auto.
  apply agree_undef_regs with rs; auto. 
  intros. unfold Pregmap.set. destruct (PregEq.eq r' (preg_of r)). 
  congruence. auto. 
  intros. rewrite Pregmap.gso; auto. 
Qed.

Lemma agree_change_sp:
  forall mu ms sp rs sp' tsp',
  agree mu ms sp rs -> 
  (*NEW:*) sp_spec mu sp' ->
  val_inject (as_inj mu) sp' tsp' -> SM_wd mu ->
  agree mu ms sp' (rs#SP <- tsp').
Proof.
  intros. inv H. split; auto.
  rewrite Pregmap.gss.
    destruct H0 as [spb' [z [tspb' [SPB' LOC]]]]; subst; inv H1.
     rewrite (local_in_all _ H2 _ _ _ LOC) in H3. inv H3.
       econstructor; try eassumption. trivial.
  intros. rewrite Pregmap.gso; auto with asmgen.
Qed.

(** Connection between Mach and Asm calling conventions for external
    functions. *)

Lemma extcall_arg_match:
  forall mu ms sp rs m m' l v (WD: SM_wd mu),
  agree mu ms sp rs ->
  Mem.inject (as_inj mu) m m' -> (*WAS: Mem.extends m m'*)
  Mach.extcall_arg ms m sp l v ->
  exists v', Asm_comp.extcall_arg rs m' l v' /\ 
             val_inject (as_inj mu) v v' (*WAS: lessdef*).
Proof.
  intros. inv H1.
  exists (rs#(preg_of r)); split. constructor. eapply preg_val; eauto.
  unfold load_stack in H2.
  apply agree_sp_local in H. (* destruct H as [b [z [SP [J RSESP]]]]. subst.*)
  exploit Mem.loadv_inject; eauto. 
     eapply val_add_inject. 
       eapply val_inject_incr; try eassumption. eapply local_in_all; try eassumption.
       constructor. 
  intros [v' [A B]]. 
  exists v'; split; auto.
  econstructor. eauto. assumption. 
Qed.

Lemma extcall_args_match: forall mu ms sp rs m m' (WD: SM_wd mu), 
     agree mu ms sp rs -> Mem.inject (as_inj mu) m m' ->
  forall ll vl,
  list_forall2 (Mach.extcall_arg ms m sp) ll vl ->
  exists vl', list_forall2 (Asm_comp.extcall_arg rs m') ll vl' /\ 
              val_list_inject (as_inj mu) vl vl'.
Proof.
  induction 4; intros. 
  exists (@nil val); split. constructor. constructor.
  exploit extcall_arg_match; eauto. intros [v1' [A B]].
  destruct IHlist_forall2 as [vl' [C D]].
  exists (v1' :: vl'); split; constructor; auto.
Qed.

Lemma extcall_arguments_match:
  forall mu ms m m' sp rs sg args (WD: SM_wd mu),
  agree mu ms sp rs -> Mem.inject (as_inj mu) m m' ->
  Mach.extcall_arguments ms m sp sg args ->
  exists args', Asm_comp.extcall_arguments rs m' sg args' /\ 
                val_list_inject (as_inj mu) args args'.
Proof.
  unfold Mach.extcall_arguments, Asm_comp.extcall_arguments; intros.
  eapply extcall_args_match; eauto.
Qed.

(** * Correspondence between Mach code and Asm code *)

Lemma find_instr_in:
  forall c pos i,
  find_instr pos c = Some i -> In i c.
Proof.
  induction c; simpl. intros; discriminate.
  intros until i. case (zeq pos 0); intros.
  left; congruence. right; eauto.
Qed.

(** The ``code tail'' of an instruction list [c] is the list of instructions
  starting at PC [pos]. *)

Inductive code_tail: Z -> code -> code -> Prop :=
  | code_tail_0: forall c,
      code_tail 0 c c
  | code_tail_S: forall pos i c1 c2,
      code_tail pos c1 c2 ->
      code_tail (pos + 1) (i :: c1) c2.

Lemma code_tail_pos:
  forall pos c1 c2, code_tail pos c1 c2 -> pos >= 0.
Proof.
  induction 1. omega. omega.
Qed.

Lemma find_instr_tail:
  forall c1 i c2 pos,
  code_tail pos c1 (i :: c2) ->
  find_instr pos c1 = Some i.
Proof.
  induction c1; simpl; intros.
  inv H.
  destruct (zeq pos 0). subst pos.
  inv H. auto. generalize (code_tail_pos _ _ _ H4). intro. omegaContradiction.
  inv H. congruence. replace (pos0 + 1 - 1) with pos0 by omega.
  eauto.
Qed.

Remark code_tail_bounds_1:
  forall fn ofs c,
  code_tail ofs fn c -> 0 <= ofs <= list_length_z fn.
Proof.
  induction 1; intros; simpl.
  generalize (list_length_z_pos c). omega. 
  rewrite list_length_z_cons. omega.
Qed.

Remark code_tail_bounds_2:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) -> 0 <= ofs < list_length_z fn.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> 0 <= ofs < list_length_z fn).
  induction 1; intros; simpl. 
  rewrite H. rewrite list_length_z_cons. generalize (list_length_z_pos c'). omega.
  rewrite list_length_z_cons. generalize (IHcode_tail _ _ H0). omega.
  eauto.
Qed.

Lemma code_tail_next:
  forall fn ofs i c,
  code_tail ofs fn (i :: c) ->
  code_tail (ofs + 1) fn c.
Proof.
  assert (forall ofs fn c, code_tail ofs fn c ->
          forall i c', c = i :: c' -> code_tail (ofs + 1) fn c').
  induction 1; intros.
  subst c. constructor. constructor.
  constructor. eauto.
  eauto.
Qed.

Lemma code_tail_next_int:
  forall fn ofs i c,
  list_length_z fn <= Int.max_unsigned ->
  code_tail (Int.unsigned ofs) fn (i :: c) ->
  code_tail (Int.unsigned (Int.add ofs Int.one)) fn c.
Proof.
  intros. rewrite Int.add_unsigned.
  change (Int.unsigned Int.one) with 1.
  rewrite Int.unsigned_repr. apply code_tail_next with i; auto.
  generalize (code_tail_bounds_2 _ _ _ _ H0). omega. 
Qed.

(** [transl_code_at_pc pc fb f c ep tf tc] holds if the code pointer [pc] points
  within the Asm code generated by translating Mach function [f],
  and [tc] is the tail of the generated code at the position corresponding
  to the code pointer [pc]. *)

Inductive transl_code_at_pc (ge: Mach.genv):
    val -> block -> Mach.function -> Mach.code -> bool -> Asm_comp.function -> Asm_comp.code -> Prop :=
  transl_code_at_pc_intro:
    forall b ofs f c ep tf tc,
    Genv.find_funct_ptr ge b = Some(Internal f) ->
    transf_function f = Errors.OK tf ->
    transl_code f c ep = OK tc ->
    code_tail (Int.unsigned ofs) (fn_code tf) tc ->
    transl_code_at_pc ge (Vptr b ofs) b f c ep tf tc.

(** Equivalence between [transl_code] and [transl_code']. *)

Local Open Scope error_monad_scope.

Lemma transl_code_rec_transl_code:
  forall f il ep k,
  transl_code_rec f il ep k = (do c <- transl_code f il ep; k c).
Proof.
  induction il; simpl; intros.
  auto.
  rewrite IHil.
  destruct (transl_code f il (it1_is_parent ep a)); simpl; auto.
Qed.

Lemma transl_code'_transl_code:
  forall f il ep,
  transl_code' f il ep = transl_code f il ep.
Proof.
  intros. unfold transl_code'. rewrite transl_code_rec_transl_code. 
  destruct (transl_code f il ep); auto. 
Qed.

(** Predictor for return addresses in generated Asm code.

  The [return_address_offset] predicate defined here is used in the
  semantics for Mach to determine the return addresses that are
  stored in activation records. *)

(** Consider a Mach function [f] and a sequence [c] of Mach instructions
  representing the Mach code that remains to be executed after a
  function call returns.  The predicate [return_address_offset f c ofs]
  holds if [ofs] is the integer offset of the PPC instruction
  following the call in the Asm code obtained by translating the
  code of [f]. Graphically:
<<
     Mach function f    |--------- Mcall ---------|
         Mach code c    |                |--------|
                        |                 \        \
                        |                  \        \
                        |                   \        \
     Asm code           |                    |--------|
     Asm function       |------------- Pcall ---------|

                        <-------- ofs ------->
>>
*)

Definition return_address_offset (f: Mach.function) (c: Mach.code) (ofs: int) : Prop :=
  forall tf tc,
  transf_function f = OK tf ->
  transl_code f c false = OK tc ->
  code_tail (Int.unsigned ofs) (fn_code tf) tc.

(** We now show that such an offset always exists if the Mach code [c]
  is a suffix of [f.(fn_code)].  This holds because the translation
  from Mach to PPC is compositional: each Mach instruction becomes
  zero, one or several PPC instructions, but the order of instructions
  is preserved. *)

Lemma is_tail_code_tail:
  forall c1 c2, is_tail c1 c2 -> exists ofs, code_tail ofs c2 c1.
Proof.
  induction 1. exists 0; constructor.
  destruct IHis_tail as [ofs CT]. exists (ofs + 1); constructor; auto.
Qed.

Section RETADDR_EXISTS.

Hypothesis transl_instr_tail:
  forall f i ep k c, transl_instr f i ep k = OK c -> is_tail k c.
Hypothesis transf_function_inv:
  forall f tf, transf_function f = OK tf ->
  exists tc, exists ep, transl_code f (Mach.fn_code f) ep = OK tc /\ is_tail tc (fn_code tf).
Hypothesis transf_function_len:
  forall f tf, transf_function f = OK tf -> list_length_z (fn_code tf) <= Int.max_unsigned.

Lemma transl_code_tail: 
  forall f c1 c2, is_tail c1 c2 ->
  forall tc2 ep2, transl_code f c2 ep2 = OK tc2 ->
  exists tc1, exists ep1, transl_code f c1 ep1 = OK tc1 /\ is_tail tc1 tc2.
Proof.
  induction 1; simpl; intros.
  exists tc2; exists ep2; split; auto with coqlib.
  monadInv H0. exploit IHis_tail; eauto. intros [tc1 [ep1 [A B]]].
  exists tc1; exists ep1; split. auto. 
  apply is_tail_trans with x. auto. eapply transl_instr_tail; eauto.
Qed.

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. destruct (transf_function f) as [tf|] eqn:TF.
+ exploit transf_function_inv; eauto. intros (tc1 & ep1 & TR1 & TL1).
  exploit transl_code_tail; eauto. intros (tc2 & ep2 & TR2 & TL2).
Opaque transl_instr.
  monadInv TR2. 
  assert (TL3: is_tail x (fn_code tf)).
  { apply is_tail_trans with tc1; auto. 
    apply is_tail_trans with tc2; auto.
    eapply transl_instr_tail; eauto. }
  exploit is_tail_code_tail. eexact TL3. intros [ofs CT].
  exists (Int.repr ofs). red; intros. 
  rewrite Int.unsigned_repr. congruence. 
  exploit code_tail_bounds_1; eauto.
  apply transf_function_len in TF. omega. 
+ exists Int.zero; red; intros. congruence. 
Qed.

End RETADDR_EXISTS.

Remark code_tail_no_bigger:
  forall pos c1 c2, code_tail pos c1 c2 -> (length c2 <= length c1)%nat.
Proof.
  induction 1; simpl; omega.
Qed.

Remark code_tail_unique:
  forall fn c pos pos',
  code_tail pos fn c -> code_tail pos' fn c -> pos = pos'.
Proof.
  induction fn; intros until pos'; intros ITA CT; inv ITA; inv CT; auto.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  generalize (code_tail_no_bigger _ _ _ H3); simpl; intro; omega.
  f_equal. eauto.
Qed.

Lemma return_address_offset_correct:
  forall ge b ofs fb f c tf tc ofs',
  transl_code_at_pc ge (Vptr b ofs) fb f c false tf tc ->
  return_address_offset f c ofs' ->
  ofs' = ofs.
Proof.
  intros. inv H. red in H0.  
  exploit code_tail_unique. eexact H12. eapply H0; eauto. intro.
  rewrite <- (Int.repr_unsigned ofs). 
  rewrite <- (Int.repr_unsigned ofs').
  congruence.
Qed.

(** The [find_label] function returns the code tail starting at the
  given label.  A connection with [code_tail] is then established. *)

Fixpoint find_label (lbl: label) (c: code) {struct c} : option code :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some c' else find_label lbl c'
  end.

Lemma label_pos_code_tail:
  forall lbl c pos c',
  find_label lbl c = Some c' ->
  exists pos',
  label_pos lbl pos c = Some pos' 
  /\ code_tail (pos' - pos) c c'
  /\ pos < pos' <= pos + list_length_z c.
Proof.
  induction c. 
  simpl; intros. discriminate.
  simpl; intros until c'.
  case (is_label lbl a).
  intro EQ; injection EQ; intro; subst c'.
  exists (pos + 1). split. auto. split.
  replace (pos + 1 - pos) with (0 + 1) by omega. constructor. constructor. 
  rewrite list_length_z_cons. generalize (list_length_z_pos c). omega. 
  intros. generalize (IHc (pos + 1) c' H). intros [pos' [A [B C]]].
  exists pos'. split. auto. split.
  replace (pos' - pos) with ((pos' - (pos + 1)) + 1) by omega.
  constructor. auto. 
  rewrite list_length_z_cons. omega.
Qed.

(** Helper lemmas to reason about 
- the "code is tail of" property
- correct translation of labels. *)

Definition tail_nolabel (k c: code) : Prop :=
  is_tail k c /\ forall lbl, find_label lbl c = find_label lbl k.

Lemma tail_nolabel_refl:
  forall c, tail_nolabel c c.
Proof.
  intros; split. apply is_tail_refl. auto.
Qed.

Lemma tail_nolabel_trans:
  forall c1 c2 c3, tail_nolabel c2 c3 -> tail_nolabel c1 c2 -> tail_nolabel c1 c3.
Proof.
  intros. destruct H; destruct H0; split. 
  eapply is_tail_trans; eauto.
  intros. rewrite H1; auto.
Qed.

Definition nolabel (i: instruction) :=
  match i with Plabel _ => False | _ => True end.

Hint Extern 1 (nolabel _) => exact I : labels.

Lemma tail_nolabel_cons:
  forall i c k,
  nolabel i -> tail_nolabel k c -> tail_nolabel k (i :: c).
Proof.
  intros. destruct H0. split. 
  constructor; auto.
  intros. simpl. rewrite <- H1. destruct i; reflexivity || contradiction.
Qed.

Hint Resolve tail_nolabel_refl: labels.

Ltac TailNoLabel :=
  eauto with labels;
  match goal with
  | [ |- tail_nolabel _ (_ :: _) ] => apply tail_nolabel_cons; [auto; exact I | TailNoLabel]
  | [ H: Error _ = OK _ |- _ ] => discriminate
  | [ H: assertion_failed = OK _ |- _ ] => discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H; TailNoLabel
  | [ H: bind _ _ = OK _ |- _ ] => monadInv H;  TailNoLabel
  | [ H: (if ?x then _ else _) = OK _ |- _ ] => destruct x; TailNoLabel
  | [ H: match ?x with nil => _ | _ :: _ => _ end = OK _ |- _ ] => destruct x; TailNoLabel
  | _ => idtac
  end.

(** * Execution of straight-line code *)

Section STRAIGHTLINE.
Variable hf: I64Helpers.helper_functions.

Variable ge: genv.
Variable fn: function.

(** Straight-line code is composed of processor instructions that execute
  in sequence (no branches, no function calls and returns).
  The following inductive predicate relates the machine states
  before and after executing a straight-line sequence of instructions.
  Instructions are taken from the first list instead of being fetched
  from memory. *)

(*NEW: added effects*)
Inductive eff_exec_straight: (block -> Z -> bool) ->
                         code -> regset -> mem -> 
                         code -> regset -> mem -> Prop :=
  | eff_exec_straight_one:
      forall i1 c rs1 m1 rs2 m2 U,
      exec_instr ge (fn_code fn) i1 rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      U = effect_instr ge (fn_code fn) i1 rs1 m1 ->
      eff_exec_straight U (i1 :: c) rs1 m1 c rs2 m2
  | eff_exec_straight_step:
      forall i c rs1 m1 rs2 m2 c' rs3 m3 U U2 ,
      exec_instr ge (fn_code fn) i rs1 m1 = Next rs2 m2 ->
      rs2#PC = Val.add rs1#PC Vone ->
      eff_exec_straight U2 c rs2 m2 c' rs3 m3 ->
      U = (fun b z => effect_instr ge (fn_code fn) i rs1 m1 b z || 
                       (U2 b z && valid_block_dec m1 b)) ->
      eff_exec_straight U (i :: c) rs1 m1 c' rs3 m3.

(*NEW*)
Lemma eff_exec_straight_forward:  forall c1 rs1 m1 c2 rs2 m2 U ,
  eff_exec_straight U c1 rs1 m1 c2 rs2 m2 -> mem_forward m1 m2.
Proof. intros.
  induction H.
   eapply exec_instr_forward; eassumption.
   apply exec_instr_forward in H.
     eapply mem_forward_trans; eassumption.
Qed.

Lemma eff_exec_straight_valid: forall M c1 rs1 m1 c2 rs2 m2,
       eff_exec_straight M c1 rs1 m1 c2 rs2 m2 ->
       forall b z, M b z = true -> Mem.valid_block m1 b.
Proof. intros.
  inv H. clear -H0 H1.
  eapply exec_instr_valid_block; eassumption.

  apply orb_true_iff in H0.
  destruct H0. 
    eapply exec_instr_valid_block; eassumption.
  apply andb_true_iff in H; destruct H as [_ ?].
    destruct (valid_block_dec m1 b); trivial. inv H.
Qed.

Lemma eff_exec_straight_trans:
  forall U1 c1 rs1 m1 c2 rs2 m2 
  (EX1:  eff_exec_straight U1 c1 rs1 m1 c2 rs2 m2)
  U2 c3 rs3 m3 
  (EX2: eff_exec_straight U2 c2 rs2 m2 c3 rs3 m3) U
  (HU: U = (fun b z => U1 b z || (U2 b z && valid_block_dec m1 b))),
  eff_exec_straight U c1 rs1 m1 c3 rs3 m3.
Proof. intros U1 c1 rs1 m1 c2 rs2 m2 EX1.
  induction EX1; intros.
  subst. apply eff_exec_straight_step with rs2 m2 U2; auto.
  eapply eff_exec_straight_step.
    eassumption. eassumption.
    eapply IHEX1. eassumption. reflexivity.
    subst. extensionality b; extensionality z. clear IHEX1.
    apply exec_instr_forward in H. 
    remember (effect_instr ge (fn_code fn) i rs1 m1 b z) as d.
    destruct d; simpl; trivial.
    remember (U2 b z && valid_block_dec m1 b) as q; apply eq_sym in Heqq.
    destruct q; simpl. rewrite andb_true_iff in Heqq. destruct Heqq.
    rewrite H1, H2. simpl. trivial.
    remember (U0 b z && valid_block_dec m1 b) as w; apply eq_sym in Heqw.
    destruct w; simpl. rewrite andb_true_iff in Heqw. destruct Heqw.
    rewrite H1, H2. simpl.
      destruct (valid_block_dec m2 b); simpl. rewrite orb_true_r. trivial.
      elim n. apply H. destruct (valid_block_dec m1 b); trivial. inv H2.
    apply eq_sym.
      destruct (valid_block_dec m1 b); simpl in *.
        rewrite andb_false_iff in *.
        destruct Heqq; try congruence. 
        destruct Heqw; try congruence.
        rewrite H1, H2; simpl. left; trivial.
      rewrite andb_false_r. trivial.
Qed.

Lemma eff_exec_straight_two:
  forall i1 i2 c rs1 m1 rs2 m2 rs3 m3 U,
  exec_instr ge (fn_code fn) i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge (fn_code fn) i2 rs2 m2 = Next rs3 m3 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  U = (fun b z => effect_instr ge (fn_code fn) i1 rs1 m1 b z || 
        (effect_instr ge (fn_code fn) i2 rs2 m2 b z && valid_block_dec m1 b)) ->  
  eff_exec_straight U (i1 :: i2 :: c) rs1 m1 c rs3 m3.
Proof.
  intros. 
  eapply eff_exec_straight_step; try eassumption.
  apply eff_exec_straight_one; auto.
Qed.

Lemma eff_exec_straight_three:
  forall i1 i2 i3 c rs1 m1 rs2 m2 rs3 m3 rs4 m4 U,
  exec_instr ge (fn_code fn) i1 rs1 m1 = Next rs2 m2 ->
  exec_instr ge (fn_code fn) i2 rs2 m2 = Next rs3 m3 ->
  exec_instr ge (fn_code fn) i3 rs3 m3 = Next rs4 m4 ->
  rs2#PC = Val.add rs1#PC Vone ->
  rs3#PC = Val.add rs2#PC Vone ->
  rs4#PC = Val.add rs3#PC Vone ->
  U = (fun b z => effect_instr ge (fn_code fn) i1 rs1 m1 b z || 
        ((effect_instr ge (fn_code fn) i2 rs2 m2 b z ||
          effect_instr ge (fn_code fn) i3 rs3 m3 b z) 
         && valid_block_dec m1 b)) -> 
  eff_exec_straight U (i1 :: i2 :: i3 :: c) rs1 m1 c rs4 m4.
Proof.
  intros. eapply eff_exec_straight_step; try eassumption.
    eapply eff_exec_straight_two; eauto. reflexivity.
  subst. extensionality b; extensionality z.
  destruct (effect_instr ge (fn_code fn) i1 rs1 m1 b z); simpl; trivial.
  destruct (valid_block_dec m1 b); simpl.
  Focus 2. repeat rewrite andb_false_r. trivial.
  repeat rewrite andb_true_r.
  destruct (effect_instr ge (fn_code fn) i2 rs2 m2 b z); simpl; trivial.
  destruct (valid_block_dec m2 b). rewrite andb_true_r. trivial.
  elim n. eapply exec_instr_forward; eassumption.
Qed.

(** The following lemmas show that straight-line executions
  (predicate [exec_straight]) correspond to correct Asm executions. *)

Lemma eff_exec_straight_steps_1:
  forall U c rs m c' rs' m' lf,
  eff_exec_straight U c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) (fn_code fn) c ->
  effstep_plus (Asm_eff_sem hf) ge U (State rs lf) m (State rs' lf) m'.
Proof.
  induction 1; intros.
  apply effstep_plus_one.
  subst. econstructor; eauto. 
  eapply find_instr_tail. eauto.
  eapply effstep_star_plus_trans'.
    eapply effstep_star_one.
      econstructor; eauto. 
        eapply find_instr_tail. eauto.
    apply IHeff_exec_straight with b (Int.add ofs Int.one). 
      auto.
      rewrite H0. rewrite H4. reflexivity.
      auto. 
      apply code_tail_next_int with i; auto.
      apply H2.
Qed.
    
Lemma eff_exec_straight_steps_2:
  forall U c rs m c' rs' m',
  eff_exec_straight U c rs m c' rs' m' ->
  list_length_z (fn_code fn) <= Int.max_unsigned ->
  forall b ofs,
  rs#PC = Vptr b ofs ->
  Genv.find_funct_ptr ge b = Some (Internal fn) ->
  code_tail (Int.unsigned ofs) (fn_code fn) c ->
  exists ofs',
     rs'#PC = Vptr b ofs'
  /\ code_tail (Int.unsigned ofs') (fn_code fn) c'.
Proof.
  induction 1; intros.
  subst. exists (Int.add ofs Int.one). split.
  rewrite H0. rewrite H3. auto.
  apply code_tail_next_int with i1; auto.
  apply IHeff_exec_straight with (Int.add ofs Int.one).
  auto. rewrite H0. rewrite H4. reflexivity. auto. 
  apply code_tail_next_int with i; auto.
Qed.

End STRAIGHTLINE.

(** * Properties of the Mach call stack *)

Section MATCH_STACK.

Variable ge: Mach.genv.

(*NEW: ra is zero, or a gloabl block, or a local block that's mapped
  with offset 0*)
Definition ra_spec (mu: SM_Injection) (v:val) :=
  v = Vzero \/ exists b ofs, v = Vptr b ofs /\ 
               ((exists tb, local_of mu b = Some(tb,0)) \/ isGlobalBlock ge b = true).

Lemma ra_spec_intern_incr mu mu': forall 
   (INC: intern_incr mu mu') v
   (ZLOV: ra_spec mu v), ra_spec mu' v.
Proof. intros.
destruct ZLOV as [Zero | [b [ofs [SP [[tb LOC] | GL]]]]]; subst.
left; trivial.
right. exists b, ofs; split; trivial. left. exists tb. apply INC; trivial.
right. exists b, ofs; split; trivial. right; trivial.
Qed.

(*NEW: added parameter mu*)
Inductive match_stack mu : list Mach.stackframe -> Prop :=
  | match_stack_nil:
      match_stack mu nil
  | match_stack_cons: forall fb sp ra c s f tf tc,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      transl_code_at_pc ge ra fb f c false tf tc ->
      (*WAS: sp <> Vundef ->*)
      (*NEW:*) (sp_spec mu sp) ->
      (*NEW:*) (ra_spec mu ra) ->
      match_stack mu s ->
      match_stack mu (Stackframe fb sp ra c :: s).

Lemma parent_sp_def: forall mu s, match_stack mu s -> parent_sp s <> Vundef.
Proof. induction 1; simpl. unfold Vzero; congruence.
  destruct H1 as [b [ofs X]].
  destruct X as [tb [SP LOC]]. subst; congruence.
Qed.

Lemma parent_sp0_def: forall mu sp0 s, match_stack mu s -> parent_sp0 sp0 s<>Vundef.
Proof. induction 1; simpl. unfold Vzero; congruence.
  destruct H1 as [b [ofs X]].
  destruct X as [tb [SP LOC]]. subst; congruence.
Qed.

Lemma parent_sp0_spec: 
  forall mu sp0 tsp0 s, 
  match_stack mu s -> 
  local_of mu sp0 = Some (tsp0, 0) -> 
  sp_spec mu (parent_sp0 sp0 s).
Proof. 
induction 1; trivial. simpl. 
exists sp0, Int.zero, tsp0.
split; auto.
Qed.

Lemma parent_ra_spec: forall mu s, match_stack mu s -> ra_spec mu (parent_ra s).
Proof. induction 1; trivial. left; trivial. Qed.

End MATCH_STACK.

