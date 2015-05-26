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

(** Correctness proof for RTL generation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Switch.
Require Import Registers.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import RTL.
Require Import RTLgen.
Require Import RTLgenspec.

Require Import mem_lemmas.
Require Import semantics.
Require Import semantics_lemmas.
Require Import effect_semantics.
Require Import structured_injections.
Require Import reach.
Require Import simulations.
Require Import effect_properties.
Require Import simulations_lemmas.

Require Export Axioms.
Require Import CminorSel_coop.
Require Import CminorSel_eff.
Require Import RTL_coop.
Require Import BuiltinEffects.
Require Import RTL_eff.

Lemma FreeEffect_PropagateLeft':
  forall (m : mem) (sp : block) (lo hi : Z) (m' : mem),
  Mem.free m sp lo hi = Some m' ->
  forall (mu : SM_Injection) (m2 : mem),
  sm_valid mu m m2 ->
  SM_wd mu ->
  forall spb' : block,
  local_of mu sp = Some (spb', 0%Z) ->
  forall (b2 : block) (ofs : Z),
  FreeEffect m2 lo hi spb' b2 ofs = true ->
  locBlocksTgt mu b2 = false ->
  exists (b1 : block) (delta : Z),
    foreign_of mu b1 = Some (b2, delta) /\
    FreeEffect m lo hi sp b1 (ofs - delta) = true /\
    Mem.perm m b1 (ofs - delta) Max Nonempty.
Proof. intros.
  eapply FreeEffect_PropagateLeft; try eassumption.
  eapply local_in_all; eassumption.
  unfold vis. destruct (local_DomRng _ H1 _ _ _ H2); intuition.
Qed.

(** * Correspondence between Cminor environments and RTL register sets *)

(** A compilation environment (mapping) is well-formed if
  the following properties hold:
- Two distinct Cminor local variables are mapped to distinct pseudo-registers.
- A Cminor local variable and a let-bound variable are mapped to
  distinct pseudo-registers.
*)

Record map_wf (m: mapping) : Prop :=
  mk_map_wf {
    map_wf_inj:
      (forall id1 id2 r,
         m.(map_vars)!id1 = Some r -> m.(map_vars)!id2 = Some r -> id1 = id2);
     map_wf_disj:
      (forall id r,
         m.(map_vars)!id = Some r -> In r m.(map_letvars) -> False)
  }.

Lemma init_mapping_wf:
  map_wf init_mapping.
Proof.
  unfold init_mapping; split; simpl.
  intros until r. rewrite PTree.gempty. congruence.
  tauto.
Qed.

Lemma add_var_wf:
  forall s1 s2 map name r map' i,
  add_var map name s1 = OK (r,map') s2 i -> 
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  intros. monadInv H. 
  apply mk_map_wf; simpl.
  intros until r0. repeat rewrite PTree.gsspec.
  destruct (peq id1 name); destruct (peq id2 name).
  congruence.
  intros. inv H. elimtype False. 
  apply valid_fresh_absurd with r0 s1. 
  apply H1. left; exists id2; auto.
  eauto with rtlg.
  intros. inv H2. elimtype False. 
  apply valid_fresh_absurd with r0 s1. 
  apply H1. left; exists id1; auto.
  eauto with rtlg.
  inv H0. eauto.
  intros until r0. rewrite PTree.gsspec.
  destruct (peq id name). 
  intros. inv H.
  apply valid_fresh_absurd with r0 s1.
  apply H1. right; auto.
  eauto with rtlg.
  inv H0; eauto.
Qed.

Lemma add_vars_wf:
  forall names s1 s2 map map' rl i,
  add_vars map names s1 = OK (rl,map') s2 i ->
  map_wf map -> map_valid map s1 -> map_wf map'.
Proof.
  induction names; simpl; intros; monadInv H. 
  auto.
  exploit add_vars_valid; eauto. intros [A B].
  eapply add_var_wf; eauto.
Qed.

Lemma add_letvar_wf:
  forall map r,
  map_wf map -> ~reg_in_map map r -> map_wf (add_letvar map r).
Proof.
  intros. inv H. unfold add_letvar; constructor; simpl.
  auto.
  intros. elim H1; intro. subst r0. elim H0. left; exists id; auto.
  eauto.
Qed.

(** An RTL register environment matches a CminorSel local environment and
  let-environment if the value of every local or let-bound variable in
  the CminorSel environments is identical to the value of the
  corresponding pseudo-register in the RTL register environment. *)

(*LENB: replaced extension by injection. In particular, added paranmeter j:meminj
  and replaced lessdefs by val_injects*)

Record match_env (j:meminj)
      (map: mapping) (e: env) (le: letenv) (rs: regset) : Prop :=
  mk_match_env {
    me_vars:
      (forall id v,
         e!id = Some v -> exists r, map.(map_vars)!id = Some r
          /\ val_inject j v rs#r);
    me_letvars:
      val_list_inject j le rs##(map.(map_letvars))
  }.

Lemma match_env_find_var:
  forall j map e le rs id v r,
  match_env j map e le rs ->
  e!id = Some v ->
  map.(map_vars)!id = Some r ->
  val_inject j v rs#r.
Proof.
  intros. exploit me_vars; eauto. intros [r' [EQ' RS]].
  replace r with r'. auto. congruence.
Qed.

Lemma match_env_inject_incr: forall j map e le rs
        (MENV: match_env j map e le rs) j'
        (INC: inject_incr j j'),
      match_env j' map e le rs.
Proof.
  intros.
  destruct MENV as [MENVa MENVb].
  constructor; intros.
    destruct (MENVa _ _ H) as [r [MAP INJ]].
    apply (val_inject_incr _ _ _ _ INC) in INJ.
    exists r; split; trivial.
  apply (val_list_inject_incr _ _ _ _ INC) in MENVb; trivial.
Qed.

Lemma match_env_restrictD: forall j X map e le rs
        (MENV: match_env (restrict j X) map e le rs),
      match_env j map e le rs.
Proof. intros.
  eapply match_env_inject_incr; try eassumption.
  eapply restrict_incr.
Qed.

Lemma match_env_find_letvar:
  forall j map e le rs idx v r,
  match_env j map e le rs ->
  List.nth_error le idx = Some v ->
  List.nth_error map.(map_letvars) idx = Some r ->
  val_inject j v rs#r.
Proof.
  intros. exploit me_letvars; eauto.
  clear H. revert le H0 H1. generalize (map_letvars map). clear map.
  induction idx; simpl; intros.
  inversion H; subst le; inversion H0. subst v0.
  destruct l; inversion H1. subst r0.
  inversion H2. subst v'. auto.
  destruct l; destruct le; try discriminate.
  eapply IHidx; eauto.
  inversion H. auto.
Qed.

Lemma match_env_invariant:
  forall j map e le rs rs',
  match_env j map e le rs ->
  (forall r, (reg_in_map map r) -> rs'#r = rs#r) ->
  match_env j map e le rs'.
Proof.
  intros. inversion H. apply mk_match_env.
  intros. exploit me_vars0; eauto. intros [r [A B]].
  exists r; split. auto. rewrite H0; auto. left; exists id; auto.
  replace (rs'##(map_letvars map)) with (rs ## (map_letvars map)). auto.
  apply list_map_exten. intros. apply H0. right; auto.
Qed.

(** Matching between environments is preserved when an unmapped register
  (not corresponding to any Cminor variable) is assigned in the RTL
  execution. *)

Lemma match_env_update_temp:
  forall j map e le rs r v,
  match_env j map e le rs ->
  ~(reg_in_map map r) ->
  match_env j map e le (rs#r <- v).
Proof.
  intros. apply match_env_invariant with rs; auto.
  intros. case (Reg.eq r r0); intro. 
  subst r0; contradiction.
  apply Regmap.gso; auto.
Qed.
Hint Resolve match_env_update_temp: rtlg.

(** Matching between environments is preserved by simultaneous
  assignment to a Cminor local variable (in the Cminor environments)
  and to the corresponding RTL pseudo-register (in the RTL register
  environment). *)

Lemma match_env_update_var:
  forall j map e le rs id r v tv,
  val_inject j v tv ->
  map_wf map ->
  map.(map_vars)!id = Some r ->
  match_env j map e le rs ->
  match_env j map (PTree.set id v e) le (rs#r <- tv).
Proof.
  intros. inversion H0. inversion H2. apply mk_match_env.
  intros id' v'. rewrite PTree.gsspec. destruct (peq id' id); intros.
  subst id'. inv H3. exists r; split. auto. rewrite PMap.gss. auto.
  exploit me_vars0; eauto. intros [r' [A B]].
  exists r'; split. auto. rewrite PMap.gso; auto.
  red; intros. subst r'. elim n. eauto.
  erewrite list_map_exten. eauto.
  intros. symmetry. apply PMap.gso. red; intros. subst x. eauto. 
Qed.

(** A variant of [match_env_update_var] where a variable is optionally
  assigned to, depending on the [dst] parameter. *)

Lemma match_env_update_dest:
  forall j map e le rs dst r v tv,
  val_inject j v tv ->
  map_wf map ->
  reg_map_ok map r dst ->
  match_env j map e le rs ->
  match_env j map (set_optvar dst v e) le (rs#r <- tv).
Proof.
  intros. inv H1; simpl. 
  eapply match_env_update_temp; eauto. 
  eapply match_env_update_var; eauto.
Qed.
Hint Resolve match_env_update_dest: rtlg.

(** Matching and [let]-bound variables. *)

Lemma match_env_bind_letvar:
  forall j map e le rs r v,
  match_env j map e le rs ->
  val_inject j v rs#r ->
  match_env j (add_letvar map r) e (v :: le) rs.
Proof.
  intros. inv H. unfold add_letvar. apply mk_match_env; simpl; auto.
Qed.

Lemma match_env_unbind_letvar:
  forall j map e le rs r v,
  match_env j (add_letvar map r) e (v :: le) rs ->
  match_env j map e le rs.
Proof.
  unfold add_letvar; intros. inv H. simpl in *. 
  constructor. auto. inversion me_letvars0. auto.
Qed.

(** Matching between initial environments. *)

Lemma match_env_empty:
  forall j map,
  map.(map_letvars) = nil ->
  match_env j map (PTree.empty val) nil (Regmap.init Vundef).
Proof.
  intros. apply mk_match_env.
  intros. rewrite PTree.gempty in H0. discriminate.
  rewrite H. constructor.
Qed.

(** The assignment of function arguments to local variables (on the Cminor
  side) and pseudo-registers (on the RTL side) preserves matching
  between environments. *)

Lemma match_set_params_init_regs:
  forall j il rl s1 map2 s2 vl tvl i,
  add_vars init_mapping il s1 = OK (rl, map2) s2 i ->
  val_list_inject j vl tvl ->
  match_env j map2 (set_params vl il) nil (init_regs tvl rl)
  /\ (forall r, reg_fresh r s2 -> (init_regs tvl rl)#r = Vundef).
Proof.
  induction il; intros.

  inv H. split. apply match_env_empty. auto. intros. 
  simpl. apply Regmap.gi.

  monadInv H. simpl.
  exploit add_vars_valid; eauto. apply init_mapping_valid. intros [A B].
  exploit add_var_valid; eauto. intros [A' B']. clear B'.
  monadInv EQ1. 
  destruct H0 as [ | v1 tv1 vs tvs].
  (* vl = nil *)
  destruct (IHil _ _ _ _ nil nil _ EQ) as [ME UNDEF]. constructor. inv ME. split.
  replace (init_regs nil x) with (Regmap.init Vundef) in me_vars0, me_letvars0.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. inv H. exists x1; split. auto. constructor.
  eauto.
  eauto.
  destruct x; reflexivity.
  intros. apply Regmap.gi.
  (* vl = v1 :: vs *)
  destruct (IHil _ _ _ _ _ _ _ EQ H0) as [ME UNDEF]. inv ME. split.
  constructor; simpl.
  intros id v. repeat rewrite PTree.gsspec. destruct (peq id a); intros.
  subst a. (*inv H.*) inv H1. exists x1; split. auto. rewrite Regmap.gss. assumption.   
  exploit me_vars0; eauto. intros [r' [C D]]. 
  exists r'; split. auto. rewrite Regmap.gso. auto.
  apply valid_fresh_different with s.
  apply B. left; exists id; auto.
  eauto with rtlg. 
  destruct (map_letvars x0). auto. simpl in me_letvars0. inversion me_letvars0.
  intros. rewrite Regmap.gso. apply UNDEF. 
  apply reg_fresh_decr with s2; eauto with rtlg.
  apply sym_not_equal. apply valid_fresh_different with s2; auto.
Qed.

Lemma match_set_locals:
  forall j map1 s1,
  map_wf map1 ->
  forall il rl map2 s2 e le rs i,
  match_env j map1 e le rs ->
  (forall r, reg_fresh r s1 -> rs#r = Vundef) ->
  add_vars map1 il s1 = OK (rl, map2) s2 i ->
  match_env j map2 (set_locals il e) le rs.
Proof.
  induction il; simpl in *; intros.

  inv H2. auto.

  monadInv H2. 
  exploit IHil; eauto. intro. 
  monadInv EQ1.
  constructor.
  intros id v. simpl. repeat rewrite PTree.gsspec. 
  destruct (peq id a). subst a. intro. 
  exists x1. split. auto. inv H3. constructor.
  eauto with rtlg.
  intros. eapply me_vars; eauto. 
  simpl. eapply me_letvars; eauto.
Qed.

Lemma match_init_env_init_reg:
  forall j params s0 rparams map1 s1 i1 vars rvars map2 s2 i2 vparams tvparams,
  add_vars init_mapping params s0 = OK (rparams, map1) s1 i1 ->
  add_vars map1 vars s1 = OK (rvars, map2) s2 i2 ->
  val_list_inject j vparams tvparams ->
  match_env j map2 (set_locals vars (set_params vparams params))
            nil (init_regs tvparams rparams).
Proof.
  intros.
  exploit match_set_params_init_regs; eauto. intros [A B].
  eapply match_set_locals; eauto.
  eapply add_vars_wf; eauto. apply init_mapping_wf.
  apply init_mapping_valid.
Qed.

(** * The simulation argument *)

Require Import Errors.

Section CORRECTNESS.

Variable prog: CminorSel.program.
Variable tprog: RTL.program.
Hypothesis TRANSL: transl_program prog = OK tprog.

Let ge : CminorSel.genv := Genv.globalenv prog.
Let tge : RTL.genv := Genv.globalenv tprog.

(*NEW*) Variable hf : I64Helpers.helper_functions.

(** Relationship between the global environments for the original
  CminorSel program and the generated RTL program. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof
  (Genv.find_symbol_transf_partial transl_fundef _ TRANSL).

Lemma function_ptr_translated:
  forall (b: block) (f: CminorSel.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transl_fundef _ TRANSL).

Lemma functions_translated:
  forall (v: val) (f: CminorSel.fundef),
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transl_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transl_fundef _ TRANSL).

Lemma sig_transl_function:
  forall (f: CminorSel.fundef) (tf: RTL.fundef),
  transl_fundef f = OK tf ->
  RTL.funsig tf = CminorSel.funsig f.
Proof.
  intros until tf. unfold transl_fundef, transf_partial_fundef.
  case f; intro.
  unfold transl_function. 
  destruct (reserve_labels (fn_body f0) (PTree.empty node, init_state)) as [ngoto s0].
  case (transl_fun f0 ngoto s0); simpl; intros.
  discriminate.
  destruct p. simpl in H. inversion H. reflexivity.
  intro. inversion H. reflexivity.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  apply (Genv.find_var_info_transf_partial transl_fundef _ TRANSL).
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
    split. intros. rewrite varinfo_preserved. intuition.
    intros. split.
      intros [f H].
        apply function_ptr_translated in H. 
        destruct H as [? [? _]]. 
        eexists; eassumption.
     intros [f H]. 
         apply (@Genv.find_funct_ptr_rev_transf_partial
           _ _ _ transl_fundef prog _ TRANSL) in H.
         destruct H as [? [? _]]. eexists; eassumption.
Qed.

(** Correctness of the code generated by [add_move]. *)

Lemma tr_move_correct:
  forall r1 ns r2 nd cs f sp rs m,
  tr_move f.(fn_code) ns r1 nd r2 ->
  exists rs',
  corestep_star (rtl_eff_sem hf) tge
     (RTL_State cs f sp ns rs) m 
     (RTL_State cs f sp nd rs') m /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H. 
  exists rs; split. eapply corestep_star_zero. auto.
  exists (rs#r2 <- (rs#r1)); split. 
  apply corestep_star_one. eapply rtl_corestep_exec_Iop. eauto. auto. 
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

(** Correctness of the translation of [switch] statements *)

Lemma transl_switch_correct:
  forall j cs sp e m f map r nexits t ns,
  tr_switch f.(fn_code) map r nexits t ns ->
  forall rs i act,
  rs#r = Vint i ->
  map_wf map ->
  match_env j map e nil rs ->
  comptree_match i t = Some act ->
  exists nd, exists rs',
  corestep_star (rtl_eff_sem hf) tge (RTL_State cs f sp ns rs) m (RTL_State cs f sp nd rs') m /\
  nth_error nexits act = Some nd /\
  match_env j map e nil rs'.
Proof.
  Opaque Int.sub.
  induction 1; simpl; intros.
(* action *)
  inv H3. exists n; exists rs; intuition.
  apply corestep_star_zero.
(* ifeq *)
  caseEq (Int.eq i key); intro EQ; rewrite EQ in H5.
  inv H5. exists nfound; exists rs; intuition.
  apply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := true); eauto. 
  simpl. rewrite H2. simpl. congruence.
  exploit IHtr_switch; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := false); eauto.  
      simpl. rewrite H2. simpl. congruence. eexact EX.
(* iflt *)
  caseEq (Int.ltu i key); intro EQ; rewrite EQ in H5.
  exploit IHtr_switch1; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := true); eauto.  
    simpl. rewrite H2. simpl. congruence. eexact EX.
  exploit IHtr_switch2; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := false); eauto. 
    simpl. rewrite H2. simpl. congruence. eexact EX.
(* jumptable *)
  set (rs1 := rs#rt <- (Vint(Int.sub i ofs))).
  assert (ME1: match_env j map e nil rs1).
    unfold rs1. eauto with rtlg.
  assert (EX1: RTL_corestep hf tge (RTL_State cs f sp n rs) m (RTL_State cs f sp n1 rs1) m).
    eapply rtl_corestep_exec_Iop; eauto. 
    predSpec Int.eq Int.eq_spec ofs Int.zero; simpl.
    rewrite H10. rewrite Int.sub_zero_l. congruence.
    rewrite H6. simpl. rewrite <- Int.sub_add_opp. auto. 
  caseEq (Int.ltu (Int.sub i ofs) sz); intro EQ; rewrite EQ in H9.
  exploit H5; eauto. intros [nd [A B]].
  exists nd; exists rs1; intuition.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eexact EX1.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := true); eauto.  
    simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence. 
  apply corestep_star_one. eapply rtl_corestep_exec_Ijumptable; eauto. unfold rs1. apply Regmap.gss.
  exploit (IHtr_switch rs1); eauto. unfold rs1. rewrite Regmap.gso; auto.
  intros [nd [rs' [EX [NTH ME]]]].
  exists nd; exists rs'; intuition.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eexact EX1.
  eapply corestep_star_trans. 
    eapply corestep_star_one. eapply rtl_corestep_exec_Icond with (b := false); eauto. 
    simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
  eexact EX. 
Qed.

(** ** Semantic preservation for the translation of expressions *)

(*LENB: translation of sp. Contrary to selection phase,
  the use of eval_operation (and the existing lemmas about
  eval_operation_inject) here suggests that we
  require sp=Vptr b Int.zero and sp' = Vptr b' Int.zero instead
  of sp=Vptr b i and sp' = Vptr b' i for some arbitrary i.*)
Definition sp_preserved (j:meminj) (sp sp':val) := 
    exists b b', sp = Vptr b Int.zero /\ sp' = Vptr b' Int.zero /\ 
                j b = Some(b',0).

Lemma sp_incr j j' sp sp': sp_preserved j sp sp' -> inject_incr j j' ->
     sp_preserved j' sp sp'.
Proof. intros.  
  destruct H as [b [b' [? [? ?]]]].
  exists b, b'; repeat split; eauto.
Qed.

Lemma sp_preserved_intern_incr mu mu' sp sp': forall
      (SP : sp_preserved (local_of mu) sp sp')
      (INC : intern_incr mu mu'),
   sp_preserved (local_of mu') sp sp'.
Proof. intros.
  destruct SP as [spb [tspb [SP [TSP LocSP]]]]. 
  exists spb, tspb. intuition. eapply INC; assumption. 
Qed.

Lemma shift_stack_addressing_zero: forall addr,
 shift_stack_addressing (Int.repr 0) addr = addr.
Proof. intros.
  destruct addr; try reflexivity. 
  simpl. rewrite Int.add_zero_l. trivial.
Qed.

Section CORRECTNESS_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

(** The proof of semantic preservation for the translation of expressions
  is a simulation argument based on diagrams of the following form:
<<
                    I /\ P
    e, le, m, a ------------- State cs code sp ns rs tm
         ||                      |
         ||                      |*
         ||                      |
         \/                      v
    e, le, m, v ------------ State cs code sp nd rs' tm'
                    I /\ Q
>>
  where [tr_expr code map pr a ns nd rd] is assumed to hold.
  The left vertical arrow represents an evaluation of the expression [a].
  The right vertical arrow represents the execution of zero, one or
  several instructions in the generated RTL flow graph [code].

  The invariant [I] is the agreement between Cminor environments and
  RTL register environment, as captured by [match_envs].

  The precondition [P] includes the well-formedness of the compilation
  environment [mut].

  The postconditions [Q] state that in the final register environment
  [rs'], register [rd] contains value [v], and the registers in
  the set of preserved registers [pr] are unchanged, as are the registers
  in the codomain of [map].

  We formalize this simulation property by the following predicate
  parameterized by the CminorSel evaluation (left arrow).  *)

Definition transl_expr_prop 
     (le: letenv) (a: expr) (v: val) : Prop :=
  forall mu tm cs f map pr ns nd rd rs dst
 (*NEW:*)(PG: meminj_preserves_globals ge (as_inj mu))
         sp' (SP: sp_preserved (local_of mu) sp sp')
         (WD: SM_wd mu) (SMV: sm_valid mu m tm) 
         (RC: REACH_closed m (vis mu))
         (Glob: forall b, isGlobalBlock ge b = true -> 
                  frgnBlocksSrc mu b = true)
         (OBS: silent hf ge a)

    (MWF: map_wf map)
    (TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
    (ME: match_env (restrict (as_inj mu) (vis mu)) map e le rs)
    (EXT: Mem.inject (as_inj mu) m tm),
  exists rs', exists tm', exists mu',
  (intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m tm'
  /\ SM_wd mu'
  /\ sm_valid mu' m tm'
  /\ REACH_closed m (vis mu'))
  /\ corestep_star (rtl_eff_sem hf) tge
        (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm' 
  /\ match_env (restrict (as_inj mu') (vis mu')) map (set_optvar dst v e) le rs'
  /\ val_inject (restrict (as_inj mu') (vis mu')) v rs'#rd
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject (as_inj mu') m tm'.

Definition transl_exprlist_prop 
     (le: letenv) (al: exprlist) (vl: list val) : Prop :=
  forall mu tm cs f map pr ns nd rl rs
 (*NEW:*)(PG: meminj_preserves_globals ge (as_inj mu))
         sp' (SP: sp_preserved (local_of mu) sp sp')
         (WD: SM_wd mu) (SMV: sm_valid mu m tm)
         (RC: REACH_closed m (vis mu))
         (Glob: forall b, isGlobalBlock ge b = true -> 
                  frgnBlocksSrc mu b = true)
         (OBS: silentExprList hf ge al)

    (MWF: map_wf map)
    (TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
    (ME: match_env (restrict (as_inj mu) (vis mu)) map e le rs)
    (EXT: Mem.inject (as_inj mu) m tm),
  exists rs', exists tm', exists mu',
  (intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m tm'
  /\ SM_wd mu'
  /\ sm_valid mu' m tm'
  /\ REACH_closed m (vis mu'))
  /\ corestep_star (rtl_eff_sem hf) tge
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env (restrict (as_inj mu') (vis mu')) map e le rs'
  /\ val_list_inject (restrict (as_inj mu') (vis mu')) vl rs'##rl
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject (as_inj mu') m tm'.

Definition transl_condexpr_prop 
     (le: letenv) (a: condexpr) (v: bool) : Prop :=
  forall mu tm cs f map pr ns ntrue nfalse rs
 (*NEW:*)(PG: meminj_preserves_globals ge (as_inj mu))
         sp' (SP: sp_preserved (local_of mu) sp sp')
         (WD: SM_wd mu) (SMV: sm_valid mu m tm)
         (RC: REACH_closed m (vis mu))
         (Glob: forall b, isGlobalBlock ge b = true -> 
                  frgnBlocksSrc mu b = true)
         (OBS: silentCondExpr hf ge a)

    (MWF: map_wf map)
    (TE: tr_condition f.(fn_code) map pr a ns ntrue nfalse)
    (ME: match_env (restrict (as_inj mu) (vis mu)) map e le rs)
    (EXT: Mem.inject (as_inj mu) m tm),
  exists rs', exists tm', exists mu',
   (intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m tm'
  /\ SM_wd mu'
  /\ sm_valid mu' m tm'
  /\ REACH_closed m (vis mu'))
  /\ corestep_plus (rtl_eff_sem hf) tge
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' (if v then ntrue else nfalse) rs') tm'
  /\ match_env (restrict (as_inj mu') (vis mu')) map e le rs'
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject (as_inj mu') m tm'.

(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma transl_expr_Evar_correct:
  forall (le : letenv) (id : positive) (v: val),
  e ! id = Some v ->
  transl_expr_prop le (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit tr_move_correct; eauto. intros [rs' [A [B C]]]. 
  exists rs'; exists tm; exists mu. 
    split. simpl. trivial.
    split. apply intern_incr_refl.
    split. apply sm_inject_separated_same_sminj.
    split. apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      eauto.
  split. eauto.
  destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto. 
  split. eapply match_env_invariant; eauto.
  split. congruence.
  split; auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto. 
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto. 
  split. congruence. 
  split. intros. apply C. intuition congruence.
  auto.
Qed.

Lemma transl_expr_Eop_correct:
  forall (le : letenv) (op : operation) (args : exprlist)
         (vargs : list val) (v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  eval_operation ge sp op vargs m = Some v ->
  transl_expr_prop le (Eop op args) v.
Proof.
  intros; red; intros. 
(*  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition. *)
  inv TE.
(* normal case *) 
  exploit H0; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RR1 [RO1 EXT1]]]]]]]].
  (*Was: edestruct eval_operation_lessdef...*)

  assert (PGR': meminj_preserves_globals ge (restrict (as_inj mu') (vis mu'))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
      apply MU'. apply MU'. 
      intros b Gb. eapply intern_incr_vis. eapply MU'.
         unfold vis. rewrite (Glob _ Gb). intuition. 

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_operation_inject as [v' []]; try eapply H1. 
    eapply PGR'. 
    eapply restrictI_Some. 
      apply local_in_all; try eapply MU'. eassumption.       
      destruct (local_DomRng _ WD _ _ _ Jsp) as [lS lT].
        eapply intern_incr_vis; try eapply MU'. 
        unfold vis; rewrite lS. trivial.
    eapply RR1.
    eapply inject_restrict; try eassumption. eapply MU'.
  rewrite eval_shift_stack_operation in H2. simpl in H2. rewrite Int.add_zero in H2.

  exists (rs1#rd <- v'); exists tm1.
  exists mu'. split. assumption. 
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
  eapply corestep_star_one. eapply rtl_corestep_exec_Iop; eauto.
  rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ ge tge). eauto.
  exact symbols_preserved. 
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) (vargs : list val) (vaddr v : val),
  eval_exprlist ge sp e m le args vargs ->
  transl_exprlist_prop le args vargs ->
  Op.eval_addressing ge sp addr vargs = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  transl_expr_prop le (Eload chunk addr args) v.
Proof.
  intros; red; intros.
  inv TE.
  exploit H0; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  (*Was: edestruct eval_addressing_lessdef as [vaddr' []]; eauto.*)

  assert (PGR': meminj_preserves_globals ge (restrict (as_inj mu') (vis mu'))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
      apply MU'. apply MU'. 
      intros b Gb. eapply intern_incr_vis. eapply MU'.
         unfold vis. rewrite (Glob _ Gb). intuition. 

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_addressing_inject as [vaddr' [? ?]]; try eapply RES1. 
    eapply PGR'.
    eapply restrictI_Some. 
      apply local_in_all; try eapply MU'. eassumption.       
      destruct (local_DomRng _ WD _ _ _ Jsp) as [lS lT].
        eapply intern_incr_vis; try eapply MU'. 
        unfold vis; rewrite lS. trivial.
    eapply H1.
    
  rewrite shift_stack_addressing_zero in H3; simpl in H3.
  edestruct Mem.loadv_inject as [v' []].
    eapply inject_restrict. eapply EXT1. eapply MU'.
    eassumption.
    eassumption. 
  exists (rs1#rd <- v'); exists tm1; exists mu'.
  split. assumption. 
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
    eapply corestep_star_one.
      eapply rtl_corestep_exec_Iload; try eassumption. 
    rewrite (eval_addressing_preserved ge). assumption.
       exact symbols_preserved.
(* Match-env *)
  split. eauto with rtlg. 
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto. 
Qed.

Lemma transl_expr_Econdition_correct:
  forall (le : letenv) (a: condexpr) (ifso ifnot : expr)
         (va : bool) (v : val),
  eval_condexpr ge sp e m le a va ->
  transl_condexpr_prop le a va ->
  eval_expr ge sp e m le (if va then ifso else ifnot) v ->
  transl_expr_prop le (if va then ifso else ifnot) v ->
  transl_expr_prop le (Econdition a ifso ifnot) v.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. 
     simpl in OBS. apply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [OTHER1 EXT1]]]]]]].
  assert (tr_expr f.(fn_code) map pr (if va then ifso else ifnot) (if va then ntrue else nfalse) nd rd dst).
    destruct va; auto.
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros b Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
         destruct va; eapply OBS.
     eauto. 
     eauto.
     eassumption. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]]]].
  exists rs2; exists tm2, mu''.
  split. 
    intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_plus_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_plus_fwd. eassumption.
             eapply corestep_star_fwd. eassumption.  
 (* Exec *)
  split. eapply corestep_star_trans.
           apply corestep_plus_star. eexact EX1. eexact EX2.
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r); auto.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Elet_correct:
  forall (le : letenv) (a1 a2 : expr) (v1 v2 : val),
  eval_expr ge sp e m le a1 v1 ->
  transl_expr_prop le a1 v1 ->
  eval_expr ge sp e m (v1 :: le) a2 v2 ->
  transl_expr_prop (v1 :: le) a2 v2 ->
  transl_expr_prop le (Elet a1 a2) v2.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros b Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
       eapply OBS.
     eauto. 
     eauto.
     eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME3 [RES2 [OTHER2 EXT2]]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_star_fwd. eassumption.
             eapply corestep_star_fwd. eassumption.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1. eexact EX2. (* auto.*)
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r0); auto.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Eletvar_correct:
  forall (le : list val) (n : nat) (v : val),
  nth_error le n = Some v ->
  transl_expr_prop le (Eletvar n) v.
Proof.
  intros; red; intros; inv TE.
  exploit tr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1; exists tm, mu.
  split. clear H2. intuition. 
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.

      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.      
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split. 
  destruct H2 as [[A B] | [A B]].
  subst r dst; simpl. 
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto. 
(* Other regs *)
  split. intros. 
  destruct H2 as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma transl_expr_Ebuiltin_correct:
  forall le ef al vl v,
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  transl_expr_prop le (Ebuiltin ef al) v.
Proof.
  intros; red; intros. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition. 
  inv TE.
  simpl in OBS.
  exploit H0; eauto. eapply OBS.
  destruct OBS as [isHLP SEL]. 
  assert (OBS :~ observableEF hf ef) by solve [eapply EFhelpers; trivial]. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RR1 [RO1 EXT1]]]]]]]].
  (*WAS: exploit external_call_mem_extends; eauto. 
        intros [v' [tm2 [A [B [C [D E]]]]]].*)
  destruct MU' as [INC [SEP [LOCALLOC' [WD' [SMV' RC']]]]].
  exploit (inlineable_extern_inject _ _ GDE_lemma);
       try eapply RR1; try eapply H1; try eassumption.
     apply symbols_preserved.
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC. 
        rewrite <- FF; apply Glob.
     eapply intern_incr_meminj_preserves_globals_as_inj.
         apply WD. split; assumption. 
     assumption. assumption. 
 (* exploit external_call_mem_inject; eauto. 
        intros [j' [v' [tm2 [A [B [C [D [E [F G]]]]]]]]].*)
   intros [mu'' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD'' [SMV'' RC'']]]]]]]]]]]]].
  exists (rs1#rd <- vres'); exists tm', mu''.
  split. intuition.
    eapply intern_incr_trans. eassumption. eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_star_fwd. eassumption.
             eapply external_call_mem_forward; eassumption.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
         apply corestep_star_one. eapply rtl_corestep_exec_Ibuiltin; try eassumption. 
(*  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.*)
(* Match-env *)
  split. eapply match_env_update_dest; try eassumption.
     eapply match_env_inject_incr; try eassumption.
     apply intern_incr_restrict; eassumption. 
(* Result reg *)
  split. intros. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  assumption. 
Qed.

Lemma silentD_Eexternal name ef al b:  forall
  (SIL: silent hf ge (Eexternal name (ef_sig ef) al))
  (FS: Genv.find_symbol ge name = Some b)
  (FFP: Genv.find_funct_ptr ge b = Some (External ef)),
  silentExprList hf ge al /\ EFisHelper hf ef.
Proof. intros.  
unfold silent in SIL.
rewrite FS, FFP in SIL.
intuition.
Qed.
(*
Lemma silentD_Eexternal name ef al b:  forall
  (SIL: silent hf ge (Eexternal name (ef_sig ef) al))
  (FS: Genv.find_symbol ge name = Some b)
  (FFP: Genv.find_funct_ptr ge b = Some (External ef)),
  silentExprList hf ge al /\ observableEF hf ef = false
   /\ forall (args : list val) (m : mem),
             BuiltinEffect ge ef args m = EmptyEffect.
Proof. intros.  
unfold silent in SIL.
rewrite FS, FFP in SIL.
intuition.
Qed.
*)
Lemma transl_expr_Eexternal_correct:
  forall le id sg al b ef vl v,
  Genv.find_symbol ge id = Some b ->
  Genv.find_funct_ptr ge b = Some (External ef) ->
  ef_sig ef = sg ->
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  transl_expr_prop le (Eexternal id sg al) v.
Proof.
  intros; red; intros. inv TE.
  destruct (silentD_Eexternal _ _ _ _ OBS H H0)
    as [SilentArgs isHLP]; clear OBS.
  assert (OBS := EFhelpers _ _ isHLP). 
  exploit H3; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RR1 [RO1 EXT1]]]]]]]].
  assert (PG': meminj_preserves_globals ge (as_inj mu')).     
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
      apply MU'. apply MU'.
  destruct MU' as [INC [SEP [LOCALLOC' [WD' [SMV' RC']]]]].
  exploit (inlineable_extern_inject _ _ GDE_lemma);
       try eapply RR1; try eapply H1; try eassumption.
     apply symbols_preserved.
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC. 
        rewrite <- FF; apply Glob.
  intros [mu'' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD'' [SMV'' RC'']]]]]]]]]]]]].
  eexists; exists tm', mu''. 
  split. intuition.
     eapply intern_incr_trans; eassumption.
     eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_star_fwd. eassumption.
     eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_star_fwd. eassumption.
             eapply external_call_mem_forward; eassumption.
  exploit function_ptr_translated; eauto. simpl. intros [tf [P Q]]. inv Q. 
(*  exists (rs1#rd <- vres'); exists tm2.*)
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1.
    eapply corestep_star_trans. 
     apply corestep_star_one. eapply rtl_corestep_exec_Icall; eauto.
        simpl. rewrite symbols_preserved. rewrite H. eauto. auto.
    eapply corestep_star_trans. 
     apply corestep_star_one. eapply rtl_corestep_exec_function_external.
       assumption. eassumption.
     (*  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.*)
     apply corestep_star_one. apply rtl_corestep_exec_return. 
(* Match-env *)
  split. eapply match_env_update_dest; try eassumption.
     eapply match_env_inject_incr; try eassumption.
     apply intern_incr_restrict; eassumption. 
(* Result reg *)
   split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma transl_exprlist_Enil_correct:
  forall (le : letenv),
  transl_exprlist_prop le Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs; exists tm, mu.
  split. intuition. 
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.

      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.     
  split. apply corestep_star_zero.
  split. assumption.
  split. constructor.
  auto.
Qed.

Lemma transl_exprlist_Econs_correct:
  forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
         (vl : list val),
  eval_expr ge sp e m le a1 v1 ->
  transl_expr_prop le a1 v1 ->
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  transl_exprlist_prop le (Econs a1 al) (v1 :: vl).
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1.
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros b Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
     eapply OBS.
     eauto. 
     eauto.
     eassumption. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_star_fwd. eassumption.
             eapply corestep_star_fwd. eassumption.
(* Exec *)
  split. eapply corestep_star_trans. eexact EX1. eexact EX2. 
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. constructor. rewrite OTHER2. 
     eapply val_inject_incr; try eassumption. 
     eapply intern_incr_restrict. eapply MU''. eapply MU''.
    simpl; tauto.
  auto.
(* Other regs *)
  split. intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto. 
  apply OTHER1; auto.
(* Mem *)
  auto.
Qed.

Lemma transl_condexpr_CEcond_correct:
  forall le cond al vl vb,
  eval_exprlist ge sp e m le al vl ->
  transl_exprlist_prop le al vl ->
  eval_condition cond vl m = Some vb ->
  transl_condexpr_prop le (CEcond cond al) vb.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  exists rs1; exists tm1, mu'.
  split. assumption.
(* Exec *)
  split. eapply corestep_star_plus_trans. eexact EX1.
      eapply corestep_plus_one. eapply rtl_corestep_exec_Icond. eauto. 
      (*eapply eval_condition_lessdef; eauto.*)
    eapply eval_condition_inject; eauto. 
    eapply inject_restrict; eauto.
     eapply MU'.
    auto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. assumption. 
(* Mem *)
  auto.
Qed.

Lemma transl_condexpr_CEcondition_correct:
  forall le a b c va v,
  eval_condexpr ge sp e m le a va ->
  transl_condexpr_prop le a va ->
  eval_condexpr ge sp e m le (if va then b else c) v ->
  transl_condexpr_prop le (if va then b else c) v ->
  transl_condexpr_prop le (CEcondition a b c) v.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [OTHER1 EXT1]]]]]]].
  assert (tr_condition (fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
    destruct va; auto.
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1.
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros bb Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
       destruct va; eapply OBS.
     eauto. 
     eauto.
     eassumption. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME2 [OTHER2 EXT2]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_plus_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_plus_fwd. eassumption.
             eapply corestep_plus_fwd. eassumption.
(* Exec *)
  split. eapply corestep_plus_trans. eexact EX1. eexact EX2.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. intros. rewrite OTHER2; auto. 
(* Mem *)
  auto.
Qed.

Lemma transl_condexpr_CElet_correct:
  forall le a b v1 v2,
  eval_expr ge sp e m le a v1 ->
  transl_expr_prop le a v1 ->
  eval_condexpr ge sp e m (v1 :: le) b v2 ->
  transl_condexpr_prop (v1 :: le) b v2 ->
  transl_condexpr_prop le (CElet a b) v2.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto. 
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1.
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros bb Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb).
       eapply OBS. 
     eauto. 
     eauto.
     eapply match_env_bind_letvar; eauto. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME3 [OTHER2 EXT2]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply corestep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply corestep_star_fwd. eassumption.
             eapply corestep_plus_fwd. eassumption.
(* Exec *)
  split. eapply corestep_star_plus_trans. eexact EX1. eexact EX2.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Other regs *)
  split. intros. rewrite OTHER2; auto. 
(* Mem *)
  auto.
Qed.

Theorem transl_expr_correct:
  forall le a v,
  eval_expr ge sp e m le a v ->
  transl_expr_prop le a v.
Proof
  (eval_expr_ind3 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_condexpr_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_expr_Ebuiltin_correct
     transl_expr_Eexternal_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_condexpr_CEcond_correct
     transl_condexpr_CEcondition_correct
     transl_condexpr_CElet_correct).

Theorem transl_exprlist_correct:
  forall le a v,
  eval_exprlist ge sp e m le a v ->
  transl_exprlist_prop le a v.
Proof
  (eval_exprlist_ind3 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_condexpr_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_expr_Ebuiltin_correct
     transl_expr_Eexternal_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_condexpr_CEcond_correct
     transl_condexpr_CEcondition_correct
     transl_condexpr_CElet_correct).

Theorem transl_condexpr_correct:
  forall le a v,
  eval_condexpr ge sp e m le a v ->
  transl_condexpr_prop le a v.
Proof
  (eval_condexpr_ind3 ge sp e m
     transl_expr_prop
     transl_exprlist_prop
     transl_condexpr_prop
     transl_expr_Evar_correct
     transl_expr_Eop_correct
     transl_expr_Eload_correct
     transl_expr_Econdition_correct
     transl_expr_Elet_correct
     transl_expr_Eletvar_correct
     transl_expr_Ebuiltin_correct
     transl_expr_Eexternal_correct
     transl_exprlist_Enil_correct
     transl_exprlist_Econs_correct
     transl_condexpr_CEcond_correct
     transl_condexpr_CEcondition_correct
     transl_condexpr_CElet_correct).

End CORRECTNESS_EXPR.

(*LENB: The same for effect-steps*)
Section CORRECTNESS_EXPR_EFF.

Lemma Efftr_move_correct:
  forall r1 ns r2 nd cs f sp rs m,
  tr_move f.(fn_code) ns r1 nd r2 ->
  exists rs',
  effstep_star (rtl_eff_sem hf) tge EmptyEffect
     (RTL_State cs f sp ns rs) m 
     (RTL_State cs f sp nd rs') m /\
  rs'#r2 = rs#r1 /\
  (forall r, r <> r2 -> rs'#r = rs#r).
Proof.
  intros. inv H. 
  exists rs; split. eapply effstep_star_zero. auto.
  exists (rs#r2 <- (rs#r1)); split. 
  apply effstep_star_one. eapply rtl_effstep_exec_Iop. eauto. auto. 
  split. apply Regmap.gss. intros; apply Regmap.gso; auto.
Qed.

Lemma Efftransl_switch_correct:
  forall j cs sp e m f map r nexits t ns,
  tr_switch f.(fn_code) map r nexits t ns ->
  forall rs i act,
  rs#r = Vint i ->
  map_wf map ->
  match_env j map e nil rs ->
  comptree_match i t = Some act ->
  exists nd, exists rs',
  effstep_star (rtl_eff_sem hf) tge EmptyEffect
        (RTL_State cs f sp ns rs) m (RTL_State cs f sp nd rs') m /\
  nth_error nexits act = Some nd /\
  match_env j map e nil rs'.
Proof.
  Opaque Int.sub.
  induction 1; simpl; intros.
(* action *)
  inv H3. exists n; exists rs; intuition.
  apply effstep_star_zero.
(* ifeq *)
  caseEq (Int.eq i key); intro EQ; rewrite EQ in H5.
  inv H5. exists nfound; exists rs; intuition.
  apply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := true); eauto. 
  simpl. rewrite H2. simpl. congruence.
  exploit IHtr_switch; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply effstep_star_trans'. 
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := false); eauto.  
      simpl. rewrite H2. simpl. congruence. eexact EX.
   extensionality b; extensionality z. rewrite absoption_orb; trivial.
(* iflt *)
  caseEq (Int.ltu i key); intro EQ; rewrite EQ in H5.
  exploit IHtr_switch1; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply effstep_star_trans'. 
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := true); eauto.  
    simpl. rewrite H2. simpl. congruence. eexact EX.
    extensionality b; extensionality z. rewrite absoption_orb; trivial.
  exploit IHtr_switch2; eauto. intros [nd1 [rs1 [EX [NTH ME]]]].
  exists nd1; exists rs1; intuition.
  eapply effstep_star_trans'. 
    eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := false); eauto. 
    simpl. rewrite H2. simpl. congruence. eexact EX.
    extensionality b; extensionality z. rewrite absoption_orb; trivial.
(* jumptable *)
  set (rs1 := rs#rt <- (Vint(Int.sub i ofs))).
  assert (ME1: match_env j map e nil rs1).
    unfold rs1. eauto with rtlg.
  assert (EX1: RTL_effstep hf tge EmptyEffect (RTL_State cs f sp n rs) m (RTL_State cs f sp n1 rs1) m).
    eapply rtl_effstep_exec_Iop; eauto. 
    predSpec Int.eq Int.eq_spec ofs Int.zero; simpl.
    rewrite H10. rewrite Int.sub_zero_l. congruence.
    rewrite H6. simpl. rewrite <- Int.sub_add_opp. auto. 
  caseEq (Int.ltu (Int.sub i ofs) sz); intro EQ; rewrite EQ in H9.
  exploit H5; eauto. intros [nd [A B]].
  exists nd; exists rs1; intuition.
  eapply effstep_star_trans'. 
    eapply effstep_star_one. eexact EX1.
    eapply effstep_star_trans. 
      eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := true); eauto.  
      simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.  
    apply effstep_star_one. eapply rtl_effstep_exec_Ijumptable; eauto. unfold rs1. apply Regmap.gss.    
    extensionality b; extensionality z. rewrite absoption_orb; trivial.
  exploit (IHtr_switch rs1); eauto. unfold rs1. rewrite Regmap.gso; auto.
  intros [nd [rs' [EX [NTH ME]]]].
  exists nd; exists rs'; intuition.
  eapply effstep_star_trans'. 
    eapply effstep_star_one. eexact EX1.
    eapply effstep_star_trans. 
      eapply effstep_star_one. eapply rtl_effstep_exec_Icond with (b := false); eauto. 
      simpl. unfold rs1. rewrite Regmap.gss. simpl. congruence.
    eexact EX.
  extensionality b; extensionality z. rewrite absoption_orb; trivial. 
Qed.

Variable sp: val.
Variable e: env.
Variable m: mem.

Definition Efftransl_expr_prop 
     (le: letenv) (a: expr) (v: val) : Prop :=
  forall mu tm cs f map pr ns nd rd rs dst
 (*NEW:*)(PG: meminj_preserves_globals ge (as_inj mu))
         sp' (SP: sp_preserved (local_of mu) sp sp')
         (WD: SM_wd mu) (SMV: sm_valid mu m tm) 
         (RC: REACH_closed m (vis mu))
         (Glob: forall b, isGlobalBlock ge b = true -> 
                  frgnBlocksSrc mu b = true)
         (OBS: silent hf ge a)

    (MWF: map_wf map)
    (TE: tr_expr f.(fn_code) map pr a ns nd rd dst)
    (ME: match_env (restrict (as_inj mu) (vis mu)) map e le rs)
    (EXT: Mem.inject (as_inj mu) m tm),
  exists rs', exists tm', exists mu',
  (intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m tm'
  /\ SM_wd mu'
  /\ sm_valid mu' m tm'
  /\ REACH_closed m (vis mu'))
  /\ effstep_star (rtl_eff_sem hf) tge EmptyEffect
        (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env (restrict (as_inj mu') (vis mu')) map (set_optvar dst v e) le rs'
  /\ val_inject (restrict (as_inj mu') (vis mu')) v rs'#rd
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject (as_inj mu') m tm'.

Definition Efftransl_exprlist_prop 
     (le: letenv) (al: exprlist) (vl: list val) : Prop :=
  forall mu tm cs f map pr ns nd rl rs
 (*NEW:*)(PG: meminj_preserves_globals ge (as_inj mu))
         sp' (SP: sp_preserved  (local_of mu) sp sp')
         (WD: SM_wd mu) (SMV: sm_valid mu m tm)
         (RC: REACH_closed m (vis mu))
         (Glob: forall b, isGlobalBlock ge b = true -> 
                  frgnBlocksSrc mu b = true)
         (OBS: silentExprList hf ge al)

    (MWF: map_wf map)
    (TE: tr_exprlist f.(fn_code) map pr al ns nd rl)
    (ME: match_env (restrict (as_inj mu) (vis mu)) map e le rs)
    (EXT: Mem.inject (as_inj mu) m tm),
  exists rs', exists tm', exists mu',
  (intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m tm'
  /\ SM_wd mu'
  /\ sm_valid mu' m tm'
  /\ REACH_closed m (vis mu'))
  /\ effstep_star (rtl_eff_sem hf) tge EmptyEffect
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' nd rs') tm'
  /\ match_env (restrict (as_inj mu') (vis mu')) map e le rs'
  /\ val_list_inject (restrict (as_inj mu') (vis mu')) vl rs'##rl
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject (as_inj mu') m tm'.

Definition Efftransl_condexpr_prop 
     (le: letenv) (a: condexpr) (v: bool) : Prop :=
  forall mu tm cs f map pr ns ntrue nfalse rs
 (*NEW:*)(PG: meminj_preserves_globals ge (as_inj mu))
         sp' (SP: sp_preserved (local_of mu) sp sp')
         (WD: SM_wd mu) (SMV: sm_valid mu m tm)
         (RC: REACH_closed m (vis mu))
         (Glob: forall b, isGlobalBlock ge b = true -> 
                  frgnBlocksSrc mu b = true)
         (OBS: silentCondExpr hf ge a)

    (MWF: map_wf map)
    (TE: tr_condition f.(fn_code) map pr a ns ntrue nfalse)
    (ME: match_env (restrict (as_inj mu) (vis mu)) map e le rs)
    (EXT: Mem.inject (as_inj mu) m tm),
  exists rs', exists tm', exists mu',
   (intern_incr mu mu'
  /\ sm_inject_separated mu mu' m tm
  /\ sm_locally_allocated mu mu' m tm m tm'
  /\ SM_wd mu'
  /\ sm_valid mu' m tm'
  /\ REACH_closed m (vis mu'))
  /\ effstep_plus (rtl_eff_sem hf) tge EmptyEffect
       (RTL_State cs f sp' ns rs) tm (RTL_State cs f sp' (if v then ntrue else nfalse) rs') tm'
  /\ match_env (restrict (as_inj mu') (vis mu')) map e le rs'
  /\ (forall r, In r pr -> rs'#r = rs#r)
  /\ Mem.inject (as_inj mu') m tm'.

(** The correctness of the translation is a huge induction over
  the Cminor evaluation derivation for the source program.  To keep
  the proof manageable, we put each case of the proof in a separate
  lemma.  There is one lemma for each Cminor evaluation rule.
  It takes as hypotheses the premises of the Cminor evaluation rule,
  plus the induction hypotheses, that is, the [transl_expr_prop], etc,
  corresponding to the evaluations of sub-expressions or sub-statements. *)

Lemma Efftransl_expr_Evar_correct:
  forall (le : letenv) (id : positive) (v: val),
  e ! id = Some v ->
  Efftransl_expr_prop le (Evar id) v.
Proof.
  intros; red; intros. inv TE.
  exploit match_env_find_var; eauto. intro EQ.
  exploit Efftr_move_correct; eauto. intros [rs' [A [B C]]]. 
  exists rs'; exists tm;  exists mu. 
    split. simpl. trivial.
    split. apply intern_incr_refl.
    split. apply sm_inject_separated_same_sminj.
    split. apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      eauto.
  split. eauto. 
  destruct H2 as [[D E] | [D E]].
  (* optimized case *)
  subst r dst. simpl.
  assert (forall r, rs'#r = rs#r).
    intros. destruct (Reg.eq r rd). subst r. auto. auto. 
  split. eapply match_env_invariant; eauto.
  split. congruence.
  split; auto.
  (* general case *)
  split.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto. 
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd). congruence. auto. 
  split. congruence. 
  split. intros. apply C. intuition congruence.
  auto.
Qed.

Lemma Efftransl_expr_Eop_correct:
  forall (le : letenv) (op : operation) (args : exprlist)
         (vargs : list val) (v : val),
  eval_exprlist ge sp e m le args vargs ->
  Efftransl_exprlist_prop le args vargs ->
  eval_operation ge sp op vargs m = Some v ->
  Efftransl_expr_prop le (Eop op args) v.
Proof.
  intros; red; intros. inv TE.
(* normal case *) 
  exploit H0; eauto.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RR1 [RO1 EXT1]]]]]]]].
  (*Was: edestruct eval_operation_lessdef...*)

  assert (PGR': meminj_preserves_globals ge (restrict (as_inj mu') (vis mu'))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
      apply MU'. apply MU'. 
      intros b Gb. eapply intern_incr_vis. eapply MU'.
         unfold vis. rewrite (Glob _ Gb). intuition. 

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_operation_inject as [v' []]; try eapply H1. 
    eapply PGR'. 
    eapply restrictI_Some. 
      apply local_in_all; try eapply MU'. eassumption.       
      destruct (local_DomRng _ WD _ _ _ Jsp) as [lS lT].
        eapply intern_incr_vis; try eapply MU'. 
        unfold vis; rewrite lS. trivial.
    eapply RR1.
    eapply inject_restrict; try eassumption. eapply MU'.
  rewrite eval_shift_stack_operation in H2. simpl in H2. rewrite Int.add_zero in H2.

  exists (rs1#rd <- v'); exists tm1.
  exists mu'. split. assumption. 
(* Exec *)
  split. eapply effstep_star_trans'. eexact EX1.
    eapply effstep_star_one. eapply rtl_effstep_exec_Iop; eauto.
      rewrite (@eval_operation_preserved CminorSel.fundef _ _ _ ge tge). eauto.
      exact symbols_preserved.
    extensionality b; extensionality z. rewrite absoption_orb; trivial. 
(* Match-env *)
  split. eauto with rtlg.
(* Result reg *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Eload_correct:
  forall (le : letenv) (chunk : memory_chunk) (addr : Op.addressing)
         (args : exprlist) (vargs : list val) (vaddr v : val),
  eval_exprlist ge sp e m le args vargs ->
  Efftransl_exprlist_prop le args vargs ->
  Op.eval_addressing ge sp addr vargs = Some vaddr ->
  Mem.loadv chunk m vaddr = Some v ->
  Efftransl_expr_prop le (Eload chunk addr args) v.
Proof.
  intros; red; intros. inv TE.
  exploit H0; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  (*Was: edestruct eval_addressing_lessdef as [vaddr' []]; eauto.*)

  assert (PGR': meminj_preserves_globals ge (restrict (as_inj mu') (vis mu'))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
      apply MU'. apply MU'. 
      intros b Gb. eapply intern_incr_vis. eapply MU'.
         unfold vis. rewrite (Glob _ Gb). intuition. 

  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  edestruct eval_addressing_inject as [vaddr' [? ?]]; try eapply RES1. 
    eapply PGR'.
    eapply restrictI_Some. 
      apply local_in_all; try eapply MU'. eassumption.       
      destruct (local_DomRng _ WD _ _ _ Jsp) as [lS lT].
        eapply intern_incr_vis; try eapply MU'. 
        unfold vis; rewrite lS. trivial.
    eapply H1.
    
  rewrite shift_stack_addressing_zero in H3; simpl in H3.
  edestruct Mem.loadv_inject as [v' []].
    eapply inject_restrict. eapply EXT1. eapply MU'.
    eassumption.
    eassumption. 
  exists (rs1#rd <- v'); exists tm1; exists mu'.
  split. assumption. 
(* Exec *)
  split. eapply effstep_star_trans'. eexact EX1.
    eapply effstep_star_one.
      eapply rtl_effstep_exec_Iload; try eassumption. 
    rewrite (eval_addressing_preserved ge). assumption.
       exact symbols_preserved.
    extensionality b; extensionality z. rewrite absoption_orb; trivial.
(* Match-env *)
  split. eauto with rtlg. 
(* Result *)
  split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto. 
Qed.

Lemma Efftransl_expr_Econdition_correct:
  forall (le : letenv) (a: condexpr) (ifso ifnot : expr)
         (va : bool) (v : val),
  eval_condexpr ge sp e m le a va ->
  Efftransl_condexpr_prop le a va ->
  eval_expr ge sp e m le (if va then ifso else ifnot) v ->
  Efftransl_expr_prop le (if va then ifso else ifnot) v ->
  Efftransl_expr_prop le (Econdition a ifso ifnot) v.
Proof.
  intros; red; intros; inv TE.
  exploit H0; eauto. 
     simpl in OBS. apply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [OTHER1 EXT1]]]]]]].
  assert (tr_expr f.(fn_code) map pr (if va then ifso else ifnot) (if va then ntrue else nfalse) nd rd dst).
    destruct va; auto.
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros b Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
         destruct va; eapply OBS.
     eauto. 
     eauto.
     eassumption. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]]]].
  exists rs2; exists tm2, mu''.
  split. 
    intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_plus_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_plus_fwd. eassumption.
             eapply effstep_star_fwd. eassumption.  
 (* Exec *)
  split. eapply effstep_star_trans'.
           apply effstep_plus_star. eexact EX1. eexact EX2.
    extensionality b; extensionality z. rewrite absoption_orb; trivial.
(* Match-env *)
  split. assumption.
(* Result value *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r); auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Elet_correct:
  forall (le : letenv) (a1 a2 : expr) (v1 v2 : val),
  eval_expr ge sp e m le a1 v1 ->
  Efftransl_expr_prop le a1 v1 ->
  eval_expr ge sp e m (v1 :: le) a2 v2 ->
  Efftransl_expr_prop (v1 :: le) a2 v2 ->
  Efftransl_expr_prop le (Elet a1 a2) v2.
Proof.
  intros; red; intros; inv TE. 
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto.
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1. 
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros b Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
       eapply OBS.
     eauto. 
     eauto.
     eapply match_env_bind_letvar; eauto.
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME3 [RES2 [OTHER2 EXT2]]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_star_fwd. eassumption.
             eapply effstep_star_fwd. eassumption.
(* Exec *)
  split. eapply effstep_star_trans'. eexact EX1. eexact EX2. auto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Result *)
  split. assumption.
(* Other regs *)
  split. intros. transitivity (rs1#r0); auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Eletvar_correct:
  forall (le : list val) (n : nat) (v : val),
  nth_error le n = Some v ->
  Efftransl_expr_prop le (Eletvar n) v.
Proof.
  intros; red; intros; inv TE.
  exploit Efftr_move_correct; eauto. intros [rs1 [EX1 [RES1 OTHER1]]].
  exists rs1; exists tm, mu.
  split. clear H2. intuition. 
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.

      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.      
(* Exec *)
  split. eexact EX1.
(* Match-env *)
  split. 
  destruct H2 as [[A B] | [A B]].
  subst r dst; simpl. 
  apply match_env_invariant with rs. auto.
  intros. destruct (Reg.eq r rd). subst r. auto. auto.
  apply match_env_invariant with (rs#rd <- (rs#r)).
  apply match_env_update_dest; auto.
  eapply match_env_find_letvar; eauto.
  intros. rewrite Regmap.gsspec. destruct (peq r0 rd); auto.
  congruence.
(* Result *)
  split. rewrite RES1. eapply match_env_find_letvar; eauto. 
(* Other regs *)
  split. intros. 
  destruct H2 as [[A B] | [A B]].
  destruct (Reg.eq r0 rd); subst; auto.
  apply OTHER1. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_expr_Ebuiltin_correct:
  forall le ef al vl v,
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  Efftransl_expr_prop le (Ebuiltin ef al) v.
Proof.
  intros; red; intros. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).     
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals; try eassumption.
     unfold vis. intuition. 
  inv TE.
  destruct OBS as [isHLP silExpr].
  exploit H0; eauto. 
  assert (OBS' := EFhelpers _ _ isHLP). 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RR1 [RO1 EXT1]]]]]]]].
  (*WAS: exploit external_call_mem_extends; eauto. 
        intros [v' [tm2 [A [B [C [D E]]]]]].*)
  destruct MU' as [INC [SEP [LOCALLOC' [WD' [SMV' RC']]]]].
  exploit (inlineable_extern_inject _ _ GDE_lemma);
       try eapply RR1; try eapply H1; try eassumption.
     apply symbols_preserved.
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC. 
        rewrite <- FF; apply Glob.
     eapply intern_incr_meminj_preserves_globals_as_inj.
         apply WD. split; assumption. 
     assumption. assumption. 
 (* exploit external_call_mem_inject; eauto. 
        intros [j' [v' [tm2 [A [B [C [D [E [F G]]]]]]]]].*)
   intros [mu'' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD'' [SMV'' RC'']]]]]]]]]]]]].
  exists (rs1#rd <- vres'); exists tm', mu''.
  split. intuition.
    eapply intern_incr_trans. eassumption. eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_star_fwd. eassumption.
             eapply external_call_mem_forward; eassumption.
(* Exec *)
  split. eapply effstep_star_trans'. eexact EX1.
         apply effstep_star_one. eapply rtl_effstep_exec_Ibuiltin; try eassumption. 
         rewrite (helpers_EmptyEffect _ _ _ _ _ isHLP). intuition. 
    (*  eapply external_call_symbols_preserved; eauto. 
        exact symbols_preserved. exact varinfo_preserved.*)
(* Match-env *)
  split. eapply match_env_update_dest; try eassumption.
     eapply match_env_inject_incr; try eassumption.
     apply intern_incr_restrict; eassumption. 
(* Result reg *)
  split. intros. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  assumption. 
Qed.

Lemma Efftransl_expr_Eexternal_correct:
  forall le id sg al b ef vl v,
  Genv.find_symbol ge id = Some b ->
  Genv.find_funct_ptr ge b = Some (External ef) ->
  ef_sig ef = sg ->
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  external_call ef ge vl m E0 v m ->
  Efftransl_expr_prop le (Eexternal id sg al) v.
Proof.
  intros; red; intros. inv TE.
  destruct (silentD_Eexternal _ _ _ _ OBS H H0)
    as [SilentArgs isHLP]; clear OBS.
  exploit H3; eauto.  
  assert (OBS' := EFhelpers _ _ isHLP). 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RR1 [RO1 EXT1]]]]]]]].
  assert (PG': meminj_preserves_globals ge (as_inj mu')).     
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
      apply MU'. apply MU'. 
  destruct MU' as [INC [SEP [LOCALLOC' [WD' [SMV' RC']]]]].
  exploit (inlineable_extern_inject _ _ GDE_lemma);
       try eapply RR1; try eapply H1; try eassumption.
     apply symbols_preserved.
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC. 
        rewrite <- FF; apply Glob.
  intros [mu'' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD'' [SMV'' RC'']]]]]]]]]]]]].
  eexists; exists tm', mu''. 
  split. intuition.
     eapply intern_incr_trans; eassumption.
     eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_star_fwd. eassumption.
     eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_star_fwd. eassumption.
             eapply external_call_mem_forward; eassumption.
  exploit function_ptr_translated; eauto. simpl. intros [tf [P Q]]. inv Q. 
(*  exists (rs1#rd <- vres'); exists tm2.*)
(* Exec *)
  split. eapply effstep_star_trans'. eexact EX1.
    eapply effstep_star_trans'. 
     apply effstep_star_one. eapply rtl_effstep_exec_Icall; eauto.
        simpl. rewrite symbols_preserved. rewrite H. eauto. auto.
    eapply effstep_star_trans'. 
     apply effstep_star_one. eapply rtl_effstep_exec_function_external.
       assumption. eassumption.
     (*  eapply external_call_symbols_preserved; eauto. exact symbols_preserved. exact varinfo_preserved.*)
     apply effstep_star_one. apply rtl_effstep_exec_return. 
     reflexivity. reflexivity.
     simpl in *. rewrite (helpers_EmptyEffect _ _ _ _ _ isHLP). intuition. 
(* Match-env *)
  split. eapply match_env_update_dest; try eassumption.
     eapply match_env_inject_incr; try eassumption.
     apply intern_incr_restrict; eassumption. 
(* Result reg *)
   split. rewrite Regmap.gss. auto.
(* Other regs *)
  split. intros. rewrite Regmap.gso. auto. intuition congruence.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_exprlist_Enil_correct:
  forall (le : letenv),
  Efftransl_exprlist_prop le Enil nil.
Proof.
  intros; red; intros; inv TE.
  exists rs; exists tm, mu.
  split. intuition. 
      apply intern_incr_refl.
      apply sm_inject_separated_same_sminj.

      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition. 
  split. apply effstep_star_zero.
  split. assumption.
  split. constructor.
  auto.
Qed.

Lemma Efftransl_exprlist_Econs_correct:
  forall (le : letenv) (a1 : expr) (al : exprlist) (v1 : val)
         (vl : list val),
  eval_expr ge sp e m le a1 v1 ->
  Efftransl_expr_prop le a1 v1 ->
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  Efftransl_exprlist_prop le (Econs a1 al) (v1 :: vl).
Proof.
  intros; red; intros; inv TE.
  simpl in OBS. destruct OBS as [silentA silentAL].
  exploit H0; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1.
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros b Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
     eapply silentAL.
     eauto. 
     eauto.
     eassumption. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME2 [RES2 [OTHER2 EXT2]]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_star_fwd. eassumption.
             eapply effstep_star_fwd. eassumption.
(* Exec *)
  split. eapply effstep_star_trans'. eexact EX1. eexact EX2. auto. 
(* Match-env *)
  split. assumption.
(* Results *)
  split. simpl. constructor. rewrite OTHER2. 
     eapply val_inject_incr; try eassumption. 
     eapply intern_incr_restrict. eapply MU''. eapply MU''.
    simpl; tauto.
  auto.
(* Other regs *)
  split. intros. transitivity (rs1#r).
  apply OTHER2; auto. simpl; tauto. 
  apply OTHER1; auto.
(* Mem *)
  auto.
Qed.

Lemma Efftransl_condexpr_CEcond_correct:
  forall le cond al vl vb,
  eval_exprlist ge sp e m le al vl ->
  Efftransl_exprlist_prop le al vl ->
  eval_condition cond vl m = Some vb ->
  Efftransl_condexpr_prop le (CEcond cond al) vb.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. 
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  exists rs1; exists tm1, mu'.
  split. assumption.
(* Exec *)
  split. eapply effstep_star_plus_trans'. eexact EX1.
      eapply effstep_plus_one.
        eapply rtl_effstep_exec_Icond. eauto. 
      (*eapply eval_condition_lessdef; eauto.*)
    eapply eval_condition_inject; eauto. 
    eapply inject_restrict; eauto.
     eapply MU'.
    auto.
    eauto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. assumption. 
(* Mem *)
  auto.
Qed.

Lemma Efftransl_condexpr_CEcondition_correct:
  forall le a b c va v,
  eval_condexpr ge sp e m le a va ->
  Efftransl_condexpr_prop le a va ->
  eval_condexpr ge sp e m le (if va then b else c) v ->
  Efftransl_condexpr_prop le (if va then b else c) v ->
  Efftransl_condexpr_prop le (CEcondition a b c) v.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [OTHER1 EXT1]]]]]]].
  assert (tr_condition (fn_code f) map pr (if va then b else c) (if va then n2 else n3) ntrue nfalse).
    destruct va; auto.
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1.
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros bb Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb). 
       destruct va; eapply OBS.
     eauto. 
     eauto.
     eassumption. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME2 [OTHER2 EXT2]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_plus_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_plus_fwd. eassumption.
             eapply effstep_plus_fwd. eassumption.
(* Exec *)
  split. eapply effstep_plus_trans'. eexact EX1. eexact EX2. eauto.
(* Match-env *)
  split. assumption.
(* Other regs *)
  split. intros. rewrite OTHER2; auto. 
(* Mem *)
  auto.
Qed.

Lemma Efftransl_condexpr_CElet_correct:
  forall le a b v1 v2,
  eval_expr ge sp e m le a v1 ->
  Efftransl_expr_prop le a v1 ->
  eval_condexpr ge sp e m (v1 :: le) b v2 ->
  Efftransl_condexpr_prop (v1 :: le) b v2 ->
  Efftransl_condexpr_prop le (CElet a b) v2.
Proof.
  intros; red; intros. inv TE. 
  exploit H0; eauto. eapply OBS.
  intros [rs1 [tm1 [mu' [MU' [EX1 [ME1 [RES1 [OTHER1 EXT1]]]]]]]].
  assert (map_wf (add_letvar map r)).
    eapply add_letvar_wf; eauto. 
  destruct SP as [spb [spb' [SP [SP' Jsp]]]]. subst sp sp'.
  exploit H2; try eapply EXT1.
       eapply intern_incr_meminj_preserves_globals_as_inj.
         eassumption. split; assumption. 
       eapply MU'. eapply MU'.
       { red. exists spb, spb'. split. eassumption. 
           split. reflexivity. 
           eapply MU'. eassumption. }
       eapply MU'. eapply MU'. eapply MU'. 
       intros bb Gb. 
         assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply MU'.  
         rewrite <- FRG. apply (Glob _ Gb).
       eapply OBS. 
     eauto. 
     eauto.
     eapply match_env_bind_letvar; eauto. 
  intros [rs2 [tm2 [mu'' [MU'' [EX2 [ME3 [OTHER2 EXT2]]]]]]].
  exists rs2; exists tm2, mu''.
  split. intuition.
    eapply intern_incr_trans; eassumption. 
    eapply inject_separated_intern_incr_fwd; try eassumption. 
           eapply effstep_star_fwd. eassumption.
    eapply sm_locally_allocated_trans; try eassumption. 
             apply mem_forward_refl. 
             apply mem_forward_refl.
             eapply effstep_star_fwd. eassumption.
             eapply effstep_plus_fwd. eassumption.
(* Exec *)
  split. eapply effstep_star_plus_trans'. 
    eexact EX1. eexact EX2. eauto.
(* Match-env *)
  split. eapply match_env_unbind_letvar; eauto.
(* Other regs *)
  split. intros. rewrite OTHER2; auto. 
(* Mem *)
  auto.
Qed.

Theorem Efftransl_expr_correct:
  forall le a v,
  eval_expr ge sp e m le a v ->
  Efftransl_expr_prop le a v.
Proof
  (eval_expr_ind3 ge sp e m
     Efftransl_expr_prop
     Efftransl_exprlist_prop
     Efftransl_condexpr_prop
     Efftransl_expr_Evar_correct
     Efftransl_expr_Eop_correct
     Efftransl_expr_Eload_correct
     Efftransl_expr_Econdition_correct
     Efftransl_expr_Elet_correct
     Efftransl_expr_Eletvar_correct
     Efftransl_expr_Ebuiltin_correct
     Efftransl_expr_Eexternal_correct
     Efftransl_exprlist_Enil_correct
     Efftransl_exprlist_Econs_correct
     Efftransl_condexpr_CEcond_correct
     Efftransl_condexpr_CEcondition_correct
     Efftransl_condexpr_CElet_correct).

Theorem Efftransl_exprlist_correct:
  forall le a v,
  eval_exprlist ge sp e m le a v ->
  Efftransl_exprlist_prop le a v.
Proof
  (eval_exprlist_ind3 ge sp e m
     Efftransl_expr_prop
     Efftransl_exprlist_prop
     Efftransl_condexpr_prop
     Efftransl_expr_Evar_correct
     Efftransl_expr_Eop_correct
     Efftransl_expr_Eload_correct
     Efftransl_expr_Econdition_correct
     Efftransl_expr_Elet_correct
     Efftransl_expr_Eletvar_correct
     Efftransl_expr_Ebuiltin_correct 
     Efftransl_expr_Eexternal_correct
     Efftransl_exprlist_Enil_correct
     Efftransl_exprlist_Econs_correct
     Efftransl_condexpr_CEcond_correct
     Efftransl_condexpr_CEcondition_correct
     Efftransl_condexpr_CElet_correct).

Theorem Efftransl_condexpr_correct:
  forall le a v,
  eval_condexpr ge sp e m le a v ->
  Efftransl_condexpr_prop le a v.
Proof
  (eval_condexpr_ind3 ge sp e m
     Efftransl_expr_prop
     Efftransl_exprlist_prop
     Efftransl_condexpr_prop
     Efftransl_expr_Evar_correct
     Efftransl_expr_Eop_correct
     Efftransl_expr_Eload_correct
     Efftransl_expr_Econdition_correct
     Efftransl_expr_Elet_correct
     Efftransl_expr_Eletvar_correct
     Efftransl_expr_Ebuiltin_correct
     Efftransl_expr_Eexternal_correct
     Efftransl_exprlist_Enil_correct
     Efftransl_exprlist_Econs_correct
     Efftransl_condexpr_CEcond_correct
     Efftransl_condexpr_CEcondition_correct
     Efftransl_condexpr_CElet_correct).

End CORRECTNESS_EXPR_EFF.

(** ** Measure over CminorSel states *)

Open Local Scope nat_scope.

Fixpoint size_stmt (s: stmt) : nat :=
  match s with
  | Sskip => 0
  | Sseq s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sifthenelse c s1 s2 => (size_stmt s1 + size_stmt s2 + 1)
  | Sloop s1 => (size_stmt s1 + 1)
  | Sblock s1 => (size_stmt s1 + 1)
  | Sexit n => 0
  | Slabel lbl s1 => (size_stmt s1 + 1)
  | _ => 1
  end.

Fixpoint size_cont (k: cont) : nat :=
  match k with
  | Kseq s k1 => (size_stmt s + size_cont k1 + 1)
  | Kblock k1 => (size_cont k1 + 1)
  | _ => 0%nat
  end.

Definition measure_state (S: CMinSel_core) :=
  match S with
  | CMinSel_State _ s k _ _ => (size_stmt s + size_cont k, size_stmt s)
  | _                           => (0, 0)
  end.

Definition lt_state (S1 S2: CMinSel_core) :=
  lex_ord lt lt (measure_state S1) (measure_state S2).

Lemma lt_state_intro:
  forall f1 s1 k1 sp1 e1 f2 s2 k2 sp2 e2,
  size_stmt s1 + size_cont k1 < size_stmt s2 + size_cont k2
  \/ (size_stmt s1 + size_cont k1 = size_stmt s2 + size_cont k2
      /\ size_stmt s1 < size_stmt s2) ->
  lt_state (CMinSel_State f1 s1 k1 sp1 e1)
           (CMinSel_State f2 s2 k2 sp2 e2).
Proof.
  intros. unfold lt_state. simpl. destruct H as [A | [A B]].
  left. auto.
  rewrite A. right. auto.
Qed.

Ltac Lt_state :=
  apply lt_state_intro; simpl; try omega.

Require Import Wellfounded.

Lemma lt_state_wf:
  well_founded lt_state.
Proof.
  unfold lt_state. apply wf_inverse_image with (f := measure_state).
  apply wf_lex_ord. apply lt_wf. apply lt_wf. 
Qed.

(** ** Semantic preservation for the translation of statements *)   

(** The simulation diagram for the translation of statements
  and functions is a "star" diagram of the form:
<<
           I                         I
     S1 ------- R1             S1 ------- R1
     |          |              |          |
   t |        + | t      or  t |        * | t    and |S2| < |S1|
     v          v              v          |
     S2 ------- R2             S2 ------- R2
           I                         I
>>
  where [I] is the [match_states] predicate defined below.  It includes:
- Agreement between the Cminor statement under consideration and
  the current program point in the RTL control-flow graph,
  as captured by the [tr_stmt] predicate.
- Agreement between the Cminor continuation and the RTL control-flow
  graph and call stack, as captured by the [tr_cont] predicate below.
- Agreement between Cminor environments and RTL register environments,
  as captured by [match_envs].

*)

Inductive tr_fun (tf: function) (map: mapping) (f: CminorSel.function)
                     (ngoto: labelmap) (nret: node) (rret: option reg) : Prop :=
  | tr_fun_intro: forall nentry r,
      rret = ret_reg f.(CminorSel.fn_sig) r ->
      tr_stmt tf.(fn_code) map f.(fn_body) nentry nret nil ngoto nret rret ->
      tf.(fn_stacksize) = f.(fn_stackspace) ->
      tr_fun tf map f ngoto nret rret.

(*LENB: new: meminj parameter mu*)
Inductive tr_cont mu: RTL.code -> mapping -> 
                   CminorSel.cont -> node -> list node -> labelmap -> node -> option reg ->
                   list RTL.stackframe -> Prop :=
  | tr_Kseq: forall c map s k nd nexits ngoto nret rret cs n,
      tr_stmt c map s nd n nexits ngoto nret rret ->
      tr_cont mu c map k n nexits ngoto nret rret cs ->
      tr_cont mu c map (Kseq s k) nd nexits ngoto nret rret cs
  | tr_Kblock: forall c map k nd nexits ngoto nret rret cs,
      tr_cont mu c map k nd nexits ngoto nret rret cs ->
      tr_cont mu c map (Kblock k) nd (nd :: nexits) ngoto nret rret cs
  | tr_Kstop: forall c map ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks mu Kstop cs ->
      tr_cont mu c map Kstop nret nil ngoto nret rret cs
  | tr_Kcall: forall c map optid f sp e k ngoto nret rret cs,
      c!nret = Some(Ireturn rret) ->
      match_stacks mu (Kcall optid f sp e k) cs ->
      tr_cont mu c map (Kcall optid f sp e k) nret nil ngoto nret rret cs

with match_stacks mu : CminorSel.cont -> list RTL.stackframe -> Prop :=
  | match_stacks_stop:
      match_stacks mu Kstop nil
  | match_stacks_call: forall optid f sp e k r tf n rs cs map nexits ngoto nret rret sp',
      map_wf map ->
      tr_fun tf map f ngoto nret rret ->
      match_env (as_inj mu) map e nil rs ->
      reg_map_ok map r optid ->
      tr_cont mu tf.(fn_code) map k n nexits ngoto nret rret cs ->
      (*NEW:*) sp_preserved (local_of mu) sp sp' ->
      match_stacks mu (Kcall optid f sp e k) (Stackframe r tf sp' n rs :: cs).

(*Derivation of induction scheme as explained her:
http://coq.inria.fr/cocorico/Mutual%20Induction*)
Scheme tr_cont_ind_2 := Induction for tr_cont Sort Prop
  with match_stacks_ind_2 := Induction for match_stacks Sort Prop.
Combined Scheme tr_cont_match_stacks_mutual_ind
  from tr_cont_ind_2, match_stacks_ind_2.

Lemma tr_cont_match_stacks_intern_incr: 
      forall mu mu' (WD': SM_wd mu') (INC: intern_incr mu mu'),
      (forall c map k ncont nexits ngoto nret rret cs,
         tr_cont mu c map k ncont nexits ngoto nret rret cs -> 
         tr_cont mu' c map k ncont nexits ngoto nret rret cs) /\
       (forall k cs, match_stacks mu k cs -> match_stacks mu' k cs).
Proof. intros. apply tr_cont_match_stacks_mutual_ind; intros.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; try eassumption. 
     eapply match_env_inject_incr; try eassumption.
       apply intern_incr_as_inj; trivial. 
     eapply sp_incr; eauto. eapply INC.
Qed.

Lemma tr_cont_intern_incr: 
      forall mu c map k ncont nexits ngoto nret rret cs
        (TR: tr_cont mu c map k ncont nexits ngoto nret rret cs)
        mu' (WD': SM_wd mu') (INC: intern_incr mu mu'),
      tr_cont mu' c map k ncont nexits ngoto nret rret cs.
Proof. intros. 
       eapply tr_cont_match_stacks_intern_incr; try eassumption.
Qed.
Lemma match_stacks_intern_incr: 
      forall mu k cs (MS:match_stacks mu k cs) 
             mu' (WD': SM_wd mu') (INC: intern_incr mu mu'), 
      match_stacks mu' k cs.
Proof. intros. 
       eapply tr_cont_match_stacks_intern_incr; try eassumption. 
Qed. 

Lemma tr_cont_match_stacks_replace_locals: 
      forall mu pubSrc' pubTgt' (WD: SM_wd mu)
      (WD': SM_wd (replace_locals mu pubSrc' pubTgt')), 
      (forall c map k ncont nexits ngoto nret rret cs,
         tr_cont (restrict_sm mu (vis mu)) 
                 c map k ncont nexits ngoto nret rret cs -> 
         tr_cont (restrict_sm (replace_locals mu pubSrc' pubTgt') (vis mu))
                 c map k ncont nexits ngoto nret rret cs) /\
       (forall k cs, match_stacks (restrict_sm mu (vis mu)) k cs ->
                     match_stacks (restrict_sm (replace_locals mu pubSrc' pubTgt') (vis mu)) k cs).
Proof. intros. apply tr_cont_match_stacks_mutual_ind; intros.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; try eassumption.
     rewrite restrict_sm_all in *. 
     rewrite replace_locals_as_inj. assumption.
     rewrite restrict_sm_local' in *; trivial.
      rewrite replace_locals_local; trivial.
     rewrite replace_locals_vis. trivial.
Qed.

Lemma tr_cont_replace_locals: 
      forall mu c map k ncont nexits ngoto nret rret cs
        (TR: tr_cont (restrict_sm mu (vis mu)) c map k ncont nexits ngoto nret rret cs)
        pubSrc' pubTgt' (WD: SM_wd mu)
        (WD': SM_wd (replace_locals mu pubSrc' pubTgt')),
      tr_cont (restrict_sm (replace_locals mu pubSrc' pubTgt') (vis mu)) c map k ncont nexits ngoto nret rret cs.
Proof. intros. 
       eapply tr_cont_match_stacks_replace_locals; try eassumption.
Qed.
Lemma match_stacks_replace_locals: 
      forall mu k cs (MS:match_stacks (restrict_sm mu (vis mu)) k cs) 
        pubSrc' pubTgt' (WD: SM_wd mu)
        (WD': SM_wd (replace_locals mu  pubSrc' pubTgt')),
      match_stacks (restrict_sm (replace_locals mu pubSrc' pubTgt') (vis mu)) k cs.
Proof. intros. 
       eapply tr_cont_match_stacks_replace_locals; try eassumption. 
Qed. 

Lemma tr_cont_match_stacks_extern_incr: 
      forall mu mu' (WD': SM_wd mu') (INC: extern_incr mu mu'),
      (forall c map k ncont nexits ngoto nret rret cs,
         tr_cont mu c map k ncont nexits ngoto nret rret cs -> 
         tr_cont mu' c map k ncont nexits ngoto nret rret cs) /\
       (forall k cs, match_stacks mu k cs -> match_stacks mu' k cs).
Proof. intros. apply tr_cont_match_stacks_mutual_ind; intros.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; try eassumption. 
     eapply match_env_inject_incr; try eassumption.
       apply extern_incr_as_inj; trivial. 
     assert (local_of mu = local_of mu') by eapply INC.
     rewrite <- H0; trivial.
Qed.

Lemma tr_cont_extern_incr: 
      forall mu c map k ncont nexits ngoto nret rret cs
        (TR: tr_cont mu c map k ncont nexits ngoto nret rret cs)
        mu' (WD': SM_wd mu') (INC: extern_incr mu mu'),
      tr_cont mu' c map k ncont nexits ngoto nret rret cs.
Proof. intros. 
       eapply tr_cont_match_stacks_extern_incr; try eassumption.
Qed.
Lemma match_stacks_extern_incr: 
      forall mu k cs (MS:match_stacks mu k cs) 
             mu' (WD': SM_wd mu') (INC: extern_incr mu mu'), 
      match_stacks mu' k cs.
Proof. intros. 
       eapply tr_cont_match_stacks_extern_incr; try eassumption. 
Qed. 

(*Lemma tr_cont_match_stacks_replace_externs: 
      forall mu FS FT 
      (HFS: forall b, vis mu b = true -> 
          locBlocksSrc mu b || FS b = true),
      (forall c map k ncont nexits ngoto nret rret cs,
         tr_cont (restrict_sm mu (vis mu)) 
                 c map k ncont nexits ngoto nret rret cs -> 
         tr_cont (restrict_sm (replace_externs mu FS FT) FS)
                 c map k ncont nexits ngoto nret rret cs) /\
       (forall k cs, match_stacks (restrict_sm mu (vis mu)) k cs ->
                     match_stacks (restrict_sm (replace_externs mu FS FT) FS) k cs).
Proof. intros. apply tr_cont_match_stacks_mutual_ind; intros.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; try eassumption.
    rewrite restrict_sm_all in *.
    rewrite replace_externs_as_inj; trivial.
      eapply match_env_inject_incr; try eassumption.
      red; intros. destruct (restrictD_Some _ _ _ _ _ H0).
      apply restrictI_Some; trivial.
      apply 
    rewrite restrict_sm_local in *; trivial.
    rewrite replace_externs_local; trivial.
    eapply sp_incr. eassumption.
      red; intros. destruct (restrictD_Some _ _ _ _ _ H0).
      apply restrictI_Some; eauto.
Qed.

Lemma tr_cont_replace_externs mu FS FT:
      forall c map k ncont nexits ngoto nret rret cs
         (TR: tr_cont (restrict_sm mu (vis mu)) 
                 c map k ncont nexits ngoto nret rret cs)
         (HFS: forall b, vis mu b = true -> FS b = true),
         tr_cont (restrict_sm (replace_externs mu FS FT) FS)
                 c map k ncont nexits ngoto nret rret cs.
Proof. intros. 
       eapply tr_cont_match_stacks_replace_externs; try eassumption.
Qed.
Lemma match_stacks_replace_externs mu FS FT k cs: forall
       (MS: match_stacks (restrict_sm mu (vis mu)) k cs)
       (HFS: forall b, vis mu b = true -> FS b = true),
       match_stacks (restrict_sm (replace_externs mu FS FT) FS) 
                     k cs.
Proof. intros. 
       eapply tr_cont_match_stacks_replace_externs; try eassumption. 
Qed. 
*)

Lemma tr_cont_match_stacks_replace_externs: 
      forall mu FS FT 
      (HFS: forall b, vis mu b = true -> 
          locBlocksSrc mu b || FS b = true),
      (forall c map k ncont nexits ngoto nret rret cs,
         tr_cont  mu c map k ncont nexits ngoto nret rret cs -> 
         tr_cont (replace_externs mu FS FT)
                 c map k ncont nexits ngoto nret rret cs) /\
       (forall k cs, match_stacks mu k cs ->
                     match_stacks (replace_externs mu FS FT) k cs).
Proof. intros. apply tr_cont_match_stacks_mutual_ind; intros.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; eassumption.
  econstructor; try eassumption.
    rewrite replace_externs_as_inj; trivial.
    rewrite replace_externs_local; trivial.
Qed.

Lemma tr_cont_replace_externs mu FS FT:
      forall c map k ncont nexits ngoto nret rret cs
         (TR: tr_cont mu c map k ncont nexits ngoto nret rret cs)
         (HFS: forall b, vis mu b = true -> 
               locBlocksSrc mu b || FS b = true),
         tr_cont (replace_externs mu FS FT)
                 c map k ncont nexits ngoto nret rret cs.
Proof. intros. 
       eapply tr_cont_match_stacks_replace_externs; try eassumption.
Qed.
Lemma match_stacks_replace_externs mu FS FT k cs: forall
       (MS: match_stacks mu k cs)
         (HFS: forall b, vis mu b = true -> 
               locBlocksSrc mu b || FS b = true),
       match_stacks (replace_externs mu FS FT) k cs.
Proof. intros. 
       eapply tr_cont_match_stacks_replace_externs; try eassumption. 
Qed. 

Inductive match_states mu: CMinSel_core -> mem -> RTL_core -> mem -> Prop :=
  | match_state:
      forall f s k sp e m tm cs tf ns rs map ncont nexits ngoto nret rret sp'
        (MWF: map_wf map)
        (TS: tr_stmt tf.(fn_code) map s ns ncont nexits ngoto nret rret)
        (TF: tr_fun tf map f ngoto nret rret)
        (TK: tr_cont mu tf.(fn_code) map k ncont nexits ngoto nret rret cs)
        (ME: match_env (as_inj mu) map e nil rs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject (as_inj mu) m tm)
        (*NEW:*) (SP: sp_preserved (local_of mu) sp sp'),
      match_states mu (CMinSel_State f s k sp e) m
                     (RTL_State cs tf sp' ns rs) tm
  | match_callstate:
      forall f args targs k m tm cs tf
        (TF: transl_fundef f = OK tf)
        (MS: match_stacks (restrict_sm mu (vis mu)) k cs)
        (*(LD: Val.lessdef_list args targs)*)
        (AINJ: val_list_inject (restrict (as_inj mu) (vis mu)) args targs)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject (as_inj mu) m tm),
      match_states mu (CMinSel_Callstate f args k) m
                     (RTL_Callstate cs tf targs) tm
  | match_returnstate:
      forall v tv k m tm cs
        (MS: match_stacks (restrict_sm mu (vis mu)) k cs)
        (*(LD: Val.lessdef v tv)*)
         (VINJ: val_inject (restrict (as_inj mu) (vis mu)) v tv)
        (*(MEXT: Mem.extends m tm)*)
        (MINJ: Mem.inject (as_inj mu) m tm),
      match_states mu (CMinSel_Returnstate v k) m
                     (RTL_Returnstate cs tv) tm.


Lemma match_stacks_call_cont:
  forall mu c map k ncont nexits ngoto nret rret cs,
  tr_cont mu c map k ncont nexits ngoto nret rret cs ->
  match_stacks mu (call_cont k) cs /\ c!nret = Some(Ireturn rret).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma tr_cont_call_cont:
  forall mu c map k ncont nexits ngoto nret rret cs,
  tr_cont mu c map k ncont nexits ngoto nret rret cs ->
  tr_cont mu c map (call_cont k) nret nil ngoto nret rret cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma tr_find_label:
  forall mu c map lbl n (ngoto: labelmap) nret rret s' k' cs,
  ngoto!lbl = Some n ->
  forall s k ns1 nd1 nexits1,
  find_label lbl s k = Some (s', k') ->
  tr_stmt c map s ns1 nd1 nexits1 ngoto nret rret ->
  tr_cont mu c map k nd1 nexits1 ngoto nret rret cs ->
  exists ns2, exists nd2, exists nexits2,
     c!n = Some(Inop ns2)
  /\ tr_stmt c map s' ns2 nd2 nexits2 ngoto nret rret
  /\ tr_cont mu c map k' nd2 nexits2 ngoto nret rret cs.
Proof.
  induction s; intros until nexits1; simpl; try congruence.
  (* seq *)
  caseEq (find_label lbl s1 (Kseq s2 k)); intros.
  inv H1. inv H2. eapply IHs1; eauto. econstructor; eauto.
  inv H2. eapply IHs2; eauto. 
  (* ifthenelse *)
  caseEq (find_label lbl s1 k); intros.
  inv H1. inv H2. eapply IHs1; eauto.
  inv H2. eapply IHs2; eauto.
  (* loop *)
  intros. inversion H1; subst.
  eapply IHs; eauto. econstructor; eauto. econstructor; eauto.
  (* block *)
  intros. inv H1.
  eapply IHs; eauto. econstructor; eauto.
  (* label *)
  destruct (ident_eq lbl l); intros.
  inv H0. inv H1.
  assert (n0 = n). change positive with node in H4. congruence. subst n0.
  exists ns1; exists nd1; exists nexits1; auto.
  inv H1. eapply IHs; eauto.
Qed.

Definition MATCH (d:CMinSel_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict_sm mu (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu /\ Mem.inject (as_inj mu) m1 m2.

Lemma MATCH_wd: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma MATCH_restrict: forall d mu c1 m1 c2 m2 X
  (MC: MATCH d mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m1 X), 
  MATCH d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  rewrite vis_restrict_sm.
(*  rewrite restrict_sm_all.*)
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
(*split. *) rewrite restrict_sm_all.
  eapply inject_restrict; try eassumption.
(*rewrite restrict_sm_DomTgt. trivial.*)
Qed.

Lemma MATCH_valid: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
Proof. intros. eapply MC. Qed.

Lemma MATCH_PG: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2),
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

Lemma MATCH_initial: forall v
      vals1 c1 m1 j vals2 m2 (DomS DomT : block -> bool)
      (Ini: initial_core (cminsel_eff_sem hf) ge v vals1 = Some c1)
      (Inj: Mem.inject j m1 m2)
      (VInj: Forall2 (val_inject j) vals1 vals2)
      (PG:meminj_preserves_globals ge j)
      (J: forall b1 b2 delta, j b1 = Some (b2, delta) -> 
            (DomS b1 = true /\ DomT b2 = true))
      (RCH: forall b, REACH m2 
          (fun b' : block => isGlobalBlock tge b' || getBlocks vals2 b') b = true ->
          DomT b = true)
      (GFI: globalfunction_ptr_inject ge j)
      (GDE: genvs_domain_eq ge tge)
      (HDomS: forall b : block, DomS b = true -> Mem.valid_block m1 b)
      (HDomT: forall b : block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core (rtl_eff_sem hf) tge v vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1 (fun b : block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2 (fun b : block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof. intros.
  inversion Ini.
  unfold CMinSel_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  simpl; revert H1; case_eq 
    (zlt (match match Zlength vals1 with 0%Z => 0%Z
                      | Z.pos y' => Z.pos y'~0 | Z.neg y' => Z.neg y'~0
                     end
               with 0%Z => 0%Z
                 | Z.pos y' => Z.pos y'~0~0 | Z.neg y' => Z.neg y'~0~0
               end) Int.max_unsigned).
  intros l _.
  2: solve[simpl; rewrite andb_comm; inversion 2].

  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  exists (RTL_Callstate nil tf vals2).
  split.
    subst. inv Heqzz. unfold tge in FP. inv FP. rewrite H2.
    unfold cminsel_eff_sem, cminsel_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.

  assert (Zlength vals2 = Zlength vals1) as ->. 
  { apply forall_inject_val_list_inject in VInj. clear - VInj. 
    induction VInj; auto. rewrite !Zlength_cons, IHVInj; auto. }

  assert (val_casted.val_has_type_list_func vals2
           (sig_args (funsig tf))=true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H1; simpl in H1. 
    solve[rewrite andb_comm in H1; inv H1].
    assert (sig_args (funsig tf)
          = sig_args (CminorSel.funsig (Internal f))) as ->.
    { erewrite sig_transl_function; eauto. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (CminorSel.funsig (Internal f)))); auto. inv H1. }
  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite <-andb_assoc, andb_comm in H1; inv H1. }
  monadInv TF. rename x into tf.
  simpl; revert H1; case_eq 
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
    revert H1.
    destruct (val_casted.val_has_type_list_func vals1
             (sig_args (CminorSel.funsig (Internal f))) && val_casted.vals_defined vals1); 
      try solve[inversion 1]. 
    inversion 1; subst. clear H1.
    eapply match_callstate; try eassumption.
      constructor.
      rewrite restrict_sm_all, restrict_nest.
      rewrite initial_SM_as_inj.
        unfold vis, initial_SM; simpl.
        apply forall_inject_val_list_inject.
        eapply restrict_forall_vals_inject; try eassumption.
          intros. apply REACH_nil. rewrite H; intuition.
    rewrite vis_restrict_sm. 
      unfold vis, initial_SM; simpl. trivial.
    rewrite restrict_sm_all, initial_SM_as_inj.
      unfold vis, initial_SM; simpl. 
      eapply inject_restrict; try eassumption.
  intuition.
    rewrite match_genv_meminj_preserves_extern_iff_all.
      assumption.
      apply BB.
      apply EE.
    (*as in selectionproofEFF*)
    rewrite initial_SM_as_inj; auto.
    rewrite initial_SM_as_inj; assumption.
Qed.

Lemma MATCH_atExternal: forall mu c1 m1 c2 m2 e vals1 ef_sig
       (MTCH: MATCH c1 mu c1 m1 c2 m2)
       (AtExtSrc: at_external (cminsel_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
     Mem.inject (as_inj mu) m1 m2 /\
     exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
       at_external (rtl_eff_sem hf) c2 = Some (e, ef_sig, vals2) /\
      (forall pubSrc' pubTgt',
       pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
       pubTgt' = (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
       forall nu : SM_Injection, nu = replace_locals mu pubSrc' pubTgt' ->
       MATCH c1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2).
Proof. intros.
destruct MTCH as [MC [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
inv MC; simpl in AtExtSrc; inv AtExtSrc.
destruct f; simpl in *; inv H0.
inv TF.
destruct (observableEF_dec hf e0); inv H1.
split; trivial.
rewrite vis_restrict_sm, restrict_sm_all, restrict_nest in AINJ; trivial.
exploit val_list_inject_forall_inject; try eassumption. intros ARGS'.
exists targs.
split; trivial.
split; trivial.
specialize (forall_vals_inject_restrictD _ _ _ _ ARGS'); intros.
exploit replace_locals_wd_AtExternal; try eassumption. 
intuition. 
(*MATCH*)
    split; subst; rewrite replace_locals_vis. 
      econstructor; eauto. 
       rewrite restrict_sm_nest, vis_restrict_sm in *. 
         rewrite replace_locals_vis. 
         eapply match_stacks_replace_locals; eassumption.
         rewrite vis_restrict_sm; trivial.
       rewrite vis_restrict_sm, replace_locals_vis; trivial.
       rewrite vis_restrict_sm; trivial. 
       rewrite vis_restrict_sm, restrict_sm_all,
         restrict_nest; trivial. 
         rewrite replace_locals_as_inj, replace_locals_vis; trivial.
       rewrite replace_locals_vis; trivial.
       rewrite restrict_sm_all in *.
         rewrite replace_locals_as_inj. trivial.
    subst. rewrite replace_locals_frgnBlocksSrc, replace_locals_as_inj in *.
           intuition.
   (*sm_valid*)
     red. rewrite replace_locals_DOM, replace_locals_RNG. apply SMV.
(*Shared*)
  eapply inject_shared_replace_locals; try eassumption.
  subst; trivial.
Qed.

Lemma MATCH_afterExternal: forall
      (GDE : genvs_domain_eq ge tge)
      mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH st1 mu st1 m1 st2 m2)
      (AtExtSrc : at_external (cminsel_eff_sem hf) st1 = Some (e, ef_sig, vals1))
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
       (SEP : globals_separate tge nu nu')
       (*SEP: sm_inject_separated nu nu' m1 m2*)
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
  after_external (cminsel_eff_sem hf) (Some ret1) st1 =Some st1' /\
  after_external (rtl_eff_sem hf) (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros.
simpl.
 destruct MatchMu as [MC [RC [PG [GFP [Glob [VAL [WDmu INJ]]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H0. 
 destruct tf; inv AtExtTgt.
 inv TF.
 destruct (observableEF_dec hf e1); inv H0; inv H1.
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
       assert (PGnu': meminj_preserves_globals (Genv.globalenv prog) (as_inj nu')).
       eapply meminj_preserves_globals_extern_incr_separate. eassumption.
       rewrite replace_locals_as_inj. assumption.
       assumption. 
       specialize (genvs_domain_eq_isGlobal _ _ GDE_lemma). intros GL.
       red. unfold ge in GL. rewrite GL. apply SEP.

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
rewrite restrict_sm_nest, vis_restrict_sm in *; trivial. 
2: rewrite vis_restrict_sm; trivial.
split. rewrite replace_externs_vis.
{ (* MATCH*)
  rewrite restrict_sm_all in *.
  econstructor. 
  Focus 2. rewrite vis_restrict_sm, restrict_sm_all,
            replace_externs_vis, replace_externs_as_inj,
            restrict_nest; trivial.
          clear - RValInjNu' WDnu'.
          inv RValInjNu'; econstructor; eauto.
          apply restrictI_Some; trivial.
          destruct (locBlocksSrc nu' b1); simpl; trivial.
          destruct (as_inj_DomRng _ _ _ _ H WDnu') as [dS dT].
          rewrite dS; simpl.
          apply REACH_nil. unfold exportedSrc.
          apply orb_true_iff; left.
          apply getBlocks_char. exists ofs1; left; eauto.
  Focus 2. rewrite restrict_sm_all, replace_externs_as_inj.
    eapply inject_restrict; try eassumption.
  rewrite vis_restrict_sm, replace_externs_vis.
  rewrite restrict_sm_nest; trivial. 
  rewrite <- restrict_sm_replace_externs in *.
   eapply match_stacks_replace_externs.
    eapply match_stacks_extern_incr.
      eapply match_stacks_replace_locals; try eassumption. 
       instantiate (2:=fun b => locBlocksSrc mu b &&
                         REACH m1 (exportedSrc mu vals1) b).
       instantiate (1:=fun b => locBlocksTgt mu b && 
                         REACH m2 (exportedTgt mu vals2) b).
       apply replace_locals_wd; try eassumption.
       intros. rewrite andb_true_iff in H. destruct H as [HH1 HH2]. 
       exploit REACH_local_REACH; try apply HH2. 
          eassumption. eassumption. 
          rewrite restrict_nest in AINJ; trivial. 
          eapply val_list_inject_forall_inject. 
          eapply val_list_inject_incr; try eassumption.
          apply restrict_incr.
          assumption.
      intros [b2 [d [LOC RCH2]]]. exists b2, d; rewrite LOC, RCH2.
        destruct (local_DomRng _ WDmu _ _ _ LOC) as [_ lT]; intuition.
      intros. rewrite andb_true_iff in H. destruct H; trivial.
      eapply restrict_sm_WD; try eassumption. 
      intros. unfold vis in H.
        destruct (locBlocksSrc nu' b); simpl in *; trivial. 
        apply andb_true_iff; split. 
         unfold DomSrc.
           rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H).
           intuition.
         apply REACH_nil. unfold exportedSrc.
           rewrite sharedSrc_iff_frgnpub, H. intuition. trivial.
      clear - INC WDmu WDnu'.  
      red in INC; red.    
          repeat rewrite restrict_sm_extern, restrict_sm_local, 
                  restrict_sm_extBlocksSrc, restrict_sm_extBlocksTgt,
                  restrict_sm_locBlocksSrc, restrict_sm_locBlocksTgt,
                  restrict_sm_pubBlocksSrc, restrict_sm_pubBlocksTgt,
                  restrict_sm_frgnBlocksSrc, restrict_sm_frgnBlocksTgt.
          rewrite replace_locals_extern, replace_locals_local,
                  replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
                  replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
                  replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
                  replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt in INC. 
          rewrite replace_locals_extern, replace_locals_local,
                  replace_locals_extBlocksSrc, replace_locals_extBlocksTgt,
                  replace_locals_locBlocksSrc, replace_locals_locBlocksTgt,
                  replace_locals_pubBlocksSrc, replace_locals_pubBlocksTgt,
                  replace_locals_frgnBlocksSrc, replace_locals_frgnBlocksTgt. 
          intuition.
          red; intros. destruct (restrictD_Some _ _ _ _ _ H8).
            apply restrictI_Some. apply H; trivial.
            unfold vis in H11; unfold DomSrc.
              rewrite H7, H3 in *.
              destruct (locBlocksSrc nu' b); simpl in *; trivial. 
            apply andb_true_iff; split. 
               apply (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H11).
               apply REACH_nil. unfold exportedSrc.
                 rewrite sharedSrc_iff_frgnpub, H11. intuition. trivial.
          unfold vis. rewrite H1, H3, H7.
            unfold restrict. extensionality bb. unfold DomSrc. 
            remember (local_of nu' bb) as loc.
            destruct loc. 
            apply eq_sym in Heqloc. destruct p.
              destruct (local_DomRng _ WDnu' _ _ _ Heqloc) as [lS _].
              rewrite lS; simpl; trivial.
            destruct (locBlocksSrc nu' bb); simpl; trivial.
            destruct (frgnBlocksSrc nu' bb); simpl; trivial.
              destruct (extBlocksSrc nu' bb); simpl; trivial.
              destruct (REACH m1' (exportedSrc nu' (ret1 :: nil)) bb); 
                 simpl; trivial. 
              destruct (extBlocksSrc nu' bb); simpl; trivial.
              destruct (REACH m1' (exportedSrc nu' (ret1 :: nil)) bb);
                 simpl; trivial. 
       rewrite vis_restrict_sm, restrict_sm_locBlocksSrc. 
         clear - WDnu'.
         intros. unfold vis in H.
         destruct (locBlocksSrc nu' b); simpl in *; trivial. 
         apply andb_true_iff; split. 
          unfold DomSrc.
            rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H).
            intuition.
          apply REACH_nil. unfold exportedSrc.
            rewrite sharedSrc_iff_frgnpub, H. intuition. trivial. }

unfold vis in *.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj in *.
  
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
unfold vis in *.
intuition.
(*as in selectionproofEFF*)
  red; intros. destruct (GFP _ _ H1). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed.

Lemma MATCH_effcore_diagram: forall 
         st1 m1 st1' m1' (U1 : block -> Z -> bool)
         (CS: effstep (cminsel_eff_sem hf) ge U1 st1 m1 st1' m1')
         st2 mu m2 
         (MTCH: MATCH st1 mu st1 m1 st2 m2),
exists st2' m2' mu', exists U2 : block -> Z -> bool,
  (effstep_plus (rtl_eff_sem hf) tge U2 st2 m2 st2' m2' \/
      effstep_star (rtl_eff_sem hf) tge U2 st2 m2 st2' m2' /\ lt_state st1' st1)
 /\ intern_incr mu mu' /\
  sm_locally_allocated mu mu' m1 m2 m1' m2' /\
  MATCH st1' mu' st1' m1' st2' m2' /\
     (forall 
       (UHyp: forall b z, U1 b z = true -> vis mu b = true)
        b ofs, U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1)%Z = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof. intros st1 m1 st1' m1' U1 CS.
  assert (SymbPres:= symbols_preserved).
  induction CS; intros; destruct MTCH as [MSTATE PRE]; inv MSTATE. 
{ (* skip seq *)
  inv TS. inv TK.
  eexists; exists m2, mu; eexists; split.
     right; split. apply effstep_star_zero. Lt_state.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition.  }

{ (* skip block *)
  inv TS. inv TK. 
  eexists; exists m2, mu; eexists; split. 
    right; split. apply effstep_star_zero. Lt_state.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. constructor.
      intuition. }

{ (* skip return *)
  inv TS. 
  assert ((fn_code tf)!ncont = Some(Ireturn rret)
          /\ match_stacks (restrict_sm mu (vis mu)) k cs).
    inv TK; simpl in H; (*try rewrite restrict_sm_all in *;*)
         try contradiction; auto. 
  destruct H1.
  rewrite restrict_sm_all in *.
  assert (fn_stacksize tf = fn_stackspace f).
    inv TF. auto.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  destruct SP as [spb [spb' [X [Y Rsp]]]]; subst sp'; inv X.
  rewrite restrict_sm_local' in *; trivial. 
  edestruct free_parallel_inject as [tm' []]; eauto.
    eapply incr_local_restrictvis; eassumption.  
  eexists; exists tm', mu, (FreeEffect m2 0 (fn_stacksize tf) spb'); split.
    simpl in *; rewrite Zplus_0_r in H4. rewrite <- H3 in H4.
    left; apply effstep_plus_one. 
      eapply rtl_effstep_exec_Ireturn; try eassumption.
  assert (SMV': sm_valid mu m' tm').
    split; intros;  
      eapply free_forward; try eassumption.
      eapply SMV; assumption.
      eapply SMV; assumption.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_free _ _ _ _ _ H4);
          try rewrite (freshloc_free _ _ _ _ _ H0); intuition.
  split. 
    econstructor; eauto.
      rewrite restrict_sm_nest, vis_restrict_sm; trivial.
        rewrite vis_restrict_sm; trivial.
      rewrite restrict_sm_all; trivial.      
    intuition.
    eapply REACH_closed_free; try eassumption.
      eapply (free_free_inject _ m m' m2); try eassumption.
    eapply local_in_all; eassumption.
  apply FreeEffectD in H6. destruct H6 as [? [VB Arith2]]; subst.
        eapply local_visTgt; eassumption.
  rewrite H3 in H6. eapply FreeEffect_PropagateLeft'; eassumption. }

{ (* assign *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all, restrict_sm_local' in *; trivial.
  exploit Efftransl_expr_correct; eauto. 
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]; subst.
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  eexists; eexists; exists mu', EmptyEffect; split.
    right; split. eauto. Lt_state.
  assert (WDR: SM_wd (restrict_sm mu' (vis mu'))).
     apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR.
  intuition. 
  split.
      econstructor; try rewrite restrict_sm_nest; 
            try rewrite restrict_sm_all; eauto.
        econstructor; eauto. 
        eapply tr_cont_intern_incr; try eassumption.
        eapply inject_restrict; eassumption.
        eapply sp_incr; try eassumption.
          rewrite restrict_sm_local'; trivial. eapply INC'.
    intuition.

    red; intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      rewrite <-FF; auto. }

{ (* store *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all, restrict_sm_local' in *; trivial.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]; subst.
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  assert (PGR' : meminj_preserves_globals ge
                (restrict (as_inj mu') (vis mu'))).
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals; try eassumption.
     intros. eapply intern_incr_vis; try eassumption.
      unfold vis. intuition.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'; clear SP.
  exploit Efftransl_expr_correct; eauto.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
    rewrite <- FF; intuition.
  intros [rs'' [tm'' [mu'' [MU'' [F [G [J [K L]]]]]]]]; subst.
  destruct MU'' as [INC'' [SEP'' [LOCALLOC'' [WD'' [SMV'' RC'']]]]].
  assert (val_list_inject (restrict (as_inj mu') (vis mu')) vl rs''##rl).
    replace (rs'' ## rl) with (rs' ## rl). auto.
    apply list_map_exten. intros. apply K. auto.
  destruct SP' as [spb [spb' [X [Y Rsp]]]]; subst sp'; inv X. 
  edestruct eval_addressing_inject as [vaddr' []]; try eapply H1.
    apply PGR'.
    eapply incr_local_restrictvis; eassumption.
    eassumption.
  edestruct Mem.storev_mapped_inject as [tm''' []].
    eapply (inject_restrict _ _ _ _ L RC''). 
    eassumption.
    eapply val_inject_incr; try eassumption.
       eapply intern_incr_restrict; try eassumption.
    eassumption.
  assert (SMV''': sm_valid mu'' m' tm''').
    split; intros. 
      eapply storev_valid_block_1; try eassumption.
        eapply SMV''; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV''; assumption.
  assert (ADDRINJ: val_inject (restrict (as_inj mu) (vis mu)) vaddr vaddr').
           clear - INC' SEP' WD WD' H5 H2. inv H5; inv H2.
           destruct (restrictD_Some _ _ _ _ _ H) as [AI' VS']. 
           destruct SEP' as [SEPa [SEPb SEPc]].
           econstructor; try reflexivity.
           remember (as_inj mu b1) as d. 
           destruct d; apply eq_sym in Heqd.
             destruct p.
             rewrite (intern_incr_as_inj _ _ INC' WD' _ _ _ Heqd) in AI'. 
             inv AI'.
             apply restrictI_Some; try eassumption. 
             eapply intern_incr_vis_inv with (nu:=mu'); eassumption. 
           destruct (SEPa _ _ _ Heqd AI') as [DS _]. 
             destruct (as_inj_DomRng _ _ _ _ AI' WD') as [DS' _]. 
             elim (SEPb _ DS DS'). 
             exploit Mem.store_valid_access_3. eapply H1. intros. 
              eapply Mem.valid_access_valid_block; try eassumption.
              eapply Mem.valid_access_implies; try eassumption. 
                 constructor. 
  eexists; exists tm''', mu''.
    exists (StoreEffect vaddr' (encode_val chunk (rs'' # rd))).
  split.
    left; eapply effstep_star_plus_trans'.
      eapply effstep_star_trans'. eexact A. eexact F. reflexivity.
      eapply effstep_plus_one. 
        eapply rtl_effstep_exec_Istore with (a := vaddr'). eauto.
        rewrite <- H4. rewrite shift_stack_addressing_zero.
        eapply eval_addressing_preserved. exact symbols_preserved.
      eassumption.
      simpl. extensionality bb; extensionality z. 
       remember (StoreEffect vaddr' (encode_val chunk rs'' # rd) bb z) as d.
       destruct d; simpl; apply eq_sym in Heqd; trivial.
         destruct (valid_block_dec m2 bb); trivial.
         elim n; clear n.
         destruct vaddr; inv H2. inv H5. 
         apply StoreEffectD in Heqd. destruct Heqd as [ii [VV Arith]].
         inv VV. clear -  ADDRINJ MINJ. inv ADDRINJ.
             eapply Mem.valid_block_inject_2; eassumption.
  split. 
    eapply intern_incr_trans; eassumption. 
  split. 
    eapply sm_locally_allocated_trans. eapply LOCALLOC'. 
      apply sm_locally_allocatedChar.
      apply sm_locally_allocatedChar in LOCALLOC''.
      destruct LOCALLOC'' as [DS [DT [LBS [LBT [EBS EBT]]]]].
      rewrite DS, DT, LBS, LBT, EBS, EBT.
      repeat split; extensionality bb;
        try rewrite (freshloc_irrefl);
        try rewrite (storev_freshloc _ _ _ _ _ H2);
        try rewrite (storev_freshloc _ _ _ _ _ H6); intuition.
      rewrite <- (freshloc_trans tm' tm'' tm''' ), 
                 (storev_freshloc _ _ _ _ _ H6).
          rewrite orb_false_r. trivial. 
             eapply effstep_star_fwd. eassumption.
             destruct vaddr'; inv H6. eapply store_forward; eassumption.
      rewrite <- (freshloc_trans tm' tm'' tm''' ), 
                 (storev_freshloc _ _ _ _ _ H6).
          rewrite orb_false_r. trivial. 
             eapply effstep_star_fwd. eassumption.
             destruct vaddr'; inv H6. eapply store_forward; eassumption.
        apply mem_forward_refl.
        destruct vaddr; inv H2. eapply store_forward; eassumption.
        eapply effstep_star_fwd. eassumption.
        eapply mem_forward_trans.
           eapply effstep_star_fwd; eassumption.
           destruct vaddr'; inv H6. eapply store_forward; eassumption.
    assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
    assert (WDR'': SM_wd (restrict_sm mu'' (vis mu''))).
      apply restrict_sm_WD; trivial. 
    specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
    specialize (restrict_sm_intern_incr _ _ WD'' INC''); intros INCR''.
  split.
    split.
      econstructor; try rewrite restrict_sm_all; eauto. 
        constructor.
        eapply tr_cont_intern_incr; try eassumption.
          eapply intern_incr_trans; eassumption.
        rewrite restrict_sm_local'; trivial.
        eapply sp_preserved_intern_incr; try eassumption. 
          exists spb, spb'. split; trivial. split; trivial.
      intuition.

      destruct vaddr; inv H2.
        eapply REACH_Store; try eassumption. 
          inv H5. destruct (restrictD_Some _ _ _ _ _ H10); trivial.
           eapply intern_incr_vis; eassumption.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
             destruct Hoff; try contradiction. subst.   
             inv J. destruct (restrictD_Some _ _ _ _ _ H11); trivial.
      eapply meminj_preserves_incr_sep_vb
        with (j:=as_inj mu')(m0:=m)(tm:=tm'); try eassumption. 
        intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV'; eapply AI.
        assumption.
        apply intern_incr_as_inj; eassumption.
        apply sm_inject_separated_mem. assumption.
        assumption.

      red; intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
         eapply intern_incr_as_inj; try eapply H8. 
         eapply intern_incr_trans; eassumption.
         assumption.
      assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
        assert (FF': frgnBlocksSrc mu' = frgnBlocksSrc mu'') by eapply INC''.
        rewrite <-FF', <-FF; auto. 
      assert (VaddrMu: val_inject (as_inj mu'') vaddr vaddr').
        eapply val_inject_incr; try eapply H5.
        eapply inject_incr_trans. apply restrict_incr. 
          apply intern_incr_as_inj; eassumption.
      assert (VMu: val_inject (as_inj mu'') v (rs'' # rd)).
        eapply val_inject_incr; try eassumption.
        apply restrict_incr. 
      destruct (Mem.storev_mapped_inject _ _ _ _ _ _ _ _ _ 
          L H2 VaddrMu VMu) as [mm [Hmm1 Hmm2]].
      rewrite Hmm1 in H6. inv H6. assumption. 
 (*effect propagation*)
  intros.
  destruct (StoreEffectD _ _ _ _ H8) as [i [HI OFF]]. subst.
  simpl in H6. (*inv ADDRINJ; inv H2. *)
  assert (VIST: visTgt mu b0 = true). 
     inv ADDRINJ; inv H2.
     eapply visPropagateR; try eassumption.
  intuition. 
    unfold visTgt in VIST; rewrite H11 in VIST; simpl in VIST. 
    exploit StoreEffect_PropagateLeft.
         eapply H2. 2: eapply L. eassumption.
         eapply val_inject_incr; try eapply H5.
            apply intern_incr_restrict; eassumption.
         simpl. eassumption. 
         eassumption. 
         eapply frgnBlocksTgt_locBlocksTgt; try eassumption.
          assert (FF: frgnBlocksTgt mu = frgnBlocksTgt mu') by eapply INC'.
          assert (FF': frgnBlocksTgt mu' = frgnBlocksTgt mu'') by eapply INC''.
          rewrite <- FF', <- FF; trivial.
   intros [b1 [delta [FRG' [STEFF PERM]]]].
     exists b1, delta. repeat split; trivial.
     rewrite (intern_incr_foreign _ _ INC').
     rewrite (intern_incr_foreign _ _ INC''). trivial. }

{ (* call *)
  inv TS; inv H.
  (* indirect *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  assert (PGR' : meminj_preserves_globals ge
                (restrict (as_inj mu') (vis mu'))).
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals; try eassumption.
     intros. eapply intern_incr_vis; try eassumption.
      unfold vis. intuition.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'; clear SP.
  exploit Efftransl_exprlist_correct; eauto.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
    rewrite <- FF; intuition.
  intros [rs'' [tm'' [mu'' [MU'' [F [G [J [K L]]]]]]]]. 
  destruct MU'' as [INC'' [SEP'' [LOCALLOC'' [WD'' [SMV'' RC'']]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  destruct (Genv.find_funct_inv _ _ H1) as [bb XX]; subst vf.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  inv C. destruct (restrictD_Some _ _ _ _ _ H5). 
  exploit (intern_incr_as_inj _ _ INC'). 
     apply WD'. apply muBB. 
  rewrite H; intros XX; inv XX. 
  rewrite Int.add_zero in H3.
  eexists; eexists; exists mu'', EmptyEffect; split.
    left; eapply effstep_star_plus_trans'.
            eapply effstep_star_trans. eexact A. eexact F.
          eapply effstep_plus_one. 
            eapply rtl_effstep_exec_Icall; eauto.
               simpl. rewrite K. rewrite <- H3. eassumption. simpl; eauto.
               apply sig_transl_function; auto.
          reflexivity.
  intuition.
      eapply intern_incr_trans; eassumption. 
      eapply sm_locally_allocated_trans; try eassumption.      
         apply mem_forward_refl.   
         apply mem_forward_refl.
         eapply effstep_star_fwd; eassumption.
         eapply effstep_star_fwd; eassumption.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  assert (WDR'': SM_wd (restrict_sm mu'' (vis mu''))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  specialize (restrict_sm_intern_incr _ _ WD'' INC''); intros INCR''.
  split. 
    econstructor; try rewrite restrict_sm_nest, vis_restrict_sm; eauto. 
      econstructor; try rewrite restrict_sm_all; try eassumption.
      
      eapply tr_cont_intern_incr; try eassumption.
          eapply intern_incr_trans; eassumption.
      exploit sp_preserved_intern_incr; try eassumption. 
        rewrite restrict_sm_local'; trivial.
      rewrite vis_restrict_sm; trivial.
      rewrite restrict_sm_all, restrict_nest, vis_restrict_sm; try eassumption. 
      rewrite vis_restrict_sm; trivial.
      rewrite restrict_sm_all. eapply inject_restrict; eassumption.
      intuition.
   eapply meminj_preserves_incr_sep_vb
        with (j:=as_inj mu')(m0:=m)(tm:=tm'); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV'; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
         eapply intern_incr_as_inj; try eapply H8. 
         eapply intern_incr_trans. eapply INC'. eassumption. assumption.
         assumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      assert (FF': frgnBlocksSrc mu' = frgnBlocksSrc mu'') by eapply INC''.
      rewrite <-FF', <-FF; auto. 
  (* direct *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  assert (PGR' : meminj_preserves_globals ge
                (restrict (as_inj mu') (vis mu'))).
     rewrite <- restrict_sm_all. 
     eapply restrict_sm_preserves_globals; try eassumption.
     intros. eapply intern_incr_vis; try eassumption.
      unfold vis. intuition.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'; clear SP.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  eexists; eexists; exists mu', EmptyEffect; split.
    left. eapply effstep_star_plus_trans'. eexact A.
          eapply effstep_plus_one. 
            eapply rtl_effstep_exec_Icall; eauto. 
             simpl. rewrite symbols_preserved. rewrite H4. 
             rewrite Genv.find_funct_find_funct_ptr in P. eauto. 
             apply sig_transl_function; auto.
          reflexivity.
  intuition. 
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  split. 
    econstructor; try rewrite restrict_sm_nest, restrict_sm_all, 
             vis_restrict_sm; eauto.
      rewrite restrict_sm_nest.
      econstructor; try rewrite vis_restrict_sm; try eassumption. 
        rewrite restrict_sm_all; try eassumption.
      eapply tr_cont_intern_incr; try eassumption.
      rewrite restrict_sm_local'; trivial.
      rewrite vis_restrict_sm; trivial.
      rewrite restrict_sm_all, vis_restrict_sm, restrict_nest; trivial.
      rewrite restrict_sm_all. eapply inject_restrict; eassumption.
      intuition.
    red; intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
         eapply intern_incr_as_inj; try eapply H8. 
         eassumption. assumption.
         assumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      rewrite <-FF; auto. }

{ (* tailcall *)
  inv TS; inv H.
  (* indirect *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'.
  exploit Efftransl_exprlist_correct; try eapply PG'.
     eassumption.  eassumption.  eassumption.  eassumption. 
     eassumption.  
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      rewrite <- FF; intuition.
     eassumption.  eassumption.  eassumption.
     eassumption.  eassumption. 
  intros [rs'' [tm'' [mu'' [MU'' [EX [F [G [J K]]]]]]]].
  destruct MU'' as [INC'' [SEP'' [LOCALLOC'' [WD'' [SMV'' RC'']]]]].
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (FSS: fn_stacksize tf = fn_stackspace f). inv TF; auto.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP''; clear SP'.
  destruct SP'' as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB. 
  edestruct free_parallel_inject as [tm''' []]; eauto.
    eapply local_in_all; eassumption.
  destruct (Genv.find_funct_inv _ _ H1) as [bb XX]; subst vf.
  rewrite Genv.find_funct_find_funct_ptr in H1.
  destruct (GFP _ _ H1) as [muBB isGlobalBB].
  inv C. destruct (restrictD_Some _ _ _ _ _ H9). 
     specialize (intern_incr_as_inj _ _ INC' WD' _ _ _ muBB). 
     intros XX; rewrite H4 in XX; inv XX. 
  rewrite Int.add_zero in H8.
  simpl in H. rewrite Zplus_0_r in H.
  assert (LOC: local_of mu spb = Some (spb', 0%Z)). 
     destruct SP as [xb [xtb [XX [YY LOC]]]]; inv XX; inv YY.
     trivial.    
  eexists; exists tm'''; exists mu''. 
  exists (FreeEffect tm'' 0 (fn_stacksize tf) spb').
  split. left; eapply effstep_star_plus_trans'.
           eapply effstep_star_trans. eexact A. eexact EX.
           eapply effstep_plus_one.
             eapply rtl_effstep_exec_Itailcall; eauto.
             simpl. rewrite J. rewrite <- H8. eassumption.
             simpl; eauto.
             apply sig_transl_function; auto.
           rewrite FSS. eassumption.
         simpl. apply extensionality; intros b'. 
                apply extensionality; intros z.
             remember (FreeEffect tm'' 0 (fn_stacksize tf) spb' b' z) as d. 
             destruct d; simpl; trivial. 
             apply eq_sym in Heqd. 
             apply FreeEffectD in Heqd. 
             destruct Heqd as [? [? ?]]; subst.
             clear - LOC WD SMV MInj. 
             apply local_in_all in LOC; trivial.
             destruct (as_inj_DomRng _ _ _ _ LOC WD) as [_ DT].
             destruct (valid_block_dec m2 spb'); simpl; trivial. 
             elim n. eapply SMV; trivial. 
  assert (SMV''': sm_valid mu'' m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV''; assumption.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  assert (WDR'': SM_wd (restrict_sm mu'' (vis mu''))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  specialize (restrict_sm_intern_incr _ _ WD'' INC''); intros INCR''.
  intuition.
    eapply intern_incr_trans; eassumption.
    eapply sm_locally_allocated_trans. eapply LOCALLOC'. 
      apply sm_locally_allocatedChar.
      apply sm_locally_allocatedChar in LOCALLOC''.
      destruct LOCALLOC'' as [DS [DT [LBS [LBT [EBS EBT]]]]].
      rewrite DS, DT, LBS, LBT, EBS, EBT.
      repeat split; extensionality bbb;
        try rewrite (freshloc_irrefl);
        try rewrite (freshloc_free _ _ _ _ _ H);
        try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
      rewrite <- (freshloc_trans tm' tm'' tm''' ), 
                 (freshloc_free _ _ _ _ _ H).
          rewrite orb_false_r. trivial. 
             eapply effstep_star_fwd. eassumption.
             eapply free_forward; eassumption.
      rewrite <- (freshloc_trans tm' tm'' tm''' ), 
                 (freshloc_free _ _ _ _ _ H).
          rewrite orb_false_r. trivial. 
             eapply effstep_star_fwd. eassumption.
             eapply free_forward; eassumption.
        apply mem_forward_refl.
        eapply free_forward; eassumption.
        eapply effstep_star_fwd; eassumption.
        eapply mem_forward_trans.
          eapply effstep_star_fwd; eassumption.
          eapply free_forward; eassumption.
    assert (RC''': REACH_closed m' (vis mu'')).
        eapply REACH_closed_free; eassumption.
    split. 
      econstructor; try rewrite restrict_sm_all, vis_restrict_sm, 
           restrict_nest; eauto. 
        rewrite restrict_sm_nest, vis_restrict_sm; trivial.
        eapply match_stacks_intern_incr; try eassumption.
            eapply intern_incr_trans; eassumption.
        rewrite vis_restrict_sm; trivial.
        rewrite restrict_sm_all. 
          eapply inject_restrict; try eassumption.
      intuition.
   eapply meminj_preserves_incr_sep_vb
        with (j:=as_inj mu')(m0:=m)(tm:=tm'); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV'; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
         eapply intern_incr_as_inj; try eapply H8. 
         eapply intern_incr_trans. eapply INC'. eassumption. assumption.
         assumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      assert (FF': frgnBlocksSrc mu' = frgnBlocksSrc mu'') by eapply INC''.
      rewrite <-FF', <-FF; auto. 
  apply FreeEffectD in H10. destruct H10 as [? [VB Arith2]]; subst.
    eapply local_visTgt; eassumption.      
  rewrite FSS in H10. 
    exploit FreeEffect_PropagateLeft'; try eapply H10.
      eapply H3. eassumption. eassumption.  eassumption. 
       apply FreeEffectD in H10. destruct H10 as [? [VB Arith2]]; subst.
       destruct (local_DomRng _ WD _ _ _ LOC) as [_ lT].
       rewrite lT in H11; discriminate.
    intros [b1 [delta [FRG' [STEFF PERM]]]].
      exists b1, delta. repeat split; trivial.
      rewrite (intern_incr_foreign _ _ INC').
      rewrite (intern_incr_foreign _ _ INC''). trivial. 

  (* direct *)
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_exprlist_correct; eauto.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'.
  exploit functions_translated; eauto. intros [tf' [P Q]].
  exploit match_stacks_call_cont; eauto. intros [U V].
  assert (FSS: fn_stacksize tf = fn_stackspace f). inv TF; auto.
  destruct SP' as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
    apply local_in_all; eassumption.
  simpl in H. rewrite Zplus_0_r in H.
  assert (LOC: local_of mu spb = Some (spb', 0%Z)). 
     destruct SP as [xb [xtb [XX [YY LOC]]]]; inv XX; inv YY.
     assumption. 
  eexists; exists tm''', mu';
    exists (FreeEffect tm' 0 (fn_stacksize tf) spb'). 
  split. left; eapply effstep_star_plus_trans'. eexact A.
          eapply effstep_plus_one.
            eapply rtl_effstep_exec_Itailcall; eauto.
             simpl. rewrite symbols_preserved. rewrite H5. 
             rewrite Genv.find_funct_find_funct_ptr in P. eauto. 
             apply sig_transl_function; auto.
           rewrite FSS. assumption.
         simpl. apply extensionality; intros b'. 
                apply extensionality; intros z.
             remember (FreeEffect tm' 0 (fn_stacksize tf) spb' b' z) as d. 
             destruct d; simpl; trivial. 
             apply eq_sym in Heqd. 
             apply FreeEffectD in Heqd. 
             destruct Heqd as [? [? ?]]; subst.
             clear - LOC WD SMV MInj. 
             apply local_in_all in LOC; trivial.
             destruct (as_inj_DomRng _ _ _ _ LOC WD) as [_ DT].
             destruct (valid_block_dec m2 spb'); simpl; trivial. 
             elim n. eapply SMV; trivial. 
  assert (SMV'': sm_valid mu' m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV'; assumption.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  split. trivial.
  split. trivial.
    eapply sm_locally_allocated_trans. eapply LOCALLOC'. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality bbb;
        try rewrite (freshloc_free _ _ _ _ _ H);
        try rewrite (freshloc_free _ _ _ _ _ H3); intuition.
        apply mem_forward_refl.
        eapply free_forward; eassumption.
        eapply effstep_star_fwd; eassumption.
        eapply free_forward; eassumption.
  assert (RC'': REACH_closed m' (vis mu')).
        eapply REACH_closed_free; eassumption.
  split. 
    split.
      econstructor; try rewrite restrict_sm_all, vis_restrict_sm, 
           restrict_nest; eauto. 
        rewrite restrict_sm_nest, vis_restrict_sm; trivial.
          eapply match_stacks_intern_incr; try eassumption.
        rewrite vis_restrict_sm; trivial.
        rewrite restrict_sm_all. 
          eapply inject_restrict; try eassumption.
    intuition. 
    red; intros ? ? Hb. destruct (GFP _ _ Hb). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      rewrite <-FF; auto.
  (*effect propagation*)
  intros UVis ? z FREFF.
  split. apply FreeEffectD in FREFF. 
         destruct FREFF as [? [VB Arith2]]; subst.
         eapply local_visTgt; eassumption.  
  rewrite FSS in FREFF; intros lTF.
  exploit FreeEffect_PropagateLeft'; try eapply FREFF.
      eapply H3. eassumption. eassumption.  eassumption. 
       apply FreeEffectD in FREFF. destruct FREFF as [? [VB Arith2]]; subst.
       destruct (local_DomRng _ WD _ _ _ LOC) as [_ lT].
       rewrite lT in lTF; discriminate.
    intros [b1 [delta [FRG' [STEFF PERM]]]].
      exists b1, delta. repeat split; trivial.
      rewrite (intern_incr_foreign _ _ INC'). trivial.  }

{  (* builtin*)
  inv TS. 
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD INJ]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_exprlist_correct; try eapply MINJ; try eassumption.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'; clear SP.
  exploit (inlineable_extern_inject _ _ GDE_lemma);
     try eapply C; try eassumption.   
     assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'. 
       rewrite <- FF; eapply Glob; eassumption. 
  intros [mu'' [vres' [tm'' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INC'' [SEP'' [LOCALLOC'' [WD'' [SMV'' RC'']]]]]]]]]]]]].
  eexists; eexists; eexists mu''. eexists.
  split. left.
    eapply effstep_star_plus_trans'. eapply A.
      eapply effstep_plus_one.
      eapply rtl_effstep_exec_Ibuiltin. eauto. eassumption.
      assumption. reflexivity.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP''; clear SP'.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  assert (WDR'': SM_wd (restrict_sm mu'' (vis mu''))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  specialize (restrict_sm_intern_incr _ _ WD'' INC''); intros INCR''.
  split.
    eapply intern_incr_trans; eassumption.
  split.
    eapply sm_locally_allocated_trans; try eassumption. 
      apply mem_forward_refl.
      eapply external_call_mem_forward; eassumption.
      eapply effstep_star_fwd; eassumption.
      eapply external_call_mem_forward; eassumption.
  split. 
    split.
      econstructor; try rewrite restrict_sm_all, vis_restrict_sm, 
           restrict_nest; eauto. 
      constructor.
      eapply tr_cont_intern_incr; try eassumption.
        eapply intern_incr_trans; eassumption.
      rewrite restrict_sm_all.
        eapply match_env_update_dest; eauto.
          eapply match_env_inject_incr; try eassumption.
          eapply intern_incr_restrict; try eassumption.
      rewrite restrict_sm_all.
       eapply inject_restrict; try eassumption. auto.
      destruct SP'' as [spb [tspb [? [? BSP]]]].
        exists spb, tspb. split; trivial. split; trivial.
          rewrite restrict_sm_local'; trivial.
    intuition.
    eapply meminj_preserves_incr_sep. eapply PG'. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
    red; intros ? ? Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; try eapply H2. 
          eapply intern_incr_trans; eassumption.
          assumption.
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
     assert (FRG': frgnBlocksSrc mu' = frgnBlocksSrc mu'') by eapply INC''.
          rewrite <- FRG', <- FRG. eapply Glob; eassumption. 
  (*effect propagation*)
  simpl. intros UVis b z EFF. 
    apply andb_true_iff in EFF; destruct EFF as [EFF VB].
    exploit @BuiltinEffect_Propagate; try eapply EFF. 
     4: eassumption. eassumption. eassumption. eassumption.
      rewrite (intern_incr_foreign _ _ INC'). 
  intros [visT EffProp].
  assert (FF: frgnBlocksTgt mu = frgnBlocksTgt mu') by eapply INC'.
  assert (VIST: visTgt mu b = true). 
    clear EffProp.
    unfold visTgt; unfold visTgt in visT. rewrite <- FF in visT.
    clear FF. destruct (frgnBlocksTgt mu b). apply orb_true_r.
    rewrite orb_false_r in visT.
    apply sm_locally_allocatedChar in LOCALLOC'.
      destruct LOCALLOC' as [_ [_ [_ [lT _]]]]. rewrite lT in visT.
      destruct (locBlocksTgt mu b); simpl in *. trivial.
      apply freshloc_charT in visT.
      destruct (valid_block_dec m2 b). intuition. discriminate.
  split. trivial.
  intros; eapply EffProp; clear EffProp.
    unfold visTgt in VIST. rewrite H2 in VIST; simpl in *. 
    rewrite FF in VIST. eapply frgnBlocksTgt_locBlocksTgt; trivial. } 

{ (* seq *)
  inv TS.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto. econstructor; eauto.
      intuition. }

{ (* ifthenelse *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_condexpr_correct; try eassumption.
  intros [rs' [tm' [mu' [MU' [A [B [C D]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  intros SP'; clear SP.
  eexists; exists tm', mu', EmptyEffect.
  split.
    left. eexact A.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  intuition. 
  split.  
    econstructor; eauto.
      destruct b; eassumption. 
      eapply tr_cont_intern_incr; try eassumption.
      rewrite restrict_sm_all. assumption.
      rewrite restrict_sm_all. 
        apply inject_restrict; eassumption. 
      rewrite restrict_sm_local'; trivial. 
      intuition.
      red; intros ? ? Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
          rewrite <- FRG. eapply (Glob _ H0).  }

{ (* loop *)
  inversion TS; subst.
  eexists; exists m2, mu, EmptyEffect; split.
    left. apply effstep_plus_one. eapply rtl_effstep_exec_Inop; eauto. 
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor.
       econstructor; eauto.  
       econstructor; eauto.
       econstructor; eauto.
      intuition. }

{ (* block *)
  inv TS.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition. }

{ (* exit seq *)
  inv TS. inv TK. 
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state. 
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition. }

{ (* exit block 0 *)
  inv TS. inv TK. simpl in H0. inv H0.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state. 
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition. }

{ (* exit block n+1 *)
  inv TS. inv TK. simpl in H0.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state. 
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
        econstructor; eauto.
      intuition. }

{ (* switch *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit validate_switch_correct; eauto. intro CTM.
  exploit Efftransl_expr_correct; eauto. 
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  exploit Efftransl_switch_correct; eauto. inv C. auto.
  intros [nd [rs'' [F [G K]]]].
  eexists; eexists; exists mu', EmptyEffect; split.
    right; split. eapply effstep_star_trans'. 
          eexact A. eexact F. reflexivity. Lt_state. 
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  intuition. 
  split.
    econstructor; eauto. constructor; eassumption.
      eapply tr_cont_intern_incr; try eassumption.
      rewrite restrict_sm_all. assumption.
      rewrite restrict_sm_all. 
        apply inject_restrict; eassumption. 
      rewrite restrict_sm_local'; trivial. 
      intuition.
      red; intros ? ? Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
          rewrite <- FRG. eapply (Glob _ H1).  }

{ (* return none *)
  inv TS.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm''' []]; eauto.
    eapply incr_local_restrictvis; eassumption.
  eexists; exists tm''', mu.
  exists (FreeEffect m2 0 (fn_stacksize tf) spb'). 
  split. 
    simpl in H0; rewrite Zplus_0_r in H0. rewrite <- H2 in H0. 
    left; eapply effstep_plus_one. 
            eapply rtl_effstep_exec_Ireturn; eauto.
  assert (SMV': sm_valid mu m' tm''').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b'; 
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H); intuition.
  split. econstructor; try rewrite restrict_sm_all; eauto.
        rewrite vis_restrict_sm, restrict_sm_nest; trivial.
      intuition.
        eapply REACH_closed_free; eassumption.
           eapply free_free_inject; try eassumption.
           apply local_in_all; eassumption.
  apply FreeEffectD in H4. destruct H4 as [? [VB Arith2]]; subst.
    eapply local_visTgt; eassumption.
  rewrite H2 in H4. 
   eapply FreeEffect_PropagateLeft'; try eassumption. }

{ (* return some *)
  inv TS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite restrict_sm_local' in SP; trivial.
  exploit Efftransl_expr_correct; eauto.
  intros [rs' [tm' [mu' [MU' [A [B [C [D E]]]]]]]]. 
  destruct MU' as [INC' [SEP' [LOCALLOC' [WD' [SMV' RC']]]]].
  assert (PG':  meminj_preserves_globals ge (as_inj mu')).
   eapply meminj_preserves_incr_sep_vb 
        with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros ? ? ? AI. apply as_inj_DomRng in AI.
              split; eapply SMV; eapply AI.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
  clear PG.
  exploit sp_preserved_intern_incr; try eassumption.
  exploit match_stacks_call_cont; eauto. intros [U V].
  inversion TF.
  destruct SP as [spb [spb' [SPB [SPB' Rsp]]]]; subst sp'; inv SPB.
  edestruct free_parallel_inject as [tm'' []]; eauto.
    eapply intern_incr_as_inj; try eassumption.
     apply local_in_all; eassumption.
  intros.
  eexists; exists tm'', mu'.
  exists (FreeEffect tm' 0 (fn_stacksize tf) spb'). 
  split. 
    simpl in H5; rewrite Zplus_0_r in H5. rewrite <- H4 in H5. 
    left; eapply effstep_star_plus_trans'. eexact A.
          eapply effstep_plus_one.
            eapply rtl_effstep_exec_Ireturn; eauto.
         simpl. apply extensionality; intros b'. 
                apply extensionality; intros z.
             remember (FreeEffect tm' 0 (fn_stacksize tf) spb' b' z) as d. 
             destruct d; simpl; trivial. 
             apply eq_sym in Heqd. 
             apply FreeEffectD in Heqd. 
             destruct Heqd as [? [? ?]]; subst.
             clear - Rsp WD SMV MInj. 
             apply local_in_all in Rsp; trivial.
             destruct (as_inj_DomRng _ _ _ _ Rsp WD) as [_ DT].
             destruct (valid_block_dec m2 spb'); simpl; trivial. 
             elim n. eapply SMV; trivial. 
  assert (SMV'': sm_valid mu' m' tm'').
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV'; assumption.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  intuition. 
      apply sm_locally_allocatedChar.
      apply sm_locally_allocatedChar in LOCALLOC'.
      destruct LOCALLOC' as [DS [DT [LBS [LBT [EBS EBT]]]]].
      rewrite DS, DT, LBS, LBT, EBS, EBT.
      repeat split; extensionality b'; 
          try rewrite (freshloc_irrefl);
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ H5); intuition.
      rewrite <- (freshloc_trans m2 tm' tm''),
                 (freshloc_free _ _ _ _ _ H5).
          rewrite orb_false_r. trivial. 
             eapply effstep_star_fwd; eassumption.
             eapply free_forward; eassumption.
      rewrite <- (freshloc_trans m2 tm' tm''),
                 (freshloc_free _ _ _ _ _ H5).
          rewrite orb_false_r. trivial. 
             eapply effstep_star_fwd; eassumption.
             eapply free_forward; eassumption.
   assert (RC'': REACH_closed m' (vis mu')).
        eapply REACH_closed_free; eassumption.
   split. 
     econstructor; try rewrite restrict_sm_all; eauto.
      rewrite vis_restrict_sm, restrict_sm_nest; trivial.
      eapply match_stacks_intern_incr; try eassumption.
      rewrite vis_restrict_sm, restrict_nest; trivial.
      eapply inject_restrict; try eassumption.
     intuition.
      red; intros ? ? Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
          rewrite <- FRG. eapply (Glob _ H8).  
  apply FreeEffectD in H8. destruct H8 as [? [VB Arith2]]; subst.
    eapply local_visTgt; eassumption.      
  rewrite H4 in H8. 
    exploit FreeEffect_PropagateLeft'; try eapply H8.
      eapply H0. eassumption. eassumption. eapply INC'; eassumption. 
       apply FreeEffectD in H8. destruct H8 as [? [VB Arith2]]; subst.
       destruct (local_DomRng _ WD _ _ _ Rsp) as [_ lT].
       rewrite lT in H9; discriminate.
    rewrite (intern_incr_foreign _ _ INC'); trivial. }

{ (* label *)
  inv TS.
  eexists; exists m2, mu, EmptyEffect; split.
    right; split. apply effstep_star_zero. Lt_state.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition. }

{ (* goto *)
  inv TS. inversion TF; subst.
  exploit tr_find_label; eauto. eapply tr_cont_call_cont; eauto. 
  intros [ns2 [nd2 [nexits2 [A [B C]]]]].
  eexists; exists m2, mu, EmptyEffect; split.
    left; apply effstep_plus_one. eapply rtl_effstep_exec_Inop; eauto.
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      econstructor. econstructor; eauto.
      intuition. }

{ (* internal call *)
  monadInv TF. exploit transl_function_charact; eauto. intro TRF.
  inversion TRF. subst f0.
  pose (e := set_locals (fn_vars f) (set_params vargs (CminorSel.fn_params f))).
  pose (rs := init_regs targs rparams).
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite vis_restrict_sm in *.
  rewrite restrict_nest in *; trivial.
  assert (ME: match_env (restrict (as_inj mu) (vis mu)) map2 e nil rs).
    unfold rs, e. eapply match_init_env_init_reg; eauto.
  assert (MWF: map_wf map2).
    assert (map_valid init_mapping s0) by apply init_mapping_valid.
    exploit (add_vars_valid (CminorSel.fn_params f)); eauto. 
    intros [A B].
    eapply add_vars_wf; eauto. eapply add_vars_wf; eauto. 
      apply init_mapping_wf.
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [INC' [mu'SP mu'MuR]]]]]]]; eauto; try apply Zle_refl.
  destruct mu'MuR as [A [B [C [WD' [E F]]]]].
  eexists. exists tm', mu', EmptyEffect; split.
    left; apply effstep_plus_one.
       eapply rtl_effstep_exec_function_internal; simpl; eauto.
  assert (DomSP:= alloc_DomSrc _ _ _ SMV _ _ _ _ H).
      assert (TgtB2: DomTgt mu b' = false).
        remember (DomTgt mu b') as d.
        destruct d; trivial; apply eq_sym in Heqd.
        elim (Mem.fresh_block_alloc _ _ _ _ _ Alloc').
          apply SMV. assumption.
  assert (WDR': SM_wd (restrict_sm mu' (vis mu'))).
      apply restrict_sm_WD; trivial. 
  specialize (restrict_sm_intern_incr _ _ WD' INC'); intros INCR'.
  assert (IncVis: inject_incr (restrict (as_inj mu) (vis mu)) (restrict (as_inj mu') (vis mu'))). 
    red; intros. destruct (restrictD_Some _ _ _ _ _ H5).
         eapply restrictI_Some.
           eapply intern_incr_as_inj; try eassumption.
         eapply intern_incr_vis; eassumption.
  intuition.
  split. econstructor; try rewrite restrict_sm_all, restrict_sm_nest,
                 vis_restrict_sm; try eassumption.
           econstructor; eauto.
           simpl. inversion MS; subst; econstructor; eauto.
           econstructor.
           inv MS. econstructor; try rewrite restrict_sm_nest;
                    try eassumption.
                   eapply match_env_inject_incr; try eassumption.
                      rewrite restrict_sm_nest, restrict_sm_all; trivial.
                      rewrite restrict_sm_all; trivial.
                   rewrite restrict_sm_nest in H26; trivial.
                     eapply tr_cont_intern_incr; try eassumption.
                   rewrite restrict_sm_local'; trivial.
                     rewrite restrict_sm_nest, restrict_sm_local' in H27; trivial.
                     eapply sp_incr; try eassumption. apply INC'.
                  
                     eapply match_env_inject_incr; try eassumption.
                       rewrite restrict_sm_all; trivial.
           rewrite restrict_sm_all; trivial.
             eapply inject_restrict; eassumption.
           exists sp, b'. split; trivial. split; trivial.
             rewrite restrict_sm_local'; trivial.  
             destruct (joinD_Some _ _ _ _ _ mu'SP) as [EXT | [_ LOC]];
               trivial.
             destruct (extern_DomRng _ WD' _ _ _ EXT) as [eS eT].
              assert (extBlocksSrc mu = extBlocksSrc mu') by eapply INC'. 
              rewrite <- H7 in eS.
              unfold DomSrc in DomSP; rewrite eS, orb_true_r in DomSP;
                 discriminate. 
  intuition.
    apply meminj_preserves_incr_sep_vb with (j:=as_inj mu)(m0:=m)(tm:=m2); try eassumption. 
      intros. apply as_inj_DomRng in H7.
              split; eapply SMV; eapply H7.
      assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem. assumption.
      assumption.
    red; intros. destruct (GFP _ _ H7). split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC'.
      apply Glob in H7. rewrite <-FF; trivial. }

  (* no external call *)

{ (* return *)
  inv MS.
  destruct PRE as [RC [PG [GFP [Glob [SMV [WD MInj]]]]]].
  rewrite restrict_sm_all in *.
  rewrite vis_restrict_sm in *.
  rewrite restrict_nest in *; trivial.
  eexists; exists m2, mu, EmptyEffect; split. 
    left; apply effstep_plus_one; constructor. 
  intuition. 
      apply intern_incr_refl. 
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
      split. econstructor; try rewrite restrict_sm_all; eauto. 
              constructor. 
             rewrite restrict_sm_nest in *; trivial. eassumption.
             rewrite restrict_sm_all, restrict_nest in H7; trivial.
               eapply match_env_update_dest; eauto.
             rewrite restrict_sm_nest in H10; trivial.
      intuition. }
Qed.  

Lemma MATCH_halted cd mu c1 m1 c2 m2 v1: forall
        (MTCH: MATCH cd mu c1 m1 c2 m2)
        (HALT: halted (cminsel_eff_sem hf) c1 = Some v1),
exists v2 : val,
  Mem.inject (as_inj mu) m1 m2 /\
  val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
  halted (rtl_eff_sem hf) c2 = Some v2 
  /\ forall (pubSrc' pubTgt' : block -> bool)
        (pubSrcHyp : pubSrc' =
                 (fun b : block => 
                 locBlocksSrc mu b && REACH m1 (exportedSrc mu (v1::nil)) b))
        (pubTgtHyp: pubTgt' =
                 (fun b : block => 
                 locBlocksTgt mu b && REACH m2 (exportedTgt mu (v2::nil)) b))
        nu (Hnu: nu = (replace_locals mu pubSrc' pubTgt')),
      MATCH cd nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2 /\
      Forall2 (val_inject (restrict (as_inj nu) (sharedSrc nu))) (v1::nil) (v2::nil) /\
      exportedSrc nu (v1::nil) = mapped (shared_of nu) /\
      REACH_closed m1 (exportedSrc nu (v1::nil)) .
Proof. intros.
  destruct MTCH as [MC [RC [PG [GFP [Glob [SMV [WDmu INJ]]]]]]]. 
    destruct c1; inv HALT. destruct k; inv H0.
    inv MC. exists tv.
    rewrite restrict_sm_nest, vis_restrict_sm,
            restrict_sm_all, restrict_nest in *; trivial.
    split. assumption.
    split. eassumption.
    split. simpl. inv MS. trivial.
intros.
assert (WDnu: SM_wd nu).
  subst.
  eapply replace_locals_wd; eauto.
    intros.
    apply andb_true_iff in H. destruct H.
    exploit (REACH_local_REACH _ WDmu); try eassumption.
      eapply val_list_inject_forall_inject.
      econstructor.   
        eapply val_inject_incr; try eassumption.
        apply restrict_incr.
      constructor.
    intros [b2 [d [loc R2]]].
      exists b2, d.
      rewrite loc, R2. destruct (local_DomRng _ WDmu _ _ _ loc). intuition.
   intros. apply andb_true_iff in H. eapply H.
split. subst.
  split. rewrite replace_locals_vis.
    econstructor; eauto.
    rewrite vis_restrict_sm, restrict_sm_nest, replace_locals_vis.
      eapply match_stacks_replace_locals; assumption.
      rewrite replace_locals_vis; trivial.
    rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; trivial.
      rewrite replace_locals_as_inj, replace_locals_vis; trivial.
      rewrite replace_locals_vis; trivial.
    rewrite restrict_sm_all, replace_locals_as_inj; trivial.
  rewrite replace_locals_as_inj, replace_locals_vis,
         replace_locals_frgnBlocksSrc.
  intuition.
  split; intros.
    rewrite replace_locals_DOM in H. eapply SMV; trivial.
    rewrite replace_locals_RNG in H. eapply SMV; trivial.
   (*rewrite replace_locals_DomTgt. assumption.*)
assert (RCnu: REACH_closed m1 (mapped (shared_of nu))).
  subst. rewrite replace_locals_shared.
  red; intros. apply REACHAX in H. destruct H as [L HL].
    generalize dependent b.
    induction L; simpl; intros; inv HL. trivial.
    specialize (IHL _ H1); clear H1.
    destruct (mappedD_true _ _ IHL) as [[bb ofs] Hbb]. clear IHL.
    apply mapped_charT.
    assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MINJ)).
    destruct (joinD_Some _ _ _ _ _ Hbb); clear Hbb.
      exploit (MV b' z bb ofs).
        eapply restrictI_Some. apply foreign_in_all; eassumption.
          unfold vis. unfold foreign_of in H. destruct mu. simpl in *. destruct (frgnBlocksSrc b'); inv H. intuition.
        assumption.
      clear MV; intros. rewrite H4 in H0. inv H0.
      exists (b2, delta). apply joinI.
      remember (locBlocksSrc mu b) as d.
      destruct d; apply eq_sym in Heqd. 
        right; simpl. destruct (restrictD_Some _ _ _ _ _ H5); clear H5.
        split. eapply locBlocksSrc_foreignNone; eassumption.
        destruct (joinD_Some _ _ _ _ _ H0).
          destruct (extern_DomRng _ WDmu _ _ _ H3).
          apply extBlocksSrc_locBlocksSrc in H5. rewrite H5 in Heqd; inv Heqd.
           trivial.
        destruct H3. rewrite H5.
        assert (REACH m1 (exportedSrc mu (v1::nil)) b = true).
          eapply REACH_cons; try eassumption.
          eapply REACH_nil. unfold exportedSrc, sharedSrc. apply foreign_in_shared in H. rewrite H. intuition.
        rewrite H6. trivial.
      left. eapply restrict_vis_foreign; try eassumption.
               destruct (restrictD_Some _ _ _ _ _ H5).
               rewrite (as_inj_locBlocks _ _ _ _ WDmu H0) in Heqd. trivial.
    destruct H. remember (locBlocksSrc mu b' && REACH m1 (exportedSrc mu (v1::nil)) b') as d. 
       destruct d; apply eq_sym in Heqd; inv H0.
       apply andb_true_iff in Heqd; destruct Heqd.
      exploit (MV b' z bb ofs).
        eapply restrictI_Some. apply local_in_all; eassumption.
          unfold vis. rewrite H0; trivial.
        assumption.
      clear MV; intros. rewrite H4 in H5. inv H5.
      exists (b2, delta). apply joinI.
      remember (locBlocksSrc mu b) as d.
      destruct d; apply eq_sym in Heqd. 
        right; simpl. destruct (restrictD_Some _ _ _ _ _ H8); clear H8.
        split. eapply locBlocksSrc_foreignNone; eassumption.
        destruct (joinD_Some _ _ _ _ _ H5).
          destruct (extern_DomRng _ WDmu _ _ _ H7).
          apply extBlocksSrc_locBlocksSrc in H8. rewrite H8 in Heqd; inv Heqd.
           trivial.
        destruct H7. rewrite H8.
        assert (REACH m1 (exportedSrc mu (v1::nil)) b = true).
          eapply REACH_cons; try eassumption.
        rewrite H9. trivial.
      simpl. left. eapply restrict_vis_foreign; try eassumption.
               destruct (restrictD_Some _ _ _ _ _ H8).
               rewrite (as_inj_locBlocks _ _ _ _ WDmu H5) in Heqd. trivial.
assert (MINJNU: Mem.inject (shared_of nu) m1 m2).
  eapply inject_mapped. eapply INJ. eassumption.
  subst. rewrite replace_locals_shared.
    red; intros. destruct (joinD_Some _ _ _ _ _ H); clear H.
    eapply foreign_in_all; eassumption.
    destruct H0.
      destruct (locBlocksSrc mu b && REACH m1 (exportedSrc mu (v1::nil)) b); inv H0.
      rewrite H2; eapply local_in_all; eassumption.
split; trivial.
rewrite restrict_SharedSrc; trivial.
split. 
  eapply val_list_inject_forall_inject.
  econstructor; eauto.
  eapply val_inject_sub_on'; try eassumption.
  intros. rewrite restrict_vis_foreign_local in H0; trivial.
    unfold shared_of. subst. clear MINJNU.
    rewrite replace_locals_foreign, replace_locals_pub.
    apply joinI.
    destruct (joinD_Some _ _ _ _ _ H0); clear H0.
      left; trivial.
    destruct H1. right; split; trivial.
      destruct (local_DomRng _ WDmu _ _ _ H1).
      rewrite H2, H1, (getBlocks_REACH_exportedSrc _ _ _ _ H); trivial.
assert (exportedSrc nu (v1::nil) = mapped (shared_of nu)).
  clear MINJNU RCnu.
  unfold exportedSrc, mapped.
  extensionality b. unfold sharedSrc.
  remember (shared_of nu b) as d.
  destruct d; simpl. apply orb_true_r.
  rewrite orb_false_r.
  subst. rewrite replace_locals_shared in Heqd.
    apply eq_sym in Heqd.
    apply joinD_None in Heqd. destruct Heqd.
    remember (getBlocks (v1::nil) b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    rewrite (getBlocks_REACH_exportedSrc _ _ _ _ Heqd) in H0.
    rewrite andb_true_r in H0.
(*    rewrite getBlocks_char in Heqd. destruct Heqd. destruct H1.
      subst. inv VINJ.*)
    exploit getBlocks_inject. 
      eapply val_list_inject_forall_inject.
        eapply val_cons_inject; try eapply val_nil_inject.
         eapply VINJ.
      eassumption.
    intros [b2 [delta [Rb GB2]]].
    destruct (restrictD_Some _ _ _ _ _ Rb); clear Rb.
    unfold vis in H2.
    destruct (foreign_None_frgnBlocksSrc_false _ _ WDmu H).
      rewrite H3 in H1; discriminate.
      rewrite H3, orb_false_r in H2.
      rewrite H2 in H0. 
      rewrite (locBlocksSrc_as_inj_local _ _ WDmu H2) in H1.
      rewrite H1 in H0; discriminate.
rewrite H; split; trivial.
trivial.
rewrite vis_restrict_sm; trivial. 
Qed.

(** The simulation proof *)
Theorem transl_program_correct:
  SM_simulation.SM_simulation_inject (cminsel_eff_sem hf)
   (rtl_eff_sem hf) ge tge.
Proof.
intros.
assert (GDE:=GDE_lemma).
apply simulations_lemmas.inj_simulation_star_wf with
  (match_states:=MATCH) (order :=lt_state).
(*genvs_dom_eq*)
  assumption.
(*MATCH_wd*)
  apply MATCH_wd. 
(*MATCH_reachclosed*)
  apply MATCH_RC.
(*MATCH_restrict*)
  apply MATCH_restrict.
(*MATCH_valid*)
  apply MATCH_valid.
(*MATCH_preserves_globals*)
  apply MATCH_PG.
(*MATCHinitial*)
  { intros.
    eapply (MATCH_initial _ _ _); eauto. }
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]]. 
    destruct c1; inv H0. destruct k; inv H1.
    inv MC. exists tv.
    rewrite vis_restrict_sm, restrict_sm_all, 
            restrict_sm_nest, restrict_nest in *; trivial.
    split. assumption.
    split. eassumption.
    simpl. inv MS. trivial. }
(* at_external*)
  { apply MATCH_atExternal. }
(* order_wf *)
  { apply lt_state_wf. }
(* after_external*)
  { intros.
    specialize (MATCH_afterExternal GDE _ _ _ _ _ _ _ _ _ _ _ 
       MemInjMu MatchMu AtExtSrc AtExtTgt ValInjMu
       _ pubSrcHyp _ pubTgtHyp _ NuHyp _ _ _ _ _ INC GSep WDnu' SMvalNu'
       MemInjNu' RValInjNu' FwdSrc FwdTgt _ frgnSrcHyp _ frgnTgtHyp
       _ Mu'Hyp UnchPrivSrc UnchLOOR).
    intros. eapply H. }
(*effcore_diagram*)
 { intros. exploit MATCH_effcore_diagram; try eassumption.
    intros [st2' [m2' [mu' [U2 [CS2 [? [? [? ?]]]]]]]].
    exists st2', m2', mu'.
    repeat (split; trivial).
    exists U2. split; assumption. }
Qed.

End CORRECTNESS.
