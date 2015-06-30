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

(** Correctness proof for constant propagation. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import RTL.
Require Import Lattice.
Require Import Kildall.
Require Import Liveness.
Require Import ConstpropOp.
Require Import Constprop.
Require Import ConstpropOpproof.


Require Import mem_lemmas.
Require Import semantics.
Require Import semantics_lemmas.
Require Import structured_injections.
Require Import reach.
Require Import effect_semantics.
Require Import simulations.
Require Import effect_properties.
Require Import simulations_lemmas.

Require Export Axioms.
Require Import RTL_coop.
Require Import BuiltinEffects.
Require Import RTL_eff.

Lemma mem_respects_readonly_forward' {F V} (ge : Genv.t F V) m m'
         (MRR: mem_respects_readonly ge m)
         (FWD: mem_forward m m')
         (RDO: RDOnly_fwd m m' (ReadOnlyBlocks ge)):
         mem_respects_readonly ge m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption. unfold ReadOnlyBlocks. rewrite H; trivial. intros. apply NP.
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Let gapp := make_global_approx (PTree.empty _) prog.(prog_defs).

(** * Correctness of the static analysis *)

Section ANALYSIS.

Variable sp: val.

Definition regs_match_approx (a: D.t) (rs: regset) : Prop :=
  forall r, val_match_approx ge sp (D.get r a) rs#r.

Lemma regs_match_approx_top:
  forall rs, regs_match_approx D.top rs.
Proof.
  intros. red; intros. simpl. rewrite PTree.gempty. 
  unfold Approx.top, val_match_approx. auto.
Qed.

Lemma val_match_approx_increasing:
  forall a1 a2 v,
  Approx.ge a1 a2 -> val_match_approx ge sp a2 v -> val_match_approx ge sp a1 v.
Proof.
  intros until v.
  intros [A|[B|C]].
  subst a1. simpl. auto.
  subst a2. simpl. tauto.
  subst a2. auto.
Qed.

Lemma regs_match_approx_increasing:
  forall a1 a2 rs,
  D.ge a1 a2 -> regs_match_approx a2 rs -> regs_match_approx a1 rs.
Proof.
  unfold D.ge, regs_match_approx. intros.
  apply val_match_approx_increasing with (D.get r a2); auto.
Qed.

Lemma regs_match_approx_update:
  forall ra rs a v r,
  val_match_approx ge sp a v ->
  regs_match_approx ra rs ->
  regs_match_approx (D.set r a ra) (rs#r <- v).
Proof.
  intros; red; intros.
  rewrite D.gsspec. rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
  red; intros; subst ra. specialize (H0 xH). rewrite D.get_bot in H0. inv H0.
  unfold Approx.eq. red; intros; subst a. inv H.
Qed.

Lemma approx_regs_val_list:
  forall ra rs rl,
  regs_match_approx ra rs ->
  val_list_match_approx ge sp (approx_regs ra rl) rs##rl.
Proof.
  induction rl; simpl; intros.
  constructor.
  constructor. apply H. auto.
Qed.

Lemma regs_match_approx_forget:
  forall rs rl ra,
  regs_match_approx ra rs ->
  regs_match_approx (List.fold_left (fun a r => D.set r Unknown a) rl ra) rs.
Proof.
  induction rl; simpl; intros.
  auto.
  apply IHrl.
  red; intros. rewrite D.gsspec. destruct (peq r a). constructor. auto. 
  red; intros; subst ra. specialize (H xH). inv H. 
  unfold Approx.eq, Approx.bot. congruence.
Qed.

(** The correctness of the static analysis follows from the results
  of module [ConstpropOpproof] and the fact that the result of
  the static analysis is a solution of the forward dataflow inequations. *)

Lemma analyze_correct_1:
  forall f pc rs pc' i,
  f.(fn_code)!pc = Some i ->
  In pc' (successors_instr i) ->
  regs_match_approx (transfer gapp f pc (analyze gapp f)!!pc) rs ->
  regs_match_approx (analyze gapp f)!!pc' rs.
Proof.
  unfold analyze; intros.
  set (lu := last_uses f) in *.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' gapp f lu)
                        ((fn_entrypoint f, D.top) :: nil)) as [approxs|] eqn:FIX.
  apply regs_match_approx_increasing with (transfer' gapp f lu pc approxs!!pc).
  eapply DS.fixpoint_solution; eauto.
  unfold transfer'. destruct (lu!pc) as [regs|]. 
  apply regs_match_approx_forget; auto. 
  auto.
  intros. rewrite PMap.gi. apply regs_match_approx_top. 
Qed.

Lemma analyze_correct_3:
  forall f rs,
  regs_match_approx (analyze gapp f)!!(f.(fn_entrypoint)) rs.
Proof.
  intros. unfold analyze. 
  set (lu := last_uses f) in *.
  destruct (DS.fixpoint (fn_code f) successors_instr (transfer' gapp f lu)
                        ((fn_entrypoint f, D.top) :: nil)) as [approxs|] eqn:FIX.
  apply regs_match_approx_increasing with D.top.
  eapply DS.fixpoint_entry; eauto. auto with coqlib.
  apply regs_match_approx_top. 
  intros. rewrite PMap.gi. apply regs_match_approx_top.
Qed.

(** eval_static_load *)

Definition mem_match_approx (m: mem) : Prop :=
  forall id il b,
  gapp!id = Some il -> Genv.find_symbol ge id = Some b ->
  Genv.load_store_init_data ge m b 0 il /\
  Mem.valid_block m b /\
  (forall ofs, ~Mem.perm m b ofs Max Writable) /\
  (*Lenb: This is new: carry around the invariant that it's a readonly*)
  match Genv.find_var_info ge b with
  | Some gv => gvar_readonly gv && negb (gvar_volatile gv) = true /\ il=gvar_init gv
  | None => False
  end.

Lemma eval_load_init_sound:
  forall chunk m b il base ofs pos v,
  Genv.load_store_init_data ge m b base il ->
  Mem.load chunk m b ofs = Some v ->
  ofs = base + pos ->
  val_match_approx ge sp (eval_load_init chunk pos il) v.
Proof.
  induction il; simpl; intros.
(* base case il = nil *)
  auto.
(* inductive case *)
  destruct a.
  (* Init_int8 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  rewrite Mem.load_int8_signed_unsigned in H0. rewrite H in H0. simpl in H0.
  inv H0. decEq. apply Int.sign_ext_zero_ext. compute; auto. 
  congruence.
  eapply IHil; eauto. omega.
  (* Init_int16 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  rewrite Mem.load_int16_signed_unsigned in H0. rewrite H in H0. simpl in H0.
  inv H0. decEq. apply Int.sign_ext_zero_ext. compute; auto. 
  congruence.
  eapply IHil; eauto. omega.
  (* Init_int32 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_int64 *)
  destruct H. destruct (zeq pos 0). subst. rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_float32 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto. destruct (propagate_float_constants tt); simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_float64 *)
  destruct H. destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto. destruct (propagate_float_constants tt); simpl; auto.
  congruence.
  eapply IHil; eauto. omega.
  (* Init_space *)
  eapply IHil; eauto. omega.
  (* Init_symbol *)
  destruct H as [[b' [A B]] C].
  destruct (zeq pos 0). subst.  rewrite Zplus_0_r in H0.
  destruct chunk; simpl; auto.
  unfold symbol_address. rewrite A. congruence.
  eapply IHil; eauto. omega.
Qed.

Lemma eval_static_load_sound:
  forall chunk m addr vaddr v,
  Mem.loadv chunk m vaddr = Some v ->
  mem_match_approx m ->  
  val_match_approx ge sp addr vaddr ->
  val_match_approx ge sp (eval_static_load gapp chunk addr) v.
Proof.
  intros. unfold eval_static_load. destruct addr; simpl; auto. 
  destruct (gapp!i) as [il|] eqn:?; auto.
  red in H1. subst vaddr. unfold symbol_address in H. 
  destruct (Genv.find_symbol ge i) as [b'|] eqn:?; simpl in H; try discriminate.
  exploit H0; eauto. intros [A [B C]]. 
  eapply eval_load_init_sound; eauto. 
  red; auto. 
Qed.

Lemma mem_match_approx_store:
  forall chunk m addr v m',
  mem_match_approx m ->
  Mem.storev chunk m addr v = Some m' ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B [C D]]].
  destruct addr; simpl in H0; try discriminate.
  exploit Mem.store_valid_access_3; eauto. intros [P Q].
  split. apply Genv.load_store_init_data_invariant with m; auto. 
  intros. eapply Mem.load_store_other; eauto. left; red; intro; subst b0.
  eapply C. apply Mem.perm_cur_max. eapply P. instantiate (1 := Int.unsigned i).
  generalize (size_chunk_pos chunk). omega.
  split. eauto with mem.
  split; trivial. intros; red; intros. eapply C. eapply Mem.perm_store_2; eauto.
Qed.

Lemma mem_match_approx_alloc:
  forall m lo hi b m',
  mem_match_approx m ->
  Mem.alloc m lo hi = (m', b) ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B [C D]]].
  split. apply Genv.load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_alloc_unchanged; eauto. 
  split. eauto with mem.
  split; trivial. intros; red; intros. exploit Mem.perm_alloc_inv; eauto. 
  rewrite dec_eq_false. apply C. eapply Mem.valid_not_valid_diff; eauto with mem.
Qed.

Lemma mem_match_approx_free:
  forall m lo hi b m',
  mem_match_approx m ->
  Mem.free m b lo hi = Some m' ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B [C D]]].
  split. apply Genv.load_store_init_data_invariant with m; auto.
  intros. eapply Mem.load_free; eauto.
  destruct (eq_block b0 b); auto. subst b0.
  right. destruct (zlt lo hi); auto. 
  elim (C lo). apply Mem.perm_cur_max. 
  exploit Mem.free_range_perm; eauto. instantiate (1 := lo); omega. 
  intros; eapply Mem.perm_implies; eauto with mem.
  split. eauto with mem.
  split; trivial. intros; red; intros. eapply C. eauto with mem. 
Qed.

Lemma mem_match_approx_extcall:
  forall ef vargs m t vres m',
  mem_match_approx m ->
  external_call ef ge vargs m t vres m' ->
  mem_match_approx m'.
Proof.
  intros; red; intros. exploit H; eauto. intros [A [B [C D]]].
  split. apply Genv.load_store_init_data_invariant with m; auto.
  intros. eapply external_call_readonlyLD; eauto. 
  split. eapply external_call_valid_block; eauto.
  split; trivial. intros; red; intros. elim (C ofs). eapply external_call_max_perm; eauto. 
Qed.

(* Show that mem_match_approx holds initially *)

Definition global_approx_charact (g: genv) (ga: global_approx) : Prop :=
  forall id il b,
  ga!id = Some il -> 
  Genv.find_symbol g id = Some b -> 
  Genv.find_var_info g b = Some (mkglobvar tt il true false).

Lemma make_global_approx_correct:
  forall gdl g ga,
  global_approx_charact g ga ->
  global_approx_charact (Genv.add_globals g gdl) (make_global_approx ga gdl).
Proof.
  induction gdl; simpl; intros.
  auto.
  destruct a as [id gd]. apply IHgdl. 
  red; intros. 
  assert (EITHER: id0 = id /\ gd = Gvar(mkglobvar tt il true false)
               \/ id0 <> id /\ ga!id0 = Some il).
  destruct gd.
  rewrite PTree.grspec in H0. destruct (PTree.elt_eq id0 id); [discriminate|auto].
  destruct (gvar_readonly v && negb (gvar_volatile v)) eqn:?.
  rewrite PTree.gsspec in H0. destruct (peq id0 id).
  inv H0. left. split; auto. 
  destruct v; simpl in *. 
  destruct gvar_readonly; try discriminate.
  destruct gvar_volatile; try discriminate.
  destruct gvar_info. auto.
  auto.
  rewrite PTree.grspec in H0. destruct (PTree.elt_eq id0 id); [discriminate|auto].

  unfold Genv.add_global, Genv.find_symbol, Genv.find_var_info in *;
  simpl in *.
  destruct EITHER as [[A B] | [A B]].
  subst id0. rewrite PTree.gss in H1. inv H1. rewrite PTree.gss. auto.
  rewrite PTree.gso in H1; auto. destruct gd. eapply H; eauto. 
  rewrite PTree.gso. eapply H; eauto.
  red; intros; subst b. eelim Plt_strict; eapply Genv.genv_symb_range; eauto.
Qed.

(*
Theorem mem_match_approx_init:
  forall m, Genv.init_mem prog = Some m -> mem_match_approx m.
Proof.
  intros. 
  assert (global_approx_charact ge gapp).
    unfold ge, gapp.   unfold Genv.globalenv.
    apply make_global_approx_correct.
    red; intros. rewrite PTree.gempty in H0; discriminate.
  red; intros. 
  exploit Genv.init_mem_characterization.
  unfold ge in H0. eapply H0; eauto. eauto. 
  unfold Genv.perm_globvar; simpl.
  intros [A [B C]].
  split. auto. split. eapply Genv.find_symbol_not_fresh; eauto. 
  intros; red; intros. exploit B; eauto. intros [P Q]. inv Q.
Qed.
*)
End ANALYSIS.

(** * Correctness of the code transformation *)

(** We now show that the transformed code after constant propagation
  has the same semantics as the original code. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_symbol_transf.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros; unfold ge, tge, tprog, transf_program. 
  apply Genv.find_var_info_transf.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef gapp f).
Proof.  
  intros.
  exact (Genv.find_funct_transf (transf_fundef gapp) _ _ H).
Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef gapp f).
Proof.  
  intros. 
  exact (Genv.find_funct_ptr_transf (transf_fundef gapp) _ _ H).
Qed.

Lemma sig_function_translated:
  forall f,
  funsig (transf_fundef gapp f) = funsig f.
Proof.
  intros. destruct f; reflexivity.
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
        eexists; eassumption.
     intros [f H].
     destruct (Genv.find_funct_ptr_rev_transf _ _ _ H) as [? [? _]].
     eexists; eassumption.
Qed.         

(*LENB: GFP as in selectionproofEFF*)
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

Definition regs_inject j (rs1 rs2: regset) : Prop :=
  forall r, val_inject j (rs1#r) (rs2#r).

Lemma regs_inject_regs j:
  forall rs1 rs2, regs_inject j rs1 rs2 ->
  forall rl, val_list_inject j rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_inject j:
  forall r v1 v2 rs1 rs2,
  val_inject j v1 v2 -> regs_inject j rs1 rs2 -> regs_inject j (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r); auto.
Qed.

Lemma init_regs_inject j:
  forall rl vl1 vl2,
  val_list_inject j vl1 vl2 ->
  regs_inject j (init_regs vl1 rl) (init_regs vl2 rl).
Proof.
  induction rl; simpl; intros.
  red; intros. rewrite Regmap.gi. auto.
  inv H. red; intros. rewrite Regmap.gi. auto.
  apply set_reg_inject; auto.
Qed.

Lemma transf_ros_correct j:
  forall sp ros rs rs' f approx,
  regs_match_approx sp approx rs ->
  find_function ge ros rs = Some f ->
  regs_inject j rs rs' ->
  (*NEW*) forall (GFP: globalfunction_ptr_inject j),
  find_function tge (transf_ros approx ros) rs' = Some (transf_fundef gapp f).
Proof.
  intros. destruct ros; simpl in *.
(*case 1*)
  generalize (H r); intro MATCH. generalize (H1 r); intro LD.
  destruct (rs#r); simpl in H0; try discriminate.
  destruct (Int.eq_dec i Int.zero); try discriminate.
  inv LD. 
  destruct (GFP _ _ H0). rewrite H2 in H5. inv H5.  rewrite Int.add_zero in H4.
  assert (find_function tge (inl _ r) rs' = Some (transf_fundef gapp f)).
    simpl. rewrite <- H4.
    specialize (function_ptr_translated _ _ H0).
    rewrite Genv.find_funct_find_funct_ptr. trivial.     
  destruct (D.get r approx); auto.
  predSpec Int.eq Int.eq_spec i0 Int.zero; intros; auto.
  simpl in *. unfold symbol_address in MATCH. rewrite symbols_preserved.
  destruct (Genv.find_symbol ge i); try discriminate. 
  inv MATCH. apply function_ptr_translated; auto.
(*case 2*)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); try discriminate.
  apply function_ptr_translated; auto.
Qed.

Lemma const_for_result_correct:
  forall a op sp v m,
  const_for_result a = Some op ->
  val_match_approx ge sp a v ->
  eval_operation tge sp op nil m = Some v.
Proof.
  unfold const_for_result; intros. 
  destruct a; inv H; simpl in H0.
  simpl. congruence.
  destruct (generate_float_constants tt); inv H2.  simpl. congruence.
  simpl. subst v. unfold symbol_address. rewrite symbols_preserved. auto.
  simpl. congruence.
Qed.

Inductive match_pc (f: function) (app: D.t): nat -> node -> node -> Prop :=
  | match_pc_base: forall n pc,
      match_pc f app n pc pc
  | match_pc_nop: forall n pc s pcx,
      f.(fn_code)!pc = Some (Inop s) ->
      match_pc f app n s pcx ->
      match_pc f app (Datatypes.S n) pc pcx
  | match_pc_cond: forall n pc cond args s1 s2 b,
      f.(fn_code)!pc = Some (Icond cond args s1 s2) ->
      eval_static_condition cond (approx_regs app args) = Some b ->
      match_pc f app (Datatypes.S n) pc (if b then s1 else s2).

Lemma match_successor_rec:
  forall f app n pc, match_pc f app n pc (successor_rec n f app pc).
Proof.
  induction n; simpl; intros.
  apply match_pc_base.
  destruct (fn_code f)!pc as [i|] eqn:?; try apply match_pc_base.
  destruct i; try apply match_pc_base.
  eapply match_pc_nop; eauto. 
  destruct (eval_static_condition c (approx_regs app l)) as [b|] eqn:?.
  eapply match_pc_cond; eauto.
  apply match_pc_base.
Qed.

Lemma match_successor:
  forall f app pc, match_pc f app num_iter pc (successor f app pc).
Proof.
  unfold successor; intros. apply match_successor_rec.
Qed.

Section BUILTIN_STRENGTH_REDUCTION.
Variable app: D.t.
Variable sp: val.
Variable rs: regset.
Hypothesis MATCH: forall r, val_match_approx ge sp (approx_reg app r) rs#r.

Lemma annot_strength_reduction_correct:
  forall targs args targs' args' eargs,
  annot_strength_reduction app targs args = (targs', args') ->
  eventval_list_match ge eargs (annot_args_typ targs) rs##args ->
  exists eargs',
  eventval_list_match ge eargs' (annot_args_typ targs') rs##args'
  /\ annot_eventvals targs' eargs' = annot_eventvals targs eargs.
Proof.
  induction targs; simpl; intros.
- inv H. simpl. exists eargs; auto. 
- destruct a.
  + destruct args as [ | arg args0]; simpl in H0; inv H0.
    destruct (annot_strength_reduction app targs args0) as [targs'' args''] eqn:E.
    exploit IHtargs; eauto. intros [eargs'' [A B]].
    assert (DFL:
      exists eargs',
      eventval_list_match ge eargs' (annot_args_typ (AA_arg ty :: targs'')) rs##(arg :: args'')
      /\ annot_eventvals (AA_arg ty :: targs'') eargs' = ev1 :: annot_eventvals targs evl).
    {
      exists (ev1 :: eargs''); split.
      simpl; constructor; auto. simpl. congruence.
    }
    destruct ty; destruct (approx_reg app arg) as [] eqn:E2; inv H; auto.
    * exists eargs''; split; auto; simpl; f_equal; auto.
      generalize (MATCH arg); rewrite E2; simpl; intros E3;
      rewrite E3 in H5; inv H5; auto.
    * destruct (generate_float_constants tt); inv H1; auto. 
      exists eargs''; split; auto; simpl; f_equal; auto.
      generalize (MATCH arg); rewrite E2; simpl; intros E3;
      rewrite E3 in H5; inv H5; auto.
  + destruct (annot_strength_reduction app targs args) as [targs'' args''] eqn:E.
    inv H.
    exploit IHtargs; eauto. intros [eargs'' [A B]].
    exists eargs''; simpl; split; auto. congruence.
  + destruct (annot_strength_reduction app targs args) as [targs'' args''] eqn:E.
    inv H.
    exploit IHtargs; eauto. intros [eargs'' [A B]].
    exists eargs''; simpl; split; auto. congruence.
Qed.

Lemma builtin_strength_reduction_correct:
  forall ef args m t vres m',
  external_call ef ge rs##args m t vres m' ->
  let (ef', args') := builtin_strength_reduction app ef args in
  external_call ef' ge rs##args' m t vres m'.
Proof.
  intros until m'. functional induction (builtin_strength_reduction app ef args); intros; auto.
+ generalize (MATCH r1); rewrite e1; simpl; intros E. simpl in H.
  unfold symbol_address in E. destruct (Genv.find_symbol ge symb) as [b|] eqn:?; rewrite E in H.
  rewrite volatile_load_global_charact. exists b; auto. 
  inv H.
+ generalize (MATCH r1); rewrite e1; simpl; intros E. simpl in H.
  unfold symbol_address in E. destruct (Genv.find_symbol ge symb) as [b|] eqn:?; rewrite E in H.
  rewrite volatile_store_global_charact. exists b; auto. 
  inv H.
+ inv H. exploit annot_strength_reduction_correct; eauto.
  intros [eargs' [A B]]. 
  rewrite <- B. econstructor; eauto. 
Qed.

End BUILTIN_STRENGTH_REDUCTION.

(** The proof of semantic preservation is a simulation argument
  based on "option" diagrams of the following form:
<<
                 n
       st1 --------------- st2
        |                   |
       t|                   |t or (? and n' < n)
        |                   |
        v                   v
       st1'--------------- st2'
                 n'
>>
  The left vertical arrow represents a transition in the
  original RTL code.  The top horizontal bar is the [match_states]
  invariant between the initial state [st1] in the original RTL code
  and an initial state [st2] in the transformed code.
  This invariant expresses that all code fragments appearing in [st2]
  are obtained by [transf_code] transformation of the corresponding
  fragments in [st1].  Moreover, the values of registers in [st1]
  must match their compile-time approximations at the current program
  point.
  These two parts of the diagram are the hypotheses.  In conclusions,
  we want to prove the other two parts: the right vertical arrow,
  which is a transition in the transformed RTL code, and the bottom
  horizontal bar, which means that the [match_state] predicate holds
  between the final states [st1'] and [st2']. *)

Definition sp_preserved (j:meminj) (sp sp':val) := 
    exists b b', sp = Vptr b Int.zero /\ sp' = Vptr b' Int.zero /\ 
                j b = Some(b',0).

Inductive match_stackframes mu: stackframe -> stackframe -> Prop :=
   match_stackframe_intro:
      forall res sp pc rs f rs' (*NEW:*) sp',
      regs_inject (restrict (as_inj mu) (vis mu)) rs rs' ->
      (forall v, regs_match_approx sp (analyze gapp f)!!pc (rs#res <- v)) ->
      (*NEW:*) sp_preserved (local_of mu) sp sp' ->
    match_stackframes mu
        (Stackframe res f sp pc rs)
        (Stackframe res (transf_function gapp f) sp' pc rs').

Lemma match_stackframes_restrict mu X: forall s s'
  (MS: match_stackframes mu s s')
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (WD: SM_wd mu), 
  match_stackframes (restrict_sm mu X) s s'.
Proof. intros.
inv MS; econstructor; eauto.
  rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; intuition.
  rewrite restrict_sm_local'; trivial.
Qed.

Lemma regs_inject_incr j j' rs rs': forall
        (RI: regs_inject j rs rs') (INC: inject_incr j j'),
      regs_inject j' rs rs'.
Proof. intros. red; intros. specialize (RI r).
  eapply val_inject_incr; eassumption.
Qed.

Lemma match_stackframes_intern_incr mu mu' s s': forall 
        (MS: match_stackframes mu s s')
        (INC: intern_incr mu mu') (WD' : SM_wd mu'),
      match_stackframes mu' s s'.
Proof. intros.
inv MS; econstructor; eauto. 
  eapply regs_inject_incr; try eassumption.
    eapply intern_incr_restrict; try eassumption.
destruct H1 as [spb [spb' [SP [SP' LOC]]]].
  exists spb, spb'; intuition. 
  apply INC. eassumption.
Qed.

Lemma list_match_stackframes_intern_incr mu mu' s s': forall 
        (MS: list_forall2 (match_stackframes mu) s s')
        (INC: intern_incr mu mu') (WD' : SM_wd mu'),
      list_forall2 (match_stackframes mu') s s'.
Proof. intros.
induction MS; econstructor; eauto.
  eapply match_stackframes_intern_incr; eassumption.
Qed.

(*NEW: changed use of RTL.state to RTL core plus mem, and added parameter mu*)
Inductive match_states mu : nat -> RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_states_intro:
      forall s sp pc rs m f s' pc' rs' m' app n (*NEW*) sp'
           (MATCH1: regs_match_approx sp app rs)
           (MATCH2: regs_match_approx sp (analyze gapp f)!!pc rs)
           (GMATCH: mem_match_approx m)
           (STACKS: list_forall2 (match_stackframes mu) s s')
           (PC: match_pc f app n pc pc')
           (REGS: regs_inject (restrict (as_inj mu) (vis mu)) rs rs') (*WAS:(REGS: regs_lessdef rs rs')*)
           (MEM: Mem.inject (restrict (as_inj mu) (vis mu)) m m')(*WAS:(MEM: Mem.extends m m')*)
           (*NEW*) (SP: sp_preserved (local_of mu) sp sp'),
      match_states mu n (RTL_State s f sp pc rs) m
                    (RTL_State s' (transf_function gapp f) sp' pc' rs') m'
  | match_states_call:
      forall s f args m s' args' m'
           (GMATCH: mem_match_approx m)
           (STACKS: list_forall2 (match_stackframes mu) s s')
           (*(ARGS: Val.lessdef_list args args')
           (MEM: Mem.extends m m')*)
           (ARGS: val_list_inject (restrict (as_inj mu) (vis mu)) args args')
           (MEM: Mem.inject (restrict (as_inj mu) (vis mu)) m m'),
      match_states mu O (RTL_Callstate s f args) m
                    (RTL_Callstate s' (transf_fundef gapp f) args') m'
  | match_states_return:
      forall s v m s' v' m'
           (GMATCH: mem_match_approx m)
           (STACKS: list_forall2 (match_stackframes mu) s s')
           (*(RES: Val.lessdef v v')
           (MEM: Mem.extends m m'),*)
           (RES: val_inject (restrict (as_inj mu) (vis mu)) v v')
           (MEM: Mem.inject (restrict (as_inj mu) (vis mu)) m m'),
      list_forall2 (match_stackframes mu) s s' ->
      match_states mu O (RTL_Returnstate s v) m
                    (RTL_Returnstate s' v') m'.

Lemma match_states_restrict mu X: forall n s m s' m'
  (MS: match_states mu n s m s' m')
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m X) (WD: SM_wd mu), 
  match_states (restrict_sm mu X) n s m s' m'.
Proof. intros.
induction MS.
eapply match_states_intro. eapply MATCH1. 
    eassumption. eassumption. 
  induction STACKS; econstructor; eauto.
    eapply match_stackframes_restrict; eassumption.
  eassumption. 
  try rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; eauto.
  try rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; eauto.
  rewrite restrict_sm_local'; trivial.
eapply match_states_call ;
  try rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; eauto.
  induction STACKS; econstructor; eauto.
    eapply match_stackframes_restrict; eassumption.
eapply match_states_return;
  try rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; eauto.
  induction STACKS; econstructor; eauto.
    eapply match_stackframes_restrict; eassumption.
  induction STACKS; econstructor; eauto.
    eapply match_stackframes_restrict; eassumption.
Qed. 

Lemma match_states_succ mu:
  forall s f sp pc2 rs m s' rs' m' pc1 i sp',
  f.(fn_code)!pc1 = Some i ->
  In pc2 (successors_instr i) ->
  regs_match_approx sp (transfer gapp f pc1 (analyze gapp f)!!pc1) rs ->
  mem_match_approx m ->
  list_forall2 (match_stackframes mu) s s' ->
  regs_inject (restrict (as_inj mu) (vis mu)) rs rs' ->
  Mem.inject (restrict (as_inj mu) (vis mu)) m m' ->
  (*NEW*) forall (SP: sp_preserved (local_of mu) sp sp'),
  match_states mu O (RTL_State s f sp pc2 rs) m
                (RTL_State s' (transf_function gapp f) sp' pc2 rs') m'.
Proof.
  intros. 
  assert (regs_match_approx sp (analyze gapp f)!!pc2 rs).
    eapply analyze_correct_1; eauto.
  apply match_states_intro with (app := (analyze gapp f)!!pc2); auto.
  constructor.
Qed.

Lemma transf_instr_at:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  (transf_function gapp f).(fn_code)!pc = Some(transf_instr gapp f (analyze gapp f) pc i).
Proof.
  intros. simpl. unfold transf_code. rewrite PTree.gmap. rewrite H. auto. 
Qed.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get ?pc (fn_code ?f) = Some ?instr) |- _ =>
      generalize (transf_instr_at _ _ _ H); simpl
  end.

Definition MATCH n mu c1 m1 c2 m2:Prop :=
  match_states mu n c1 m1 c2 m2 /\
  (mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2) /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
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
  destruct MC as [MS [MRR [RC [PG [GFP [Glob [SMV [WD INJ (* RCT]*)]]]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  eapply match_states_restrict; eassumption.
split. assumption.
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

Lemma val_match_approx_inject mu: forall sp a v 
      (VMA: val_match_approx ge sp a v) 
      sp' (SP: sp_preserved (local_of mu) sp sp')
      cop (CFR: const_for_result a = Some cop)
      (PG:  meminj_preserves_globals ge (as_inj mu)) (WD: SM_wd mu),
     exists v', 
      val_match_approx ge sp' a v' /\ val_inject (as_inj mu) v v'.
Proof.
intros.
destruct a; simpl in *; intuition; try inv CFR.
exists (Vint i); split; eauto.
exists (Vfloat f); split; eauto.
exists (symbol_address ge i i0); split; eauto.
  unfold symbol_address.
  remember (Genv.find_symbol ge i) as d; apply eq_sym in Heqd.
  destruct d; try econstructor.
    apply find_symbol_isGlobal in Heqd. 
    eapply meminj_preserves_globals_isGlobalBlock; eassumption.
  rewrite Int.add_zero. trivial.
destruct SP as [spb [spb' [SP [SP' Jsp]]]]. 
subst; simpl in *. rewrite Int.add_zero_l.
  eexists; split. reflexivity.
  econstructor. eapply local_in_all; eassumption.
  rewrite Int.add_zero; trivial.
Qed.

(*NEW*) Variable hf : I64Helpers.helper_functions.

Lemma MATCH_atExternal: forall n1 mu c1 m1 c2 m2 e vals1 ef_sig
      (MTCH: MATCH n1 mu c1 m1 c2 m2)
      (AtExtSrc: at_external (rtl_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
      Mem.inject (as_inj mu) m1 m2  /\ 
      mem_respects_readonly ge m1 /\ mem_respects_readonly tge m2 /\
(exists vals2 : list val,
   Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
   at_external (rtl_eff_sem hf) c2 = Some (e, ef_sig, vals2) /\
   (forall pubSrc' pubTgt' : block -> bool,
    pubSrc' =
    (fun b : block => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
    pubTgt' =
    (fun b : block => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
    forall nu : SM_Injection,
    nu = replace_locals mu pubSrc' pubTgt' ->
    MATCH n1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2)).
Proof. intros.
destruct MTCH as [MS PRE].
destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
inv MS; simpl in AtExtSrc; inv AtExtSrc.
destruct f; inv H0.
split; trivial. 
split. apply MRR. 
split. apply MRR. 
exists args'. simpl.
destruct (observableEF_dec hf e0); inv H1.
split. apply val_list_inject_forall_inject; auto.
exploit replace_locals_wd_AtExternal; try eassumption.
        apply val_list_inject_forall_inject in ARGS.
        apply forall_vals_inject_restrictD in ARGS. eassumption.
intros WDnu.
intuition.
  subst.
  split. econstructor; try rewrite replace_locals_as_inj; try rewrite replace_locals_vis; eauto.
          clear - STACKS WD MEM WDnu. 
          induction STACKS; econstructor; try eassumption.
            clear IHSTACKS. inv H; econstructor; eauto.
              rewrite replace_locals_as_inj, replace_locals_vis. trivial.
              rewrite replace_locals_local. trivial.
rewrite replace_locals_as_inj, replace_locals_vis, replace_locals_frgnBlocksSrc.
intuition.
(*sm_valid*)
  red. rewrite replace_locals_DOM, replace_locals_RNG. apply SMV.
(*inject_shared*)
  eapply inject_shared_replace_locals; try eassumption.
  subst; trivial.
Qed.

Lemma match_stackframes_replace_externs mu s s' FS FT: forall 
        (MS: match_stackframes mu s s')
        (HFS: forall b, frgnBlocksSrc mu b = true -> FS b = true),
      match_stackframes (replace_externs mu FS FT) s s'.
Proof. intros.
inv MS; econstructor; eauto.
  rewrite replace_externs_as_inj, replace_externs_vis.
  eapply regs_inject_incr; try eassumption.
  red; intros. destruct (restrictD_Some _ _ _ _ _ H2).
  apply restrictI_Some; trivial.
  unfold vis in H4.
  destruct (locBlocksSrc mu); simpl in *; trivial.
  apply (HFS _ H4).

  rewrite replace_externs_local. assumption.
Qed.

Lemma list_match_stackframes_replace_externs mu s s' FS FT: forall 
        (MS: list_forall2 (match_stackframes mu) s s')
        (HFS: forall b, frgnBlocksSrc mu b = true -> FS b = true),
      list_forall2 (match_stackframes (replace_externs mu FS FT)) s s'.
Proof. intros.
induction MS; econstructor; eauto.
  eapply match_stackframes_replace_externs; eassumption.
Qed.

Lemma MATCH_initial: forall v
  (vals1 : list val) c1 (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (Ini :initial_core (rtl_eff_sem hf) ge v vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (*(R : list_norepet (map fst (prog_defs prog)))*)
  (J: forall b1 b2 d, j b1 = Some (b2, d) -> 
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (RdOnly1: mem_respects_readonly ge m1)
  (RdOnly2: mem_respects_readonly tge m2)
  (GFI: globalfunction_ptr_inject j)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists n2 c2,
  initial_core (rtl_eff_sem hf) tge v vals2 = Some c2 /\
  MATCH n2
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2. 
Proof. intros. unfold ge in *. unfold tge in *.
  apply RTL_initial_coreD in Ini.
  destruct Ini as [b [f [V1 [Heqzz [valsHT [valsDEF [valsLEN HC1]]]]]]]. subst.
  specialize (Forall2_Zlength VInj). intros ZlengthEq.
(*  simpl in Ini.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H0. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H1. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1
           (sig_args (funsig (Internal f))) && val_casted.vals_defined vals1). 
  2: solve[intros Heq; rewrite Heq in H0; inv H0].
  intros Heq; rewrite Heq in H0; inv H0.*)
  apply function_ptr_translated in Heqzz. simpl in Heqzz.
  exists O. exists (RTL_Callstate nil (Internal (transf_function gapp f)) vals2).
  split. 
    (*destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A.*) unfold tge in Heqzz. (*rewrite D in Heqzz. inv Heqzz.*)
    unfold rtl_eff_sem; simpl. rewrite Heqzz.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
(*    rewrite D. *)
    assert (val_casted.vals_defined vals2=true) as ->.
    { eapply val_casted.val_list_inject_defined.
      eapply forall_inject_val_list_inject; eauto.
      destruct (val_casted.vals_defined vals1); auto.
      (*rewrite andb_comm in Heq; inv Heq.*) }
    simpl. (* apply andb_true_iff in Heq. destruct Heq. *)
       exploit val_casted.val_list_inject_hastype.
           eapply forall_inject_val_list_inject; eauto. 
           assumption. eassumption. 
       simpl; intros VHTL. rewrite VHTL. simpl.
    rewrite <- ZlengthEq, proj_sumbool_is_true. trivial. apply valsLEN.

    intros CONTRA. solve[elimtype False; auto].
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE_lemma HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  split.
    econstructor; eauto. 
    { red. intros.  
      assert (GAC:  global_approx_charact ge gapp).
        apply make_global_approx_correct. red; intros.
        rewrite PTree.gempty in H1. discriminate.
      specialize (GAC _ _ _ H H0). clear AA BB CC DD EE FF GG.
      destruct (RdOnly1 b0 _ GAC (eq_refl _))as [XX [YY ZZ]]. rewrite GAC. simpl. intuition. }       
    constructor.
    rewrite initial_SM_as_inj.
      unfold vis, initial_SM; simpl.
      apply forall_inject_val_list_inject.
      eapply restrict_forall_vals_inject; try eassumption.
        intros. apply REACH_nil. rewrite H; intuition.
    rewrite initial_SM_as_inj.
      eapply inject_restrict; eassumption.
  rewrite initial_SM_as_inj.
  intuition.
Qed.

Lemma MATCH_afterExternal: forall
      n1 mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH n1 mu st1 m1 st2 m2)
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
       (SEP: globals_separate tge nu nu')
(*       (SEP: sm_inject_separated nu nu' m1 m2)*)
       (WDnu': SM_wd nu')
       (SMvalNu': sm_valid nu' m1' m2')
       (MemInjNu': Mem.inject (as_inj nu') m1' m2')
       (RValInjNu': val_inject (as_inj nu') ret1 ret2)
       (FwdSrc: mem_forward m1 m1')
       (FwdTgt: mem_forward m2 m2')

(*       (MRR': mem_respects_readonly ge m1' /\ mem_respects_readonly tge m2')*)
       (RDO1: RDOnly_fwd m1 m1' (ReadOnlyBlocks ge))
       (RDO2: RDOnly_fwd m2 m2' (ReadOnlyBlocks tge))

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
  exists n1' st1' st2',
  after_external (rtl_eff_sem hf) (Some ret1) st1 =Some st1' /\
  after_external (rtl_eff_sem hf) (Some ret2) st2 = Some st2' /\
  MATCH n1' mu' st1' m1' st2' m2'.
Proof. intros.
destruct MatchMu as [MS PRE].
destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WDmu INJ]]]]]]].
simpl in *. inv MS; simpl in *; inv AtExtSrc.
destruct f; inv H0.
simpl in *. apply eq_sym in AtExtTgt; inv AtExtTgt.
exists O. eexists; eexists.
    split. reflexivity.
    split. reflexivity.
 simpl in *.
destruct (observableEF_dec hf e0); inv H1. inv H0.
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
    subst. clear - INC SEP PG GFP Glob WDmu WDnu'.
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
  clear MRR (*MRR'*). intros b Hb. rewrite REACHAX in Hb. destruct Hb as [L HL].
  generalize dependent b.
  induction L; simpl; intros; inv HL.
     assumption.
  specialize (IHL _ H1); clear H1.
  apply orb_true_iff in IHL.
  remember (locBlocksSrc nu' b') as l.
  destruct l; apply eq_sym in Heql.
  { (*case locBlocksSrc nu' b' = true*)
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
          eapply SMV. unfold DOM, DomSrc. rewrite Heql. intuition.
        destruct (H VB) as [Perm Perm'].
        rewrite H0 in H4. 2: eauto.
        clear H H0.
        remember (locBlocksSrc mu b) as q.
        destruct q; simpl; trivial; apply eq_sym in Heqq.
        assert (Rb : REACH m1 (vis mu) b = true).
           eapply REACH_cons; try eassumption.
           apply REACH_nil. unfold vis. rewrite Heql; trivial.
           eauto.
        specialize (RC _ Rb). unfold vis in RC.
           rewrite Heqq in RC; simpl in *.
        rewrite replace_locals_frgnBlocksSrc in FRGnu'.
        rewrite FRGnu' in RC.
        apply andb_true_iff.  
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ RC). intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ RC). intuition. }
  { (*case locBlocksSrc nu' b' = false*)
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
    eapply REACH_cons; try eassumption. }
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


assert (LL: local_of mu = local_of nu').
  destruct INC. rewrite replace_locals_local in H0. eapply H0. 
assert (WDnuRE: SM_wd
  (replace_externs nu'
     (fun b : block =>
      DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) &&
       REACH m1' (exportedSrc nu' (ret1 :: nil)) b))
     (fun b : block =>
      DomTgt nu' b &&
      (negb (locBlocksTgt nu' b) &&
       REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))).
              eapply replace_externs_wd. assumption.
  clear - WDnu'  RValInjNu' MemInjNu'. intros.  
   apply andb_true_iff in H; destruct H.
             apply andb_true_iff in H0; destruct H0.
             remember (locBlocksSrc nu' b1) as d.
             apply eq_sym in Heqd. destruct d; inv H0.
             exploit (REACH_extern_REACH nu'); try eassumption.
               econstructor. eassumption. econstructor.
            intros [b2 [delta [EXT REXT]]].
              exists b2, delta. split; trivial.
              destruct (extern_DomRng _ WDnu' _ _ _ EXT). 
              unfold DomTgt. rewrite H2, REXT.
              rewrite (extBlocksTgt_locBlocksTgt _ WDnu' _ H2).
              trivial.
            intros. apply andb_true_iff in H; destruct H.
              apply andb_true_iff in H0; destruct H0.
              unfold DomTgt in H.
              destruct (locBlocksTgt nu' b). inv H0. simpl in H; trivial.
assert (II: inject_incr (as_inj (restrict_sm mu (vis mu)))
  (restrict (as_inj nu')
     (fun b : block =>
      locBlocksSrc nu' b
      || DomSrc nu' b &&
         (negb (locBlocksSrc nu' b) &&
          REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
  clear - INC WDnu'.
    specialize (extern_incr_restrict _ _ INC WDnu').
    rewrite replace_locals_as_inj, replace_locals_vis.
    red; intros; clear INC. rewrite restrict_sm_all in H0. 
    apply H in H0. destruct (restrictD_Some _ _ _ _ _ H0).
    apply restrictI_Some; trivial.
    destruct (as_inj_DomRng _ _ _ _ H1 WDnu'). rewrite H3.
    unfold DomSrc in H3; simpl.
    unfold vis in H2. destruct (locBlocksSrc nu' b); simpl in *; trivial.
    apply REACH_nil. unfold exportedSrc.
         apply frgnSrc_shared in H2; trivial.
         solve[rewrite H2; intuition].
  
split.
  assert (MSnu': list_forall2 (match_stackframes nu') s s').
    clear - STACKS INC WDnu'.
    induction STACKS; econstructor; eauto.
      inv H; econstructor; eauto.
      eapply regs_inject_incr; try eassumption.
        red; intros. destruct (restrictD_Some _ _ _ _ _ H).
        apply restrictI_Some.
          apply extern_incr_as_inj in INC; trivial.
            rewrite replace_locals_as_inj in INC.
            apply INC. trivial.
          apply extern_incr_vis in INC; trivial. rewrite <- INC. 
            rewrite replace_locals_vis. trivial. 
      destruct INC as [_ [LOC _]]. rewrite replace_locals_local in LOC.
        rewrite LOC in H2; trivial.
  econstructor; eauto. 
  { (*mem_match_approx m1'*)
    clear - UnchPrivSrc GMATCH FwdSrc (*MRR' *) RDO1 RDO2.  
    rewrite replace_locals_locBlocksSrc, replace_locals_pubBlocksSrc in UnchPrivSrc.
    red; intros. 
    exploit GMATCH; eauto. intros [A [B [C D]]].
    remember (Genv.find_var_info ge b) as v; destruct v; try contradiction; symmetry in Heqv.
    destruct D as [D E]. 
(*    destruct MRR' as [MRR1' _]. specialize (MRR1' _ _ Heqv D). subst il; intuition.*)
    split.
      eapply Genv.load_store_init_data_invariant ; try eassumption. (* apply Genv.load_store_init_data_invariant with m1; auto.*)
      intros. eapply readonly_readonlyLD. apply RDO1.
              unfold ReadOnlyBlocks. rewrite Heqv; eapply D.
      intros. eapply C.
    split. apply FwdSrc; trivial.
    split. intros. intros N. apply FwdSrc in N. apply (C _ N). trivial.
    split; assumption. }
  eapply list_match_stackframes_replace_externs; try eassumption.
    intros.
      unfold DomSrc. 
      rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H),
        (frgnBlocksSrc_locBlocksSrc _ WDnu' _ H); simpl.
      apply REACH_nil. unfold exportedSrc.
         rewrite (frgnSrc_shared _ WDnu' _ H). intuition.
  rewrite replace_externs_as_inj, replace_externs_vis.
    clear - RValInjNu' WDnu'.
    inv RValInjNu'; econstructor; eauto.
    apply restrictI_Some; trivial.
    destruct (as_inj_DomRng _ _ _ _ H WDnu'). rewrite H0.
    destruct (locBlocksSrc nu' b1); simpl in *; trivial.
    apply REACH_nil. unfold exportedSrc.
    apply orb_true_iff; left.
    apply getBlocks_char. eexists; left; reflexivity.
  rewrite replace_externs_as_inj, replace_externs_vis.
    eapply inject_restrict; eassumption.
  eapply list_match_stackframes_replace_externs; try eassumption.
    intros.
      unfold DomSrc. 
      rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H),
        (frgnBlocksSrc_locBlocksSrc _ WDnu' _ H); simpl.
      apply REACH_nil. unfold exportedSrc.
         rewrite (frgnSrc_shared _ WDnu' _ H). intuition.
split. clear - RDO1 RDO2 MRR FwdSrc FwdTgt. destruct MRR.
  split; eapply mem_respects_readonly_forward'; try eassumption. 
clear MRR (*MRR'*).
unfold vis in *.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj in *.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
unfold vis in *.
intuition.
(*last goal: globalfunction_ptr_inject *)
  red; intros. destruct (GFP _ _ H1). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed.

Lemma annot_strength_reduction_observable: forall t a text app targs args,
      (t, a) = annot_strength_reduction app targs args ->
      observableEF hf (EF_annot text t).
intros. simpl; trivial. Qed.

Lemma builtin_strength_reduction_observable: forall app ef args ef' args', 
       (ef', args') = builtin_strength_reduction app ef args ->
       observableEF hf ef = observableEF hf ef'.
Proof. intros.
  destruct ef; destruct args; inv H; simpl; trivial.
  destruct args. 
    destruct (approx_reg app r); inv H1; simpl; trivial.
    inv H1; simpl; trivial. 
  destruct args. 
    inv H1; simpl; trivial. 
  destruct args. 
    destruct (approx_reg app r); inv H1; simpl; trivial.
    inv H1; simpl; trivial.
  remember (annot_strength_reduction app targs nil).
    destruct p. inv H1; simpl. trivial. 
  remember (annot_strength_reduction app targs (r :: args)). 
    destruct p. inv H1; simpl. trivial.
Qed.  

Lemma builtin_strength_reductionD app ef args ef' args':
  builtin_strength_reduction app ef args = (ef', args') ->
  (ef', args') = (ef, args) \/
  (exists chunk r1 symb n1, 
       (ef, args) = (EF_vload chunk, r1::nil) /\
       approx_reg app r1 = G symb n1 /\ 
       (ef', args')= (EF_vload_global chunk symb n1, nil)) \/
  (exists chunk r1 r2 symb n1,
      (ef, args)= (EF_vstore chunk, r1 :: r2 :: nil) /\
      approx_reg app r1 = G symb n1 /\
      (ef',args')= (EF_vstore_global chunk symb n1, r2 :: nil)) \/
  (exists text targs targs',
     ef = EF_annot text targs /\ 
     (targs', args') = annot_strength_reduction app targs args /\
     ef' = EF_annot text targs').
Proof. intros. apply eq_sym in H.
apply R_builtin_strength_reduction_correct in H.
inv H.
right. left. exists chunk, r1, symb, n1.  intuition.
left; trivial.
right. right. left. exists chunk, r1, r2, symb, n1.  intuition.
left; trivial.
right. right. right. exists text, targs, targs'. intuition.
left; trivial.
Qed.

Lemma MATCH_effcore_diagram: 
  forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
       (CS: effstep (rtl_eff_sem hf) ge U1 st1 m1 st1' m1')
      n1 st2 mu m2 
(*      (EffSrc: forall b ofs, U1 b ofs = true -> vis mu b = true)*)
      (MTCH: MATCH n1 mu st1 m1 st2 m2)
      (*(LNR: list_norepet (map fst (prog_defs prog)))*),
exists n2 st2' m2' mu' (U2 : block -> Z -> bool),
    (effstep_plus (rtl_eff_sem hf) tge U2 st2 m2 st2' m2' \/
     (effstep_star (rtl_eff_sem hf) tge U2 st2 m2 st2' m2' /\ (n2 < n1)%nat))
  /\ (*exists n2 mu',*)
     intern_incr mu mu' /\   
      (*new*) globals_separate tge mu mu' /\
     (*sm_inject_separated mu mu' m1 m2 /\*)
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH n2 mu' st1' m1' st2' m2' /\
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
Proof. intros. 
induction CS; 
destruct MTCH as [MSTATE PRE]; inv MSTATE; try (inv PC; try congruence).

{ (* Inop, preserved *)
  rename pc'0 into pc. TransfInstr; intro.
  exists O; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one.
        eapply rtl_effstep_exec_Inop; eauto.
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
  split.
    eapply match_states_succ; eauto. simpl; auto.
    unfold transfer; rewrite H. auto. 
  intuition. }

{ (* Inop, skipped over *)
  rewrite H0 in H; inv H. 
  exists n; eexists; eexists; exists mu; eexists; split.
  right; esplit. apply effstep_star_zero. omega.
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
  split.
    apply match_states_intro with app; auto.
    eapply analyze_correct_1; eauto. simpl; auto. 
    unfold transfer; rewrite H0. auto.
  intuition. }

{ (* Iop *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
    eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis. intuition.
  rename pc'0 into pc. TransfInstr.
  set (app_before := (analyze gapp f)#pc).
  set (a := eval_static_operation op (approx_regs app_before args)).
  set (app_after := D.set res a app_before).
  assert (VMATCH: val_match_approx ge sp a v).  
    eapply eval_static_operation_correct; eauto.
    apply approx_regs_val_list; auto.
  assert (MATCH': regs_match_approx sp app_after rs#res <- v).
    apply regs_match_approx_update; auto.
  assert (MATCH'': regs_match_approx sp (analyze gapp f) # pc' rs # res <- v).
    eapply analyze_correct_1 with (pc := pc); eauto. simpl; auto.
    unfold transfer; rewrite H. auto.  
  destruct (const_for_result a) as [cop|] eqn:?; intros.
  (* constant is propagated *)
  exploit (val_match_approx_inject (restrict_sm mu (vis mu))).
    eassumption.
    rewrite restrict_sm_local'; try eassumption. trivial.
    eassumption.
    eassumption.
    apply restrict_sm_WD; try assumption. trivial.
  intros [v' [VMA' Vinj]].
  eexists; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one. 
    eapply rtl_effstep_exec_Iop; eauto. 
    eapply const_for_result_correct; eauto.
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
  split. 
    eapply match_states_intro with app_after; auto.
    apply match_successor.  
    apply set_reg_inject; try assumption.
    rewrite restrict_sm_all in Vinj; trivial.
  intuition.
  (* operator is strength-reduced *)
  exploit op_strength_reduction_correct. eexact MATCH2. reflexivity. eauto. 
  fold app_before.
  destruct (op_strength_reduction op args (approx_regs app_before args)) as [op' args'].
  intros [v' [EV' LD']].
  destruct SP as [spb [spb' [SP [SP' locSP]]]]. subst; simpl in *.
  exploit (eval_operation_inject PGR); try eapply EV'.
    eapply local_in_all.
      apply restrict_sm_WD; try assumption. trivial.
      rewrite restrict_sm_local'; try eassumption. trivial.
    rewrite restrict_sm_all.
      eapply regs_inject_regs. eassumption.
    rewrite restrict_sm_all.
      eapply inject_restrict; eassumption.
  intros [v'' [EV'' Vinj'']]. 
  rewrite eval_shift_stack_operation in EV''.
  eexists; eexists; eexists; exists mu; eexists; split.
    left. eapply effstep_plus_one.
          eapply rtl_effstep_exec_Iop; eauto.
            erewrite eval_operation_preserved. eexact EV''. exact symbols_preserved.
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
  split.
    apply match_states_intro with app_after; auto.
    apply match_successor.
    apply set_reg_inject; auto.
      rewrite restrict_sm_all in Vinj''.
      eapply Mem.val_lessdef_inject_compose; eassumption.
    exists spb, spb'; intuition.
  intuition. }

{ (* Iload *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
    eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis. intuition.
  rename pc'0 into pc. TransfInstr. 
  set (ap1 := eval_static_addressing addr
               (approx_regs (analyze gapp f) # pc args)).
  set (ap2 := eval_static_load gapp chunk ap1).
  assert (VM1: val_match_approx ge sp ap1 a).
    eapply eval_static_addressing_correct; eauto.
    eapply approx_regs_val_list; eauto.
  assert (VM2: val_match_approx ge sp ap2 v).
    eapply eval_static_load_sound; eauto.
  destruct (const_for_result ap2) as [cop|] eqn:?; intros.
  (* constant-propagated *)
  exploit (val_match_approx_inject (restrict_sm mu (vis mu))).
    eassumption.
    rewrite restrict_sm_local'; try eassumption. trivial.
    eassumption.
    eassumption.
    apply restrict_sm_WD; try assumption. trivial.
  intros [v' [VMA' Vinj]].
  eexists; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one.
     eapply rtl_effstep_exec_Iop; eauto.
       eapply const_for_result_correct; eauto.
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
  split. 
    eapply match_states_succ; eauto. simpl; auto.
    unfold transfer; rewrite H. apply regs_match_approx_update; auto.
    apply set_reg_inject; auto.
    rewrite restrict_sm_all in Vinj; trivial.
  intuition.
  (* strength-reduced *)
  generalize (addr_strength_reduction_correct ge sp (analyze gapp f)!!pc rs
                  MATCH2 addr args (approx_regs (analyze gapp f) # pc args) (refl_equal _)).
  destruct (addr_strength_reduction addr args (approx_regs (analyze gapp f) # pc args)) as [addr' args'].
  rewrite H0. intros P. 
 
 (* assert (ADDR': exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
    eapply eval_addressing_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct ADDR' as [a' [A B]].*)
  destruct SP as [spb [spb' [SP [SP' locSP]]]]. subst; simpl in *.
  exploit (eval_addressing_inject PGR); try eapply P.
    eapply local_in_all.
      apply restrict_sm_WD; try assumption. trivial.
      rewrite restrict_sm_local'; try eassumption. trivial.
    rewrite restrict_sm_all.
      eapply regs_inject_regs. eassumption.  
  intros [a' [A B]]. 
  rewrite eval_shift_stack_addressing in A; simpl in A. rewrite Int.add_zero in A.
  rewrite restrict_sm_all in B.

  (*assert (C: eval_addressing tge sp addr' rs'##args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.*)
  assert (C: eval_addressing tge (Vptr spb' Int.zero) addr' rs' ## args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
  clear A.

  (*exploit Mem.loadv_extends; eauto. intros [v' [D E]].*)
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))).
    eapply inject_restrict; eassumption.
    eassumption.
    eassumption.
  intros [v' [LD' Vinj]].

  eexists; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one.
    eapply rtl_effstep_exec_Iload; eauto.
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
          try rewrite (freshloc_irrefl); intuition.
  split. 
    eapply match_states_succ; eauto. simpl; auto.
    unfold transfer; rewrite H. apply regs_match_approx_update; auto.
    apply set_reg_inject; auto.
    exists spb, spb'; intuition.
  intuition. }

{ (* Istore *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (PGR: meminj_preserves_globals ge (as_inj (restrict_sm mu (vis mu)))).
    eapply restrict_sm_preserves_globals; try eassumption.
      unfold vis. intuition.
  rename pc'0 into pc. TransfInstr.
  generalize (addr_strength_reduction_correct ge sp (analyze gapp f)!!pc rs
                  MATCH2 addr args (approx_regs (analyze gapp f) # pc args) (refl_equal _)).
  destruct (addr_strength_reduction addr args (approx_regs (analyze gapp f) # pc args)) as [addr' args'].
  intros P Q. rewrite H0 in P.
  (*assert (ADDR': exists a', eval_addressing ge sp addr' rs'##args' = Some a' /\ Val.lessdef a a').
    eapply eval_addressing_lessdef; eauto. eapply regs_lessdef_regs; eauto.
  destruct ADDR' as [a' [A B]].*)
  destruct SP as [spb [spb' [SP [SP' locSP]]]]. subst; simpl in *.
  exploit (eval_addressing_inject PGR); try eapply P.
    eapply local_in_all.
      apply restrict_sm_WD; try assumption. trivial.
      rewrite restrict_sm_local'; try eassumption. trivial.
    rewrite restrict_sm_all.
      eapply regs_inject_regs. eassumption.  
  intros [a' [A B]]. 
  rewrite eval_shift_stack_addressing in A; simpl in A. rewrite Int.add_zero in A.
  rewrite restrict_sm_all in B.

  (*assert (C: eval_addressing tge sp addr' rs'##args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.*)
  assert (C: eval_addressing tge (Vptr spb' Int.zero) addr' rs' ## args' = Some a').
    rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.

  (*exploit Mem.storev_extends; eauto. intros [m2' [D E]].*)
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))).
    eapply inject_restrict; eassumption.
    eassumption.
    eassumption.
    eapply REGS.
  intros [m2' [ST' Minj2]].

  eexists; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one.
    eapply rtl_effstep_exec_Istore; eauto.
  assert (SMV': sm_valid mu m' m2').
    split; intros. 
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
  exploit (Mem.storev_mapped_inject (as_inj mu)).
    eassumption.
    eassumption.
    eapply val_inject_incr; try eassumption.
     apply restrict_incr.
    eapply val_inject_incr; try eapply REGS.
     apply restrict_incr.
  intros [m2'' [ST'' Minj2'']].
  rewrite ST' in ST''. apply eq_sym in ST''; inv ST''.
  destruct MRR as [MRR1 MRR2].
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b; 
        try rewrite (storev_freshloc _ _ _ _ _ H1);
        try rewrite (storev_freshloc _ _ _ _ _ ST'); intuition.
  split.  
    eapply match_states_succ; eauto. simpl; auto.
    unfold transfer; rewrite H. auto. 
    eapply mem_match_approx_store; eauto.
    exists spb, spb'; intuition.
  split. destruct a; inv H1. destruct a'; inv ST'.
    split; eapply mem_respects_readonly_forward; try eassumption.
      eapply store_forward; eassumption.
      intros; eapply store_readonly; try eassumption. eapply MRR1; eassumption.

      eapply store_forward; eassumption.
      intros; eapply store_readonly; try eassumption. eapply MRR2; eassumption.
      
  intuition.
  destruct a; inv H1.
        eapply REACH_Store; try eassumption. 
          inv B. destruct (restrictD_Some _ _ _ _ _ H4); trivial.
          intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
                  destruct Hoff; try contradiction.
                  specialize (REGS src). rewrite H1 in REGS; inv REGS.
                  destruct (restrictD_Some _ _ _ _ _ H6); trivial.
   apply StoreEffectD in H2. destruct H2 as [i [VADDR' _]]. subst.
     destruct a; inv H1. inv B. eapply visPropagateR; eassumption.
   eapply StoreEffect_PropagateLeft; eassumption. }

{ (* Icall *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  rename pc'0 into pc.
  exploit transf_ros_correct; eauto. 
    apply restrict_GFP_vis; trivial.
  intro FIND'.
  TransfInstr; intro.
  eexists; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one.
    eapply rtl_effstep_exec_Icall; eauto.
      apply sig_function_translated; auto.
  destruct MRR as [MRR1 MRR2].
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality b;
          try rewrite (freshloc_irrefl); intuition. 
  split.   
    constructor; auto. constructor; auto.
    econstructor; eauto. 
    intros. eapply analyze_correct_1; eauto. simpl; auto.
    unfold transfer; rewrite H.
    apply regs_match_approx_update; auto. simpl. auto.
    apply regs_inject_regs; auto.
  intuition. } 

{ (* Itailcall *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  destruct SP as [spb [spb' [SP [SP' locSP]]]]. inv SP.
  exploit free_parallel_inject; try eapply MEM. 
     eassumption.
     eapply restrictI_Some.
     eapply local_in_all; try eassumption.
     eapply local_of_vis; eassumption.
  simpl. rewrite Zplus_0_r. intros [m2' [FR2 MinjR']].
  exploit free_parallel_inject; try eapply INJ.
     eassumption.
     eapply local_in_all; try eassumption.
  simpl. rewrite Zplus_0_r. intros [m2'' [FR2' Minj']].
  rewrite FR2 in FR2'. apply eq_sym in FR2'. inv FR2'.
  exploit transf_ros_correct; eauto.
    apply restrict_GFP_vis; trivial.
  intros FIND'.
  TransfInstr; intro.
  eexists; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one. 
    eapply rtl_effstep_exec_Itailcall; eauto.
    apply sig_function_translated; auto.
  assert (SMV': sm_valid mu m' m2').
         split; intros;
           eapply Mem.valid_block_free_1; try eassumption;
           eapply SMV; assumption.
  destruct MRR as [MRR1 MRR2].
  intuition.
    apply intern_incr_refl. 
    apply gsep_refl.
(*    apply sm_inject_separated_same_sminj.*)
    apply sm_locally_allocatedChar.
      repeat split; extensionality b;
        try rewrite (freshloc_free _ _ _ _ _  H2);
        try rewrite (freshloc_free _ _ _ _ _  FR2); intuition.
  split.
    constructor; auto.  
    eapply mem_match_approx_free; eauto.
    apply regs_inject_regs; auto.
  split.
    split; eapply mem_respects_readonly_forward; try eassumption.
      eapply free_forward; eassumption.
      intros; eapply free_readonly; try eassumption. eapply MRR1; eassumption.

      eapply free_forward; eassumption.
      intros; eapply free_readonly; try eassumption. eapply MRR2; eassumption.
  intuition.
    eapply REACH_closed_free; eassumption.
    apply FreeEffectD in H3. destruct H3 as [? [VB Arith2]]; subst.
      unfold visTgt. destruct (local_DomRng _ WD _ _ _ locSP).
      rewrite H4; intuition. 
    simpl in H3.
      eapply FreeEffect_PropagateLeft; try eassumption.
        eapply local_in_all; eassumption.
        eapply local_of_vis; eassumption. } 

{ (* Ibuiltin *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  rename pc'0 into pc.
Opaque builtin_strength_reduction.
  exploit builtin_strength_reduction_correct; eauto. 
  TransfInstr.
  remember (builtin_strength_reduction (analyze gapp f)#pc ef args) as RED.
  destruct RED as [ef' args'].
  intros P Q.
  rewrite (builtin_strength_reduction_observable _ _ _ _ _ HeqRED) in H1. 
  exploit (inlineable_extern_inject _ _ GDE_lemma ); try eapply Q.
     apply symbols_preserved.
      eassumption. eassumption.
      eassumption. eassumption.
      eapply H1.
      eassumption. eassumption.
      apply regs_inject_regs. eassumption.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [GlobSep [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]]].
(*  exploit external_call_mem_extends; eauto. 
  instantiate (1 := rs'##args'). apply regs_lessdef_regs; auto.
  intros [v' [m2' [A [B [C D]]]]].*)
  eexists; eexists; eexists; exists mu'; eexists; split.
  left. eapply effstep_plus_one.
    eapply rtl_effstep_exec_Ibuiltin. eauto. 
    eapply external_call_symbols_preserved; eauto.
    apply H1.
    (* exact symbols_preserved. exact varinfo_preserved.*)
  split; trivial.
  split. eapply gsep_domain_eq. eassumption. apply GDE_lemma.
  destruct MRR as [MRR1 MRR2].
  intuition.
  { (*MATCH*) 
    split.
      eapply match_states_succ; eauto. simpl; auto.
      unfold transfer; rewrite H. 
      apply regs_match_approx_update; auto. simpl; auto.
      eapply mem_match_approx_extcall; eauto. 
      eapply list_match_stackframes_intern_incr; eauto.
      apply set_reg_inject; auto.
      eapply regs_inject_incr; try eassumption. 
        eapply intern_incr_restrict; eassumption.
      eapply inject_restrict; eassumption.
      destruct SP as [spb [spb' [SP [SP' locSP]]]].
        exists spb, spb'; intuition. eapply INCR; eassumption.
    split.
      split; eapply mem_respects_readonly_forward; try eassumption.
        eapply external_call_mem_forward; eassumption.
        intros; eapply external_call_readonly; try eassumption. eapply MRR1; eassumption.

        eapply external_call_mem_forward; eassumption.
        intros; eapply external_call_readonly; try eassumption. eapply MRR2; eassumption.
    intuition.
    apply intern_incr_as_inj in INCR; trivial.
      apply sm_inject_separated_mem in SEPARATED; trivial.
      eapply meminj_preserves_incr_sep; try eapply PG.
        eassumption. eassumption. eassumption. 
    red; intros b ff Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
    assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. eapply (Glob _ H2). }
  unfold transf_code in P.
  eapply (@BuiltinEffect_Propagate). eapply Q.
    eapply regs_inject_regs; eassumption. eassumption. eassumption. eassumption.
  clear UNMAPPED OUTOFREACH H1. simpl in P.
  exploit transf_instr_at. eassumption. intros. simpl in H1.
  rewrite P in H1; clear P.
  assert (builtin_strength_reduction (analyze gapp f) # pc ef args = (ef', args')).
    remember (builtin_strength_reduction (analyze gapp f) # pc ef args) as d.
    destruct d. inv H1. trivial.  
  clear H1.
  destruct (builtin_strength_reductionD _ _ _ _ _ H4)
     as [EQ | [VLD | [VST | ANNOT]]]; clear H4.
  inv EQ. eapply (@BuiltinEffect_Propagate). eapply Q.
    eapply regs_inject_regs; eassumption. eassumption. eassumption. eassumption. eassumption.
  destruct VLD as [ch [r1 [symb [nn [EQ [APP EQ']]]]]].
    inv EQ; inv EQ'. unfold BuiltinEffect in H2. simpl in H2. inv H2.
  destruct VST as [ch [r1 [r2 [symb [nn [EQ [APP EQ']]]]]]].
    inv EQ; inv EQ'. unfold BuiltinEffect in H2. simpl in H2. inv H2.
  destruct ANNOT as [text [targs [targs' [EF [AS EF']]]]].
    subst. unfold BuiltinEffect in H2. simpl in H2. inv H2.   
  (*eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.*) }

{ (* Icond, preserved *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  rename pc'0 into pc. TransfInstr.
  generalize (cond_strength_reduction_correct ge sp (analyze gapp f)#pc rs m
                    MATCH2 cond args (approx_regs (analyze gapp f) # pc args) (refl_equal _)).
  destruct (cond_strength_reduction cond args (approx_regs (analyze gapp f) # pc args)) as [cond' args'].
  intros EV1 TCODE.
  exists O, (RTL_State s' (transf_function gapp f) sp' (if b then ifso else ifnot) rs'), m2, mu; eexists; split.
  left. apply effstep_plus_one.
    destruct (eval_static_condition cond (approx_regs (analyze gapp f) # pc args)) eqn:?.
    (*case 1*)
      assert (eval_condition cond rs ## args m = Some b0).
        eapply eval_static_condition_correct; eauto. eapply approx_regs_val_list; eauto.
      assert (b = b0) by congruence. subst b0.
      destruct b; eapply rtl_effstep_exec_Inop; eauto. 
    (*case 2*)
      rewrite H0 in EV1.
      exploit eval_condition_inject; try eapply EV1.
        eapply regs_inject_regs; try eassumption. 
        eapply inject_restrict; eassumption.
      intros.       
      eapply rtl_effstep_exec_Icond; eauto.
      (*WAS: eapply eval_condition_lessdef with (vl1 := rs##args'); eauto. eapply regs_lessdef_regs; eauto. congruence.*)
  destruct MRR as [MRR1 MRR2].
  intuition. 
      apply intern_incr_refl. 
      apply gsep_refl.
(*      apply sm_inject_separated_same_sminj.*)
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
          try rewrite (freshloc_irrefl); intuition. 
  split.   
    eapply match_states_succ; eauto. 
    destruct b; simpl; auto.
    unfold transfer; rewrite H. auto.
  intuition. }

{ (* Icond, skipped over *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  rewrite H1 in H; inv H. 
  assert (EV: eval_condition cond rs ## args m = Some b0).
    eapply eval_static_condition_correct; eauto. eapply approx_regs_val_list; eauto.
  assert (b = b0) by congruence. subst b0. clear H0.
  exploit eval_condition_inject; try eapply EV.
    eapply regs_inject_regs; try eassumption. 
    eapply inject_restrict; eassumption.
  intros EV'.       
  eexists n; eexists; eexists; exists mu; eexists; split.
  right; split. eapply effstep_star_zero. omega.
  destruct MRR as [MRR1 MRR2].
  intuition. 
    apply intern_incr_refl. 
    apply gsep_refl.
(*    apply sm_inject_separated_same_sminj.*)
    apply sm_locally_allocatedChar.
    repeat split; extensionality bb;
        try rewrite (freshloc_irrefl); intuition. 
  split. 
    assert (MATCH': regs_match_approx sp (analyze gapp f) # (if b then ifso else ifnot) rs).
      eapply analyze_correct_1; eauto. destruct b; simpl; auto.
      unfold transfer; rewrite H1; auto.
    econstructor; eauto. constructor.
  intuition. } 

{ (* Ijumptable *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  rename pc'0 into pc.
  assert (A: (fn_code (transf_function gapp f))!pc = Some(Ijumptable arg tbl)
             \/ (fn_code (transf_function gapp f))!pc = Some(Inop pc')).
  TransfInstr. destruct (approx_reg (analyze gapp f) # pc arg) eqn:?; auto.
  generalize (MATCH2 arg). unfold approx_reg in Heqt. rewrite Heqt. rewrite H0. 
  simpl. intro EQ; inv EQ. rewrite H1. auto.
  assert (B: rs'#arg = Vint n).
  generalize (REGS arg); intro LD; inv LD; congruence.
  exists O, (RTL_State s' (transf_function gapp f) sp' pc' rs'), m2, mu; eexists; split.
  left. apply effstep_plus_one.
        destruct A. 
          eapply rtl_effstep_exec_Ijumptable; eauto.
          eapply rtl_effstep_exec_Inop; eauto.
  clear A.
  destruct MRR as [MRR1 MRR2].
  intuition. 
    apply intern_incr_refl. 
    apply gsep_refl.
(*    apply sm_inject_separated_same_sminj.*)
    apply sm_locally_allocatedChar.
    repeat split; extensionality bb;
        try rewrite (freshloc_irrefl); intuition. 
  split.
    eapply match_states_succ; eauto.
    simpl. eapply list_nth_z_in; eauto.
    unfold transfer; rewrite  H; auto.
  intuition. }

{ (* Ireturn *)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].

  (*WAS:exploit Mem.free_parallel_extends; eauto. intros [m2' [A B]].*)
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  destruct SP as [spb [spb' [B [B' Rsp]]]]; subst. inv B. 
  exploit free_parallel_inject; eauto.
    apply restrictI_Some.
      apply local_in_all; eassumption.
      eapply local_of_vis; eassumption. 
  simpl; rewrite Zplus_0_r; intros [m'' [P Q]].
  assert (SMV': sm_valid mu m' m'').
        split; intros;
          eapply Mem.valid_block_free_1; try eassumption;
          eapply SMV; assumption.

  exists O, (RTL_Returnstate s' (regmap_optget or Vundef rs')), m'', mu; eexists; split.
  left. eapply effstep_plus_one. 
     eapply rtl_effstep_exec_Ireturn; eauto. TransfInstr; auto.
  destruct MRR as [MRR1 MRR2].
  intuition. 
    apply intern_incr_refl. 
    apply gsep_refl.
(*    apply sm_inject_separated_same_sminj.*)
    apply sm_locally_allocatedChar.
    repeat split; extensionality bb;
        try rewrite (freshloc_free _ _ _ _ _  P);
        try rewrite (freshloc_free _ _ _ _ _  H0); intuition.
  split.
    constructor; auto.
    eapply mem_match_approx_free; eauto.
    destruct or; simpl; auto.
  split.
      split; eapply mem_respects_readonly_forward; try eassumption.
        eapply free_forward; eassumption.
        intros; eapply free_readonly; try eassumption. eapply MRR1; eassumption.

        eapply free_forward; eassumption.
        intros; eapply free_readonly; try eassumption. eapply MRR2; eassumption.
  intuition.
    eapply REACH_closed_free; eassumption.
    eapply free_free_inject; try eassumption.
      simpl. rewrite Zplus_0_r. apply P.
      eapply local_in_all; eassumption.
    eapply FreeEffectD in H1. destruct H1 as [? [VB Arith]]; subst. 
       destruct (local_DomRng _ WD _ _ _ Rsp) as [DS DT].
       unfold visTgt; rewrite DT; intuition.
    simpl in H1.  
      eapply FreeEffect_PropagateLeft; try eassumption.
        eapply local_in_all; eassumption.
        eapply local_of_vis; eassumption. } 

{ (* internal function *)
  (*WAS: exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m2' [A B]].*)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD INJ]]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit (alloc_parallel_intern mu); try eassumption. apply Zle_refl. apply Zle_refl. 
      intros [mu' [m2' [b' [Alloc' [INJ' [IntInc' [HA [HB [HC [HD [HE [HF HG]]]]]]]]]]]]. 
  
  simpl. unfold transf_function.
  exists O; eexists; eexists; exists mu'; eexists; split.
  left. eapply effstep_plus_one. 
    eapply rtl_effstep_exec_function_internal; simpl; eauto.
  destruct MRR as [MRR1 MRR2].
  intuition.
  eapply gsep_domain_eq. eapply intern_incr_globals_separate; eauto.
                         apply GDE_lemma.
  (*MATCH*)
    split. simpl. econstructor; eauto.
      apply analyze_correct_3; auto.
      apply analyze_correct_3; auto.
      eapply mem_match_approx_alloc; eauto.
      eapply list_match_stackframes_intern_incr; eassumption.
      instantiate (1 := f). constructor.
      apply init_regs_inject; auto.
      eapply val_list_inject_incr; try eassumption.
        eapply intern_incr_restrict; eassumption.
      eapply inject_restrict; eassumption.
      exists stk, b'; intuition.
        destruct (joinD_Some _ _ _ _ _ HA) as [EXT | [EXT LOC]]; trivial.
        assert (EXT':  extern_of mu =  extern_of mu') by eapply IntInc'.
        rewrite <- EXT' in EXT; clear EXT'.
        apply extern_in_all in EXT.
        destruct (as_inj_DomRng _ _ _ _ EXT WD) as [DS DT].
        exfalso. eapply (Mem.fresh_block_alloc _ _ _ _ _ H).
        apply SMV. apply DS.
    split.
      split; eapply mem_respects_readonly_forward; try eassumption.
        eapply alloc_forward; eassumption.
        intros; eapply alloc_readonly; try eassumption. eapply MRR1; eassumption.

        eapply alloc_forward; eassumption.
        intros; eapply alloc_readonly; try eassumption. eapply MRR2; eassumption.
    intuition.
    eapply meminj_preserves_incr_sep_vb with (m0:=m)(tm:=m2). eapply PG.
      intros. apply as_inj_DomRng in H1.
              split; eapply SMV; eapply H1.
        assumption.
      apply intern_incr_as_inj; eassumption.
      apply sm_inject_separated_mem; assumption.
    red; intros b ff Hb. destruct (GFP _ _ Hb).
         split; trivial.
         eapply intern_incr_as_inj; eassumption.
    assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc'.
          apply Glob in H1. rewrite <-FF; trivial. }

  (* external function - no case
  exploit external_call_mem_extends; eauto. 
  intros [v' [m2' [A [B [C D]]]]].
  simpl. left; econstructor; econstructor; split.
  eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto.
  eapply mem_match_approx_extcall; eauto.*)

{ (*external function - helpers*)
  destruct PRE as [MRR [RC [PG [GFP [Glob [SMV [WD MINJ]]]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  specialize (EFhelpers _ _ OBS); intros.
  exploit (inlineable_extern_inject _ _ GDE_lemma);
    try eapply ARGS; try eassumption.
    apply symbols_preserved.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [Gsep [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]]].
  exists O; eexists; eexists. exists mu'; eexists.
  split. left. eapply effstep_plus_one. eapply rtl_effstep_exec_function_external; eauto.
  split; trivial.
  split. eapply gsep_domain_eq. eassumption. apply GDE_lemma.
  split; trivial.
  split.
  { (*MATCH*)
     destruct MRR as [MRR1 MRR2].
     split; intuition.
       constructor; auto.
         eapply mem_match_approx_extcall; eauto.
         eapply list_match_stackframes_intern_incr; eassumption.
         eapply inject_restrict; eassumption.
         eapply list_match_stackframes_intern_incr; eassumption.
       eapply mem_respects_readonly_forward; try eassumption.
         eapply external_call_mem_forward; eassumption.
         intros; eapply external_call_readonly; try eassumption. eapply MRR1; eassumption.
       eapply mem_respects_readonly_forward; try eassumption.
         eapply external_call_mem_forward; eassumption.
         intros; eapply external_call_readonly; try eassumption. eapply MRR2; eassumption.
       eapply meminj_preserves_incr_sep_vb with (m0:=m)(tm:=m2). eapply PG.
         intros. apply as_inj_DomRng in H1.
              split; eapply SMV; eapply H1.
         assumption.
         apply intern_incr_as_inj; eassumption.
         apply sm_inject_separated_mem; assumption.
       red; intros b ff Hb. destruct (GFP _ _ Hb).
         split; trivial.
         eapply intern_incr_as_inj; eassumption.
       assert (FF: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          apply Glob in H1. rewrite <-FF; trivial. }
  split; trivial.
  split; trivial.
  intros. eapply BuiltinEffect_Propagate; eassumption. }
{ (* return *)
  inv H5. inv H1. 
  exists O; eexists; eexists; exists mu; eexists; split.
  left. eapply effstep_plus_one. 
    eapply rtl_effstep_exec_return; eauto. 
  intuition. 
    apply intern_incr_refl.
    apply gsep_refl. 
(*    apply sm_inject_separated_same_sminj.*)
    apply sm_locally_allocatedChar.
    repeat split; extensionality bb;
        try rewrite (freshloc_irrefl); intuition. 
  split.
    econstructor; eauto. constructor.
     apply set_reg_inject; auto.
  intuition. } 
Qed.

Theorem transl_program_correct:
SM_simulation.SM_simulation_inject (rtl_eff_sem hf)
  (rtl_eff_sem hf) ge tge.
Proof.
econstructor.
(*well_founded*)
   apply lt_wf.
(*SM_wd*)
  eapply MATCH_wd.
(*genvs_domain_eq*)
  apply GDE_lemma.
(*ginfos_preserved*)
 split; red; intros.
   rewrite varinfo_preserved. apply gvar_info_refl.
   rewrite symbols_preserved. trivial.
(*match_genv*)
  eapply MATCH_PG. 
(*match_reach_closed*)
  apply MATCH_RC.
(*match_restrict
  apply MATCH_restrict.*)
(*match_valid*)
  apply MATCH_valid.
{ (*match_initial*)
   intros. eapply MATCH_initial; eauto. }
{ (*effcore_diagram*)
  intros. exploit MATCH_effcore_diagram; try eassumption.
  intros [n2 [st2' [m2' [mu' [U2 [CS2 HH]]]]]].
  exists st2', m2', n2, mu'.
  repeat (split; try solve [eapply HH]).
  exists U2. 
  split. assumption. intros. apply HH. eassumption. }
{ (*halted*) 
  intros. destruct H as [MC [MRR [RC [PG [GFP [GF [VAL [WD INJ]]]]]]]]. 
    destruct c1; inv H0. destruct stack; inv H1.
    inv MC. inv H5. exists v'. intuition. }
{ (*atExternal*)
   apply MATCH_atExternal. }
{ (*afterExternal*)
  intros.
   eapply MATCH_afterExternal; try apply MemInjMu; try eassumption. }
Qed.

End PRESERVATION.
