Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Registers.
Require Import Inlining.
Require Import Inliningspec.
Require Import RTL.

Require Import mem_lemmas.
Require Import core_semantics.
Require Import reach.
Require Import effect_semantics.
Require Import StructuredInjections.
(*Require Import effect_simulations.*)
Load effect_simulation.
Require Import effect_properties.
Require Import effect_simulations_lemmas.


Require Export Axioms.
Require Import RTL_coop.
Require Import RTL_eff.

Load Santiago_tactics.

(* The rewriters *)
Hint Rewrite vis_restrict_sm: restrict.
Hint Rewrite restrict_sm_all: restrict.
Hint Rewrite restrict_sm_frgnBlocksSrc: restrict.

Variable SrcProg: program.
Variable TrgProg: program.
About transf_program.
Hypothesis TRANSF: transf_program SrcProg = OK TrgProg.
Let ge : genv := Genv.globalenv SrcProg.
Let tge : genv := Genv.globalenv TrgProg.
Let fenv := funenv_program SrcProg.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  intros. apply Genv.find_symbol_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. apply Genv.find_var_info_transf_partial with (transf_fundef fenv). apply TRANSF.
Qed.

Lemma functions_translated:
  forall (v: val) (f:  fundef),
    Genv.find_funct ge v = Some f ->
    exists f', Genv.find_funct tge v = Some f' /\ transf_fundef fenv f = OK f'.
Proof.
  eapply (Genv.find_funct_transf_partial (transf_fundef fenv) _ TRANSF).
Qed.
Lemma function_ptr_translated:
  forall (b: block) (f:  fundef),
    Genv.find_funct_ptr ge b = Some f ->
    exists f', Genv.find_funct_ptr tge b = Some f' /\ transf_fundef fenv f = OK f'.
Proof.
  eapply (Genv.find_funct_ptr_transf_partial (transf_fundef fenv) _ TRANSF).
Qed.
Lemma sig_function_translated:
  forall f f', transf_fundef fenv f = OK f' ->  funsig f' =  funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto. 
  auto.
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
       admit.
    (*rewrite varinfo_preserved. intuition.*)
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. xomega. 
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
    context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. xomega.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq. 
  xomega.
Qed.

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> val_inject F rs#r rs'#(sreg ctx r))
  /\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ val_inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; xomega.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r). 
  left. rewrite B; auto. 
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
    agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> val_list_inject F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
    agree_regs F ctx rs rs' ->
    val_inject F v v' ->
    Ple r ctx.(mreg) ->
    agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto. 
  rewrite Regmap.gso. auto. xomega. 
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
    agree_regs F ctx rs rs' ->
    agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto. 
  rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
    agree_regs F ctx rs rs' ->
    agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec. 
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
    agree_regs F ctx rs rs1 ->
    (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
    agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto. 
  apply shiftpos_above.
  eapply Plt_le_trans. apply shiftpos_below. xomega.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
    agree_regs F ctx rs1 rs2 ->
    inject_incr F F' ->
    agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto. 
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto. 
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
    val_list_inject F vl vl' ->
    (forall r, In r rl -> Ple r ctx.(mreg)) ->
    agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto. 
Qed.


(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
                                 forall rdsts rsrcs vl pc1 pc2 rs1,
                                   tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
                                   (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
                                   list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
                                   exists rs2,
                                     star  step tge (State stk f sp pc1 rs1 m)
                                           E0 (State stk f sp pc2 rs2 m)
                                     /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
                                     /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
  (* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  (* rdsts = a :: rdsts *)
  inv H2. inv H0. 
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply  exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

Lemma tr_moves_init_regs':
  forall F hf stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
                                 forall rdsts rsrcs vl pc1 pc2 rs1,
                                   tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
                                   (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
                                   list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
                                   exists rs2, core_semantics_lemmas.corestep_star (rtl_eff_sem hf) tge
                                                             (RTL_State stk f sp pc1 rs1) m
                                                             (RTL_State stk f sp pc2 rs2) m
                                               /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
                                               /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
  (* rdsts = nil *)
  inv H0. exists rs1; split. apply core_semantics_lemmas.corestep_star_zero. split. apply agree_regs_init. auto.
  (* rdsts = a :: rdsts *)
  inv H2. inv H0. 
  exists rs1; split. apply core_semantics_lemmas.corestep_star_zero. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply core_semantics_lemmas.corestep_star_trans; eauto. 
  eapply core_semantics_lemmas.corestep_star_one.
eapply  rtl_corestep_exec_Iop; eauto.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

Lemma tr_moves_init_regs_eff:
  forall F hf stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
                                    forall rdsts rsrcs vl pc1 pc2 rs1,
                                      tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
                                      (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
                                      list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
                                      exists rs2,
                                        effstep_star (rtl_eff_sem hf) tge EmptyEffect
                                                     (RTL_State stk f sp pc1 rs1) m
                                                     (RTL_State stk f sp pc2 rs2) m
                                        /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
                                        /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
  (* rdsts = nil *)
  inv H0. exists rs1; split. apply effstep_star_zero. split. apply agree_regs_init. auto.
  (* rdsts = a :: rdsts *)
  inv H2. inv H0. 
  exists rs1; split. apply effstep_star_zero. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. 
  eapply effstep_star_trans'; eauto.
  eapply effstep_star_one.
  eapply  rtl_effstep_exec_Iop; eauto.
  extensionality x. reflexivity.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply sym_not_equal. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.


(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
    range_private F m m' sp lo hi ->
    (forall b delta ofs,
       F1 b = Some(sp, delta) ->
       Mem.perm m1 b ofs Max Nonempty ->
       lo <= ofs + delta < hi ->
       F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
    (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
    range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto.
  intros; red; intros. exploit H0; eauto. omega. intros [P Q]. 
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
    range_private F m m' sp lo hi ->
    Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
    range_private F m m' sp' base hi ->
    Mem.alloc m 0 sz = (m1, sp) ->
    F1 sp = Some(sp', base) ->
    (forall b, b <> sp -> F1 b = F b) ->
    range_private F1 m1 m' sp' (base + Zmax sz 0) hi.
Proof.
  intros; red; intros. 
  exploit (H ofs). generalize (Zmax2 sz 0). omega. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4. 
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); omega.
  rewrite H2 in H4; auto. eelim B; eauto. 
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
    range_private F m m' sp (base + Zmax sz 0) hi ->
    Mem.free m b 0 sz = Some m1 ->
    F b = Some(sp, base) ->
    Mem.inject F m m' ->
    range_private F m1 m' sp base hi.
Proof.
  intros; red; intros. 
  destruct (zlt ofs (base + Zmax sz 0)) as [z|z].
  red; split. 
  replace ofs with ((ofs - base) + base) by omega.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); omega. 
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  exploit Mem.mi_no_overlap; eauto. 
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto. 
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); omega.
  eapply Mem.perm_free_3; eauto. 
  intros [A | A]. congruence. omega. 

  exploit (H ofs). omega. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
    range_private F m1 m1' sp base hi ->
    (forall b ofs p,
       Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
    Mem.unchanged_on (loc_out_of_reach F m1) m1' m2' ->
    Mem.inject F m1 m1' ->
    inject_incr F F' ->
    inject_separated F F' m1 m1' ->
    Mem.valid_block m1' sp ->
    range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto. 
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H0 in EQ; inv EQ. 
  red; intros; eelim B; eauto. eapply PERM; eauto. 
  red. destruct (plt b (Mem.nextblock m1)); auto. 
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. tauto. 
Qed.

(*NEW*)
Lemma range_private_extcall_sm:
  forall F F' m1 m2 m1' m2' sp base hi (WDF: SM_wd F) (WDF': SM_wd F'),
    range_private (as_inj F) m1 m1' sp base hi ->
    (forall b ofs p,
       Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
    Mem.unchanged_on (local_out_of_reach F m1) m1' m2' ->
    Mem.inject (as_inj F) m1 m1' ->
    extern_incr F F' ->
    sm_inject_separated F F' m1 m1' ->
    Mem.valid_block m1' sp ->
    (*NEW*) locBlocksTgt F sp = true -> 
    range_private (as_inj F') m2 m2' sp base hi.
Proof.
  intros until hi; intros WDF WDF' RP PERM UNCH INJ INCR SEP VB LBT.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto. 
  split; trivial. 
  intros. left. apply local_in_all in H0; eauto. 
  intros. 
  destruct SEP as [SEPa [SEPb SEPc]]. 
  destruct (as_inj F b) as [[sp1 delta1] |] eqn:?.
    exploit (extern_incr_as_inj _ _ INCR); eauto. 
    intros EQ; rewrite H0 in EQ; inv EQ. 
  red; intros. eelim B; eauto. eapply PERM; eauto. 
  red. destruct (plt b (Mem.nextblock m1)); auto. 
  exploit Mem.mi_freeblocks; eauto. congruence.
  destruct (SEPa _ _ _ Heqo H0). 
  elim (SEPc _ H2). unfold DomTgt. 
     assert (LT: locBlocksTgt F = locBlocksTgt F') by eapply INCR. 
     rewrite <- LT, LBT. trivial. 
  eapply Mem.perm_valid_block; eassumption.
Qed.


(** ** Relating global environments *)

(*Lenb: changed the first parameter to be structured injection,
  to facilitate adding the conjunct frgnBlocksSrc mu b = true 
  in DOMAIN*)
Inductive match_globalenvs mu (bound: block): Prop :=
| mk_match_globalenvs
    (DOMAIN: forall b, Plt b bound -> 
             (frgnBlocksSrc mu b = true /\ as_inj mu b = Some(b, 0)))

      (*Lenb: added assumption Genv.find_var_info. See also
              Cminorgen, SimplLocals, Stacking*) 
      (IMAGE: forall b1 b2 delta gv
              (GV: Genv.find_var_info ge b2 = Some gv),
               as_inj mu b1 = Some(b2, delta) -> Plt b2 bound -> 
               b1 = b2)
      (*WAS: (IMAGE: forall b1 b2 delta, 
               F b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)*)

    (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
    (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
    (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

Lemma find_function_agree:
  forall ros rs fd F ctx rs' bound,
    find_function ge ros rs = Some fd ->
    agree_regs (as_inj F) ctx rs rs' ->
    match_globalenvs F bound ->
    exists fd',
      find_function tge (sros ctx ros) rs' = Some fd' /\ transf_fundef fenv fd = OK fd'.
Proof.
  intros. destruct ros as [r | id]; simpl in *.
  (* register *)
  assert (rs'#(sreg ctx r) = rs#r).
  exploit Genv.find_funct_inv; eauto. intros [b EQ].
  assert (A: val_inject (as_inj F) rs#r rs'#(sreg ctx r)). eapply agree_val_reg; eauto.
  rewrite EQ in A; inv A.
  inv H1. destruct (DOMAIN b). 
    apply FUNCTIONS with fd. 
    rewrite EQ in H; rewrite Genv.find_funct_find_funct_ptr in H. auto.
  rewrite H2 in H5; inv H5. rewrite Int.add_zero. rewrite EQ. trivial.
  eapply functions_translated; eauto. rewrite <- H2 in H. trivial.
  (* symbol *)
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try discriminate.
  eapply function_ptr_translated; eauto.
Qed.

(** ** Relating stacks *) 
Inductive match_stacks (mu: SM_Injection) (m m': mem):
  list stackframe -> list stackframe -> block -> Prop :=
| match_stacks_nil: forall bound1 bound
                           (MG: match_globalenvs mu bound1)
                           (BELOW: Ple bound1 bound)
                           (* SL: locBlockSrc mu bound = true *),
                      match_stacks mu m m' nil nil bound
| match_stacks_cons: forall res (f:function) sp pc rs stk (f':function) sp' rs' stk' bound ctx
                            (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                            (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
                            (AG: agree_regs (as_inj mu) ctx rs rs')
                            (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
(* locBlockSrc mu sp = true *)
(SL: locBlocksTgt mu sp' = true )
(PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
(SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
(SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
(RES: Ple res ctx.(mreg))
(BELOW: Plt sp' bound),
                       match_stacks (mu) m m'
                                    (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                    (Stackframe (sreg ctx res) f' (Vptr sp' Int.zero) (spc ctx pc) rs' :: stk')
                                    bound
| match_stacks_untailcall: forall stk res f' sp' rpc rs' stk' bound ctx
                                  (MS: match_stacks_inside (mu) m m' stk stk' f' ctx sp' rs')
                                  (PRIV: range_private (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
                                  (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                                  (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
                                  (RET: ctx.(retinfo) = Some (rpc, res))
(SL: locBlocksTgt mu sp' = true )
(BELOW: Plt sp' bound),
                             match_stacks (mu) m m'
                                          stk
                                          (Stackframe res f' (Vptr sp' Int.zero) rpc rs' :: stk')
                                          bound

with match_stacks_inside (mu: SM_Injection) (m m': mem):
       list stackframe -> list stackframe -> function -> context -> block -> regset -> Prop :=
     | match_stacks_inside_base: forall stk stk' f' ctx sp' rs'
                                        (MS: match_stacks (mu) m m' stk stk' sp')
(SL: locBlocksTgt mu sp' = true ) (*Maybe*)
(RET: ctx.(retinfo) = None)
(DSTK: ctx.(dstk) = 0),
                                   match_stacks_inside (mu) m m' stk stk' f' ctx sp' rs'
     | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' ctx sp' rs' ctx'
                                           (MS: match_stacks_inside (mu) m m' stk stk' f' ctx' sp' rs')
                                           (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
                                           (AG: agree_regs (as_inj mu) ctx' rs rs')
                                           (SP: (local_of mu) sp = Some(sp', ctx'.(dstk)))
(*locBlockSrc mu sp = true*)
(SL: locBlocksTgt mu sp' = true )
(PAD: range_private (as_inj mu) m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
(RES: Ple res ctx'.(mreg))
(RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
(BELOW: context_below ctx' ctx)
(SBELOW: context_stack_call ctx' ctx),
                                      match_stacks_inside (mu) m m' (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
                                                          stk' f' ctx sp' rs'.

(** Properties of match_stacks *)

(*NEW*)
Section MATCH_STACKS_replace_externs.
  Variable mu: SM_Injection.
  Variables FS FT: block -> bool.
  Hypothesis HFS: forall b, frgnBlocksSrc mu b = true -> FS b = true.
  Variables m m': mem.

  Lemma match_stacks_replace_externs:
    forall stk stk' bound,
      match_stacks mu m m' stk stk' bound ->
      match_stacks (replace_externs mu FS FT) m m' stk stk' bound
    with match_stacks_inside_replace_externs:
     forall stk stk' f ctx sp rs', 
      match_stacks_inside mu m m' stk stk' f ctx sp rs' ->  
      match_stacks_inside (replace_externs mu FS FT) m m' stk stk' f ctx sp rs'.
  Proof.
    induction 1; eauto.
     { econstructor; try rewrite replace_externs_as_inj; try eassumption.
       destruct MG. 
       econstructor; try rewrite replace_externs_as_inj; eauto. 
       intros. rewrite replace_externs_frgnBlocksSrc. 
       destruct (DOMAIN _ H). split; eauto. }

     { econstructor; try rewrite replace_externs_as_inj; eauto. 
       rewrite replace_externs_locBlocksTgt. assumption. }

     { econstructor; try rewrite replace_externs_as_inj; eauto. 
        rewrite replace_externs_locBlocksTgt; trivial. }

    induction 1; eauto.
    { econstructor; eauto.
      rewrite replace_externs_locBlocksTgt; trivial. }
    { eapply match_stacks_inside_inlined; 
         try rewrite replace_externs_as_inj; eauto.
      rewrite replace_externs_local; trivial.  
      rewrite replace_externs_locBlocksTgt; trivial. }
  Qed.

End MATCH_STACKS_replace_externs.


(*NEW*)
Section MATCH_STACKS_replace_locals.
  Variable mu: SM_Injection.
  Variables PS PT: block -> bool.
  Variables m m': mem.

  Lemma match_stacks_replace_locals:
    forall stk stk' bound,
      match_stacks mu m m' stk stk' bound ->
      match_stacks (replace_locals mu PS PT) m m' stk stk' bound
    with match_stacks_inside_replace_locals:
     forall stk stk' f ctx sp rs', 
      match_stacks_inside mu m m' stk stk' f ctx sp rs' ->  
      match_stacks_inside (replace_locals mu PS PT) m m' stk stk' f ctx sp rs'.
  Proof.
    induction 1; eauto.
    { econstructor; try eassumption.
       destruct MG.
       constructor; try rewrite replace_locals_as_inj; eauto. 
       rewrite replace_locals_frgnBlocksSrc; assumption. }

    { econstructor; try rewrite replace_locals_as_inj; eauto. 
      rewrite replace_locals_locBlocksTgt; trivial. }
    { econstructor; try rewrite replace_locals_as_inj; eauto. 
      rewrite replace_locals_locBlocksTgt; trivial. }
    induction 1; eauto.
    { econstructor; eauto.
      rewrite replace_locals_locBlocksTgt; trivial. }
    { eapply match_stacks_inside_inlined; 
        try rewrite replace_locals_as_inj; eauto.
      rewrite replace_locals_local; trivial.  
      rewrite replace_locals_locBlocksTgt; trivial. }
  Qed.

End MATCH_STACKS_replace_locals.

Lemma match_globalenvs_intern_incr mu mu' b: forall
    (MG: match_globalenvs mu b) (INC: intern_incr mu mu')
    (HJ: forall b1 b2 d, as_inj mu' b1 = Some (b2, d) -> 
          Plt b2 b -> as_inj mu b1 = Some (b2, d))
    (WD: SM_wd mu'),
  match_globalenvs mu' b.
Proof. intros. inv MG. constructor; eauto.
assert (FBS: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
rewrite <- FBS; intros. destruct (DOMAIN _ H). split. trivial.
eapply (intern_incr_as_inj _ _ INC); trivial.
Qed.  

Lemma match_globalenvs_extern_incr mu mu' b: forall
    (MG: match_globalenvs mu b) (INC: extern_incr mu mu')
    (HJ: forall b1 b2 d, as_inj mu' b1 = Some (b2, d) -> 
          Plt b2 b -> as_inj mu b1 = Some (b2, d))
    (WD: SM_wd mu'),
  match_globalenvs mu' b.
Proof. intros. inv MG. constructor; eauto.
assert (FBS: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INC.
rewrite <- FBS; intros. destruct (DOMAIN _ H). split. trivial.
eapply (extern_incr_as_inj _ _ INC); trivial.
Qed.  
(*
Lemma match_globalenvs_inc j j' b: forall
    (MG: match_globalenvs j b) (INC: inject_incr j j')
    (HJ: forall b1 b2 d, j' b1 = Some (b2, d) -> Plt b2 b -> j b1 = Some (b2, d)),
  match_globalenvs j' b.
Proof. intros. inv MG. constructor; eauto. Qed.  
*)
(*
Section MATCH_STACKS_extern_incr.
  Variables mu mu': SM_Injection.
  Hypothesis WD': SM_wd mu'.
  Hypothesis INC: extern_incr mu mu'.
  Variables m m': mem.
  Hypothesis SEP: sm_inject_separated mu mu' m m'.
  Hypothesis SMV: sm_valid mu m m'. 

  Lemma match_stacks_extern_incr:
    forall stk stk' bound, 
      match_stacks mu m m' stk stk' bound ->
      Mem.valid_block m' bound ->
      match_stacks mu' m m' stk stk' bound
    with match_stacks_inside_extern_incr:
     forall stk stk' f ctx sp rs', 
      match_stacks_inside mu m m' stk stk' f ctx sp rs' -> 
      match_stacks_inside mu' m m' stk stk' f ctx sp rs'.
  Proof. 
    assert (INC':= extern_incr_as_inj _ _ INC WD').
    induction 1; eauto.
     econstructor; try eassumption.
       eapply match_globalenvs_inc; eauto.
       clear - WD' BELOW INC' SEP H. intros.
       remember (as_inj mu b1) as dd.         
       destruct dd; apply eq_sym in Heqdd.
         destruct p. rewrite (INC' _ _ _ Heqdd) in H0. assumption.
       destruct SEP as [? [? ?]].
       destruct (H2 _ _ _ Heqdd H0).
       destruct (as_inj_DomRng _ _ _ _ H0 WD').       
       elim (H4 _ H6 H8). clear - H BELOW H1. 
       red; red in H. xomega. 
     econstructor; eauto.
       eapply agree_regs_incr; try eassumption.
       assert (LL: locBlocksTgt mu = locBlocksTgt mu') by eapply INC. 
        rewrite <- LL; assumption.
       red; intros. red in PRIV. destruct (PRIV _ H0).
         split; trivial; intros. apply H2; clear H2.
         remember (as_inj mu b) as dd.         
         destruct dd; apply eq_sym in Heqdd.
           destruct p. rewrite (INC' _ _ _ Heqdd) in H3. assumption.
         destruct SEP as [? [? ?]].
         destruct (H2 _ _ _ Heqdd H3).
         destruct (as_inj_DomRng _ _ _ _ H3 WD').       
         elim (H5 _ H7 H9). eapply Mem.perm_valid_block; eassumption. 
       intros. econstructor; eauto.
       red; intros. red in PRIV. destruct (PRIV _ H0).
         split; trivial; intros. apply H2; clear H2.
         remember (as_inj mu b) as dd.         
         destruct dd; apply eq_sym in Heqdd.
           destruct p. rewrite (INC' _ _ _ Heqdd) in H3. assumption.
         destruct SEP as [? [? ?]].
         destruct (H2 _ _ _ Heqdd H3).
         destruct (as_inj_DomRng _ _ _ _ H3 WD').       
         elim (H5 _ H7 H9). eapply Mem.perm_valid_block; eassumption. 
       assert (LL: locBlocksTgt mu = locBlocksTgt mu') by eapply INC. 
        rewrite <- LL; assumption.
    assert (INC':= extern_incr_as_inj _ _ INC WD').
    induction 1; eauto.
     assert (LL: locBlocksTgt mu = locBlocksTgt mu') by eapply INC. 
     econstructor; try rewrite <- LL; eauto.
       eapply match_stacks_extern_incr; try eassumption. 
        eapply SMV. unfold RNG, DomTgt. rewrite SL. trivial. 
     eapply match_stacks_inside_inlined; eauto. 
       eapply agree_regs_incr; try eassumption.
       assert (LOC: local_of mu = local_of mu') by eapply INC. 
        rewrite <- LOC; assumption.
       assert (LL: locBlocksTgt mu = locBlocksTgt mu') by eapply INC. 
         rewrite <- LL; eauto.
       red; intros. red in PAD. destruct (PAD _ H0).
         split; trivial; intros. apply H2; clear H2.
         remember (as_inj mu b) as dd.         
         destruct dd; apply eq_sym in Heqdd.
           destruct p. rewrite (INC' _ _ _ Heqdd) in H3. assumption.
         destruct SEP as [? [? ?]].
         destruct (H2 _ _ _ Heqdd H3).
         destruct (as_inj_DomRng _ _ _ _ H3 WD').       
         elim (H5 _ H7 H9). eapply Mem.perm_valid_block; eassumption. 
  Qed.

End MATCH_STACKS_extern_incr.
*)
(*
Section MATCH_STACKS_EXTERN.
  Variable mu mu': SM_Injection.
  Variables m m' m1 m1': mem.
  Hypothesis INCR: extern_incr mu mu'.
  Hypothesis WD: SM_wd mu.
  Hypothesis WD': SM_wd mu'.
  Let inj := as_inj mu.
  Let inj' := as_inj mu'.

  Lemma match_stacks_extern_invariant:
    forall stk stk' bound, match_stacks mu m m' stk stk' bound ->
                           forall (INJ: forall b1 b2 delta, 
                                          inj' b1 = Some(b2, delta) -> Plt b2 bound -> inj b1 = Some(b2, delta))
                                  (PERM1: forall b1 b2 delta ofs,
                                            inj' b1 = Some(b2, delta) -> Plt b2 bound ->
                                            Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
                                  (PERM2: forall b ofs, Plt b bound ->
                                                        Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
                                  (PERM3: forall b ofs k p, Plt b bound ->
                                                            Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
                             match_stacks mu' m1 m1' stk stk' bound

                             with match_stacks_inside_extern_invariant:
                                    forall stk stk' f' ctx sp' rs1, 
                                      match_stacks_inside mu m m' stk stk' f' ctx sp' rs1 ->
                                      forall rs2
                                             (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
                                             (INJ: forall b1 b2 delta, 
                                                     inj' b1 = Some(b2, delta) -> Ple b2 sp' -> inj b1 = Some(b2, delta))
                                             (PERM1: forall b1 b2 delta ofs,
                                                       inj' b1 = Some(b2, delta) -> Ple b2 sp' ->
                                                       Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
                                             (PERM2: forall b ofs, Ple b sp' ->
                                                                   Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
                                             (PERM3: forall b ofs k p, Ple b sp' ->
                                                                       Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
                                        match_stacks_inside mu' m1 m1' stk stk' f' ctx sp' rs2.

  Proof.
    assert (INC:= extern_incr_as_inj _ _ INCR WD').
    induction 1; intros.
    (* nil *)
    apply match_stacks_nil with (bound1 := bound1).
    eapply match_globalenvs_inc; try eassumption. 
      intros. eapply INJ; eauto. eapply Plt_le_trans; eauto. trivial. 
    (* cons *)
    apply match_stacks_cons with (ctx := ctx); auto.
    eapply match_stacks_inside_extern_invariant; eauto.
    intros; eapply INJ; eauto; xomega. 
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    eapply agree_regs_incr; eauto.
    assert (locBlocksTgt mu = locBlocksTgt mu') by eapply INCR.
      rewrite <- H; trivial.
    eapply range_private_invariant; eauto. 
    (* untailcall *)
    apply match_stacks_untailcall with (ctx := ctx); auto. 
    eapply match_stacks_inside_extern_invariant; eauto.
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    eapply range_private_invariant; eauto. 
    assert (locBlocksTgt mu = locBlocksTgt mu') by eapply INCR.
      rewrite <- H; trivial.

    assert (INC:= extern_incr_as_inj _ _ INCR WD'). 
    induction 1; intros.
    (* base *)
    eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extern_invariant; eauto. 
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    assert (locBlocksTgt mu = locBlocksTgt mu') by eapply INCR.
      rewrite <- H; trivial.
    (* inlined *)
    apply match_stacks_inside_inlined with (ctx' := ctx'); auto. 
    apply IHmatch_stacks_inside; auto.
    intros. apply RS. red in BELOW. xomega. 
    apply agree_regs_incr with inj; auto. 
    apply agree_regs_invariant with rs'; auto. 
    intros. apply RS. red in BELOW. xomega.
    assert (LOC: local_of mu = local_of mu') by eapply INCR.
      rewrite <- LOC; trivial.
    assert (LL: locBlocksTgt mu = locBlocksTgt mu') by eapply INCR.
      rewrite <- LL; trivial.
    eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. xomega. eapply PERM1; eauto. xomega.
    intros. eapply PERM2; eauto. xomega.
  Qed.

End MATCH_STACKS_EXTERN.
*)
Section MATCH_STACKS.
  Variable F: SM_Injection.
  Variables m m': mem.
  Let Finj := as_inj F.

  Lemma match_stacks_globalenvs:
    forall stk stk' bound,
      match_stacks F m m' stk stk' bound -> 
      exists b, match_globalenvs F b
  with match_stacks_inside_globalenvs:
    forall stk stk' f ctx sp rs', 
      match_stacks_inside F m m' stk stk' f ctx sp rs' ->
      exists b, match_globalenvs F b.
  Proof.
    induction 1; eauto.
    induction 1; eauto.
  Qed.

  Lemma match_globalenvs_preserves_globals:
    forall b, match_globalenvs F b -> meminj_preserves_globals ge Finj.
  Proof.
    intros. inv H. red.
    split. intros. eapply (DOMAIN _ (SYMBOLS _ _ H)). 
    split. intros. eapply (DOMAIN _ (VARINFOS _ _ H)). 
    intros. symmetry. eapply IMAGE; eauto.
  Qed. 

  Lemma match_stacks_inside_globals:
    forall stk stk' f ctx sp rs', 
      match_stacks_inside F m m' stk stk' f ctx sp rs' -> 
      meminj_preserves_globals ge Finj.
  Proof.
    intros. exploit match_stacks_inside_globalenvs; eauto. intros [b A]. 
    eapply match_globalenvs_preserves_globals; eauto.
  Qed.

  Lemma match_stacks_bound:
    forall stk stk' bound bound1,
      match_stacks F m m' stk stk' bound ->
      Ple bound bound1 ->
      match_stacks F m m' stk stk' bound1.
  Proof.
    intros. inv H.
    apply match_stacks_nil with bound0. auto. eapply Ple_trans; eauto. 
    eapply match_stacks_cons; eauto. eapply Plt_le_trans; eauto. 
    eapply match_stacks_untailcall; eauto. eapply Plt_le_trans; eauto. 
  Qed. 

  Variable F1: SM_Injection.
  Let Finj1 := as_inj F1.
  Variables m1 m1': mem.
  (*Hypothesis INCR: inject_incr Finj Finj1.*)
  Hypothesis INCR: intern_incr F F1.
  Hypothesis WDF: SM_wd F.
  Hypothesis WDF1: SM_wd F1.
  Lemma INCR':  inject_incr Finj Finj1.
    eapply intern_incr_as_inj; auto.
  Qed.
  Lemma incre_local_of: forall mu mu' (INCR0: intern_incr mu mu') b b' delta, local_of mu b = Some (b', delta) -> local_of mu' b = Some (b', delta).
      intros.
      apply intern_incr_local in INCR0.
      apply INCR0; auto.
  Qed.

  Lemma match_stacks_invariant:
    forall stk stk' bound, match_stacks F m m' stk stk' bound ->
                           forall (INJ: forall b1 b2 delta, 
                                          Finj1 b1 = Some(b2, delta) -> Plt b2 bound -> Finj b1 = Some(b2, delta))
                                  (PERM1: forall b1 b2 delta ofs,
                                            Finj1 b1 = Some(b2, delta) -> Plt b2 bound ->
                                            Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
                                  (PERM2: forall b ofs, Plt b bound ->
                                                        Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
                                  (PERM3: forall b ofs k p, Plt b bound ->
                                                            Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
                             match_stacks F1 m1 m1' stk stk' bound

                             with match_stacks_inside_invariant:
                                    forall stk stk' f' ctx sp' rs1, 
                                      match_stacks_inside F m m' stk stk' f' ctx sp' rs1 ->
                                      forall rs2
                                             (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
                                             (INJ: forall b1 b2 delta, 
                                                     Finj1 b1 = Some(b2, delta) -> Ple b2 sp' -> Finj b1 = Some(b2, delta))
                                             (PERM1: forall b1 b2 delta ofs,
                                                       Finj1 b1 = Some(b2, delta) -> Ple b2 sp' ->
                                                       Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
                                             (PERM2: forall b ofs, Ple b sp' ->
                                                                   Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
                                             (PERM3: forall b ofs k p, Ple b sp' ->
                                                                       Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
                                        match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs2.

  Proof.
    assert (INCR':  inject_incr Finj Finj1) by (exact INCR').
    induction 1; intros.
    (* nil *)
    apply match_stacks_nil with (bound1 := bound1).
    inv MG. constructor; auto. 
    intros. destruct (DOMAIN _ H).
       split. 
         assert (frgnBlocksSrc F = frgnBlocksSrc F1) by eapply INCR.
         rewrite <- H2; trivial.
       eapply (intern_incr_as_inj _ _ INCR); trivial.
    intros. eapply (IMAGE _ _ delta _ GV). eapply INJ; eauto. eapply Plt_le_trans; eauto.
    auto. auto.
    (* cons *)
    apply match_stacks_cons with (ctx := ctx); auto.
    eapply match_stacks_inside_invariant; eauto.
    intros; eapply INJ; eauto; xomega. 
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    eapply agree_regs_incr; eauto.
    destruct INCR; repeat open_Hyp; apply H2; assumption.
    eapply range_private_invariant; eauto. 
    (* untailcall *)
    apply match_stacks_untailcall with (ctx := ctx); auto. 
    eapply match_stacks_inside_invariant; eauto.
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    eapply range_private_invariant; eauto. 
    destruct INCR; repeat open_Hyp; apply H2; assumption.
    assert (INCR':  inject_incr Finj Finj1) by (exact INCR').
    induction 1; intros.
    (* base *)
    eapply match_stacks_inside_base; eauto.
    eapply match_stacks_invariant; eauto. 
    intros; eapply INJ; eauto; xomega.
    intros; eapply PERM1; eauto; xomega.
    intros; eapply PERM2; eauto; xomega.
    intros; eapply PERM3; eauto; xomega.
    destruct INCR; repeat open_Hyp; apply H2; assumption.
    (* inlined *)
    apply match_stacks_inside_inlined with (ctx' := ctx'); auto. 
    apply IHmatch_stacks_inside; auto.
    intros. apply RS. red in BELOW. xomega. 
    apply agree_regs_incr with Finj; auto. 
    apply agree_regs_invariant with rs'; auto. 
    intros. apply RS. red in BELOW. xomega.
    eapply (incre_local_of F F1); auto.
    destruct INCR; repeat open_Hyp. apply H3; assumption.
    eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto. xomega. eapply PERM1; eauto. xomega.
    intros. eapply PERM2; eauto. xomega.
  Qed.

  Lemma match_stacks_empty:
    forall stk stk' bound,
      match_stacks F m m' stk stk' bound -> stk = nil -> stk' = nil
      with match_stacks_inside_empty:
             forall stk stk' f ctx sp rs,
               match_stacks_inside F m m' stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
  Proof.
    induction 1; intros.
    auto.
    discriminate.
    exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
    induction 1; intros.
    split. eapply match_stacks_empty; eauto. auto.
    discriminate.
  Qed.

End MATCH_STACKS.



(** Preservation by assignment to a register *)
Hint Immediate intern_incr_refl. (* : incr_refl.*)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v,
    SM_wd F ->
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    match_stacks_inside F m m' stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto. 
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. xomega.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1', 
    SM_wd F ->
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    Mem.store chunk m b ofs v = Some m1 ->
    Mem.store chunk' m' b' ofs' v' = Some m1' ->
    match_stacks_inside F m1 m1' stk stk' f' ctx sp' rs'.
Proof.
  intros. 
  eapply match_stacks_inside_invariant; eauto with mem.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sp' rs',
    SM_wd F ->
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    forall sz m1 b F1 delta,
    SM_wd F1 ->
      Mem.alloc m 0 sz = (m1, b) ->
      (intern_incr F F1) ->
      (as_inj F1) b = Some(sp', delta) ->
      (forall b1, b1 <> b -> (as_inj F1) b1 = (as_inj F) b1) ->
      delta >= ctx.(dstk) ->
      match_stacks_inside F1 m1 m' stk stk' f' ctx sp' rs'.
Proof.
  induction 2; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply (match_stacks_invariant F m m' F1); eauto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H3 in H6; inv H6. eelim Plt_strict; eauto. 
  rewrite H4 in H6; auto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H3 in H6; inv H6. eelim Plt_strict; eauto. 
  destruct H2; repeat open_Hyp. apply H8; assumption.
  (* inlined *)
  assert (INCR':  inject_incr (as_inj F) (as_inj F1)).
  eapply intern_incr_as_inj; auto.
  eapply match_stacks_inside_inlined; eauto. 
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. omega. 
  eapply agree_regs_incr; eauto.
  apply intern_incr_local in H3.
  apply H3; auto.
  destruct H3; repeat open_Hyp. apply H9; assumption.
  eapply range_private_invariant; eauto. 
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H4 in H7; inv H7. elimtype False; xomega. 
  rewrite H5 in H7; auto. 
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1,
    SM_wd F ->
    match_stacks F m m' stk stk' sp ->
    Mem.free m b lo hi = Some m1 ->
    match_stacks F m1 m' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto.
  intros. eapply Mem.perm_free_3; eauto. 
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sp lo hi m1',
    SM_wd F ->
    match_stacks F m m' stk stk' sp ->
    Mem.free m' sp lo hi = Some m1' ->
    match_stacks F m m1' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto. 
  intros. eapply Mem.perm_free_1; eauto. 
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H. 
  assert (2 <= sz -> (2 | n)). intros.
  destruct (zle sz 1). omegaContradiction.
  destruct (zle sz 2). auto. 
  destruct (zle sz 4). apply Zdivides_trans with 4; auto. exists 2; auto.
  apply Zdivides_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
  destruct (zle sz 1). omegaContradiction.
  destruct (zle sz 2). omegaContradiction.
  destruct (zle sz 4). auto.
  apply Zdivides_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
  destruct (zle sz 1). omegaContradiction.
  destruct (zle sz 2). omegaContradiction.
  destruct (zle sz 4). omegaContradiction.
  auto.
  destruct chunk; simpl in *; auto.
  apply Zone_divide.
  apply Zone_divide.
  apply H2; omega.
Qed.


(** Preservation by external calls *)

Section EXTCALL.

  Variables F1 F2: SM_Injection.
  Hypothesis WDF1: SM_wd F1.
  Hypothesis WDF2: SM_wd F2.
  Let Finj1 := as_inj F1.
  Let Finj2 := as_inj F2.
  Variables m1 m2 m1' m2': mem.
  Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
  Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
  Hypothesis UNCHANGED: Mem.unchanged_on (loc_out_of_reach Finj1 m1) m1' m2'.
  Hypothesis INJ: Mem.inject Finj1 m1 m1'.
  Hypothesis INCR: intern_incr F1 F2.
  (* Hypothesis INCR: inject_incr Finj1 Finj2. *)
  About INCR'.
  Hypothesis SEP: inject_separated Finj1 Finj2 m1 m1'.
  Hypothesis SMV: sm_valid F1 m1 m1'. 

  Lemma match_stacks_extcall:
    forall stk stk' bound, 
      match_stacks F1 m1 m1' stk stk' bound ->
      Ple bound (Mem.nextblock m1') ->
      match_stacks F2 m2 m2' stk stk' bound
      with match_stacks_inside_extcall:
             forall stk stk' f' ctx sp' rs',
               match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs' ->
               Plt sp' (Mem.nextblock m1') ->
               match_stacks_inside F2 m2 m2' stk stk' f' ctx sp' rs'.
  Proof.
    assert (INCR': inject_incr Finj1 Finj2) by (apply INCR'; auto). 
    induction 1; intros.
    apply match_stacks_nil with bound1; auto. 
    inv MG. constructor; intros; eauto. 
    destruct (DOMAIN _ H0).
      split. assert (F12: frgnBlocksSrc F1 = frgnBlocksSrc F2) by eapply INCR.
             rewrite <- F12; trivial.
      eapply (intern_incr_as_inj _ _ INCR); trivial.
    remember (Finj1 b1) as d; apply eq_sym in Heqd.
      destruct d.
        destruct p.
        rewrite (intern_incr_as_inj _ _ INCR WDF2 _ _ _ Heqd) in H0.
        inv H0. apply (IMAGE _ _ _ _ GV Heqd H1).
      destruct (SEP _ _ _ Heqd H0).
        destruct (DOMAIN _ H1).
        elim H3. apply SMV. eapply (as_inj_DomRng _ _ _ _ H5 WDF1).

    eapply match_stacks_cons; eauto. 
    eapply match_stacks_inside_extcall; eauto. xomega. 
    eapply agree_regs_incr; eauto. 
    destruct INCR; repeat open_Hyp. apply H3; assumption.
    eapply range_private_extcall; eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
    eapply match_stacks_untailcall; eauto. 
    eapply match_stacks_inside_extcall; eauto. xomega. 
    eapply range_private_extcall; eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
    destruct INCR; repeat open_Hyp; apply H3; assumption.
    assert (INCR': inject_incr Finj1 Finj2) by (apply INCR'; auto). 
    induction 1; intros.
    eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall; eauto. xomega. 
    destruct INCR; repeat open_Hyp; apply H3; assumption.
    eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_incr; eauto.    
    eapply (incre_local_of F1); auto.
    destruct INCR; repeat open_Hyp; apply H4; assumption.
    eapply range_private_extcall; eauto.
  Qed.

End EXTCALL.

(*NEW*)
Section EXTCALL_SM.

  Variables F1 F2: SM_Injection.
  Hypothesis WDF1: SM_wd F1.
  Hypothesis WDF2: SM_wd F2.
  Let Finj1 := as_inj F1.
  Let Finj2 := as_inj F2.
  Variables m1 m2 m1' m2': mem.
  Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
  Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
  Hypothesis UNCHANGED: Mem.unchanged_on (local_out_of_reach F1 m1) m1' m2'.
  Hypothesis INJ: Mem.inject Finj1 m1 m1'.
  Hypothesis INCR: extern_incr F1 F2.
  Hypothesis SEP: sm_inject_separated F1 F2 m1 m1'.
  Hypothesis SMV: sm_valid F1 m1 m1'. 

  Lemma match_stacks_extcall_sm:
    forall stk stk' bound, 
      match_stacks F1 m1 m1' stk stk' bound ->
      Ple bound (Mem.nextblock m1') ->
      match_stacks F2 m2 m2' stk stk' bound
      with match_stacks_inside_extcall_sm:
             forall stk stk' f' ctx sp' rs',
               match_stacks_inside F1 m1 m1' stk stk' f' ctx sp' rs' ->
               Plt sp' (Mem.nextblock m1') ->
               match_stacks_inside F2 m2 m2' stk stk' f' ctx sp' rs'.
  Proof.
    assert (INCR':= extern_incr_as_inj _ _ INCR WDF2). 
    induction 1; intros.
  { apply match_stacks_nil with bound1; auto. 
    inv MG. constructor; intros; eauto. 
    destruct (DOMAIN _ H0).
      split. assert (F12: frgnBlocksSrc F1 = frgnBlocksSrc F2) by eapply INCR.
             rewrite <- F12; trivial.
      eapply (extern_incr_as_inj _ _ INCR); trivial.
    remember (Finj1 b1) as d; apply eq_sym in Heqd.
      destruct d.
        destruct p.
        rewrite (extern_incr_as_inj _ _ INCR WDF2 _ _ _ Heqd) in H0.
        inv H0. apply (IMAGE _ _ _ _ GV Heqd H1).
      destruct SEP as [SEPa [SEPb SEPc]]. 
        destruct (SEPa _ _ _ Heqd H0).
        destruct (DOMAIN _ H1).
        elim (SEPc _ H3). eapply (as_inj_DomRng _ _ _ _ H0 WDF2).
        eapply SMV. eapply (as_inj_DomRng _ _ _ _ H5 WDF1). }

  { eapply match_stacks_cons; eauto. 
    eapply match_stacks_inside_extcall_sm; eauto. xomega. 
    eapply agree_regs_incr; eauto. 
    destruct INCR; repeat open_Hyp.
    rewrite <- H5; assumption. 
    eapply (range_private_extcall_sm F1); eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega. }
  { eapply match_stacks_untailcall; eauto. 
    eapply match_stacks_inside_extcall_sm; eauto. xomega. 
    eapply (range_private_extcall_sm F1); eauto. red; xomega. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red; xomega.
    assert (LT: locBlocksTgt F1 = locBlocksTgt F2) by eapply INCR.
      rewrite <- LT; assumption. }
  assert (INCR':= extern_incr_as_inj _ _ INCR WDF2).  
    induction 1; intros.
  { eapply match_stacks_inside_base; eauto.
    eapply match_stacks_extcall_sm; eauto. xomega. 
    assert (LT: locBlocksTgt F1 = locBlocksTgt F2) by eapply INCR.
      rewrite <- LT; assumption. }
  { eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_incr; eauto. 
    assert (LOC: local_of F1 = local_of F2) by eapply INCR.   
    rewrite <- LOC; trivial.
    assert (LT: locBlocksTgt F1 = locBlocksTgt F2) by eapply INCR.
      rewrite <- LT; assumption.
    eapply (range_private_extcall_sm F1); eauto. } 
  Qed.

End EXTCALL_SM.

(*NEW*)
Section MATCH_STACK_restrict_locals.
  Variable mu : SM_Injection.
  Variable m1 m2: mem.
  Variable vals1 vals2 : list val.
  Hypothesis WD : SM_wd mu.
  Hypothesis PG: meminj_preserves_globals ge (as_inj mu).

  Let mu1 := restrict_sm mu (fun b => locBlocksSrc mu b || 
                             frgnBlocksSrc mu b).
  Let mu2 := 
       (replace_locals mu
        (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b)
        (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b)).
  

  Lemma MGE_restrict_local bnd: match_globalenvs  mu1 bnd ->
        match_globalenvs mu2 bnd.
  Proof. intros.
    inv H. econstructor; eauto.
     intros. destruct (DOMAIN _ H).
      unfold mu2. rewrite replace_locals_as_inj, replace_locals_frgnBlocksSrc. 
      split. unfold mu1 in H0. 
             rewrite restrict_sm_frgnBlocksSrc in H0. trivial. 
      unfold mu1 in H1. rewrite restrict_sm_all in H1. 
        apply (restrictD_Some _ _ _ _ _ H1). 
     intros. unfold mu2 in H. rewrite replace_locals_as_inj in H. 
       symmetry. eapply PG; eassumption. 
  Qed. 

  Lemma range_private_restrict_locals sp' n sz : forall
    (PRIV : range_private (as_inj mu1) m1 m2 sp' n sz)
    (SL : locBlocksTgt mu1 sp' = true),
   range_private (as_inj mu2) m1 m2 sp' n sz.
  Proof. intros.
    red; intros ? HH. destruct (PRIV _ HH). split;  trivial. 
      unfold mu2; rewrite replace_locals_as_inj.
       unfold mu1 in H0; rewrite restrict_sm_all in H0. 
       intros. eapply (H0 b delta). 
       unfold mu1 in SL; rewrite restrict_sm_locBlocksTgt in SL.
       apply restrictI_Some; trivial.
       rewrite (as_inj_locBlocks _ _ _ _ WD H1), SL. trivial.
  Qed.

  Lemma agree_regs_restrict_locals rs rs' ctx: 
     agree_regs (as_inj mu1) ctx rs rs' ->
     agree_regs (as_inj mu2) ctx rs rs'.
  Proof. intros AG; destruct AG. 
    split; intros. 
        unfold mu2; rewrite replace_locals_as_inj. 
        eapply val_inject_incr; try eapply H. 
        unfold mu1; rewrite restrict_sm_all. apply restrict_incr.
        trivial.
    apply (H0 _ H1).
  Qed.

  Lemma match_stacks_restrict_locals:
   forall stk stk' bnd,
     match_stacks mu1 m1 m2 stk stk' bnd ->
  (*         Ple bnd (Mem.nextblock m2) ->*)
     match_stacks mu2 m1 m2 stk stk' bnd
  with match_stacks_inside_restrict_locals:
      forall stk stk' f' ctx sp' rs',
      match_stacks_inside mu1 m1 m2 stk stk' f' ctx sp' rs' ->
(*               Plt sp' (Mem.nextblock m1) ->*)
      match_stacks_inside mu2 m1 m2 stk stk' f' ctx sp' rs'.
  Proof.
    induction 1; intros.
  { eapply match_stacks_nil; auto. 
      eapply MGE_restrict_local; eassumption. assumption. } 
  { eapply match_stacks_cons; eauto. 
    eapply agree_regs_restrict_locals; eassumption.
    unfold mu2; rewrite replace_locals_as_inj.
      unfold mu1 in SP; rewrite restrict_sm_all in SP.
      eapply (restrictD_Some _ _ _ _ _ SP).
    unfold mu2; rewrite replace_locals_locBlocksTgt.
      unfold mu1 in SL; rewrite restrict_sm_locBlocksTgt in SL. trivial.
    eapply range_private_restrict_locals; eassumption. }
  { eapply match_stacks_untailcall; eauto. 
    eapply range_private_restrict_locals; eassumption. 
    unfold mu2; rewrite replace_locals_locBlocksTgt.
      unfold mu1 in SL; rewrite restrict_sm_locBlocksTgt in SL. trivial. }

    induction 1; intros.
  { eapply match_stacks_inside_base; eauto.
    unfold mu2; rewrite replace_locals_locBlocksTgt.
      unfold mu1 in SL; rewrite restrict_sm_locBlocksTgt in SL. trivial. }
  { eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_restrict_locals; eassumption. 
    unfold mu2; rewrite replace_locals_local.
      unfold mu1 in SP; rewrite restrict_sm_local in SP. 
      apply (restrictD_Some _ _ _ _ _ SP). 
    unfold mu2; rewrite replace_locals_locBlocksTgt.
      unfold mu1 in SL; rewrite restrict_sm_locBlocksTgt in SL. trivial.
    eapply range_private_restrict_locals; eassumption. }
  Qed.

End MATCH_STACK_restrict_locals. 

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq. 
  apply Zdiv_unique with (b := amount - 1). omega. omega.
Qed.

Lemma match_stacks_inside_inlined_tailcall:
  forall F m m' stk stk' f' ctx sp' rs' ctx' f,
    match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
    context_below ctx ctx' ->
    context_stack_tailcall ctx f ctx' ->
    ctx'.(retinfo) = ctx.(retinfo) ->
    range_private (as_inj F) m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
    tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
    match_stacks_inside F m m' stk stk' f' ctx' sp' rs'.
Proof.
  intros. inv H.
  (* base *)
  eapply match_stacks_inside_base; eauto. congruence. 
  rewrite H1. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Zdivide_0.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H1. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto. 
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply H3. inv H4. xomega. 
  congruence. 
  unfold context_below in *. xomega.
  unfold context_stack_call in *. omega. 
Qed.

(** ** Relating states *)

Inductive match_states:  SM_Injection -> RTL_core -> mem -> RTL_core -> mem -> Prop :=
| match_regular_states: forall mu stk f sp pc rs m stk' f' sp' rs' m' ctx
                               (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                               (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
                               (AG: agree_regs (as_inj mu) ctx rs rs')
                               (SP: (as_inj mu) sp = Some(sp', ctx.(dstk)))
                               (MINJ: Mem.inject (as_inj mu) m m')
                               (VB: Mem.valid_block m' sp')
                               (PRIV: range_private (as_inj mu) m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
                               (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                               (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
                          match_states mu (RTL_State stk f (Vptr sp Int.zero) pc rs) m
                                       (RTL_State stk' f' (Vptr sp' Int.zero) (spc ctx pc) rs') m'
| match_call_states: forall (mu: SM_Injection) stk fd args m stk' fd' args' m'
                            (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
                            (FD: transf_fundef fenv fd = OK fd')
                            (VINJ: val_list_inject  (as_inj mu) args args')
                            (MINJ: Mem.inject (as_inj mu) m m'),
                       match_states mu (RTL_Callstate stk fd args) m
                                    (RTL_Callstate stk' fd' args') m'
| match_call_regular_states: forall (mu: SM_Injection) stk f vargs m stk' f' sp' rs' m' ctx ctx' pc' pc1' rargs
                                    (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                                    (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
                                    (BELOW: context_below ctx' ctx)
                                    (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
                                    (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
                                    (VINJ: list_forall2 (val_reg_charact (as_inj mu) ctx' rs') vargs rargs)
                                    (MINJ: Mem.inject (as_inj mu) m m')
                                    (VB: Mem.valid_block m' sp')
                                    (PRIV: range_private  (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
                                    (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                                    (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
                               match_states mu (RTL_Callstate stk (Internal f) vargs) m
                                            (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'
| match_return_states: forall (mu: SM_Injection) stk v m stk' v' m'
                              (MS: match_stacks mu m m' stk stk' (Mem.nextblock m'))
                              (VINJ: val_inject (as_inj mu) v v')
                              (MINJ: Mem.inject (as_inj mu) m m'),
                         match_states mu (RTL_Returnstate stk v) m
                                      (RTL_Returnstate stk' v') m'
| match_return_regular_states: forall (mu: SM_Injection)stk v m stk' f' sp' rs' m' ctx pc' or rinfo
                                      (MS: match_stacks_inside mu m m' stk stk' f' ctx sp' rs')
                                      (RET: ctx.(retinfo) = Some rinfo)
                                      (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
                                      (VINJ: match or with None => v = Vundef | Some r => val_inject (as_inj mu) v rs'#(sreg ctx r) end)
                                      (MINJ: Mem.inject (as_inj mu) m m')
                                      (VB: Mem.valid_block m' sp')
                                      (PRIV: range_private (as_inj mu) m m' sp' ctx.(dstk) f'.(fn_stacksize))
                                      (SSZ1: 0 <= f'.(fn_stacksize) < Int.max_unsigned)
                                      (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
                                 match_states mu (RTL_Returnstate stk v) m
                                              (RTL_State stk' f' (Vptr sp' Int.zero) pc' rs') m'.

Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states (restrict_sm mu (vis mu)) c1 m1 c2 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\
  SM_wd mu /\
  Mem.inject (as_inj mu) m1 m2.

(** ** Forward simulation *)
Definition RTL_measure (S: RTL_core) : nat :=
  match S with
    | RTL_State _ _ _ _ _ => 1%nat
    | RTL_Callstate _ _ _ => 0%nat
    | RTL_Returnstate _ _ => 0%nat
  end.


Lemma tr_funbody_inv:
  forall sz cts f c pc i,
    tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto. 
Qed.

(** MISSING THEOREM step_simulation *)


Definition entry_points_ok entrypoints:= forall (v1 v2 : val) (sig : signature),
                                           In (v1, v2, sig) entrypoints -> 
                                           exists b f1 f2, 
                                             v1 = Vptr b Int.zero 
                                             /\ v2 = Vptr b Int.zero
                                             /\ Genv.find_funct_ptr ge b = Some f1
                                             /\ Genv.find_funct_ptr tge b = Some f2.

(*NEW*) Variable hf : I64Helpers.helper_functions.

  Lemma MATCH_initial_core: forall (v1 v2 : val) (sig : signature) entrypoints
  (EP: In (v1, v2, sig) entrypoints)
  (entry_ok : forall (v1 v2 : val) (sig : signature),
                  In (v1, v2, sig) entrypoints ->
                  exists
                    (b : Values.block) f1 f2,
                    v1 = Vptr b Int.zero /\
                    v2 = Vptr b Int.zero /\
                    Genv.find_funct_ptr ge b = Some f1 /\
                    Genv.find_funct_ptr tge b = Some f2)
  (vals1 : list val) c1 (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (Ini : initial_core (rtl_eff_sem hf) ge v1 vals1 = Some c1)
  (Inj: Mem.inject j m1 m2)
  (VInj: Forall2 (val_inject j) vals1 vals2)
  (PG: meminj_preserves_globals ge j)
  (R : list_norepet (map fst (prog_defs SrcProg)))
  (J: forall b1 b2 d, j b1 = Some (b2, d) -> 
                      DomS b1 = true /\ DomT b2 = true)
  (RCH: forall b, REACH m2
        (fun b' : Values.block => isGlobalBlock tge b' || getBlocks vals2 b') b =
         true -> DomT b = true)
  (InitMem : exists m0 : mem, Genv.init_mem SrcProg = Some m0 
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m1) 
      /\ Ple (Mem.nextblock m0) (Mem.nextblock m2))
  (GDE: genvs_domain_eq ge tge)
  (HDomS: forall b : Values.block, DomS b = true -> Mem.valid_block m1 b)
  (HDomT: forall b : Values.block, DomT b = true -> Mem.valid_block m2 b),
exists c2,
  initial_core (rtl_eff_sem hf) tge v2 vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Admitted.
(*
Proof.
intros.
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv SrcProg) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1 
            (sig_args (funsig (Internal f))) 
           && val_casted.vals_defined vals1).
  2: solve[intros H2; rewrite H2 in H1; inv H1].
  intros H2; rewrite H2 in H1. inv H1. 
  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
    exploit sig_function_translated; try eassumption. intros SIG.
    destruct (entry_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. unfold ge in C. rewrite C in Heqzz. inv Heqzz.
     unfold tge in FP. rewrite D in FP. inv FP.
    assert (FF: exists f', tf = Internal f').
       Errors.monadInv TF. eexists; reflexivity.
    destruct FF as [f' ?]. subst tf.
    unfold rtl_eff_sem, rtl_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    rewrite D. 
  assert (val_casted.val_has_type_list_func vals2
           (sig_args (funsig (Internal f')))=true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; simpl in H2. solve[inv H2].
    assert (sig_args (funsig (Internal f'))
          = sig_args (funsig (Internal f))) as ->.
    { rewrite SIG. simpl. reflexivity. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (funsig (Internal f)))); auto. }
  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; inv H2. }
  simpl. 
  eexists; split.
  reflexivity.
  Focus 2.
    intros CONTRA.
    solve[elimtype False; auto].
  clear e e0.
  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]].
  remember (val_casted.val_has_type_list_func vals1 (sig_args (funsig (Internal f))) &&
         val_casted.vals_defined vals1) as vc.
  destruct vc; inv H2. 
  split. 
  { specialize (Genv.find_funct_ptr_not_fresh SrcProg). intros FFP.
       destruct InitMem as [m0 [INIT_MEM [? ?]]].
       specialize (FFP _ _ _ INIT_MEM C). 
       destruct (valid_init_is_global _ R _ INIT_MEM _ FFP) as [id Hid].
    econstructor; try rewrite restrict_sm_all, initial_SM_as_inj.
    2: assumption.
    { clear GG FF. 
      econstructor; try rewrite restrict_sm_all, initial_SM_as_inj.
      2: eassumption.
      unfold initial_SM in *; simpl in *.
        unfold vis; simpl.
        clear CC DD Ini.
        exploit @restrict_preserves_globals. eapply PG.
          instantiate (1:=(fun b : block =>
              REACH m1 (fun b1 : block =>
          isGlobalBlock (Genv.globalenv SrcProg) b1
            || getBlocks vals1 b1) b)).
          simpl; intros. unfold ge in EE; apply EE in H3.
            apply H3. 
        intros PGR.
        destruct PGR as [A [B CC]].
        constructor. 
  { (*DOMAIN*)
    simpl. unfold as_inj; simpl.
    intros b DD. (*intros [[id E]|[[gv E]|[fptr E]]]; eauto.*)
    cut (exists id, Genv.find_symbol (Genv.globalenv SrcProg) id = Some b).
    intros [symb ID].
    split. apply REACH_nil. rewrite (find_symbol_isGlobal _ _ _ ID). 
           trivial.
    apply joinI. left. solve[eapply A; eauto].
    eapply valid_init_is_global; eauto. }
  { (*IMAGE*)
     unfold as_inj; simpl.
     intros.  symmetry. destruct (joinD_Some _ _ _ _ _ H3). 
        solve [eapply (CC _ _ _ _ GV); eauto].
     destruct H5. destruct (restrictD_Some _ _ _ _ _ H6).
       discriminate. }
  { intros. eapply Genv.find_symbol_not_fresh; eauto. }
  { intros. eapply Genv.find_funct_ptr_not_fresh ; eauto. }
  { intros. eapply Genv.find_var_info_not_fresh; eauto. }

  }

  unfold initial_SM, vis; simpl. 
    clear - VInj.
    eapply forall_inject_val_list_inject.  
    apply restrict_forall_vals_inject; try eassumption.
    intros. apply REACH_nil. apply orb_true_iff; right. trivial.
  eapply inject_restrict; eassumption. }

rewrite initial_SM_as_inj.
intuition.
Qed.
*)
  Hint Resolve MATCH_initial_core: trans_correct.

Lemma MGE_restrict mu X bnd:
    match_globalenvs mu bnd ->
    (forall b, Plt b bnd -> X b = true) ->
    match_globalenvs (restrict_sm mu X) bnd.
Proof. intros.
destruct H. constructor; eauto.
  rewrite restrict_sm_all, restrict_sm_frgnBlocksSrc. 
  intros. destruct (DOMAIN _ H). split; trivial. 
  apply restrictI_Some. auto. auto.
rewrite restrict_sm_all. 
  intros. destruct (restrictD_Some _ _ _ _ _ H).
  eauto.
Qed.
Lemma MGE_restrict' mu X bnd:
    match_globalenvs mu bnd ->
    (forall b, Ple b bnd -> X b = true) ->
    match_globalenvs (restrict_sm mu X) bnd.
Proof. intros.
eapply MGE_restrict. assumption. intros. apply H0. xomega. 
Qed.
Lemma MGE_restrict'' mu X bnd:
    match_globalenvs mu bnd ->
    (forall b, frgnBlocksSrc mu b = true -> X b = true) ->
    match_globalenvs (restrict_sm mu X) bnd.
Proof. intros.
destruct H. constructor; eauto.
  rewrite restrict_sm_all, restrict_sm_frgnBlocksSrc. 
  intros. destruct (DOMAIN _ H). split; trivial. 
  apply restrictI_Some. auto. auto.
rewrite restrict_sm_all. 
  intros. destruct (restrictD_Some _ _ _ _ _ H).
  eauto.
Qed.

Section MS_RSI.
  Variable mu nu: SM_Injection.
  Hypothesis WDmu : SM_wd mu.
  Hypothesis WDnu : SM_wd nu.
  Hypothesis PG: meminj_preserves_globals ge (as_inj mu).
  Hypothesis INC: inject_incr (as_inj mu) (as_inj nu).
  Variables X Y: block -> bool.
  Hypothesis HX: forall b, vis mu b = true -> X b = true.
  Hypothesis HY: forall b, vis nu b = true -> Y b = true.
  Hypothesis H_mu_nu: forall b, vis mu b = true -> vis nu b = true.
  Hypothesis HXY: inject_incr (restrict (local_of mu) X) 
                              (restrict (local_of nu) Y).
  Hypothesis LBTmu: forall b, locBlocksTgt mu b = true ->
             locBlocksTgt nu b = true.
  Variables m1 m1' m2 m2' :mem.
  Variables PS PT: block -> bool.
  Let muR:= replace_locals mu PS PT.
  Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
  Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
  Hypothesis UNCHANGED: Mem.unchanged_on (local_out_of_reach muR m1) m1' m2'.

  Let muV:= restrict_sm mu (vis mu).
  Let nuY:= restrict_sm nu Y.
  Hypothesis FrgnSrcPres: forall b, frgnBlocksSrc mu b = true ->
             frgnBlocksSrc nu b = true.
  Hypothesis SEP: sm_inject_separated muR nu m1 m1'.

  Hypothesis HAI: local_of mu = local_of nu.
  Hypothesis SMVmu: sm_valid mu m1 m1'.

  Lemma MGE_RSI bnd :
       match_globalenvs muV bnd -> match_globalenvs nuY bnd.
  Proof. intros.
   inv H.
   constructor; eauto.
   intros. destruct (DOMAIN _ H). 
     unfold muV in H0. rewrite restrict_sm_frgnBlocksSrc in H0.
     unfold muV in H1. rewrite restrict_sm_all in H1.
     unfold nuY. rewrite restrict_sm_frgnBlocksSrc, restrict_sm_all.
     rewrite (FrgnSrcPres _ H0). 
     split. trivial.
     destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
        apply restrictI_Some. eapply INC. trivial.
        auto.
   intros. unfold nuY in H. rewrite restrict_sm_all in H. 
     destruct (restrictD_Some _ _ _ _ _ H); clear H. 
     remember (as_inj muV b1) as q. apply eq_sym in Heqq.
     destruct q.
       destruct p. unfold muV in Heqq.
       rewrite restrict_sm_all in Heqq.
       destruct (restrictD_Some _ _ _ _ _ Heqq); clear Heqq.
       rewrite (INC _ _ _ H) in H1; inv H1.
       eapply (IMAGE _ _ _ _ GV); trivial.
       unfold muV; rewrite restrict_sm_all.
       apply restrictI_Some; eassumption.
     destruct SEP as [SEPa [SEPb SEPc]].
       assert (HH: as_inj muR b1 = None). 
         unfold muR. rewrite replace_locals_as_inj.
         unfold muV in Heqq. rewrite restrict_sm_all in Heqq.
         destruct (restrictD_None' _ _ _ Heqq); clear Heqq. trivial.
         destruct H as [bb2 [dd [AI VIS]]].
         specialize (INC _ _ _ AI). rewrite H1 in INC. inv INC.
         destruct PG as [PGa [PGb PGc]]. 
         specialize (PGc _ _ _ _ GV AI). subst.
         destruct (DOMAIN _ H0). unfold muV in H.
         rewrite restrict_sm_frgnBlocksSrc in H.
         unfold vis in VIS. rewrite H, orb_true_r in VIS.
          discriminate.
       destruct (SEPa _ _ _ HH H1).
       destruct (DOMAIN _ H0).
       unfold muV in H5; rewrite restrict_sm_all in H5.
       destruct (restrictD_Some _ _ _ _ _ H5); clear H5.
       destruct (as_inj_DomRng _ _ _ _ H6 WDmu).
       unfold DomTgt, muR in H3. 
       rewrite replace_locals_extBlocksTgt, 
          replace_locals_locBlocksTgt in H3. 
       unfold DomTgt in H8. rewrite H8 in H3. discriminate. 
Qed. 

  Lemma range_private_RSI sp' n sz : forall
    (PRIV : range_private (as_inj muV) m1 m1' sp' n sz)
    (SL : locBlocksTgt muV sp' = true),
   range_private (as_inj nuY) m2 m2' sp' n sz.
  Proof. intros.
    red; intros ? HH. destruct (PRIV _ HH).
    split. eapply UNCHANGED. red; intros. 
      unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL. 
      unfold muR. 
      split. rewrite replace_locals_locBlocksTgt. trivial. 
      rewrite replace_locals_local, replace_locals_pubBlocksSrc.
      intros. left. eapply H0.
      unfold muV; rewrite restrict_sm_all. 
      apply restrictI_Some.
        apply local_in_all; eassumption.
        unfold vis. destruct (local_DomRng _ WDmu _ _ _ H1); intuition.
      eapply Mem.perm_valid_block; eassumption.
      eassumption.
    intros. intros N. 
       unfold nuY in H1; rewrite restrict_sm_all in H1.
       unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL.
       destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
       apply LBTmu in SL.
       destruct (joinD_Some _ _ _ _ _ H2) as [EXT | [EXT LOC]]; clear H2.
         destruct (extern_DomRng _ WDnu _ _ _ EXT).        
         rewrite (extBlocksTgt_locBlocksTgt _ WDnu _ H2) in SL. 
         discriminate.
       rewrite <- HAI in LOC.
       apply MAXPERM in N. eapply (H0 b delta); trivial. 
           unfold muV; rewrite restrict_sm_all. 
           apply restrictI_Some. 
           apply local_in_all; eassumption. 
           unfold vis. destruct (local_DomRng _ WDmu _ _ _ LOC). 
           rewrite H1; trivial. 
       eapply SMVmu. apply local_in_all in LOC; trivial. 
         eapply (as_inj_DomRng _ _ _ _ LOC WDmu). 
(*specialize (HAI _ _ _ H1).
       unfold nuY in H1; rewrite restrict_sm_all in H1.
       unfold muV in H0; rewrite restrict_sm_all in H0. 
       intros N.
       unfold muV in HAI; rewrite restrict_sm_all in HAI. 
       assert (Mem.valid_block m1' sp').
         eapply Mem.perm_valid_block; eassumption.
       eapply (H0 b delta); clear H0. 
         eauto.
       unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL.
       destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
       apply MAXPERM; trivial. 
       eapply SMVmu. 
       destruct (restrictD_Some _ _ _ _ _ (HAI H2)).
       eapply (as_inj_DomRng _ _ _ _ H1 WDmu).*)
  Qed.

  Lemma agree_regs_RSI rs rs' ctx: 
     agree_regs (as_inj muV) ctx rs rs' ->
     agree_regs (as_inj nuY) ctx rs rs'.
  Proof. intros AG; destruct AG. 
    split; intros. 
        eapply val_inject_incr; try eapply H. 
        unfold nuY, muV; repeat rewrite restrict_sm_all. 
        red; intros.
        destruct (restrictD_Some _ _ _ _ _ H2); clear H2.         
        apply restrictI_Some; eauto. 
        trivial.
    apply (H0 _ H1).
  Qed.

Hypothesis BV: forall b1 b1' d, Mem.valid_block m1' b1' ->
           as_inj nu b1 = Some(b1',d) -> Mem.valid_block m1 b1.
Lemma match_stacks_RSI: forall stk stk' bnd
     (MS: match_stacks muV m1 m1' stk stk' bnd),
     match_stacks nuY m2 m2' stk stk' bnd
  with match_stacks_inside_RSI:
       forall stk stk' f' ctx sp' rs',
        match_stacks_inside muV m1 m1' stk stk' f' ctx sp' rs' ->
        match_stacks_inside nuY m2 m2' stk stk' f' ctx sp' rs'.
Proof.
  induction 1; intros.
  { eapply match_stacks_nil; auto. 
      eapply MGE_RSI. eapply MG. 
      (*red. red in VB. xomega. *)
      (*eapply HAI; try assumption. apply H. xomega. *)
       assumption. } 
  { eapply match_stacks_cons; eauto. 
    eapply agree_regs_RSI; eassumption.
    unfold nuY; rewrite restrict_sm_all.
      unfold muV in SP; rewrite restrict_sm_all in SP.
      destruct (restrictD_Some _ _ _ _ _ SP).
      eapply restrictI_Some; eauto.
    unfold nuY; rewrite restrict_sm_locBlocksTgt.
      unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL.
      auto.  
    eapply range_private_RSI; eassumption.
    intros. apply MAXPERM' in H. apply (SSZ2 _ H).
    eapply SMVmu. unfold muV in SL.
      rewrite restrict_sm_locBlocksTgt in SL.
      unfold RNG, DomTgt. rewrite SL; trivial. }
  { eapply match_stacks_untailcall; eauto. 
    eapply range_private_RSI; try eassumption. 
    intros. apply MAXPERM' in H. apply (SSZ2 _ H). 
    eapply SMVmu. unfold muV in SL.
      rewrite restrict_sm_locBlocksTgt in SL.
      unfold RNG, DomTgt. rewrite SL; trivial. 
    unfold nuY; rewrite restrict_sm_locBlocksTgt.
      unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL.
      eauto. } 

  induction 1; intros.
  { unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL. 
    eapply match_stacks_inside_base; eauto.
    (*apply (match_stacks_RSI _ _ _ MS). 
      intros. eapply SMVmu. unfold RNG, DomTgt. rewrite SL; trivial.*) 
      unfold nuY. rewrite restrict_sm_locBlocksTgt. auto. }
  { eapply match_stacks_inside_inlined; eauto. 
    eapply agree_regs_RSI; try eassumption.
      unfold nuY. rewrite restrict_sm_local. eapply HXY.
      unfold muV in SP; rewrite restrict_sm_local in SP.
      destruct (restrictD_Some _ _ _ _ _ SP). 
      apply restrictI_Some; trivial. auto. 
    unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL. 
      unfold nuY. rewrite restrict_sm_locBlocksTgt. auto.
    red; intros. destruct (PAD _ H0). 
      split; intros. 
         eapply UNCHANGED. 
         split; intros. 
           unfold muV in SL; rewrite restrict_sm_locBlocksTgt in SL.
           unfold muR. rewrite replace_locals_locBlocksTgt. trivial.
         unfold muR in H3. rewrite replace_locals_local in H3. 
           left. eapply H2. unfold muV. rewrite restrict_sm_all.
           apply restrictI_Some. apply local_in_all; eassumption. 
           unfold vis. destruct (local_DomRng _ WDmu _ _ _ H3). 
           rewrite H4; trivial. 
         eapply Mem.perm_valid_block; eassumption.
         assumption.
      assert (VB: Mem.valid_block m1' sp'). 
        eapply Mem.perm_valid_block; eassumption. 

      unfold muV in SL. rewrite restrict_sm_locBlocksTgt in SL. 
      intros N. apply MAXPERM in N.
         eapply H2; try eassumption. 
         unfold nuY in H3; rewrite restrict_sm_all in H3.
         destruct (restrictD_Some _ _ _ _ _ H3); clear H3.
         destruct (joinD_Some _ _ _ _ _ H4) as [EXT | [_ LOC]]; clear H4.
           destruct (extern_DomRng _ WDnu _ _ _ EXT). 
           apply (extBlocksTgt_locBlocksTgt _ WDnu) in H4.
           apply LBTmu in SL. rewrite SL in H4. discriminate.
         unfold muV; rewrite restrict_sm_all.
         rewrite <- HAI in LOC.
         apply restrictI_Some.
           apply local_in_all; try eassumption.
         unfold vis. destruct (local_DomRng _ WDmu _ _ _ LOC).
           rewrite H3; trivial.
         apply Mem.perm_valid_block in H1.
         eapply (BV _ sp' delta VB).
         unfold nuY in H3; rewrite restrict_sm_all in H3.
         apply (restrictD_Some _ _ _ _ _ H3). }
  Qed.
End MS_RSI.


(** ** Behold the theorem *)
Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs SrcProg)))
         (entrypoints : list (val * val * signature))
         (entry_ok : entry_points_ok entrypoints)
         (init_mem: exists m0, Genv.init_mem SrcProg = Some m0),
    SM_simulation.SM_simulation_inject (rtl_eff_sem hf)
                                       (rtl_eff_sem hf) ge tge (*entrypoints*).
  intros.
  (*eapply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf.*)
  eapply effect_simulations_lemmas.inj_simulation_star with (match_states:= MATCH)(measure:= RTL_measure).

  Lemma environment_equality: (exists m0:mem, Genv.init_mem SrcProg = Some m0) -> 
                              genvs_domain_eq ge tge.
    intros.
    admit.
    Qed.
  (*
    destruct H0 as [b0]; exists b0;
    rewriter_back;
    [rewrite symbols_preserved| rewrite <- symbols_preserved| rewrite varinfo_preserved| rewrite <- varinfo_preserved]; reflexivity.
  Qed.*)
  Hint Resolve environment_equality: trans_correct.
  auto with trans_correct.

  Lemma MATCH_wd: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                         (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:MATCH d mu c1 m1 c2 m2), SM_wd mu.
    intros. eapply MC. Qed.
  Hint Resolve MATCH_wd: trans_correct.
  eauto with trans_correct.

  Lemma MATCH_RC: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                         (m1 : mem) (c2 : RTL_core) (m2 : mem) (MC:
                                                                  MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
    intros. eapply MC. Qed.
  Hint Resolve MATCH_RC: trans_correct.
  eauto with trans_correct.


  Lemma MATCH_restrict: forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                               (m1 : mem) (c2 : RTL_core) (m2 : mem) (X : block -> bool) (MC: MATCH d mu c1 m1 c2 m2)(HX: forall b : block, vis mu b = true -> X b = true)(RC0:REACH_closed m1 X), MATCH d (restrict_sm mu X) c1 m1 c2 m2.
    intros.
    destruct MC as [MC [RC [PG [GF [VAL [WDmu INJ]]]]]].
    assert (WDR: SM_wd (restrict_sm mu X)).
    apply restrict_sm_WD; assumption.
    split; try rewrite vis_restrict_sm; try rewrite restrict_sm_all; try rewrite restrict_sm_frgnBlocksSrc.
    rewrite restrict_sm_nest; assumption.
    intuition.

    (*meminj_preserves_globals*)
    rewrite <- restrict_sm_all.
    eapply restrict_sm_preserves_globals; auto.
    intros.
    apply HX.
    unfold vis.
    rewrite GF; auto. 
    apply orb_true_r.

    (* sm_valid  *)
    unfold sm_valid; split; intros;
    red in VAL; destruct VAL as [H0 H1].
    apply H0; unfold DOM; erewrite <- restrict_sm_DomSrc; eauto.
    apply H1; unfold RNG; erewrite <- restrict_sm_DomTgt; eauto.
    
    (*  Mem.inject *)
    apply inject_restrict; try assumption.
  Qed.

  Hint Resolve MATCH_restrict: trans_correct.
  auto with trans_correct.

  Lemma MATCH_valid:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                             (m1 : mem) (c2 : RTL_core) (m2 : mem)
                             (MC: MATCH d mu c1 m1 c2 m2), sm_valid mu m1 m2.
    intros.
    apply MC.
  Qed.

  Hint Resolve MATCH_valid: trans_correct.
  eauto with trans_correct.

  (* Here there is a goal missing*)

  Lemma MATCH_PG:  forall (d : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                          (m1 : mem) (c2 : RTL_core) (m2 : mem)(
                            MC: MATCH d mu c1 m1 c2 m2),
                     meminj_preserves_globals ge (extern_of mu) /\
                     (forall b : block,
                        isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
  Proof.
    intros.
    assert (GF: forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true).
    apply MC.
    split; trivial.
    rewrite <- match_genv_meminj_preserves_extern_iff_all; trivial.
    apply MC. apply MC.
  Qed.
  Hint Resolve MATCH_PG: trans_correct.
  eauto with trans_correct.

  Lemma Match_Halted: forall (cd : RTL_core) (mu : SM_Injection) (c1 : RTL_core) 
                             (m1 : mem) (c2 : RTL_core) (m2 : mem) (v1 : val)
        (MC: MATCH cd mu c1 m1 c2 m2)(HALT: halted (rtl_eff_sem hf) c1 = Some v1),
                      exists v2 : val,
                        Mem.inject (as_inj mu) m1 m2 /\
                        val_inject (restrict (as_inj mu) (vis mu)) v1 v2 /\
                        halted (rtl_eff_sem hf) c2 = Some v2.
  Proof.
    intros.
    unfold MATCH in MC; destruct MC as [H0 H1].
    inv H0; simpl in *; inv HALT. 
    Print match_states.
    inv MS. 
    exists v'; split; try assumption. eapply H1.

    inv H0.
    split; trivial.
    rewrite <- restrict_sm_all; assumption.
    inv H0.
    inv MS0.
    rewrite RET in RET0; inv RET0.
    inv H0.
    inv MS.
    rewrite RET in RET0; inv RET0.
    inv H0.
  Qed.
  Hint Resolve Match_Halted: trans_correct.
  eauto with trans_correct.


  Lemma at_external_lemma: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) 
                                  (c2 : RTL_core) (m2 : mem) (e : external_function) 
                                  (vals1 : list val) (ef_sig : signature)(MC: MATCH c1 mu c1 m1 c2 m2) (ATE: at_external (rtl_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
                             Mem.inject (as_inj mu) m1 m2 /\ 
                             (exists vals2 : list val, Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\ at_external (rtl_eff_sem hf) c2 = Some (e, ef_sig, vals2)).
    intros.
    split. inv MC; apply H0.
    inv MC; simpl in *. inv H; inv ATE.
    destruct fd; inv H1. inv FD; simpl in *. 
    destruct (BuiltinEffects.observableEF_dec hf e0); inv H2.
    exists args'.
    split. apply val_list_inject_forall_inject.
    autorewrite with restrict in VINJ; assumption.
    trivial.
  Qed.
  Hint Resolve at_external_lemma: trans_correct.
  eauto with trans_correct.

  Lemma Match_AfterExternal: 
    forall (mu : SM_Injection) (st1 : RTL_core) (st2 : RTL_core) (m1 : mem) (e : external_function) (vals1 : list val) (m2 : mem) (ef_sig : signature) (vals2 : list val) (e' : external_function) (ef_sig' : signature) 
           (MemInjMu : Mem.inject (as_inj mu) m1 m2)
           (MatchMu : MATCH st1 mu st1 m1 st2 m2)
           (AtExtSrc : at_external (rtl_eff_sem hf) st1 = Some (e, ef_sig, vals1))
           (AtExtTgt : at_external (rtl_eff_sem hf) st2 = Some (e', ef_sig', vals2))
           (ValInjMu : Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
           (pubSrc' : block -> bool)
           (pubSrcHyp : pubSrc' =
                        (fun b : block =>
                           locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
           (pubTgt' : block -> bool)
           (pubTgtHyp : pubTgt' =
                        (fun b : block =>
                           locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
           (nu : SM_Injection)
           (NuHyp : nu = replace_locals mu pubSrc' pubTgt')
           (nu' : SM_Injection)
           (ret1 : val)
           (m1' : mem)
           (ret2 : val)
           (m2' : mem)
           (INC : extern_incr nu nu')
           (SEP : sm_inject_separated nu nu' m1 m2)
           (WDnu' : SM_wd nu')
           (SMvalNu' : sm_valid nu' m1' m2')
           (MemInjNu' : Mem.inject (as_inj nu') m1' m2')
           (RValInjNu' : val_inject (as_inj nu') ret1 ret2)
           (FwdSrc : mem_forward m1 m1')
           (FwdTgt : mem_forward m2 m2')
           (frgnSrc' : block -> bool)
           (frgnSrcHyp : frgnSrc' =
                         (fun b : block =>
                            DomSrc nu' b &&
                                   (negb (locBlocksSrc nu' b) &&
                                         REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
           (frgnTgt' : block -> bool)
           (frgnTgtHyp : frgnTgt' =
                         (fun b : block =>
                            DomTgt nu' b &&
                                   (negb (locBlocksTgt nu' b) &&
                                         REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
           (mu' : SM_Injection)
           (Mu'Hyp : mu' = replace_externs nu' frgnSrc' frgnTgt')
           (UnchPrivSrc : Mem.unchanged_on
                            (fun (b : block) (_ : Z) =>
                               locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
           (UnchLOOR : Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
    exists (st1' st2' : RTL_core),
      after_external (rtl_eff_sem hf) (Some ret1) st1 = Some st1' /\
      after_external (rtl_eff_sem hf) (Some ret2) st2 = Some st2' /\
      MATCH st1' mu' st1' m1' st2' m2'.
  Proof. intros. 
         destruct MatchMu as [MC [RC [PG [GF [VAL [WDmu [INJ GFP]]]]]]].
         inv MC; simpl in *; inv AtExtSrc.
         destruct fd; inv H0.
         destruct fd'; inv AtExtTgt.
         inv FD.
         destruct (BuiltinEffects.observableEF_dec hf e1); inv H0; inv H1.
         rename o into OBS.
         exists (RTL_Returnstate stk ret1). eexists.
         split. reflexivity.
         split. reflexivity.
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
         assert (PHnu': meminj_preserves_globals (Genv.globalenv SrcProg) (as_inj nu')).
         subst. clear - INC SEP PG GF WDmu WDnu'.
         apply meminj_preserves_genv2blocks in PG.
         destruct PG as [PGa [PGb PGc]].
         apply meminj_preserves_genv2blocks.
         split; intros.
         specialize (PGa _ H).
         apply joinI; left. apply INC.
         rewrite replace_locals_extern.
         apply foreign_in_extern.
         assert (GG: isGlobalBlock ge b = true).
         unfold isGlobalBlock, ge. apply genv2blocksBool_char1 in H.
         rewrite H. trivial.
         destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
         rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
         assumption.
         split; intros. specialize (PGb _ H).
         apply joinI; left. apply INC.
         rewrite replace_locals_extern. 
         assert (GG: isGlobalBlock ge b = true). (*4 goals*)
         unfold isGlobalBlock, ge. apply genv2blocksBool_char2 in H.
         rewrite H. intuition. (*3 goals*)
         destruct (frgnSrc _ WDmu _ (GF _ GG)) as [bb2 [dd [FF FT2]]].
         rewrite (foreign_in_all _ _ _ _ FF) in PGb. inv PGb.
         apply foreign_in_extern; eassumption. (*2 goals*)
         eapply (PGc _ _ delta H). specialize (PGb _ H). clear PGa PGc.
         remember (as_inj mu b1) as d.
         destruct d; apply eq_sym in Heqd. (*3 goals*)
         destruct p. 
         apply extern_incr_as_inj in INC; trivial. (*3 goals*)
         rewrite replace_locals_as_inj in INC.
         rewrite (INC _ _ _ Heqd) in H0. trivial. (*3 goals*)
         destruct SEP as [SEPa _].
         rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt in SEPa. 
         destruct (SEPa _ _ _ Heqd H0).
         destruct (as_inj_DomRng _ _ _ _ PGb WDmu).
         congruence. (*1 goal*)
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
         destruct IHL. inv H.
         apply andb_true_iff in H. simpl in H. 
         destruct H as[DomNu' Rb']. 
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
         assert (GFnu': forall b, isGlobalBlock (Genv.globalenv SrcProg) b = true ->
                                  DomSrc nu' b &&
                                         (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
         intros. specialize (GF _ H).
         assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
         rewrite replace_locals_frgnBlocksSrc in FSRC.
         rewrite FSRC in GF.
         rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ GF). 
         apply andb_true_iff; simpl.
         split.
         unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ GF). intuition.
         apply REACH_nil. unfold exportedSrc.
         rewrite (frgnSrc_shared _ WDnu' _ GF). intuition.
rewrite restrict_sm_all in *.
exploit (eff_after_check1 mu); try eassumption; try reflexivity.
  eapply val_list_inject_forall_inject.
  eapply val_list_inject_incr; try eassumption.
    apply restrict_incr.
intros [WDnu [SMVnu [MinjNu VinjNu]]].
assert (WDR: SM_wd (restrict_sm mu (vis mu))).
   apply restrict_sm_WD; trivial.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
assert (RRC1': REACH_closed m1'
     (fun b : block =>
      locBlocksSrc nu' b
      || DomSrc nu' b &&
         (negb (locBlocksSrc nu' b) &&
          REACH m1' (exportedSrc nu' (ret1 :: nil)) b))).
  intuition.
assert (WDR': SM_wd
     (restrict_sm nu'
        (fun b : block =>
         locBlocksSrc nu' b
         || DomSrc nu' b &&
            (negb (locBlocksSrc nu' b) &&
             REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))).
               apply restrict_sm_WD.
                  assumption.
                 intros. unfold vis in H1.
                 destruct (locBlocksSrc nu' b); simpl in *; trivial. 
                 apply andb_true_iff; split. 
                 unfold DomSrc.
                   rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H1).
                   intuition.
                 apply REACH_nil. unfold exportedSrc.
                 rewrite sharedSrc_iff_frgnpub, H1. intuition. trivial. 

split.
Focus 2. unfold vis in *.
     rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj in *. intuition.
  
econstructor; try rewrite restrict_sm_all; try eassumption.
         { (*Match_stacks*)
           clear UnchPrivSrc OBS INCvisNu'. 
           eapply match_stacks_bound. instantiate (1:=Mem.nextblock m2).
           2: eapply forward_nextblock; eassumption.
           eapply match_stacks_RSI.
             18: eapply MS.
             12: eapply UnchLOOR.
             assumption.  
             assumption.  
             assumption.  
             rewrite replace_externs_as_inj. 
                apply extern_incr_as_inj in INC. 
                rewrite replace_locals_as_inj in INC; assumption. 
                assumption. 
             instantiate (1:= vis mu). trivial.
             trivial. 
             rewrite replace_externs_vis. intros.
                exploit extern_incr_vis; try eassumption.
                rewrite replace_locals_vis; intros. rewrite H2 in H1.
                clear H2.
                unfold vis in H1. remember (locBlocksSrc nu' b) as q.    
                destruct q; simpl in *; trivial.
                apply andb_true_iff; split.
                unfold DomSrc. 
                rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H1). 
                intuition. 
                apply REACH_nil. unfold exportedSrc. 
                rewrite sharedSrc_iff_frgnpub, H1; trivial.
                intuition. 
             rewrite replace_externs_local, replace_externs_vis.
               assert (LOC: local_of mu = local_of nu').
                 red in INC. rewrite replace_locals_local in INC. 
                 eapply INC.
               rewrite <- LOC in *. 
               red; intros ? ? ? Hb. 
               destruct (restrictD_Some _ _ _ _ _ Hb); clear Hb.
               apply restrictI_Some; trivial.
               destruct (local_DomRng _ WDmu _ _ _ H1) as [lS _].
               assert (LS: locBlocksSrc mu = locBlocksSrc nu').
                  red in INC. 
                  rewrite replace_locals_locBlocksSrc in INC. 
                  eapply INC.
               rewrite <- LS, lS. trivial.
             rewrite replace_externs_locBlocksTgt. 
                assert (LOC: locBlocksTgt mu = locBlocksTgt nu').
                 red in INC. 
                 rewrite replace_locals_locBlocksTgt in INC. 
                 eapply INC.
                rewrite LOC; trivial. 
             intros. eapply FwdSrc; eassumption.
             intros. eapply FwdTgt; eassumption.
             rewrite replace_externs_frgnBlocksSrc.
               intros. unfold DomSrc. 
               assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc nu').
                 red in INC. 
                 rewrite replace_locals_frgnBlocksSrc in INC. 
                 apply INC.
               rewrite FRG in H1.
               specialize (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H1).
               intros EE.
               rewrite (extBlocksSrc_locBlocksSrc _ WDnu' b), EE; simpl.
               apply REACH_nil. apply orb_true_iff. right. 
                apply frgnSrc_shared; trivial. 
               trivial.
              clear - SEP. red. red in SEP.
                  rewrite replace_externs_DomSrc, 
                   replace_externs_DomTgt, replace_externs_as_inj. 
                  rewrite replace_locals_as_inj, 
                  replace_locals_DomSrc, replace_locals_DomTgt in *.
                  apply SEP.
              rewrite replace_externs_local. 
                red in INC. rewrite replace_locals_local in INC.
                eapply INC.
             assumption.
             rewrite replace_externs_as_inj. intros.
               red in SEP. rewrite replace_locals_as_inj,
                  replace_locals_DomSrc, replace_locals_DomTgt in SEP. 
                  destruct SEP as [SEPa [SEPb SEPc]].
               remember (as_inj mu b1) as w; apply eq_sym in Heqw. 
               destruct w.
                 destruct p.
                 apply VAL. apply (as_inj_DomRng _ _ _ _ Heqw WDmu).
               destruct (SEPa _ _ _ Heqw H2).
                 elim (SEPc _ H4). apply (as_inj_DomRng _ _ _ _ H2 WDnu'). trivial.
         }
         rewrite replace_externs_as_inj, replace_externs_vis. 
          clear - RValInjNu' WDnu'.
          inv RValInjNu'; econstructor; eauto.
          apply restrictI_Some; trivial.
          destruct (locBlocksSrc nu' b1); simpl; trivial.
          destruct (as_inj_DomRng _ _ _ _ H WDnu') as [dS dT].
          rewrite dS; simpl.
          apply REACH_nil. unfold exportedSrc.
          apply orb_true_iff; left.
          apply getBlocks_char. exists ofs1; left; eauto.
         rewrite replace_externs_as_inj, replace_externs_vis.
           eapply inject_restrict; try eassumption.
Qed.
  Hint Resolve Match_AfterExternal: trans_correct.
  eauto with trans_correct.

  clear entry_ok.
  clear init_mem.

(*New restrict lemmas*)
    Lemma as_inj_retrict: forall mu b1 b2 d,
      as_inj (restrict_sm mu (vis mu)) b1 = Some (b2, d) ->
      as_inj mu b1 = Some (b2, d).
      intros; autorewrite with restrict in H.
      unfold restrict in H; destruct (vis mu b1) eqn:eq; inv H; auto.
    Qed.

  Ltac extend_smart:=  let x := fresh "x" in extensionality x.
  Ltac rewrite_freshloc := match goal with
                             | H: (Mem.storev _ _ _ _ = Some _) |- _ => rewrite (storev_freshloc _ _ _ _ _ H)
                             | H: (Mem.free _ _ _ _ = Some _) |- _ => apply freshloc_free in H; rewrite H
                             | _ => try rewrite freshloc_irrefl
                           end.
  Ltac loc_alloc_solve := apply sm_locally_allocatedChar; repeat split; try extend_smart;
                          try rewrite_freshloc; intuition.
  Print sm_locally_allocated.

  Lemma step_simulation_noeffect: forall (st1 : RTL_core) (m1 : mem) (st1' : RTL_core) (m1' : mem)
                                         (CS: corestep (rtl_eff_sem hf) ge st1 m1 st1' m1')
                                         (st2 : RTL_core) (mu : SM_Injection) (m2 : mem)
                                         (MC:MATCH st1 mu st1 m1 st2 m2),
                                  exists (st2' : RTL_core) (m2' : mem),
                                    (core_semantics_lemmas.corestep_plus (rtl_eff_sem hf) tge st2 m2 st2' m2' \/
                                     (RTL_measure st1' < RTL_measure st1)%nat /\
                                     core_semantics_lemmas.corestep_star (rtl_eff_sem hf) tge st2 m2 st2' m2') /\
                                    exists (mu' : SM_Injection),
                                      intern_incr mu mu' /\
                                      sm_inject_separated mu mu' m1 m2 /\
                                      sm_locally_allocated mu mu' m1 m2 m1' m2' /\
                                      MATCH st1' mu' st1' m1' st2' m2'.
    
    intros.
    simpl in *.
    destruct MC as [MS H].
    
    inv CS;
      inv MS.
    (* Inop *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    eexists. eexists. 

    split.
    left.
    eapply core_semantics_lemmas.corestep_plus_one.
    eapply rtl_corestep_exec_Inop. eassumption.
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)(* This is a Hint now*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH.
    intuition.
    eapply match_regular_states; first [eassumption| split; eassumption].


    (* Iop *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    repeat open_Hyp.
    exploit eval_operation_inject. 

    eapply match_stacks_inside_globals; eauto.
    exact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
    fold (sop ctx op). intros [v' [A B]].
    eexists. eexists.
    split; simpl.
    left. 
    eapply core_semantics_lemmas.corestep_plus_one. 

    eapply rtl_corestep_exec_Iop. eassumption.
    erewrite eval_operation_preserved; eauto.
    exact symbols_preserved. 
    econstructor; eauto. 
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH.
    intuition.
    eapply match_regular_states; eauto.
    apply match_stacks_inside_set_reg; auto.
    eapply restrict_sm_WD; auto.
    apply agree_set_reg; auto. 

    (* Iload *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
    fold (saddr ctx addr). intros [a' [P Q]].
    exploit Mem.loadv_inject; eauto. intros [v' [U V]].
    assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
    eexists. eexists.
    split; simpl. left.
    eapply core_semantics_lemmas.corestep_plus_one. 
    eapply rtl_corestep_exec_Iload; try eassumption.
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH;
      intuition.
    eapply match_regular_states; eauto.
    apply match_stacks_inside_set_reg; auto.
    eapply restrict_sm_WD; auto.
    apply agree_set_reg; auto.
    

    (* Istore *)

    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    
    destruct H as [RC [PG [GF [SMV [WD INJ]]]]].
    exploit eval_addressing_inject.
    eapply match_stacks_inside_globals. 
    eassumption.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
    fold saddr. intros [a' [P Q]].
    Check Mem.storev_mapped_inject. 
    exploit Mem.storev_mapped_inject. 
    eexact INJ.
    eassumption.
    eapply val_inject_incr; try eapply Q.
    autorewrite with restrict.
    apply restrict_incr.
    eapply agree_val_reg; eauto.
    eapply agree_regs_incr.
    eassumption.
    autorewrite with restrict.
    apply restrict_incr.
    
    intros [m2' [U V]].
    assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
    eexists. eexists.
    split; simpl.
    left.
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Istore; eauto.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    destruct a; simpl in H1; try discriminate.
    destruct a'; simpl in U; try discriminate.
    assert (RC1': REACH_closed m1' (vis mu)).
    eapply REACH_Store;
    try eassumption.
    inv Q.
    autorewrite with restrict in H8.
    eapply restrictD_Some.
    eapply H8.
    intros.
    rewrite getBlocks_char in H5.
    destruct H5. 
    destruct H5.
    Check agree_val_reg.
    assert (val_inject (as_inj (restrict_sm mu (vis mu))) rs # src rs' # (sreg ctx src)).
    eapply agree_val_reg; eauto.
    rewrite H5 in H6.
    inv H6.
    autorewrite with restrict in H10.
    eapply restrictD_Some.
    eassumption.
    simpl in H5.
    contradiction.

    unfold MATCH;
      intuition.
    (*match_states*)
    econstructor; eauto.
    eapply match_stacks_inside_store; eauto.
    apply restrict_sm_WD; auto.
    autorewrite with restrict; eapply inject_restrict; try eassumption.
    
    eapply Mem.store_valid_block_1; eauto.
    eapply range_private_invariant; eauto.
    intros; split; auto. eapply Mem.perm_store_2; eauto.
    intros; eapply Mem.perm_store_1; eauto.
    intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.
    inv H2.

    (* sm_valid mu m1' m2' *)
    split; intros. 
    eapply Mem.store_valid_block_1; try eassumption.
    eapply SMV; assumption.
    eapply Mem.store_valid_block_1; try eassumption.
    eapply SMV; assumption.
    
    (* Icall *)
    exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
    exploit find_function_agree; eauto.
    eauto. intros [fd' [A B]].
    exploit tr_funbody_inv; eauto. intros TR. inv TR.

    (* not inlined *)
    eexists. eexists.
    split; simpl.
    left.
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Icall; eauto.
    Print rtl_corestep_exec_Icall.
    eapply sig_function_translated; eauto.
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    split.
    econstructor; eauto.
    eapply match_stacks_cons; eauto.
    destruct MS0; assumption.
    eapply agree_val_regs; eauto.   
    intuition.

    (* inlined *)
    assert (fd = Internal f0).
    simpl in H1. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat SrcProg). 
    try eassumption. eauto. intros. 
    unfold ge in H1. congruence.
    subst fd.
    
    eexists. eexists.
    split; simpl.
    right; split. simpl; omega.
    eapply core_semantics_lemmas.corestep_star_zero.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
      intuition.
    Focus 1.
    eapply match_call_regular_states; eauto. (* match_call_regular_states*)
    assert (SL: locBlocksTgt (restrict_sm mu (vis mu)) sp' = true) by (destruct MS0; assumption).
    eapply match_stacks_inside_inlined; eauto.
    Lemma local_of_loc_inj: forall mu b b' delta (WD: SM_wd mu) (loc: locBlocksTgt mu b' = true), as_inj  mu b = Some (b', delta) -> local_of mu b = Some (b', delta).
      unfold as_inj. unfold join. 
      intros.
      destruct WD.
      destruct (extern_of mu b) eqn:extern_mu_b; try assumption.
      destruct p. inv H.
      apply extern_DomRng in extern_mu_b.
      destruct extern_mu_b as [extDom  extRng].
      destruct (disjoint_extern_local_Tgt b'); [rewrite loc in H | rewrite extRng in H]; discriminate. 
    Qed. (* Need to get  locBlocksTgt from MS0*)
    apply local_of_loc_inj; auto;
     try (apply restrict_sm_WD); auto.
    
    red; intros. apply PRIV. inv H14. destruct H17.
    xomega.
    apply agree_val_regs_gen; auto.
    red; intros; apply PRIV. destruct H17. omega.

    (* Itailcall *)
    exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
    exploit find_function_agree; eauto. intros [fd' [A B]].
    assert (PRIV': range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    eapply range_private_free_left; eauto. 
    inv FB. rewrite <- H5. auto.
    exploit tr_funbody_inv; eauto.
    intros TR. 
    inv TR.

    (* within the original function *)
    inv MS0; try congruence.

    assert (X: { m1' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto. xomega.
    destruct X as [m2' FREE].
    
    eexists. eexists.
    split; simpl.
    left. 
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Itailcall; eauto.
    eapply sig_function_translated; eauto.
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    
    assert (Mem.inject (as_inj mu) m1' m2').
    eapply Mem.free_right_inject. eapply Mem.free_left_inject. eapply H12.
    eassumption.
    eassumption.

    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
    eelim Q.
    autorewrite with restrict.
    eapply restrictI_Some.
    eapply H11.
    rewrite restrict_sm_locBlocksTgt in SL.
    erewrite <- (as_inj_locBlocks _ b1 sp') in SL; try eassumption.
    unfold vis.
    rewrite SL.
    eapply orb_true_l.
    replace (ofs + delta - delta) with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

    unfold MATCH.
    intuition.
    econstructor; eauto.
    eapply match_stacks_bound with (bound := sp'). 
    eapply match_stacks_invariant; eauto.
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.nextblock_free; eauto. red in VB; xomega.
    eapply agree_val_regs; eauto.
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
    eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    eapply REACH_closed_free; eauto.
    (* sm_valid mu m1' m2' *)
    split; intros. 
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H7; assumption.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H7; assumption.
(*    replace (ofs + delta - dstk ctx) with ofs by omega. *)

    (* turned into a call *)
    eexists. eexists. split; simpl.
    left. 
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Icall; eauto.
    eapply sig_function_translated; eauto.
    
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    econstructor; eauto.
    eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_invariant; eauto. 
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto.
    destruct MS0; assumption.
   
    eapply agree_val_regs; eauto.
    eapply Mem.free_left_inject; eauto.
    eapply REACH_closed_free; eauto.
    
    (*  sm_valid mu m1' m2 *)
    split; intros. 
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H7; assumption.
    eapply H7; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)
    eapply Mem.free_left_inject; eauto.

    (* inlined *)
    assert (fd = Internal f0).
    simpl in H1. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat SrcProg); eauto. intros. 
    unfold ge in H1. congruence.
    subst fd.
    eexists. eexists.
    split; simpl.
    right; split. simpl; omega. 
    eapply core_semantics_lemmas.corestep_star_zero.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
      intuition.
    econstructor; eauto.
    eapply match_stacks_inside_inlined_tailcall; eauto.
    eapply match_stacks_inside_invariant; eauto.
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto.
    apply agree_val_regs_gen; auto.
    eapply Mem.free_left_inject; eauto.
    red; intros; apply PRIV'. 
    assert (dstk ctx <= dstk ctx'). red in H15; rewrite H15. apply align_le. apply min_alignment_pos.
    omega.
    eapply REACH_closed_free; eauto.
    (* sm_valid mu m1' m2 *)
    split; intros.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H11; assumption.
    eapply H11; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)
    eapply Mem.free_left_inject; eauto.

    { (* builtin*)
      exploit tr_funbody_inv; eauto. intros TR; inv TR.
      rename MINJ into MINJR.
      destruct H as [RC [PG [Glob [SMV [WD MINJ]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      rewrite restrict_sm_all in *.
      assert (ArgsInj:= agree_val_regs _ _ _ _ args AG).
      exploit (BuiltinEffects.inlineable_extern_inject _ _ GDE_lemma);
        try eapply H1; try eassumption.
        apply symbols_preserved. 
      intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
      exists (RTL_State stk' f' (Vptr sp' Int.zero) (spc ctx pc')
               (rs'#(sreg ctx res) <- vres')), tm'; split.
        left. apply core_semantics_lemmas.corestep_plus_one. 
                eapply rtl_corestep_exec_Ibuiltin; eauto. 
      exists mu'. intuition.
      assert (ISEP: inject_separated (restrict (as_inj mu) (vis mu))
                    (restrict (as_inj mu') (vis mu')) m1 m2).
                red. intros ??? RAI RAI'.
                destruct (restrictD_Some _ _ _ _ _ RAI')
                  as [AI' VIS']; clear RAI'.
                destruct (restrictD_None' _ _ _ RAI) 
                    as [AI | [bb2 [dd [AI VIS]]]]; clear RAI.
                  apply sm_inject_separated_mem in SEPARATED.
                  apply (SEPARATED _ _ _ AI AI'). trivial. 
                rewrite (intern_incr_vis_inv _ _ WD WD' 
                    INCR _ _ _ AI VIS') in VIS; discriminate.
      split. 
      {  econstructor; eauto.
        { eapply match_stacks_inside_set_reg.
            apply restrict_sm_WD; trivial.  
            eapply match_stacks_inside_extcall; try eapply MS0.
              apply restrict_sm_WD; trivial.  
              apply restrict_sm_WD; trivial.  
              intros; eapply external_call_max_perm; eauto. 
              intros; eapply external_call_max_perm; eauto.
              rewrite restrict_sm_all. apply OUTOFREACH.
              rewrite restrict_sm_all. apply MINJR.
              apply restrict_sm_intern_incr; trivial. 
              repeat rewrite restrict_sm_all; trivial.
              clear - SMV. destruct SMV.
                split; intros.
                 rewrite restrict_sm_DOM in H1. apply (H _ H1).
                 rewrite restrict_sm_RNG in H1. apply (H0 _ H1). 
              apply VB. }
        rewrite restrict_sm_all. apply agree_set_reg; eauto.  
          eapply agree_regs_incr; eauto. 
          apply (intern_incr_restrict _ _ WD' INCR).
        rewrite restrict_sm_all. 
          apply (intern_incr_restrict _ _ WD' INCR). assumption.
        rewrite restrict_sm_all. apply inject_restrict; assumption.
        eapply external_call_mem_forward; try eassumption.
        { rewrite restrict_sm_all.
          eapply range_private_extcall; try eassumption.
            intros. eapply external_call_mem_forward; eauto. 
            apply (intern_incr_restrict _ _ WD' INCR). }
        intros. apply SSZ2. eapply external_call_max_perm; eauto. 
      }
      intuition.
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. apply Glob; assumption. }

    (* Icond *)

    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    assert (eval_condition cond rs'##(sregs ctx args) m2 = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto. 
    
    eexists. eexists. 
    split; simpl.
    left. 
    eapply core_semantics_lemmas.corestep_plus_one.
    eapply rtl_corestep_exec_Icond; eauto.

    exists mu. intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    destruct b;
      econstructor; eauto.


    (* jumptable *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    assert (H3: val_inject (as_inj (restrict_sm mu (vis mu))) rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
    rewrite H1 in H3; inv H3.
    
    eexists. eexists.
    split; simpl.
    left.
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Ijumptable; eauto.
    rewrite list_nth_z_map. rewrite H2. simpl; reflexivity. 
    
    exists mu. intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    econstructor; eauto.


    (* return *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.

    (* not inlined *)
    inv MS0; try congruence.
    assert (X: { m1' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
    destruct X as [m2' FREE].
    
    eexists. eexists.
    split; simpl.
    left.
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Ireturn; eauto. 
    
    exists mu.
    intuition.
    (* apply intern_incr_refl. *)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
      intuition.
    econstructor; eauto.
    eapply match_stacks_bound with (bound := sp'). 
    eapply match_stacks_invariant; eauto.
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.nextblock_free; eauto. red in VB; xomega.
    destruct or; simpl. apply agree_val_reg; auto. auto.

    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H16 in PRIV. eapply range_private_free_left; eauto. 
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
    eelim B; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

    eapply REACH_closed_free; eauto.

    (*  sm_valid mu m1' m2 *)
    split; intros.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H8; assumption.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H8; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H16 in PRIV. eapply range_private_free_left; eauto. 
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
    eelim B. 
    autorewrite with restrict.
    eapply restrictI_Some.
    apply H10.
    rewrite restrict_sm_locBlocksTgt in SL.
    erewrite <- (as_inj_locBlocks _ b1 sp') in SL; try eassumption.
    unfold vis.
    rewrite SL.
    eapply orb_true_l.
    replace (ofs + delta - delta) with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    
    (* inlined *)
    eexists. eexists.             
    split; simpl.
    right; split; simpl. omega.
    
    eapply core_semantics_lemmas.corestep_star_zero.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)

    apply sm_inject_separated_same_sminj.
    loc_alloc_solve. 
    
    unfold MATCH;
      intuition.
    econstructor; eauto.
    
    
    eapply match_stacks_inside_invariant; eauto. 
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto.
    destruct or; simpl. apply agree_val_reg; auto. auto.
    eapply Mem.free_left_inject; eauto.
    inv FB. subst.  rewrite H13 in PRIV. eapply range_private_free_left; eauto.
    
    eapply REACH_closed_free; eauto.
    (*sm_valid*)
    split; intros.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H8; assumption.
    eapply H8; assumption.
    (*  Mem.inject (as_inj mu) m1' m2 *)
    eapply Mem.free_left_inject; eauto.




    (* internal function, not inlined *)
    assert (A: exists f', tr_function fenv f f' /\ fd' = Internal f'). 
    Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. 
    destruct A as [f' [TR EQ]]. inversion TR; subst.
    repeat open_Hyp.
    exploit alloc_parallel_intern; 
      eauto. apply Zle_refl. 
    instantiate (1 := fn_stacksize f'). inv H1. xomega.
    intros [mu' [m2' [sp' [A [B [C [D E]]]]]]].
    
    eexists. eexists.
    split; simpl.
    left.
    eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_function_internal; eauto.

    rewrite H5.
    exists mu'. 
    intuition.

    unfold MATCH; intuition.
    rewrite H6.
    rewrite <- H5.
    
    eapply match_regular_states; eauto.
    assert (SP: sp' = Mem.nextblock m2) by (eapply Mem.alloc_result; eauto).
    apply match_stacks_inside_base.
    rewrite <- SP in MS0. 
    eapply (match_stacks_invariant (restrict_sm mu (vis mu))); eauto.
    eapply restrict_sm_intern_incr; auto.
    eapply restrict_sm_WD; auto.
    
    intros. 
    destruct (eq_block b1 stk). 
    subst b1.
    apply as_inj_retrict  in H20; rewrite D in H20; inv H20. subst b2. eelim Plt_strict; eauto.
    rewrite <- H20.
    autorewrite with restrict.
    unfold restrict.
    rewrite H14; auto.
    assert (vis mu' b1 = true ).
    destruct (vis mu' b1) eqn:vismu'b1; auto.
    autorewrite with restrict in H20.
    unfold restrict in H20.
    rewrite vismu'b1 in H20; inv H20.
    erewrite (intern_incr_vis_inv mu mu'); auto.
    rewrite H22; auto.
    rewrite <- H14; auto.
    apply as_inj_retrict in H20; eassumption.
    
    intros. exploit Mem.perm_alloc_inv. eexact H0. eauto. 
    destruct (eq_block b1 stk); intros; auto. 
    subst b1. apply as_inj_retrict in H20.
    rewrite D in H20; inv H20. subst b2. eelim Plt_strict; eauto.  

    intros. eapply Mem.perm_alloc_1; eauto. 
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto. 
    rewrite dec_eq_false; auto.

    (*This should be a lemma! *)
    Lemma alloc_local_restrict: forall mu mu' m1 m2 m1' m2' sp' f' (A : Mem.alloc m2 0 (fn_stacksize f') = (m2', sp')) (H15 : sm_locally_allocated mu mu' m1 m2 m1' m2') (SP: sp' = Mem.nextblock m2), locBlocksTgt (restrict_sm mu' (vis mu')) sp' = true.
      intros.
      unfold sm_locally_allocated in H15.
    destruct mu.
    destruct mu'; simpl in *.
    intuition.
    rewrite H1.
    assert (fl: freshloc m2 m2' sp' = true).
    unfold freshloc.
    assert (vb: ~ Mem.valid_block m2 sp').
    unfold Mem.valid_block.
    subst sp'.
    xomega.
    assert (vb': Mem.valid_block m2' sp').
    unfold Mem.valid_block.
    (*erewrite (Mem.nextblock_alloc m2 _ _ m2' sp').*)
    rewrite (Mem.nextblock_alloc m2 0 (fn_stacksize f') m2' sp').
    subst sp'.
    xomega.
    subst sp'.
    exact A.
    destruct (valid_block_dec m2' sp'); destruct (valid_block_dec m2 sp'); intuition.
    rewrite fl; apply orb_true_r.
    Qed.
    (*End of lemma.*)
    eapply alloc_local_restrict; eauto.

    auto. auto. auto.
    rewrite H5. apply agree_regs_init_regs.
    Check val_list_inject_incr.
    eapply val_list_inject_incr.
    autorewrite with restrict.
    eapply intern_incr_restrict; try (apply C); auto.
    autorewrite with restrict in VINJ; auto.
    inv H1; auto. 
    
    Lemma freshalloc_restricted_map: forall mu mu' stk m1 m1' m2 m2' f sp' delta,
                                 Mem.alloc m1 0 (fn_stacksize f) = (m1', stk) ->
                                 sm_locally_allocated mu mu' m1 m2 m1' m2' ->
                                 as_inj mu' stk = Some (sp', delta) ->
                                 as_inj (restrict_sm mu' (vis mu')) stk = Some (sp', delta).
    intros mu mu' stk m1 m1' m2 m2' f sp' delta alloc loc_alloc map.
      autorewrite with restrict.
      unfold restrict.
      rewrite map.
      unfold vis.


    (*This should be a lemma*)
    Lemma allocated_is_local: forall mu mu' stk m1 m1' m2 m2' f,  
                     Mem.alloc m1 0 (fn_stacksize f) = (m1', stk) ->
                     sm_locally_allocated mu mu' m1 m2 m1' m2' ->
                     locBlocksSrc mu' stk = true. 
    intros  mu mu' stk m1 m1' m2 m2' f H1 H2.
    rewrite (Mem.alloc_result _ _ _ _ stk H1).
    rewrite (Mem.alloc_result _ _ _ _ stk H1) in H1.
    unfold sm_locally_allocated in H2.
    destruct mu; destruct mu'; simpl in *.
    intuition.
    rewrite H.
    assert (fl: freshloc m1 m1' (Mem.nextblock m1) = true).
    unfold freshloc.
    assert (vb: ~ Mem.valid_block m1 (Mem.nextblock m1)).
    unfold Mem.valid_block.
    xomega.
    assert (vb': Mem.valid_block m1' (Mem.nextblock m1)).
    unfold Mem.valid_block.
    rewrite (Mem.nextblock_alloc m1 0 (fn_stacksize f) m1' (Mem.nextblock m1)).
    xomega.
    auto.
    destruct (valid_block_dec m1' (Mem.nextblock m1)); destruct (valid_block_dec m1 (Mem.nextblock m1)); intuition.
    rewrite fl; apply orb_true_r.
    Qed.
    
    erewrite allocated_is_local; eauto.
    Qed.
    eapply  freshalloc_restricted_map; eauto.
    rewrite H2; auto.
    
    autorewrite with restrict.
    apply inject_restrict; auto.

    eapply Mem.valid_new_block; eauto.
    red; intros. split.
    eapply Mem.perm_alloc_2; eauto. inv H1; xomega.
    intros; red; intros. exploit Mem.perm_alloc_inv. eexact H0. eauto.
    destruct (eq_block b stk); intros; apply as_inj_retrict in H21. 
    subst. 
    rewrite D in H21; inv H21. inv H1; xomega.
    rewrite H14 in H21; auto. eelim Mem.fresh_block_alloc. eexact A.
    eapply Mem.mi_mappedblocks.
    apply H13.
    apply H21.


    intros.
    exploit Mem.perm_alloc_3; eauto.
    xomega.

    apply (meminj_preserves_incr_sep ge (as_inj mu) H9 m1 m2); eauto.
    apply intern_incr_as_inj; auto.
    apply sm_inject_separated_mem; auto.

    eapply intern_incr_meminj_preserves_globals_as_inj in H17.
    destruct H17 as [H00 H01]; apply H01; auto.
    eexact H20.
    exact H12.
    split; eauto.
    assumption.


(* internal function, inlined *)
inversion FB; subst.
repeat open_Hyp.
exploit alloc_left_mapped_sm_inject; try eassumption.
(* sp' is local *)
destruct MS0; unfold locBlocksTgt in SL; unfold restrict_sm in SL; destruct mu; simpl in *; assumption.
(* offset is representable *)
instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
(* size of target block is representable *)
intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
(* we have full permissions on sp' at and above dstk ctx *)
intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
eapply range_private_perms; eauto. xomega.
(* offset is aligned *)
replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
inv FB. apply min_alignment_sound; auto.
(* nobody maps to (sp, dstk ctx...) *)
intros. exploit (PRIV (ofs + delta')); eauto. xomega.
intros [A B]. apply (B b delta'); eauto.
assert (SL': locBlocksTgt mu sp' = true).
destruct MS0; unfold locBlocksTgt in SL; unfold restrict_sm in SL; destruct mu; simpl in *; assumption.
rewrite <- (as_inj_locBlocks mu b sp' delta') in SL'; auto.
autorewrite with restrict.
unfold restrict; unfold vis.
rewrite SL'.
rewrite orb_true_l; simpl; assumption.
replace (ofs + delta' - delta') with ofs by omega.
apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
intros [mu' [A [B [C D]]]].
exploit tr_moves_init_regs'; eauto. intros [rs'' [P [Q R]]].
eexists. eexists.
split; simpl. 
left.
eapply core_semantics_lemmas.corestep_plus_star_trans.
eapply core_semantics_lemmas.corestep_plus_one. 
eapply rtl_corestep_exec_Inop; eauto. 
eapply P.
(* assert (SEP: sm_inject_separated mu mu' m1 m2).
  admit. *)

exists mu'; intuition.

unfold MATCH; intuition.
constructor; eauto.
assert (SM_wd (restrict_sm mu (vis mu))).
apply restrict_sm_WD; auto.
assert (SM_wd (restrict_sm mu' (vis mu'))).
apply restrict_sm_WD; auto.
eapply (match_stacks_inside_alloc_left (restrict_sm mu (vis mu))); eauto.
eapply match_stacks_inside_invariant; eauto.
eapply restrict_sm_intern_incr; eauto.
eapply freshalloc_restricted_map; eauto.
Lemma injection_almost_equality_restrict: forall mu mu' m1 m2 m1' m2' stk f,
                                            Mem.alloc m1 0 (fn_stacksize f) = (m1', stk) ->
                                            intern_incr mu mu' ->
                                            sm_locally_allocated mu mu' m1 m2 m1' m2' ->
                                            (forall b : block, (b = stk -> False) -> 
                                                               as_inj mu' b = as_inj mu b) ->
                                            forall b1 : block,
                                              b1 <> stk ->
                                              as_inj (restrict_sm mu' (vis mu')) b1 =
                                              as_inj (restrict_sm mu (vis mu)) b1.

Lemma intern_incr_localloc_vis: forall mu mu' m1 m2 m1' m2',
                                  intern_incr mu mu' ->
                                  sm_locally_allocated mu mu' m1 m2 m1' m2' ->
                                  forall b, vis mu' b = vis mu b || freshloc m1 m1' b.
unfold sm_locally_allocated, intern_incr, vis.
intros; destruct mu, mu'; simpl in *.
repeat open_Hyp.
rewrite H0. rewrite H9.
repeat rewrite <- orb_assoc.
f_equal.
apply orb_comm.
Qed.
intros.
autorewrite with restrict.
unfold restrict.
erewrite intern_incr_localloc_vis; eauto.
erewrite (freshloc_alloc _ _ _ _ stk H).
destruct (eq_block b1 stk).
simpl. apply H3 in e; inversion e.
simpl; rewrite orb_false_r. rewrite H2; eauto.
Qed.
eapply injection_almost_equality_restrict; eauto.

omega.

apply agree_regs_incr with (as_inj (restrict_sm mu (vis mu))); auto.
apply intern_incr_as_inj; try apply restrict_sm_intern_incr; eauto.
apply restrict_sm_WD; auto.
eapply freshalloc_restricted_map; eauto.
autorewrite with restrict. 
eapply inject_restrict; eauto.
rewrite H3. eapply range_private_alloc_left; eauto.
eapply freshalloc_restricted_map; eauto.


eapply injection_almost_equality_restrict; eauto.

eapply meminj_preserves_incr_sep; eauto.
apply intern_incr_as_inj; eauto.
eapply sm_inject_separated_mem; eauto.

exploit (intern_incr_meminj_preserves_globals ge); eauto; try split; eauto.
eapply match_genv_meminj_preserves_extern_iff_all; eauto.
intros D; destruct D as [? isGlobal_frgn]; auto.

 { (* nonobservable external call *)
      rename MINJ into MINJR.
      destruct H as [RC [PG [Glob [SMV [WD MINJ]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      rewrite restrict_sm_all in *.
      simpl in FD. inv FD. 
      specialize (BuiltinEffects.EFhelpers _ _ OBS); intros.
      exploit (BuiltinEffects.inlineable_extern_inject _ _ GDE_lemma);
        try eapply H0; try eassumption.
        apply symbols_preserved. 
      intros [mu' [vres' [tm' [EC [RESINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
      eexists; eexists. 
      split. left. 
             eapply core_semantics_lemmas.corestep_plus_one. 
             eapply rtl_corestep_exec_function_external; eauto.
      exists mu'. intuition.
      assert (ISEP: inject_separated (restrict (as_inj mu) (vis mu))
                    (restrict (as_inj mu') (vis mu')) m1 m2).
                red. intros ??? RAI RAI'.
                destruct (restrictD_Some _ _ _ _ _ RAI')
                  as [AI' VIS']; clear RAI'.
                destruct (restrictD_None' _ _ _ RAI) 
                    as [AI | [bb2 [dd [AI VIS]]]]; clear RAI.
                  apply sm_inject_separated_mem in SEPARATED.
                  apply (SEPARATED _ _ _ AI AI'). trivial. 
                rewrite (intern_incr_vis_inv _ _ WD WD' 
                    INCR _ _ _ AI VIS') in VIS; discriminate.
      split. 
      {  econstructor; try solve[rewrite restrict_sm_all; eassumption].
        { (*eapply match_stacks_inside_set_reg.
            apply restrict_sm_WD; trivial.  *)
           eapply match_stacks_bound.
             eapply match_stacks_extcall. 10: eapply MS0.
              apply restrict_sm_WD; trivial.  
              apply restrict_sm_WD; trivial.  
              intros; eapply external_call_max_perm; eauto. 
              intros; eapply external_call_max_perm; eauto.
              rewrite restrict_sm_all. apply OUTOFREACH.
              rewrite restrict_sm_all. apply MINJR.
              apply restrict_sm_intern_incr; trivial. 
              repeat rewrite restrict_sm_all; trivial.
              clear - SMV. destruct SMV.
                split; intros.
                 rewrite restrict_sm_DOM in H1. apply (H _ H1).
                 rewrite restrict_sm_RNG in H1. apply (H0 _ H1). 
              xomega.
           eapply forward_nextblock. 
             eapply external_call_mem_forward; eassumption. }
        rewrite restrict_sm_all. apply inject_restrict; assumption.
      }
      intuition.
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. apply Glob; assumption. }

(* return fron noninlined function *)
inv MS0.
(* normal case *)
eexists. eexists.
split; simpl.
left.
eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_return.

exists mu. intuition.
apply sm_inject_separated_same_sminj.
loc_alloc_solve.

unfold MATCH; intuition.
econstructor; eauto. 
apply match_stacks_inside_set_reg; auto. 
apply restrict_sm_WD; auto.
apply agree_set_reg; auto.

(* untailcall case *)
inv MS; try congruence.
rewrite RET in RET0; inv RET0.
(*
  assert (rpc = pc). unfold spc in H0; unfold node in *; xomega.
  assert (res0 = res). unfold sreg in H1; unfold reg in *; xomega.
  subst rpc res0.
 *)
eexists. eexists.     
split; simpl.
left.
eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_return.
exists mu. intuition.
apply sm_inject_separated_same_sminj.
loc_alloc_solve.

Print MATCH.

unfold MATCH. intuition.
eapply match_regular_states; eauto. 
eapply match_stacks_inside_set_reg; eauto.
apply restrict_sm_WD; auto.
apply agree_set_reg; auto.

(*This should be a lemma*)
Lemma local_of_restrict_vis: forall mu sp sp' delta,  
                               SM_wd mu -> 
                               local_of (restrict_sm mu (vis mu)) sp = Some (sp', delta) -> 
                               as_inj (restrict_sm mu (vis mu)) sp = Some (sp', delta).
  intros mu sp sp' delta SMWD SP.
  autorewrite with restrict.
  unfold restrict.
  rewrite restrict_sm_local in SP; auto.
  unfold restrict in SP.
  destruct (vis mu sp) eqn:vismusp; simpl in SP; try solve [inv SP].
  unfold as_inj, join.
  rewrite SP.
  destruct (extern_of mu sp) eqn:extofmusp; simpl; auto. destruct p.
  apply SMWD in extofmusp; apply SMWD in SP.
  repeat open_Hyp.
  destruct SMWD; specialize (disjoint_extern_local_Src sp);
  destruct disjoint_extern_local_Src. 
  rewrite H3 in H1; inv H1.
  rewrite H3 in H; inv H.
Qed.
(*End lemma *)

apply local_of_restrict_vis; auto.

red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.

(* return from inlined function *)
inv MS0; try congruence. rewrite RET0 in RET; inv RET. 
unfold inline_return in AT. 
assert (PRIV': range_private (as_inj mu) m1' m2 sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
assert (restrict_bridge: range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx' + mstk ctx') (fn_stacksize f')).
red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega.
red; intros.
red in restrict_bridge.
apply restrict_bridge in H0.

(*This should be a lemma*)
unfold loc_private in *.
repeat open_Hyp.
split.
auto.
intros.
apply H1.
assert (SL': locBlocksTgt mu sp' = true).
erewrite <- restrict_sm_locBlocksTgt. apply SL.
autorewrite with restrict; unfold restrict; unfold vis.
erewrite <- (as_inj_locBlocks) in SL'; eauto.
erewrite SL'; rewrite orb_true_l; eauto.

(* with a result *)
destruct or.
eexists. eexists.
split; simpl.
left. 
eapply core_semantics_lemmas.corestep_plus_one.
eapply rtl_corestep_exec_Iop; eauto. simpl. reflexivity.

exists mu. intuition.
apply sm_inject_separated_same_sminj.
loc_alloc_solve.

unfold MATCH; intuition.
econstructor; eauto. apply match_stacks_inside_set_reg; auto. 
apply restrict_sm_WD; auto.
apply agree_set_reg; auto.
(* without a result *)
apply local_of_restrict_vis; auto.
red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.

eexists. eexists.
split; simpl. left.  
eapply core_semantics_lemmas.corestep_plus_one. eapply rtl_corestep_exec_Inop; eauto.
exists mu. intuition.
apply sm_inject_separated_same_sminj.
apply sm_locally_allocatedChar.
repeat split; extensionality b0;
rewrite freshloc_irrefl;
intuition.
unfold MATCH; intuition.
econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
apply local_of_restrict_vis; auto.

red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.
Qed.

intros.
exploit step_simulation_noeffect; eauto.
Hint Resolve step_simulation_noeffect: trans_correct.
eauto with trans_correct.

Lemma Empty_Effect_implication: forall mu m1 (b0 : block) (ofs : Z),
   EmptyEffect b0 ofs = true ->
   visTgt mu b0 = true /\
   (locBlocksTgt mu b0 = false ->
    exists (b1 : block) (delta1 : Z),
      foreign_of mu b1 = Some (b0, delta1) /\
      EmptyEffect b1 (ofs - delta1) = true /\
      Mem.perm m1 b1 (ofs - delta1) Max Nonempty).
    intros mu m1 b ofs empt;
    unfold EmptyEffect in empt; inv empt.
Qed.

Lemma step_simulation_effect: forall (st1 : RTL_core) (m1 : mem) (st1' : RTL_core) 
     (m1' : mem) (U1 : block -> Z -> bool)
   (ES: effstep (rtl_eff_sem hf) ge U1 st1 m1 st1' m1'),
   forall (st2 : RTL_core) (mu : SM_Injection) (m2 : mem)
   (U2vis: forall (b : block) (ofs : Z), U1 b ofs = true -> vis mu b = true)
   (MC: MATCH st1 mu st1 m1 st2 m2),
   exists (st2' : RTL_core) (m2' : mem),
     (exists U2 : block -> Z -> bool,
        (effstep_plus (rtl_eff_sem hf) tge U2 st2 m2 st2' m2' \/
         (RTL_measure st1' < RTL_measure st1)%nat /\
         effstep_star (rtl_eff_sem hf) tge U2 st2 m2 st2' m2') /\
        (forall (b : block) (ofs : Z),
         U2 b ofs = true ->
         visTgt mu b = true /\
         (locBlocksTgt mu b = false ->
          exists (b1 : block) (delta1 : Z),
            foreign_of mu b1 = Some (b, delta1) /\
            U1 b1 (ofs - delta1) = true /\
            Mem.perm m1 b1 (ofs - delta1) Max Nonempty))) /\
exists (mu' : SM_Injection),
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m1 m2 /\
     sm_locally_allocated mu mu' m1 m2 m1' m2' /\
     MATCH st1' mu' st1' m1' st2' m2'.

  intros.
    simpl in *.
    destruct MC as [MS H].
    
    inv ES;
      inv MS.
    (* Inop *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    eexists. eexists. split.
    eexists. split.

    left; simpl.
    eapply effstep_plus_one; simpl.
    eapply rtl_effstep_exec_Inop. eassumption.
    
    apply Empty_Effect_implication.

    exists mu.
    intuition.
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH.
    intuition.
    eapply match_regular_states; first [eassumption| split; eassumption].

    (* Iop *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    repeat open_Hyp.
    exploit eval_operation_inject. 

    eapply match_stacks_inside_globals; eauto.
    exact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact MINJ. eauto.
    fold (sop ctx op). intros [v' [A B]].
    eexists. eexists.
    split; simpl.
    eexists. split.
    
    left; simpl.
    eapply effstep_plus_one; simpl.

    eapply rtl_effstep_exec_Iop. eassumption.
    erewrite eval_operation_preserved; eauto.
    exact symbols_preserved. 

    apply Empty_Effect_implication.

    econstructor; eauto. 
    split; auto.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH.
    intuition.
    eapply match_regular_states; eauto.
    apply match_stacks_inside_set_reg; auto.
    eapply restrict_sm_WD; auto.
    apply agree_set_reg; auto. 

    (* Iload *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    exploit eval_addressing_inject. 
    eapply match_stacks_inside_globals; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
    fold (saddr ctx addr). intros [a' [P Q]].
    exploit Mem.loadv_inject; eauto. intros [v' [U V]].
    assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.
    eexists. eexists.
    split; simpl. 
    eexists. split.

    left; simpl.
    eapply effstep_plus_one. 
    eapply rtl_effstep_exec_Iload; try eassumption.

    apply Empty_Effect_implication.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    unfold MATCH;
      intuition.
    eapply match_regular_states; eauto.
    apply match_stacks_inside_set_reg; auto.
    eapply restrict_sm_WD; auto.
    apply agree_set_reg; auto.
    
    (* Istore *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    
    destruct H as [RC [PG [GF [SMV [WD INJ]]]]].
    exploit eval_addressing_inject.
    eapply match_stacks_inside_globals. 
    eassumption.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
    fold saddr. intros [a' [P Q]].
    Check Mem.storev_mapped_inject. 
    exploit Mem.storev_mapped_inject. 
    eexact INJ.
    eassumption.
    eapply val_inject_incr; try eapply Q.
    autorewrite with restrict.
    apply restrict_incr.
    eapply agree_val_reg; eauto.
    eapply agree_regs_incr.
    eassumption.
    autorewrite with restrict.
    apply restrict_incr.
    
    intros [m2' [U V]].
    assert (eval_addressing tge (Vptr sp' Int.zero) (saddr ctx addr) rs' ## (sregs ctx args) = Some a').
    rewrite <- P. apply eval_addressing_preserved. exact symbols_preserved.

    eexists. eexists. split.
    eexists. split.

    left; simpl.
    eapply effstep_plus_one. eapply rtl_effstep_exec_Istore; eauto.
    
    (*Here is the effect: store*)
    destruct a; inv H2.
    rewrite restrict_sm_all in Q. inv Q.
    intuition.
    apply StoreEffectD in H6. destruct H6 as [z [HI Ibounds]].
            apply eq_sym in HI. inv HI.
            eapply visPropagateR; eassumption.
    eapply StoreEffect_PropagateLeft; try eassumption.
     econstructor. eassumption. trivial.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    destruct a; simpl in H1; try discriminate.
    destruct a'; simpl in U; try discriminate.
    assert (RC1': REACH_closed m1' (vis mu)).
    eapply REACH_Store;
    try eassumption.
    inv Q.
    autorewrite with restrict in H8.
    eapply restrictD_Some.
    eapply H8.
    intros.
    rewrite getBlocks_char in H5.
    destruct H5. 
    destruct H5.
    Check agree_val_reg.
    assert (val_inject (as_inj (restrict_sm mu (vis mu))) rs # src rs' # (sreg ctx src)).
    eapply agree_val_reg; eauto.
    rewrite H5 in H6.
    inv H6.
    autorewrite with restrict in H10.
    eapply restrictD_Some.
    eassumption.
    simpl in H5.
    contradiction.

    unfold MATCH;
      intuition.
    (*match_states*)
    econstructor; eauto.
    eapply match_stacks_inside_store; eauto.
    apply restrict_sm_WD; auto.
    autorewrite with restrict; eapply inject_restrict; try eassumption.
    
    eapply Mem.store_valid_block_1; eauto.
    eapply range_private_invariant; eauto.
    intros; split; auto. eapply Mem.perm_store_2; eauto.
    intros; eapply Mem.perm_store_1; eauto.
    intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.
    inv H2.

    (* sm_valid mu m1' m2' *)
    split; intros. 
    eapply Mem.store_valid_block_1; try eassumption.
    eapply SMV; assumption.
    eapply Mem.store_valid_block_1; try eassumption.
    eapply SMV; assumption.
    
    (* Icall *)
    exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
    exploit find_function_agree; eauto.
    intros [fd' [A B]].
    exploit tr_funbody_inv; eauto. intros TR. inv TR.

    (* not inlined *)
    eexists. eexists. split.
    eexists. split.

    left; simpl.
    eapply effstep_plus_one. eapply rtl_effstep_exec_Icall; eauto.
    eapply sig_function_translated; eauto.

    apply Empty_Effect_implication.
    
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    split.
    econstructor; eauto.
    eapply match_stacks_cons; eauto.
    destruct MS0; assumption.
    eapply agree_val_regs; eauto.   
    intuition.

    (* inlined *)
    assert (fd = Internal f0).
    simpl in H1. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat SrcProg). 
    try eassumption. eauto. intros. 
    unfold ge in H1. congruence.
    subst fd.
    
    eexists. eexists. split.
    eexists. split.
    right; split; simpl. 
    omega.
    eapply effstep_star_zero.
    intuition.
    
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
      intuition.
    Focus 1.
    eapply match_call_regular_states; eauto. (* match_call_regular_states*)
    assert (SL: locBlocksTgt (restrict_sm mu (vis mu)) sp' = true) by (destruct MS0; assumption).
    eapply match_stacks_inside_inlined; eauto.
    
    apply local_of_loc_inj; auto;
     try (apply restrict_sm_WD); auto.
    
    red; intros. apply PRIV. inv H14. destruct H17.
    xomega.
    apply agree_val_regs_gen; auto.
    red; intros; apply PRIV. destruct H17. omega.

    (* Itailcall *)
    exploit match_stacks_inside_globalenvs; eauto. intros [bound G].
    exploit find_function_agree; eauto. intros [fd' [A B]].
    assert (PRIV': range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    eapply range_private_free_left; eauto. 
    inv FB. rewrite <- H5. auto.
    exploit tr_funbody_inv; eauto.
    intros TR. 
    inv TR.

    (* within the original function *)
    inv MS0; try congruence.

    assert (X: { m1' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto. xomega.
    destruct X as [m2' FREE].
    
    eexists. eexists. split.
    eexists. split.
    left; simpl.
    eapply effstep_plus_one. eapply rtl_effstep_exec_Itailcall; eauto.
    eapply sig_function_translated; eauto.

    (*Here is the effect: tailcall*)
    rewrite restrict_sm_all in SP.
    destruct (restrictD_Some _ _ _ _ _ SP).
    intuition.
    apply FreeEffectD in H13.
           destruct H13; subst. 
           eapply visPropagate; try eassumption.
    eapply FreeEffect_PropagateLeft; try eassumption.
    eapply as_inj_retrict; autorewrite with restrict; rewrite <- DSTK; eassumption.

    Lemma FreeEffect_step: forall m lo hi hi' sp b ofs,
                             hi' <= hi ->
                             FreeEffect m lo hi' sp b ofs = true ->
                             FreeEffect m lo hi sp b ofs = true.
      unfold FreeEffect.
      intros.
      destruct (valid_block_dec m b); try discriminate.
      destruct (eq_block b sp); simpl in *; try discriminate.
      destruct (zle lo ofs); simpl in *; try discriminate.
      Locate "<=".
      unfold zlt.
      destruct (Z_lt_dec ofs hi); simpl; auto.
      destruct (zlt ofs hi'); simpl in *; try discriminate.
      contradiction n; omega.
    Qed.
    
    eapply FreeEffect_step; eauto.
    assert (fn_stacksize f <= fn_stacksize f').
    { unfold transf_fundef in B.
    destruct FB.
    Locate "|".
    rewrite H18 in H21.
    rewrite DSTK in H21.
    simpl in H21.
    destruct (Zmax.Zmax_spec (fn_stacksize f) 0) as [H22 | H22]; destruct H22 as [H22 H23].
    rewrite H23 in H21; auto.
    omega. }
    
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.
    
    assert (Mem.inject (as_inj mu) m1' m2').
    eapply Mem.free_right_inject. eapply Mem.free_left_inject. eapply H12.
    eassumption.
    eassumption.

    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
    eelim Q.
    autorewrite with restrict.
    eapply restrictI_Some.
    eapply H11.
    rewrite restrict_sm_locBlocksTgt in SL.
    erewrite <- (as_inj_locBlocks _ b1 sp') in SL; try eassumption.
    unfold vis.
    rewrite SL.
    eapply orb_true_l.
    replace (ofs + delta - delta) with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

    unfold MATCH.
    intuition.
    econstructor; eauto.
    eapply match_stacks_bound with (bound := sp'). 
    eapply match_stacks_invariant; eauto.
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.nextblock_free; eauto. red in VB; xomega.
    eapply agree_val_regs; eauto.
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
    eelim Q; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    eapply REACH_closed_free; eauto.
    (* sm_valid mu m1' m2' *)
    split; intros. 
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H7; assumption.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H7; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)(* Got it for free*)
    (* eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.*)
    (* show that no valid location points into the stack block being freed *)
    (*The following isnot needed*)
    (*intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [P Q]. 
    eelim Q.
    assert (HH: vis mu b1 = true).
    a d m i t.
    instantiate (2:= b1).
    autorewrite with restrict. 
    unfold restrict. erewrite HH; simpl; eauto.
    replace (ofs + delta - delta) with (ofs) by omega. 
(*    replace (ofs + delta - dstk ctx) with ofs by omega. *)
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.*)

    (* turned into a call *)
    eexists. eexists. split.
    eexists. split.
    left; simpl. 
    eapply effstep_plus_one. eapply rtl_effstep_exec_Icall; eauto.
    eapply sig_function_translated; eauto.

    intros b ofs empt;
    unfold EmptyEffect in empt; inv empt.
    
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    econstructor; eauto.
    eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_invariant; eauto. 
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto.
    destruct MS0; assumption.
   
    eapply agree_val_regs; eauto.
    eapply Mem.free_left_inject; eauto.
    eapply REACH_closed_free; eauto.
    
    (*  sm_valid mu m1' m2 *)
    split; intros. 
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H7; assumption.
    eapply H7; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)
    eapply Mem.free_left_inject; eauto.

   (* inlined *)
    assert (fd = Internal f0).
    simpl in H1. destruct (Genv.find_symbol ge id) as [b|] eqn:?; try discriminate.
    exploit (funenv_program_compat SrcProg); eauto. intros. 
    unfold ge in H1. congruence.
    subst fd.
    eexists. eexists. split.
    eexists. split.
    right; split. simpl; omega. 
    eapply effstep_star_zero.
    intuition.

    exists mu.
    intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
      intuition.
    econstructor; eauto.
    eapply match_stacks_inside_inlined_tailcall; eauto.
    eapply match_stacks_inside_invariant; eauto.
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto.
    apply agree_val_regs_gen; auto.
    eapply Mem.free_left_inject; eauto.
    red; intros; apply PRIV'. 
    assert (dstk ctx <= dstk ctx'). red in H15; rewrite H15. apply align_le. apply min_alignment_pos.
    omega.
    eapply REACH_closed_free; eauto.
    (* sm_valid mu m1' m2 *)
    split; intros.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H11; assumption.
    eapply H11; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)
    eapply Mem.free_left_inject; eauto.

    { (* builtin*)
      exploit tr_funbody_inv; eauto. intros TR; inv TR.
      rename MINJ into MINJR.
      destruct H as [RC [PG [Glob [SMV [WD MINJ]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      rewrite restrict_sm_all in *.
      assert (ArgsInj:= agree_val_regs _ _ _ _ args AG).
      exploit (BuiltinEffects.inlineable_extern_inject _ _ GDE_lemma);
        try eapply H1; try eassumption.
        apply symbols_preserved. 
      intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
      exists (RTL_State stk' f' (Vptr sp' Int.zero) (spc ctx pc')
               (rs'#(sreg ctx res) <- vres')), tm'.
      split. eexists.
        split. left. apply effstep_plus_one. 
                eapply rtl_effstep_exec_Ibuiltin; eauto. 
        intros. eapply BuiltinEffects.BuiltinEffect_Propagate; eassumption.
      exists mu'. intuition.
      assert (ISEP: inject_separated (restrict (as_inj mu) (vis mu))
                    (restrict (as_inj mu') (vis mu')) m1 m2).
                red. intros ??? RAI RAI'.
                destruct (restrictD_Some _ _ _ _ _ RAI')
                  as [AI' VIS']; clear RAI'.
                destruct (restrictD_None' _ _ _ RAI) 
                    as [AI | [bb2 [dd [AI VIS]]]]; clear RAI.
                  apply sm_inject_separated_mem in SEPARATED.
                  apply (SEPARATED _ _ _ AI AI'). trivial. 
                rewrite (intern_incr_vis_inv _ _ WD WD' 
                    INCR _ _ _ AI VIS') in VIS; discriminate.
      split. 
      {  econstructor; eauto.
        { eapply match_stacks_inside_set_reg.
            apply restrict_sm_WD; trivial.  
            eapply match_stacks_inside_extcall; try eapply MS0.
              apply restrict_sm_WD; trivial.  
              apply restrict_sm_WD; trivial.  
              intros; eapply external_call_max_perm; eauto. 
              intros; eapply external_call_max_perm; eauto.
              rewrite restrict_sm_all. apply OUTOFREACH.
              rewrite restrict_sm_all. apply MINJR.
              apply restrict_sm_intern_incr; trivial. 
              repeat rewrite restrict_sm_all; trivial.
              clear - SMV. destruct SMV.
                split; intros.
                 rewrite restrict_sm_DOM in H1. apply (H _ H1).
                 rewrite restrict_sm_RNG in H1. apply (H0 _ H1). 
              apply VB. }
        rewrite restrict_sm_all. apply agree_set_reg; eauto.  
          eapply agree_regs_incr; eauto. 
          apply (intern_incr_restrict _ _ WD' INCR).
        rewrite restrict_sm_all. 
          apply (intern_incr_restrict _ _ WD' INCR). assumption.
        rewrite restrict_sm_all. apply inject_restrict; assumption.
        eapply external_call_mem_forward; try eassumption.
        { rewrite restrict_sm_all.
          eapply range_private_extcall; try eassumption.
            intros. eapply external_call_mem_forward; eauto. 
            apply (intern_incr_restrict _ _ WD' INCR). }
        intros. apply SSZ2. eapply external_call_max_perm; eauto. 
      }
      intuition.
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. apply Glob; assumption. }

    (* Icond *)

    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    assert (eval_condition cond rs'##(sregs ctx args) m2 = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto. 
    
    eexists. eexists. split; simpl.
    eexists. split.
    left; simpl.
    eapply effstep_plus_one.
    eapply rtl_effstep_exec_Icond; eauto.

    apply Empty_Effect_implication.

    exists mu. intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    destruct b;
      econstructor; eauto.


    (* jumptable *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.
    assert (H3: val_inject (as_inj (restrict_sm mu (vis mu))) rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
    rewrite H1 in H3; inv H3.
    
    eexists. eexists. split; simpl.
    eexists. split.
    left.
    eapply effstep_plus_one. eapply rtl_effstep_exec_Ijumptable; eauto.
    rewrite list_nth_z_map. rewrite H2. simpl; reflexivity. 
    
    apply Empty_Effect_implication.
    
    exists mu. intuition.
    (*apply intern_incr_refl.*)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH.
    intuition.
    econstructor; eauto.


    (* return *)
    exploit tr_funbody_inv; eauto. intros TR; inv TR.

    (* not inlined *)
    inv MS0; try congruence.
    assert (X: { m1' | Mem.free m2 sp' 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)). 
    replace ofs with (ofs + dstk ctx) by omega. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. omega.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); omega.
    destruct X as [m2' FREE].
    
    eexists. eexists. split.
    eexists. split; simpl.
    left.
    eapply effstep_plus_one. eapply rtl_effstep_exec_Ireturn; eauto. 

    (*Here is the effect: return*)
    rewrite restrict_sm_all in SP.
    destruct (restrictD_Some _ _ _ _ _ SP).
    intuition. 
    apply FreeEffectD in H12.
           destruct H12; subst. 
           eapply visPropagate; try eassumption.
    eapply FreeEffect_PropagateLeft; try eassumption.
    eapply as_inj_retrict; autorewrite with restrict; rewrite <- DSTK; eassumption.
    admit.

    exists mu.
    intuition.
    (* apply intern_incr_refl. *)
    apply sm_inject_separated_same_sminj.
    loc_alloc_solve.

    unfold MATCH;
      intuition.
    econstructor; eauto.
    eapply match_stacks_bound with (bound := sp'). 
    eapply match_stacks_invariant; eauto.
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto. 
    intros. eapply Mem.perm_free_1; eauto. 
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.nextblock_free; eauto. red in VB; xomega.
    destruct or; simpl. apply agree_val_reg; auto. auto.

    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H16 in PRIV. eapply range_private_free_left; eauto. 
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
    eelim B; eauto. replace (ofs + delta - delta) with ofs by omega. 
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.

    eapply REACH_closed_free; eauto.

    (*  sm_valid mu m1' m2 *)
    split; intros.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H8; assumption.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H8; assumption.
    (*  Mem.inject (as_inj mu) m1' m2' *)
    eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    (* show that no valid location points into the stack block being freed *)
    intros. inversion FB; subst.
    assert (PRIV': range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx) f'.(fn_stacksize)).
    rewrite H16 in PRIV. eapply range_private_free_left; eauto. 
    rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). omega. intros [A B]. 
    eelim B. 
    autorewrite with restrict.
    eapply restrictI_Some.
    apply H10.
    rewrite restrict_sm_locBlocksTgt in SL.
    erewrite <- (as_inj_locBlocks _ b1 sp') in SL; try eassumption.
    unfold vis.
    rewrite SL.
    eapply orb_true_l.
    replace (ofs + delta - delta) with ofs by omega.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    
    (* inlined *)
    eexists. eexists. split; simpl.
    eexists. split.
    right; split; simpl. omega.
    
    eapply effstep_star_zero.
    intuition.
    
    exists mu.
    intuition.
    (*apply intern_incr_refl.*)

    apply sm_inject_separated_same_sminj.
    loc_alloc_solve. 
    
    unfold MATCH;
      intuition.
    econstructor; eauto.
    
    
    eapply match_stacks_inside_invariant; eauto. 
    apply restrict_sm_WD; auto.
    intros. eapply Mem.perm_free_3; eauto.
    destruct or; simpl. apply agree_val_reg; auto. auto.
    eapply Mem.free_left_inject; eauto.
    inv FB. subst.  rewrite H13 in PRIV. eapply range_private_free_left; eauto.
    
    eapply REACH_closed_free; eauto.
    (*sm_valid*)
    split; intros.
    eapply Mem.valid_block_free_1; try eassumption.
    eapply H8; assumption.
    eapply H8; assumption.
    (*  Mem.inject (as_inj mu) m1' m2 *)
    eapply Mem.free_left_inject; eauto.




    (* internal function, not inlined *)
    assert (A: exists f', tr_function fenv f f' /\ fd' = Internal f'). 
    Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. 
    destruct A as [f' [TR EQ]]. inversion TR; subst.
    repeat open_Hyp.
    exploit alloc_parallel_intern; 
      eauto. apply Zle_refl. 
    instantiate (1 := fn_stacksize f'). inv H1. xomega.
    intros [mu' [m2' [sp' [A [B [C [D E]]]]]]].
    
    eexists. eexists. split; simpl.
    eexists.
    split; simpl.
    left.
    eapply effstep_plus_one. eapply rtl_effstep_exec_function_internal; eauto.

    apply Empty_Effect_implication.
    
    rewrite H5.
    exists mu'. 
    intuition.

    unfold MATCH; intuition.
    rewrite H6.
    rewrite <- H5.
    
    eapply match_regular_states; eauto.
    assert (SP: sp' = Mem.nextblock m2) by (eapply Mem.alloc_result; eauto).
    apply match_stacks_inside_base.
    rewrite <- SP in MS0. 
    eapply (match_stacks_invariant (restrict_sm mu (vis mu))); eauto.
    eapply restrict_sm_intern_incr; auto.
    eapply restrict_sm_WD; auto.
    
    intros. 
    destruct (eq_block b1 stk). 
    subst b1.
    apply as_inj_retrict  in H20; rewrite D in H20; inv H20. subst b2. eelim Plt_strict; eauto.
    rewrite <- H20.
    autorewrite with restrict.
    unfold restrict.
    rewrite H14; auto.
    assert (vis mu' b1 = true ).
    destruct (vis mu' b1) eqn:vismu'b1; auto.
    autorewrite with restrict in H20.
    unfold restrict in H20.
    rewrite vismu'b1 in H20; inv H20.
    erewrite (intern_incr_vis_inv mu mu'); auto.
    rewrite H22; auto.
    rewrite <- H14; auto.
    apply as_inj_retrict in H20; eassumption.
    
    intros. exploit Mem.perm_alloc_inv. eexact H0. eauto. 
    destruct (eq_block b1 stk); intros; auto. 
    subst b1. apply as_inj_retrict in H20.
    rewrite D in H20; inv H20. subst b2. eelim Plt_strict; eauto.  

    intros. eapply Mem.perm_alloc_1; eauto. 
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto. 
    rewrite dec_eq_false; auto.

    eapply alloc_local_restrict; eauto.

    auto. auto. auto.
    rewrite H5. apply agree_regs_init_regs.
    Check val_list_inject_incr.
    eapply val_list_inject_incr.
    autorewrite with restrict.
    eapply intern_incr_restrict; try (apply C); auto.
    autorewrite with restrict in VINJ; auto.
    inv H1; auto. 
    
    eapply  freshalloc_restricted_map; eauto.
    rewrite H2; auto.
    
    autorewrite with restrict.
    apply inject_restrict; auto.

    eapply Mem.valid_new_block; eauto.
    red; intros. split.
    eapply Mem.perm_alloc_2; eauto. inv H1; xomega.
    intros; red; intros. exploit Mem.perm_alloc_inv. eexact H0. eauto.
    destruct (eq_block b stk); intros; apply as_inj_retrict in H21. 
    subst. 
    rewrite D in H21; inv H21. inv H1; xomega.
    rewrite H14 in H21; auto. eelim Mem.fresh_block_alloc. eexact A.
    eapply Mem.mi_mappedblocks.
    apply H13.
    apply H21.


    intros.
    exploit Mem.perm_alloc_3; eauto.
    xomega.

    apply (meminj_preserves_incr_sep ge (as_inj mu) H9 m1 m2); eauto.
    apply intern_incr_as_inj; auto.
    apply sm_inject_separated_mem; auto.

    eapply intern_incr_meminj_preserves_globals_as_inj in H17.
    destruct H17 as [H00 H01]; apply H01; auto.
    eexact H20.
    exact H12.
    split; eauto.
    assumption.


(* internal function, inlined *)
inversion FB; subst.
repeat open_Hyp.
exploit alloc_left_mapped_sm_inject; try eassumption.
(* sp' is local *)
destruct MS0; unfold locBlocksTgt in SL; unfold restrict_sm in SL; destruct mu; simpl in *; assumption.
(* offset is representable *)
instantiate (1 := dstk ctx). generalize (Zmax2 (fn_stacksize f) 0). omega.
(* size of target block is representable *)
intros. right. exploit SSZ2; eauto with mem. inv FB; omega.
(* we have full permissions on sp' at and above dstk ctx *)
intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
eapply range_private_perms; eauto. xomega.
(* offset is aligned *)
replace (fn_stacksize f - 0) with (fn_stacksize f) by omega.
inv FB. apply min_alignment_sound; auto.
(* nobody maps to (sp, dstk ctx...) *)
intros. exploit (PRIV (ofs + delta')); eauto. xomega.
intros [A B]. apply (B b delta'); eauto.
assert (SL': locBlocksTgt mu sp' = true).
destruct MS0; unfold locBlocksTgt in SL; unfold restrict_sm in SL; destruct mu; simpl in *; assumption.
rewrite <- (as_inj_locBlocks mu b sp' delta') in SL'; auto.
autorewrite with restrict.
unfold restrict; unfold vis.
rewrite SL'.
rewrite orb_true_l; simpl; assumption.
replace (ofs + delta' - delta') with ofs by omega.
apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
intros [mu' [A [B [C D]]]].
exploit tr_moves_init_regs_eff; eauto. intros [rs'' [P [Q R]]].

eexists. eexists. split; simpl.
eexists. split; simpl. 
left.

eapply effstep_plus_star_trans.
eapply effstep_plus_one. 
eapply rtl_effstep_exec_Inop; eauto. 
eapply P.

apply Empty_Effect_implication.

assert (SEP: sm_inject_separated mu mu' m1 m2).
  admit.

exists mu'; intuition.

unfold MATCH; intuition.
constructor; eauto.
assert (SM_wd (restrict_sm mu (vis mu))).
apply restrict_sm_WD; auto.
assert (SM_wd (restrict_sm mu' (vis mu'))).
apply restrict_sm_WD; auto.
eapply (match_stacks_inside_alloc_left (restrict_sm mu (vis mu))); eauto.
eapply match_stacks_inside_invariant; eauto.
eapply restrict_sm_intern_incr; eauto.
eapply freshalloc_restricted_map; eauto.
eapply injection_almost_equality_restrict; eauto.

omega.

apply agree_regs_incr with (as_inj (restrict_sm mu (vis mu))); auto.
apply intern_incr_as_inj; try apply restrict_sm_intern_incr; eauto.
apply restrict_sm_WD; auto.
eapply freshalloc_restricted_map; eauto.
autorewrite with restrict. 
eapply inject_restrict; eauto.
rewrite H3. eapply range_private_alloc_left; eauto.
eapply freshalloc_restricted_map; eauto.


eapply injection_almost_equality_restrict; eauto.

eapply meminj_preserves_incr_sep; eauto.
apply intern_incr_as_inj; eauto.
eapply sm_inject_separated_mem; eauto.

exploit (intern_incr_meminj_preserves_globals ge); eauto; try split; eauto.
eapply match_genv_meminj_preserves_extern_iff_all; eauto.
intros D; destruct D as [? isGlobal_frgn]; auto.

 { (* nonobservable external call *)
      rename MINJ into MINJR.
      destruct H as [RC [PG [Glob [SMV [WD MINJ]]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
      rewrite restrict_sm_all in *.
      simpl in FD. inv FD. 
      specialize (BuiltinEffects.EFhelpers _ _ OBS); intros.
      exploit (BuiltinEffects.inlineable_extern_inject _ _ GDE_lemma);
        try eapply H0; try eassumption.
        apply symbols_preserved. 
      intros [mu' [vres' [tm' [EC [RESINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
      eexists; eexists. 
      split. eexists.
        split. left. 
             eapply effstep_plus_one. 
             eapply rtl_effstep_exec_function_external; eauto.
        intros. eapply BuiltinEffects.BuiltinEffect_Propagate; eassumption.
      exists mu'. intuition.
      assert (ISEP: inject_separated (restrict (as_inj mu) (vis mu))
                    (restrict (as_inj mu') (vis mu')) m1 m2).
                red. intros ??? RAI RAI'.
                destruct (restrictD_Some _ _ _ _ _ RAI')
                  as [AI' VIS']; clear RAI'.
                destruct (restrictD_None' _ _ _ RAI) 
                    as [AI | [bb2 [dd [AI VIS]]]]; clear RAI.
                  apply sm_inject_separated_mem in SEPARATED.
                  apply (SEPARATED _ _ _ AI AI'). trivial. 
                rewrite (intern_incr_vis_inv _ _ WD WD' 
                    INCR _ _ _ AI VIS') in VIS; discriminate.
      split. 
      {  econstructor; try solve[rewrite restrict_sm_all; eassumption].
        { (*eapply match_stacks_inside_set_reg.
            apply restrict_sm_WD; trivial.  *)
           eapply match_stacks_bound.
             eapply match_stacks_extcall. 10: eapply MS0.
              apply restrict_sm_WD; trivial.  
              apply restrict_sm_WD; trivial.  
              intros; eapply external_call_max_perm; eauto. 
              intros; eapply external_call_max_perm; eauto.
              rewrite restrict_sm_all. apply OUTOFREACH.
              rewrite restrict_sm_all. apply MINJR.
              apply restrict_sm_intern_incr; trivial. 
              repeat rewrite restrict_sm_all; trivial.
              clear - SMV. destruct SMV.
                split; intros.
                 rewrite restrict_sm_DOM in H1. apply (H _ H1).
                 rewrite restrict_sm_RNG in H1. apply (H0 _ H1). 
              xomega.
           eapply forward_nextblock. 
             eapply external_call_mem_forward; eassumption. }
        rewrite restrict_sm_all. apply inject_restrict; assumption.
      }
      intuition.
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. apply Glob; assumption. }

(* return fron noninlined function *)
inv MS0.
(* normal case *)
eexists. eexists. split; simpl.
eexists. split; simpl.
left.
eapply effstep_plus_one. eapply rtl_effstep_exec_return.

apply Empty_Effect_implication.

exists mu. intuition.
apply sm_inject_separated_same_sminj.
loc_alloc_solve.

unfold MATCH; intuition.
econstructor; eauto. 
apply match_stacks_inside_set_reg; auto. 
apply restrict_sm_WD; auto.
apply agree_set_reg; auto.

(* untailcall case *)
inv MS; try congruence.
rewrite RET in RET0; inv RET0.
(*
  assert (rpc = pc). unfold spc in H0; unfold node in *; xomega.
  assert (res0 = res). unfold sreg in H1; unfold reg in *; xomega.
  subst rpc res0.
 *)
eexists. eexists. split; simpl.
eexists. split.
left.
eapply effstep_plus_one. eapply rtl_effstep_exec_return.

apply Empty_Effect_implication.

exists mu. intuition.
apply sm_inject_separated_same_sminj.
loc_alloc_solve.

Print MATCH.

unfold MATCH. intuition.
eapply match_regular_states; eauto. 
eapply match_stacks_inside_set_reg; eauto.
apply restrict_sm_WD; auto.
apply agree_set_reg; auto.

(*This should be a lemma*)

(*End lemma *)

apply local_of_restrict_vis; auto.

red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.

(* return from inlined function *)
inv MS0; try congruence. rewrite RET0 in RET; inv RET. 
unfold inline_return in AT. 
assert (PRIV': range_private (as_inj mu) m1' m2 sp' (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
assert (restrict_bridge: range_private (as_inj (restrict_sm mu (vis mu))) m1' m2 sp' (dstk ctx' + mstk ctx') (fn_stacksize f')).
red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. omega. apply PRIV. omega.
red; intros.
red in restrict_bridge.
apply restrict_bridge in H0.

(*This should be a lemma*)
unfold loc_private in *.
repeat open_Hyp.
split.
auto.
intros.
apply H1.
assert (SL': locBlocksTgt mu sp' = true).
erewrite <- restrict_sm_locBlocksTgt. apply SL.
autorewrite with restrict; unfold restrict; unfold vis.
erewrite <- (as_inj_locBlocks) in SL'; eauto.
erewrite SL'; rewrite orb_true_l; eauto.

(* with a result *)
destruct or.
eexists. eexists. split; simpl.
eexists. split; simpl.
left. 
eapply effstep_plus_one.
eapply rtl_effstep_exec_Iop; eauto. simpl. reflexivity.

apply Empty_Effect_implication.

exists mu. intuition.
apply sm_inject_separated_same_sminj.
loc_alloc_solve.

unfold MATCH; intuition.
econstructor; eauto. apply match_stacks_inside_set_reg; auto. 
apply restrict_sm_WD; auto.
apply agree_set_reg; auto.
(* without a result *)
apply local_of_restrict_vis; auto.
red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.

eexists. eexists. split; simpl.
eexists. split.
left.  
eapply effstep_plus_one. eapply rtl_effstep_exec_Inop; eauto.

apply Empty_Effect_implication.

exists mu. intuition.
apply sm_inject_separated_same_sminj.
apply sm_locally_allocatedChar.
repeat split; extensionality b0;
rewrite freshloc_irrefl;
intuition.
unfold MATCH; intuition.
econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
apply local_of_restrict_vis; auto.

red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; omega. apply PRIV; omega.

Qed.

Hint Resolve step_simulation_effect: trans_correct.
eauto with trans_correct.