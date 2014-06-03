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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib.
Require Export Axioms.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Op.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Registers.
Require Import RTL.
Require Import Conventions.
Require Import Tailcall.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.effect_semantics.
Require Import StructuredInjections.
Require Import reach.
Require Import effect_simulations.
Require Import sepcomp.effect_properties.
Require Import effect_simulations_lemmas.

Require Import RTL_coop.
Require Import BuiltinEffects.
Require Import RTL_eff.

Require Import RTL2RTL_proofEFF.
(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    omega.
    destruct (f!pc); try omega. 
    destruct i; try omega.
    generalize (IHn n0). omega.
    generalize (IHn n0). omega.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  omega.
  destruct n2. omegaContradiction. assert (n1 <= n2)%nat by omega.
  simpl. destruct f!pc; try omega. destruct i; try omega.
  generalize (IHn1 n2 n H0). omega.
  generalize (IHn1 n2 n H0). omega.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. omegaContradiction. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. omega.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. omega.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl. 
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto. 
  simpl. rewrite H2. omega. omega.

  intros op args dst s EQ1 EQ2. 
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro. 
  exploit is_move_operation_correct; eauto. intros [A B]. subst. 
  eapply is_return_move; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto. 
  simpl. rewrite EQ2. omega. omega.
 
  intros or EQ1 EQ2. destruct or; intros. 
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r. 
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  caseEq (is_return niter f n r && tailcall_is_possible s &&
          opt_typ_eq (sig_res s) (sig_res (fn_sig f))); intros.
  destruct (andb_prop _ _ H0). destruct (andb_prop _ _ H1).
  eapply transf_instr_tailcall; eauto.
  eapply is_return_charact; eauto. 
  constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0). destruct (eliminate_tailcalls tt).
  simpl. rewrite PTree.gmap. rewrite H. simpl. 
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto. 
  exists i; split. auto. constructor.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

(*Definition regset_lessdef (rs rs': regset) : Prop :=
  forall r, Val.lessdef (rs#r) (rs'#r).

Lemma regset_get_list:
  forall rs rs' l,
  regset_lessdef rs rs' -> Val.lessdef_list (rs##l) (rs'##l).
Proof.
  induction l; simpl; intros; constructor; auto.
Qed.

Lemma regset_set:
  forall rs rs' v v' r,
  regset_lessdef rs rs' -> Val.lessdef v v' ->
  regset_lessdef (rs#r <- v) (rs'#r <- v').
Proof.
  intros; red; intros. repeat rewrite PMap.gsspec. destruct (peq r0 r); auto. 
Qed.

Lemma regset_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regset_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply regset_set. auto. auto.
Qed.
*)

(** * Proof of semantic preservation *)

Section PRESERVATION.

Variable prog: program.
Let tprog := transf_program prog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf transf_fundef prog).

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof (Genv.find_var_info_transf transf_fundef prog).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (@Genv.find_funct_transf _ _ _ transf_fundef prog).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (@Genv.find_funct_ptr_transf _ _ _ transf_fundef prog).

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function. 
  destruct (zeq (fn_stacksize f) 0 && eliminate_tailcalls tt); auto. 
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

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros. 
  destruct (zeq (fn_stacksize f) 0 && eliminate_tailcalls tt); auto.
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

Lemma find_function_translated j:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regset_inject j rs rs' ->
  globalfunction_ptr_inject j ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (RR: rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD.
    rewrite EQ in *; clear EQ.
    rewrite Genv.find_funct_find_funct_ptr in H.
    apply H1 in H. destruct H. rewrite H in H5; inv H5.
    rewrite Int.add_zero. trivial.
  rewrite RR. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes mu: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes mu nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' sp' f,
      match_stackframes mu stk stk' ->
      regset_inject (restrict (as_inj mu) (vis mu)) rs rs' ->
      local_of mu sp = Some(sp',0) ->
      match_stackframes mu 
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp' Int.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes mu stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      (*maybe not needed? localBlocksSrc mu sp = true ->*)
      match_stackframes mu
        (Stackframe res f (Vptr sp Int.zero) pc rs :: stk)
        stk'.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states mu: RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f sp'
             (STACKS: match_stackframes mu s s')
             (RLD: regset_inject (restrict (as_inj mu) (vis mu)) rs rs')
             (MLD: Mem.inject (as_inj mu) m m') (*(MLD: Mem.extends m m')*)
             (*NEW*) (SPloc: local_of mu sp = Some(sp',0)),
      match_states mu (RTL_State s f (Vptr sp Int.zero) pc rs) m
                      (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc rs') m'
  | match_states_call:
      forall s f args m s' args' m',
      match_stackframes mu s s' ->
      val_list_inject (restrict (as_inj mu) (vis mu)) args args' -> (*Val.lessdef_list args args' ->*)
      Mem.inject (as_inj mu) m m' -> (*Mem.extends m m' ->*) 
      match_states mu (RTL_Callstate s f args) m
                      (RTL_Callstate s' (transf_fundef f) args') m'
  | match_states_return:
      forall s v m s' v' m',
      match_stackframes mu s s' ->
      val_inject (restrict (as_inj mu) (vis mu)) v v' -> (*Val.lessdef v v' ->*)
      Mem.inject (as_inj mu) m m' -> (*Mem.extends m m' ->*)
      match_states mu (RTL_Returnstate s v) m
                      (RTL_Returnstate s' v') m'
  | match_states_interm:
      forall s sp pc rs m s' m' f r v'
             (STACKS: match_stackframes mu s s')
             (MLD: Mem.inject (as_inj mu) m m'), (*(MLD: Mem.extends m m'),*)
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      val_inject (restrict (as_inj mu) (vis mu)) (rs#r) v' -> (*Val.lessdef (rs#r) v' ->*)
      match_states mu (RTL_State s f (Vptr sp Int.zero) pc rs) m
                      (RTL_Returnstate s' v') m'.

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: RTL_core) : nat :=
  match st with
  | RTL_State s f sp pc rs => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | RTL_Callstate s f args => 0%nat
  | RTL_Returnstate s v => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Definition MATCH (d:RTL_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\ 
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  globalfunction_ptr_inject (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu.

Lemma MATCH_wd: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), SM_wd mu.
Proof. intros. eapply MC. Qed.

Lemma MATCH_RC: forall d mu c1 m1 c2 m2 
  (MC: MATCH d mu c1 m1 c2 m2), REACH_closed m1 (vis mu).
Proof. intros. eapply MC. Qed.

Lemma match_stackframes_restrict mu s s' X: forall 
          (MS : match_stackframes mu s s')
          (HX : forall b : block, vis mu b = true -> X b = true)
          (WD : SM_wd mu),
      match_stackframes (restrict_sm mu X) s s'.
Proof. intros.
induction MS; econstructor; eauto.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
rewrite restrict_sm_local. 
  eapply restrictI_Some; trivial.
  apply HX. destruct (local_DomRng _ WD _ _ _ H0). 
  unfold vis. intuition.
Qed.

Lemma match_states_restrict mu c1 m1 c2 m2 X: forall 
          (MS : match_states mu c1 m1 c2 m2)
          (HX : forall b : block, vis mu b = true -> X b = true)
          (WD : SM_wd mu) (RC: REACH_closed m1 X),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
inv MS.
econstructor; eauto.
  eapply match_stackframes_restrict; eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
  rewrite restrict_sm_all.
    eapply inject_restrict; trivial.
  rewrite restrict_sm_local. 
    eapply restrictI_Some; trivial.
    apply HX. destruct (local_DomRng _ WD _ _ _ SPloc). 
    unfold vis. intuition.    
econstructor; eauto.
  eapply match_stackframes_restrict; eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
  rewrite restrict_sm_all.
    eapply inject_restrict; trivial.
econstructor; eauto.
  eapply match_stackframes_restrict; eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
  rewrite restrict_sm_all.
    eapply inject_restrict; trivial.
econstructor; eauto.
  eapply match_stackframes_restrict; eassumption.
  rewrite restrict_sm_all.
    eapply inject_restrict; trivial.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
Qed.

Lemma MATCH_restrict: forall d mu c1 m1 c2 m2 X
  (MC: MATCH d mu c1 m1 c2 m2)
  (HX: forall b : block, vis mu b = true -> X b = true) 
  (RX: REACH_closed m1 X), 
  MATCH d (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
  destruct MC as [MS [RC [PG [GF [Glob [SMV WD]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  eapply match_states_restrict; eassumption.
(*split. rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.*)
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
assumption.
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

Lemma match_stackframes_intern_incr mu s s': forall
        (MS: match_stackframes mu s s') mu'
        (INCR : intern_incr mu mu') (WD': SM_wd mu'),
        match_stackframes mu' s s'.
Proof. intros.
  induction MS; econstructor; eauto.
    eapply regset_incr; eauto. 
      apply intern_incr_restrict; trivial.
    eapply INCR; trivial.
Qed.

Lemma match_stackframes_replace_locals mu: forall s s'
      (MS : match_stackframes mu s s') pubS pubT,
  match_stackframes
  (replace_locals mu pubS pubT) s s'.
(*     (fun b : block => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b)
     (fun b : block => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
  s s'.*)
Proof.
  intros.
  induction MS; econstructor; eauto.
  rewrite replace_locals_as_inj, replace_locals_vis. assumption.
  rewrite replace_locals_local. trivial.
Qed.

Lemma MATCH_atExternal: forall (mu : SM_Injection) (c1 : RTL_core) (m1 : mem) (c2 : RTL_core)
  (m2 : mem) (e : external_function) (vals1 : list val) (ef_sig : signature),
MATCH c1 mu c1 m1 c2 m2 ->
at_external rtl_eff_sem c1 = Some (e, ef_sig, vals1) ->
Mem.inject (as_inj mu) m1 m2 /\
(exists vals2 : list val,
   Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
   at_external rtl_eff_sem c2 = Some (e, ef_sig, vals2) /\
   (forall pubSrc' pubTgt' : block -> bool,
    pubSrc' =
    (fun b : block => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
    pubTgt' =
    (fun b : block => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
    forall nu : SM_Injection,
    nu = replace_locals mu pubSrc' pubTgt' ->
    MATCH c1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2)).
Proof. intros.
 destruct H as [MC [RC [PG [GFP [Glob [SMV WDmu]]]]]].
 simpl in *. inv MC; simpl in *; inv H0.
 destruct f; inv H4.
 rename args' into vals2. rename H2 into MINJ.
 split; trivial.
 eexists.
    split. eapply val_list_inject_forall_inject. eassumption.
    simpl. split. reflexivity.
 intros.
assert (WDnu: SM_wd nu).
  subst.
  eapply replace_locals_wd; eauto.
    intros b Hb.
    apply andb_true_iff in Hb. destruct Hb.
    exploit (REACH_local_REACH _ WDmu); try eassumption.
      eapply val_list_inject_forall_inject. 
      eapply val_list_inject_incr; try eassumption.
      apply restrict_incr.
    intros [b2 [d [loc R2]]].
      exists b2, d.
      rewrite loc, R2. destruct (local_DomRng _ WDmu _ _ _ loc). intuition.
   intros b Hb. apply andb_true_iff in Hb. eapply Hb.
split. subst.
  split. 
    econstructor; eauto.
    eapply match_stackframes_replace_locals; eassumption.
    rewrite replace_locals_as_inj, replace_locals_vis. trivial.
    rewrite replace_locals_as_inj; trivial.
rewrite replace_locals_as_inj, replace_locals_vis,
         replace_locals_frgnBlocksSrc.
intuition.
  split; intros b Hb.
    rewrite replace_locals_DOM in Hb. eapply SMV; trivial.
    rewrite replace_locals_RNG in Hb. eapply SMV; trivial.
assert (MINJR: Mem.inject (restrict (as_inj mu) (vis mu)) m1 m2). 
  eapply inject_restrict; try eassumption.
assert (RCnu: REACH_closed m1 (mapped (shared_of nu))).
  subst. rewrite replace_locals_shared.
  clear MINJ.
  red; intros b Hb. apply REACHAX in Hb. destruct Hb as [L HL].
    generalize dependent b.
    induction L; simpl; intros; inv HL. trivial.
    specialize (IHL _ H3); clear H3.
    destruct (mappedD_true _ _ IHL) as [[bb ofs] Hbb]. clear IHL.
    apply mapped_charT.
    assert (MV:= Mem.mi_memval _ _ _ (Mem.mi_inj _ _ _ MINJR)).
    destruct (joinD_Some _ _ _ _ _ Hbb); clear Hbb.
      exploit (MV b' z bb ofs).
        eapply restrictI_Some. apply foreign_in_all; eassumption.
          unfold vis. unfold foreign_of in H0. destruct mu. simpl in *.
          destruct (frgnBlocksSrc b'); inv H0. intuition.
        assumption.
      clear MV; intros. rewrite H6 in H2. inv H2.
      exists (b2, delta). apply joinI.
      remember (locBlocksSrc mu b) as d.
      destruct d; apply eq_sym in Heqd. 
        right; simpl. 
        split. eapply locBlocksSrc_foreignNone; eassumption.
        destruct (restrictD_Some _ _ _ _ _ H7); clear H7.
        destruct (joinD_Some _ _ _ _ _ H2).
          destruct (extern_DomRng _ WDmu _ _ _ H5).
          apply extBlocksSrc_locBlocksSrc in H7. rewrite H7 in Heqd; inv Heqd.
           trivial.
        destruct H5. rewrite H7.
        assert (Rb: REACH m1 (exportedSrc mu vals1) b = true).
          eapply REACH_cons; try eassumption.
          eapply REACH_nil. unfold exportedSrc, sharedSrc. apply foreign_in_shared in H0. rewrite H0. intuition.
        rewrite Rb; trivial.
      left. eapply restrict_vis_foreign; try eassumption.
               destruct (restrictD_Some _ _ _ _ _ H7).
               rewrite (as_inj_locBlocks _ _ _ _ WDmu H2) in Heqd. trivial.
    destruct H0. remember (locBlocksSrc mu b' && REACH m1 (exportedSrc mu vals1) b') as d. 
       destruct d; apply eq_sym in Heqd; inv H2.
       apply andb_true_iff in Heqd; destruct Heqd.
      exploit (MV b' z bb ofs).
        eapply restrictI_Some. apply local_in_all; eassumption.
          unfold vis. rewrite H2; trivial.
        assumption.
      clear MV; intros. rewrite H6 in H7. inv H7.
      exists (b2, delta). apply joinI.
      remember (locBlocksSrc mu b) as d.
      destruct d; apply eq_sym in Heqd. 
        right; simpl. destruct (restrictD_Some _ _ _ _ _ H10); clear H10.
        split. eapply locBlocksSrc_foreignNone; eassumption.
        destruct (joinD_Some _ _ _ _ _ H7).
          destruct (extern_DomRng _ WDmu _ _ _ H9).
          apply extBlocksSrc_locBlocksSrc in H10. rewrite H10 in Heqd; inv Heqd.
           trivial.
        destruct H9. rewrite H10.
        assert (REACH m1 (exportedSrc mu vals1) b = true).
          eapply REACH_cons; try eassumption.
        rewrite H11. trivial.
      simpl. left. eapply restrict_vis_foreign; try eassumption.
               destruct (restrictD_Some _ _ _ _ _ H10).
               rewrite (as_inj_locBlocks _ _ _ _ WDmu H7) in Heqd. trivial.
eapply inject_mapped. eapply MINJ. eassumption.
  subst. rewrite replace_locals_shared.
    red; intros b b' delta Hb. destruct (joinD_Some _ _ _ _ _ Hb); clear Hb.
    eapply foreign_in_all; eassumption.
    destruct H0.
      destruct (locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b); inv H2.
      rewrite H4; eapply local_in_all; eassumption.
Qed.

Lemma match_stackframes_replace_externs mu s s': forall
    (MS: match_stackframes mu s s') frgnS frgnT
    (HfrgnSrc: forall b, frgnBlocksSrc mu b = true -> frgnS b = true),
  match_stackframes (replace_externs mu frgnS frgnT) s s'.
Proof.
  intros.
  induction MS; econstructor; eauto.
    rewrite replace_externs_as_inj, replace_externs_vis.
    eapply regset_incr; eauto.
      red; intros. destruct (restrictD_Some _ _ _ _ _ H1).
      apply restrictI_Some; trivial.
      unfold vis in H3. destruct (locBlocksSrc mu b); simpl in *; trivial.
     apply HfrgnSrc; trivial.
    rewrite  replace_externs_local; trivial.
Qed.

Lemma match_stackframes_extern_incr mu s s': forall
        (MS: match_stackframes mu s s') mu' 
        (INC: extern_incr mu mu') (WD': SM_wd mu'),
       match_stackframes mu' s s'.
Proof.
  intros.
  induction MS; econstructor; eauto.
    eapply regset_incr; eauto.
      apply extern_incr_restrict; eauto.
    assert (LOC: local_of mu= local_of mu') by eapply INC.
      rewrite LOC in H0; trivial.
Qed.

Lemma MATCH_afterExternal: forall (mu : SM_Injection) (st1 st2 : RTL_core) (m1 : mem)
  (e : external_function) (vals1 : list val) (m2 : mem) (ef_sig : signature)
  (vals2 : list val) (e' : external_function) (ef_sig' : signature)
  (INJ: Mem.inject (as_inj mu) m1 m2)
  (MTCH: MATCH st1 mu st1 m1 st2 m2)
  (AtExtSrc: at_external rtl_eff_sem st1 = Some (e, ef_sig, vals1))
  (AtExtTgt: at_external rtl_eff_sem st2 = Some (e', ef_sig', vals2))
  (ArgsInj: Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2)
  (pubSrc' : block -> bool)
  (HpubSrc: pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b))
  (pubTgt' : block -> bool)
  (HpubTgt: pubTgt' = (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b))
  (nu : SM_Injection)
  (Hnu: nu = replace_locals mu pubSrc' pubTgt')
  (nu' : SM_Injection) (ret1 : val) (m1' : mem) (ret2 : val) (m2' : mem)
  (INC: extern_incr nu nu')
  (SEP: sm_inject_separated nu nu' m1 m2)
  (WDnu': SM_wd nu')
  (SMVnu': sm_valid nu' m1' m2')
  (INJnu': Mem.inject (as_inj nu') m1' m2')
  (RetInj: val_inject (as_inj nu') ret1 ret2)
  (FWD1: mem_forward m1 m1')  
  (FWD2: mem_forward m2 m2')
  (frgnSrc' : block -> bool)
  (HfrgnSrc: frgnSrc' = (fun b =>
      DomSrc nu' b &&
      (negb (locBlocksSrc nu' b) && REACH m1' (exportedSrc nu' (ret1 :: nil)) b)))
  (frgnTgt' : block -> bool)
  (HfrgnTgt: frgnTgt' = (fun b =>
      DomTgt nu' b &&
      (negb (locBlocksTgt nu' b) && REACH m2' (exportedTgt nu' (ret2 :: nil)) b)))
  mu' (Hmu': mu' = replace_externs nu' frgnSrc' frgnTgt')
  (UnchPrivSrc: Mem.unchanged_on (fun b z => locBlocksSrc nu b = true /\ pubBlocksSrc nu b = false) m1 m1')
  (UnchLOOR: Mem.unchanged_on (local_out_of_reach nu m1) m2 m2'),
exists st1' st2' : RTL_core,
  after_external rtl_eff_sem (Some ret1) st1 = Some st1' /\
  after_external rtl_eff_sem (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros. simpl.
 destruct MTCH as [MC [RC [PG [GFP [Glob [VAL WDmu]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 destruct f; inv H3. simpl in *. inv AtExtTgt.
 eexists. eexists.
    split. reflexivity.
    split. reflexivity.
 simpl in *.
(* inv TF.*)
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
    destruct H2 as [DomNu' Rb']. 
    clear INC SEP INCvisNu' UnchLOOR UnchPrivSrc.
    remember (locBlocksSrc nu' b) as d.
    destruct d; simpl; trivial. apply eq_sym in Heqd.
    apply andb_true_iff.
    split. assert (RET: Forall2 (val_inject (as_inj nu')) (ret1::nil) (ret2::nil)).
              constructor. assumption. constructor.
           destruct (REACH_as_inj _ WDnu' _ _ _ _ INJnu' RET
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
split. clear - WDnu' INC H INJnu' RetInj.
  econstructor; try eassumption.
  eapply match_stackframes_replace_externs.
    eapply match_stackframes_extern_incr; try eapply INC; trivial.
    eapply match_stackframes_replace_locals; eauto.
  intros. unfold DomSrc.
    specialize (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H0); intros EXT.
    rewrite EXT, (extBlocksSrc_locBlocksSrc _ WDnu' _ EXT). simpl.
    apply REACH_nil. unfold exportedSrc.
    rewrite (frgnSrc_shared _ WDnu' _ H0). intuition. 
  unfold vis. rewrite replace_externs_as_inj. 
       rewrite replace_externs_frgnBlocksSrc, replace_externs_locBlocksSrc. 
       eapply restrict_val_inject; try eassumption.
       intros.
        destruct (getBlocks_inject (as_inj nu') (ret1::nil) (ret2::nil))
           with (b:=b) as [bb [dd [JJ' GBbb]]]; try eassumption.
          constructor. assumption. constructor.
        remember (locBlocksSrc nu' b) as d.
        destruct d; simpl; trivial. apply andb_true_iff.
        split. eapply as_inj_DomRng; eassumption.
        apply REACH_nil. unfold exportedSrc.
           rewrite H0; trivial.
  rewrite replace_externs_as_inj; trivial.
  
destruct (eff_after_check2 _ _ _ _ _ INJnu' RetInj 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMVnu').
unfold vis in *.
  rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
          (*replace_externs_DomTgt, *) replace_externs_as_inj in *.
intuition.
(*as in selectionproofEFF*)
  red; intros b fb Hb. destruct (GFP _ _ Hb). split; trivial.
  eapply extern_incr_as_inj; try eassumption.
  rewrite replace_locals_as_inj. assumption.
Qed.

Lemma MATCH_initial: forall (v1 v2 : val) (sig : signature) entrypoints
  (EP: In (v1, v2, sig) entrypoints)
  (entry_points_ok : forall (v1 v2 : val) (sig : signature),
                  In (v1, v2, sig) entrypoints ->
                  exists
                    (b : Values.block) f1 f2,
                    v1 = Vptr b Int.zero /\
                    v2 = Vptr b Int.zero /\
                    Genv.find_funct_ptr ge b = Some f1 /\
                    Genv.find_funct_ptr tge b = Some f2)
  (vals1 : list val) c1 (m1 : mem) (j : meminj)
  (vals2 : list val) (m2 : mem) (DomS DomT : Values.block -> bool)
  (Ini : initial_core rtl_eff_sem ge v1 vals1 = Some c1)
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
exists c2,
  initial_core rtl_eff_sem tge v2 vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2.
Proof.
intros.
  inversion Ini.
  unfold RTL_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1 
            (sig_args (funsig (Internal f))) 
           && val_casted.vals_defined vals1).
  2: solve[intros H2; rewrite H2 in H1; inv H1].
  intros H2; rewrite H2 in H1. inv H1. 
  exploit funct_ptr_translated; eauto. intros FP.
    destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
    subst. inv A. rewrite C in Heqzz. inv Heqzz.
    unfold tge in FP. rewrite D in FP. inv FP.
    unfold rtl_eff_sem, rtl_coop_sem. simpl.
    case_eq (Int.eq_dec Int.zero Int.zero). intros ? e.
    rewrite D.
  assert (val_casted.val_has_type_list_func vals2
           (sig_args (funsig (Internal (transf_function f))))=true) as ->.
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; simpl in H2. solve[inv H2].
    assert (sig_args (funsig (Internal (transf_function f)))
          = sig_args (funsig (Internal f))) as ->.
    { specialize (sig_preserved (Internal f)). simpl. intros. rewrite H. reflexivity. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (funsig (Internal f)))); auto. }
  assert (val_casted.vals_defined vals2=true) as ->.
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; inv H2. }
  simpl. 
  eexists; split. reflexivity.
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
  split. simpl.
    eapply match_states_call; try eassumption.
      constructor. 
      rewrite initial_SM_as_inj.
        unfold vis, initial_SM; simpl.
        apply forall_inject_val_list_inject.
        eapply restrict_forall_vals_inject; try eassumption.
          intros. apply REACH_nil. rewrite H1; intuition.
      rewrite initial_SM_as_inj; trivial.
  rewrite initial_SM_as_inj.
  intuition.
    (*as in selectionproofEFF*)
      red; intros. specialize (Genv.find_funct_ptr_not_fresh prog). intros.
         destruct InitMem as [m0 [INIT_MEM [? ?]]].
         specialize (H2 _ _ _ INIT_MEM H1). 
         destruct (valid_init_is_global _ R _ INIT_MEM _ H2) as [id Hid]. 
           destruct PG as [PGa [PGb PGc]]. split. eapply PGa; eassumption.
         unfold isGlobalBlock. 
          apply orb_true_iff. left. apply genv2blocksBool_char1.
            simpl. exists id; eassumption.
 Qed. 

Lemma MATCH_step: forall st1 m1 st1' m1'
      (CS: corestep rtl_eff_sem ge st1 m1 st1' m1')
      st2 mu m2 (MTCH: MATCH st1 mu st1 m1 st2 m2),
  (exists st2' m2',
    corestep rtl_eff_sem tge st2 m2 st2' m2' /\
    exists mu', intern_incr mu mu' /\
      sm_inject_separated mu mu' m1 m2 /\
      sm_locally_allocated mu mu' m1 m2 m1' m2' /\
      MATCH st1' mu' st1' m1' st2' m2')
   \/ (measure st1' < measure st1 /\ 
       sm_locally_allocated mu mu m1 m2 m1' m2 /\
       MATCH st2 mu st1' m1' st2 m2)%nat.
Proof.
  induction 1; intros; destruct MTCH as [MS PRE];
  inv MS; EliminatedInstr.

(* nop *)
  TransfInstr.
  left; eexists; eexists; split.
      eapply rtl_corestep_exec_Inop; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
         rewrite (freshloc_irrefl); intuition.
  split.
    constructor; auto.
  intuition.
(* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
         rewrite (freshloc_irrefl); intuition.
  split.
    econstructor; eauto.
  auto. 

(* op *)
  TransfInstr.
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) (rs##args) (rs'##args)). 
    apply regset_get_list; auto.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_operation_inject; try eapply H0.
    eassumption.
    eapply restrictI_Some. apply local_in_all; eauto.
      unfold vis. destruct (local_DomRng _ WD _ _ _ SPloc). intuition.
    eassumption.
    eapply inject_restrict; eassumption.
  intros [v' [EVAL' VLD]]. 
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' (rs'#res <- v')), m2; split.
  eapply rtl_corestep_exec_Iop; eauto.  rewrite <- EVAL'.
  rewrite eval_shift_stack_operation. simpl. rewrite Int.add_zero.
  apply eval_operation_preserved. exact symbols_preserved.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    econstructor; eauto. apply regset_set; auto.
  intuition.

(* eliminated move *)
  rewrite H1 in H. clear H1. inv H. 
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
         rewrite (freshloc_irrefl); intuition.
  split.
    econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.
  intuition. 

(* load *)
  TransfInstr.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) (rs##args) (rs'##args)). 
    apply regset_get_list; auto.
  exploit eval_addressing_inject; try eapply H0.
    apply PGR.
    eapply restrictI_Some. apply local_in_all; eauto.
      unfold vis. destruct (local_DomRng _ WD _ _ _ SPloc). intuition.
    eassumption.
  rewrite eval_shift_stack_addressing; simpl. rewrite Int.add_zero. 
  intros [a' [ADDR' ALD]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))); eauto.
  intros [v' [LOAD' VLD]].
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' (rs'#dst <- v')), m2; split.
    eapply rtl_corestep_exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
    apply eval_addressing_preserved. exact symbols_preserved. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    econstructor; eauto. apply regset_set; auto.
  intuition.

(* store *)
  TransfInstr.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (SrcInj: val_inject (restrict (as_inj mu) (vis mu)) (rs # src) (rs' # src)). 
    eapply RLD. 
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) (rs##args) (rs'##args)). 
    apply regset_get_list; auto.
  exploit eval_addressing_inject; try eapply H0.
    apply PGR.
    eapply restrictI_Some. apply local_in_all; eauto.
      unfold vis. destruct (local_DomRng _ WD _ _ _ SPloc). intuition.
    eassumption.
  rewrite eval_shift_stack_addressing; simpl. rewrite Int.add_zero. 
  intros [a' [ADDR' ALD]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))); try eassumption.
  intros [m2' [STORE' MLD']].
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' rs'), m2'; split.
    eapply rtl_corestep_exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
    apply eval_addressing_preserved. exact symbols_preserved. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (storev_freshloc _ _ _ _ _ H1);
            try rewrite (storev_freshloc _ _ _ _ _ STORE'); intuition.
  destruct a; simpl in H1; try discriminate.
  inv ALD.
  split.    
    econstructor; eauto.
    exploit (Mem.store_mapped_inject (as_inj mu)). eassumption. eassumption. 
      eapply restrictD_Some; eassumption. 
      eapply val_inject_incr; try eassumption. eapply restrict_incr.
      intros [m2'' [ST2 INJ]]. simpl in STORE'. 
      assert (PERM: Mem.perm m b (Int.unsigned i) Cur Writable).
        eapply Mem.store_valid_access_3. eassumption. 
        specialize (size_chunk_pos chunk); intros; omega.
      exploit (Mem.address_inject (restrict (as_inj mu) (vis mu)) m m2); try eassumption.
         intros. rewrite H2 in STORE'.
      rewrite ST2 in STORE'; inv STORE'. eassumption. 
  intuition.
    eapply REACH_Store; try eassumption.  
      destruct (restrictD_Some _ _ _ _ _ H4); trivial.
      intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.   
                  rewrite H2 in SrcInj. inv SrcInj.
                  destruct (restrictD_Some _ _ _ _ _ H7); trivial.
    split; intros; 
      eapply Mem.store_valid_block_1; try eassumption;
      eapply SMV; assumption.

(* call *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  exploit find_function_translated; eauto.
    eapply restrict_preserves_globalfun_ptr; try eassumption.
    intros. unfold vis. rewrite (Glob _ H1); intuition.
  intro FIND'.  
  TransfInstr.
(* call turned tailcall *)
  assert ({ m'' | Mem.free m2 sp' 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7. 
    red; intros; omegaContradiction.
  destruct X as [m'' FREE].
  left. exists (RTL_Callstate s' (transf_fundef fd) (rs'##args)), m''; split.
  eapply rtl_corestep_exec_Itailcall; eauto. apply sig_preserved.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _ FREE);
            try rewrite freshloc_irrefl; intuition.
  split.
    constructor. eapply match_stackframes_tail; eauto. apply regset_get_list; auto.
    eapply Mem.free_right_inject; eauto.
    rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
  intuition.
    split; intros.  
      eapply SMV; assumption.
      eapply free_forward; try eassumption.
        eapply SMV; assumption.

(* call that remains a call *)
  left. exists (RTL_Callstate (Stackframe res (transf_function f) (Vptr sp' Int.zero) pc' rs' :: s')
                          (transf_fundef fd) (rs'##args)), m2; split.
    eapply rtl_corestep_exec_Icall; eauto. apply sig_preserved. 
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite freshloc_irrefl; intuition.
  split.
    constructor. constructor; auto. apply regset_get_list; auto. auto.
  intuition. 

(* tailcall *) 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  exploit find_function_translated; eauto.
    eapply restrict_preserves_globalfun_ptr; try eassumption.
    intros. unfold vis. rewrite (Glob _ H1); intuition.
  intro FIND'.
  exploit free_parallel_inject. eassumption. eassumption.
    eapply local_in_all; eassumption.
  intros [m2' [FREE EXT]].
  TransfInstr.
  simpl in FREE; rewrite Zplus_0_r in FREE. 
  left. exists (RTL_Callstate s' (transf_fundef fd) (rs'##args)), m2'; split.
    eapply rtl_corestep_exec_Itailcall; eauto. apply sig_preserved.
    rewrite stacksize_preserved; auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _ H2);
            try rewrite (freshloc_free _ _ _ _ _ FREE); intuition.
  split.
    constructor. auto.  apply regset_get_list; auto. auto.
  intuition.
    eapply REACH_closed_free; eassumption.
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.

(* builtin *)
  TransfInstr.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (ArgsInj:= regset_get_list _ _ _ args RLD).
  exploit (inlineable_extern_inject _ _ GDE_lemma); try eapply H0.
        eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' (rs'#res <- vres')), tm'; split.
    eapply rtl_corestep_exec_Ibuiltin; eauto.
  exists mu'.
    intuition.
    split. 
      econstructor; eauto.
        eapply match_stackframes_intern_incr; eassumption.
        apply regset_set; auto.
          eapply regset_incr; eauto.
            apply intern_incr_restrict; trivial.
        eapply INCR; trivial.
      intuition. 
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      red; intros b fb Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. eapply (Glob _ H2). 

(* cond *)
  TransfInstr. 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (ArgsInj:= regset_get_list _ _ _ args RLD).
  exploit eval_condition_inject; try eassumption.
    eapply inject_restrict; eauto.
  intros EvalCond'.
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) (if b then ifso else ifnot) rs'), m2; split.
     eapply rtl_corestep_exec_Icond; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite freshloc_irrefl; intuition.
  split.
    constructor; auto.
  intuition.

(* jumptable *)
  TransfInstr. 
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' rs'), m2; split.
    eapply rtl_corestep_exec_Ijumptable; eauto.
    generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite freshloc_irrefl; intuition.
  split.
    constructor; auto.
  intuition.

(* return *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  exploit free_parallel_inject; eauto. eapply local_in_all; eassumption.
  intros [m2' [FREE INJ']].
  simpl in FREE; rewrite Zplus_0_r in FREE.
  TransfInstr.
  left. exists (RTL_Returnstate s' (regmap_optget or Vundef rs')), m2'; split.
    apply rtl_corestep_exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  exists mu.
  intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b'; 
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ FREE); intuition.
  split. 
    constructor; try eassumption.
    destruct or; simpl. apply RLD. constructor.
  intuition.
    eapply REACH_closed_free; eassumption.
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.

(* eliminated return None *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (or = None) by congruence. subst or. 
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
         try rewrite (freshloc_free _ _ _ _ _ H0);
         try rewrite freshloc_irrefl; intuition.
  split.
    constructor. auto.
      simpl. constructor.
      eapply Mem.free_left_inject; eauto.
  intuition. 
    eapply REACH_closed_free; eassumption.
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply SMV; assumption.

(* eliminated return Some *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
         try rewrite (freshloc_free _ _ _ _ _ H0);
         try rewrite freshloc_irrefl; intuition.
  split.
    constructor. auto.
    simpl. auto.
    eapply Mem.free_left_inject; eauto.
  intuition. 
    eapply REACH_closed_free; eassumption.
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply SMV; assumption.

(* internal call *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [IntInc [AIb'1 
       [AIb'2 [Sep [LocAlloc [WD' [SMV' RC']]]]]]]]]]]]; eauto; try apply Zle_refl.
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0 && eliminate_tailcalls tt); auto. 
  destruct H0 as [EQ1 [EQ2 EQ3]]. 
  left. eexists; eexists; split.
          simpl. eapply rtl_corestep_exec_function_internal; eauto. rewrite EQ1; eauto.
  exists mu'.
  intuition.
  split. 
    rewrite EQ2. rewrite EQ3. constructor; auto.
        eapply match_stackframes_intern_incr; eassumption.
        apply regset_init_regs.
          eapply val_list_inject_incr; try eassumption.
            apply intern_incr_restrict; trivial.
          destruct (joinD_Some _ _ _ _ _ AIb'1) as [EXT | [EXT LOC]]; eauto.
            assert (extern_of mu = extern_of mu') by eapply IntInc.
            rewrite <- H1 in EXT. apply extern_in_all in EXT.
            exfalso; clear - EXT H WD SMV.
            eapply Mem.fresh_block_alloc; eauto.
            eapply SMV. 
            eapply as_inj_DomRng; eassumption.
   intuition.
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      red; intros b fb Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
          rewrite <- FRG. eapply (Glob _ H1). 

(* no rule for external call
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto. *)

(* returnstate *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  inv H1. 
(* synchronous return in both programs *)
  left. eexists; eexists; split.
        simpl. eapply rtl_corestep_exec_return.
  exists mu. intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b'; 
          rewrite freshloc_irrefl; intuition.
  split. econstructor; eauto. apply regset_set; auto.
  intuition. 
(* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length. 
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat. 
  generalize (return_measure_bounds (fn_code f) pc). omega.  
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
         try rewrite freshloc_irrefl; intuition.
  split.
    econstructor; eauto.
    rewrite Regmap.gss. auto.
  intuition. 
Qed.

Lemma MATCH_effstep: forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
      (CS: effstep rtl_eff_sem ge U1 st1 m1 st1' m1')
      st2 mu m2
      (UHyp: forall b z, U1 b z = true -> vis mu b = true)
      (MTCH: MATCH st1 mu st1 m1 st2 m2),
  (exists st2' m2' U2,
    effstep rtl_eff_sem tge U2 st2 m2 st2' m2' /\
    exists mu', intern_incr mu mu' /\
      sm_inject_separated mu mu' m1 m2 /\
      sm_locally_allocated mu mu' m1 m2 m1' m2' /\
      MATCH st1' mu' st1' m1' st2' m2'  /\
     (forall (b : block) (ofs : Z),
      U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1)%Z = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)))
   \/ (measure st1' < measure st1 /\ 
       sm_locally_allocated mu mu m1 m2 m1' m2 /\
       MATCH st2 mu st1' m1' st2 m2)%nat.
Proof.
  induction 1; intros; destruct MTCH as [MS PRE];
  inv MS; EliminatedInstr.

(* nop *)
  TransfInstr.
  left; eexists; eexists; eexists; split.
      eapply rtl_effstep_exec_Inop; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
         rewrite (freshloc_irrefl); intuition.
  split. 
    split.
      constructor; auto.
    intuition.
  intuition.
(* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
         rewrite (freshloc_irrefl); intuition.
  split.
    econstructor; eauto.
  auto. 

(* op *)
  TransfInstr.
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) (rs##args) (rs'##args)). 
    apply regset_get_list; auto.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  exploit eval_operation_inject; try eapply H0.
    eassumption.
    eapply restrictI_Some. apply local_in_all; eauto.
      unfold vis. destruct (local_DomRng _ WD _ _ _ SPloc). intuition.
    eassumption.
    eapply inject_restrict; eassumption.
  intros [v' [EVAL' VLD]]. 
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' (rs'#res <- v')), m2; eexists; split.
  eapply rtl_effstep_exec_Iop; eauto.  rewrite <- EVAL'.
  rewrite eval_shift_stack_operation. simpl. rewrite Int.add_zero.
  apply eval_operation_preserved. exact symbols_preserved.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    split.
      econstructor; eauto. apply regset_set; auto.
    intuition.
  intuition.

(* eliminated move *)
  rewrite H1 in H. clear H1. inv H. 
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb; 
         rewrite (freshloc_irrefl); intuition.
  split.
    econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.
  intuition. 

(* load *)
  TransfInstr.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) (rs##args) (rs'##args)). 
    apply regset_get_list; auto.
  exploit eval_addressing_inject; try eapply H0.
    apply PGR.
    eapply restrictI_Some. apply local_in_all; eauto.
      unfold vis. destruct (local_DomRng _ WD _ _ _ SPloc). intuition.
    eassumption.
  rewrite eval_shift_stack_addressing; simpl. rewrite Int.add_zero. 
  intros [a' [ADDR' ALD]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))); eauto.
  intros [v' [LOAD' VLD]].
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' (rs'#dst <- v')), m2; eexists; split.
    eapply rtl_effstep_exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
    apply eval_addressing_preserved. exact symbols_preserved. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    split.
      econstructor; eauto. apply regset_set; auto.
    intuition.
  intuition.

(* store *)
  TransfInstr.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (SrcInj: val_inject (restrict (as_inj mu) (vis mu)) (rs # src) (rs' # src)). 
    eapply RLD. 
  assert (ArgsInj: val_list_inject (restrict (as_inj mu) (vis mu)) (rs##args) (rs'##args)). 
    apply regset_get_list; auto.
  exploit eval_addressing_inject; try eapply H0.
    apply PGR.
    eapply restrictI_Some. apply local_in_all; eauto.
      unfold vis. destruct (local_DomRng _ WD _ _ _ SPloc). intuition.
    eassumption.
  rewrite eval_shift_stack_addressing; simpl. rewrite Int.add_zero. 
  intros [a' [ADDR' ALD]].
  assert (MInjR : Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption.
  exploit (Mem.storev_mapped_inject (restrict (as_inj mu) (vis mu))); try eassumption.
  intros [m2' [STORE' MLD']].
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' rs'), m2'; eexists; split.
    eapply rtl_effstep_exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
    apply eval_addressing_preserved. exact symbols_preserved. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (storev_freshloc _ _ _ _ _ H1);
            try rewrite (storev_freshloc _ _ _ _ _ STORE'); intuition.
  destruct a; simpl in H1; try discriminate.
  inv ALD.
  split.    
    split.
      econstructor; eauto.
      exploit (Mem.store_mapped_inject (as_inj mu)). eassumption. eassumption. 
        eapply restrictD_Some; eassumption. 
        eapply val_inject_incr; try eassumption. eapply restrict_incr.
        intros [m2'' [ST2 INJ]]. simpl in STORE'. 
        assert (PERM: Mem.perm m b (Int.unsigned i) Cur Writable).
          eapply Mem.store_valid_access_3. eassumption. 
          specialize (size_chunk_pos chunk); intros; omega.
        exploit (Mem.address_inject (restrict (as_inj mu) (vis mu)) m m2); try eassumption.
          intros. rewrite H2 in STORE'.
        rewrite ST2 in STORE'; inv STORE'. eassumption.  
    intuition.
    eapply REACH_Store; try eassumption.  
      destruct (restrictD_Some _ _ _ _ _ H4); trivial.
      intros bb' Hbb'. rewrite getBlocks_char in Hbb'. destruct Hbb' as [off Hoff].
                  destruct Hoff; try contradiction. subst.   
                  rewrite H2 in SrcInj. inv SrcInj.
                  destruct (restrictD_Some _ _ _ _ _ H7); trivial.
    split; intros; 
      eapply Mem.store_valid_block_1; try eassumption;
      eapply SMV; assumption.
  intros.
    apply StoreEffectD in H2. destruct H2 as [ii [VV Arith]].
      inv VV. 
      split. eapply visPropagateR; eassumption.
      intros. eapply StoreEffect_PropagateLeft; try eassumption.
         econstructor. eassumption. trivial.
      unfold StoreEffect.
      destruct (eq_block b0 b0); simpl in *; subst.
        destruct (zle (Int.unsigned (Int.add i (Int.repr delta))) ofs); simpl.
          destruct (zlt ofs
                     (Int.unsigned (Int.add i (Int.repr delta)) +
                      Z.of_nat (length (encode_val chunk rs' # src)))); simpl; trivial.
          omega. omega.
      elim n; trivial.

(* call *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  exploit find_function_translated; eauto.
    eapply restrict_preserves_globalfun_ptr; try eassumption.
    intros. unfold vis. rewrite (Glob _ H1); intuition.
  intro FIND'.  
  TransfInstr. 
(* call turned tailcall *)
  assert ({ m'' | Mem.free m2 sp' 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7. 
    red; intros; omegaContradiction.
  destruct X as [m'' FREE].
  left. exists (RTL_Callstate s' (transf_fundef fd) (rs'##args)), m''; eexists; split.
  eapply rtl_effstep_exec_Itailcall; eauto. apply sig_preserved.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _ FREE);
            try rewrite freshloc_irrefl; intuition.
  split.
    split.
      constructor. eapply match_stackframes_tail; eauto. apply regset_get_list; auto.
      eapply Mem.free_right_inject; eauto.
      rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
    intuition.
    split; intros.  
      eapply SMV; assumption.
      eapply free_forward; try eassumption.
        eapply SMV; assumption.
  intros. apply FreeEffectD in H1.
     destruct H1 as [SP [VB Arith]]; subst.
     destruct (local_DomRng _ WD _ _ _ SPloc).
     unfold visTgt. rewrite H2. intuition.

(* call that remains a call *)
  left. exists (RTL_Callstate (Stackframe res (transf_function f) (Vptr sp' Int.zero) pc' rs' :: s')
                          (transf_fundef fd) (rs'##args)), m2; eexists; split.
    eapply rtl_effstep_exec_Icall; eauto. apply sig_preserved. 
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite freshloc_irrefl; intuition.
  split.
    split.
      constructor. constructor; auto. apply regset_get_list; auto. auto.
    intuition.
  intuition. 

(* tailcall *) 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]]. 
  exploit find_function_translated; eauto.
    eapply restrict_preserves_globalfun_ptr; try eassumption.
    intros. unfold vis. rewrite (Glob _ H1); intuition.
  intro FIND'.  
  TransfInstr. 
  exploit free_parallel_inject. eassumption. eassumption.
    eapply local_in_all; eassumption.
  intros [m2' [FREE EXT]].
  simpl in FREE; rewrite Zplus_0_r in FREE. 
  left. exists (RTL_Callstate s' (transf_fundef fd) (rs'##args)), m2'; eexists; split.
    eapply rtl_effstep_exec_Itailcall; eauto. apply sig_preserved.
    rewrite stacksize_preserved; auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite (freshloc_free _ _ _ _ _ H2);
            try rewrite (freshloc_free _ _ _ _ _ FREE); intuition.
  split.
    split.
      constructor. auto.  apply regset_get_list; auto. auto.
    intuition.
      eapply REACH_closed_free; eassumption.
      split; intros;
        eapply Mem.valid_block_free_1; try eassumption;
        eapply SMV; assumption.
  intros. apply FreeEffectD in H1.
     destruct H1 as [SP [VB Arith]]; subst.
     destruct (local_DomRng _ WD _ _ _ SPloc).
     unfold visTgt. rewrite H3. intuition.


(* builtin *)
  TransfInstr.
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  assert (ArgsInj:= regset_get_list _ _ _ args RLD).
  exploit (inlineable_extern_inject _ _ GDE_lemma); try eapply H0.
        eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' (rs'#res <- vres')), tm'; eexists; split.
    eapply rtl_effstep_exec_Ibuiltin; eauto.
  exists mu'.
  split; trivial.
  split; trivial.
  split; trivial.
  split.
    split. 
      econstructor; eauto.
        eapply match_stackframes_intern_incr; eassumption.
        apply regset_set; auto.
          eapply regset_incr; eauto.
            apply intern_incr_restrict; trivial.
        eapply INCR; trivial.
    intuition. 
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      red; intros b fb Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
          rewrite <- FRG. eapply (Glob _ H2). 
  eapply BuiltinEffect_Propagate; eassumption. 

(* cond *)
  TransfInstr. 
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (ArgsInj:= regset_get_list _ _ _ args RLD).
  exploit eval_condition_inject; try eassumption.
    eapply inject_restrict; eauto.
  intros EvalCond'.
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) (if b then ifso else ifnot) rs'), m2; eexists; split.
     eapply rtl_effstep_exec_Icond; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite freshloc_irrefl; intuition.
  split.
    split.
      constructor; auto.
    intuition.
  intuition.

(* jumptable *)
  TransfInstr. 
  left. exists (RTL_State s' (transf_function f) (Vptr sp' Int.zero) pc' rs'), m2; eexists; split.
    eapply rtl_effstep_exec_Ijumptable; eauto.
    generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
         repeat split; extensionality bb; 
            try rewrite freshloc_irrefl; intuition.
  split.
    split.
      constructor; auto.
    intuition.
  intuition.

(* return *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  exploit free_parallel_inject; eauto. eapply local_in_all; eassumption.
  intros [m2' [FREE INJ']].
  simpl in FREE; rewrite Zplus_0_r in FREE.
  TransfInstr.
  left. exists (RTL_Returnstate s' (regmap_optget or Vundef rs')), m2'; eexists; split.
    apply rtl_effstep_exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      repeat split; extensionality b'; 
          try rewrite (freshloc_free _ _ _ _ _ H0);
          try rewrite (freshloc_free _ _ _ _ _ FREE); intuition.
  split.
    split.
      constructor; try eassumption.
      destruct or; simpl. apply RLD. constructor.
    intuition.
    eapply REACH_closed_free; eassumption.
    split; intros;
      eapply Mem.valid_block_free_1; try eassumption;
      eapply SMV; assumption.
  intros. apply FreeEffectD in H1.
     destruct H1 as [SP [VB Arith]]; subst.
     destruct (local_DomRng _ WD _ _ _ SPloc).
     unfold visTgt. rewrite H2. intuition.

(* eliminated return None *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (or = None) by congruence. subst or. 
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
         try rewrite (freshloc_free _ _ _ _ _ H0);
         try rewrite freshloc_irrefl; intuition.
  split.
    constructor. auto.
      simpl. constructor.
      eapply Mem.free_left_inject; eauto.
  intuition. 
    eapply REACH_closed_free; eassumption.
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply SMV; assumption.

(* eliminated return Some *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega.
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
         try rewrite (freshloc_free _ _ _ _ _ H0);
         try rewrite freshloc_irrefl; intuition.
  split.
    constructor. auto.
    simpl. auto.
    eapply Mem.free_left_inject; eauto.
  intuition. 
    eapply REACH_closed_free; eassumption.
    split; intros.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply SMV; assumption.

(* internal call *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  edestruct alloc_parallel_intern as [mu' [tm' [b' [Alloc' [MInj' [IntInc [AIb'1 
       [AIb'2 [Sep [LocAlloc [WD' [SMV' RC']]]]]]]]]]]]; eauto; try apply Zle_refl.
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0 && eliminate_tailcalls tt); auto. 
  destruct H0 as [EQ1 [EQ2 EQ3]]. 
  left. eexists; eexists; eexists; split.
          simpl. eapply rtl_effstep_exec_function_internal; eauto. rewrite EQ1; eauto.
  exists mu'.
  intuition.
  split. 
    rewrite EQ2. rewrite EQ3. constructor; auto.
        eapply match_stackframes_intern_incr; eassumption.
        apply regset_init_regs.
          eapply val_list_inject_incr; try eassumption.
            apply intern_incr_restrict; trivial.
          destruct (joinD_Some _ _ _ _ _ AIb'1) as [EXT | [EXT LOC]]; eauto.
            assert (extern_of mu = extern_of mu') by eapply IntInc.
            rewrite <- H1 in EXT. apply extern_in_all in EXT.
            exfalso; clear - EXT H WD SMV.
            eapply Mem.fresh_block_alloc; eauto.
            eapply SMV. 
            eapply as_inj_DomRng; eassumption.
   intuition.
      eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
      red; intros b fb Hb. destruct (GFP _ _ Hb).
          split; trivial.
          eapply intern_incr_as_inj; eassumption.
      assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply IntInc.
          rewrite <- FRG. eapply (Glob _ H1). 

(* no rule for external call
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto. *)

(* returnstate *)
  destruct PRE as [RC [PG [GFP [Glob [SMV WD]]]]].
  inv H1. 
(* synchronous return in both programs *)
  left. eexists; eexists; eexists; split.
        simpl. eapply rtl_effstep_exec_return.
  exists mu. intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      apply sm_locally_allocatedChar.
      repeat split; extensionality b'; 
          rewrite freshloc_irrefl; intuition.
  split. econstructor; eauto. apply regset_set; auto.
  intuition. 
(* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length. 
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat. 
  generalize (return_measure_bounds (fn_code f) pc). omega.  
  split.
      apply sm_locally_allocatedChar.
      repeat split; extensionality bb;
         try rewrite freshloc_irrefl; intuition.
  split.
    econstructor; eauto.
    rewrite Regmap.gss. auto.
  intuition. 
Qed.

Theorem transl_program_correct:
  forall (R: list_norepet (map fst (prog_defs prog)))
         entrypoints
         (entry_points_ok : 
            forall v1 v2 sig,
              In (v1, v2, sig) entrypoints -> 
              exists b f1 f2, 
                v1 = Vptr b Int.zero 
                /\ v2 = Vptr b Int.zero
                /\ Genv.find_funct_ptr ge b = Some f1
                /\ Genv.find_funct_ptr tge b = Some f2)
         (init_mem: exists m0, Genv.init_mem prog = Some m0),
SM_simulation.SM_simulation_inject rtl_eff_sem
   rtl_eff_sem ge tge entrypoints.
Proof.
intros.
assert (GDE:= GDE_lemma).
apply sepcomp.effect_simulations_lemmas.inj_simulation_plus with
  (match_states:=MATCH)(measure :=measure).
(*apply sepcomp.effect_simulations_lemmas.inj_simulation_star_wf with
  (match_states:=MATCH) (order :=measure).*)
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
    eapply (MATCH_initial _ _ _ entrypoints); eauto.
    destruct init_mem as [m0 INIT].
    exists m0; split; auto.
    unfold meminj_preserves_globals in H3.    
    destruct H3 as [A [B C]].

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
    apply A in H3.
    assert (Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - H8; unfold Mem.valid_block in H8.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H3.
    assert (Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - H8; unfold Mem.valid_block in H8.
    xomega.
    
    intros b LT.    
    unfold ge. 
    apply valid_init_is_global with (b0 := b) in INIT.
    eapply INIT; auto.
    apply R.
    apply LT. }
(*halted*) 
  { intros. destruct H as [MC [RC [PG [GFP [Glob [SMV WD]]]]]]. 
    destruct c1; inv H0. destruct stack; inv H1.
    inv MC. exists v'.
    split. assumption.
    split. eassumption.
    simpl. inv H1. trivial. }
(* at_external*)
  { apply MATCH_atExternal. }
(* after_external*)
  { apply MATCH_afterExternal. }
(* core_diagram*)
  { intros. exploit MATCH_step; try eassumption.
    intros [[st2' [m2' [CS' [mu' X]]]] | [meas [locAlloc MTCH]]].
      exists st2', m2', mu'. intuition. 
      left. apply corestep_plus_one; assumption.
    exists st2, m2, mu. intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      right. split; trivial. apply corestep_star_zero. }
(*effcore_diagram*)
 { intros. exploit MATCH_effstep; try eassumption.
   intros [[st2' [m2' [U2 [CS' [mu' [INC [SEP [LOCALLOC [MTCH UH]]]]]]]]] | [meas [locAlloc MTCH]]].
   exists st2', m2', mu'.
     repeat (split; trivial).
     exists U2. split. left.  apply effstep_plus_one; assumption. assumption.
   exists st2, m2, mu. intuition.
      apply intern_incr_refl. 
      apply sm_inject_separated_same_sminj.
      exists EmptyEffect.
      split. right. split; trivial. apply effstep_star_zero.
      intuition.
 }
Qed.

End PRESERVATION.

(*Original CompCert proofs:
Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  (exists s2', step tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

(* nop *)
  TransfInstr. left. econstructor; split. 
  eapply exec_Inop; eauto. constructor; auto.
(* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega. split. auto. 
  econstructor; eauto. 

(* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit eval_operation_lessdef; eauto. 
  intros [v' [EVAL' VLD]]. 
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.  rewrite <- EVAL'.
  apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply regset_set; auto.
(* eliminated move *)
  rewrite H1 in H. clear H1. inv H. 
  right. split. simpl. omega. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence. 

(* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit eval_addressing_lessdef; eauto. 
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends; eauto. 
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  econstructor; eauto. apply regset_set; auto.

(* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit eval_addressing_lessdef; eauto. 
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.  
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'). eauto.  rewrite <- ADDR'.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  econstructor; eauto.

(* call *)
  exploit find_function_translated; eauto. intro FIND'.  
  TransfInstr.
(* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7. 
    red; intros; omegaContradiction.
  destruct X as [m'' FREE].
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m''); split.
  eapply exec_Itailcall; eauto. apply sig_preserved. 
  constructor. eapply match_stackframes_tail; eauto. apply regset_get_list; auto.
  eapply Mem.free_right_extends; eauto.
  rewrite stacksize_preserved. rewrite H7. intros. omegaContradiction.
(* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Int.zero) pc' rs' :: s')
                          (transf_fundef fd) (rs'##args) m'); split.
  eapply exec_Icall; eauto. apply sig_preserved. 
  constructor. constructor; auto. apply regset_get_list; auto. auto. 

(* tailcall *) 
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m'1); split.
  eapply exec_Itailcall; eauto. apply sig_preserved.
  rewrite stacksize_preserved; auto.
  constructor. auto.  apply regset_get_list; auto. auto. 

(* builtin *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regset_get_list; auto. 
  exploit external_call_mem_extends; eauto.
  intros [v' [m'1 [A [B [C D]]]]].
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' (rs'#res <- v') m'1); split.
  eapply exec_Ibuiltin; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  econstructor; eauto. apply regset_set; auto.

(* cond *)
  TransfInstr. 
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_lessdef with (rs##args) m; auto. apply regset_get_list; auto.
  constructor; auto. 

(* jumptable *)
  TransfInstr. 
  left. exists (State s' (transf_function f) (Vptr sp0 Int.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  constructor; auto. 

(* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  constructor. auto.
  destruct or; simpl. apply RLD. constructor.
  auto.

(* eliminated return None *)
  assert (or = None) by congruence. subst or. 
  right. split. simpl. omega. split. auto. 
  constructor. auto.
  simpl. constructor.
  eapply Mem.free_left_extends; eauto. 

(* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. auto.
  eapply Mem.free_left_extends; eauto.

(* internal call *)
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0 && eliminate_tailcalls tt); auto. 
  destruct H0 as [EQ1 [EQ2 EQ3]]. 
  left. econstructor; split.
  simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  rewrite EQ2. rewrite EQ3. constructor; auto.
  apply regset_init_regs. auto. 

(* external call *)
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  constructor; auto. 

(* returnstate *)
  inv H2. 
(* synchronous return in both programs *)
  left. econstructor; split. 
  apply exec_return. 
  constructor; auto. apply regset_set; auto. 
(* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length. 
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat. 
  generalize (return_measure_bounds (fn_code f) pc). omega.  
  split. auto. 
  econstructor; eauto.
  rewrite Regmap.gss. auto. 
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H. 
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto. apply Genv.init_mem_transf. auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  reflexivity.
  rewrite <- H3. apply sig_preserved.
  constructor. constructor. constructor. apply Mem.extends_refl. 
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H3. constructor. 
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_opt with (measure := measure); eauto.
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct. 
Qed.

End PRESERVATION.

*)
