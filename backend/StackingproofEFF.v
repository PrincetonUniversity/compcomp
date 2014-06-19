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

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib.
Require Export Axioms.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Op.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import LTL.
Require Import Linear.
Require Import Lineartyping.
Require Import Mach.
Require Import Bounds.
Require Import Conventions.
Require Import Stacklayout.
Require Import Stacking.

Require Import mem_lemmas.
Require Import core_semantics.
Require Import core_semantics_lemmas.
Require Import effect_semantics.
Require Import StructuredInjections.
Require Import reach.
Require Import effect_simulations.
Require Import effect_properties.
Require Import effect_simulations_lemmas.

Require Import Linear_coop.
Require Import Linear_eff.
Require Import Mach_coop.
Require Import BuiltinEffects.
Require Import Mach_eff.
Require Import val_casted.

(** * Properties of frame offsets *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

(** Agreement over initial (Mach) args *)

Fixpoint agree_args_match_aux j (ls: locset) ofs args tys : Prop :=
  match tys with
    | nil => args=nil
    | ty'::tys' => 
      match args with 
        | nil => False
        | a'::args' => 
          match ty' with
            | Tlong => 
              match a' with
                | Vlong n => 
                  ls (S Incoming (ofs+1) Tint) = Vint (Int64.hiword n)
                  /\ ls (S Incoming ofs Tint) = Vint (Int64.loword n)
                  /\ agree_args_match_aux j ls (ofs+2) args' tys'
                | _ => False
              end
            | _ =>  
              val_inject j (ls (S Incoming ofs ty')) a' 
              /\ agree_args_match_aux j ls (ofs+typesize ty') args' tys'
          end
      end
  end.

(*TODO: should go in core/mem_lemmas.v*)
Lemma val_inject_restrict_sub X Y j v1 v2 :
  val_inject (restrict j X) v1 v2 -> 
  (forall b, X b=true -> Y b=true) ->
  val_inject (restrict j Y) v1 v2.
Proof.
inversion 1; subst; auto. intros sub. econstructor; eauto.
apply restrictD_Some in H0. destruct H0 as [H4 H7].
unfold restrict. rewrite (sub _ H7); auto.
Qed.

Lemma agree_args_match_aux_sub j X Y ls ofs args tys :
  (forall b, X b=true -> Y b=true) -> 
  agree_args_match_aux (restrict j X) ls ofs args tys -> 
  agree_args_match_aux (restrict j Y) ls ofs args tys.
Proof.
revert args ofs ls. induction tys. destruct args; auto.
intros ? ? ? sub. destruct args. auto. simpl.
destruct a;
try solve[intros [H2 [H H3]]; split; auto;
          split; auto; eapply val_inject_restrict_sub; eauto
         |intros [H H3]; split; auto;
          eapply val_inject_restrict_sub; eauto]. 
destruct v; auto.
intros [? [? ?]]. split; auto. 
Qed.

Lemma loc_setregs_eq regs rvals ls ofs ty :
  (Locmap.setlist R ## regs rvals ls) (S Incoming ofs ty) 
  = ls (S Incoming ofs ty).
Proof.
apply Locmap.gsetlisto. rewrite Loc.notin_iff.
intros l'. induction regs. inversion 1.
simpl. intros [H|H]. subst l'; auto. destruct l'; auto. apply IHregs; auto.
Qed.

Lemma agree_args_match_aux_setreg j ls ofs args tys reg v :
  agree_args_match_aux j ls ofs args tys -> 
  agree_args_match_aux j (Locmap.set (R reg) v ls) ofs args tys.
Proof.
revert ofs args ls; induction tys; simpl; auto.
destruct args; simpl; auto.
destruct args; simpl; auto.
intros ls. destruct a. 
simpl. intros [H2 H3]. solve[split; auto].
simpl. intros [H2 H3]. solve[split; auto].
simpl. destruct v0; auto. intros [H [H2 H3]]. solve[split; auto].
simpl. intros [H2 H3]. solve[split; auto].
Qed.

Lemma agree_args_match_aux_setregs j ls ofs args tys regs rvals :
  agree_args_match_aux j ls ofs args tys -> 
  agree_args_match_aux j (Locmap.setlist R ## regs rvals ls) ofs args tys.
Proof.
revert ofs args ls; induction tys; simpl; auto.
destruct args; simpl; auto.
destruct args; simpl; auto.
intros ls. destruct a. 
simpl. intros [H2 H3]. split; auto. solve[rewrite loc_setregs_eq; auto].
simpl. intros [H2 H3]. split; auto. solve[rewrite loc_setregs_eq; auto].
simpl. destruct v; auto. intros [H [H2 H3]]. split; auto.
  solve[rewrite loc_setregs_eq; auto]. split; auto.
  solve[rewrite loc_setregs_eq; auto].
simpl. intros [H2 H3]. split; auto. solve[rewrite loc_setregs_eq; auto].
Qed.

Lemma agree_args_match_aux_set_writable j ls ofs args tys slt z ty v :
  slot_writable slt=true -> 
  agree_args_match_aux j ls ofs args tys -> 
  agree_args_match_aux j (Locmap.set (S slt z ty) v ls) ofs args tys.
Proof.
revert ofs args ls; induction tys; simpl; auto.
destruct args; simpl; auto.
destruct args; simpl; auto.
intros ls. destruct a. 
simpl. intros WR [H2 H3]. 
  split; auto. revert WR. destruct slt; try solve[inversion 1].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
simpl. intros WR [H2 H3]. 
  split; auto. revert WR. destruct slt; try solve[inversion 1].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
simpl. destruct v0; auto. intros WR [H [H2 H3]]. 
  split. revert WR. destruct slt; try solve[inversion 1].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  split. revert WR. destruct slt; try solve[inversion 1].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  solve[auto].
simpl. intros WR [H2 H3]. 
  split; auto. revert WR. destruct slt; try solve[inversion 1].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
  rewrite Locmap.gso; auto. simpl. solve[left; intros C; congruence].
Qed.

Lemma undef_regs_get regs ls slt ofs ty :
   LTL.undef_regs regs ls (S slt ofs ty) = ls (S slt ofs ty).
Proof.
revert ls slt ofs ty. induction regs; auto.
Qed.

Lemma agree_args_match_aux_undef_regs j ls ofs args tys regs :
  agree_args_match_aux j ls ofs args tys -> 
  agree_args_match_aux j (LTL.undef_regs regs ls) ofs args tys.
Proof.
revert ofs args ls; induction tys; simpl; auto.
destruct args; simpl; auto.
destruct args; simpl; auto.
intros ls. destruct a. 
simpl. intros [H2 H3]. split; auto. solve[rewrite undef_regs_get; auto].
simpl. intros [H2 H3]. split; auto. solve[rewrite undef_regs_get; auto].
simpl. destruct v; auto. intros [H [H2 H3]]. 
  split. rewrite undef_regs_get; auto. split; auto.
  solve[rewrite undef_regs_get; auto].
simpl. intros [H2 H3]. split; auto. solve[rewrite undef_regs_get; auto].
Qed.

Lemma val_inject_intern_incr mu mu' v1 v2 (WD': SM_wd mu') :
  intern_incr mu mu' -> 
  val_inject (restrict (as_inj mu) (vis mu)) v1 v2 ->
  val_inject (restrict (as_inj mu') (vis mu')) v1 v2.
Proof.
intros H H2. apply val_inject_incr 
  with (f1 := (restrict (as_inj mu) (vis mu))); auto.
generalize H as X; intro. inv H; auto. unfold inject_incr. 
intros ? ? ? H. apply restrictD_Some in H. destruct H.
unfold restrict. cut (vis mu' b=true). intros ->.
assert (inject_incr (as_inj mu) (as_inj mu')).
{ apply intern_incr_as_inj; auto. }
solve[apply H4 in H; auto].
eapply intern_incr_vis in X; eauto.
Qed.

Lemma val_inject_extern_incr mu mu' v1 v2 (WD': SM_wd mu') :
  extern_incr mu mu' -> 
  val_inject (restrict (as_inj mu) (vis mu)) v1 v2 ->
  val_inject (restrict (as_inj mu') (vis mu')) v1 v2.
Proof.
intros H H2. apply val_inject_incr 
  with (f1 := (restrict (as_inj mu) (vis mu))); auto.
generalize H as X; intro. inv H; auto. unfold inject_incr. 
intros ? ? ? H. apply restrictD_Some in H. destruct H.
unfold restrict. cut (vis mu' b=true). intros ->.
assert (inject_incr (as_inj mu) (as_inj mu')).
{ apply extern_incr_as_inj; auto. }
solve[apply H4 in H; auto].
erewrite extern_incr_vis in H3; eauto.
Qed.

Lemma agree_args_match_aux_intern_incr mu mu' ls ofs args tys (WD' : SM_wd mu') :
  intern_incr mu mu' -> 
  agree_args_match_aux (restrict (as_inj mu) (vis mu)) ls ofs args tys ->   
  agree_args_match_aux (restrict (as_inj mu') (vis mu')) ls ofs args tys.
Proof.
intros X; revert ofs args ls; induction tys.
destruct args; simpl; auto.
destruct args; simpl; auto.
intros ls. destruct a. 
simpl. intros [H2 H3]. split; auto.
  revert H2. solve[apply val_inject_intern_incr; auto].
simpl. intros [H2 H3]. split; auto.
  revert H2. solve[apply val_inject_intern_incr; auto].
simpl. destruct v; auto. intros [H [H2 H3]]. solve[split; auto].
simpl. intros [H2 H3]. split; auto.
  revert H2. solve[apply val_inject_intern_incr; auto].
Qed.

Lemma agree_args_match_aux_extern_incr mu mu' ls ofs args tys (WD' : SM_wd mu') :
  extern_incr mu mu' -> 
  agree_args_match_aux (restrict (as_inj mu) (vis mu)) ls ofs args tys ->   
  agree_args_match_aux (restrict (as_inj mu') (vis mu')) ls ofs args tys.
Proof.
intros X; revert ofs args ls; induction tys.
destruct args; simpl; auto.
destruct args; simpl; auto.
intros ls. destruct a. 
simpl. intros [H2 H3]. split; auto.
  revert H2. solve[apply val_inject_extern_incr; auto].
simpl. intros [H2 H3]. split; auto.
  revert H2. solve[apply val_inject_extern_incr; auto].
simpl. destruct v; auto. intros [H [H2 H3]]. solve[split; auto].
simpl. intros [H2 H3]. split; auto.
  revert H2. solve[apply val_inject_extern_incr; auto].
Qed.

Fixpoint agree_args_contains_aux m' sp' ofs args tys : Prop :=
  let vsp := Vptr sp' Int.zero in
  match tys with
    | nil => args=nil
    | ty'::tys' => 
      match args with 
        | nil => False
        | a'::args' => 
          match ty' with
            | Tlong => 
              match a' with
                | Vlong n => 
                  load_stack m' vsp Tint (Int.repr (fe_ofs_arg + 4*(ofs+1)))
                  = Some (Vint (Int64.hiword n))
                  /\ load_stack m' vsp Tint (Int.repr (fe_ofs_arg + 4*ofs))
                     = Some (Vint (Int64.loword n))
                  /\ agree_args_contains_aux m' sp' (ofs+2) args' tys'
                | _ => False
              end
            | _ =>  
              load_stack m' vsp ty' (Int.repr (fe_ofs_arg + 4*ofs)) = Some a' 
              /\ agree_args_contains_aux m' sp' (ofs+typesize ty') args' tys'
          end
      end
  end.

Lemma agree_args_contains_aux_invariant:
  forall tys m sp ofs args m',
  agree_args_contains_aux m sp ofs args tys -> 
  Mem.unchanged_on (fun b ofs => b=sp) m m' ->
  agree_args_contains_aux m' sp ofs args tys.
Proof.
induction tys. destruct args; simpl; auto.
intros m'; destruct args; simpl; auto. destruct a.
generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z. 
intros z [H H2] [H3 H4]. split; eauto. 
unfold load_stack, Mem.loadv in H3|-*. 
revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z)); 
  try solve[inversion 1].
simpl; intros ? ?; inversion 1; subst.
eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z. 
intros z [H H2] [H3 H4]. split; eauto. 
unfold load_stack, Mem.loadv in H3|-*. 
revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z)); 
  try solve[inversion 1].
simpl; intros ? ?; inversion 1; subst.
eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z. 
generalize
     (Int.repr
        match ofs + 1 with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z1. 
destruct v; try inversion 3.
intros z1 z [H H2] [H3 [H4 H5]]. split; eauto. 
unfold load_stack, Mem.loadv in H3|-*. 
revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z)); 
  try solve[inversion 1].
simpl; intros ? ?; inversion 1; subst.
eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
split. eapply Mem.load_unchanged_on; eauto. intros. solve[simpl; auto].
solve[eapply IHtys; eauto]. 
generalize
     (Int.repr
        match ofs with
        | 0 => 0
        | Z.pos y' => Z.pos y'~0~0
        | Z.neg y' => Z.neg y'~0~0
        end) as z. 
intros z [H H2] [H3 H4]. split; eauto. 
unfold load_stack, Mem.loadv in H3|-*. 
revert H3; case_eq (Val.add (Vptr sp Int.zero) (Vint z)); 
  try solve[inversion 1].
simpl; intros ? ?; inversion 1; subst.
eapply Mem.load_unchanged_on. eapply H0. intros. solve[simpl; auto].
Qed.

(*Fixpoint agree_args_contains_aux m' sp' ofs args tys : Prop :=
  match args,tys with
    | nil,nil => True
    | a::args',ty::tys' => 
        Mem.load (chunk_of_type ty) m' sp' (fe_ofs_arg + 4*ofs) = Some a
        /\ agree_args_contains_aux m' sp' (ofs+1) args' tys'
    | _,_ => False
  end.*)

Fixpoint last_frame (stack: list Linear.stackframe) :=
  match stack with
    | nil => nil
    | frm :: nil => frm :: nil
    | frm :: stack' => last_frame stack'
  end.

Lemma last_frame_cons_nonnil c s : ~last_frame (c::s) = nil.
Proof. 
simpl. induction s. intros; congruence. 
intros C. destruct s. inv C. apply IHs; auto.
Qed.

(* agree_args. sp' is a pointer to the dummy stack frame initialized 
   at program startup. *)

Record agree_args (f: Linear.fundef) 
                  (mu: SM_Injection) (args: list val) (tys: list typ)
                  (stack: list Linear.stackframe)
                  (ls: locset) (m': mem) (sp': block) : Prop :=
  mk_agree_args {

    (** [call_regs' ls] is well-typed. *)
    agree_args_wt: wt_locset (call_regs' ls);
   
    (** [tys] match the signature of the initial Linear function. *)
    agree_args_sig_match: sig_args (Linear.funsig f) = tys;

    (** The last stack frame contains the initial function context. *)
    agree_args_frame_match: 
      match last_frame stack with
        | nil => True
        | Linear.Stackframe f1 sp1 ls1 c1 :: nil => 
            f = Internal f1 \/ tailcall_possible (Linear.fn_sig f1)              
        | _ :: _ => True
      end;

    (** The Linear initial arguments [args0] inject to the Mach
        initial arguments [args]. *)
    agree_args_inj: 
      exists args0,
      Forall2 (val_inject (restrict (as_inj mu) (vis mu))) args0 args;

    (** Values in incoming stack slots (on the Linear side) match 
        the initial arguments args. *)
    agree_args_match: 
      agree_args_match_aux (restrict (as_inj mu) (vis mu)) ls 0 args tys;

    (** Values loaded from the Mach stack frame at pointer sp match 
        the initial arguments args. Arguments are pushed RTL, 
        which means argument 0 in args is at offset 0. *)
    agree_args_contains: 
      agree_args_contains_aux m' sp' 0 args tys;

    (** No source block maps to the dummy stack pointer sp'. *)
    agree_sp_fresh:
      forall b0 z, as_inj mu b0 = Some (sp',z) -> False;

    (** sp' is local *)
    agree_sp_local: locBlocksTgt mu sp'=true
  }.

Section PRESERVATION.

(*NEW*) Variable hf : I64Helpers.helper_functions.
Variable return_address_offset: Mach.function -> Mach.code -> int -> Prop.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Let step := Mach.step return_address_offset.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
  intros; discriminate.
Qed.

Lemma transf_function_well_typed:
  wt_function f = true.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb. auto. intros; discriminate.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Int.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. omega.
  intros; discriminate.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Zmax1.
Qed.  

(** A frame index is valid if it lies within the resource bounds
  of the current function. *)

Definition index_valid (idx: frame_index) :=
  match idx with
  | FI_link => True
  | FI_retaddr => True
  | FI_local x ty => ty <> Tlong /\ 0 <= x /\ x + typesize ty <= b.(bound_local)
  | FI_arg x ty => ty <> Tlong /\ 0 <= x /\ x + typesize ty <= b.(bound_outgoing)
  | FI_saved_int x => 0 <= x < b.(bound_int_callee_save)
  | FI_saved_float x => 0 <= x < b.(bound_float_callee_save)
  end.

Definition type_of_index (idx: frame_index) :=
  match idx with
  | FI_link => Tint
  | FI_retaddr => Tint
  | FI_local x ty => ty
  | FI_arg x ty => ty
  | FI_saved_int x => Tint
  | FI_saved_float x => Tfloat
  end.

(** Non-overlap between the memory areas corresponding to two
  frame indices. *)

Definition index_diff (idx1 idx2: frame_index) : Prop :=
  match idx1, idx2 with
  | FI_link, FI_link => False
  | FI_retaddr, FI_retaddr => False
  | FI_local x1 ty1, FI_local x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_arg x1 ty1, FI_arg x2 ty2 =>
      x1 + typesize ty1 <= x2 \/ x2 + typesize ty2 <= x1
  | FI_saved_int x1, FI_saved_int x2 => x1 <> x2
  | FI_saved_float x1, FI_saved_float x2 => x1 <> x2
  | _, _ => True
  end.

Lemma index_diff_sym:
  forall idx1 idx2, index_diff idx1 idx2 -> index_diff idx2 idx1.
Proof.
  unfold index_diff; intros. 
  destruct idx1; destruct idx2; intuition.
Qed.

Ltac AddPosProps :=
  generalize (bound_local_pos b); intro;
  generalize (bound_int_callee_save_pos b); intro;
  generalize (bound_float_callee_save_pos b); intro;
  generalize (bound_outgoing_pos b); intro;
  generalize (bound_stack_data_pos b); intro.

Lemma size_pos: 0 <= fe.(fe_size).
Proof.
  generalize (frame_env_separated b). intuition.
  AddPosProps.
  unfold fe. omega.
Qed.

Opaque function_bounds.

Ltac InvIndexValid :=
  match goal with
  | [ H: ?ty <> Tlong /\ _ |- _ ] =>
       destruct H; generalize (typesize_pos ty) (typesize_typesize ty); intros
  end.

Lemma offset_of_index_disj:
  forall idx1 idx2,
  index_valid idx1 -> index_valid idx2 ->
  index_diff idx1 idx2 ->
  offset_of_index fe idx1 + AST.typesize (type_of_index idx1) <= offset_of_index fe idx2 \/
  offset_of_index fe idx2 + AST.typesize (type_of_index idx2) <= offset_of_index fe idx1.
Proof.
  intros idx1 idx2 V1 V2 DIFF.
  generalize (frame_env_separated b). intuition. fold fe in H.
  AddPosProps.
  destruct idx1; destruct idx2;
  simpl in V1; simpl in V2; repeat InvIndexValid; simpl in DIFF;
  unfold offset_of_index, type_of_index;
  change (AST.typesize Tint) with 4;
  change (AST.typesize Tfloat) with 8;
  omega.
Qed.

Lemma offset_of_index_disj_stack_data_1:
  forall idx,
  index_valid idx ->
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_stack_data)
  \/ fe.(fe_stack_data) + b.(bound_stack_data) <= offset_of_index fe idx.
Proof.
  intros idx V.
  generalize (frame_env_separated b). intuition. fold fe in H.
  AddPosProps.
  destruct idx;
  simpl in V; repeat InvIndexValid;
  unfold offset_of_index, type_of_index;
  change (AST.typesize Tint) with 4;
  change (AST.typesize Tfloat) with 8;
  omega.
Qed.

Lemma offset_of_index_disj_stack_data_2:
  forall idx,
  index_valid idx ->
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_stack_data)
  \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= offset_of_index fe idx.
Proof.
  intros. 
  exploit offset_of_index_disj_stack_data_1; eauto.
  generalize bound_stack_data_stacksize. 
  omega.
Qed.

(** Alignment properties *)

Remark aligned_4_4x: forall x, (4 | 4 * x).
Proof. intro. exists x; ring. Qed.

Remark aligned_4_8x: forall x, (4 | 8 * x).
Proof. intro. exists (x * 2); ring. Qed.

Remark aligned_8_4:
  forall x, (8 | x) -> (4 | x).
Proof. intros. apply Zdivides_trans with 8; auto. exists 2; auto. Qed.

Hint Resolve Zdivide_0 Zdivide_refl Zdivide_plus_r 
             aligned_4_4x aligned_4_8x aligned_8_4: align_4.
Hint Extern 4 (?X | ?Y) => (exists (Y/X); reflexivity) : align_4.

Lemma offset_of_index_aligned:
  forall idx, (4 | offset_of_index fe idx).
Proof.
  intros.
  generalize (frame_env_aligned b). intuition. fold fe in H. intuition.
  destruct idx; try (destruct t);
  unfold offset_of_index, type_of_index, AST.typesize;
  auto with align_4.
Qed.

Lemma fe_stack_data_aligned:
  (8 | fe_stack_data fe).
Proof.
  intros.
  generalize (frame_env_aligned b). intuition. fold fe in H. intuition.
Qed.

(** The following lemmas give sufficient conditions for indices
  of various kinds to be valid. *)

Lemma index_local_valid:
  forall ofs ty,
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  index_valid (FI_local ofs ty).
Proof.
  unfold slot_within_bounds, slot_valid, index_valid; intros. 
  InvBooleans. 
  split. destruct ty; congruence. auto.
Qed.

Lemma index_arg_valid:
  forall ofs ty,
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  index_valid (FI_arg ofs ty).
Proof.
  unfold slot_within_bounds, slot_valid, index_valid; intros. 
  InvBooleans. 
  split. destruct ty; congruence. auto.
Qed.

Lemma index_saved_int_valid:
  forall r,
  In r int_callee_save_regs ->
  index_int_callee_save r < b.(bound_int_callee_save) ->
  index_valid (FI_saved_int (index_int_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_int_callee_save_pos; auto. 
  auto.
Qed.

Lemma index_saved_float_valid:
  forall r,
  In r float_callee_save_regs ->
  index_float_callee_save r < b.(bound_float_callee_save) ->
  index_valid (FI_saved_float (index_float_callee_save r)).
Proof.
  intros. red. split. 
  apply Zge_le. apply index_float_callee_save_pos; auto. 
  auto.
Qed.

Hint Resolve index_local_valid index_arg_valid
             index_saved_int_valid index_saved_float_valid: stacking.

(** The offset of a valid index lies within the bounds of the frame. *)

Lemma offset_of_index_valid:
  forall idx,
  index_valid idx ->
  0 <= offset_of_index fe idx /\
  offset_of_index fe idx + AST.typesize (type_of_index idx) <= fe.(fe_size).
Proof.
  intros idx V.
  generalize (frame_env_separated b). intros [A B]. fold fe in A. fold fe in B.
  AddPosProps.
  destruct idx; simpl in V; repeat InvIndexValid;
  unfold offset_of_index, type_of_index;
  change (AST.typesize Tint) with 4;
  change (AST.typesize Tfloat) with 8;
  omega.
Qed.

(** The image of the Linear stack data block lies within the bounds of the frame. *)

Lemma stack_data_offset_valid:
  0 <= fe.(fe_stack_data) /\ fe.(fe_stack_data) + b.(bound_stack_data) <= fe.(fe_size).
Proof.
  generalize (frame_env_separated b). intros [A B]. fold fe in A. fold fe in B.
  AddPosProps.
  omega.
Qed.

(** Offsets for valid index are representable as signed machine integers
  without loss of precision. *)

Lemma offset_of_index_no_overflow:
  forall idx,
  index_valid idx ->
  Int.unsigned (Int.repr (offset_of_index fe idx)) = offset_of_index fe idx.
Proof.
  intros.
  generalize (offset_of_index_valid idx H). intros [A B].
  apply Int.unsigned_repr.
  generalize (AST.typesize_pos (type_of_index idx)).
  generalize size_no_overflow. 
  omega.
Qed.

(** Likewise, for offsets within the Linear stack slot, after shifting. *)

Lemma shifted_stack_offset_no_overflow:
  forall ofs,
  0 <= Int.unsigned ofs < Linear.fn_stacksize f ->
  Int.unsigned (Int.add ofs (Int.repr fe.(fe_stack_data))) 
  = Int.unsigned ofs + fe.(fe_stack_data).
Proof.
  intros. unfold Int.add.
  generalize size_no_overflow stack_data_offset_valid bound_stack_data_stacksize; intros.
  AddPosProps.
  replace (Int.unsigned (Int.repr (fe_stack_data fe))) with (fe_stack_data fe).
  apply Int.unsigned_repr. omega. 
  symmetry. apply Int.unsigned_repr. omega.
Qed.

(** * Contents of frame slots *)

Inductive index_contains (m: mem) (sp: block) (idx: frame_index) (v: val) : Prop :=
  | index_contains_intro:
      index_valid idx ->
      Mem.load (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) = Some v ->
      index_contains m sp idx v.

Lemma index_contains_load_stack:
  forall m sp idx v,
  index_contains m sp idx v ->
  load_stack m (Vptr sp Int.zero) (type_of_index idx)
              (Int.repr (offset_of_index fe idx)) = Some v.
Proof.
  intros. inv H. 
  unfold load_stack, Mem.loadv, Val.add. rewrite Int.add_commut. rewrite Int.add_zero.
  rewrite offset_of_index_no_overflow; auto.
Qed.

(** Good variable properties for [index_contains] *)

Lemma gss_index_contains_base:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  exists v',
     index_contains m' sp idx v'
  /\ decode_encode_val v (chunk_of_type (type_of_index idx)) (chunk_of_type (type_of_index idx)) v'.
Proof.
  intros. 
  exploit Mem.load_store_similar. eauto. reflexivity. omega. 
  intros [v' [A B]].
  exists v'; split; auto. constructor; auto.
Qed.

Lemma gss_index_contains:
  forall idx m m' sp v,
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  Val.has_type v (type_of_index idx) ->
  index_contains m' sp idx v.
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v' [A B]].
  assert (v' = v).
    destruct v; destruct (type_of_index idx); simpl in *;
    try contradiction; auto. rewrite Floats.Float.singleoffloat_of_single in B; auto. 
  subst v'. auto.
Qed.

Lemma gso_index_contains:
  forall idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains m sp idx' v' ->
  index_diff idx idx' ->
  index_contains m' sp idx' v'.
Proof.
  intros. inv H1. constructor; auto. 
  rewrite <- H4. eapply Mem.load_store_other; eauto.
  right. repeat rewrite size_type_chunk. 
  apply offset_of_index_disj; auto. apply index_diff_sym; auto.
Qed.

Lemma store_other_index_contains:
  forall chunk m blk ofs v' m' sp idx v,
  Mem.store chunk m blk ofs v' = Some m' ->
  blk <> sp \/
    (fe.(fe_stack_data) <= ofs /\ ofs + size_chunk chunk <= fe.(fe_stack_data) + f.(Linear.fn_stacksize)) ->
  index_contains m sp idx v ->
  index_contains m' sp idx v.
Proof.
  intros. inv H1. constructor; auto. rewrite <- H3. 
  eapply Mem.load_store_other; eauto. 
  destruct H0. auto. right. 
  exploit offset_of_index_disj_stack_data_2; eauto. intros.
  rewrite size_type_chunk.
  omega.
Qed.

Definition frame_perm_freeable (m: mem) (sp: block): Prop :=
  forall ofs,
  0 <= ofs < fe.(fe_size) ->
  ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
  Mem.perm m sp ofs Cur Freeable.

Lemma offset_of_index_perm:
  forall m sp idx,
  index_valid idx ->
  frame_perm_freeable m sp ->
  Mem.range_perm m sp (offset_of_index fe idx) (offset_of_index fe idx + AST.typesize (type_of_index idx)) Cur Freeable.
Proof.
  intros.
  exploit offset_of_index_valid; eauto. intros [A B].
  exploit offset_of_index_disj_stack_data_2; eauto. intros.
  red; intros. apply H0. omega. omega.
Qed.

Lemma store_index_succeeds:
  forall m sp idx v,
  index_valid idx ->
  frame_perm_freeable m sp ->
  exists m',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m'.
Proof.
  intros.
  destruct (Mem.valid_access_store m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx) v) as [m' ST].
  constructor.
  rewrite size_type_chunk. 
  apply Mem.range_perm_implies with Freeable; auto with mem.
  apply offset_of_index_perm; auto.
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4.
  apply offset_of_index_aligned; auto.
  assert (type_of_index idx <> Tlong).
    destruct idx; simpl in *; tauto || congruence.
  destruct (type_of_index idx); reflexivity || congruence. 
  exists m'; auto.
Qed.

Lemma store_stack_succeeds:
  forall m sp idx v m',
  index_valid idx ->
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  store_stack m (Vptr sp Int.zero) (type_of_index idx) (Int.repr (offset_of_index fe idx)) v = Some m'.
Proof.
  intros. unfold store_stack, Mem.storev, Val.add.
  rewrite Int.add_commut. rewrite Int.add_zero.
  rewrite offset_of_index_no_overflow; auto.
Qed.

(** A variant of [index_contains], up to a memory injection. *)

Definition index_contains_inj (j: meminj) (m: mem) (sp: block) (idx: frame_index) (v: val) : Prop :=
  exists v', index_contains m sp idx v' /\ val_inject j v v'.

Lemma gss_index_contains_inj:
  forall j idx m m' sp v v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v' = Some m' ->
  index_valid idx ->
  Val.has_type v (type_of_index idx) ->
  val_inject j v v' ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v'' [A B]].
  exists v''; split; auto.
  inv H2; destruct (type_of_index idx); simpl in *; try contradiction; subst; auto.
  rewrite Floats.Float.singleoffloat_of_single; auto. 
  econstructor; eauto.
Qed.

Lemma gss_index_contains_inj':
  forall j idx m m' sp v v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v' = Some m' ->
  index_valid idx ->
  val_inject j v v' ->
  index_contains_inj j m' sp idx (Val.load_result (chunk_of_type (type_of_index idx)) v).
Proof.
  intros. exploit gss_index_contains_base; eauto. intros [v'' [A B]].
  exists v''; split; auto.
  inv H1; destruct (type_of_index idx); simpl in *; try contradiction; subst; auto. 
  econstructor; eauto.
Qed.

Lemma gso_index_contains_inj:
  forall j idx m m' sp v idx' v',
  Mem.store (chunk_of_type (type_of_index idx)) m sp (offset_of_index fe idx) v = Some m' ->
  index_valid idx ->
  index_contains_inj j m sp idx' v' ->
  index_diff idx idx' ->
  index_contains_inj j m' sp idx' v'.
Proof.
  intros. destruct H1 as [v'' [A B]]. exists v''; split; auto.
  eapply gso_index_contains; eauto.
Qed.

Lemma store_other_index_contains_inj:
  forall j chunk m b ofs v' m' sp idx v,
  Mem.store chunk m b ofs v' = Some m' ->
  b <> sp \/
    (fe.(fe_stack_data) <= ofs /\ ofs + size_chunk chunk <= fe.(fe_stack_data) + f.(Linear.fn_stacksize)) ->
  index_contains_inj j m sp idx v ->
  index_contains_inj j m' sp idx v.
Proof.
  intros. destruct H1 as [v'' [A B]]. exists v''; split; auto.
  eapply store_other_index_contains; eauto.
Qed.

Lemma index_contains_inj_incr:
  forall j m sp idx v j',
  index_contains_inj j m sp idx v ->
  inject_incr j j' ->
  index_contains_inj j' m sp idx v.
Proof.
  intros. destruct H as [v'' [A B]]. exists v''; split; auto. eauto. 
Qed.

Lemma index_contains_inj_undef:
  forall j m sp idx,
  index_valid idx ->
  frame_perm_freeable m sp ->
  index_contains_inj j m sp idx Vundef.
Proof.
  intros. 
  exploit (Mem.valid_access_load m (chunk_of_type (type_of_index idx)) sp (offset_of_index fe idx)).
  constructor. 
  rewrite size_type_chunk.
  apply Mem.range_perm_implies with Freeable; auto with mem.
  apply offset_of_index_perm; auto. 
  replace (align_chunk (chunk_of_type (type_of_index idx))) with 4. 
  apply offset_of_index_aligned.
  assert (type_of_index idx <> Tlong).
    destruct idx; simpl in *; tauto || congruence.
  destruct (type_of_index idx); reflexivity || congruence. 
  intros [v C]. 
  exists v; split; auto. constructor; auto. 
Qed.

Hint Resolve store_other_index_contains_inj index_contains_inj_incr: stacking.

(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, val_inject j (ls (R r)) (rs r).

(** Agreement over data stored in memory *)

Record agree_frame (j: meminj) (ls ls0: locset)
                   (m: mem) (sp: block)
                   (m': mem) (sp': block)
                   (parent retaddr: val) : Prop :=
  mk_agree_frame {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Local and outgoing stack slots (on the Linear side) have
        the same values as the one loaded from the current Mach frame 
        at the corresponding offsets. *)
    agree_locals:
      forall ofs ty, 
      slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
      index_contains_inj j m' sp' (FI_local ofs ty) (ls (S Local ofs ty));
    agree_outgoing:
      forall ofs ty, 
      slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
      index_contains_inj j m' sp' (FI_arg ofs ty) (ls (S Outgoing ofs ty));

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty, 
       In (S Incoming ofs ty) (loc_parameters f.(Linear.fn_sig)) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty);

    (** The back link and return address slots of the Mach frame contain
        the [parent] and [retaddr] values, respectively. *)
    agree_link:
      index_contains m' sp' FI_link parent;
    agree_retaddr:
      index_contains m' sp' FI_retaddr retaddr;

    (** The areas of the frame reserved for saving used callee-save
        registers always contain the values that those registers had
        in the caller. *)
    agree_saved_int:
      forall r,
      In r int_callee_save_regs ->
      index_int_callee_save r < b.(bound_int_callee_save) ->
      index_contains_inj j m' sp' (FI_saved_int (index_int_callee_save r)) (ls0 (R r));
    agree_saved_float:
      forall r,
      In r float_callee_save_regs ->
      index_float_callee_save r < b.(bound_float_callee_save) ->
      index_contains_inj j m' sp' (FI_saved_float (index_float_callee_save r)) (ls0 (R r));

    (** Mapping between the Linear stack pointer and the Mach stack pointer *)
    agree_inj:
      j sp = Some(sp', fe.(fe_stack_data));
    agree_inj_unique:
      forall b delta, j b = Some(sp', delta) -> b = sp /\ delta = fe.(fe_stack_data);

    (** The Linear and Mach stack pointers are valid *)
    agree_valid_linear:
      Mem.valid_block m sp;
    agree_valid_mach:
      Mem.valid_block m' sp';

    (** Bounds of the Linear stack data block *)
    agree_bounds:
      forall ofs p, Mem.perm m sp ofs Max p -> 0 <= ofs < f.(Linear.fn_stacksize);

    (** Permissions on the frame part of the Mach stack block *)
    agree_perm:
      frame_perm_freeable m' sp';

    (** Current locset is well-typed *)
    agree_wt_ls:
      wt_locset ls
  }.

Hint Resolve agree_unused_reg agree_locals agree_outgoing agree_incoming
             agree_link agree_retaddr agree_saved_int agree_saved_float
             agree_valid_linear agree_valid_mach agree_perm
             agree_wt_ls: stacking.

(** Auxiliary predicate used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => ~In r destroyed_at_call
  | S _ _ _ => True
  end ->
  ls l = ls0 l.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> val_inject j (ls (R r)) (rs r).
Proof.
  intros. auto. 
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> val_list_inject j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor. eauto with stacking. auto. 
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  val_inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros. 
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0. 
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_regs:
  forall j rl vl vl' ls rs,
  agree_regs j ls rs ->
  val_list_inject j vl vl' ->
  agree_regs j (Locmap.setlist (map R rl) vl ls) (set_regs rl vl' rs).
Proof.
  induction rl; simpl; intros. 
  auto.
  inv H0. auto.
  apply IHrl; auto. apply agree_regs_set_reg; auto. 
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]]. 
  rewrite A. constructor. 
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto. 
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) rs.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

(** ** Properties of [agree_frame] *)

(** Preservation under assignment of machine register. *)

Lemma agree_frame_set_reg:
  forall j ls ls0 m sp m' sp' parent ra r v,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  mreg_within_bounds b r ->
   Val.has_type v (Loc.type (R r)) ->
  agree_frame j (Locmap.set (R r) v ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. intuition congruence.
  apply wt_setreg; auto.
Qed.

Lemma agree_frame_set_regs:
  forall j ls0 m sp m' sp' parent ra rl vl ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  (forall r, In r rl -> mreg_within_bounds b r) ->
  Val.has_type_list vl (map Loc.type (map R rl)) ->
  agree_frame j (Locmap.setlist (map R rl) vl ls) ls0 m sp m' sp' parent ra.
Proof.
  induction rl; destruct vl; simpl; intros; intuition.
  apply IHrl; auto. 
  eapply agree_frame_set_reg; eauto. 
Qed.

Lemma agree_frame_undef_regs:
  forall j ls0 m sp m' sp' parent ra regs ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_frame j (LTL.undef_regs regs ls) ls0 m sp m' sp' parent ra.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_frame_set_reg; auto. red; auto.
Qed.

Lemma caller_save_reg_within_bounds:
  forall r,
  In r destroyed_at_call -> mreg_within_bounds b r.
Proof.
  intros. red.
  destruct (zlt (index_int_callee_save r) 0).
  destruct (zlt (index_float_callee_save r) 0).
  generalize (bound_int_callee_save_pos b) (bound_float_callee_save_pos b); omega.
  exfalso. eapply float_callee_save_not_destroyed; eauto. eapply index_float_callee_save_pos2; eauto.
  exfalso. eapply int_callee_save_not_destroyed; eauto. eapply index_int_callee_save_pos2; eauto.
Qed.

Lemma agree_frame_undef_locs:
  forall j ls0 m sp m' sp' parent ra regs ls,
  agree_frame j ls ls0 m sp m' sp' parent ra ->
  incl regs destroyed_at_call ->
  agree_frame j (LTL.undef_regs regs ls) ls0 m sp m' sp' parent ra.
Proof.
  intros. eapply agree_frame_undef_regs; eauto. 
  intros. apply caller_save_reg_within_bounds. auto. 
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_frame_set_local:
  forall j ls ls0 m sp m' sp' parent retaddr ofs ty v v' m'',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  val_inject j v v' ->
  Mem.store (chunk_of_type ty) m' sp' (offset_of_index fe (FI_local ofs ty)) v' = Some m'' ->
  agree_frame j (Locmap.set (S Local ofs ty) v ls) ls0 m sp m'' sp' parent retaddr.
Proof.
  intros. inv H. 
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_local ofs ty))) in H3.
  constructor; auto; intros.
(* local *)
  unfold Locmap.set.
  destruct (Loc.eq (S Local ofs ty) (S Local ofs0 ty0)).
  inv e. eapply gss_index_contains_inj'; eauto with stacking.
  destruct (Loc.diff_dec (S Local ofs ty) (S Local ofs0 ty0)).
  eapply gso_index_contains_inj. eauto. eauto with stacking. eauto. 
  simpl. simpl in d. intuition.
  apply index_contains_inj_undef. auto with stacking.
  red; intros. eapply Mem.perm_store_1; eauto.
(* outgoing *)
  rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking.
  red; auto. red; left; congruence. 
(* parent *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* retaddr *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* int callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto. 
(* float callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
(* valid *)
  eauto with mem.
(* perm *)
  red; intros. eapply Mem.perm_store_1; eauto.
(* wt *)
  apply wt_setstack; auto. 
Qed.

(** Preservation by assignment to outgoing slot *)

Lemma agree_frame_set_outgoing:
  forall j ls ls0 m sp m' sp' parent retaddr ofs ty v v' m'',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  val_inject j v v' ->
  Mem.store (chunk_of_type ty) m' sp' (offset_of_index fe (FI_arg ofs ty)) v' = Some m'' ->
  agree_frame j (Locmap.set (S Outgoing ofs ty) v ls) ls0 m sp m'' sp' parent retaddr.
Proof.
  intros. inv H. 
  change (chunk_of_type ty) with (chunk_of_type (type_of_index (FI_arg ofs ty))) in H3.
  constructor; auto; intros.
(* local *)
  rewrite Locmap.gso. eapply gso_index_contains_inj; eauto with stacking. red; auto.
  red; left; congruence.
(* outgoing *)
  unfold Locmap.set. destruct (Loc.eq (S Outgoing ofs ty) (S Outgoing ofs0 ty0)).
  inv e. eapply gss_index_contains_inj'; eauto with stacking.
  destruct (Loc.diff_dec (S Outgoing ofs ty) (S Outgoing ofs0 ty0)).
  eapply gso_index_contains_inj; eauto with stacking.
  red. red in d. intuition. 
  apply index_contains_inj_undef. auto with stacking.
  red; intros. eapply Mem.perm_store_1; eauto.
(* parent *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* retaddr *)
  eapply gso_index_contains; eauto with stacking. red; auto.
(* int callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto. 
(* float callee save *)
  eapply gso_index_contains_inj; eauto with stacking. simpl; auto.
(* valid *)
  eauto with mem stacking.
(* perm *)
  red; intros. eapply Mem.perm_store_1; eauto.
(* wt *)
  apply wt_setstack; auto. 
Qed.

(** General invariance property with respect to memory changes. *)

Lemma agree_frame_invariant:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  (Mem.valid_block m sp -> Mem.valid_block m1 sp) ->
  (forall ofs p, Mem.perm m1 sp ofs Max p -> Mem.perm m sp ofs Max p) ->
  (Mem.valid_block m' sp' -> Mem.valid_block m1' sp') ->
  (forall chunk ofs v,
     ofs + size_chunk chunk <= fe.(fe_stack_data) \/
     fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
     Mem.load chunk m' sp' ofs = Some v ->
     Mem.load chunk m1' sp' ofs = Some v) ->
  (forall ofs k p,
     ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
     Mem.perm m' sp' ofs k p -> Mem.perm m1' sp' ofs k p) ->
  agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  intros.
  assert (IC: forall idx v,
              index_contains m' sp' idx v -> index_contains m1' sp' idx v).
    intros. inv H5.
    exploit offset_of_index_disj_stack_data_2; eauto. intros. 
    constructor; eauto. apply H3; auto. rewrite size_type_chunk; auto.
  assert (ICI: forall idx v,
              index_contains_inj j m' sp' idx v -> index_contains_inj j m1' sp' idx v).
    intros. destruct H5 as [v' [A B]]. exists v'; split; auto. 
  inv H; constructor; auto; intros.
  eauto.
  red; intros. apply H4; auto.
Qed.

Lemma agree_args_match_contain j ls z args0 args tys m' sp' ofs ty :
  agree_args_match_aux j ls z args tys -> 
  agree_args_contains_aux m' sp' z args tys -> 
  In (S Outgoing ofs ty) (loc_arguments_rec tys z) -> 
  Forall2 (val_inject j) args0 args -> 
  exists v, 
  load_stack m' (Vptr sp' Int.zero) ty (Int.repr (4*ofs)) = Some v
  /\ val_inject j (ls (S Incoming ofs ty)) v.
Proof.
revert args0 args z. induction tys. 
destruct args; simpl; try solve[intros; contradiction].
destruct args. intros z H H2. simpl in H; contradiction.
intros z H H2 IN VINJ. simpl in H, H2. destruct a.
{ destruct H as [H3 H4]. destruct H2 as [H2 H5]. simpl in IN. destruct IN. 
  - inversion H. subst ofs ty. exists v. split; auto.
  - inv VINJ. eapply IHtys; eauto. }
{ destruct H as [H3 H4]. destruct H2 as [H2 H5]. simpl in IN. destruct IN. 
  - inversion H. subst ofs ty. exists v. split; auto.
  - inv VINJ. eapply IHtys; eauto. }
{ destruct v; try inversion H. destruct H2 as [H2 H5]. simpl in IN. destruct IN. 
  - inversion H3. subst ofs ty. destruct H as [X [Y Z]].
    exists (Vint (Int64.hiword i)); split; auto. rewrite H0. constructor. 
  - destruct H3. inversion H3. subst ofs ty. destruct H as [X [Y Z]].
    exists (Vint (Int64.loword i)); split; auto. destruct H5; auto.
    destruct H1 as [H1 _]; rewrite H1; constructor.
    destruct H2. destruct H5. destruct H as [? [? ?]]. destruct H1. inv VINJ.
    eapply IHtys; eauto. }
{ destruct H as [H3 H4]. destruct H2 as [H2 H5]. simpl in IN. destruct IN. 
  - inversion H. subst ofs ty. exists v. split; auto.
  - inv VINJ. eapply IHtys; eauto. }
Qed.

Lemma agree_args_invariant:
  forall f mu args tys stack ls m' sp' m1' (WD : SM_wd mu),
  agree_args f mu args tys stack ls m' sp' ->
  Mem.unchanged_on (fun b ofs => b=sp') m' m1' ->
  agree_args f mu args tys stack ls m1' sp'.
Proof.
intros. inv H. constructor; auto.
eapply agree_args_contains_aux_invariant; eauto.
Qed.

Lemma agree_args_invariant':
  forall f mu args tys stack ls m m' sp' m1' (WD : SM_wd mu),
  agree_args f mu args tys stack ls m' sp' -> 
  Mem.unchanged_on (local_out_of_reach mu m) m' m1' ->
  agree_args f mu args tys stack ls m1' sp'.
Proof.
intros. eapply agree_args_invariant; eauto.
apply mem_unchanged_on_sub with (Q := local_out_of_reach mu m); auto.
intros b0 ofs Heq; subst b0. split; auto. solve[inv H; auto].
intros b0 z lOf. inv H. apply local_in_all in lOf; auto. exfalso; eauto. 
Qed.

Lemma agree_args_alloc: 
  forall f mu args tys stack ls m sp' m' lo hi b (WD : SM_wd mu),
  agree_args f mu args tys stack ls m sp' -> 
  Mem.alloc m lo hi = (m',b) -> 
  agree_args f mu args tys stack ls m' sp'.
Proof.
intros. apply agree_args_invariant with (m' := m); auto.
apply Mem.alloc_unchanged_on with (P := fun b z => b=sp') in H0; auto.
Qed.

Lemma agree_args_free: 
  forall f mu args tys stack ls m sp' m' b lo hi (WD : SM_wd mu),
  agree_args f mu args tys stack ls m sp' -> 
  b<>sp' -> 
  Mem.free m b lo hi = Some m' -> 
  agree_args f mu args tys stack ls m' sp'.
Proof.
intros. apply agree_args_invariant with (m' := m); auto.
eapply Mem.free_unchanged_on; eauto.
Qed.

Lemma Zlength_pos A : forall l : list A, Zlength l >= 0.
Proof.
intros l.
assert (forall z, z >= 0 -> Zlength_aux z A l >= 0).
{ induction l. simpl. intros; omega. intros. 
  simpl. eapply IHl. omega. }
unfold Zlength. apply H. omega.
Qed.

Lemma Zlength_cons_pos A (a : A) l : Zlength (a::l) > 0.
Proof.
rewrite Zlength_cons.
generalize (Zlength_pos _ l).
omega.
Qed. 

Lemma agree_args_replace_locals f0 mu args tys stack ls m' sp' PS PT :
  agree_args f0 mu args tys stack ls m' sp' ->
  agree_args f0 (replace_locals mu PS PT) args tys stack ls m' sp'.
Proof.
inversion 1; subst.
constructor; auto.
destruct agree_args_inj0 as [x X]. exists x. 
  solve[rewrite replace_locals_vis, replace_locals_as_inj; auto].
solve[rewrite replace_locals_as_inj, replace_locals_vis; auto].
solve[rewrite replace_locals_as_inj; auto].
solve[rewrite replace_locals_locBlocksTgt; auto].
Qed.

(*TODO: put in core/StructuredInjections or somewhere similar*)
Lemma forall_vals_inject_restrictD' j vals1 vals2 X 
      (Inj : Forall2 (val_inject (restrict j X)) vals1 vals2) :
  Forall2 (val_inject j) vals1 vals2 
  /\ (forall b : block, getBlocks vals1 b = true -> X b = true).
Proof. 
intros. induction Inj. constructor.
constructor; trivial. unfold getBlocks. simpl. intros; congruence.
destruct IHInj as [H0 H1]. split. constructor; auto.
  eapply val_inject_restrictD in H. eassumption.
intros b0 GET. rewrite getBlocksD in GET. 
assert (H2: (exists ofs, x=Vptr b0 ofs) \/ getBlocks l b0=true).
{ revert GET; case_eq x; auto. intros b1 i ? H2; subst x. 
  rewrite orb_true_iff in H2. destruct H2; auto. 
  destruct (eq_block b1 b0); try (simpl in H2; congruence). subst.
  left. exists i. auto. }
destruct H2 as [[ofs H2]|H2]. subst x. 
inv H. apply restrictD_Some in H4. destruct H4; auto.
apply H1; auto.
Qed.

Lemma forall_vals_inject_intern_incr mu mu' vals1 vals2 
      (Inj : Forall2 (val_inject (as_inj mu)) vals1 vals2) 
      (Incr : intern_incr mu mu') 
      (WD : SM_wd mu') : 
  Forall2 (val_inject (as_inj mu')) vals1 vals2. 
Proof. 
intros. induction Inj. constructor.
constructor; trivial. apply val_inject_incr with (f1 := as_inj mu); auto.
apply intern_incr_as_inj; auto.
Qed.

Lemma forall_vals_inject_extern_incr mu mu' vals1 vals2 
      (Inj : Forall2 (val_inject (as_inj mu)) vals1 vals2) 
      (Incr : extern_incr mu mu') 
      (WD : SM_wd mu') : 
  Forall2 (val_inject (as_inj mu')) vals1 vals2. 
Proof. 
intros. induction Inj. constructor.
constructor; trivial. apply val_inject_incr with (f1 := as_inj mu); auto.
apply extern_incr_as_inj; auto.
Qed.
(*END TODO*)

Lemma agree_args_replace_externs f0 mu args tys stack ls m' sp' FS FT 
    (HFS: forall b, vis mu b = true -> locBlocksSrc mu b || FS b = true) :
  agree_args f0 mu args tys stack ls m' sp' ->
  agree_args f0 (replace_externs mu FS FT) args tys stack ls m' sp'.
Proof.
inversion 1; subst.
constructor; auto.
destruct agree_args_inj0 as [x X]. exists x. 
  rewrite replace_externs_vis, replace_externs_as_inj; auto.
  apply restrict_forall_vals_inject.
  apply forall_vals_inject_restrictD in X; auto. 
  apply forall_vals_inject_restrictD' in X; auto. destruct X as [_ X].
  intros b0 GET. apply HFS. apply X; auto.
rewrite replace_externs_vis, replace_externs_as_inj. 
  solve[apply agree_args_match_aux_sub with (X := vis mu); auto].
solve[rewrite replace_externs_as_inj; intros ? ? INJ; eauto].
solve[rewrite replace_externs_locBlocksTgt; auto].
Qed.

Lemma agree_args_intern_incr f0 mu mu' args tys stack ls m1 m2 m2' sp' (WD' : SM_wd mu') :
  intern_incr mu mu' ->
  sm_inject_separated mu mu' m1 m2 ->
  agree_args f0 mu args tys stack ls m2' sp' ->
  agree_args f0 mu' args tys stack ls m2' sp'.
Proof.
inversion 1; subst. constructor; auto. intros. 
  inv H3; auto.
  inv H3; auto.
  inv H3; auto.
  inv H3. destruct agree_args_inj0 as [args0 INJ]. exists args0. 
    apply restrict_forall_vals_inject.
    apply forall_vals_inject_restrictD in INJ; auto. 
    apply forall_vals_inject_intern_incr with (mu := mu); auto.
    apply forall_vals_inject_restrictD' in INJ; auto. destruct INJ as [_ X].
    intros b0 GET. cut (vis mu b0=true). apply intern_incr_vis; auto.
    solve[apply X; auto].
  inv H3. eapply agree_args_match_aux_intern_incr; eauto. 
  inv H3; auto.
inv H3. intros ? ? X. inv H2. specialize (H3 b0 sp' z). revert H3.
specialize (agree_sp_fresh0 b0 z). revert agree_sp_fresh0.
case_eq (as_inj mu b0). intros [? ?] INJ.
apply intern_incr_as_inj in H; auto. 
apply H in INJ. rewrite INJ in X. inv X. 
solve[intros Y _; apply Y; auto].
intros NONE _ Y. destruct (Y (eq_refl _) X) as [Y1 Y2].
unfold DomTgt in Y2. rewrite agree_sp_local0 in Y2. simpl in Y2; congruence.
destruct H1 as [_ [_ [X [_ [_ _]]]]]. 
apply X; inv H3; auto.
Qed.

Lemma agree_args_extern_incr f0 mu mu' args tys stack ls m1 m2 m2' sp' (WD' : SM_wd mu') :
  extern_incr mu mu' ->
  sm_inject_separated mu mu' m1 m2 ->
  agree_args f0 mu args tys stack ls m2' sp' ->
  agree_args f0 mu' args tys stack ls m2' sp'.
Proof.
inversion 1; subst. constructor; auto. intros. 
  inv H3; auto. 
  inv H3; auto. 
  inv H3; auto. 
  inv H3. destruct agree_args_inj0 as [args0 INJ]. exists args0.
    apply restrict_forall_vals_inject.
    apply forall_vals_inject_restrictD in INJ; auto. 
    apply forall_vals_inject_extern_incr with (mu := mu); auto.
    apply forall_vals_inject_restrictD' in INJ; auto. destruct INJ as [_ X].
    intros b0 GET. cut (vis mu b0=true). intros. erewrite <-extern_incr_vis; eauto.
    solve[apply X; auto].
  inv H3. eapply agree_args_match_aux_extern_incr; eauto. 
  inv H3; auto.
inv H3. intros ? ? X. inv H2. specialize (H3 b0 sp' z). revert H3.
specialize (agree_sp_fresh0 b0 z). revert agree_sp_fresh0.
case_eq (as_inj mu b0). intros [? ?] INJ.
apply extern_incr_as_inj in H; auto. 
apply H in INJ. rewrite INJ in X. inv X. 
solve[intros Y _; apply Y; auto].
intros NONE _ Y. destruct (Y (eq_refl _) X) as [Y1 Y2].
unfold DomTgt in Y2. rewrite agree_sp_local0 in Y2. simpl in Y2; congruence.
destruct H1 as [_ [_ [_ [_ [<- _]]]]]. inv H3; auto.
Qed.

(** A variant of the latter, for use with external calls *)

(*LENB: converted to strcutural injections*)
Lemma agree_frame_extcall_invariant:
  forall mu ls ls0 m sp m' sp' parent retaddr m1 m1',
  agree_frame (as_inj mu) ls ls0 m sp m' sp' parent retaddr ->
  (Mem.valid_block m sp -> Mem.valid_block m1 sp) ->
  (forall ofs p, Mem.perm m1 sp ofs Max p -> Mem.perm m sp ofs Max p) ->
  (Mem.valid_block m' sp' -> Mem.valid_block m1' sp') ->
  Mem.unchanged_on (local_out_of_reach mu m) m' m1' ->
  (*LENB: New conditions :*)
  forall (WD: SM_wd mu) (SP: locBlocksTgt mu sp' = true),
  agree_frame (as_inj mu) ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  intros.
  assert (REACH: forall ofs,
     ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
    local_out_of_reach mu m sp' ofs).
  { intros; red; intros. 
        split; intros. trivial. apply local_in_all in H5; trivial. 
        exploit agree_inj_unique; eauto.
    intros [EQ1 EQ2]; subst.
    left. red; intros. exploit agree_bounds; eauto. omega. }
  eapply agree_frame_invariant; eauto.
  intros. eapply Mem.load_unchanged_on; eauto. intros. apply REACH. omega. 
  intros. eapply Mem.perm_unchanged_on; eauto with mem. auto. 
Qed.

Lemma agree_frame_extcall_invariant':
  forall mu ls ls0 m sp m' sp' parent retaddr m1 m1',
  agree_frame (as_inj mu) ls ls0 m sp m' sp' parent retaddr ->
  (Mem.valid_block m sp -> Mem.valid_block m1 sp) ->
  (forall ofs p, Mem.perm m1 sp ofs Max p -> Mem.perm m sp ofs Max p) ->
  (Mem.valid_block m' sp' -> Mem.valid_block m1' sp') ->
  Mem.unchanged_on (loc_out_of_reach (as_inj (restrict_sm mu (vis mu))) m) m' m1' ->
  (*LENB: New conditions :*)
  forall (WD: SM_wd mu) (SP: locBlocksTgt mu sp' = true),
  agree_frame (as_inj mu) ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
  intros.
  assert (REACH: forall ofs,
     ofs < fe.(fe_stack_data) \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
    loc_out_of_reach (as_inj (restrict_sm mu (vis mu))) m sp' ofs).
    intros; red; intros. 
      rewrite restrict_sm_all, restrict_vis_foreign_local in H5; trivial.
      destruct (joinD_Some _ _ _ _ _ H5) as [FRG | [FRG LOC]]; clear H5.
        assert (locBlocksTgt mu sp' = false). eapply foreign_DomRng; eassumption.
        rewrite H5 in SP; discriminate.
        apply local_in_all in LOC; trivial. 
        exploit agree_inj_unique; eauto.
    intros [EQ1 EQ2]; subst.
    red; intros. exploit agree_bounds; eauto. omega.
  eapply agree_frame_invariant; eauto.
  intros. eapply Mem.load_unchanged_on; eauto. intros. apply REACH. omega. 
  intros. eapply Mem.perm_unchanged_on; eauto with mem. auto. 
Qed.

(** Preservation by parallel stores in the Linear and Mach codes *)

Lemma agree_frame_parallel_stores:
  forall j ls ls0 m sp m' sp' parent retaddr chunk addr addr' v v' m1 m1',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  Mem.inject j m m' ->
  val_inject j addr addr' ->
  Mem.storev chunk m addr v = Some m1 ->
  Mem.storev chunk m' addr' v' = Some m1' ->
  agree_frame j ls ls0 m1 sp m1' sp' parent retaddr.
Proof.
Opaque Int.add.
  intros until m1'. intros AG MINJ VINJ STORE1 STORE2.
  inv VINJ; simpl in *; try discriminate.
  eapply agree_frame_invariant; eauto.
  eauto with mem.
  eauto with mem.
  eauto with mem.
  intros. rewrite <- H1. eapply Mem.load_store_other; eauto. 
    destruct (eq_block sp' b2); auto.
    subst b2. right.
    exploit agree_inj_unique; eauto. intros [P Q]. subst b1 delta.
    exploit Mem.store_valid_access_3. eexact STORE1. intros [A B].
    rewrite shifted_stack_offset_no_overflow.
    exploit agree_bounds. eauto. apply Mem.perm_cur_max. apply A. 
    instantiate (1 := Int.unsigned ofs1). generalize (size_chunk_pos chunk). omega.
    intros C.
    exploit agree_bounds. eauto. apply Mem.perm_cur_max. apply A. 
    instantiate (1 := Int.unsigned ofs1 + size_chunk chunk - 1). 
      generalize (size_chunk_pos chunk). omega.
    intros D.
    omega.
    eapply agree_bounds. eauto. apply Mem.perm_cur_max. apply A. 
    generalize (size_chunk_pos chunk). omega.
  intros; eauto with mem.
Qed.

(** Preservation by increasing memory injections (allocations and external calls) *)

Lemma agree_frame_inject_incr:
  forall j ls ls0 m sp m' sp' parent retaddr m1 m1' j',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  inject_incr j j' -> inject_separated j j' m1 m1' ->
  Mem.valid_block m1' sp' ->
  agree_frame j' ls ls0 m sp m' sp' parent retaddr.
Proof.
  intros. inv H. constructor; auto; intros; eauto with stacking.
  case_eq (j b0). 
  intros [b' delta'] EQ. rewrite (H0 _ _ _ EQ) in H. inv H. auto. 
  intros EQ. exploit H1. eauto. eauto. intros [A B]. contradiction.
Qed.

(*Lenb: in Lemma agree_frame_inject_inc above, the condition
    inject_separated is a bit too strong -- really only
  entries  mapping into sp' matter. One way to express this
  is the following variant*)
Lemma agree_frame_inject_incr_restrict:
  forall j ls ls0 m sp m' sp' parent retaddr X Y,
  agree_frame (restrict j X) ls ls0 m sp m' sp' parent retaddr ->
  (forall b, X b = true -> Y b = true) ->
  (forall b d, restrict j Y b = Some (sp', d) -> restrict j X b = Some (sp', d)) -> 
  agree_frame (restrict j Y) ls ls0 m sp m' sp' parent retaddr.
Proof.
  intros.
  assert (inject_incr (restrict j X) (restrict j Y)).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H2).
      apply H0 in H4. eapply restrictI_Some; eassumption.
  inv H. constructor; auto; intros; eauto with stacking.
Qed.

Remark inject_alloc_separated:
  forall j m1 m2 j' b1 b2 delta,
  inject_incr j j' ->
  j' b1 = Some(b2, delta) ->
  (forall b, b <> b1 -> j' b = j b) ->
  ~Mem.valid_block m1 b1 -> ~Mem.valid_block m2 b2 ->
  inject_separated j j' m1 m2.
Proof.
  intros. red. intros.
  destruct (eq_block b0 b1). subst b0. rewrite H0 in H5; inv H5. tauto.
  rewrite H1 in H5. congruence. auto.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Lemma agree_frame_return:
  forall j ls ls0 m sp m' sp' parent retaddr ls',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  agree_callee_save ls' ls ->
  wt_locset ls' ->
  agree_frame j ls' ls0 m sp m' sp' parent retaddr.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
  rewrite H0; auto. red; intros; elim H. apply caller_save_reg_within_bounds; auto. 
  rewrite H0; auto.
  rewrite H0; auto.
  rewrite H0; auto.
Qed.

(** Preservation at tailcalls (when [ls0] is changed but not [ls]). *)

Lemma agree_frame_tailcall:
  forall j ls ls0 m sp m' sp' parent retaddr ls0',
  agree_frame j ls ls0 m sp m' sp' parent retaddr ->
  agree_callee_save ls0 ls0' ->
  agree_frame j ls ls0' m sp m' sp' parent retaddr.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
  rewrite <- H0; auto. red; intros; elim H. apply caller_save_reg_within_bounds; auto. 
  rewrite <- H0; auto.
  rewrite <- H0. auto. red; intros. eapply int_callee_save_not_destroyed; eauto. 
  rewrite <- H0. auto. red; intros. eapply float_callee_save_not_destroyed; eauto. 
Qed.

(** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto.
  rewrite pred_dec_false; auto. 
Qed.

Lemma agree_callee_save_set_result:
  forall sg vl ls1 ls2,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.setlist (map R (loc_result sg)) vl ls1) ls2.
Proof.
  intros sg. generalize (loc_result_caller_save sg).
  generalize (loc_result sg).
Opaque destroyed_at_call.
  induction l; simpl; intros.
  auto.
  destruct vl; auto. 
  apply IHl; auto.
  red; intros. rewrite Locmap.gso. apply H0; auto. 
  destruct l0; simpl; auto. 
Qed.

(** Properties of destroyed registers. *)

Lemma check_mreg_list_incl:
  forall l1 l2,
  forallb (fun r => In_dec mreg_eq r l2) l1 = true ->
  incl l1 l2.
Proof.
  intros; red; intros. 
  rewrite forallb_forall in H. eapply proj_sumbool_true. eauto. 
Qed.

Remark destroyed_by_op_caller_save:
  forall op, incl (destroyed_by_op op) destroyed_at_call.
Proof.
  destruct op; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_load_caller_save:
  forall chunk addr, incl (destroyed_by_load chunk addr) destroyed_at_call.
Proof.
  intros. destruct chunk; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_store_caller_save:
  forall chunk addr, incl (destroyed_by_store chunk addr) destroyed_at_call.
Proof.
  intros. destruct chunk; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_cond_caller_save:
  forall cond, incl (destroyed_by_cond cond) destroyed_at_call.
Proof.
  destruct cond; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_jumptable_caller_save:
  incl destroyed_by_jumptable destroyed_at_call.
Proof.
  apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_setstack_caller_save:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_call.
Proof.
  destruct ty; apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_at_function_entry_caller_save:
  incl destroyed_at_function_entry destroyed_at_call.
Proof.
  apply check_mreg_list_incl; compute; auto.
Qed.

Remark destroyed_by_move_at_function_entry:
  incl (destroyed_by_op Omove) destroyed_at_function_entry.
Proof.
  apply check_mreg_list_incl; compute; auto.
Qed.

Remark temp_for_parent_frame_caller_save:
  In temp_for_parent_frame destroyed_at_call.
Proof.
  Transparent temp_for_parent_frame.
  Transparent destroyed_at_call.
  unfold temp_for_parent_frame; simpl; tauto.
Qed.

Hint Resolve destroyed_by_op_caller_save destroyed_by_load_caller_save
    destroyed_by_store_caller_save
    destroyed_by_cond_caller_save destroyed_by_jumptable_caller_save
    destroyed_at_function_entry_caller_save: stacking.

Remark transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
Proof.
  intros; destruct op; reflexivity.
Qed.

Remark transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

Remark transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)
Section SAVE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable csregs: list mreg.
Variable ls: locset.

Inductive stores_in_frame: mem -> mem -> Prop :=
  | stores_in_frame_refl: forall m,
      stores_in_frame m m
  | stores_in_frame_step: forall m1 chunk ofs v m2 m3,
       ofs + size_chunk chunk <= fe.(fe_stack_data)
       \/ fe.(fe_stack_data) + f.(Linear.fn_stacksize) <= ofs ->
       Mem.store chunk m1 sp ofs v = Some m2 ->
       stores_in_frame m2 m3 ->
       stores_in_frame m1 m3.

Remark stores_in_frame_trans:
  forall m1 m2, stores_in_frame m1 m2 ->
  forall m3, stores_in_frame m2 m3 -> stores_in_frame m1 m3.
Proof.
  induction 1; intros. auto. econstructor; eauto.
Qed.

Lemma agree_args_stores_in_frame f0 mu args tys s m m' sp0 (WD : SM_wd mu) :
  agree_args f0 mu args tys s ls m sp0 -> 
  sp<>sp0 -> 
  stores_in_frame m m' -> 
  agree_args f0 mu args tys s ls m' sp0.
Proof.
intros H NEQ H2; induction H2; auto.
apply IHstores_in_frame.
eapply agree_args_invariant; eauto.
eapply Mem.store_unchanged_on; eauto.
Qed.

Hypothesis number_inj: 
  forall r1 r2, In r1 csregs -> In r2 csregs -> r1 <> r2 -> number r1 <> number r2.
Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis mkindex_inj:
  forall z1 z2, z1 <> z2 -> mkindex z1 <> mkindex z2.
Hypothesis mkindex_diff:
  forall r idx,
  idx <> mkindex (number r) -> index_diff (mkindex (number r)) idx.
Hypothesis csregs_typ:
  forall r, In r csregs -> mreg_type r = ty.

Hypothesis ls_temp_undef:
  forall r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef.

Hypothesis wt_ls: wt_locset ls.

Lemma save_callee_save_regs_correct:
  forall l k rs lf m,
  incl l csregs ->
  list_norepet l ->
  frame_perm_freeable m sp ->
  agree_regs j ls rs ->
  exists rs', exists m',
    corestep_star (Mach_eff_sem hf return_address_offset) tge 
       (Mach_State cs fb (Vptr sp Int.zero)
         (save_callee_save_regs bound number mkindex ty fe l k) rs lf) m
       (Mach_State cs fb (Vptr sp Int.zero) k rs' lf) m'
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_contains_inj j m' sp (mkindex (number r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'
  /\ (*NEW*) freshloc m m' = (fun b => false).
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists rs; exists m. split. apply corestep_star_zero. 
  split. intros. elim H3.
  split. auto.
  split. constructor.
  split. auto.
  split. auto.
  apply extensionality. intros b'. apply freshloc_irrefl.
  (* inductive case *)
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  exploit store_index_succeeds. apply (mkindex_valid a); auto with coqlib. 
  eauto. instantiate (1 := rs a). intros [m1 ST].
  exploit (IHl k (undef_regs (destroyed_by_setstack ty) rs) lf m1).  
    auto with coqlib. auto. 
  red; eauto with mem.
  apply agree_regs_exten with ls rs. auto.
  intros. destruct (In_dec mreg_eq r (destroyed_by_setstack ty)).
  left. apply ls_temp_undef; auto. 
  right; split. auto. apply undef_regs_other; auto.
  intros [rs' [m' [A [B [C [D [E [F G]]]]]]]].
  exists rs'; exists m'. 
  split. eapply corestep_star_trans. 
           eapply corestep_star_one. econstructor. 
            rewrite <- (mkindex_typ (number a)). 
            apply store_stack_succeeds; auto with coqlib.
            eassumption.
            eauto.
         eassumption.
  split; intros.
  simpl in H3. destruct (mreg_eq a r). subst r.
  assert (index_contains_inj j m1 sp (mkindex (number a)) (ls (R a))).
    eapply gss_index_contains_inj; eauto.
    rewrite mkindex_typ. rewrite <- (csregs_typ a). apply wt_ls. auto with coqlib.
  destruct H5 as [v' [P Q]].
  exists v'; split; auto. apply C; auto. 
  intros. apply mkindex_inj. apply number_inj; auto with coqlib. 
  inv H0. intuition congruence.
  apply B; auto with coqlib. 
  intuition congruence.
  split. intros.
  apply C; auto with coqlib.
  eapply gso_index_contains; eauto with coqlib. 
  split. econstructor; eauto.
  rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; eauto with coqlib.
  split. auto.
  split. auto.
  (*freshloc*)
  specialize (store_forward _ _ _ _ _ _ ST). intros FWD1.
  specialize (corestep_star_fwd _ _ _ _ _ _ A). intros FWD2.
  apply extensionality. intros b'.
  rewrite <- (freshloc_trans _ m1); trivial.
  rewrite G, (store_freshloc _ _ _ _ _ _ ST). trivial.
(* no store takes place *)
  exploit (IHl k rs lf m); auto with coqlib. 
  intros [rs' [m' [A [B [C [D [E [F G]]]]]]]].
  exists rs'; exists m'; intuition. 
  simpl in H3. destruct H3. subst r. omegaContradiction. apply B; auto.
  apply C; auto with coqlib.
  intros. eapply H4; eauto. auto with coqlib.
Qed.

Definition STEffect bb ofs len (b : block) (z : Z) :=
    eq_block bb b && zle ofs z && zlt z (ofs + len).

Lemma STEffect_Store chunk m bb off v m': forall
      (ST : Mem.store chunk m bb off v = Some m'),
      Mem.unchanged_on
    (fun (b : block) (ofs : Z) =>
     STEffect bb off (size_chunk chunk) b ofs = false) m m'.
Proof. intros.
  unfold STEffect.
  split; intros.
      split; intros. eapply Mem.perm_store_1; eassumption.
      eapply Mem.perm_store_2; eassumption.
  rewrite (Mem.store_mem_contents _ _ _ _ _ _ ST). clear ST.
  destruct (eq_block bb b0); subst; simpl in *.
    rewrite PMap.gss. apply andb_false_iff in H.  
    apply Mem.setN_outside.
    destruct H. destruct (zle off ofs ); simpl in *. inv H.
                left. xomega.
    right. rewrite encode_val_length, <- size_chunk_conv.
    destruct (zlt ofs (off + size_chunk chunk)); simpl in *. inv H.
     trivial. 
  rewrite PMap.gso. trivial. intros N; subst. elim n; trivial. 
Qed.

(*The effect of save_callee_save_regs*)
Fixpoint SCS_Effect (l:list mreg) (b : block) (z : Z):bool :=
  match l with nil => false
   | cons a t => eq_block sp b &&
                  ((zlt (number a) (bound fe) && 
                    STEffect sp (offset_of_index fe (mkindex (number a))) 
                          (size_chunk (chunk_of_type ty)) b z)
                   || SCS_Effect t b z)
  end.

Lemma SCS_Effect_sp l bb z: true = SCS_Effect l bb z -> bb=sp.
Proof. intros.
  destruct l ; simpl in *. inv H.
  destruct (eq_block sp bb); trivial; simpl in *. subst; trivial.
  inv H.
Qed.

Lemma SCS_Effect_noStore a l: forall (H: number a >= bound fe),
      SCS_Effect (a :: l) = SCS_Effect l.
Proof. intros.
  unfold SCS_Effect; simpl.
  destruct (zlt (number a) (bound fe)); simpl; try omega.
  apply extensionality; intros bb.
  apply extensionality; intros z.
  fold SCS_Effect.
  remember (SCS_Effect l bb z) as q.
  destruct q; simpl. 
    apply SCS_Effect_sp in Heqq.
    destruct (eq_block sp bb); trivial. intuition.
  apply andb_false_r.
Qed.

Lemma SCS_Effect_nil:  SCS_Effect nil = EmptyEffect.
Proof. intros. reflexivity. Qed.

Lemma save_callee_save_regs_correct_eff:
  forall l k rs m lf,
  incl l csregs ->
  list_norepet l ->
  frame_perm_freeable m sp ->
  agree_regs j ls rs ->
  exists rs', exists m', 
    effstep_star (Mach_eff_sem hf return_address_offset) tge 
       (SCS_Effect l)
       (Mach_State cs fb (Vptr sp Int.zero)
         (save_callee_save_regs bound number mkindex ty fe l k) rs lf) m
       (Mach_State cs fb (Vptr sp Int.zero) k rs' lf) m' 
  /\ (forall r,
       In r l -> number r < bound fe ->
       index_contains_inj j m' sp (mkindex (number r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       (forall r,
         In r l -> number r < bound fe -> idx <> mkindex (number r)) ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'
  /\ (*NEW*) freshloc m m' = (fun b => false).
Proof.
  induction l; intros; simpl save_callee_save_regs.
  (* base case *)
  exists rs; exists m.
    split. apply effstep_star_zero.
  split. intros. elim H3.
  split. auto.
  split. constructor.
  split. auto.
  split. auto.
  apply extensionality. intros b'. apply freshloc_irrefl.
  (* inductive case *)
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold save_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  (* a store takes place *)
  exploit store_index_succeeds. apply (mkindex_valid a); auto with coqlib. 
  eauto. instantiate (1 := rs a). intros [m1 ST].
  exploit (IHl k (undef_regs (destroyed_by_setstack ty) rs) m1).  auto with coqlib. auto. 
    red; eauto with mem.
    apply agree_regs_exten with ls rs. auto.
    intros. destruct (In_dec mreg_eq r (destroyed_by_setstack ty)).
    left. apply ls_temp_undef; auto.   
    right; split. auto. apply undef_regs_other; auto.
  clear IHl; intros [rs' [m' [A [B [C [D [E [F G]]]]]]]].
  exists rs'; exists m'. 
  split. eapply effstep_star_trans'. 
           eapply effstep_star_one. econstructor. 
            rewrite <- (mkindex_typ (number a)). 
            apply store_stack_succeeds; auto with coqlib.
            eassumption.
            eauto.
         eassumption. 
         apply extensionality; intros bb. apply extensionality; intros z.
           assert (Val.add (Vptr sp Int.zero)
                           (Vint (Int.repr (offset_of_index fe (mkindex (number a)))))
                   = Vptr sp (Int.repr (offset_of_index fe (mkindex (number a))))).
             clear. simpl. rewrite Int.add_zero_l. trivial.
           rewrite H3; clear H3.
           simpl.
           rewrite offset_of_index_no_overflow.
           Focus 2. eapply mkindex_valid. apply H. left; trivial. assumption.
           destruct (zlt (number a) (bound fe)); simpl; try omega.
           unfold STEffect. 
           destruct (eq_block sp bb); subst; simpl; trivial.
             rewrite <- e in *. clear e bb.
             destruct (valid_block_dec m sp).
             Focus 2. elim n. eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies. eapply Mem.store_valid_access_3. eassumption. constructor.
             simpl; rewrite andb_true_r. 
             rewrite encode_val_length. rewrite <- size_chunk_conv. 
             reflexivity.
           remember (SCS_Effect l bb z) as q.
             destruct q; simpl; trivial.
             apply SCS_Effect_sp in Heqq. intuition.
  split; intros.
  simpl in H3. destruct (mreg_eq a r). subst r.
  assert (index_contains_inj j m1 sp (mkindex (number a)) (ls (R a))).
    eapply gss_index_contains_inj; eauto.
    rewrite mkindex_typ. rewrite <- (csregs_typ a). apply wt_ls. auto with coqlib.
  destruct H5 as [v' [P Q]].
  exists v'; split; auto. apply C; auto. 
  intros. apply mkindex_inj. apply number_inj; auto with coqlib. 
  inv H0. intuition congruence.
  apply B; auto with coqlib. 
  intuition congruence.
  split. intros.
  apply C; auto with coqlib.
  eapply gso_index_contains; eauto with coqlib. 
  split. econstructor; eauto.
  rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; eauto with coqlib.
  split. auto.
  split. auto.
  (*freshloc*)
  specialize (store_forward _ _ _ _ _ _ ST). intros FWD1.
  specialize (effstep_star_fwd _ _ _ _ _ _ _ A). intros FWD2.
  apply extensionality. intros b'.
  rewrite <- (freshloc_trans _ m1); trivial.
  rewrite G, (store_freshloc _ _ _ _ _ _ ST). trivial.
(* no store takes place *)
  exploit (IHl k rs m lf); auto with coqlib. 
  intros [rs' [m' [A [B [C [D [E [F G]]]]]]]].
  exists rs'; exists m'. intuition.
  (*1/3*) rewrite SCS_Effect_noStore; trivial. 
  (*2/3*) 
  simpl in H3. destruct H3. subst r. omegaContradiction. apply B; auto.
  (*3/3*)
  apply C; auto with coqlib.
  intros. eapply H4; eauto. auto with coqlib.
Qed.

End SAVE_CALLEE_SAVE.

Remark LTL_undef_regs_same:
  forall r rl ls, In r rl -> LTL.undef_regs rl ls (R r) = Vundef.
Proof.
  induction rl; simpl; intros. contradiction. 
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto. 
  destruct (Loc.diff_dec (R a) (R r)); auto. 
  apply IHrl. intuition congruence.
Qed.

Remark LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> LTL.undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition. 
Qed.

Remark LTL_undef_regs_slot:
  forall sl ofs ty rl ls, LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto. 
Qed.

Lemma save_callee_save_correct:
  forall j ls0 rs sp cs fb k m lf,
  let ls := LTL.undef_regs destroyed_at_function_entry ls0 in
  agree_regs j ls rs -> wt_locset ls ->
  frame_perm_freeable m sp ->
  exists rs', exists m',
    corestep_star (Mach_eff_sem hf return_address_offset) tge 
       (Mach_State cs fb (Vptr sp Int.zero) (save_callee_save fe k) rs lf) m
       (Mach_State cs fb (Vptr sp Int.zero) k rs' lf) m'
  /\ (forall r,
       In r int_callee_save_regs -> index_int_callee_save r < b.(bound_int_callee_save) ->
       index_contains_inj j m' sp (FI_saved_int (index_int_callee_save r)) (ls (R r)))
  /\ (forall r,
       In r float_callee_save_regs -> index_float_callee_save r < b.(bound_float_callee_save) ->
       index_contains_inj j m' sp (FI_saved_float (index_float_callee_save r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       match idx with FI_saved_int _ => False | FI_saved_float _ => False | _ => True end ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame sp m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'
  /\ (*NEW*) freshloc m m' = (fun b => false).
Proof.
  intros.
  assert (UNDEF: forall r, In r (destroyed_by_op Omove) -> ls (R r) = Vundef).
    intros. unfold ls. apply LTL_undef_regs_same. apply destroyed_by_move_at_function_entry; auto.
  exploit (save_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int Tint
             j cs fb sp int_callee_save_regs ls).
  intros. apply index_int_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_int_callee_save_pos; auto. assumption.
  auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply int_callee_save_type. auto.
Local Transparent destroyed_by_setstack.
  simpl. tauto.
  auto.
  apply incl_refl. 
  apply int_callee_save_norepet.
  eauto.
  eauto.
  intros [rs1 [m1 [A [B [C [D [E [F G]]]]]]]].
  exploit (save_callee_save_regs_correct 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float Tfloat
             j cs fb sp float_callee_save_regs ls).
  intros. apply index_float_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_float_callee_save_pos; auto. assumption.
  simpl; auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply float_callee_save_type. auto.
  simpl. tauto. 
  auto. 
  apply incl_refl. 
  apply float_callee_save_norepet.
  eexact E.
  eexact F.
  intros [rs2 [m2 [P [Q [R [S [T [U V]]]]]]]].
  exists rs2; exists m2.
  split. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply corestep_star_trans; try eassumption. 
  split; intros.
  destruct (B r H2 H3) as [v [X Y]]. exists v; split; auto. apply R.
  apply index_saved_int_valid; auto. 
  intros. congruence.
  auto.
  split. intros. apply Q; auto.
  split. intros. apply R. auto.
  intros. destruct idx; contradiction||congruence.
  apply C. auto. 
  intros. destruct idx; contradiction||congruence.
  auto.
  split. eapply stores_in_frame_trans; eauto.
  split. auto.
  split. auto.
  (*freshloc*)
  apply extensionality. intros b'.
  specialize (corestep_star_fwd _ _ _ _ _ _ A). intros FWD1.
  specialize (corestep_star_fwd _ _ _ _ _ _ P). intros FWD2.
  rewrite <- (freshloc_trans _ m1); trivial.
  rewrite G, V. trivial.
Qed.

Definition PrologueEffect m sp' (bb : block) (z : Z):=
           SCS_Effect fe_num_int_callee_save index_int_callee_save FI_saved_int Tint
             sp' int_callee_save_regs bb z
           || SCS_Effect fe_num_float_callee_save index_float_callee_save
                FI_saved_float Tfloat sp' float_callee_save_regs bb z &&
              valid_block_dec m bb.

Lemma PrologueEffect_sp m sp' bb z: 
      PrologueEffect m sp' bb z = true -> bb=sp'.
Proof. intros. unfold PrologueEffect in H.
  apply orb_true_iff in H.
  destruct H.
    apply eq_sym in H. eapply SCS_Effect_sp; eassumption.
  apply andb_true_iff in H; destruct H.
    apply eq_sym in H. eapply SCS_Effect_sp; eassumption.
Qed.

Lemma save_callee_save_correct_eff:
  forall j ls0 rs sp cs fb k m lf,
  let ls := LTL.undef_regs destroyed_at_function_entry ls0 in
  agree_regs j ls rs -> wt_locset ls ->
  frame_perm_freeable m sp ->
  exists rs', exists m', 
    effstep_star (Mach_eff_sem hf return_address_offset) tge 
       (PrologueEffect m sp)
       (Mach_State cs fb (Vptr sp Int.zero) (save_callee_save fe k) rs lf) m
       (Mach_State cs fb (Vptr sp Int.zero) k rs' lf) m'
  /\ (forall r,
       In r int_callee_save_regs -> index_int_callee_save r < b.(bound_int_callee_save) ->
       index_contains_inj j m' sp (FI_saved_int (index_int_callee_save r)) (ls (R r)))
  /\ (forall r,
       In r float_callee_save_regs -> index_float_callee_save r < b.(bound_float_callee_save) ->
       index_contains_inj j m' sp (FI_saved_float (index_float_callee_save r)) (ls (R r)))
  /\ (forall idx v,
       index_valid idx ->
       match idx with FI_saved_int _ => False | FI_saved_float _ => False | _ => True end ->
       index_contains m sp idx v ->
       index_contains m' sp idx v)
  /\ stores_in_frame sp m m'
  /\ frame_perm_freeable m' sp
  /\ agree_regs j ls rs'
  /\ (*NEW*) freshloc m m' = (fun b => false).
Proof.
  intros.
  assert (UNDEF: forall r, In r (destroyed_by_op Omove) -> ls (R r) = Vundef).
    intros. unfold ls. apply LTL_undef_regs_same. apply destroyed_by_move_at_function_entry; auto.
  exploit (save_callee_save_regs_correct_eff
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int Tint
             j cs fb sp int_callee_save_regs ls).
  intros. apply index_int_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_int_callee_save_pos; auto. assumption.
  auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply int_callee_save_type. auto.
Local Transparent destroyed_by_setstack.
  simpl. tauto.
  auto.
  apply incl_refl. 
  apply int_callee_save_norepet.
  eauto.
  eauto.
  intros [rs1 [m1 [A [B [C [D [E [F G]]]]]]]].
  exploit (save_callee_save_regs_correct_eff 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float Tfloat
             j cs fb sp float_callee_save_regs ls).
  intros. apply index_float_callee_save_inj; auto. 
  intros. simpl. split. apply Zge_le. apply index_float_callee_save_pos; auto. assumption.
  simpl; auto.
  intros; congruence.
  intros; simpl. destruct idx; auto. congruence.
  intros. apply float_callee_save_type. auto.
  simpl. tauto. 
  auto. 
  apply incl_refl. 
  apply float_callee_save_norepet.
  eexact E.
  eexact F.
  intros [rs2 [m2 [P [Q [R [S [T [U V]]]]]]]].
  exists rs2; exists m2.
  split. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply effstep_star_trans'; try eassumption. reflexivity. 
  split; intros.
  destruct (B r H2 H3) as [v [X Y]]. exists v; split; auto. apply R.
  apply index_saved_int_valid; auto. 
  intros. congruence.
  auto.
  split. intros. apply Q; auto.
  split. intros. apply R. auto.
  intros. destruct idx; contradiction||congruence.
  apply C. auto. 
  intros. destruct idx; contradiction||congruence.
  auto.
  split. eapply stores_in_frame_trans; eauto.
  split. auto.
  split. auto.
  (*freshloc*)
  apply extensionality. intros b'.
  specialize (effstep_star_fwd _ _ _ _ _ _ _ A). intros FWD1.
  specialize (effstep_star_fwd _ _ _ _ _ _ _ P). intros FWD2.
  rewrite <- (freshloc_trans _ m1); trivial.
  rewrite G, V. trivial.
Qed.

(** Properties of sequences of stores in the frame. *)

Lemma stores_in_frame_inject:
  forall j sp sp' m,
  (forall b delta, j b = Some(sp', delta) -> b = sp /\ delta = fe.(fe_stack_data)) ->
  (forall ofs k p, Mem.perm m sp ofs k p -> 0 <= ofs < f.(Linear.fn_stacksize)) ->
  forall m1 m2, stores_in_frame sp' m1 m2 -> Mem.inject j m m1 -> Mem.inject j m m2.
Proof.
  induction 3; intros.
  auto.
  apply IHstores_in_frame.
  intros. eapply Mem.store_outside_inject; eauto.
  intros. exploit H; eauto. intros [A B]; subst.
  exploit H0; eauto. omega. 
Qed.

Lemma stores_in_frame_valid:
  forall b sp m m', stores_in_frame sp m m' -> Mem.valid_block m b -> Mem.valid_block m' b.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_perm:
  forall b ofs k p sp m m', stores_in_frame sp m m' -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p.
Proof.
  induction 1; intros. auto. apply IHstores_in_frame. eauto with mem.
Qed.

Lemma stores_in_frame_contents:
  forall chunk b ofs sp, Plt b sp ->
  forall m m', stores_in_frame sp m m' -> 
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction 2. auto. 
  rewrite IHstores_in_frame. eapply Mem.load_store_other; eauto.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

Lemma function_prologue_correct:
  forall mu ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k lf
  (SMV: sm_valid mu m1 m1') (WD: SM_wd mu) (RC: REACH_closed m1 (vis mu)),
  agree_regs (restrict (as_inj mu) (vis mu)) ls rs ->
  agree_callee_save ls ls0 ->
  wt_locset ls ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.inject (as_inj mu) m1 m1' ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tint -> Val.has_type ra Tint ->
  exists mu', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5',
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) ra = Some m4'
  /\ corestep_star (Mach_eff_sem hf return_address_offset) tge 
         (Mach_State cs fb (Vptr sp' Int.zero) (save_callee_save fe k) rs1 lf) m4'
         (Mach_State cs fb (Vptr sp' Int.zero) k rs' lf) m5'
  /\ agree_regs (restrict (as_inj mu') (vis mu')) ls1 rs'
  /\ agree_frame (restrict (as_inj mu') (vis mu')) ls1 ls0 m2 sp m5' sp' parent ra
  /\ intern_incr mu mu' (*modified this guarantee*)
  /\ sm_inject_separated mu mu' m1 m1' (*modified this guarantee*)
  /\ Mem.inject (as_inj mu') m2 m5'
  /\ stores_in_frame sp' m2' m5'
  (*New guarantees:*)
(*  /\ sm_locally_allocated (alloc_right_sm mu sp') mu' m1 m2' m2 m2'*)
  /\ sm_locally_allocated mu mu' m1 m1' m2 m5'
  /\ SM_wd mu' /\ sm_valid mu' m2 m5' 
  /\ locBlocksTgt mu' sp' = true /\ REACH_closed m2 (vis mu').
Proof.
  intros until lf; intros SMV WD RC AGREGS AGCS WTREGS LS1 RS1 INJ1 ALLOC TYPAR TYRA.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Allocation step *)
  caseEq (Mem.alloc m1' 0 (fe_size fe)). intros m2' sp' ALLOC'.
  exploit (alloc_left_mapped_sm_inject (alloc_right_sm mu sp') m1 m2').
     eapply alloc_right_sm_wd; try assumption. 
       remember (DomTgt mu sp') as d; destruct d; trivial.
       apply eq_sym in Heqd.
       exfalso. eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC').
       eapply SMV. apply Heqd.
     red. unfold DOM, RNG. rewrite alloc_right_sm_DomTgt, alloc_right_sm_DomSrc.
       split. apply SMV.
       intros. destruct (eq_block b2 sp'); simpl in H.
                 subst. eapply Mem.valid_new_block; eassumption.
               eapply Mem.valid_block_alloc; try eassumption.
                 apply SMV. apply H.
     unfold vis; simpl. apply RC.
     instantiate (1 := sp'). rewrite alloc_right_sm_locBlocksTgt. 
         destruct (eq_block sp' sp'); trivial. elim n; trivial.
     eapply Mem.alloc_right_inject; try eassumption.
     eassumption.
     eapply Mem.valid_new_block; eassumption.
(*    instantiate (1 := sp'). eauto with mem.*)
    instantiate (1 := fe_stack_data fe).
    generalize stack_data_offset_valid (bound_stack_data_pos b) size_no_overflow; omega.
    intros; right. 
    exploit Mem.perm_alloc_inv. eexact ALLOC'. eauto. rewrite dec_eq_true. 
    generalize size_no_overflow. omega. 
    intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto.
    generalize stack_data_offset_valid bound_stack_data_stacksize; omega.
    red. intros. apply Zdivides_trans with 8. 
    destruct chunk; simpl; auto with align_4.
    apply fe_stack_data_aligned.
    intros.
      assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
      assert (~Mem.valid_block m1' sp') by eauto with mem.
      contradiction.
  intros [mu' [INJ2 [INCR [MAP1 [MAP2 [WD' [SMV' [LOCALLOC' RC']]]]]]]]. 
  assert (PERM: frame_perm_freeable m2' sp').
    red; intros. eapply Mem.perm_alloc_2; eauto.
  assert (SPlocalTgt': locBlocksTgt mu' sp' = true).
    eapply INCR. rewrite alloc_right_sm_locBlocksTgt. 
    destruct (eq_block sp' sp'); trivial. elim n; trivial.
  (* Store of parent *)
  exploit (store_index_succeeds m2' sp' FI_link parent). red; auto. auto. 
  intros [m3' STORE2].
  (* Store of retaddr *)
  exploit (store_index_succeeds m3' sp' FI_retaddr ra). red; auto. red; eauto with mem.
  intros [m4' STORE3].
  (* Saving callee-save registers *)
  assert (PERM4: frame_perm_freeable m4' sp').
    red; intros. eauto with mem. 
  exploit (save_callee_save_correct (as_inj (restrict_sm mu' (vis mu')))). 
    instantiate (1 := rs1). instantiate (1 := call_regs ls).
    subst rs1. apply agree_regs_undef_regs. 
    apply agree_regs_call_regs. eapply agree_regs_inject_incr; try eassumption.
      rewrite restrict_sm_all.
      eapply intern_incr_restrict. apply WD'.
      eapply intern_incr_trans.
        eapply alloc_right_sm_intern_incr; eassumption.
        eassumption.
    apply wt_undef_regs. apply wt_call_regs. auto.
    eexact PERM4.
  rewrite <- LS1.
  intros [rs' [m5' [STEPS [ICS [FCS [OTHERS [STORES [PERM5 [AGREGS' FRESH4'5']]]]]]]]].
  rewrite restrict_sm_all in *.
  (* stores in frames *)
  assert (SIF: stores_in_frame sp' m2' m5').
    econstructor; eauto. 
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
    econstructor; eauto.
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
  (* separation *)
  assert (SEP: forall b0 delta, as_inj mu' b0 = Some(sp', delta) -> b0 = sp /\ delta = fe_stack_data fe).
    intros. destruct (eq_block b0 sp). 
    subst b0. rewrite MAP1 in H; inv H; auto.
    rewrite MAP2 in H; auto. 
    assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
    assert (~Mem.valid_block m1' sp') by eauto with mem.
    contradiction.
  (* Conclusions *)
  exists mu'; exists rs'; exists m2'; exists sp'; exists m3'; exists m4'; exists m5'.
  split. auto.
  (* store parent *)
  split. change Tint with (type_of_index FI_link). 
  change (fe_ofs_link fe) with (offset_of_index fe FI_link).
  apply store_stack_succeeds; auto. red; auto.
  (* store retaddr *)
  split. change Tint with (type_of_index FI_retaddr). 
  change (fe_ofs_retaddr fe) with (offset_of_index fe FI_retaddr).
  apply store_stack_succeeds; auto. red; auto.
  (* saving of registers *)
  split. eexact STEPS.
  (* agree_regs *)
  split. auto.
  (* agree frame *)
  split. constructor; intros.
    (* unused regs *)
    assert (~In r destroyed_at_call). 
      red; intros; elim H; apply caller_save_reg_within_bounds; auto.
    rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs. 
    apply AGCS; auto. red; intros; elim H0. 
    apply destroyed_at_function_entry_caller_save; auto.
    (* locals *)
    rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs. 
    apply index_contains_inj_undef; auto with stacking.
    (* outgoing *)
    rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs. 
    apply index_contains_inj_undef; auto with stacking.
    (* incoming *)
    rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs.
    apply AGCS; auto. 
    (* parent *)
    apply OTHERS; auto. red; auto.
    eapply gso_index_contains; eauto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    red; auto.
    (* retaddr *)
    apply OTHERS; auto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    (* int callee save *)
    assert (~In r destroyed_at_call). 
      red; intros. eapply int_callee_save_not_destroyed; eauto.
    exploit ICS; eauto. rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs.
    rewrite AGCS; auto. 
    red; intros; elim H1. apply destroyed_at_function_entry_caller_save; auto.
    (* float callee save *)
    assert (~In r destroyed_at_call). 
      red; intros. eapply float_callee_save_not_destroyed; eauto.
    exploit FCS; eauto. rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs.
    rewrite AGCS; auto. 
    red; intros; elim H1. apply destroyed_at_function_entry_caller_save; auto.
    (* inj *)
    eapply restrictI_Some; try eassumption.
    destruct (joinD_Some _ _ _ _ _ MAP1) as [EXT | [_ LOC]].
      destruct (extern_DomRng _ WD' _ _ _ EXT).
      apply (extBlocksTgt_locBlocksTgt _ WD') in H0.
      rewrite SPlocalTgt' in H0; discriminate.
    destruct (local_DomRng _ WD' _ _ _ LOC).
      unfold vis; rewrite H. trivial.
    (* inj_unique *)
    destruct (restrictD_Some _ _ _ _ _ H). auto.
    (* valid sp *)
    eauto with mem.
    (* valid sp' *)
    eapply stores_in_frame_valid with (m := m2'); eauto with mem.
    (* bounds *)
    exploit Mem.perm_alloc_inv. eexact ALLOC. eauto. rewrite dec_eq_true. auto.
    (* perms *)
    auto.
    (* wt *)
    rewrite LS1. apply wt_undef_regs. apply wt_call_regs; auto.
  (* incr *)
  split. eapply intern_incr_trans; try eassumption.
         eapply alloc_right_sm_intern_incr.
  (* separated *)
  split. apply sm_locally_allocatedChar in LOCALLOC'.
         split; intros. destruct (eq_block b1 sp); subst.
            rewrite MAP1 in H0. inv H0. clear - ALLOC' ALLOC SMV.
            split.
            remember (DomSrc mu sp) as d; destruct d; trivial.
              apply eq_sym in Heqd. exfalso.
              eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).
              eapply SMV. apply Heqd.
            remember (DomTgt mu b2) as d; destruct d; trivial.
              apply eq_sym in Heqd. exfalso.
              eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC').
              eapply SMV. apply Heqd.
         rewrite (MAP2 _ n), alloc_right_sm_as_inj, H in H0. discriminate. 
       destruct LOCALLOC' as [DomSrc' [DomTgt' _]]; rewrite DomSrc', DomTgt'.
         rewrite alloc_right_sm_DomTgt, alloc_right_sm_DomSrc. 
         split; intros. rewrite H in H0; simpl in H0. rewrite freshloc_charT in H0. apply H0. 
         rewrite H, freshloc_irrefl in H0. 
         destruct (eq_block b2 sp'); subst; simpl in H0; try discriminate.
         eapply Mem.fresh_block_alloc; eassumption. 
  (* inject *)
  split. eapply stores_in_frame_inject; eauto.
  intros. exploit Mem.perm_alloc_inv. eexact ALLOC. eauto. rewrite dec_eq_true. auto.
  (* stores in frame *)
  split. auto.
  (*PRE' assertions*)
  intuition.
  clear ICS FCS OTHERS STORES PERM5 AGREGS' SIF.
    assert (freshloc m1' m5' = fun b' => eq_block b' sp').
      specialize (store_forward _ _ _ _ _ _ STORE2). intros FWD2.
      specialize (store_forward _ _ _ _ _ _ STORE3). intros FWD3.
      specialize (corestep_star_fwd _ _ _ _ _ _ STEPS). intros FWD4.
      apply extensionality; intros b'.
      specialize (alloc_forward _ _ _ _ _ ALLOC'); intros FWD1.
      rewrite <- (freshloc_trans _ m4'); try eassumption.
      rewrite FRESH4'5'.
      rewrite <- (freshloc_trans _ m3'); try eassumption.
      rewrite (store_freshloc _ _ _ _ _ _ STORE3).
      rewrite <- (freshloc_trans _ m2'); try eassumption.
      rewrite (store_freshloc _ _ _ _ _ _ STORE2).
      rewrite (freshloc_alloc _ _ _ _ _ ALLOC').
        repeat rewrite orb_false_r. trivial.
      eapply mem_forward_trans; eassumption.
      eapply mem_forward_trans; try eassumption.
        eapply mem_forward_trans; eassumption.          
    rewrite sm_locally_allocatedChar.
    rewrite sm_locally_allocatedChar in LOCALLOC'.
    destruct LOCALLOC' as [LASrc [LATgt [LAlocSrc [LAlocTgt [LAextSrc LAextTgt]]]]].
    rewrite LASrc, LATgt, LAlocSrc, LAlocTgt, LAextSrc, LAextTgt.
    clear LASrc LATgt LAlocSrc LAlocTgt LAextSrc LAextTgt.
    rewrite alloc_right_sm_DomSrc, alloc_right_sm_DomTgt,
            alloc_right_sm_locBlocksTgt, H.
            simpl. intuition.
            apply extensionality. intros b'. rewrite freshloc_irrefl, orb_false_r.
              apply orb_comm.
            apply extensionality. intros b'. rewrite freshloc_irrefl, orb_false_r.
              apply orb_comm.
  split; intros.
    eapply SMV'. assumption.
    eapply corestep_star_fwd; try eassumption.
      eapply store_forward; try eassumption.
      eapply store_forward; try eassumption.
      eapply SMV'. assumption.
Qed.

Lemma function_prologue_correct_eff:
  forall mu ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k lf
  (SMV: sm_valid mu m1 m1') (WD: SM_wd mu) (RC: REACH_closed m1 (vis mu)),
  agree_regs (restrict (as_inj mu) (vis mu)) ls rs ->
  agree_callee_save ls ls0 ->
  wt_locset ls ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.inject (as_inj mu) m1 m1' ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tint -> Val.has_type ra Tint ->
  exists mu', exists rs', exists m2', exists sp', exists m3', 
              exists m4', exists m5',
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) ra = Some m4'
  /\ effstep_star (Mach_eff_sem hf return_address_offset) tge
         (PrologueEffect m4' sp')
         (Mach_State cs fb (Vptr sp' Int.zero) (save_callee_save fe k) rs1 lf) m4'
         (Mach_State cs fb (Vptr sp' Int.zero) k rs' lf) m5'
  /\ agree_regs (restrict (as_inj mu') (vis mu')) ls1 rs'
  /\ agree_frame (restrict (as_inj mu') (vis mu')) ls1 ls0 m2 sp m5' sp' parent ra
  /\ intern_incr mu mu' (*modified this guarantee*)
  /\ sm_inject_separated mu mu' m1 m1' (*modified this guarantee*)
  /\ Mem.inject (as_inj mu') m2 m5'
  /\ stores_in_frame sp' m2' m5'
  (*New guarantees:*)
(*  /\ sm_locally_allocated (alloc_right_sm mu sp') mu' m1 m2' m2 m2'*)
  /\ sm_locally_allocated mu mu' m1 m1' m2 m5'
  /\ SM_wd mu' /\ sm_valid mu' m2 m5' 
  /\ locBlocksTgt mu' sp' = true /\ REACH_closed m2 (vis mu').
Proof.
  intros until lf; intros SMV WD RC AGREGS AGCS WTREGS LS1 RS1 INJ1 ALLOC TYPAR TYRA.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Allocation step *)
  caseEq (Mem.alloc m1' 0 (fe_size fe)). intros m2' sp' ALLOC'.
  exploit (alloc_left_mapped_sm_inject (alloc_right_sm mu sp') m1 m2').
     eapply alloc_right_sm_wd; try assumption. 
       remember (DomTgt mu sp') as d; destruct d; trivial.
       apply eq_sym in Heqd.
       exfalso. eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC').
       eapply SMV. apply Heqd.
     red. unfold DOM, RNG. rewrite alloc_right_sm_DomTgt, alloc_right_sm_DomSrc.
       split. apply SMV.
       intros. destruct (eq_block b2 sp'); simpl in H.
                 subst. eapply Mem.valid_new_block; eassumption.
               eapply Mem.valid_block_alloc; try eassumption.
                 apply SMV. apply H.
     unfold vis; simpl. apply RC.
     instantiate (1 := sp'). rewrite alloc_right_sm_locBlocksTgt. 
         destruct (eq_block sp' sp'); trivial. elim n; trivial.
     eapply Mem.alloc_right_inject; try eassumption.
     eassumption.
     eapply Mem.valid_new_block; eassumption.
(*    instantiate (1 := sp'). eauto with mem.*)
    instantiate (1 := fe_stack_data fe).
    generalize stack_data_offset_valid (bound_stack_data_pos b) size_no_overflow; omega.
    intros; right. 
    exploit Mem.perm_alloc_inv. eexact ALLOC'. eauto. rewrite dec_eq_true. 
    generalize size_no_overflow. omega. 
    intros. apply Mem.perm_implies with Freeable; auto with mem. 
    eapply Mem.perm_alloc_2; eauto.
    generalize stack_data_offset_valid bound_stack_data_stacksize; omega.
    red. intros. apply Zdivides_trans with 8. 
    destruct chunk; simpl; auto with align_4.
    apply fe_stack_data_aligned.
    intros.
      assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
      assert (~Mem.valid_block m1' sp') by eauto with mem.
      contradiction.
  intros [mu' [INJ2 [INCR [MAP1 [MAP2 [WD' [SMV' [LOCALLOC' RC']]]]]]]]. 
  assert (PERM: frame_perm_freeable m2' sp').
    red; intros. eapply Mem.perm_alloc_2; eauto.
  assert (SPlocalTgt': locBlocksTgt mu' sp' = true).
    eapply INCR. rewrite alloc_right_sm_locBlocksTgt. 
    destruct (eq_block sp' sp'); trivial. elim n; trivial.
  (* Store of parent *)
  exploit (store_index_succeeds m2' sp' FI_link parent). red; auto. auto. 
  intros [m3' STORE2].
  (* Store of retaddr *)
  exploit (store_index_succeeds m3' sp' FI_retaddr ra). red; auto. red; eauto with mem.
  intros [m4' STORE3].
  (* Saving callee-save registers *)
  assert (PERM4: frame_perm_freeable m4' sp').
    red; intros. eauto with mem. 
  exploit (save_callee_save_correct_eff (as_inj (restrict_sm mu' (vis mu')))). 
    instantiate (1 := rs1). instantiate (1 := call_regs ls).
    subst rs1. apply agree_regs_undef_regs. 
    apply agree_regs_call_regs. eapply agree_regs_inject_incr; try eassumption.
      rewrite restrict_sm_all.
      eapply intern_incr_restrict. apply WD'.
      eapply intern_incr_trans.
        eapply alloc_right_sm_intern_incr; eassumption.
        eassumption.
    apply wt_undef_regs. apply wt_call_regs. auto.
    eexact PERM4.
  rewrite <- LS1.
  intros [rs' [m5' [STEPS [ICS [FCS [OTHERS [STORES [PERM5 [AGREGS' FRESH4'5']]]]]]]]].
  rewrite restrict_sm_all in *.
  (* stores in frames *)
  assert (SIF: stores_in_frame sp' m2' m5').
    econstructor; eauto. 
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
    econstructor; eauto.
    rewrite size_type_chunk. apply offset_of_index_disj_stack_data_2; auto. red; auto.
  (* separation *)
  assert (SEP: forall b0 delta, as_inj mu' b0 = Some(sp', delta) -> b0 = sp /\ delta = fe_stack_data fe).
    intros. destruct (eq_block b0 sp). 
    subst b0. rewrite MAP1 in H; inv H; auto.
    rewrite MAP2 in H; auto. 
    assert (Mem.valid_block m1' sp'). eapply Mem.valid_block_inject_2; eauto.
    assert (~Mem.valid_block m1' sp') by eauto with mem.
    contradiction.
  (* Conclusions *)
  exists mu'; exists rs'; exists m2'; exists sp'; exists m3'; exists m4'; exists m5'.
  split. auto.
  (* store parent *)
  split. change Tint with (type_of_index FI_link). 
  change (fe_ofs_link fe) with (offset_of_index fe FI_link).
  apply store_stack_succeeds; auto. red; auto.
  (* store retaddr *)
  split. change Tint with (type_of_index FI_retaddr). 
  change (fe_ofs_retaddr fe) with (offset_of_index fe FI_retaddr).
  apply store_stack_succeeds; auto. red; auto.
  (* saving of registers *)
  split. eexact STEPS.
  (* agree_regs *)
  split. auto.
  (* agree frame *)
  split. constructor; intros.
    (* unused regs *)
    assert (~In r destroyed_at_call). 
      red; intros; elim H; apply caller_save_reg_within_bounds; auto.
    rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs. 
    apply AGCS; auto. red; intros; elim H0. 
    apply destroyed_at_function_entry_caller_save; auto.
    (* locals *)
    rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs. 
    apply index_contains_inj_undef; auto with stacking.
    (* outgoing *)
    rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs. 
    apply index_contains_inj_undef; auto with stacking.
    (* incoming *)
    rewrite LS1. rewrite LTL_undef_regs_slot. unfold call_regs.
    apply AGCS; auto. 
    (* parent *)
    apply OTHERS; auto. red; auto.
    eapply gso_index_contains; eauto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    red; auto.
    (* retaddr *)
    apply OTHERS; auto. red; auto.
    eapply gss_index_contains; eauto. red; auto.
    (* int callee save *)
    assert (~In r destroyed_at_call). 
      red; intros. eapply int_callee_save_not_destroyed; eauto.
    exploit ICS; eauto. rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs.
    rewrite AGCS; auto. 
    red; intros; elim H1. apply destroyed_at_function_entry_caller_save; auto.
    (* float callee save *)
    assert (~In r destroyed_at_call). 
      red; intros. eapply float_callee_save_not_destroyed; eauto.
    exploit FCS; eauto. rewrite LS1. rewrite LTL_undef_regs_others. unfold call_regs.
    rewrite AGCS; auto. 
    red; intros; elim H1. apply destroyed_at_function_entry_caller_save; auto.
    (* inj *)
    eapply restrictI_Some; try eassumption.
    destruct (joinD_Some _ _ _ _ _ MAP1) as [EXT | [_ LOC]].
      destruct (extern_DomRng _ WD' _ _ _ EXT).
      apply (extBlocksTgt_locBlocksTgt _ WD') in H0.
      rewrite SPlocalTgt' in H0; discriminate.
    destruct (local_DomRng _ WD' _ _ _ LOC).
      unfold vis; rewrite H. trivial.
    (* inj_unique *)
    destruct (restrictD_Some _ _ _ _ _ H). auto.
    (* valid sp *)
    eauto with mem.
    (* valid sp' *)
    eapply stores_in_frame_valid with (m := m2'); eauto with mem.
    (* bounds *)
    exploit Mem.perm_alloc_inv. eexact ALLOC. eauto. rewrite dec_eq_true. auto.
    (* perms *)
    auto.
    (* wt *)
    rewrite LS1. apply wt_undef_regs. apply wt_call_regs; auto.
  (* incr *)
  split. eapply intern_incr_trans; try eassumption.
         eapply alloc_right_sm_intern_incr.
  (* separated *)
  split. apply sm_locally_allocatedChar in LOCALLOC'.
         split; intros. destruct (eq_block b1 sp); subst.
            rewrite MAP1 in H0. inv H0. clear - ALLOC' ALLOC SMV.
            split.
            remember (DomSrc mu sp) as d; destruct d; trivial.
              apply eq_sym in Heqd. exfalso.
              eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC).
              eapply SMV. apply Heqd.
            remember (DomTgt mu b2) as d; destruct d; trivial.
              apply eq_sym in Heqd. exfalso.
              eapply (Mem.fresh_block_alloc _ _ _ _ _ ALLOC').
              eapply SMV. apply Heqd.
         rewrite (MAP2 _ n), alloc_right_sm_as_inj, H in H0. discriminate. 
       destruct LOCALLOC' as [DomSrc' [DomTgt' _]]; rewrite DomSrc', DomTgt'.
         rewrite alloc_right_sm_DomTgt, alloc_right_sm_DomSrc. 
         split; intros. rewrite H in H0; simpl in H0. rewrite freshloc_charT in H0. apply H0. 
         rewrite H, freshloc_irrefl in H0. 
         destruct (eq_block b2 sp'); subst; simpl in H0; try discriminate.
         eapply Mem.fresh_block_alloc; eassumption. 
  (* inject *)
  split. eapply stores_in_frame_inject; eauto.
  intros. exploit Mem.perm_alloc_inv. eexact ALLOC. eauto. rewrite dec_eq_true. auto.
  (* stores in frame *)
  split. auto.
  (*PRE' assertions*)
  intuition.
  clear ICS FCS OTHERS STORES PERM5 AGREGS' SIF.
    assert (freshloc m1' m5' = fun b' => eq_block b' sp').
      specialize (store_forward _ _ _ _ _ _ STORE2). intros FWD2.
      specialize (store_forward _ _ _ _ _ _ STORE3). intros FWD3.
      specialize (effstep_star_fwd _ _ _ _ _ _ _ STEPS). intros FWD4.
      apply extensionality; intros b'.
      specialize (alloc_forward _ _ _ _ _ ALLOC'); intros FWD1.
      rewrite <- (freshloc_trans _ m4'); try eassumption.
      rewrite FRESH4'5'.
      rewrite <- (freshloc_trans _ m3'); try eassumption.
      rewrite (store_freshloc _ _ _ _ _ _ STORE3).
      rewrite <- (freshloc_trans _ m2'); try eassumption.
      rewrite (store_freshloc _ _ _ _ _ _ STORE2).
      rewrite (freshloc_alloc _ _ _ _ _ ALLOC').
        repeat rewrite orb_false_r. trivial.
      eapply mem_forward_trans; eassumption.
      eapply mem_forward_trans; try eassumption.
        eapply mem_forward_trans; eassumption.          
    rewrite sm_locally_allocatedChar.
    rewrite sm_locally_allocatedChar in LOCALLOC'.
    destruct LOCALLOC' as [LASrc [LATgt [LAlocSrc [LAlocTgt [LAextSrc LAextTgt]]]]].
    rewrite LASrc, LATgt, LAlocSrc, LAlocTgt, LAextSrc, LAextTgt.
    clear LASrc LATgt LAlocSrc LAlocTgt LAextSrc LAextTgt.
    rewrite alloc_right_sm_DomSrc, alloc_right_sm_DomTgt,
            alloc_right_sm_locBlocksTgt, H.
            simpl. intuition.
            apply extensionality. intros b'. rewrite freshloc_irrefl, orb_false_r.
              apply orb_comm.
            apply extensionality. intros b'. rewrite freshloc_irrefl, orb_false_r.
              apply orb_comm.
  split; intros.
    eapply SMV'. assumption.
    eapply effstep_star_fwd; try eassumption.
      eapply store_forward; try eassumption.
      eapply store_forward; try eassumption.
      eapply SMV'. assumption.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable bound: frame_env -> Z.
Variable number: mreg -> Z.
Variable mkindex: Z -> frame_index.
Variable ty: typ.
Variable csregs: list mreg.
Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Hypothesis mkindex_valid:
  forall r, In r csregs -> number r < bound fe -> index_valid (mkindex (number r)).
Hypothesis mkindex_typ:
  forall z, type_of_index (mkindex z) = ty.
Hypothesis number_within_bounds:
  forall r, In r csregs ->
  (number r < bound fe <-> mreg_within_bounds b r).
Hypothesis mkindex_val:
  forall r,
  In r csregs -> number r < bound fe ->
  index_contains_inj j m sp (mkindex (number r)) (ls0 (R r)).

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> val_inject j (ls0 (R r)) (rs r).

Lemma restore_callee_save_regs_correct:
  forall l rs k lf,
  incl l csregs ->
  list_norepet l -> 
  agree_unused ls0 rs ->
  exists rs',
    corestep_star (Mach_eff_sem hf return_address_offset) tge
     (Mach_State cs fb (Vptr sp Int.zero)
        (restore_callee_save_regs bound number mkindex ty fe l k) rs lf) m
     (Mach_State cs fb (Vptr sp Int.zero) k rs' lf) m
  /\ (forall r, In r l -> val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists rs. intuition. apply corestep_star_zero.
  (* inductive case *)
  assert (R0: In a csregs). apply H; auto with coqlib.
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  exploit (mkindex_val a); auto. intros [v [X Y]].
  set (rs1 := Regmap.set a v rs).
  exploit (IHl rs1 k); eauto.
    red; intros. unfold rs1. unfold Regmap.set. destruct (RegEq.eq r a).
    subst r. auto.
    auto.
  intros [rs' [A [B [C D]]]].
  exists rs'. split.
  eapply corestep_star_trans.
    eapply corestep_star_one. 
      constructor. rewrite <- (mkindex_typ (number a)). apply index_contains_load_stack. eauto.   
    eauto.
  split. intros. destruct H2.
  subst r. rewrite C. unfold rs1. rewrite Regmap.gss. auto. inv H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  auto.
  (* no load takes place *)
  exploit (IHl rs k lf); auto.
  intros [rs' [A [B [C D]]]].
  exists rs'. split. assumption.
  split. intros. destruct H2.
  subst r. apply D. 
  rewrite <- number_within_bounds. auto. auto. auto.
  split. intros. simpl in H2. apply C. tauto.
  auto.
Qed.

Lemma restore_callee_save_regs_correct_eff:
  forall l rs k lf,
  incl l csregs ->
  list_norepet l -> 
  agree_unused ls0 rs ->
  exists rs',
    effstep_star (Mach_eff_sem hf return_address_offset) tge EmptyEffect
     (Mach_State cs fb (Vptr sp Int.zero)
        (restore_callee_save_regs bound number mkindex ty fe l k) rs lf) m
     (Mach_State cs fb (Vptr sp Int.zero) k rs' lf) m
  /\ (forall r, In r l -> val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
  induction l; intros; simpl restore_callee_save_regs.
  (* base case *)
  exists rs. intuition. apply effstep_star_zero.
  (* inductive case *)
  assert (R0: In a csregs). apply H; auto with coqlib.
  assert (R1: incl l csregs). eauto with coqlib.
  assert (R2: list_norepet l). inversion H0; auto.
  unfold restore_callee_save_reg.
  destruct (zlt (number a) (bound fe)).
  exploit (mkindex_val a); auto. intros [v [X Y]].
  set (rs1 := Regmap.set a v rs).
  exploit (IHl rs1 k); eauto.
    red; intros. unfold rs1. unfold Regmap.set. destruct (RegEq.eq r a).
    subst r. auto.
    auto.
  intros [rs' [A [B [C D]]]].
  exists rs'. split.
  eapply effstep_star_trans'.
    eapply effstep_star_one. 
      constructor. rewrite <- (mkindex_typ (number a)). apply index_contains_load_stack. eauto.   
    eauto.
    intuition.
  split. intros. destruct H2.
  subst r. rewrite C. unfold rs1. rewrite Regmap.gss. auto. inv H0; auto.
  auto.
  split. intros. simpl in H2. rewrite C. unfold rs1. apply Regmap.gso.
  apply sym_not_eq; tauto. tauto.
  auto.
  (* no load takes place *)
  exploit (IHl rs k lf); auto.
  intros [rs' [A [B [C D]]]].
  exists rs'. split. assumption.
  split. intros. destruct H2.
  subst r. apply D. 
  rewrite <- number_within_bounds. auto. auto. auto.
  split. intros. simpl in H2. apply C. tauto.
  auto.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall j ls ls0 m sp m' sp' pa ra cs fb rs k lf,
  agree_frame j ls ls0 m sp m' sp' pa ra ->
  agree_unused j ls0 rs ->
  exists rs',
    corestep_star (Mach_eff_sem hf return_address_offset) tge
      (Mach_State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs lf) m'
      (Mach_State cs fb (Vptr sp' Int.zero) k rs' lf) m'
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. 
    exploit (restore_callee_save_regs_correct 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int
             Tint
             int_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  intros. unfold mreg_within_bounds. split; intros.
  split; auto. destruct (zlt (index_float_callee_save r) 0).
  generalize (bound_float_callee_save_pos b). omega. 
  eelim int_float_callee_save_disjoint. eauto. 
  eapply index_float_callee_save_pos2. eauto. auto.
  destruct H2; auto. 
  eapply agree_saved_int; eauto. 
  apply incl_refl.
  apply int_callee_save_norepet.
  eauto.
  intros [rs1 [A [B [C D]]]].
  exploit (restore_callee_save_regs_correct 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float
             Tfloat
             float_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  intros. unfold mreg_within_bounds. split; intros.
  split; auto. destruct (zlt (index_int_callee_save r) 0).
  generalize (bound_int_callee_save_pos b). omega. 
  eelim int_float_callee_save_disjoint. 
  eapply index_int_callee_save_pos2. eauto. eauto. auto.
  destruct H2; auto. 
  eapply agree_saved_float; eauto. 
  apply incl_refl.
  apply float_callee_save_norepet.
  eexact D.
  intros [rs2 [P [Q [R S]]]].
  exists rs2.
  split. unfold restore_callee_save. eapply corestep_star_trans; eauto.
  split. intros. destruct H1.
    rewrite R. apply B; auto. red; intros. exploit int_float_callee_save_disjoint; eauto.
    apply Q; auto.
  intros. rewrite R; auto.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)

Lemma function_epilogue_correct:
  forall mu ls ls0 m sp m' sp' pa ra cs fb rs k m1 lf
  (RC: REACH_closed m (vis mu)) (WD: SM_wd mu)
  (SPlocalTgt: locBlocksTgt mu sp' = true),
  agree_regs (restrict (as_inj mu) (vis mu)) ls rs ->
  agree_frame (restrict (as_inj mu) (vis mu)) ls ls0 m sp m' sp' pa ra ->
  Mem.inject (as_inj mu) m m' ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ corestep_star (Mach_eff_sem hf return_address_offset) tge
       (Mach_State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs lf) m'
       (Mach_State cs fb (Vptr sp' Int.zero) k rs1 lf) m'
  /\ agree_regs (restrict (as_inj mu) (vis mu)) (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ Mem.inject (as_inj mu) m1 m1'.
Proof.
  intros.
  (* can free *)
  destruct (Mem.range_perm_free m' sp' 0 (fn_stacksize tf)) as [m1' FREE].
  rewrite unfold_transf_function; unfold fn_stacksize. red; intros.
  assert (EITHER: fe_stack_data fe <= ofs < fe_stack_data fe + Linear.fn_stacksize f
              \/ (ofs < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= ofs))
  by omega.
  destruct EITHER.
  replace ofs with ((ofs - fe_stack_data fe) + fe_stack_data fe) by omega.
  eapply Mem.perm_inject with (f :=restrict (as_inj mu) (vis mu)).
    eapply agree_inj; eauto.
    eapply inject_restrict; eassumption.
    (*eapply agree_frame_inject_incr. eassumption. essert (agree_frame j ls ls0 m sp m' sp' pa ra).*)
    eapply Mem.free_range_perm; eauto. omega.
  eapply agree_perm; eauto. 
  (* inject after free *)
  assert (INJ1: Mem.inject (as_inj mu) m1 m1').
  eapply Mem.free_inject with (l := (sp, 0, f.(Linear.fn_stacksize)) :: nil); eauto.
  simpl. rewrite H2. auto.
  intros. exploit agree_inj_unique; eauto.
            eapply restrictI_Some; try eassumption.
            unfold vis.
            destruct (joinD_Some _ _ _ _ _ H3) as [EXT | [_ LOC]]; clear H3.
               destruct (extern_DomRng _ WD _ _ _ EXT).
               rewrite (extBlocksTgt_locBlocksTgt _ WD _ H6) in SPlocalTgt. discriminate.
            destruct (local_DomRng _ WD _ _ _ LOC). rewrite H3; trivial.            
  intros [P Q]; subst b1 delta.
  exists 0; exists (Linear.fn_stacksize f); split. auto with coqlib.
  eapply agree_bounds. eauto. eapply Mem.perm_max. eauto.  
  (* can execute epilogue *)
  exploit restore_callee_save_correct; eauto.
    instantiate (1 := rs). red; intros. 
    rewrite <- (agree_unused_reg _ _ _ _ _ _ _ _ _ H0). auto. auto. 
  intros [rs1 [A [B C]]].
  (* conclusions *)
  exists rs1; exists m1'.
  split. rewrite unfold_transf_function; unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link); eauto with stacking.
  split. rewrite unfold_transf_function; unfold fn_retaddr_ofs. 
    eapply index_contains_load_stack with (idx := FI_retaddr); eauto with stacking.
  split. auto.
  split. eexact A.
  split. red; intros. unfold return_regs.
    generalize (register_classification r) (int_callee_save_not_destroyed r) 
               (float_callee_save_not_destroyed r); intros.
    destruct (in_dec mreg_eq r destroyed_at_call). 
    rewrite C; auto. 
    apply B. intuition. 
  split. apply agree_callee_save_return_regs.
  auto.
Qed.

Lemma restore_callee_save_correct_eff:
  forall j ls ls0 m sp m' sp' pa ra cs fb rs k lf,
  agree_frame j ls ls0 m sp m' sp' pa ra ->
  agree_unused j ls0 rs ->
  exists rs',
    effstep_star (Mach_eff_sem hf return_address_offset) tge EmptyEffect
      (Mach_State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs lf) m'
      (Mach_State cs fb (Vptr sp' Int.zero) k rs' lf) m'
  /\ (forall r, 
        In r int_callee_save_regs \/ In r float_callee_save_regs -> 
        val_inject j (ls0 (R r)) (rs' r))
  /\ (forall r, 
        ~(In r int_callee_save_regs) ->
        ~(In r float_callee_save_regs) ->
        rs' r = rs r).
Proof.
  intros. 
    exploit (restore_callee_save_regs_correct_eff 
             fe_num_int_callee_save
             index_int_callee_save
             FI_saved_int
             Tint
             int_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  intros. unfold mreg_within_bounds. split; intros.
  split; auto. destruct (zlt (index_float_callee_save r) 0).
  generalize (bound_float_callee_save_pos b). omega. 
  eelim int_float_callee_save_disjoint. eauto. 
  eapply index_float_callee_save_pos2. eauto. auto.
  destruct H2; auto. 
  eapply agree_saved_int; eauto. 
  apply incl_refl.
  apply int_callee_save_norepet.
  eauto.
  intros [rs1 [A [B [C D]]]].
  exploit (restore_callee_save_regs_correct_eff 
             fe_num_float_callee_save
             index_float_callee_save
             FI_saved_float
             Tfloat
             float_callee_save_regs
             j cs fb sp' ls0 m'); auto.
  intros. unfold mreg_within_bounds. split; intros.
  split; auto. destruct (zlt (index_int_callee_save r) 0).
  generalize (bound_int_callee_save_pos b). omega. 
  eelim int_float_callee_save_disjoint. 
  eapply index_int_callee_save_pos2. eauto. eauto. auto.
  destruct H2; auto. 
  eapply agree_saved_float; eauto. 
  apply incl_refl.
  apply float_callee_save_norepet.
  eexact D.
  intros [rs2 [P [Q [R S]]]].
  exists rs2.
  split. unfold restore_callee_save. eapply effstep_star_trans'; eauto.
  split. intros. destruct H1.
    rewrite R. apply B; auto. red; intros. exploit int_float_callee_save_disjoint; eauto.
    apply Q; auto.
  intros. rewrite R; auto.
Qed.

Lemma function_epilogue_correct_eff:
  forall mu ls ls0 m sp m' sp' pa ra cs fb rs k m1 lf
  (RC: REACH_closed m (vis mu)) (WD: SM_wd mu)
  (SPlocalTgt: locBlocksTgt mu sp' = true),
  agree_regs (restrict (as_inj mu) (vis mu)) ls rs ->
  agree_frame (restrict (as_inj mu) (vis mu)) ls ls0 m sp m' sp' pa ra ->
  Mem.inject (as_inj mu) m m' ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ effstep_star (Mach_eff_sem hf return_address_offset) tge EmptyEffect
       (Mach_State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs lf) m'
       (Mach_State cs fb (Vptr sp' Int.zero) k rs1 lf) m'
  /\ agree_regs (restrict (as_inj mu) (vis mu)) (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ Mem.inject (as_inj mu) m1 m1'.
Proof.
  intros.
  (* can free *)
  destruct (Mem.range_perm_free m' sp' 0 (fn_stacksize tf)) as [m1' FREE].
  rewrite unfold_transf_function; unfold fn_stacksize. red; intros.
  assert (EITHER: fe_stack_data fe <= ofs < fe_stack_data fe + Linear.fn_stacksize f
              \/ (ofs < fe_stack_data fe \/ fe_stack_data fe + Linear.fn_stacksize f <= ofs))
  by omega.
  destruct EITHER.
  replace ofs with ((ofs - fe_stack_data fe) + fe_stack_data fe) by omega.
  eapply Mem.perm_inject with (f :=restrict (as_inj mu) (vis mu)).
    eapply agree_inj; eauto.
    eapply inject_restrict; eassumption.
    (*eapply agree_frame_inject_incr. eassumption. essert (agree_frame j ls ls0 m sp m' sp' pa ra).*)
    eapply Mem.free_range_perm; eauto. omega.
  eapply agree_perm; eauto. 
  (* inject after free *)
  assert (INJ1: Mem.inject (as_inj mu) m1 m1').
  eapply Mem.free_inject with (l := (sp, 0, f.(Linear.fn_stacksize)) :: nil); eauto.
  simpl. rewrite H2. auto.
  intros. exploit agree_inj_unique; eauto.
            eapply restrictI_Some; try eassumption.
            unfold vis.
            destruct (joinD_Some _ _ _ _ _ H3) as [EXT | [_ LOC]]; clear H3.
               destruct (extern_DomRng _ WD _ _ _ EXT).
               rewrite (extBlocksTgt_locBlocksTgt _ WD _ H6) in SPlocalTgt. discriminate.
            destruct (local_DomRng _ WD _ _ _ LOC). rewrite H3; trivial.            
  intros [P Q]; subst b1 delta.
  exists 0; exists (Linear.fn_stacksize f); split. auto with coqlib.
  eapply agree_bounds. eauto. eapply Mem.perm_max. eauto.  
  (* can execute epilogue *)
  exploit restore_callee_save_correct_eff; eauto.
    instantiate (1 := rs). red; intros. 
    rewrite <- (agree_unused_reg _ _ _ _ _ _ _ _ _ H0). auto. auto. 
  intros [rs1 [A [B C]]].
  (* conclusions *)
  exists rs1; exists m1'.
  split. rewrite unfold_transf_function; unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link); eauto with stacking.
  split. rewrite unfold_transf_function; unfold fn_retaddr_ofs. 
    eapply index_contains_load_stack with (idx := FI_retaddr); eauto with stacking.
  split. auto.
  split. eexact A.
  split. red; intros. unfold return_regs.
    generalize (register_classification r) (int_callee_save_not_destroyed r) 
               (float_callee_save_not_destroyed r); intros.
    destruct (in_dec mreg_eq r destroyed_at_call). 
    rewrite C; auto. 
    apply B. intuition. 
  split. apply agree_callee_save_return_regs.
  auto.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariant *)

Inductive match_globalenvs (j: meminj) (bound: block) : Prop :=
  | match_globalenvs_intro
      (DOMAIN: forall b, Plt b bound -> j b = Some(b, 0))

      (*Lenb: added assumttion Genv.find_var_info 
        -I seem to have done this in Cminorgen, too, and it seems to be needed
         here in prove MacthAfterEtxernal*)
      (IMAGE: forall b1 b2 delta gv (GV: Genv.find_var_info ge b2 = Some gv),
               j b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)

      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).

(*Lenb: replaced (j:meminj) by mu, to enable the addition of (SPlocal:
  locBlocksTgt mu sp = true)*)

Inductive match_stacks mu (m m': mem) (sp0: block) (ls0: locset) : 
       list Linear.stackframe -> list stackframe -> signature -> block -> block -> Prop :=
  | match_stacks_empty: forall sg hi bound bound',
        Ple hi bound -> Ple hi bound' ->
        match_globalenvs (restrict (as_inj mu) (vis mu)) hi ->
        (*tailcall_possible sg ->*)
        match_stacks mu m m' sp0 ls0 nil nil sg bound bound'
  | match_stacks_cons: forall f sp ls c cs fb sp' ra c' cs' sg bound bound' trf
        (TAIL: is_tail c (Linear.fn_code f))
        (WTF: wt_function f = true)
        (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
        (TRF: transf_function f = OK trf)
        (TRC: transl_code (make_env (function_bounds f)) c = c')
        (TY_RA: Val.has_type ra Tint)
        (FRM: agree_frame f (restrict (as_inj mu) (vis mu)) ls 
              (parent_locset0 ls0 cs) m sp m' sp' (parent_sp0 sp0 cs') (parent_ra cs'))
        (ARGS: forall ofs ty,
           In (S Outgoing ofs ty) (loc_arguments sg) ->
           slot_within_bounds (function_bounds f) Outgoing ofs ty)
        (STK: match_stacks mu m m' sp0 ls0 cs cs' (Linear.fn_sig f) sp sp')
        (BELOW: Plt sp bound)
        (BELOW': Plt sp' bound')
        (SPLOCT: locBlocksTgt mu sp' = true) (*NEW*),
      match_stacks mu m m' sp0 ls0
                   (Linear.Stackframe f (Vptr sp Int.zero) ls c :: cs)
                   (Stackframe fb (Vptr sp' Int.zero) ra c' :: cs')
                   sg bound bound'.

(** Invariance with respect to change of bounds. *)

Lemma match_stacks_change_bounds:
  forall j m1 m' sp0 ls0 cs cs' sg bound bound',
  match_stacks j m1 m' sp0 ls0 cs cs' sg bound bound' ->
  forall xbound xbound',
  Ple bound xbound -> Ple bound' xbound' ->
  match_stacks j m1 m' sp0 ls0 cs cs' sg xbound xbound'.
Proof.
  induction 1; intros. 
  apply match_stacks_empty with hi; auto. apply Ple_trans with bound; eauto. 
    apply Ple_trans with bound'; eauto. 
  econstructor; eauto. eapply Plt_le_trans; eauto. eapply Plt_le_trans; eauto. 
Qed.

(** Invariance with respect to change of [m]. *)

Lemma match_stacks_change_linear_mem:
  forall j m1 m2 m' sp0 ls0 cs cs' sg bound bound',
  match_stacks j m1 m' sp0 ls0 cs cs' sg bound bound' ->
  (forall b, Plt b bound -> Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_stacks j m2 m' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_invariant; eauto. 
  apply IHmatch_stacks.
  intros. apply H0; auto. apply Plt_trans with sp; auto.
  intros. apply H1. apply Plt_trans with sp; auto. auto.
Qed.

(** Invariance with respect to change of [m']. *)

Lemma match_stacks_change_mach_mem:
  forall mu m m1' sp0 ls0 m2' cs cs' sg bound bound',
  match_stacks mu m m1' sp0 ls0 cs cs' sg bound bound' ->
  (forall b, Plt b bound' -> Mem.valid_block m1' b -> Mem.valid_block m2' b) ->
  (forall b ofs k p, Plt b bound' -> Mem.perm m1' b ofs k p -> Mem.perm m2' b ofs k p) ->
  (forall chunk b ofs v, 
     Plt b bound' -> 
     Mem.load chunk m1' b ofs = Some v -> 
     Mem.load chunk m2' b ofs = Some v) ->
  match_stacks mu m m2' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_invariant; eauto. 
  apply IHmatch_stacks. 
  intros; apply H0; auto. apply Plt_trans with sp'; auto. 
  intros; apply H1; auto. apply Plt_trans with sp'; auto. 
  intros; apply H2; auto. apply Plt_trans with sp'; auto. 
Qed.

(** A variant of the latter, for use with external calls *)

Lemma match_stacks_change_mem_extcall:
  forall mu m1 m2 m1' sp0 ls0 m2' cs cs' sg bound bound',
  match_stacks mu m1 m1' sp0 ls0 cs cs' sg bound bound' ->
  (forall b, Plt b bound -> Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall b, Plt b bound' -> Mem.valid_block m1' b -> Mem.valid_block m2' b) ->
  Mem.unchanged_on (local_out_of_reach mu m1) m1' m2' ->
  (*LENB: added:*) SM_wd mu ->
  match_stacks mu m2 m2' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; try eassumption.
    clear IHmatch_stacks.
    rewrite <- restrict_sm_all.  rewrite <- restrict_sm_all in FRM. 
    eapply agree_frame_extcall_invariant; eauto.
      eapply mem_unchanged_on_sub; try eassumption.
        unfold local_out_of_reach.
        rewrite restrict_sm_locBlocksTgt.
        rewrite restrict_sm_pubBlocksSrc. 
        rewrite restrict_sm_local. intros.
     intuition. 
       remember (pubBlocksSrc mu b0) as d.
       destruct d; apply eq_sym in Heqd.
       left. destruct (H7 b0 delta); intuition. 
        apply restrictI_Some. trivial.
          unfold vis. destruct (local_DomRng _ H4 _ _ _ H5). rewrite H8. trivial.
        rewrite H8 in Heqd; congruence.
       right; trivial. 
        eapply restrict_sm_WD; try eassumption. intuition.
       rewrite restrict_sm_locBlocksTgt; trivial.
  apply IHmatch_stacks. 
    intros; apply H0; auto. apply Plt_trans with sp; auto. 
    intros; apply H1. apply Plt_trans with sp; auto. auto.
    intros; apply H2; auto. apply Plt_trans with sp'; auto. 
    auto. assumption.
Qed.

Lemma match_stacks_change_mem_extcall':
  forall mu m1 m2 m1' sp0 ls0 m2' cs cs' sg bound bound',
  match_stacks mu m1 m1' sp0 ls0 cs cs' sg bound bound' ->
  (forall b, Plt b bound -> Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  (forall b ofs p, Plt b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall b, Plt b bound' -> Mem.valid_block m1' b -> Mem.valid_block m2' b) ->
  Mem.unchanged_on (loc_out_of_reach (restrict (as_inj mu) (vis mu)) m1) m1' m2' ->
  (*LENB: added:*) SM_wd mu ->
  match_stacks mu m2 m2' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; try eassumption.
    clear IHmatch_stacks.
    rewrite <- restrict_sm_all. rewrite <- restrict_sm_all in FRM. 
    eapply agree_frame_extcall_invariant'; eauto.
       rewrite restrict_sm_all, vis_restrict_sm. 
       rewrite restrict_sm_all, restrict_nest; trivial. 
    eapply restrict_sm_WD; try eassumption. trivial.
       rewrite restrict_sm_locBlocksTgt; trivial.
  apply IHmatch_stacks. 
    intros; apply H0; auto. apply Plt_trans with sp; auto. 
    intros; apply H1. apply Plt_trans with sp; auto. auto.
    intros; apply H2; auto. apply Plt_trans with sp'; auto. 
    auto. assumption.
Qed.

(** Invariance with respect to change of [j]. *)

Lemma match_stacks_replace_locals PS PT:
  forall mu m m' sp0 ls0 cs cs' sg bound bound',
  match_stacks mu m m' sp0 ls0 cs cs' sg bound bound' ->
  match_stacks (replace_locals mu PS PT) m m' sp0 ls0 cs cs' sg bound bound'.
Proof.
  intros.
   induction H; try econstructor; eauto.
     rewrite replace_locals_as_inj, replace_locals_vis. trivial.
     rewrite replace_locals_as_inj, replace_locals_vis. trivial.
     eauto. rewrite replace_locals_locBlocksTgt. trivial.
Qed.

Lemma match_stacks_change_meminj_intern:
  forall mu mu' m m' sp0 ls0 m1 m1',
  intern_incr mu mu' ->
  sm_inject_separated mu mu' m1 m1' ->
  forall cs cs' sg bound bound',
  match_stacks mu m m' sp0 ls0 cs cs' sg bound bound' ->
  Ple bound' (Mem.nextblock m1') -> SM_wd mu -> SM_wd mu' ->
  match_stacks mu' m m' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 3; intros.
  apply match_stacks_empty with hi; auto.
  inv H3. constructor; eauto.
    intros. specialize (DOMAIN _ H3).
      eapply intern_incr_restrict; eassumption. 
  intros. red in H0.
    case_eq (restrict (as_inj mu) (vis mu) b1).
    intros [b' delta'] EQ.
      apply intern_incr_restrict in H; trivial.
      rewrite (H _ _ _ EQ) in H3. inv H3. eauto.
  intros EQ. specialize (DOMAIN _ H7).
             destruct (restrictD_Some _ _ _ _ _ H3); clear H3. 
             destruct (restrictD_Some _ _ _ _ _ DOMAIN); clear DOMAIN. 
             destruct (restrictD_None' _ _ _ EQ); clear EQ.
               destruct H0 as [AI [DD TT]].
               destruct (AI _ _ _ H11 H8).
               assert (DomTgt mu b2 = true).
                 eapply as_inj_DomRng; eassumption.
               rewrite H13 in H12. discriminate. 
             destruct H11 as [? [? [? ?]]].
               assert (as_inj mu' b1 = Some (x, x0)).
                  eapply intern_incr_as_inj; eassumption.
               rewrite H13 in H8; inv H8.
               rewrite (intern_incr_vis_inv _ _ H5 H6 H _ _ _ H11 H9) in H12.
               discriminate.  
  econstructor; eauto. 
  eapply agree_frame_inject_incr; eauto.
    eapply intern_incr_restrict; eassumption.
    instantiate (1:=m1'). instantiate (1:=m1).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H6); clear H6.
         destruct (restrictD_None' _ _ _ H5); clear H5.
           red in H0. destruct H0 as [HH1 HH2]. 
           destruct (HH1 _ _ _ H6 H7). 
           destruct (as_inj_DomRng _ _ _ _ H7); trivial.
           split; eapply HH2; eassumption.
         destruct H6 as [? [? [? ?]]].    
           rewrite (intern_incr_vis_inv _ _ H3 H4 H _ _ _ H5 H8) in H6.
               discriminate.
    red. eapply Plt_le_trans; eauto.  
    apply IHmatch_stacks; trivial. apply Ple_trans with bound'; auto. apply Plt_Ple; auto.
    eapply H. assumption.
Qed.

Lemma match_stacks_change_meminj_extern:
  forall mu mu' m m' sp0 ls0 m1 m1',
  extern_incr mu mu' ->
  sm_inject_separated mu mu' m1 m1' ->
  forall cs cs' sg bound bound',
  match_stacks mu m m' sp0 ls0 cs cs' sg bound bound' ->
  Ple bound' (Mem.nextblock m1') -> SM_wd mu -> SM_wd mu' ->
  match_stacks mu' m m' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 3; intros.
  apply match_stacks_empty with hi; auto.
  inv H3. constructor; eauto.
    intros. specialize (DOMAIN _ H3). 
    eapply extern_incr_restrict; eassumption. 
  intros.
    case_eq (restrict (as_inj mu) (vis mu) b1).
    intros [b' delta'] EQ.
      apply extern_incr_restrict in H; trivial.
      rewrite (H _ _ _ EQ) in H3. inv H3. eauto.
  intros EQ. specialize (DOMAIN _ H7).
             destruct (restrictD_Some _ _ _ _ _ H3); clear H3. 
             destruct (restrictD_Some _ _ _ _ _ DOMAIN); clear DOMAIN. 
             destruct (restrictD_None' _ _ _ EQ); clear EQ.
               destruct H0 as [AI [DD TT]].
               destruct (AI _ _ _ H11 H8).
               assert (DomTgt mu b2 = true).
                 eapply as_inj_DomRng; eassumption.
               rewrite H13 in H12. discriminate. 
             destruct H11 as [? [? [? ?]]].
               assert (as_inj mu' b1 = Some (x, x0)).
                  eapply extern_incr_as_inj; eassumption.
               rewrite H13 in H8; inv H8.
               rewrite (extern_incr_vis _ _ H) in H12.
               rewrite H12 in H9.
               discriminate.  
  econstructor; eauto. 
  eapply agree_frame_inject_incr; eauto.
    eapply extern_incr_restrict; eassumption.
    instantiate (1:=m1'). instantiate (1:=m1).
    red; intros. destruct (restrictD_Some _ _ _ _ _ H6); clear H6.
         destruct (restrictD_None' _ _ _ H5); clear H5.
           red in H0. destruct H0 as [HH1 HH2]. 
           destruct (HH1 _ _ _ H6 H7). 
           destruct (as_inj_DomRng _ _ _ _ H7); trivial.
           split; eapply HH2; eassumption.
         destruct H6 as [? [? [? ?]]].    
               rewrite (extern_incr_vis _ _ H) in H6.
               rewrite H6 in H8.
               discriminate.
    red. eapply Plt_le_trans; eauto.  
    apply IHmatch_stacks; trivial. apply Ple_trans with bound'; auto. apply Plt_Ple; auto.
    assert (locBlocksTgt mu = locBlocksTgt mu') by eapply H.
    rewrite <- H5; assumption.
Qed.

(** Preservation by parallel stores in Linear and Mach. *)

Lemma match_stacks_parallel_stores:
  forall j m m' sp0 ls0 chunk addr addr' v v' m1 m1',
  Mem.inject (restrict (as_inj j) (vis j)) m m' ->
  val_inject (restrict (as_inj j) (vis j)) addr addr' ->
  Mem.storev chunk m addr v = Some m1 ->
  Mem.storev chunk m' addr' v' = Some m1' ->
  forall cs cs' sg bound bound',
  match_stacks j m m' sp0 ls0 cs cs' sg bound bound' ->
  match_stacks j m1 m1' sp0 ls0 cs cs' sg bound bound'.
Proof.
  intros until m1'. intros MINJ VINJ STORE1 STORE2.
  induction 1.
  econstructor; eauto.
  econstructor; eauto.
  eapply agree_frame_parallel_stores; eassumption. 
Qed.

(** Invariance by external calls. *)
Lemma match_stack_change_extcall:
  forall m1 m2 m1' m2' sp0 ls0 j j',
(*  external_call ec ge args m1 t res m2 
    replaced by forward:*) mem_forward m1 m2 ->
(*  external_call ec ge args' m1' t' res' m2'
    replaced by forward:*) mem_forward m1' m2' ->
  extern_incr j j' -> SM_wd j -> SM_wd j' ->
  sm_inject_separated j j' m1 m1' ->
  Mem.unchanged_on (local_out_of_reach j m1) m1' m2' ->
  forall cs cs' sg bound bound',
  match_stacks j m1 m1' sp0 ls0 cs cs' sg bound bound' ->
  Ple bound (Mem.nextblock m1) -> Ple bound' (Mem.nextblock m1') ->
  match_stacks j' m2 m2' sp0 ls0 cs cs' sg bound bound'.
Proof.
  intros. 
  eapply match_stacks_change_meminj_extern; eauto. 
  eapply match_stacks_change_mem_extcall; eauto.
  intros. eapply H; eassumption.
  intros. eapply H; try eassumption.
    unfold Mem.valid_block. xomega.
  intros. eapply H0; eassumption.
Qed.

Lemma match_stack_change_extcall_intern:
  forall m1 m2 m1' m2' sp0 ls0 mu mu',
(*  external_call ec ge args m1 t res m2 
    replaced by forward:*) mem_forward m1 m2 ->
(*  external_call ec ge args' m1' t' res' m2'
    replaced by forward:*) mem_forward m1' m2' ->
  intern_incr mu mu' -> SM_wd mu -> SM_wd mu' ->
  sm_inject_separated mu mu' m1 m1' ->
  Mem.unchanged_on (loc_out_of_reach (restrict (as_inj mu) (vis mu)) m1) m1' m2' ->
  forall cs cs' sg bound bound',
  match_stacks mu m1 m1' sp0 ls0 cs cs' sg bound bound' ->
  Ple bound (Mem.nextblock m1) -> Ple bound' (Mem.nextblock m1') ->
  match_stacks mu' m2 m2' sp0 ls0 cs cs' sg bound bound'.
Proof.
  intros. 
  eapply match_stacks_change_meminj_intern; eauto. 
  eapply match_stacks_change_mem_extcall'; eauto.
  intros. eapply H; eassumption.
  intros. eapply H; try eassumption.
    unfold Mem.valid_block. xomega.
  intros. eapply H0; eassumption.
Qed.

(** Invariance with respect to change of signature *)

Lemma match_stacks_change_sig:
  forall sg1 j m m' sp0 ls0 cs cs' sg bound bound',
  match_stacks j m m' sp0 ls0 cs cs' sg bound bound' ->
  tailcall_possible sg1 ->
  match_stacks j m m' sp0 ls0 cs cs' sg1 bound bound'.
Proof.
  induction 1; intros.
  econstructor; eauto. 
  econstructor; eauto. intros. elim (H0 _ H1).
Qed.

(** [match_stacks] implies [match_globalenvs], which implies [meminj_preserves_globals]. *)

Lemma match_stacks_globalenvs:
  forall mu m m' sp0 ls0 cs cs' sg bound bound',
  match_stacks mu m m' sp0 ls0 cs cs' sg bound bound' ->
  exists hi, match_globalenvs (restrict (as_inj mu) (vis mu)) hi.
Proof.
  induction 1. exists hi; auto. auto.
Qed.

Lemma match_stacks_preserves_globals:
  forall j m m' sp0 ls0 cs cs' sg bound bound',
  match_stacks j m m' sp0 ls0 cs cs' sg bound bound' ->
  meminj_preserves_globals ge (restrict (as_inj j) (vis j)).
Proof.
  intros. exploit match_stacks_globalenvs; eauto. intros [hi MG]. inv MG.
  split. eauto. split. eauto. intros. symmetry. eauto. 
Qed.

(** Typing properties of [match_stacks]. *)

Lemma match_stacks_wt_locset:
  forall j m m' sp0 ls0 cs cs' sg bound bound' ls,
  match_stacks j m m' sp0 ls0 cs cs' sg bound bound' ->
  wt_locset (call_regs' ls) -> 
  wt_locset (parent_locset0 ls cs).
Proof.
  induction 1; simpl; auto.
  inv FRM; auto.
Qed.

Lemma match_stacks_type_sp:
  forall j m m' sp0 ls0 cs cs' sg bound bound',
  match_stacks j m m' sp0 ls0 cs cs' sg bound bound' ->
  Val.has_type (parent_sp0 sp0 cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma match_stacks_type_retaddr:
  forall j m m' sp0 ls0 cs cs' sg bound bound',
  match_stacks j m m' sp0 ls0 cs cs' sg bound bound' ->
  Val.has_type (parent_ra cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

(** Preservation by restriction *)
  
Lemma match_stacks_restrict mu m m' sp0 ls0 cs cs' sg bound bound' X:
  forall (MS: match_stacks mu m m' sp0 ls0 cs cs' sg bound bound')
         (HX : forall b : block, vis mu b = true -> X b = true)
         (WDR : SM_wd (restrict_sm mu X)),
      match_stacks (restrict_sm mu X) m m' sp0 ls0 cs cs' sg bound bound'.
Proof.
  induction 1; simpl; econstructor; try eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption. 
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; eassumption. 
  eapply IHMS; eassumption.
  rewrite restrict_sm_locBlocksTgt. assumption.
Qed.

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_fold_right:
  forall (A: Type) (fn: A -> Mach.code -> Mach.code) lbl,
  (forall x k, Mach.find_label lbl (fn x k) = Mach.find_label lbl k) ->  forall (args: list A) k,
  Mach.find_label lbl (List.fold_right fn k args) = Mach.find_label lbl k.
Proof.
  induction args; simpl. auto. 
  intros. rewrite H. auto.
Qed.

Remark find_label_save_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (save_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold save_callee_save, save_callee_save_int, 
                 save_callee_save_float, save_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold save_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold save_callee_save_reg.  
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Remark find_label_restore_callee_save:
  forall fe lbl k,
  Mach.find_label lbl (restore_callee_save fe k) = Mach.find_label lbl k.
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, 
                 restore_callee_save_float, restore_callee_save_regs.
  repeat rewrite find_label_fold_right. reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_float_callee_save x) (fe_num_float_callee_save fe));
  intro; reflexivity.
  intros. unfold restore_callee_save_reg. 
  case (zlt (index_int_callee_save x) (fe_num_int_callee_save fe));
  intro; reflexivity.
Qed.

Lemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr fe i (transl_code fe c).
Proof.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
  auto.
  rewrite transl_code_eq. 
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  rewrite find_label_restore_callee_save. auto.
  simpl. case (peq lbl l); intro. reflexivity. auto.
  rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) = 
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl. 
  unfold transl_body. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c', 
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save_regs:
  forall bound number mkindex ty fe csl k,
  is_tail k (save_callee_save_regs bound number mkindex ty fe csl k).
Proof.
  induction csl; intros; simpl. auto with coqlib.
  unfold save_callee_save_reg. destruct (zlt (number a) (bound fe)). 
  constructor; auto. auto.
Qed.

Lemma is_tail_save_callee_save:
  forall fe k,
  is_tail k (save_callee_save fe k).
Proof.
  intros. unfold save_callee_save, save_callee_save_int, save_callee_save_float.
  eapply is_tail_trans; apply is_tail_save_callee_save_regs.
Qed.

Lemma is_tail_restore_callee_save_regs:
  forall bound number mkindex ty fe csl k,
  is_tail k (restore_callee_save_regs bound number mkindex ty fe csl k).
Proof.
  induction csl; intros; simpl. auto with coqlib.
  unfold restore_callee_save_reg. destruct (zlt (number a) (bound fe)). 
  constructor; auto. auto.
Qed.

Lemma is_tail_restore_callee_save:
  forall fe k,
  is_tail k (restore_callee_save fe k).
Proof.
  intros. unfold restore_callee_save, restore_callee_save_int, restore_callee_save_float.
  eapply is_tail_trans; apply is_tail_restore_callee_save_regs.
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq. 
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl. 
  unfold transl_body. eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_transf_partial transf_fundef _ TRANSF).

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  exists tf,
  Genv.find_funct_ptr tge v = Some tf /\ transf_fundef f = OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto. 
  auto.
Qed.

Lemma find_function_translated:
  forall mu ls rs m m' sp0 ls0 cs cs' sg bound bound' ros f,
  agree_regs (restrict (as_inj mu) (vis mu)) ls rs ->
  match_stacks mu m m' sp0 ls0 cs cs' sg bound bound' ->
  Linear.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG MS FF.
  exploit match_stacks_globalenvs; eauto. intros [hi MG]. 
  destruct ros; simpl in FF.
  exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF. 
  rewrite Genv.find_funct_find_funct_ptr in FF. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  inv MG. rewrite DOMAIN in H2. inv H2. simpl. auto. eapply FUNCTIONS; eauto. 
  destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate. 
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl. 
  rewrite symbols_preserved. auto.
Qed.

Lemma GDE_lemma: genvs_domain_eq ge tge.
Proof.
    unfold genvs_domain_eq, genv2blocks.
    simpl; split; intros.
     split; intros; destruct H as [id Hid].
      rewrite <- symbols_preserved in Hid.
      exists id; assumption.
     rewrite symbols_preserved in Hid.
      exists id; assumption.
     split; intros; destruct H as [id Hid].
      rewrite <- varinfo_preserved in Hid.
      exists id; assumption.
     rewrite varinfo_preserved in Hid.
      exists id; assumption.
Qed.

(** Preservation of the arguments to an external call. *)

Section EXT_ARGUMENTS_FUN.
Variable rs: regset.
Variable cs': list stackframe.
Variable sg: signature.
Variable m1: mem.
Variable m2: mem.

(*NEW*)
Lemma transl_external_argument_fun:
  forall l (Hl: In l (loc_arguments sg)) sp0
  (HH: forall ofs ty ch, In (S Outgoing ofs ty) (loc_arguments sg) ->
          Mem.loadv ch m1 (Val.add (parent_sp0 sp0 cs') (Vint (Int.repr (fe_ofs_arg + 4 * ofs)))) =
          Mem.loadv ch m2 (Val.add (parent_sp0 sp0 cs') (Vint (Int.repr (fe_ofs_arg + 4 * ofs)))))
  v1 (EC1: extcall_arg rs m1 (parent_sp0 sp0 cs') l v1)
  v2 (EC2: extcall_arg rs m2 (parent_sp0 sp0 cs') l v2), v1=v2. 
Proof.
  intros.
  assert (loc_argument_acceptable l). apply loc_arguments_acceptable with sg; auto.
  inv EC1; inv EC2; trivial.
  unfold load_stack in *.
  rewrite (HH _ _ (chunk_of_type ty) Hl) in H0.
  rewrite H0 in H7. inv H7; trivial.
Qed.

(*NEW*)
Lemma transl_external_arguments_rec_fun:
  forall locs (Hlocs: incl locs (loc_arguments sg)) sp0
  (HH: forall ofs ty ch, In (S Outgoing ofs ty) (loc_arguments sg) ->
          Mem.loadv ch m1 (Val.add (parent_sp0 sp0 cs') (Vint (Int.repr (fe_ofs_arg + 4 * ofs)))) =
          Mem.loadv ch m2 (Val.add (parent_sp0 sp0 cs') (Vint (Int.repr (fe_ofs_arg + 4 * ofs)))))
  vl1 (VL1: list_forall2 (extcall_arg rs m1 (parent_sp0 sp0 cs')) locs vl1)
  vl2 (VL2: list_forall2 (extcall_arg rs m2 (parent_sp0 sp0 cs')) locs vl2),
  vl1 = vl2.  
Proof.
  induction locs; simpl; intros.
  inv VL1; inv VL2; trivial.
  inv VL1; inv VL2; trivial.
  f_equal. 
    eapply transl_external_argument_fun.
    instantiate (1:=a). eapply Hlocs. left; trivial.
    eauto. assumption. assumption. 
  eapply IHlocs; trivial.
    red; intros. eapply Hlocs. right; trivial.
    eauto. auto. auto.
Qed.

(*NEW*)
Lemma transl_external_arguments_fun: forall vl1 vl2 sp0
      (HH: forall ofs ty ch, In (S Outgoing ofs ty) (loc_arguments sg) ->
        Mem.loadv ch m1 (Val.add (parent_sp0 sp0 cs') (Vint (Int.repr (fe_ofs_arg + 4 * ofs)))) =
        Mem.loadv ch m2 (Val.add (parent_sp0 sp0 cs') (Vint (Int.repr (fe_ofs_arg + 4 * ofs)))))
      (EA1: extcall_arguments rs m1 (parent_sp0 sp0 cs') sg vl1)
      (EA2: extcall_arguments rs m2 (parent_sp0 sp0 cs') sg vl2), vl1=vl2.
Proof.
  unfold extcall_arguments. intros. 
  eapply transl_external_arguments_rec_fun; try eassumption.
  auto with coqlib.
Qed.

End EXT_ARGUMENTS_FUN.

Section EXTERNAL_ARGUMENTS.

Variable mu: SM_Injection.
Variables m m': mem.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': block.
Variable sp0: block.
Variable ls0: locset.
Hypothesis MS: match_stacks mu m m' sp0 ls0 cs cs' sg bound bound'.
Variables ls ls': locset.
Variable rs: regset.
Hypothesis AGR: agree_regs (restrict (as_inj mu) (vis mu)) ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset0 ls' cs).
Hypothesis INCTX: (Zlength cs > 0 \/ tailcall_possible sg).

Lemma transl_external_argument:
  forall l,
  In l (loc_arguments sg) ->
  exists v, 
    extcall_arg rs m' (parent_sp0 sp0 cs') l v 
    /\ val_inject (restrict (as_inj mu) (vis mu)) (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l). apply loc_arguments_acceptable with sg; auto.
  destruct l; red in H0.
  exists (rs r); split. constructor. auto. 
  destruct sl; try contradiction.
  inv MS.
  simpl parent_sp0. 
  destruct INCTX as [H4|H4]. unfold Zlength in H4. simpl in H4. omega.
  solve[elim (H4 _ H)].
  unfold parent_sp0.
  assert (slot_valid f Outgoing pos ty = true).
    exploit loc_arguments_acceptable; eauto. intros [A B]. 
    unfold slot_valid. unfold proj_sumbool. rewrite zle_true. 
    destruct ty; reflexivity || congruence. omega.
  assert (slot_within_bounds (function_bounds f) Outgoing pos ty).
    eauto.
  exploit agree_outgoing; eauto. intros [v [A B]].
  exists v; split.
  constructor. 
  eapply index_contains_load_stack with (idx := FI_arg pos ty); eauto. 
  red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
  list_forall2 (extcall_arg rs m' (parent_sp0 sp0 cs')) locs vl
  /\ val_list_inject (restrict (as_inj mu) (vis mu)) ls##locs vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
  extcall_arguments rs m' (parent_sp0 sp0 cs') sg vl /\
  val_list_inject (restrict (as_inj mu) (vis mu)) (ls ## (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments. 
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** Preservation of the arguments to an annotation. *)

Section ANNOT_ARGUMENTS.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable j: meminj.
Variables m m': mem.
Variables ls ls0: locset.
Variable rs: regset.
Variables sp sp': block.
Variables parent retaddr: val.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGF: agree_frame f j ls ls0 m sp m' sp' parent retaddr.

Lemma transl_annot_param_correct:
  forall l,
  loc_valid f l = true ->
  match l with S sl ofs ty => slot_within_bounds b sl ofs ty | _ => True end ->
  exists v, annot_arg rs m' (Vptr sp' Int.zero) (transl_annot_param fe l) v
         /\ val_inject j (ls l) v.
Proof.
  intros. destruct l; simpl in H.
(* reg *)
  exists (rs r); split. constructor. auto.
(* stack *) 
  destruct sl; try discriminate. 
  exploit agree_locals; eauto. intros [v [A B]]. inv A. 
  exists v; split. constructor. rewrite Zplus_0_l. auto. auto.
Qed.

Lemma transl_annot_params_correct:
  forall ll,
  forallb (loc_valid f) ll = true ->
  (forall sl ofs ty, In (S sl ofs ty) ll -> slot_within_bounds b sl ofs ty) ->
  exists vl,
     annot_arguments rs m' (Vptr sp' Int.zero) (map (transl_annot_param fe) ll) vl
  /\ val_list_inject j (map ls ll) vl.
Proof.
  induction ll; simpl; intros. 
  exists (@nil val); split; constructor.
  InvBooleans. 
  exploit (transl_annot_param_correct a). auto. destruct a; auto. 
  intros [v1 [A B]].
  exploit IHll. auto. auto. 
  intros [vl [C D]].
  exists (v1 :: vl); split; constructor; auto.
Qed.

End ANNOT_ARGUMENTS.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset0 ls s] of the current function and its caller,
  and on the Mach side the register set [rs] and the contents of
  the memory area corresponding to the stack frame.
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Memory injection between the Linear and the Mach memory states.
- Well-typedness of [f].
*)

(* Lenb: added parameter mu, and removed MINJ clauses (they're in MATCH now)
   Adapted type from Linear.state -> Mach.state -> Prop to
   Linear_core -> mem -> Mach_core -> mem -> Prop *)

(* We distinguish between internal and external calls (cf. introduction
   of constructor Mach_CallstateOut). *)

Inductive match_states mu: Linear_core -> mem -> Mach_core -> mem -> Prop:=
  | match_states_intro:
      forall cs f sp c ls ls0 f0 m cs' fb sp' rs m' tf args0 tys0 sp0
        (STACKS: match_stacks mu m m' sp0 ls0 cs cs' f.(Linear.fn_sig) sp sp')
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (WTF: wt_function f = true)
        (AGREGS: agree_regs (restrict (as_inj mu) (vis mu)) ls rs)
        (AGFRAME: agree_frame f (restrict (as_inj mu) (vis mu)) ls 
                    (parent_locset0 ls0 cs) m sp m' sp' 
                    (parent_sp0 sp0 cs') (parent_ra cs'))
        (TAIL: is_tail c (Linear.fn_code f))
        (SPLOCT: locBlocksTgt mu sp' = true) 
        (AGARGS: agree_args (Internal f0) mu args0 tys0 cs ls0 m' sp0)
        (SPNEQ: sp0<>sp')
        (AGINITF: match cs with nil => f=f0 
                                    \/ tailcall_possible (Linear.fn_sig f)
                              | _::_ => True end),
      match_states mu
        (Linear_State cs f (Vptr sp Int.zero) c ls (Linear_coop.mk_load_frame ls0 f0)) m
        (Mach_State cs' fb (Vptr sp' Int.zero) 
                    (transl_code (make_env (function_bounds f)) c) rs 
                    (mk_load_frame sp0 args0 tys0)) m'

  | match_states_init:
      forall f tf fb ls args tys m m'
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (WTLS: wt_locset ls)
        (NOREGS: forall r, ls (R r) = Vundef)
        (NOLOCSIN: forall slt ofs ty, 
                   slt = Local \/ slt = Incoming -> ls (S slt ofs ty) = Vundef)
        (AGARGS: agree_args_match_aux (restrict (as_inj mu) (vis mu)) (call_regs ls) 0 args tys)
        (TYSEQ: sig_args (Linear.fn_sig f) = tys)
        (ARGS0: exists args0, val_list_inject (restrict (as_inj mu) (vis mu)) args0 args
                           /\ ls = init_locset tys args0)
        (VALSDEF: vals_defined args=true)
        (HASTY: Val.has_type_list args tys),
      match_states mu (Linear_CallstateIn nil (Internal f) ls (Linear_coop.mk_load_frame ls f)) m 
                      (Mach_CallstateIn fb args tys) m'

  | match_states_call_intern:
      forall cs f ls ls0 f0 m cs' fb rs m' tf args0 tys0 sp0
        (STACKS: match_stacks mu m m' sp0 ls0 cs cs' 
                   (Linear.funsig f) (Mem.nextblock m) (Mem.nextblock m'))
        (TRANSL: transf_fundef f = OK (Internal tf))
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs (restrict (as_inj mu) (vis mu)) ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset0 ls0 cs))
        (AGARGS: agree_args (Internal f0) mu args0 tys0 cs ls0 m' sp0)
        (AGINITF: match cs with nil => f=Internal f0 
                                    \/ tailcall_possible (Linear.funsig f) 
                              | _::_ => True end), 
      match_states mu (Linear_Callstate cs f ls (Linear_coop.mk_load_frame ls0 f0)) m
                      (Mach_Callstate cs' fb rs (mk_load_frame sp0 args0 tys0)) m'

  | match_states_call_extern:
      forall cs f ls ls0 f0 m cs' fb rs m' tf args0 tys0 sp0
        (STACKS: match_stacks mu m m' sp0 ls0 cs cs' 
                   (Linear.funsig f) (Mem.nextblock m) (Mem.nextblock m'))
        (TRANSL: transf_fundef f = OK (External tf))
        (FIND: Genv.find_funct_ptr tge fb = Some (External tf))
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs (restrict (as_inj mu) (vis mu)) ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset0 ls0 cs))
        args (GETARGS: extcall_arguments rs m' (parent_sp0 sp0 cs') (ef_sig tf) args)
        (AGARGS: agree_args (Internal f0) mu args0 tys0 cs ls0 m' sp0)
        (INCTX: Zlength cs > 0 \/ tailcall_possible (Linear.funsig f)),
      match_states mu (Linear_Callstate cs f ls (Linear_coop.mk_load_frame ls0 f0)) m
                      (Mach_CallstateOut cs' fb tf args rs (mk_load_frame sp0 args0 tys0)) m'

  | match_states_return:
      forall cs ls ls0 f0 m cs' retty rs m' sg args0 tys0 sp0
        (STACKS: match_stacks mu m m' sp0 ls0 cs cs' sg (Mem.nextblock m) (Mem.nextblock m'))
        (WTLS: wt_locset ls)
        (AGREGS: agree_regs (restrict (as_inj mu) (vis mu)) ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset0 ls0 cs))
        (AGARGS: agree_args (Internal f0) mu args0 tys0 cs ls0 m' sp0),
      match_states mu (Linear_Returnstate cs retty ls (Linear_coop.mk_load_frame ls0 f0)) m
                      (Mach_Returnstate cs' retty rs (mk_load_frame sp0 args0 tys0)) m'.

Lemma match_states_restrict mu c1 m1 c2 m2 X: forall 
          (MS : match_states mu c1 m1 c2 m2)
          (HX : forall b : block, vis mu b = true -> X b = true)
          (WD : SM_wd mu)
          (WDR : SM_wd (restrict_sm mu X)),
      match_states (restrict_sm mu X) c1 m1 c2 m2.
Proof. intros.
inv MS.
econstructor; try eassumption.
  eapply match_stacks_restrict; eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; eassumption.
  rewrite restrict_sm_locBlocksTgt. assumption.
  inv AGARGS. constructor; auto. intros.
  destruct agree_args_inj0 as [x H]. 
    exists x. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; auto.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest. auto. auto.
    rewrite restrict_sm_all. intros. 
    apply restrictD_Some in H. destruct H. solve[eapply agree_sp_fresh0; eauto].
    solve[rewrite restrict_sm_locBlocksTgt; auto].
econstructor; try eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
econstructor; try eassumption.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.
auto.
econstructor; try eassumption.
  eapply match_stacks_restrict; eassumption. 
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption. 
  inv AGARGS. constructor; auto. intros.
  destruct agree_args_inj0 as [x H]. 
    exists x. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; auto.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest. auto. auto.
    rewrite restrict_sm_all. intros. 
    apply restrictD_Some in H. destruct H. solve[eapply agree_sp_fresh0; eauto].
    solve[rewrite restrict_sm_locBlocksTgt; auto].
econstructor; try eassumption.
  eapply match_stacks_restrict; eassumption. 
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.  
  inv AGARGS. constructor; auto. intros.
  destruct agree_args_inj0 as [x H]. 
    exists x. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; auto.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest. auto. auto.
    rewrite restrict_sm_all. intros. 
    apply restrictD_Some in H. destruct H. solve[eapply agree_sp_fresh0; eauto].
    solve[rewrite restrict_sm_locBlocksTgt; auto].
econstructor; try eassumption.
  eapply match_stacks_restrict; eassumption. 
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest; assumption.  
  inv AGARGS. constructor; eauto. 
  destruct agree_args_inj0 as [x H]. 
    exists x. rewrite vis_restrict_sm, restrict_sm_all, restrict_nest; auto.
  rewrite vis_restrict_sm. rewrite restrict_sm_all.
    rewrite restrict_nest. auto. auto.
    rewrite restrict_sm_all. intros. 
    apply restrictD_Some in H. destruct H. solve[eapply agree_sp_fresh0; eauto].
    solve[rewrite restrict_sm_locBlocksTgt; auto].
Qed.

Definition MATCH (d:Linear_core) mu c1 m1 c2 m2:Prop :=
  match_states mu c1 m1 c2 m2 /\ Mem.inject (as_inj mu) m1 m2 /\
  REACH_closed m1 (vis mu) /\
  meminj_preserves_globals ge (as_inj mu) /\
  (forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true) /\
  sm_valid mu m1 m2 /\ SM_wd mu.

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
  destruct MC as [MS [INJ [RC [PG (*[GF*) [Glob [SMV WD]]]]]].
assert (WDR: SM_wd (restrict_sm mu X)).
   apply restrict_sm_WD; assumption.
split.
  eapply match_states_restrict; eassumption.
split. rewrite restrict_sm_all.
  eapply inject_restrict; eassumption.
split. unfold vis.
  rewrite restrict_sm_locBlocksSrc, restrict_sm_frgnBlocksSrc.
  apply RC.
split. clear -PG Glob HX.
  eapply restrict_sm_preserves_globals; try eassumption.
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

Lemma wt_locset_setlist_loc_arguments: forall l i vals LM,
  wt_locset LM ->
  wt_locset (Locmap.setlist (loc_arguments_rec l i) vals LM).
Proof. intros l.
induction l; simpl; intros. trivial.
destruct a; simpl; intros.
  destruct vals. trivial.
  eapply IHl. eapply wt_setstack. trivial.
  destruct vals. trivial.
  eapply IHl. eapply wt_setstack. trivial.
  destruct vals. trivial.
  destruct vals. eapply wt_setstack. trivial.
  eapply IHl. eapply wt_setstack. eapply wt_setstack. trivial.
  destruct vals. trivial.
  eapply IHl. eapply wt_setstack. trivial.
Qed. 

Lemma setlist_encode_long_regs: 
  forall r sgargs LM vals i, 
    Locmap.setlist (loc_arguments_rec sgargs i)
                   (val_casted.encode_longs sgargs vals) LM (Locations.R r) 
    = LM (Locations.R r).
Proof. intros r sgargs.
induction sgargs; simpl; intros. reflexivity.
destruct a; simpl. 
  destruct vals; try reflexivity.
  rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.
  destruct vals; try reflexivity.
  rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.
  destruct vals; try reflexivity.
  destruct v; try reflexivity.
  rewrite IHsgargs. rewrite Locmap.gso. rewrite Locmap.gso; trivial. 
    constructor. constructor.
  rewrite IHsgargs. rewrite Locmap.gso. rewrite Locmap.gso; trivial. 
    constructor. constructor.
  destruct vals; try reflexivity.
  rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.
  rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.  
  rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.  
  rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.  
  destruct vals; auto. rewrite IHsgargs. rewrite Locmap.gso; trivial. constructor.  
Qed.

Lemma getBlocks_cons v l b :
  getBlocks (v::nil) b=true -> 
  getBlocks (v::l) b=true.
Proof.
rewrite !getBlocks_getBlocks'. simpl. destruct v; auto; try congruence.
rewrite orb_true_iff. inversion 1; try congruence. rewrite H0; auto.
Qed.

Lemma getBlocks_tail v l b :
  getBlocks l b=true -> 
  getBlocks (v::l) b=true.
Proof.
rewrite !getBlocks_getBlocks'. simpl. destruct v; auto; try congruence.
rewrite orb_true_iff. inversion 1. right; auto.
Qed.

Lemma loc_arguments_gso z z' vl tys ty v ls :
  z' >= typesize ty ->
  Val.has_type v ty ->
  Locmap.setlist (loc_arguments_rec tys (z + z')) vl
    (Locmap.set (S Outgoing z ty) v ls) (S Outgoing z ty) = v.
Proof.
intros size.
rewrite Locmap.gsetlisto.
rewrite Locmap.gss.
solve[apply Val.load_result_same].
rewrite Loc.notin_iff; intros l' IN.
apply loc_arguments_rec_charact in IN.
destruct l'; try solve[inv IN]. 
destruct sl; try solve[inv IN]. destruct IN as [H H0].
right. omega.
Qed.

Lemma loc_arguments_gso' z z' vl tys ty1 ty2 v1 v2 ls :
  z' >= typesize ty1 + typesize ty2 ->
  Val.has_type v2 ty2 ->
  Locmap.setlist (loc_arguments_rec tys (z + z')) vl
     (Locmap.set (S Outgoing z ty1) v1
        (Locmap.set (S Outgoing (z + typesize ty1) ty2) v2 ls))
     (S Outgoing (z + typesize ty1) ty2) = v2.
Proof.
intros size.
rewrite Locmap.gsetlisto.
rewrite Locmap.gso.
rewrite Locmap.gss.
solve[apply Val.load_result_same].
simpl. right; omega.
rewrite Loc.notin_iff; intros l' IN.
apply loc_arguments_rec_charact in IN.
destruct l'; try solve[inv IN]. 
destruct sl; try solve[inv IN]. destruct IN as [H H0].
right. omega.
Qed.

Lemma loc_arguments_gso_reg z vl tys r :
  Locmap.setlist (loc_arguments_rec tys z) vl (Locmap.init Vundef) (R r) = Vundef.
Proof.
rewrite Locmap.gsetlisto. auto.
rewrite Loc.notin_iff; intros l' IN.
apply loc_arguments_rec_charact in IN.
destruct l'; try solve[inv IN]. 
destruct sl; try solve[inv IN]. destruct IN as [H H0].
simpl; auto.
Qed.

Lemma wt_setlist_loc_arguments sig vals :
  wt_locset
    (Locmap.setlist (loc_arguments sig)
                    (encode_longs (sig_args sig) vals)
                    (Locmap.init Vundef)).
Proof.
apply wt_locset_setlist_loc_arguments.
apply wt_init.
Qed.

Lemma wt_init_locset sig args : 
  let tys := sig_args sig in
  wt_locset (call_regs' (call_regs (init_locset tys args))).
Proof.
intros tys. cut (wt_locset (init_locset tys args)). 
intros H l. specialize (H l). revert H; destruct l; simpl; auto. 
destruct sl; try solve[constructor]. auto.
unfold init_locset. solve[apply wt_setlist_loc_arguments].
Qed.

Lemma agree_args_match_init vals1 vals2 tys j m1 m2 DomS DomT z : 
   vals_defined vals1=true -> 
   val_list_inject j vals1 vals2 ->
   val_has_type_list_func vals1 tys = true ->
   agree_args_match_aux
     (restrict j
        (vis
           (initial_SM DomS DomT
              (REACH m1
                 (fun b0 : block =>
                  isGlobalBlock (Genv.globalenv prog) b0
                  || getBlocks vals1 b0))
              (REACH m2
                 (fun b0 : block =>
                  isGlobalBlock (Genv.globalenv tprog) b0
                  || getBlocks vals2 b0)) j)))
     (call_regs
        (Locmap.setlist (loc_arguments_rec tys z) (encode_longs tys vals1)
           (Locmap.init Vundef))) z vals2 tys.
Proof.
intros DEF INJ' TY. 
generalize INJ' as INJ; intro. 
apply encode_longs_inject with (tyl := tys) in INJ.
revert z tys vals1 DEF TY INJ INJ'. 
generalize (Locmap.init Vundef) as ls. induction vals2.
intros. inv INJ'. simpl in TY. destruct tys; [|congruence]. 
  solve[simpl; auto].
intros. inv INJ'. destruct tys. inv TY. simpl.
set (X := vis
  (initial_SM DomS DomT
              (REACH m1
                     (fun b0 : block =>
                        isGlobalBlock (Genv.globalenv prog) b0
                                      || getBlocks vl b0))
              (REACH m2
                     (fun b0 : block =>
                        isGlobalBlock (Genv.globalenv tprog) b0
                                      || getBlocks vals2 b0)) j)).
destruct t. 
+ simpl. split. 
change 1 with (typesize Tint); rewrite loc_arguments_gso; auto. 
apply restrict_val_inject; auto.
intros b G. unfold vis. rewrite orb_true_iff. right. simpl.
apply REACH_nil. rewrite orb_true_iff. right.
solve[apply getBlocks_cons; auto]. omega. 
simpl in TY. rewrite andb_true_iff in TY. destruct TY as [TY _].
solve[rewrite <-val_has_type_funcP in TY; auto].
apply agree_args_match_aux_sub with (X := X).
intros b; unfold X. unfold vis. rewrite !orb_true_iff. intros [?|?].
simpl in H. congruence.
simpl in H|-*. right. eapply REACH_mono; eauto.
  simpl. intros b0. rewrite !orb_true_iff. intros [?|?]. solve[left; auto].
  simpl. right. solve[apply getBlocks_tail; auto].
apply IHvals2; auto.
simpl in DEF. solve[destruct v; try congruence; auto].
simpl in TY. rewrite andb_true_iff in TY. solve[destruct TY; auto].
simpl in INJ. solve[inv INJ; auto].
+ split. simpl.
change 2 with (typesize Tfloat); rewrite loc_arguments_gso; auto. 
apply restrict_val_inject; auto. 
intros b G. unfold vis. rewrite orb_true_iff. right. simpl.
apply REACH_nil. rewrite orb_true_iff. right.
solve[apply getBlocks_cons; auto]. omega.
simpl in TY. rewrite andb_true_iff in TY. destruct TY as [TY _].
solve[rewrite val_has_type_funcP; auto].
apply agree_args_match_aux_sub with (X := X).
intros b; unfold X. unfold vis. rewrite !orb_true_iff. intros [?|?].
simpl in H. congruence.
simpl in H|-*. right. eapply REACH_mono; eauto.
  simpl. intros b0. rewrite !orb_true_iff. intros [?|?]. solve[left; auto].
  simpl. right. solve[apply getBlocks_tail; auto].
apply IHvals2; auto.
simpl in DEF. solve[destruct v; try congruence; auto].
simpl in TY. rewrite andb_true_iff in TY. solve[destruct TY; auto].
simpl in INJ. solve[inv INJ; auto].
+ assert (R: exists n, v = Vlong n).
{ simpl in TY. rewrite andb_true_iff in TY. destruct TY as [TY _].
  rewrite <-val_has_type_funcP in TY. unfold Val.has_type in TY.
  simpl in DEF. destruct v; try solve[inversion TY|inversion DEF].
  exists i; auto. }
destruct R as [n' R]. rewrite R in *. simpl.  
assert (L: exists n, a = Vlong n). 
{ inv H2. exists n'. auto. }
destruct L as [n L]. rewrite L in *. simpl in TY, DEF. 
split. inv H2.
  generalize (Locmap.set (S Outgoing z Tint) (Vint (Int64.loword n)) ls)
    as ls'.
  assert (z+2 = z+(1+1)) as -> by omega.
  change 1 with (typesize Tint). 
  remember (typesize Tint+typesize Tint) as z'.
  intros ls'. rewrite loc_arguments_gso'; auto. simpl; auto.
  subst z'. simpl. omega. solve[simpl; auto].
split. inv H2. 
  generalize (Locmap.set (S Outgoing (z+1) Tint) (Vint (Int64.hiword n)) ls)
    as ls'.
  intros ls'. rewrite loc_arguments_gso; auto. simpl; omega. simpl; auto.
apply agree_args_match_aux_sub with (X := X).
intros b; unfold X. unfold vis. rewrite !orb_true_iff. intros [?|?].
simpl in H. congruence.
simpl in H|-*. right. eapply REACH_mono; eauto.
  simpl. intros b0. rewrite !orb_true_iff. intros [?|?]. solve[left; auto].
  simpl. right. solve[apply getBlocks_tail; auto].
apply IHvals2; auto.
simpl in INJ. inv INJ. inv H6. solve[auto].
+ simpl. split. 
change 1 with (typesize Tsingle); rewrite loc_arguments_gso; auto. 
apply restrict_val_inject; auto.
intros b G. unfold vis. rewrite orb_true_iff. right. simpl.
apply REACH_nil. rewrite orb_true_iff. right.
solve[apply getBlocks_cons; auto]. omega. 
simpl in TY. rewrite andb_true_iff in TY. destruct TY as [TY _].
solve[rewrite <-val_has_type_funcP in TY; auto].
apply agree_args_match_aux_sub with (X := X).
intros b; unfold X. unfold vis. rewrite !orb_true_iff. intros [?|?].
simpl in H. congruence.
simpl in H|-*. right. eapply REACH_mono; eauto.
  simpl. intros b0. rewrite !orb_true_iff. intros [?|?]. solve[left; auto].
  simpl. right. solve[apply getBlocks_tail; auto].
apply IHvals2; auto.
simpl in DEF. solve[destruct v; try congruence; auto].
simpl in TY. rewrite andb_true_iff in TY. solve[destruct TY; auto].
simpl in INJ. solve[inv INJ; auto].
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
  (Ini :initial_core (Linear_eff_sem hf) ge v1 vals1 = Some c1)
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
  initial_core (Mach_eff_sem hf return_address_offset) tge v2 vals2 = Some c2 /\
  MATCH c1
    (initial_SM DomS DomT
       (REACH m1
          (fun b : Values.block => isGlobalBlock ge b || getBlocks vals1 b))
       (REACH m2
          (fun b : Values.block => isGlobalBlock tge b || getBlocks vals2 b))
       j) c1 m1 c2 m2. 
Proof. intros.
  inversion Ini.
  unfold Linear_initial_core in H0. unfold ge in *. unfold tge in *.
  destruct v1; inv H0.
  remember (Int.eq_dec i Int.zero) as z; destruct z; inv H1. clear Heqz.
  remember (Genv.find_funct_ptr (Genv.globalenv prog) b) as zz; destruct zz; inv H0. 
    apply eq_sym in Heqzz.
  destruct f; try discriminate.
  case_eq (val_casted.val_has_type_list_func vals1 
            (sig_args (Linear.funsig (Internal f))) 
           && val_casted.vals_defined vals1).
  2: solve[intros H2; rewrite H2 in H1; inv H1].
  intros H2; rewrite H2 in H1. inv H1. 

  exploit function_ptr_translated; eauto. intros [tf [FP TF]].
  clear Ini.

  assert (VALS2: val_casted.val_has_type_list_func vals2 (sig_args (funsig tf))=true).
  { eapply val_casted.val_list_inject_hastype; eauto.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; simpl in H2. solve[inv H2].
    assert (sig_args (funsig tf)
          = sig_args (Linear.funsig (Internal f))) as ->.
    { erewrite sig_preserved; eauto. }
    destruct (val_casted.val_has_type_list_func vals1
      (sig_args (Linear.funsig (Internal f)))); auto. }

  assert (DEF2: val_casted.vals_defined vals2=true).
  { eapply val_casted.val_list_inject_defined.
    eapply forall_inject_val_list_inject; eauto.
    destruct (val_casted.vals_defined vals1); auto.
    rewrite andb_comm in H2; inv H2. }

  destruct (entry_points_ok _ _ _ EP) as [b0 [f1 [f2 [A [B [C D]]]]]].
  subst. apply eq_sym in A. inv A. rewrite C in Heqzz. inv Heqzz.
  unfold tge in FP. rewrite D in FP. inv FP.
  case_eq (Int.eq_dec Int.zero Int.zero).
  2: solve[intros CONTRA; elimtype False; auto].
  intros ? e.
  exists (Mach_CallstateIn b vals2 (sig_args (funsig tf))).
  split. simpl. rewrite e, D. 

  rewrite VALS2, DEF2. monadInv TF. rename x into tf. simpl. 
  solve[simpl; auto].

  destruct (core_initial_wd ge tge _ _ _ _ _ _ _  Inj
     VInj J RCH PG GDE HDomS HDomT _ (eq_refl _))
    as [AA [BB [CC [DD [EE [FF GG]]]]]]. simpl in *.  
  destruct InitMem as [m0 [INIT [? ?]]].

  assert (InitBlocks: forall b, Plt b (Mem.nextblock m0) -> 
            isGlobalBlock ge b = true).    
  { intros bb LT. unfold ge. 
    apply valid_init_is_global with (b0 := bb) in INIT.
    destruct INIT. eapply find_symbol_isGlobal; eassumption. auto. apply LT. }

  split. 2: rewrite initial_SM_as_inj; intuition.
  apply bind_inversion in TF. destruct TF as [x [TF X]]. inv X.

  assert (Linear.fn_sig f=fn_sig x) as ->.
  { apply unfold_transf_function in TF; rewrite TF; auto. }

  eapply match_states_init; eauto. simpl.

  solve[apply wt_setlist_loc_arguments].
  solve[intros r; apply loc_arguments_gso_reg].

  intros ? ? ? [X|X]; subst; unfold init_locset. 
  { rewrite Locmap.gsetlisto; auto. rewrite Loc.notin_iff.
  intros l X. apply loc_arguments_rec_charact in X. 
  destruct l; try destruct sl; try solve[contradiction].
  left; intros CONTRA; congruence. }
  { rewrite Locmap.gsetlisto; auto. rewrite Loc.notin_iff.
  intros l X. apply loc_arguments_rec_charact in X. 
  destruct l; try destruct sl; try solve[contradiction].
  left; intros CONTRA; congruence. }

  simpl. unfold loc_arguments. rewrite initial_SM_as_inj.
  rewrite andb_true_iff in H2. destruct H2 as [H2 H3]. revert H2.
  generalize (sig_args (fn_sig x)) as tys.
  apply forall_inject_val_list_inject in VInj. intros tys.
  generalize (encode_longs_inject _ tys vals1 vals2 VInj).
  solve[intros H2 H4; apply agree_args_match_init; auto].

  solve[rewrite H1; auto].
  exists vals1. rewrite initial_SM_as_inj. 
    unfold initial_SM, vis. simpl. split; auto.
    apply forall_inject_val_list_inject.
    apply restrict_forall_vals_inject; auto.
    intros b0 GET. apply REACH_nil. 
    solve[rewrite orb_true_iff; right; auto].
  solve[rewrite val_has_type_list_func_charact; auto].
Qed.

Lemma MATCH_atExternal: forall mu c1 m1 c2 m2 e vals1 ef_sig
       (MTCH: MATCH c1 mu c1 m1 c2 m2)
       (AtExtSrc: at_external (Linear_eff_sem hf) c1 = Some (e, ef_sig, vals1)),
     Mem.inject (as_inj mu) m1 m2 /\
     exists vals2,
       Forall2 (val_inject (restrict (as_inj mu) (vis mu))) vals1 vals2 /\
       at_external (Mach_eff_sem hf return_address_offset)  c2 = Some (e, ef_sig, vals2) /\
      (forall pubSrc' pubTgt',
       pubSrc' = (fun b => locBlocksSrc mu b && REACH m1 (exportedSrc mu vals1) b) ->
       pubTgt' = (fun b => locBlocksTgt mu b && REACH m2 (exportedTgt mu vals2) b) ->
       forall nu : SM_Injection, nu = replace_locals mu pubSrc' pubTgt' ->
       MATCH c1 nu c1 m1 c2 m2 /\ Mem.inject (shared_of nu) m1 m2).
Proof. intros. 
destruct MTCH as [MC [INJ [RC [PG [GF [SMV WD]]]]]].
  inv MC; simpl in AtExtSrc; inv AtExtSrc.
  destruct f; simpl in *; inv H0.
  split; trivial. monadInv TRANSL.
  destruct f; simpl in *; inv H0.
  monadInv TRANSL.
  split; trivial. 
exploit transl_external_arguments_rec; eauto. eapply incl_refl.
intros [targs [Htargs AINJ]].
exploit transl_external_arguments_fun.
   2:eapply GETARGS. 2:eapply Htargs. trivial.
intros; subst. 
exists (decode_longs (sig_args (AST.ef_sig tf)) targs).
assert 
(H: val_list_inject (restrict (as_inj mu) (vis mu))
    (decode_longs (sig_args (AST.ef_sig tf)) ls ## (loc_arguments (AST.ef_sig tf)))
    (decode_longs (sig_args (AST.ef_sig tf)) targs)).
{ apply decode_longs_inject; auto. }
destruct (observableEF_dec hf tf); try inv H1. 
rename o into OBS.
split. 
solve[apply val_list_inject_forall_inject; auto].
exploit replace_locals_wd_AtExternal; try eassumption.
  apply val_list_inject_forall_inject in H.
  apply forall_vals_inject_restrictD in H. eassumption.
intros WDnu. split; auto. intros; subst. split. split; auto.
econstructor; try rewrite replace_locals_as_inj, replace_locals_vis; eauto. 
eapply match_stacks_replace_locals; eassumption.
solve[apply agree_args_replace_locals; auto]. 
rewrite replace_locals_as_inj, replace_locals_vis, replace_locals_frgnBlocksSrc.
split; auto. split; auto. split; auto. split; auto. split; auto.
(*sm_valid*) red. rewrite replace_locals_DOM, replace_locals_RNG. solve[apply SMV]. 
(*inject_shared*) eapply inject_shared_replace_locals; eauto. eauto. solve[eauto].
Qed.

Lemma list_Loc_type_mreg r: Loc.type ## (R ## r) = mreg_type ## r.
Proof.
  induction r; simpl. trivial.
  rewrite IHr. trivial.
Qed.

Lemma size_arguments_id: forall args i, 
      (size_arguments_rec args i = i -> args=nil) /\
      (size_arguments_rec args i >= i).
Proof.
induction args; simpl.
  intros. split; trivial. omega.
  intros. destruct (IHargs (i + typesize a)). clear IHargs.
  split. intros. rewrite H1 in *. specialize (typesize_pos a). intros. omega.
  specialize (typesize_pos a). intros. omega. 
Qed. 

Lemma match_stacks_replace_externs FSrc FTgt:
  forall mu m m' sp0 ls0 cs cs' sg bound bound'
  (PGmu: meminj_preserves_globals (Genv.globalenv prog) (as_inj mu))
  (HFSrc: forall b, vis mu b = true -> locBlocksSrc mu b || FSrc b = true),
  match_stacks mu m m' sp0 ls0 cs cs' sg bound bound' -> SM_wd mu ->
  match_stacks (replace_externs mu FSrc FTgt) m m' sp0 ls0 cs cs' sg bound bound'.
Proof.
  intros.
   induction H; try econstructor; eauto.
   rewrite replace_externs_as_inj, replace_externs_vis.
       inv H2. constructor; eauto.
       intros. specialize (DOMAIN _ H2).
          destruct (restrictD_Some _ _ _ _ _ DOMAIN).
          eapply restrictI_Some; try eassumption.
          apply HFSrc; trivial.
       intros. 
          destruct (restrictD_Some _ _ _ _ _ H2); clear H2.
          symmetry. eapply PGmu; eassumption. 
 
     rewrite replace_externs_as_inj, replace_externs_vis.
       eapply agree_frame_inject_incr_restrict; try eassumption.
       intros. destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
               eapply restrictI_Some; try eassumption.
               unfold vis.
               rewrite <- (as_inj_locBlocks _ _ _ _ H0 H2) in SPLOCT.
               rewrite SPLOCT. trivial.

     rewrite replace_externs_locBlocksTgt; trivial.
Qed.

Lemma MATCH_afterExternal: forall
      (GDE : genvs_domain_eq ge tge)
      mu st1 st2 m1 e vals1 m2 ef_sig vals2 e' ef_sig'
      (MemInjMu : Mem.inject (as_inj mu) m1 m2)
      (MatchMu: MATCH st1 mu st1 m1 st2 m2)
      (AtExtSrc : at_external (Linear_eff_sem hf) st1 = Some (e, ef_sig, vals1))
      (AtExtTgt : at_external (Mach_eff_sem hf return_address_offset) st2 
                  = Some (e', ef_sig', vals2))
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
       (SEP: sm_inject_separated nu nu' m1 m2)
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
  after_external (Linear_eff_sem hf) (Some ret1) st1 =Some st1' /\
  after_external (Mach_eff_sem hf return_address_offset) (Some ret2) st2 = Some st2' /\
  MATCH st1' mu' st1' m1' st2' m2'.
Proof. intros.
simpl. 
 destruct MatchMu as [MC [INJ [RC [PG [GFP [VAL WDmu]]]]]].
 simpl in *. inv MC; simpl in *; inv AtExtSrc.
 inv AtExtTgt.
 destruct f; inv H0. 
 inv AtExtTgt.
 inv TRANSL.
 destruct (observableEF_dec hf tf); inv H0; inv H1.
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
    subst. clear - INC SEP PG GFP WDmu WDnu'.
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
      destruct (frgnSrc _ WDmu _ (GFP _ GG)) as [bb2 [dd [FF FT2]]].
      rewrite (foreign_in_all _ _ _ _ FF) in PGa. inv PGa.
      apply foreign_in_extern; eassumption.
    split; intros. specialize (PGb _ H).
      apply joinI; left. apply INC.
      rewrite replace_locals_extern.
      assert (GG: isGlobalBlock ge b = true).
          unfold isGlobalBlock, ge. apply genv2blocksBool_char2 in H.
          rewrite H. intuition.
      destruct (frgnSrc _ WDmu _ (GFP _ GG)) as [bb2 [dd [FF FT2]]].
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
        rewrite replace_locals_as_inj, replace_locals_DomSrc, replace_locals_DomTgt 
          in SEPa. 
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
        rewrite Heql in *. simpl in *. clear INCTX. intuition.
        assert (VB: Mem.valid_block m1 b').
        { eapply VAL. unfold DOM, DomSrc. rewrite Heql; auto. }
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
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ RC). 
          intuition.
        apply REACH_nil. unfold exportedSrc.
          rewrite (frgnSrc_shared _ WDnu' _ RC). intuition.
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
  { eapply REACH_closed_intersection; eassumption. }

assert (GFnu': forall b, 
                 isGlobalBlock (Genv.globalenv prog) b = true ->
                 DomSrc nu' b 
                 && (negb (locBlocksSrc nu' b) 
                     && REACH m1' (exportedSrc nu' (ret1 :: nil)) b) = true).
{ intros. specialize (GFP _ H).
  assert (FSRC:= extern_incr_frgnBlocksSrc _ _ INC).
  { rewrite replace_locals_frgnBlocksSrc in FSRC.
    rewrite FSRC in GFP.
    rewrite (frgnBlocksSrc_locBlocksSrc _ WDnu' _ GFP). 
    apply andb_true_iff; simpl.
    split.
    unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ GFP). intuition.
    apply REACH_nil. unfold exportedSrc.
    rewrite (frgnSrc_shared _ WDnu' _ GFP). intuition. }}

split.
  econstructor. instantiate (1:=ef_sig e).
    { exploit match_stack_change_extcall. eapply FwdSrc. eapply FwdTgt.
       eassumption.
       eapply replace_locals_wd. assumption.
         intros. apply andb_true_iff in H; destruct H.
            eapply forall_vals_inject_restrictD in ValInjMu.
            exploit (REACH_local_REACH mu); try eassumption.
              intros [b2 [d [loc R2]]].
              destruct (local_DomRng _ WDmu _ _ _ loc).
              exists b2, d. rewrite R2, H2; simpl. split; trivial.
            intros. apply andb_true_iff in H; eapply H.
            assumption.
         clear - SEP. assumption.
         assumption.
      eapply match_stacks_replace_locals. eassumption.
      xomega.
      xomega.
      intros. eapply match_stacks_change_bounds.
        eapply match_stacks_replace_externs; try eassumption.
        intros. unfold vis in H0.
        destruct (locBlocksSrc nu' b); simpl in *; trivial.

      apply andb_true_iff.
        split. unfold DomSrc. rewrite (frgnBlocksSrc_extBlocksSrc _ WDnu' _ H0).
               intuition.
        apply REACH_nil. unfold exportedSrc.
          apply frgnSrc_shared in H0; trivial.
          rewrite H0; intuition.
      eapply forward_nextblock; assumption.
      eapply forward_nextblock; assumption.
    }

  (*wtlocset*)
    eapply wt_setlist_result. 2: assumption. 
    admit. (*MATCH_afterExternal: eapply external_call_well_typed; eauto. *)

  (*agree*)
   { rewrite replace_externs_as_inj, replace_externs_vis. 
     apply agree_regs_set_regs; auto.
     eapply agree_regs_inject_incr. (* with j; auto. *)
       eassumption.
       clear - WDnu' INC. 
         apply extern_incr_restrict in INC; trivial. 
         rewrite replace_locals_as_inj, replace_locals_vis in INC.
         red; intros. apply INC in H.
         destruct (restrictD_Some _ _ _ _ _ H); clear H.
         apply restrictI_Some; trivial.
         destruct (as_inj_DomRng _ _ _ _ H0 WDnu'). rewrite H.
         unfold vis in H1.
         destruct (locBlocksSrc nu' b); simpl in *; trivial. 
         apply REACH_nil. unfold exportedSrc.
           rewrite (frgnSrc_shared _ WDnu' _ H1). intuition.
       clear - WDnu' RValInjNu'. 
         eapply encode_long_inject.
         inv RValInjNu'; econstructor; eauto.
         apply restrictI_Some; trivial.
         destruct (as_inj_DomRng _ _ _ _ H WDnu'). rewrite H0.
         destruct (locBlocksSrc nu' b1); simpl in *; trivial. 
         apply REACH_nil. unfold exportedSrc.
         apply orb_true_iff; left.
         apply getBlocks_char. exists ofs1; left; trivial. }

 (*agree_callee_save*)
    { apply agree_callee_save_set_result; auto. }

 (*agree_args*)
    apply agree_args_replace_externs; auto.
    unfold vis. intros b. rewrite !orb_true_iff. 
    intros [H|H]. left; auto. right. rewrite !andb_true_iff. split; auto.
    unfold DomSrc. apply frgnBlocksSrc_extBlocksSrc in H; auto. 
    solve[rewrite H, orb_comm; auto].
    split. apply frgnBlocksSrc_locBlocksSrc in H; auto. solve[rewrite H; auto].
    apply REACH_nil. unfold exportedSrc. rewrite orb_true_iff; right.
    solve[apply frgnSrc_shared; auto].
    set (nu := (replace_locals mu
             (fun b : block =>
              locBlocksSrc mu b &&
              REACH m1
                (exportedSrc mu
                   (decode_longs (sig_args (ef_sig e))
                      ls ## (loc_arguments (ef_sig e)))) b)
             (fun b : block =>
              locBlocksTgt mu b &&
              REACH m2
                (exportedTgt mu (decode_longs (sig_args (ef_sig e)) args)) b)))
    in *.
    assert (ValInjMu': 
              Forall2 (val_inject (as_inj mu))
                      (decode_longs (sig_args (ef_sig e))
                                    ls ## (loc_arguments (ef_sig e)))
                      (decode_longs (sig_args (ef_sig e)) args)).
    { apply forall_vals_inject_restrictD in ValInjMu; auto. }
    assert (NUWD: SM_wd nu).
    { destruct (eff_after_check1 _ WDmu _ _ VAL MemInjMu _ _ ValInjMu'
               _ (eq_refl _) _ (eq_refl _) nu (eq_refl _)); auto. }
    apply agree_args_invariant with (m' := m2); eauto. 
    eapply agree_args_extern_incr; eauto.      
    solve[apply agree_args_replace_locals; eauto].
    eapply mem_unchanged_on_sub. apply UnchLOOR. intros b ofs.
    intros Heq; subst b. split. 
    solve[inv AGARGS; unfold nu in *; rewrite replace_locals_locBlocksTgt; auto].
    intros b0 z. unfold nu in *; rewrite replace_locals_local. intros lOf.
    exfalso. inv AGARGS. apply local_in_all in lOf; auto. 
    solve[eapply agree_sp_fresh0; eauto]. 
    
unfold vis in *.
rewrite replace_externs_locBlocksSrc, replace_externs_frgnBlocksSrc,
        replace_externs_as_inj in *.
destruct (eff_after_check2 _ _ _ _ _ MemInjNu' RValInjNu' 
      _ (eq_refl _) _ (eq_refl _) _ (eq_refl _) WDnu' SMvalNu').
unfold vis in *. solve[intuition].
Qed.

Lemma store_args_rec_outside m sp z args tys m' v ch sz : 
  sz >= 0 -> z >= 0 -> 4*sz >= size_chunk ch -> 
  4*(z+sz+2*(Zlength args)) <= Int.max_unsigned -> 
  store_args_rec m sp (z + sz) args tys = Some m' -> 
  Mem.load ch m sp (Int.unsigned (Int.add Int.zero (Int.repr (4*z)))) = Some v -> 
  Mem.load ch m' sp (Int.unsigned (Int.add Int.zero (Int.repr (4*z)))) = Some v.
Proof.
  revert m args z sz. induction tys. destruct args. intros ? ? POS POS2 OVER H H2 H3.
  simpl in H2. inv H2; auto. intros ? ? POS POS2 OVER H H2 H3. simpl in H2. inv H2.
  intros ? ? ? ? POS POS2 OVER H H2 H3. destruct args. inv H2. destruct a. 
  - revert H2. unfold store_args_rec. 
  case_eq (store_stack m (Vptr sp Int.zero) Tint
            (Int.repr (fe_ofs_arg + 4 * (z + sz))) v0); try solve[inversion 2].
  fold store_args_rec. intros m0 STORE REST. 
  apply IHtys with (m := m0) (sz := sz + typesize Tint) (args := args); eauto. 
  simpl; omega. simpl typesize. omega. 
  simpl typesize. revert H. rewrite Zlength_cons. unfold Z.succ. intros; omega.
  assert (z+(sz+typesize Tint) = z+sz+typesize Tint) as -> by omega; eauto.
  unfold store_stack, Mem.storev in STORE; simpl in STORE. 
  erewrite Mem.load_store_other; eauto.  
  right. left. simpl. rewrite !Int.add_zero_l. rewrite !Int.unsigned_repr. 
  assert (A: 4*z+size_chunk ch <= 4*(z+sz)) by omega. solve[apply A].
  revert H. generalize (Zlength_cons_pos _ v0 args). generalize (Zlength (v0::args)). intros.
  assert (A: 0 <= 4*(z+sz) <= Int.max_unsigned) by omega. solve[apply A].
  revert H. generalize (Zlength_cons_pos _ v0 args). generalize (Zlength (v0::args)). intros.
  assert (A: 0 <= 4*z <= Int.max_unsigned) by omega. solve[apply A].
Admitted. (*other cases are similar*)

Lemma store_args_contains m sp args tys m' z 
      (POS: z >= 0) 
      (OVER: 4*(z+2*(Zlength args)) <= Int.max_unsigned) : 
  val_has_type_list_func args tys=true -> 
  store_args_rec m sp z args tys = Some m' -> 
  agree_args_contains_aux m' sp z args tys.
Proof.
  revert m args z POS OVER. induction tys.
  destruct args; auto. simpl; auto. simpl. inversion 3.
  destruct args; auto. simpl. inversion 3.
  unfold store_args. unfold store_args_rec, agree_args_contains_aux. 
  intros z POS OVER HASTY. simpl in HASTY. 
  rewrite andb_true_iff in HASTY. destruct HASTY as [H HASTY].
  destruct a.
  - case_eq (store_stack m (Vptr sp Int.zero) Tint (Int.repr (fe_ofs_arg + 4*z)) v);
    try solve[inversion 2].
  intros m0 STORE REST. unfold store_stack, Mem.storev in STORE; simpl in STORE.
  unfold load_stack, Mem.loadv; simpl. split. fold store_args_rec in REST.  
  eapply store_args_rec_outside with (sz := typesize Tint); eauto. 
  simpl; omega. simpl; omega. 
  rewrite Zlength_cons in OVER. unfold Z.succ in OVER. simpl typesize. omega.
  erewrite Mem.load_store_same; eauto.
  f_equal. change Mint32 with (chunk_of_type Tint).
  rewrite Val.load_result_same; eauto. solve[apply val_has_type_funcP; auto].
  eapply IHtys; eauto. omega. 
  clear - OVER. rewrite Zlength_cons in OVER. unfold Z.succ in OVER. omega.
  - case_eq (store_stack m (Vptr sp Int.zero) Tfloat (Int.repr (fe_ofs_arg + 4*z)) v);
    try solve[inversion 2].
  intros m0 STORE REST. unfold store_stack, Mem.storev in STORE; simpl in STORE.
  unfold load_stack, Mem.loadv; simpl. split. fold store_args_rec in REST.  
  eapply store_args_rec_outside with (sz := typesize Tfloat); eauto. 
  simpl; omega. simpl; omega. 
  rewrite Zlength_cons in OVER. unfold Z.succ in OVER. simpl typesize. omega.
  erewrite Mem.load_store_same; eauto.
  f_equal. change Mfloat64al32 with (chunk_of_type Tfloat).
  rewrite Val.load_result_same; eauto. solve[apply val_has_type_funcP; auto].
  eapply IHtys; eauto. omega. 
  clear - OVER. rewrite Zlength_cons in OVER. unfold Z.succ in OVER. omega.
  - destruct v; try solve[inversion 1].
  case_eq (store_stack m (Vptr sp Int.zero) Tint (Int.repr (fe_ofs_arg + 4*(z+1))) 
                       (Vint (Int64.hiword i)));
    try solve[inversion 2].
  intros m0 STORE. unfold store_stack, Mem.storev in STORE; simpl in STORE.
  case_eq (store_stack m0 (Vptr sp Int.zero) Tint (Int.repr (fe_ofs_arg + 4*z)) 
                       (Vint (Int64.loword i)));
    try solve[inversion 2].
  intros m1 STORE' REST. unfold store_stack, Mem.storev in STORE'; simpl in STORE'.
  unfold load_stack, Mem.loadv; simpl. split. fold store_args_rec in REST.  
  eapply store_args_rec_outside with (sz := 1) (args := args); eauto. 
  omega. simpl; omega. simpl; omega.
  rewrite Zlength_cons in OVER. unfold Z.succ in OVER. simpl typesize. omega.
  assert (z+1+1 = z+2) as -> by omega; eauto. 
  erewrite Mem.load_store_other; eauto.
  erewrite Mem.load_store_same with (m1 := m); eauto. f_equal. 
  right. simpl. right. rewrite !Int.add_zero_l, !Int.unsigned_repr. 
  assert (A: 4*z + 4 <= 4*(z+1)) by omega. solve[apply A].
  assert (A: 0 <= 4*(z+1) <= Int.max_unsigned). 
  { clear - OVER POS. revert OVER. 
    generalize (Zlength_cons_pos _ (Vlong i) args).
    generalize (Zlength (Vlong i::args)). intros. omega. }
  solve[apply A].
  assert (A: 0 <= 4*z <= Int.max_unsigned). 
  { clear - OVER POS. revert OVER. 
    generalize (Zlength_cons_pos _ (Vlong i) args).
    generalize (Zlength (Vlong i::args)). intros. omega. }
  solve[apply A].
  fold store_args_rec in REST. split. 
  eapply store_args_rec_outside with (sz := 2); eauto. simpl; omega. simpl; omega.
  rewrite Zlength_cons in OVER. unfold Z.succ in OVER. simpl typesize. omega.
  erewrite Mem.load_store_same; eauto.
  change Mint32 with (chunk_of_type Tint).
  rewrite Val.load_result_same; eauto. solve[apply val_has_type_funcP; auto].
  eapply IHtys; eauto. omega. 
  clear - OVER. rewrite Zlength_cons in OVER. unfold Z.succ in OVER. omega.
  - case_eq (store_stack m (Vptr sp Int.zero) Tsingle (Int.repr (fe_ofs_arg + 4*z)) v);
    try solve[inversion 2].
  intros m0 STORE REST. unfold store_stack, Mem.storev in STORE; simpl in STORE.
  unfold load_stack, Mem.loadv; simpl. split. fold store_args_rec in REST.  
  eapply store_args_rec_outside with (sz := typesize Tsingle); eauto. 
  simpl; omega. simpl; omega. 
  rewrite Zlength_cons in OVER. unfold Z.succ in OVER. simpl typesize. omega.
  erewrite Mem.load_store_same; eauto.
  f_equal. change Mfloat32 with (chunk_of_type Tsingle).
  rewrite Val.load_result_same; eauto. solve[apply val_has_type_funcP; auto].
  eapply IHtys; eauto. omega. 
  clear - OVER. rewrite Zlength_cons in OVER. unfold Z.succ in OVER. omega.
Qed.

Lemma MATCH_corediagram: forall st1 m1 st1' m1'
      (CS: corestep (Linear_eff_sem hf) ge st1 m1 st1' m1')
      st2 mu m2 (MTCH: MATCH st1 mu st1 m1 st2 m2),
  exists st2' m2',
    corestep_plus (Mach_eff_sem hf return_address_offset) tge st2 m2 st2' m2' /\
  exists mu', intern_incr mu mu' /\
    sm_inject_separated mu mu' m1 m2 /\
    sm_locally_allocated mu mu' m1 m2 m1' m2' /\
    MATCH st1' mu' st1' m1' st2' m2'.
Proof.
intros.
  assert (USEWTF: forall f i c,
          wt_function f = true -> is_tail (i :: c) (Linear.fn_code f) ->
          wt_instr f i = true).
    intros. unfold wt_function, wt_code in H. rewrite forallb_forall in H.
    apply H. eapply is_tail_in; eauto. 
assert(SymbPres := symbols_preserved).
destruct CS; intros; destruct MTCH as [MS [INJ PRE]];
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (USEWTF _ _ _ WTF TAIL); intro WTI; simpl in WTI; InvBooleans);
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

{ (* Lgetstack *)
  destruct BOUND. unfold destroyed_by_getstack; destruct sl.
  (* Lgetstack, local *)
  exploit agree_locals; eauto. intros [v [A B]].
  eexists; eexists; split.
    apply corestep_plus_one. apply Mach_exec_Mgetstack. 
    solve[eapply index_contains_load_stack; eauto].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). solve[intuition].
  constructor.
    econstructor; eauto with coqlib.
    apply agree_regs_set_reg; auto. simpl. apply agree_frame_set_reg; auto. 
      simpl. eapply Val.has_subtype; eauto. 
      solve[eapply agree_wt_ls; eauto].
  solve[intuition]. 

 (* Lgetstack, incoming *)
  unfold slot_valid in H0. InvBooleans.
  exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  inversion STACKS; clear STACKS.
  subst. 

  (* read from dummy frame *)
  generalize AGARGS as AGARGS'; intro.
  inv AGARGS. simpl in *. destruct agree_args_inj0 as [args1 X].
  exploit agree_args_match_contain; eauto. 
  destruct AGINITF as [Y|Y]. subst. solve[eauto]. solve[elim (Y _ IN_ARGS)].
  intros [v [LD VINJ]]. 
  eexists; eexists. split. 
  apply corestep_plus_one. econstructor; eauto.
    rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link). eapply TRANSL. 
      solve[eapply agree_link; eauto].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      clear AGINITF. intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  constructor.
    econstructor; eauto with coqlib. econstructor; eauto.
    apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto. 
    cut (rs (S Incoming ofs ty) = ls0 (S Incoming ofs ty)). solve[intros ->; auto].
    inv AGFRAME. solve[rewrite agree_incoming0; auto].
    eapply agree_frame_set_reg; eauto. eapply agree_frame_set_reg; eauto. 
    apply caller_save_reg_within_bounds. 
    apply temp_for_parent_frame_caller_save.
    simpl. eapply Val.has_subtype; eauto. eapply agree_wt_ls; eauto.
  solve[intuition].

  (* read from a real parent stack frame *)
  subst bound bound' s cs'.
  exploit agree_outgoing. eexact FRM. eapply ARGS; eauto.
  exploit loc_arguments_acceptable; eauto. intros [A B].
  unfold slot_valid, proj_sumbool. rewrite zle_true. 
  destruct ty; reflexivity || congruence. omega.
  intros [v [A B]].
  eexists; eexists; split.
    apply corestep_plus_one. eapply Mach_exec_Mgetparam; eauto. 
    rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link). eapply TRANSL. 
      eapply agree_link; eauto.
    simpl parent_sp0.
    change (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty))
      with (offset_of_index (make_env (function_bounds f0)) (FI_arg ofs ty)).
    eapply index_contains_load_stack with (idx := FI_arg ofs ty). eauto. eauto.
    exploit agree_incoming; eauto. intros EQ; simpl in EQ.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  constructor.
    econstructor; eauto with coqlib. econstructor; eauto.
    apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto. congruence. 
    eapply agree_frame_set_reg; eauto. eapply agree_frame_set_reg; eauto. 
    apply caller_save_reg_within_bounds. 
    apply temp_for_parent_frame_caller_save.
    simpl. eapply Val.has_subtype; eauto. eapply agree_wt_ls; eauto.
  solve[intuition]. 

 (* Lgetstack, outgoing *)
  exploit agree_outgoing; eauto. intros [v [A B]].
  eexists; eexists; split.
    apply corestep_plus_one. apply Mach_exec_Mgetstack. 
    eapply index_contains_load_stack; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  constructor.
    econstructor; eauto with coqlib.
    apply agree_regs_set_reg; auto.
    apply agree_frame_set_reg; auto.
    simpl. eapply Val.has_subtype; eauto. eapply agree_wt_ls; eauto.
  solve[intuition]. }

{ (* Lsetstack *)
  set (idx := match sl with
              | Local => FI_local ofs ty
              | Incoming => FI_link (*dummy*)
              | Outgoing => FI_arg ofs ty
              end).
  assert (index_valid f idx).
    unfold idx; destruct sl.
    apply index_local_valid; auto.
    red; auto.
    apply index_arg_valid; auto.
  exploit store_index_succeeds; eauto. eapply agree_perm; eauto.
  intros [m1' STORE].
  eexists; eexists; split.
    apply corestep_plus_one. destruct sl; simpl in H0.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. eauto.
    discriminate.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. auto. 
  eexists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition. 
  constructor.
    econstructor. 
    auto.
    apply match_stacks_change_mach_mem with m2; auto.
    eauto with mem. eauto with mem. intros. 
      rewrite <- H3; eapply Mem.load_store_other; eauto. 
    eauto. eauto. auto. 
    apply agree_regs_set_slot. apply agree_regs_undef_regs; auto. 
    destruct sl.
      eapply agree_frame_set_local. eapply agree_frame_undef_locs; eauto.
      apply destroyed_by_setstack_caller_save. auto. auto. apply AGREGS. 
      assumption.   
    simpl in H0; discriminate.
      eapply agree_frame_set_outgoing. eapply agree_frame_undef_locs; eauto.
      apply destroyed_by_setstack_caller_save. auto. auto. apply AGREGS.
      assumption.  
    eauto with coqlib.
    assumption.
    (* agree_args *)
    { apply agree_args_invariant with (m' := m2); auto.
      solve[destruct PRE as [? [? [? [? ?]]]]; auto].
      eapply Mem.store_unchanged_on; eauto. }
    solve[auto].
    solve[auto].

  intuition.
  eapply Mem.store_outside_inject; eauto. 
      intros. exploit agree_inj_unique; eauto. 
        eapply restrictI_Some. eassumption.
        unfold vis.
        destruct (joinD_Some _ _ _ _ _ H6) as [EXT | [_ LOC]].
        destruct (extern_DomRng _ H7 _ _ _ EXT).
          rewrite (extBlocksTgt_locBlocksTgt _ H7 _ H11) in SPLOCT; discriminate.
        destruct (local_DomRng _ H7 _ _ _ LOC). rewrite H10. trivial.
      intros [EQ1 EQ2]; subst b' delta.
      rewrite size_type_chunk in H9.
      exploit offset_of_index_disj_stack_data_2; eauto.
      exploit agree_bounds. eauto. apply Mem.perm_cur_max. eauto. 
      omega.
  split; intros. eapply H5. assumption.
         eapply Mem.store_valid_block_1; try eassumption.
           eapply H5. assumption. }

{ (* Lop *)
  assert (Val.has_type v (mreg_type res)).
    destruct (is_move_operation op args) as [arg|] eqn:?.
    exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst op args. 
    eapply Val.has_subtype; eauto. simpl in H; inv H. eapply agree_wt_ls; eauto. 
    destruct (type_of_operation op) as [targs tres] eqn:TYOP. 
    eapply Val.has_subtype; eauto. 
    replace tres with (snd (type_of_operation op)).
    eapply type_of_operation_sound; eauto.
    red; intros. subst op. simpl in Heqo.
    destruct args; simpl in H. discriminate. destruct args. discriminate. 
      simpl in H. discriminate.
    rewrite TYOP; auto. 
  assert (exists v',
          eval_operation ge (Vptr sp' Int.zero) 
                         (transl_op (make_env (function_bounds f)) op) rs0##args m2 
          = Some v'
       /\ val_inject (restrict (as_inj mu) (vis mu)) v v').
  eapply eval_operation_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
    eapply inject_restrict; try eassumption. eapply PRE.
  destruct H1 as [v' [A B]].
  eexists; eexists; split.   
    apply corestep_plus_one. econstructor.   
    instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved. 
    exact symbols_preserved. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  constructor.
    econstructor; eauto with coqlib.
    apply agree_regs_set_reg; auto.
    rewrite transl_destroyed_by_op.  apply agree_regs_undef_regs; auto. 
    apply agree_frame_set_reg; auto. apply agree_frame_undef_locs; auto.
    apply destroyed_by_op_caller_save.
  solve[intuition]. }

{ (* Lload *)
  assert (exists a',
          eval_addressing ge (Vptr sp' Int.zero) 
                          (transl_addr (make_env (function_bounds f)) addr) rs0##args 
          = Some a'
       /\ val_inject (restrict (as_inj mu) (vis mu)) a a').
  eapply eval_addressing_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))); eauto.
  intros [v' [C D]].
  eexists; eexists; split.   
    apply corestep_plus_one. econstructor.   
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. 
      exact symbols_preserved.
    eexact C. eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  constructor.    
    econstructor; eauto with coqlib.
    apply agree_regs_set_reg. rewrite transl_destroyed_by_load. 
      apply agree_regs_undef_regs; auto. auto. 
    apply agree_frame_set_reg. apply agree_frame_undef_locs; auto.
    apply destroyed_by_load_caller_save. auto. 
    simpl. eapply Val.has_subtype; eauto. destruct a; simpl in H0; try discriminate. 
      eapply Mem.load_type; eauto.
  solve[intuition]. }

{ (* Lstore *)
  assert (exists a',
          eval_addressing ge (Vptr sp' Int.zero) 
                          (transl_addr (make_env (function_bounds f)) addr) rs0##args 
          = Some a'
       /\ val_inject (restrict (as_inj mu) (vis mu)) a a').
  eapply eval_addressing_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  assert (VINJR: val_inject (restrict (as_inj mu) (vis mu)) (rs (R src)) (rs0 src)).
     eauto.
  exploit (Mem.storev_mapped_inject (as_inj mu)); eauto.
     eapply val_inject_incr; try eassumption.
       apply restrict_incr.
     eapply val_inject_incr; try eassumption.
       apply restrict_incr.
  intros [m1' [C D]].
  eexists; eexists; split.   
    apply corestep_plus_one. econstructor. 
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. 
      exact symbols_preserved.
    eexact C. eauto.
  assert (SMV': sm_valid mu m' m1').
    destruct PRE as [RC [PG [ Glob [SMV WD]]]].
    split; intros. 
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
  exists mu.
  destruct a; inv H0. rename H2 into STORE.
  destruct a'; inv C. rename H1 into STORE'.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE'). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE'). intuition.
  constructor.
    clear VINJR.    
    econstructor; eauto with coqlib.
    eapply match_stacks_parallel_stores. eexact INJR. eexact B. eauto. eauto. auto. 
    rewrite transl_destroyed_by_store. 
    apply agree_regs_undef_regs; auto. 
    apply agree_frame_undef_locs; auto.
    eapply agree_frame_parallel_stores; eauto.
    apply destroyed_by_store_caller_save. 
    assert (NEQ: b1 <> sp1).
    { intros C. subst b1. inv B. 
      apply restrictD_Some in H3. destruct H3 as [H3 H4].
      inv AGARGS. apply agree_sp_fresh0 in H3; auto. }
    eapply agree_args_invariant; eauto.
    destruct PRE as [? [? [? [? ?]]]]; auto.
    solve[eapply Mem.store_unchanged_on; eauto].
  intuition.
  eapply REACH_Store; try eassumption. 
    inv B. destruct (restrictD_Some _ _ _ _ _ H8); trivial.
    intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
       destruct Hoff; try contradiction. subst.   
       rewrite H4 in VINJR. inv VINJR.
       solve[destruct (restrictD_Some _ _ _ _ _ H9); trivial]. }

{ (* Lcall *)
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. eexact IST.
  intros [ra D].
  assert (mtch_stack_intermediate: 
    match_stacks mu m m2 sp1 ls0
                         (Linear.Stackframe f (Vptr sp0 Int.zero) rs b :: s)
                         (Stackframe fb (Vptr sp' Int.zero) (Vptr fb ra)
                           (transl_code (make_env (function_bounds f)) b) :: cs')
                         (Linear.funsig f') (Mem.nextblock m) (Mem.nextblock m2)).
    econstructor; eauto with coqlib.
    simpl; auto.
    intros; red.
      apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
      apply loc_arguments_bounded; auto.
    eapply agree_valid_linear; eauto.
    eapply agree_valid_mach; eauto.
  assert (AGCS: agree_callee_save rs 
                  (parent_locset0 (init_locset tys0 args0) 
                                  (Linear.Stackframe f (Vptr sp0 Int.zero) rs b :: s))). 
    solve[simpl; red; auto].

  (*New: distinguish whether invoked function is internal or external - 
    in the latter case, we now perform an additional step*)
  destruct tf'.

  (*Lcall: case internal function call*)
  eexists; eexists; split.
    apply corestep_plus_one. 
     eapply Mach_exec_Mcall_internal; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  constructor.
    econstructor; eauto.
      eapply agree_wt_ls; eauto.
      inv AGARGS. constructor; auto. clear - agree_args_frame_match0 AGINITF.
      induction s; auto. simpl. destruct AGINITF. 
        left; subst; auto. solve[right; auto].
  solve[intuition].

  (*Lcall: case external function call.*)
  exploit transl_external_arguments; try eapply mtch_stack_intermediate; 
    try eassumption. left; solve[apply Zlength_cons_pos].
  intros [args' [ExtArgs' ArgsInj]].
  assert (SG: ef_sig e = Linear.funsig f'). apply sig_preserved in C; apply C.
  rewrite <- SG in ExtArgs'.
  eexists; eexists.
  split. 
     eapply corestep_plus_one.
       eapply Mach_exec_Mcall_external; eauto.
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
    eapply match_states_call_extern; eauto.
      eapply agree_wt_ls; eauto.
      inv AGARGS. constructor; auto. clear - agree_args_frame_match0 AGINITF.
      induction s; auto. subst. simpl. destruct AGINITF.
        subst; left; auto. solve[right; auto].
  solve[left; apply Zlength_cons_pos].
  solve[intuition]. }

{ (* Ltailcall_internal *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  exploit function_epilogue_correct; eauto.
  intros [rs2 [m1' [P [Q [R [S [T [U V]]]]]]]].
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  assert (MSF': match_stacks mu m m2 sp0 rs0 s cs' (Linear.funsig f') stk sp').
      eapply match_stacks_change_sig. eassumption.
      solve[apply zero_size_arguments_tailcall_possible; auto].
  clear STACKS.
  assert (MS: match_stacks mu m' m1' sp0 rs0 s cs' (Linear.funsig f') 
           (Mem.nextblock m') (Mem.nextblock m1')).
  { apply match_stacks_change_bounds with stk sp'.
    apply match_stacks_change_linear_mem with m. 
    apply match_stacks_change_mach_mem with m2.
    apply MSF'.
    eauto with mem. intros. eapply Mem.perm_free_1; eauto. 
    intros. rewrite <- H3. eapply Mem.load_free; eauto. 
    eauto with mem. intros. eapply Mem.perm_free_3; eauto. 
    apply Plt_Ple. change (Mem.valid_block m' stk). 
      eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
    apply Plt_Ple. change (Mem.valid_block m1' sp'). 
    eapply Mem.valid_block_free_1; eauto. 
    eapply agree_valid_mach; eauto. }

  (*New: distinguish whether invoked function is internal or external - 
    in the latter case, we now perform an additional step*)
  destruct f'.

  (*Mtailcall: case f' = Internal f0*)
  monadInv C.
  clear MSF'.
  eexists; eexists; split.
    eapply corestep_star_plus_trans.
      eexact S.
      eapply corestep_plus_one.
       solve[eapply Mach_exec_Mtailcall_internal; eauto].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
  split.
    eapply match_states_call_intern; eauto.
    simpl. unfold bind. rewrite EQ. reflexivity.
    apply wt_return_regs; auto. 
    eapply match_stacks_wt_locset; eauto.
    inv AGARGS; auto. 
    eapply agree_wt_ls; eauto.
    eapply agree_args_free; eauto. 
    destruct s; auto. right. 
    solve[apply zero_size_arguments_tailcall_possible; auto].
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        solve[eapply SMV; assumption].
  
  (*Mtailcall: case f' = External e*)
  exploit transl_external_arguments.
     (*previsously had eapply MSF' here.
       If MS remains the one that's used here we can probably
       elimnate MSF' here entirely)*) eapply MS.
     eassumption. eassumption. right. 
     solve[apply zero_size_arguments_tailcall_possible; auto].
  intros [targs [ExtCallArgs ArgsInj]].
  clear MSF'.
  rewrite <- (sig_preserved _ _ C) in *; simpl in *.
  monadInv C.
  eexists; eexists; split.
    eapply corestep_star_plus_trans.
      eexact S.
     eapply corestep_plus_one.
      eapply Mach_exec_Mtailcall_external; eassumption. 
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
  split.
    eapply match_states_call_extern; eauto. 
    apply wt_return_regs; auto. 
      eapply match_stacks_wt_locset; eauto.
      inv AGARGS; auto.
      eapply agree_wt_ls; eauto.
      eapply agree_args_free; eauto. 
      right. solve[apply zero_size_arguments_tailcall_possible; auto].
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        solve[eapply SMV; assumption]. }

{ (* Mbuiltin*)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  inv H. 
  exploit (inlineable_extern_inject _ _ GDE_lemma); try eassumption.
     eapply decode_longs_inject. eapply agree_reglist; eassumption.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  eexists; eexists. 
  split. eapply corestep_plus_one.
           econstructor. econstructor. eassumption.
            reflexivity. eassumption. reflexivity.
  exists mu'.
  intuition.
  split.
    econstructor; eauto with coqlib. 
    eapply (match_stack_change_extcall_intern m m' m2 tm' sp1 ls0 mu); try assumption.
        eapply external_call_mem_forward; eassumption.
        eapply external_call_mem_forward; eassumption.
      apply Plt_Ple. change (Mem.valid_block m sp0). eapply agree_valid_linear; eauto.
      apply Plt_Ple. change (Mem.valid_block m2 sp'). eapply agree_valid_mach; eauto.
    apply agree_regs_set_regs; auto. apply agree_regs_undef_regs; auto.
             eapply agree_regs_inject_incr; eauto.
               eapply intern_incr_restrict; eassumption.
             eapply encode_long_inject; eassumption.
    apply agree_frame_set_regs; auto.
        apply agree_frame_undef_regs; auto.
             eapply agree_frame_inject_incr. 
             eapply agree_frame_invariant; try eassumption.
               intros. eapply external_call_mem_forward; eassumption.
               intros. eapply external_call_mem_forward; try eassumption.
                        eapply AGFRAME.
               intros. eapply external_call_mem_forward; eassumption.
               intros. eapply Mem.load_unchanged_on; try eassumption.
                       red; intros.
                       exploit agree_inj_unique. eapply  AGFRAME. eassumption.
                         intros [SP DD]; subst.
                       intros N. exploit agree_bounds. eapply AGFRAME. eapply N. intros.
                       destruct H; omega. 
               intros. eapply OUTOFREACH; trivial.
                       red; intros.
                         exploit agree_inj_unique. eapply  AGFRAME. eassumption. 
                           intros [SP DD]; subst.
                         intros N. exploit agree_bounds. eapply AGFRAME. eapply N. intros.
                         destruct H; omega.
                       eapply Mem.perm_valid_block; eassumption.
                  eapply intern_incr_restrict; eassumption.
                  apply sm_inject_separated_mem in SEPARATED.
                    red; intros. destruct (restrictD_Some _ _ _ _ _ H2); clear H2.
                      destruct (restrictD_None' _ _ _ H); clear H.
                        eapply SEPARATED; eassumption.
                      destruct H2 as [bb2 [dd2 [AI1 Vis]]].
                      rewrite (intern_incr_vis_inv _ _ WD WD' INCR _ _ _ AI1 H4) in Vis. 
                      discriminate.
                    assumption.
              eapply AGFRAME.
        rewrite list_Loc_type_mreg. eapply Val.has_subtype_list. eassumption. 
           eapply external_call_well_typed'. econstructor. eapply H1. trivial.
    eapply INCR. assumption.
    (* agree_args *)
    eapply agree_args_intern_incr; eauto.
    apply (BuiltinEffect_unchOn hf) in EC.
    apply agree_args_invariant with (m' := m2); auto.
    eapply mem_unchanged_on_sub; eauto.
    intros ? ? ?; subst. intros b0 ofs0 RES. 
    apply restrictD_Some in RES. destruct RES as [INJ' VIS].
    inv AGARGS. apply agree_sp_fresh0 in INJ'. solve[auto]. solve[auto].
  intuition.
  eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
  assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
    solve[rewrite <- FRG; apply Glob; assumption]. }

{ (* Llabel *)
  eexists; eexists; split.
    apply corestep_plus_one; apply Mach_exec_Mlabel.
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
    econstructor; eauto with coqlib.
    intuition. }

{ (* Lgoto *)
  eexists; eexists; split.
    apply corestep_plus_one; eapply Mach_exec_Mgoto; eauto.
    apply transl_find_label; eauto.
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
    econstructor; eauto. 
      eapply find_label_tail; eauto.
    intuition. }

{ (* Lcond, true *)
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  eexists; eexists; split.
    apply corestep_plus_one. eapply Mach_exec_Mcond_true; eauto.
    eapply eval_condition_inject with (f:=(restrict (as_inj mu) (vis mu))); eauto.
      eapply agree_reglist; eauto.
      eapply transl_find_label; eauto.
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
    econstructor. eauto. eauto. eauto. eauto. eauto.
    apply agree_frame_undef_locs; auto. 
    apply destroyed_by_cond_caller_save; auto.
    eapply find_label_tail; eauto. auto. auto. auto. auto.
  solve[intuition]. }

{ (* Lcond, false *)
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  eexists; eexists; split.
    apply corestep_plus_one. eapply Mach_exec_Mcond_false; eauto.
    eapply eval_condition_inject with (f:=(restrict (as_inj mu) (vis mu))); eauto.
    eapply agree_reglist; eauto.
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
    econstructor. eauto. eauto. eauto. eauto. eauto. 
    apply agree_frame_undef_locs; auto. apply destroyed_by_cond_caller_save. 
    eauto with coqlib. auto. auto. auto. auto.
  solve[intuition]. }

{ (* Ljumptable *)
  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite H. intro IJ; inv IJ; auto. }
  eexists; eexists; split.
    apply corestep_plus_one; eapply Mach_exec_Mjumptable; eauto. 
    apply transl_find_label; eauto.
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
    econstructor. eauto. eauto. eauto. eauto. eauto. 
    apply agree_frame_undef_locs; auto. apply destroyed_by_jumptable_caller_save.
    eapply find_label_tail; eauto. auto. auto. auto. auto.
  solve[intuition]. }

{ (* Lreturn *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption. 
  exploit function_epilogue_correct; eauto.
  intros [rs2 [m1' [P [Q [R [S [T [U V]]]]]]]].
  eexists; eexists; split.
    eapply corestep_star_plus_trans. eexact S.
    eapply corestep_plus_one. econstructor; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
  split.  
    assert (FNSIG: Linear.fn_sig f=fn_sig tf).
    { rewrite (unfold_transf_function _ _ TRANSL); trivial. }
    rewrite FNSIG. eapply match_states_return; eauto.
    apply match_stacks_change_bounds with stk sp'.
    apply match_stacks_change_linear_mem with m.  
    apply match_stacks_change_mach_mem with m2. eauto. 
    eauto with mem. intros. eapply Mem.perm_free_1; eauto. 
    intros. rewrite <- H1. eapply Mem.load_free; eauto. 
    eauto with mem. intros. eapply Mem.perm_free_3; eauto. 
    apply Plt_Ple. change (Mem.valid_block m' stk). 
      eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
    apply Plt_Ple. change (Mem.valid_block m1' sp'). 
      eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
    apply wt_return_regs; auto. eapply match_stacks_wt_locset; eauto. 
    solve[inv AGARGS; auto].
    eapply agree_wt_ls; eauto.
    solve[eapply agree_args_free; eauto]. 
  intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption. }

{ (* initial function *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]]. 
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f0); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  set (tys := sig_args (Linear.fn_sig f0)).
  assert (exists z, args_len_rec args tys = Some z).
  { eapply args_len_rec_succeeds; eauto. }
  destruct H as [z ARGSLEN]. 
  case_eq (Mem.alloc m2 0 (4*z)). intros m3 sp0 ALLOC.
  assert (STORE: exists m4, store_args m3 sp0 args tys = Some m4).
  { unfold store_args; eapply store_args_rec_succeeds; eauto.
    admit. (*TODO: initial_core should fail if arguments don't fit in address space*) }
  destruct STORE as [m4 STORE].
  eexists; eexists; split.
    eapply corestep_plus_one. simpl. econstructor; eauto.
  exists (alloc_right_sm mu sp0); intuition.
  apply alloc_right_sm_intern_incr.
  split. rewrite alloc_right_sm_as_inj; intros ? ? ? -> ?; congruence.
  split. rewrite alloc_right_sm_DomSrc; intros ? -> ?; congruence.
  intros ? H. rewrite alloc_right_sm_DomTgt. rewrite H, orb_true_iff.
  intros [Y|Y]; try solve[intros; congruence]. 
  unfold eq_block in Y. cut (b2 = sp0). intros. subst b2. clear Y.
  eapply Mem.fresh_block_alloc; eauto.
  solve[destruct (peq b2 sp0); try simpl in Y; congruence].
  (*TODO: sm_locally_allocated_alloc_right_sm*)
  { rewrite sm_locally_allocatedChar.
  assert (locBlocksSrc (alloc_right_sm mu sp0) = locBlocksSrc mu) as -> by auto.
  assert (locBlocksTgt (alloc_right_sm mu sp0) 
        = (fun b => eq_block b sp0 || locBlocksTgt mu b)) as -> by auto.
  assert (extBlocksSrc (alloc_right_sm mu sp0) = extBlocksSrc mu) as -> by auto.
  assert (extBlocksTgt (alloc_right_sm mu sp0) = extBlocksTgt mu) as -> by auto.
  assert (DomSrc (alloc_right_sm mu sp0) = DomSrc mu) as -> by auto.
  cut (freshloc m2 m4 = fun b => eq_block b sp0). intros ->.
  split; auto. extensionality b. 
    solve[rewrite freshloc_irrefl, orb_comm; simpl; auto].
  split; auto. extensionality b. simpl. unfold DomTgt. destruct mu; simpl.
    solve[rewrite <-orb_assoc, orb_comm; auto].
  split; auto. extensionality b. 
    solve[rewrite freshloc_irrefl, orb_comm; simpl; auto].
  split; auto. extensionality b. solve[rewrite orb_comm; auto].
  assert (F: freshloc m3 m4 = fun b => false). 
  {  apply store_args_rec_only_stores in STORE. clear - STORE. 
     induction STORE. extensionality b. rewrite freshloc_irrefl; auto.
     apply extensionality. intros b'. 
     generalize e as e'; intro. apply store_freshloc in e. 
     rewrite <-freshloc_trans with (m'':=m''), e, IHSTORE; simpl; auto.
     apply store_forward in e'; auto. apply only_stores_fwd in STORE; auto. }
  assert (freshloc m2 m4 = freshloc m2 m3) as ->.
  { extensionality b; rewrite <-freshloc_trans with (m'' := m3), F, orb_comm; auto.
    apply alloc_forward in ALLOC; auto.    
    apply store_args_fwd in STORE; auto. }
  apply freshloc_alloc in ALLOC; rewrite ALLOC; auto. }
  split.
  apply match_states_call_intern with (tf := tfn); auto.
  admit. (*TODO: match_globalenvs*)
  simpl. unfold bind. solve[rewrite TRANSL; auto].
  intros r. simpl. solve[rewrite Regmap.gi, NOREGS; auto].
  simpl. unfold agree_callee_save. 
    destruct l. intros _. simpl. rewrite NOREGS; auto.
    intros _. simpl. solve[destruct sl; auto]. 
  constructor; auto. 
  destruct ARGS0 as [args0 [_ Y]]. clear - Y. subst rs0. 
  solve[apply wt_init_locset].
  simpl; auto. destruct ARGS0 as [args0 [ARGS0 _]].
  solve[eexists; eapply val_list_inject_forall_inject; eauto].
  eapply store_args_contains; eauto. omega. 
  assert (OVER: 4*(2*Zlength args) <= Int.max_unsigned). admit. (*TODO: no overflow check*)
  solve[apply OVER].
  solve[apply val_has_type_list_func_charact; apply HASTY].
  rewrite alloc_right_sm_as_inj. intros b0 z0 ASINJ. destruct SMV as [H H0]. 
    specialize (H0 sp0). exploit H0. unfold RNG.
    apply as_inj_DomRng in ASINJ. destruct ASINJ; auto. auto. 
    intros VAL. apply Mem.fresh_block_alloc in ALLOC. solve[apply ALLOC; auto].
  rewrite alloc_right_sm_locBlocksTgt, orb_true_iff; left.
  solve[destruct (eq_block sp0 sp0); auto].
  intuition.
  rewrite alloc_right_sm_as_inj. generalize ALLOC as ALLOC'; intro.
  eapply Mem.alloc_right_inject in ALLOC; eauto.
  { apply store_args_rec_only_stores in STORE. 
    assert (H: forall b0 ofs, as_inj mu b0 = Some (sp0,ofs) -> False). 
    { intros b0 ofs INJ'. destruct SMV as [H H0]. 
      apply Mem.fresh_block_alloc in ALLOC'. apply ALLOC'. apply H0.
      unfold RNG. exploit as_inj_DomRng; eauto. intros [? ?]; auto. }
    clear - STORE ALLOC H. revert m ALLOC; induction STORE; auto.
    intros m0 INJ. eapply IHSTORE. eapply Mem.store_outside_inject; eauto. }
  cut (sm_valid (alloc_right_sm mu sp0) m m3). intro H.
  { clear - H STORE. destruct H. apply store_args_rec_only_stores in STORE. 
    split; auto. intros b2 H2. specialize (H0 _ H2). clear - H0 STORE.
    induction STORE; auto. apply IHSTORE. eapply Mem.store_valid_block_1; eauto. }
  clear - SMV ALLOC. split. intros b1 H. 
  unfold DOM in H. rewrite alloc_right_sm_DomSrc in H. 
  destruct SMV as [A B]. solve[apply A; auto].
  intros b2 H. unfold RNG in H. rewrite alloc_right_sm_DomTgt in H. 
  destruct (eq_block b2 sp0). subst sp0.
  eapply Mem.valid_new_block; eauto.
  eapply Mem.valid_block_alloc in ALLOC; eauto. 
  destruct SMV as [A B]. apply B. simpl in H. unfold RNG. rewrite H; auto.
  apply alloc_right_sm_wd; auto.
  destruct SMV. case_eq (DomTgt mu sp0); auto. intros Q.
  unfold RNG in H0. specialize (H0 _ Q). 
  apply Mem.fresh_block_alloc in ALLOC. exfalso. solve[apply ALLOC; auto]. }

{ (* internal function *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]]. 
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  exploit function_prologue_correct; eauto.
    eapply match_stacks_type_sp; eauto. 
    eapply match_stacks_type_retaddr; eauto.
  intros [mu' [rs' [m2' [sp' [m3' [m4' [m5' [A [B [C [D [E [F [G 
            [J [K [L [LOCALLOC' [WD' [SMV' [spLocalTgt' RC']]]]]]]]]]]]]]]]]]]]].
  eexists; eexists; split.
    eapply corestep_plus_star_trans.
      eapply corestep_plus_one. econstructor; eauto. 
      rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body. 
      eexact D.
  generalize (Mem.alloc_result _ _ _ _ _ H). intro SP_EQ. 
  generalize (Mem.alloc_result _ _ _ _ _ A). intro SP'_EQ.
  exists mu'.
  intuition. 
  split. 
    assert (SPNEQ: sp0 <> sp'). 
    { subst. cut (Mem.valid_block m2 sp0). intros VAL CONTRA. subst.
      unfold Mem.valid_block in VAL. 
      apply SimplLocals.VSet.MSet.Raw.L.MO.lt_irrefl in VAL; auto.
      generalize (agree_sp_local _ _ _ _ _ _ _ _ AGARGS); intros LOC. 
      destruct SMV as [H0 H1]. apply H1. 
      unfold RNG, DomTgt. rewrite orb_true_iff. solve[left; auto]. }
    econstructor; eauto. 
      apply match_stacks_change_mach_mem with m2.
      apply match_stacks_change_linear_mem with m.
      rewrite SP_EQ; rewrite SP'_EQ.
      eapply match_stacks_change_meminj_intern; eauto. apply Ple_refl. 
      eauto with mem. intros. exploit Mem.perm_alloc_inv. eexact H. eauto. 
      rewrite dec_eq_false; auto. 
      intros. eapply stores_in_frame_valid; eauto with mem. 
      intros. eapply stores_in_frame_perm; eauto with mem.
      intros. rewrite <- H1. transitivity (Mem.load chunk m2' b ofs). 
        eapply stores_in_frame_contents; eauto.
      eapply Mem.load_alloc_unchanged; eauto. red. congruence.
      eapply transf_function_well_typed; eauto.
      auto with coqlib.
      revert AGARGS. destruct s. intros ARGS.
        eapply agree_args_stores_in_frame; eauto.
        eapply agree_args_alloc; eauto.
        eapply agree_args_intern_incr; eauto.
      intros AGARGS.
        eapply agree_args_stores_in_frame; eauto.
        eapply agree_args_alloc; eauto.
        solve[eapply agree_args_intern_incr; eauto].
        revert AGINITF. destruct s; auto. intros [Y|Y].
        solve[inv Y; auto]. solve[auto].
    intuition.
    eapply (intern_incr_meminj_preserves_globals_as_inj _ mu); trivial.
      split; assumption.
    eapply (intern_incr_meminj_preserves_globals_as_inj ge mu); trivial.
      split; assumption. }

{ (* external function *)
     apply bind_inversion in TRANSL. 
    destruct TRANSL as [ff [FT X]]. discriminate. }

{ monadInv TRANSL. }

{ (*nonobservable extern function*)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  simpl in TRANSL. inversion TRANSL; subst tf.
  inv H0. 
  exploit transl_external_arguments; try eassumption.
  intros [vl [ARGS VINJ]].
  assert (VL: vl = args1).
    eapply transl_external_arguments_fun; try eassumption. trivial.
  subst vl.
  exploit (inlineable_extern_inject _ _ GDE_lemma); try eapply H.
     eassumption. 
     Focus 8. eapply decode_longs_inject. eapply VINJ. 
     assumption. eassumption. assumption. assumption.
     eapply EFhelpers; eassumption. assumption. assumption. 
  intros [mu' [vres' [tm' [EC [RINJ' [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  eexists; exists tm'.
  split. simpl.
           apply corestep_plus_one. 
              eapply Mach_exec_function_external; try assumption.
              econstructor. eapply EC.
              reflexivity. reflexivity. 
          (*eapply external_call_symbols_preserved'; eauto.
            exact symbols_preserved. exact varinfo_preserved.*)
  exists mu'.  
  assert (STACKS': match_stacks mu' m' tm' sp0 ls0 s cs' 
           (Linear.funsig (External ef))
           (Mem.nextblock m') (Mem.nextblock tm')).
      apply match_stacks_change_bounds
           with (Mem.nextblock m) (Mem.nextblock m2).
        eapply match_stack_change_extcall_intern; try eapply STACKS.
          eapply external_call_mem_forward; eassumption.
          eapply external_call_mem_forward; eassumption.
          assumption. assumption. assumption. assumption. assumption.
          apply Ple_refl. apply Ple_refl. 
       eapply external_call_nextblock'. econstructor; eauto.
       eapply external_call_nextblock'. econstructor; eauto.
  clear STACKS.
  assert (WTL: wt_locset (Locmap.setlist R ## (loc_result (ef_sig ef))
                  (encode_long (sig_res (ef_sig ef)) v) rs1)).
     apply wt_setlist_result. 
       eapply external_call_well_typed; eauto. auto.
  assert (AGREGS': agree_regs (restrict (as_inj mu') (vis mu'))
             (Locmap.setlist R ## (loc_result (ef_sig ef))
                 (encode_long (sig_res (ef_sig ef)) v) rs1)
             (set_regs (loc_result (ef_sig ef))
                (encode_long (sig_res (ef_sig ef)) vres') rs)).
    apply agree_regs_set_regs; auto. 
    eapply agree_regs_inject_incr; try eassumption.
    eapply intern_incr_restrict; eassumption. 
    eapply encode_long_inject; eassumption.
  assert (AGCalleeSave: agree_callee_save
             (Locmap.setlist R ## (loc_result (ef_sig ef))
               (encode_long (sig_res (ef_sig ef)) v) rs1)
             (parent_locset0 ls0 s)).
    apply agree_callee_save_set_result. assumption. 
  split; trivial.
  split; trivial.
  split; trivial.
  split. clear AGREGS.
    econstructor; eauto.
     eapply agree_args_intern_incr; try eassumption.
      eapply agree_args_invariant; try eapply AGARGS. assumption.
      eapply mem_unchanged_on_sub; try eassumption.
       unfold loc_out_of_reach; intros; subst b.
         destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
         intros N.
         eapply agree_sp_fresh; eassumption.
  split. assumption.
  split. auto.
  split. 
    eapply (intern_incr_meminj_preserves_globals_as_inj _ mu); trivial.
      split; assumption.
  split.
    eapply (intern_incr_meminj_preserves_globals_as_inj ge mu); trivial.
      split; assumption.
  split; assumption. }

{ (* return *)
  inv STACKS. simpl in AGLOCS.  
  eexists; eexists; split.
    apply corestep_plus_one. apply Mach_exec_return. 
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
  split.  
    econstructor; eauto. 
    eapply agree_frame_return; eauto.
    inv AGARGS. constructor; auto. simpl in *. destruct s; auto. simpl; auto.
    intros C. subst sp'. inv AGARGS. eapply agree_sp_fresh0.
    inv FRM. apply restrictD_Some in agree_inj0. 
    destruct agree_inj0 as [X Y]. solve[apply X].
    inv AGARGS. revert agree_args_frame_match0. simpl. destruct s; auto.
    intros [Y|Y]. left; inv Y; auto. right; auto.
  solve[intuition]. }
Qed.

Lemma MATCH_eff_diagram: forall st1 m1 st1' m1' (U1 : block -> Z -> bool)
        (CS: effstep (Linear_eff_sem hf) ge U1 st1 m1 st1' m1')
        st2 mu m2 (MTCH: MATCH st1 mu st1 m1 st2 m2)
        (HypU1: forall b ofs, U1 b ofs = true -> vis mu b = true),
     exists st2' m2' U2,
      effstep_plus (Mach_eff_sem hf return_address_offset) tge U2 st2 m2 st2' m2' /\
     exists mu', intern_incr mu mu' /\
          sm_inject_separated mu mu' m1 m2 /\
          sm_locally_allocated mu mu' m1 m2 m1' m2' /\
          MATCH st1' mu' st1' m1' st2' m2' /\
     (forall (b : block) (ofs : Z),
      U2 b ofs = true ->
      visTgt mu b = true /\
      (locBlocksTgt mu b = false ->
       exists (b1 : block) (delta1 : Z),
         foreign_of mu b1 = Some (b, delta1) /\
         U1 b1 (ofs - delta1) = true /\
         Mem.perm m1 b1 (ofs - delta1) Max Nonempty)).
Proof.  
intros.
  assert (USEWTF: forall f i c,
          wt_function f = true -> is_tail (i :: c) (Linear.fn_code f) ->
          wt_instr f i = true).
    intros. unfold wt_function, wt_code in H. rewrite forallb_forall in H.
    apply H. eapply is_tail_in; eauto. 
assert(SymbPres := symbols_preserved).
destruct CS; intros; destruct MTCH as [MS [INJ PRE]];
  try inv MS;
  try rewrite transl_code_eq;
  try (generalize (USEWTF _ _ _ WTF TAIL); intro WTI; simpl in WTI; InvBooleans);
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.

{ (* Lgetstack *)
  destruct BOUND. unfold destroyed_by_getstack; destruct sl.
  (* Lgetstack, local *)
  exploit agree_locals; eauto. intros [v [A B]].
  eexists; eexists; eexists; split.
    apply effstep_plus_one. apply Mach_effexec_Mgetstack. 
    solve[eapply index_contains_load_stack; eauto].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). solve[intuition].
  split.
    constructor.
      econstructor; eauto with coqlib.
      apply agree_regs_set_reg; auto. simpl. apply agree_frame_set_reg; auto. 
        simpl. eapply Val.has_subtype; eauto. 
        solve[eapply agree_wt_ls; eauto].
    solve[intuition]. 
   intuition. 

 (* Lgetstack, incoming *)
  unfold slot_valid in H0. InvBooleans.
  exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  inversion STACKS; clear STACKS.
  subst. 

  (* read from dummy frame *)
  generalize AGARGS as AGARGS'; intro.
  inv AGARGS. simpl in *. destruct agree_args_inj0 as [args1 X].
  exploit agree_args_match_contain; eauto. 
  destruct AGINITF as [Y|Y]. subst. solve[eauto]. solve[elim (Y _ IN_ARGS)].
  intros [v [LD VINJ]]. 
  eexists; eexists. eexists; split. 
  apply effstep_plus_one. econstructor; eauto.
    rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link). eapply TRANSL. 
      solve[eapply agree_link; eauto].
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      clear AGINITF. intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  split.
    constructor.
      econstructor; eauto with coqlib. econstructor; eauto.
      apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto. 
      cut (rs (S Incoming ofs ty) = ls0 (S Incoming ofs ty)). solve[intros ->; auto].
      inv AGFRAME. solve[rewrite agree_incoming0; auto].
      eapply agree_frame_set_reg; eauto. eapply agree_frame_set_reg; eauto. 
      apply caller_save_reg_within_bounds. 
      apply temp_for_parent_frame_caller_save.
      simpl. eapply Val.has_subtype; eauto. eapply agree_wt_ls; eauto.
    solve[intuition].
  intuition.

  (* read from a real parent stack frame *)
  subst bound bound' s cs'.
  exploit agree_outgoing. eexact FRM. eapply ARGS; eauto.
  exploit loc_arguments_acceptable; eauto. intros [A B].
  unfold slot_valid, proj_sumbool. rewrite zle_true. 
  destruct ty; reflexivity || congruence. omega.
  intros [v [A B]].
  eexists; eexists; eexists; split.
    apply effstep_plus_one. eapply Mach_effexec_Mgetparam; eauto. 
    rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs. 
    eapply index_contains_load_stack with (idx := FI_link). eapply TRANSL. 
      eapply agree_link; eauto.
    simpl parent_sp0.
    change (offset_of_index (make_env (function_bounds f)) (FI_arg ofs ty))
      with (offset_of_index (make_env (function_bounds f0)) (FI_arg ofs ty)).
    eapply index_contains_load_stack with (idx := FI_arg ofs ty). eauto. eauto.
    exploit agree_incoming; eauto. intros EQ; simpl in EQ.
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
    constructor.
      econstructor; eauto with coqlib. econstructor; eauto.
      apply agree_regs_set_reg. apply agree_regs_set_reg. auto. auto. congruence. 
      eapply agree_frame_set_reg; eauto. eapply agree_frame_set_reg; eauto. 
      apply caller_save_reg_within_bounds. 
      apply temp_for_parent_frame_caller_save.
      simpl. eapply Val.has_subtype; eauto. eapply agree_wt_ls; eauto.
    solve[intuition]. 
  intuition.

 (* Lgetstack, outgoing *)
  exploit agree_outgoing; eauto. intros [v [A B]].
  eexists; eexists; eexists; split.
    apply effstep_plus_one. apply Mach_effexec_Mgetstack. 
    eapply index_contains_load_stack; eauto.
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
    constructor.
      econstructor; eauto with coqlib.
      apply agree_regs_set_reg; auto.
      apply agree_frame_set_reg; auto.
      simpl. eapply Val.has_subtype; eauto. eapply agree_wt_ls; eauto.
    solve[intuition].
  intuition. }

{ (* Lsetstack *)
  set (idx := match sl with
              | Local => FI_local ofs ty
              | Incoming => FI_link (*dummy*)
              | Outgoing => FI_arg ofs ty
              end).
  assert (index_valid f idx).
    unfold idx; destruct sl.
    apply index_local_valid; auto.
    red; auto.
    apply index_arg_valid; auto.
  exploit store_index_succeeds; eauto. eapply agree_perm; eauto.
  intros [m1' STORE].
  eexists; eexists.
  exists (StoreEffect
        (Val.add (Vptr sp' Int.zero)
           (Vint
              (Int.repr
                 (offset_of_index (make_env (function_bounds f))
                    idx))))
        (encode_val (chunk_of_type ty) (rs0 src))).
  split.
    apply effstep_plus_one. destruct sl; simpl in H0.
      econstructor. eapply store_stack_succeeds with (idx := idx); eauto. eauto.
    discriminate.
    econstructor. eapply store_stack_succeeds with (idx := idx); eauto. auto. 
  eexists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition. 
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition. 
  split.
    constructor.
     {(*match_states*)
      econstructor. 
      auto.
      apply match_stacks_change_mach_mem with m2; auto.
      eauto with mem. eauto with mem. intros. 
        rewrite <- H3; eapply Mem.load_store_other; eauto. 
      eauto. eauto. auto. 
      apply agree_regs_set_slot. apply agree_regs_undef_regs; auto. 
      destruct sl.
        eapply agree_frame_set_local. eapply agree_frame_undef_locs; eauto.
        apply destroyed_by_setstack_caller_save. auto. auto. apply AGREGS. 
        assumption.   
      simpl in H0; discriminate.
        eapply agree_frame_set_outgoing. eapply agree_frame_undef_locs; eauto.
        apply destroyed_by_setstack_caller_save. auto. auto. apply AGREGS.
        assumption.  
      eauto with coqlib.
      assumption.
      (* agree_args *)
      { apply agree_args_invariant with (m' := m2); auto.
        solve[destruct PRE as [? [? [? [? ?]]]]; auto].
        eapply Mem.store_unchanged_on; eauto. }
      solve[auto].
      solve[auto].
    }
    intuition.
    eapply Mem.store_outside_inject; eauto. 
      intros. exploit agree_inj_unique; eauto. 
        eapply restrictI_Some. eassumption.
        unfold vis.
        destruct (joinD_Some _ _ _ _ _ H6) as [EXT | [_ LOC]].
        destruct (extern_DomRng _ H7 _ _ _ EXT).
          rewrite (extBlocksTgt_locBlocksTgt _ H7 _ H11) in SPLOCT; discriminate.
        destruct (local_DomRng _ H7 _ _ _ LOC). rewrite H10. trivial.
      intros [EQ1 EQ2]; subst b' delta.
      rewrite size_type_chunk in H9.
      exploit offset_of_index_disj_stack_data_2; eauto.
      exploit agree_bounds. eauto. apply Mem.perm_cur_max. eauto. 
      omega.
    split; intros. eapply H5. assumption.
         eapply Mem.store_valid_block_1; try eassumption.
           eapply H5. assumption.
 (*effect propagation*)
   simpl. intros. 
   destruct (eq_block sp' b0); simpl in *; try discriminate.
     subst b0. unfold visTgt; rewrite SPLOCT; intuition. }

{ (* Lop *)
  assert (Val.has_type v (mreg_type res)).
    destruct (is_move_operation op args) as [arg|] eqn:?.
    exploit is_move_operation_correct; eauto. intros [EQ1 EQ2]; subst op args. 
    eapply Val.has_subtype; eauto. simpl in H; inv H. eapply agree_wt_ls; eauto. 
    destruct (type_of_operation op) as [targs tres] eqn:TYOP. 
    eapply Val.has_subtype; eauto. 
    replace tres with (snd (type_of_operation op)).
    eapply type_of_operation_sound; eauto.
    red; intros. subst op. simpl in Heqo.
    destruct args; simpl in H. discriminate. destruct args. discriminate. 
      simpl in H. discriminate.
    rewrite TYOP; auto. 
  assert (exists v',
          eval_operation ge (Vptr sp' Int.zero) 
                         (transl_op (make_env (function_bounds f)) op) rs0##args m2 
          = Some v'
       /\ val_inject (restrict (as_inj mu) (vis mu)) v v').
  eapply eval_operation_inject; eauto.
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
    eapply inject_restrict; try eassumption. eapply PRE.
  destruct H1 as [v' [A B]].
  eexists; eexists; eexists; split.   
    apply effstep_plus_one. econstructor.   
    instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved. 
    exact symbols_preserved. eauto.
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
    constructor.
      econstructor; eauto with coqlib.
      apply agree_regs_set_reg; auto.
      rewrite transl_destroyed_by_op.  apply agree_regs_undef_regs; auto. 
      apply agree_frame_set_reg; auto. apply agree_frame_undef_locs; auto.
      apply destroyed_by_op_caller_save.
    solve[intuition]. 
  intuition. }

{ (* Lload *)
  assert (exists a',
          eval_addressing ge (Vptr sp' Int.zero) 
                          (transl_addr (make_env (function_bounds f)) addr) rs0##args 
          = Some a'
       /\ val_inject (restrict (as_inj mu) (vis mu)) a a').
  eapply eval_addressing_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  exploit (Mem.loadv_inject (restrict (as_inj mu) (vis mu))); eauto.
  intros [v' [C D]].
  eexists; eexists; eexists; split.   
    apply effstep_plus_one. econstructor.   
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. 
      exact symbols_preserved.
    eexact C. eauto.
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
    constructor.    
      econstructor; eauto with coqlib.
      apply agree_regs_set_reg. rewrite transl_destroyed_by_load. 
        apply agree_regs_undef_regs; auto. auto. 
      apply agree_frame_set_reg. apply agree_frame_undef_locs; auto.
      apply destroyed_by_load_caller_save. auto. 
      simpl. eapply Val.has_subtype; eauto. destruct a; simpl in H0; try discriminate. 
        eapply Mem.load_type; eauto.
    solve[intuition].
  intuition. }

{ (* Lstore *)
  assert (exists a',
          eval_addressing ge (Vptr sp' Int.zero) 
                          (transl_addr (make_env (function_bounds f)) addr) rs0##args 
          = Some a'
       /\ val_inject (restrict (as_inj mu) (vis mu)) a a').
  eapply eval_addressing_inject; eauto. 
  eapply match_stacks_preserves_globals; eauto.
  eapply agree_inj; eauto. eapply agree_reglist; eauto.
  destruct H1 as [a' [A B]].
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  assert (VINJR: val_inject (restrict (as_inj mu) (vis mu)) (rs (R src)) (rs0 src)).
     eauto.
  exploit (Mem.storev_mapped_inject (as_inj mu)); eauto.
     eapply val_inject_incr; try eassumption.
       apply restrict_incr.
     eapply val_inject_incr; try eassumption.
       apply restrict_incr.
  intros [m1' [C D]].
  eexists; eexists; eexists; split.   
    apply effstep_plus_one. econstructor. 
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. 
      exact symbols_preserved.
    eexact C. eauto.
  assert (SMV': sm_valid mu m' m1').
    destruct PRE as [RC [PG [ Glob [SMV WD]]]].
    split; intros. 
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
      eapply storev_valid_block_1; try eassumption.
        eapply SMV; assumption.
  exists mu.
  destruct a; inv H0. rename H2 into STORE.
  destruct a'; inv C. rename H1 into STORE'.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE'). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE). intuition.
      apply extensionality; intros; rewrite (store_freshloc _ _ _ _ _ _ STORE'). intuition.
  split. 
  { (*MATCH*)
    constructor.
    clear VINJR.    
    econstructor; eauto with coqlib.
    eapply match_stacks_parallel_stores. eexact INJR. eexact B. eauto. eauto. auto. 
    rewrite transl_destroyed_by_store. 
    apply agree_regs_undef_regs; auto. 
    apply agree_frame_undef_locs; auto.
    eapply agree_frame_parallel_stores; eauto.
    apply destroyed_by_store_caller_save. 
    assert (NEQ: b1 <> sp1).
    { intros C. subst b1. inv B. 
      apply restrictD_Some in H3. destruct H3 as [H3 H4].
      inv AGARGS. apply agree_sp_fresh0 in H3; auto. }
    eapply agree_args_invariant; eauto.
    destruct PRE as [? [? [? [? ?]]]]; auto.
    solve[eapply Mem.store_unchanged_on; eauto].
  intuition.
  eapply REACH_Store; try eassumption. 
    inv B. destruct (restrictD_Some _ _ _ _ _ H8); trivial.
    intros b' Hb'. rewrite getBlocks_char in Hb'. destruct Hb' as [off Hoff].
       destruct Hoff; try contradiction. subst.   
       rewrite H4 in VINJR. inv VINJR.
       solve[destruct (restrictD_Some _ _ _ _ _ H9); trivial].
   }
   (*effect propagation*)
  intros.
    destruct PRE as [RC [PG [ Glob [SMV WD]]]].
    split. destruct (StoreEffectD _ _ _ _ H0) as [ii [HI OFF]].
           inv HI. inv B.
           eapply visPropagateR; eassumption.
    intros. eapply StoreEffect_PropagateLeft; try eassumption. }

{ (* Lcall *)
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. eexact IST.
  intros [ra D].
  assert (mtch_stack_intermediate: 
    match_stacks mu m m2 sp1 ls0
                         (Linear.Stackframe f (Vptr sp0 Int.zero) rs b :: s)
                         (Stackframe fb (Vptr sp' Int.zero) (Vptr fb ra)
                           (transl_code (make_env (function_bounds f)) b) :: cs')
                         (Linear.funsig f') (Mem.nextblock m) (Mem.nextblock m2)).
    econstructor; eauto with coqlib.
    simpl; auto.
    intros; red.
      apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
      apply loc_arguments_bounded; auto.
    eapply agree_valid_linear; eauto.
    eapply agree_valid_mach; eauto.
  assert (AGCS: agree_callee_save rs 
                  (parent_locset0 (init_locset tys0 args0) 
                                  (Linear.Stackframe f (Vptr sp0 Int.zero) rs b :: s))). 
    solve[simpl; red; auto].

  (*New: distinguish whether invoked function is internal or external - 
    in the latter case, we now perform an additional step*)
  destruct tf'.

  (*Lcall: case internal function call*)
  eexists; eexists; eexists; split.
    apply effstep_plus_one. 
     eapply Mach_effexec_Mcall_internal; eauto.
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
    constructor.
      econstructor; eauto.
        eapply agree_wt_ls; eauto.
        inv AGARGS. constructor; auto. clear - agree_args_frame_match0 AGINITF.
        induction s; auto. simpl. destruct AGINITF. 
          left; subst; auto. solve[right; auto].
    solve[intuition].
  intuition. 

  (*Lcall: case external function call.*)
  exploit transl_external_arguments; try eapply mtch_stack_intermediate; 
    try eassumption. left; solve[apply Zlength_cons_pos].
  intros [args' [ExtArgs' ArgsInj]].
  assert (SG: ef_sig e = Linear.funsig f'). apply sig_preserved in C; apply C.
  rewrite <- SG in ExtArgs'.
  eexists; eexists; eexists.
  split. 
     eapply effstep_plus_one.
       eapply Mach_effexec_Mcall_external; eauto.
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
      eapply match_states_call_extern; eauto.
        eapply agree_wt_ls; eauto.
        inv AGARGS. constructor; auto. clear - agree_args_frame_match0 AGINITF.
        induction s; auto. subst. simpl. destruct AGINITF.
          subst; left; auto. solve[right; auto].
      solve[left; apply Zlength_cons_pos].
    solve[intuition].
  intuition. }

{ (* Ltailcall_internal *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  exploit function_epilogue_correct_eff; eauto.
  intros [rs2 [m1' [P [Q [R [S [T [U V]]]]]]]].
  exploit find_function_translated; eauto. intros [bf [tf' [A [B C]]]].
  assert (MSF': match_stacks mu m m2 sp0 rs0 s cs' (Linear.funsig f') stk sp').
      eapply match_stacks_change_sig. eassumption.
      solve[apply zero_size_arguments_tailcall_possible; auto].
  clear STACKS.
  assert (MS: match_stacks mu m' m1' sp0 rs0 s cs' (Linear.funsig f') 
           (Mem.nextblock m') (Mem.nextblock m1')).
  { apply match_stacks_change_bounds with stk sp'.
    apply match_stacks_change_linear_mem with m. 
    apply match_stacks_change_mach_mem with m2.
    apply MSF'.
    eauto with mem. intros. eapply Mem.perm_free_1; eauto. 
    intros. rewrite <- H3. eapply Mem.load_free; eauto. 
    eauto with mem. intros. eapply Mem.perm_free_3; eauto. 
    apply Plt_Ple. change (Mem.valid_block m' stk). 
      eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
    apply Plt_Ple. change (Mem.valid_block m1' sp'). 
    eapply Mem.valid_block_free_1; eauto. 
    eapply agree_valid_mach; eauto. }

  (*New: distinguish whether invoked function is internal or external - 
    in the latter case, we now perform an additional step*)
  destruct f'.

  (*Mtailcall: case f' = Internal f0*)
  monadInv C.
  clear MSF'.
  eexists; eexists; eexists; split.
    eapply effstep_star_plus_trans'.
      eexact S.
      eapply effstep_plus_one.
       solve[eapply Mach_effexec_Mtailcall_internal; eauto].
      reflexivity.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
  split.
    split.
      eapply match_states_call_intern; eauto.
      simpl. unfold bind. rewrite EQ. reflexivity.
      apply wt_return_regs; auto. 
      eapply match_stacks_wt_locset; eauto.
      inv AGARGS; auto. 
      eapply agree_wt_ls; eauto.
      eapply agree_args_free; eauto. 
      destruct s; auto. right. 
      solve[apply zero_size_arguments_tailcall_possible; auto].
    intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        solve[eapply SMV; assumption].
  unfold EmptyEffect; simpl; intros.
    apply andb_true_iff in H1. destruct H1.
    destruct AGFRAME.
    apply FreeEffectD in H1. destruct H1 as [? [VB Arith2]]; subst.
    split. eapply visPropagateR; eassumption.
    rewrite SPLOCT. intuition.
  
  (*Mtailcall: case f' = External e*)
  exploit transl_external_arguments.
     (*previsously had eapply MSF' here.
       If MS remains the one that's used here we can probably
       elimnate MSF' here entirely)*) eapply MS.
     eassumption. eassumption. right. 
     solve[apply zero_size_arguments_tailcall_possible; auto].
  intros [targs [ExtCallArgs ArgsInj]].
  clear MSF'.
  rewrite <- (sig_preserved _ _ C) in *; simpl in *.
  monadInv C.
  eexists; eexists; eexists; split.
    eapply effstep_star_plus_trans'.
      eexact S.
     eapply effstep_plus_one.
      eapply Mach_effexec_Mtailcall_external; eassumption. 
     reflexivity.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H2). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
  split.
    split. 
      eapply match_states_call_extern; eauto. 
      apply wt_return_regs; auto. 
        eapply match_stacks_wt_locset; eauto.
        inv AGARGS; auto.
        eapply agree_wt_ls; eauto.
        eapply agree_args_free; eauto. 
        right. solve[apply zero_size_arguments_tailcall_possible; auto].
    intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        solve[eapply SMV; assumption].
  unfold EmptyEffect; simpl; intros.
    apply andb_true_iff in H1. destruct H1.
    destruct AGFRAME.
    apply FreeEffectD in H1. destruct H1 as [? [VB Arith2]]; subst.
    split. eapply visPropagateR; eassumption.
    rewrite SPLOCT. intuition. }

{ (* Mbuiltin*)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
      assert (PGR: meminj_preserves_globals ge (restrict (as_inj mu) (vis mu))).
        rewrite <- restrict_sm_all.
        eapply restrict_sm_preserves_globals; try eassumption.
          unfold vis. intuition.
  inv H. 
  exploit (inlineable_extern_inject _ _ GDE_lemma); try eassumption.
     eapply decode_longs_inject. eapply agree_reglist; eassumption.
  intros [mu' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  eexists; eexists; eexists. 
  split. eapply effstep_plus_one.
           econstructor. econstructor. eassumption.
            reflexivity. eassumption. reflexivity.
  exists mu'.
  split. assumption.
  split. assumption.
  split. assumption.
  split. 
  { (*MATCH*)
    split.  
    econstructor; eauto with coqlib. 
    eapply (match_stack_change_extcall_intern m m' m2 tm' sp1 ls0 mu); try assumption.
        eapply external_call_mem_forward; eassumption.
        eapply external_call_mem_forward; eassumption.
      apply Plt_Ple. change (Mem.valid_block m sp0). eapply agree_valid_linear; eauto.
      apply Plt_Ple. change (Mem.valid_block m2 sp'). eapply agree_valid_mach; eauto.
    apply agree_regs_set_regs; auto. apply agree_regs_undef_regs; auto.
             eapply agree_regs_inject_incr; eauto.
               eapply intern_incr_restrict; eassumption.
             eapply encode_long_inject; eassumption.
    apply agree_frame_set_regs; auto.
        apply agree_frame_undef_regs; auto.
             eapply agree_frame_inject_incr. 
             eapply agree_frame_invariant; try eassumption.
               intros. eapply external_call_mem_forward; eassumption.
               intros. eapply external_call_mem_forward; try eassumption.
                        eapply AGFRAME.
               intros. eapply external_call_mem_forward; eassumption.
               intros. eapply Mem.load_unchanged_on; try eassumption.
                       red; intros.
                       exploit agree_inj_unique. eapply  AGFRAME. eassumption.
                         intros [SP DD]; subst.
                       intros N. exploit agree_bounds. eapply AGFRAME. eapply N. intros.
                       destruct H; omega. 
               intros. eapply OUTOFREACH; trivial.
                       red; intros.
                         exploit agree_inj_unique. eapply  AGFRAME. eassumption. 
                           intros [SP DD]; subst.
                         intros N. exploit agree_bounds. eapply AGFRAME. eapply N. intros.
                         destruct H; omega.
                       eapply Mem.perm_valid_block; eassumption.
                  eapply intern_incr_restrict; eassumption.
                  apply sm_inject_separated_mem in SEPARATED.
                    red; intros. destruct (restrictD_Some _ _ _ _ _ H2); clear H2.
                      destruct (restrictD_None' _ _ _ H); clear H.
                        eapply SEPARATED; eassumption.
                      destruct H2 as [bb2 [dd2 [AI1 Vis]]].
                      rewrite (intern_incr_vis_inv _ _ WD WD' INCR _ _ _ AI1 H4) in Vis. 
                      discriminate.
                    assumption.
              eapply AGFRAME.
        rewrite list_Loc_type_mreg. eapply Val.has_subtype_list. eassumption. 
           eapply external_call_well_typed'. econstructor. eapply H1. trivial.
    eapply INCR. assumption.
    (* agree_args *)
    eapply agree_args_intern_incr; eauto.
    apply (BuiltinEffect_unchOn hf) in EC.
    apply agree_args_invariant with (m' := m2); auto.
    eapply mem_unchanged_on_sub; eauto.
    intros ? ? ?; subst. intros b0 ofs0 RES. 
    apply restrictD_Some in RES. destruct RES as [INJ' VIS].
    inv AGARGS. apply agree_sp_fresh0 in INJ'. solve[auto]. solve[auto].
  intuition.
  eapply meminj_preserves_incr_sep. eapply PG. eassumption. 
             apply intern_incr_as_inj; trivial.
             apply sm_inject_separated_mem; eassumption.
  assert (FRG: frgnBlocksSrc mu = frgnBlocksSrc mu') by eapply INCR.
    solve[rewrite <- FRG; apply Glob; assumption]. }
  eapply BuiltinEffect_Propagate; try eassumption. 
     eapply decode_longs_inject. eapply agree_reglist; eassumption. }

{ (* Llabel *)
  eexists; eexists; eexists; split.
    apply effstep_plus_one; apply Mach_effexec_Mlabel.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition.
    split. 
      econstructor; eauto with coqlib.
      intuition. }

{ (* Lgoto *)
  eexists; eexists; eexists; split.
    apply effstep_plus_one; eapply Mach_effexec_Mgoto; eauto.
    apply transl_find_label; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition.
  split.
    econstructor; eauto. 
      eapply find_label_tail; eauto.
    intuition. }

{ (* Lcond, true *)
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  eexists; eexists; eexists; split.
    apply effstep_plus_one. eapply Mach_effexec_Mcond_true; eauto.
    eapply eval_condition_inject with (f:=(restrict (as_inj mu) (vis mu))); eauto.
      eapply agree_reglist; eauto.
      eapply transl_find_label; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition.
  split.
    econstructor. eauto. eauto. eauto. eauto. eauto.
    apply agree_frame_undef_locs; auto. 
    apply destroyed_by_cond_caller_save; auto.
    eapply find_label_tail; eauto. auto. auto. auto. auto.
  solve[intuition]. }

{ (* Lcond, false *)
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; try eassumption. eapply PRE.
  eexists; eexists; eexists; split.
    apply effstep_plus_one. eapply Mach_effexec_Mcond_false; eauto.
    eapply eval_condition_inject with (f:=(restrict (as_inj mu) (vis mu))); eauto.
    eapply agree_reglist; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition.
  split.
    econstructor. eauto. eauto. eauto. eauto. eauto. 
    apply agree_frame_undef_locs; auto. apply destroyed_by_cond_caller_save. 
    eauto with coqlib. auto. auto. auto. auto.
  solve[intuition]. }

{ (* Ljumptable *)
  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite H. intro IJ; inv IJ; auto. }
  eexists; eexists; eexists; split.
    apply effstep_plus_one; eapply Mach_effexec_Mjumptable; eauto. 
    apply transl_find_label; eauto.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
      apply extensionality; intros; rewrite (freshloc_irrefl). intuition.
  intuition.
  split.  
    econstructor. eauto. eauto. eauto. eauto. eauto. 
    apply agree_frame_undef_locs; auto. apply destroyed_by_jumptable_caller_save.
    eapply find_label_tail; eauto. auto. auto. auto. auto.
  solve[intuition]. }

{ (* Lreturn *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  assert (INJR: Mem.inject (restrict (as_inj mu) (vis mu)) m m2).
    eapply inject_restrict; eassumption. 
  exploit function_epilogue_correct_eff; eauto.
  intros [rs2 [m1' [P [Q [R [S [T [U V]]]]]]]].
  eexists; eexists; eexists; split.
    eapply effstep_star_plus_trans'. eexact S.
    eapply effstep_plus_one. econstructor; eauto.
    reflexivity.
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ H). intuition.
      apply extensionality; intros; rewrite (freshloc_free _ _ _ _ _ R). intuition.
  split.  
  { (*MATCH*)
    split.
      assert (FNSIG: Linear.fn_sig f=fn_sig tf).
      { rewrite (unfold_transf_function _ _ TRANSL); trivial. }
      rewrite FNSIG. 
      eapply match_states_return; eauto.
      apply match_stacks_change_bounds with stk sp'.
      apply match_stacks_change_linear_mem with m.  
      apply match_stacks_change_mach_mem with m2. eauto. 
      eauto with mem. intros. eapply Mem.perm_free_1; eauto. 
      intros. rewrite <- H1. eapply Mem.load_free; eauto. 
      eauto with mem. intros. eapply Mem.perm_free_3; eauto. 
      apply Plt_Ple. change (Mem.valid_block m' stk). 
        eapply Mem.valid_block_free_1; eauto. eapply agree_valid_linear; eauto. 
      apply Plt_Ple. change (Mem.valid_block m1' sp'). 
        eapply Mem.valid_block_free_1; eauto. eapply agree_valid_mach; eauto. 
      apply wt_return_regs; auto. eapply match_stacks_wt_locset; eauto. 
      solve[inv AGARGS; auto].
      eapply agree_wt_ls; eauto.
      solve[eapply agree_args_free; eauto]. 
    intuition.
    eapply REACH_closed_free; try eassumption.
    split; intros. 
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption.
      eapply Mem.valid_block_free_1; try eassumption.
        eapply SMV; assumption. }
  unfold EmptyEffect; simpl; intros.
    apply andb_true_iff in H0. destruct H0.
    destruct AGFRAME.
    apply FreeEffectD in H0. destruct H0 as [? [VB Arith2]]; subst.
    split. eapply visPropagateR; eassumption.
    rewrite SPLOCT. intuition. }

{ (* initial function *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]]. 
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f0); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  set (tys := sig_args (Linear.fn_sig f0)).
  assert (exists z, args_len_rec args tys = Some z).
  { eapply args_len_rec_succeeds; eauto. }
  destruct H as [z ARGSLEN]. 
  case_eq (Mem.alloc m2 0 (4*z)). intros m3 sp0 ALLOC.
  assert (STORE: exists m4, store_args m3 sp0 args tys = Some m4).
  { unfold store_args; eapply store_args_rec_succeeds; eauto.
    admit. (*TODO: initial_core should fail if arguments don't fit in address space*) }
  destruct STORE as [m4 STORE].
  eexists; eexists; eexists; split.
    eapply effstep_plus_one. simpl. econstructor; eauto.
  exists (alloc_right_sm mu sp0); intuition.
  apply alloc_right_sm_intern_incr.
  split. rewrite alloc_right_sm_as_inj; intros ? ? ? -> ?; congruence.
  split. rewrite alloc_right_sm_DomSrc; intros ? -> ?; congruence.
  intros ? H. rewrite alloc_right_sm_DomTgt. rewrite H, orb_true_iff.
  intros [Y|Y]; try solve[intros; congruence]. 
  unfold eq_block in Y. cut (b2 = sp0). intros. subst b2. clear Y.
  eapply Mem.fresh_block_alloc; eauto.
  solve[destruct (peq b2 sp0); try simpl in Y; congruence].
  (*TODO: sm_locally_allocated_alloc_right_sm*)
  { rewrite sm_locally_allocatedChar.
  assert (locBlocksSrc (alloc_right_sm mu sp0) = locBlocksSrc mu) as -> by auto.
  assert (locBlocksTgt (alloc_right_sm mu sp0) 
        = (fun b => eq_block b sp0 || locBlocksTgt mu b)) as -> by auto.
  assert (extBlocksSrc (alloc_right_sm mu sp0) = extBlocksSrc mu) as -> by auto.
  assert (extBlocksTgt (alloc_right_sm mu sp0) = extBlocksTgt mu) as -> by auto.
  assert (DomSrc (alloc_right_sm mu sp0) = DomSrc mu) as -> by auto.
  cut (freshloc m2 m4 = fun b => eq_block b sp0). intros ->.
  split; auto. extensionality b. 
    solve[rewrite freshloc_irrefl, orb_comm; simpl; auto].
  split; auto. extensionality b. simpl. unfold DomTgt. destruct mu; simpl.
    solve[rewrite <-orb_assoc, orb_comm; auto].
  split; auto. extensionality b. 
    solve[rewrite freshloc_irrefl, orb_comm; simpl; auto].
  split; auto. extensionality b. solve[rewrite orb_comm; auto].
  assert (F: freshloc m3 m4 = fun b => false). 
  {  apply store_args_rec_only_stores in STORE. clear - STORE. 
     induction STORE. extensionality b. rewrite freshloc_irrefl; auto.
     apply extensionality. intros b'. 
     generalize e as e'; intro. apply store_freshloc in e. 
     rewrite <-freshloc_trans with (m'':=m''), e, IHSTORE; simpl; auto.
     apply store_forward in e'; auto. apply only_stores_fwd in STORE; auto. }
  assert (freshloc m2 m4 = freshloc m2 m3) as ->.
  { extensionality b; rewrite <-freshloc_trans with (m'' := m3), F, orb_comm; auto.
    apply alloc_forward in ALLOC; auto.    
    apply store_args_fwd in STORE; auto. }
  apply freshloc_alloc in ALLOC; rewrite ALLOC; auto. }
  split.
  apply match_states_call_intern with (tf := tfn); auto.
  admit. (*TODO: match_globalenvs*)
  simpl. unfold bind. solve[rewrite TRANSL; auto].
  intros r. simpl. solve[rewrite Regmap.gi, NOREGS; auto].
  simpl. unfold agree_callee_save. 
    destruct l. intros _. simpl. rewrite NOREGS; auto.
    intros _. simpl. solve[destruct sl; auto]. 
  constructor; auto. 
  destruct ARGS0 as [args0 [_ Y]]. clear - Y. subst rs0. 
  solve[apply wt_init_locset].
  simpl; auto. destruct ARGS0 as [args0 [ARGS0 _]].
  solve[eexists; eapply val_list_inject_forall_inject; eauto].
  eapply store_args_contains; eauto. omega. 
  assert (OVER: 4*(2*Zlength args) <= Int.max_unsigned). admit. (*TODO: no overflow check*)
  solve[apply OVER].
  solve[apply val_has_type_list_func_charact; apply HASTY].
  rewrite alloc_right_sm_as_inj. intros b0 z0 ASINJ. destruct SMV as [H H0]. 
    specialize (H0 sp0). exploit H0. unfold RNG.
    apply as_inj_DomRng in ASINJ. destruct ASINJ; auto. auto. 
    intros VAL. apply Mem.fresh_block_alloc in ALLOC. solve[apply ALLOC; auto].
  rewrite alloc_right_sm_locBlocksTgt, orb_true_iff; left.
  solve[destruct (eq_block sp0 sp0); auto].
  intuition.
  rewrite alloc_right_sm_as_inj. generalize ALLOC as ALLOC'; intro.
  eapply Mem.alloc_right_inject in ALLOC; eauto.
  { apply store_args_rec_only_stores in STORE. 
    assert (H: forall b0 ofs, as_inj mu b0 = Some (sp0,ofs) -> False). 
    { intros b0 ofs INJ'. destruct SMV as [H H0]. 
      apply Mem.fresh_block_alloc in ALLOC'. apply ALLOC'. apply H0.
      unfold RNG. exploit as_inj_DomRng; eauto. intros [? ?]; auto. }
    clear - STORE ALLOC H. revert m ALLOC; induction STORE; auto.
    intros m0 INJ. eapply IHSTORE. eapply Mem.store_outside_inject; eauto. }
  cut (sm_valid (alloc_right_sm mu sp0) m m3). intro H.
  { clear - H STORE. destruct H. apply store_args_rec_only_stores in STORE. 
    split; auto. intros b2 H2. specialize (H0 _ H2). clear - H0 STORE.
    induction STORE; auto. apply IHSTORE. eapply Mem.store_valid_block_1; eauto. }
  clear - SMV ALLOC. split. intros b1 H. 
  unfold DOM in H. rewrite alloc_right_sm_DomSrc in H. 
  destruct SMV as [A B]. solve[apply A; auto].
  intros b2 H. unfold RNG in H. rewrite alloc_right_sm_DomTgt in H. 
  destruct (eq_block b2 sp0). subst sp0.
  eapply Mem.valid_new_block; eauto.
  eapply Mem.valid_block_alloc in ALLOC; eauto. 
  destruct SMV as [A B]. apply B. simpl in H. unfold RNG. rewrite H; auto.
  apply alloc_right_sm_wd; auto.
  destruct SMV. case_eq (DomTgt mu sp0); auto. intros Q.
  unfold RNG in H0. specialize (H0 _ Q). 
  apply Mem.fresh_block_alloc in ALLOC. exfalso. solve[apply ALLOC; auto]. }

{ (* internal function *)
  destruct PRE as [RC [PG [Glob [SMV WD]]]]. 
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  caseEq (transf_function f); simpl; try congruence.
  intros tfn TRANSL EQ. inversion EQ; clear EQ; subst tf.
  exploit function_prologue_correct_eff; eauto.
    eapply match_stacks_type_sp; eauto. 
    eapply match_stacks_type_retaddr; eauto.
  intros [mu' [rs' [m2' [sp' [m3' [m4' [m5' [A [B [C [D [E [F [G 
            [J [K [L [LOCALLOC' [WD' [SMV' [spLocalTgt' RC']]]]]]]]]]]]]]]]]]]]].
  eexists; eexists; eexists; split.
    eapply effstep_plus_star_trans'.
      eapply effstep_plus_one. econstructor; eauto. 
      rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body. 
      eexact D.
    reflexivity.
  generalize (Mem.alloc_result _ _ _ _ _ H). intro SP_EQ. 
  generalize (Mem.alloc_result _ _ _ _ _ A). intro SP'_EQ.
  exists mu'.
  split. assumption.
  split. assumption.
  split. assumption.
  split. 
  { (*MATCH*)
    split.
    assert (SPNEQ: sp0 <> sp'). 
    { subst. cut (Mem.valid_block m2 sp0). intros VAL CONTRA. subst.
      unfold Mem.valid_block in VAL. 
      apply SimplLocals.VSet.MSet.Raw.L.MO.lt_irrefl in VAL; auto.
      generalize (agree_sp_local _ _ _ _ _ _ _ _ AGARGS); intros LOC. 
      destruct SMV as [H0 H1]. apply H1. 
      unfold RNG, DomTgt. rewrite orb_true_iff. solve[left; auto]. }
    econstructor; eauto. 
      apply match_stacks_change_mach_mem with m2.
      apply match_stacks_change_linear_mem with m.
      rewrite SP_EQ; rewrite SP'_EQ.
      eapply match_stacks_change_meminj_intern; eauto. apply Ple_refl. 
      eauto with mem. intros. exploit Mem.perm_alloc_inv. eexact H. eauto. 
      rewrite dec_eq_false; auto. 
      intros. eapply stores_in_frame_valid; eauto with mem. 
      intros. eapply stores_in_frame_perm; eauto with mem.
      intros. rewrite <- H1. transitivity (Mem.load chunk m2' b ofs). 
        eapply stores_in_frame_contents; eauto.
      eapply Mem.load_alloc_unchanged; eauto. red. congruence.
      eapply transf_function_well_typed; eauto.
      auto with coqlib.
      revert AGARGS. destruct s. intros ARGS.
        eapply agree_args_stores_in_frame; eauto.
        eapply agree_args_alloc; eauto.
        eapply agree_args_intern_incr; eauto.
      intros AGARGS.
        eapply agree_args_stores_in_frame; eauto.
        eapply agree_args_alloc; eauto.
        solve[eapply agree_args_intern_incr; eauto].
        revert AGINITF. destruct s; auto. intros [Y|Y].
        solve[inv Y; auto]. solve[auto].
    intuition.
    eapply (intern_incr_meminj_preserves_globals_as_inj _ mu); trivial.
      split; assumption.
    eapply (intern_incr_meminj_preserves_globals_as_inj ge mu); trivial.
      split; assumption. }
  intuition.
  apply orb_true_iff in H0. destruct H0. intuition.
    apply andb_true_iff in H0. destruct H0.
    apply PrologueEffect_sp in H0. subst; clear - H1. 
      destruct (valid_block_dec m2 (Mem.nextblock m2)).
        exfalso. unfold Mem.valid_block in v. clear -v. xomega.
      inv H1.
  apply orb_true_iff in H0. destruct H0. intuition.
    apply andb_true_iff in H0. destruct H0.
    apply PrologueEffect_sp in H0. subst; clear - H2. 
      destruct (valid_block_dec m2 (Mem.nextblock m2)).
        exfalso. unfold Mem.valid_block in v. clear -v. xomega.
      inv H2. }  

{ (* external function *)
     apply bind_inversion in TRANSL. 
    destruct TRANSL as [ff [FT X]]. discriminate. }

{ monadInv TRANSL. }

{ (*nonobservable extern function*)
  destruct PRE as [RC [PG [Glob [SMV WD]]]].
  simpl in TRANSL. inversion TRANSL; subst tf.
  inv H0. 
  exploit transl_external_arguments; try eassumption.
  intros [vl [ARGS VINJ]].
  assert (VL: vl = args1).
    eapply transl_external_arguments_fun; try eassumption. trivial.
  subst vl.
  exploit (inlineable_extern_inject _ _ GDE_lemma); try eapply H.
     eassumption. 
     Focus 8. eapply decode_longs_inject. eapply VINJ. 
     assumption. eassumption. assumption. assumption.
     eapply EFhelpers; eassumption. assumption. assumption. 
  intros [mu' [vres' [tm' [EC [RINJ' [MINJ' [UNMAPPED [OUTOFREACH 
           [INCR [SEPARATED [LOCALLOC [WD' [VAL' RC']]]]]]]]]]]]].
  eexists; exists tm'; eexists.
  split. simpl.
           apply effstep_plus_one. 
              eapply Mach_effexec_function_external; try assumption.
              econstructor. eapply EC.
              reflexivity. reflexivity. 
          (*eapply external_call_symbols_preserved'; eauto.
            exact symbols_preserved. exact varinfo_preserved.*)
  exists mu'.  
  assert (STACKS': match_stacks mu' m' tm' sp0 ls0 s cs' 
           (Linear.funsig (External ef))
           (Mem.nextblock m') (Mem.nextblock tm')).
      apply match_stacks_change_bounds
           with (Mem.nextblock m) (Mem.nextblock m2).
        eapply match_stack_change_extcall_intern; try eapply STACKS.
          eapply external_call_mem_forward; eassumption.
          eapply external_call_mem_forward; eassumption.
          assumption. assumption. assumption. assumption. assumption.
          apply Ple_refl. apply Ple_refl. 
       eapply external_call_nextblock'. econstructor; eauto.
       eapply external_call_nextblock'. econstructor; eauto.
  clear STACKS.
  assert (WTL: wt_locset (Locmap.setlist R ## (loc_result (ef_sig ef))
                  (encode_long (sig_res (ef_sig ef)) v) rs1)).
     apply wt_setlist_result. 
       eapply external_call_well_typed; eauto. auto.
  assert (AGREGS': agree_regs (restrict (as_inj mu') (vis mu'))
             (Locmap.setlist R ## (loc_result (ef_sig ef))
                 (encode_long (sig_res (ef_sig ef)) v) rs1)
             (set_regs (loc_result (ef_sig ef))
                (encode_long (sig_res (ef_sig ef)) vres') rs)).
    apply agree_regs_set_regs; auto. 
    eapply agree_regs_inject_incr; try eassumption.
    eapply intern_incr_restrict; eassumption. 
    eapply encode_long_inject; eassumption.
  assert (AGCalleeSave: agree_callee_save
             (Locmap.setlist R ## (loc_result (ef_sig ef))
               (encode_long (sig_res (ef_sig ef)) v) rs1)
             (parent_locset0 ls0 s)).
    apply agree_callee_save_set_result. assumption. 
  split; trivial.
  split; trivial.
  split; trivial.
  split. clear AGREGS.
    split.
      econstructor; eauto.
      eapply agree_args_intern_incr; try eassumption.
      eapply agree_args_invariant; try eapply AGARGS. assumption.
      eapply mem_unchanged_on_sub; try eassumption.
       unfold loc_out_of_reach; intros; subst b.
         destruct (restrictD_Some _ _ _ _ _ H1); clear H1.
         intros N.
         eapply agree_sp_fresh; eassumption.
    split. assumption.
    split. auto.
    split. 
      eapply (intern_incr_meminj_preserves_globals_as_inj _ mu); trivial.
        split; assumption.
    split.
      eapply (intern_incr_meminj_preserves_globals_as_inj ge mu); trivial.
        split; assumption.
    split; assumption. 
  intros. 
  rewrite BuiltinEffect_decode.
  eapply BuiltinEffect_Propagate; try eapply H. 
     eapply decode_longs_inject. apply VINJ. 
     eassumption. eassumption. 
     instantiate (1:=tge).
     unfold BuiltinEffect. unfold BuiltinEffect in H0.
     destruct ef; simpl in *; trivial; contradiction. }

{ (* return *)
  inv STACKS. simpl in AGLOCS.  
  eexists; eexists; eexists; split.
    apply effstep_plus_one. apply Mach_effexec_return. 
  exists mu.
  split. apply intern_incr_refl. 
  split. apply sm_inject_separated_same_sminj.
  split. apply sm_locally_allocatedChar.
      intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
      apply extensionality; intros; rewrite freshloc_irrefl. intuition.
  split. 2: intuition.
  split.  
    econstructor; eauto. 
    eapply agree_frame_return; eauto.
    inv AGARGS. constructor; auto. simpl in *. destruct s; auto. simpl; auto.
    intros C. subst sp'. inv AGARGS. eapply agree_sp_fresh0.
    inv FRM. apply restrictD_Some in agree_inj0. 
    destruct agree_inj0 as [X Y]. solve[apply X].
    inv AGARGS. revert agree_args_frame_match0. simpl. destruct s; auto.
    intros [Y|Y]. left; inv Y; auto. right; auto.
  solve[intuition]. }
Qed.

(** The simulation proof *)
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
SM_simulation.SM_simulation_inject (Linear_eff_sem hf)
   (Mach_eff_sem hf return_address_offset) ge tge entrypoints.
Proof.
intros.
assert (GDE:= GDE_lemma). 
 eapply effect_simulations_lemmas.inj_simulation_plus with
  (match_states:=MATCH) (measure:=fun x => O).
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
    assert (VB: Mem.valid_block m1 (Mem.nextblock m1)).
      eapply Mem.valid_block_inject_1; eauto.
    clear - VB; unfold Mem.valid_block in VB.
    xomega.

    destruct (P (Mem.nextblock m0) (Mem.nextblock m2)); auto.
    exfalso. 
    destruct (D _ p).
    apply A in H3.
    assert (VB: Mem.valid_block m2 (Mem.nextblock m2)).
      eapply Mem.valid_block_inject_2; eauto.
    clear - VB; unfold Mem.valid_block in VB.
    xomega.
    
    intros b LT.    
    unfold ge. 
    apply valid_init_is_global with (b0 := b) in INIT.
    eapply INIT; auto.
    apply R.
    apply LT. }
(*halted*)
  { intros. destruct H as [MC [RC [PG [Glob [VAL [WD INJ]]]]]].
    inv MC. 
    simpl in H0; inv H0. 
    simpl in H0; inv H0.
    simpl in H0; inv H0.
    simpl in H0; inv H0.
    specialize (match_states_return _ _ _ _ f0 _ _ retty _ _ _ args0 tys0 _ 
                                    STACKS WTLS AGREGS AGLOCS). intros.
    destruct cs; inv H0.    
    remember (ls (Locations.R AX)) as d.
    inv STACKS.
    destruct retty. (* try solve[inv H2].*)
    { destruct t; inv H2.
      + exists (rs AX); split; auto. 
      + exists (rs FP0); split; auto. 
      + exists (Val.longofwords (rs DX) (rs AX)).
        split; auto. split; auto. 
        apply val_longofwords_inject; auto. 
      + exists (rs FP0); split; auto. }
    { inv H2.
      exists (rs AX); split; auto. } }
(* at_external*) 
  { eapply MATCH_atExternal; eassumption. }
(* after_external*)
  { eapply MATCH_afterExternal; eassumption. }
(*Core_diagram*)
  { intros. exploit MATCH_corediagram; try eassumption.
    intros [st2' [m2' [CSTgt [mu' MU]]]].
    exists st2', m2', mu'. intuition. }
(*Effcore_diagram*)
  { intros. exploit MATCH_eff_diagram; try eassumption.
    intros [st2' [m2' [U2 [CSTgt [mu' MU]]]]].
    exists st2', m2', mu'. intuition.
    exists U2. intuition. }
Qed.

End PRESERVATION.
