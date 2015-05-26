
Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Cminor.
Require Import Op.

Require Import mem_lemmas.
Require Import structured_injections.
Require Import reach.
Require Import Axioms.

  (** * Axiomatization of the helper functions *)

Section HELPERS.

Context {F V: Type} (ge: Genv.t (AST.fundef F) V).

Record helper_functions : Type := mk_helper_functions {
  i64_dtos: ident;                      (**r float -> signed long *)
  i64_dtou: ident;                      (**r float -> unsigned long *)
  i64_stod: ident;                      (**r signed long -> float *)
  i64_utod: ident;                      (**r unsigned long -> float *)
  i64_stof: ident;                      (**r signed long -> float32 *)
  i64_utof: ident;                      (**r unsigned long -> float32 *)
  i64_neg: ident;                       (**r opposite *)
  i64_add: ident;                       (**r addition *)
  i64_sub: ident;                       (**r subtraction *)
  i64_mul: ident;                       (**r multiplication 32x32->64 *)
  i64_sdiv: ident;                      (**r signed division *)
  i64_udiv: ident;                      (**r unsigned division *)
  i64_smod: ident;                      (**r signed remainder *)
  i64_umod: ident;                      (**r unsigned remainder *)
  i64_shl: ident;                       (**r shift left *)
  i64_shr: ident;                       (**r shift right unsigned *)
  i64_sar: ident                        (**r shift right signed *)
}.

Variable hf: helper_functions.

Definition hf_names := hf.(i64_dtos)::hf.(i64_dtou) :: 
  hf.(i64_stod) ::  hf.(i64_utod) :: hf.(i64_stof) ::
  hf.(i64_utof) :: hf.(i64_neg) :: hf.(i64_add) :: 
  hf.(i64_sub) :: hf.(i64_mul) :: hf.(i64_sdiv) ::
  hf.(i64_udiv) :: hf.(i64_smod) :: hf.(i64_umod) ::
  hf.(i64_shl) :: hf.(i64_shr) :: hf.(i64_sar) :: nil.


End HELPERS.


Definition sig_l_l := mksignature (Tlong :: nil) (Some Tlong).
Definition sig_l_f := mksignature (Tlong :: nil) (Some Tfloat).
Definition sig_l_s := mksignature (Tlong :: nil) (Some Tsingle).
Definition sig_f_l := mksignature (Tfloat :: nil) (Some Tlong).
Definition sig_ll_l := mksignature (Tlong :: Tlong :: nil) (Some Tlong).
Definition sig_li_l := mksignature (Tlong :: Tint :: nil) (Some Tlong).
Definition sig_ii_l := mksignature (Tint :: Tint :: nil) (Some Tlong).


(** Setting up the helper functions *)

Require Import Errors.

Local Open Scope string_scope.
Local Open Scope error_monad_scope.

Parameter get_helper: String.string -> signature -> res ident.
Parameter get_builtin: String.string -> signature -> res ident.

Definition get_helpers : res helper_functions :=
  do i64_dtos <- get_helper "__i64_dtos" sig_f_l ;
  do i64_dtou <- get_helper "__i64_dtou" sig_f_l ;
  do i64_stod <- get_helper "__i64_stod" sig_l_f ;
  do i64_utod <- get_helper "__i64_utod" sig_l_f ;
  do i64_stof <- get_helper "__i64_stof" sig_l_s ;
  do i64_utof <- get_helper "__i64_utof" sig_l_s ;
  do i64_neg <- get_builtin "__builtin_negl" sig_l_l ;
  do i64_add <- get_builtin "__builtin_addl" sig_ll_l ;
  do i64_sub <- get_builtin "__builtin_subl" sig_ll_l ;
  do i64_mul <- get_builtin "__builtin_mull" sig_ll_l ;
  do i64_sdiv <- get_helper "__i64_sdiv" sig_ll_l ;
  do i64_udiv <- get_helper "__i64_udiv" sig_ll_l ;
  do i64_smod <- get_helper "__i64_smod" sig_ll_l ;
  do i64_umod <- get_helper "__i64_umod" sig_ll_l ;
  do i64_shl <- get_helper "__i64_shl" sig_li_l ;
  do i64_shr <- get_helper "__i64_shr" sig_li_l ;
  do i64_sar <- get_helper "__i64_sar" sig_li_l ;
  OK (mk_helper_functions
     i64_dtos i64_dtou i64_stod i64_utod i64_stof i64_utof
     i64_neg i64_add i64_sub i64_mul i64_sdiv i64_udiv i64_smod i64_umod
     i64_shl i64_shr i64_sar).

Inductive is_I64_helper hf : ident -> signature -> Prop :=
  ef_dtos: is_I64_helper hf hf.(i64_dtos) sig_f_l
| ef_dtou: is_I64_helper hf hf.(i64_dtou) sig_f_l
| ef_stod: is_I64_helper hf hf.(i64_stod) sig_l_f
| ef_utod: is_I64_helper hf hf.(i64_utod) sig_l_f
| ef_stof: is_I64_helper hf hf.(i64_stof) sig_l_s
| ef_utof: is_I64_helper hf hf.(i64_utof)  sig_l_s
| ef_neg: is_I64_helper hf hf.(i64_neg) sig_l_l
| ef_add: is_I64_helper hf hf.(i64_add) sig_ll_l
| ef_sub: is_I64_helper hf hf.(i64_sub) sig_ll_l
| ef_mul: is_I64_helper hf hf.(i64_mul) sig_ii_l (*Changed this back to sig_ii_l*)
| ef_sdiv: is_I64_helper hf hf.(i64_sdiv) sig_ll_l
| ef_udiv: is_I64_helper hf hf.(i64_udiv) sig_ll_l
| ef_smod: is_I64_helper hf hf.(i64_smod) sig_ll_l
| ef_umod: is_I64_helper hf hf.(i64_umod) sig_ll_l
| ef_shl: is_I64_helper hf hf.(i64_shl) sig_li_l
| ef_shr: is_I64_helper hf hf.(i64_shr) sig_li_l
| ef_sarf: is_I64_helper hf hf.(i64_sar) sig_li_l.

Lemma is_I64_helper_dec hf name sg:
 {is_I64_helper hf name sg} + {~is_I64_helper hf name sg} .
Proof.
destruct (signature_eq sg sig_f_l); subst.
  destruct (ident_eq name hf.(i64_dtos)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_dtou)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.
destruct (signature_eq sg sig_l_f); subst.
  destruct (ident_eq name hf.(i64_stod)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_utod)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition. 
destruct (signature_eq sg sig_l_s); subst.
  destruct (ident_eq name hf.(i64_stof)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_utof)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition. 
destruct (signature_eq sg sig_l_l); subst.
  destruct (ident_eq name hf.(i64_neg)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.  
destruct (signature_eq sg sig_ii_l); subst.
  destruct (ident_eq name hf.(i64_mul)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition.  
destruct (signature_eq sg sig_ll_l); subst.
  destruct (ident_eq name hf.(i64_add)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_sub)); subst; try solve[left; constructor].
  (*destruct (ident_eq name hf.(i64_mul)); subst; try solve[left; constructor].*)
  destruct (ident_eq name hf.(i64_sdiv)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_udiv)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_smod)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_umod)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition. 
destruct (signature_eq sg sig_li_l); subst.
  destruct (ident_eq name hf.(i64_shl)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_shr)); subst; try solve[left; constructor].
  destruct (ident_eq name hf.(i64_sar)); subst; try solve[left; constructor].
  right; intros N. inv N; intuition. 
right; intros N. inv N; intuition. 
Qed.

Lemma helpers_inject: forall {F V TF TV: Type} 
  (ge: Genv.t F V) (tge : Genv.t TF TV)
  (SymbPres : forall s, Genv.find_symbol tge s = Genv.find_symbol ge s)
  hf name sg vargs m t vres m1 mu tm vargs'
  (WD : SM_wd mu)
  (SMV : sm_valid mu m tm)
  (RC : REACH_closed m (vis mu))
  (Glob : forall b, isGlobalBlock ge b = true -> frgnBlocksSrc mu b = true)
  (OBS : is_I64_helper hf name sg)
  (PG : meminj_preserves_globals ge (as_inj mu))
  (EC : extcall_io_sem name sg ge vargs m t vres m1)
  (MINJ : Mem.inject (as_inj mu) m tm)
  (ArgsInj : val_list_inject (restrict (as_inj mu) (vis mu)) vargs vargs'),
   exists (mu' : SM_Injection) (vres' : val) (tm1 : mem),
     external_call (EF_external name sg) tge vargs' tm t vres' tm1 /\
     val_inject (restrict (as_inj mu') (vis mu')) vres vres' /\
     Mem.inject (as_inj mu') m1 tm1 /\
     Mem.unchanged_on (loc_unmapped (restrict (as_inj mu) (vis mu))) m m1 /\
     Mem.unchanged_on (loc_out_of_reach (restrict (as_inj mu) (vis mu)) m) tm
       tm1 /\
     intern_incr mu mu' /\
     sm_inject_separated mu mu' m tm /\
     sm_locally_allocated mu mu' m tm m1 tm1 /\
     SM_wd mu' /\
     sm_valid mu' m1 tm1 /\
     REACH_closed m1 (vis mu').
Proof. intros. 
inv OBS.
{ (*i64dtos*)
    inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ (*i64dtou*)
    inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
{ inv EC. exists mu; eexists; eexists; split.
      econstructor.
        eapply eventval_list_match_preserved.
          apply SymbPres.
          eapply eventval_list_match_inject; try eapply ArgsInj.
            rewrite <- restrict_sm_all.
            eapply restrict_sm_preserves_globals; try eassumption.
            unfold vis. intuition.  
          assumption.
        eapply eventval_match_preserved.
          apply SymbPres. apply H0.
      intuition.
      inv H0; econstructor.
    apply intern_incr_refl.
    apply sm_inject_separated_same_sminj.
    apply sm_locally_allocatedChar.
    repeat split; extensionality b;
      try rewrite freshloc_irrefl; intuition. }
Qed.
