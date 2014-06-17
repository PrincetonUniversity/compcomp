
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
Require Import StructuredInjections.
Require Import reach.

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

Definition is_I64_helper hf (x:ident) (sg:signature) : bool:=
  (ident_eq x hf.(i64_dtos) && signature_eq sg sig_f_l) ||
  (ident_eq x hf.(i64_dtou) && signature_eq sg sig_f_l) ||
  (ident_eq x hf.(i64_stod) && signature_eq sg sig_l_f) ||
  (ident_eq x hf.(i64_utod) && signature_eq sg sig_l_f) ||
  (ident_eq x hf.(i64_stof) && signature_eq sg sig_l_s) ||
  (ident_eq x hf.(i64_utof) && signature_eq sg  sig_l_s) ||
  (ident_eq x hf.(i64_neg) && signature_eq sg sig_l_l) ||
  (ident_eq x hf.(i64_add) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_sub) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_mul) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_sdiv) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_udiv) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_smod) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_umod) && signature_eq sg sig_ll_l) ||
  (ident_eq x hf.(i64_shl) && signature_eq sg sig_li_l) ||
  (ident_eq x hf.(i64_shr) && signature_eq sg sig_li_l) ||
  (ident_eq x hf.(i64_sar) && signature_eq sg sig_li_l).

Inductive is_I64_helperP hf : ident -> signature -> Prop :=
  ef_dtos: is_I64_helperP hf hf.(i64_dtos) sig_f_l
| ef_dtou: is_I64_helperP hf hf.(i64_dtou) sig_f_l
| ef_stod: is_I64_helperP hf hf.(i64_stod) sig_l_f
| ef_utod: is_I64_helperP hf hf.(i64_utod) sig_l_f
| ef_stof: is_I64_helperP hf hf.(i64_stof) sig_l_s
| ef_utof: is_I64_helperP hf hf.(i64_utof)  sig_l_s
| ef_neg: is_I64_helperP hf hf.(i64_neg) sig_l_l
| ef_add: is_I64_helperP hf hf.(i64_add) sig_ll_l
| ef_sub: is_I64_helperP hf hf.(i64_sub) sig_ll_l
| ef_mul: is_I64_helperP hf hf.(i64_mul) sig_ll_l
| ef_sdiv: is_I64_helperP hf hf.(i64_sdiv) sig_ll_l
| ef_udiv: is_I64_helperP hf hf.(i64_udiv) sig_ll_l
| ef_smod: is_I64_helperP hf hf.(i64_smod) sig_ll_l
| ef_umod: is_I64_helperP hf hf.(i64_umod) sig_ll_l
| ef_shl: is_I64_helperP hf hf.(i64_shl) sig_li_l
| ef_shr: is_I64_helperP hf hf.(i64_shr) sig_li_l
| ef_sarf: is_I64_helperP hf hf.(i64_sar) sig_li_l.

Lemma identeq_and x b: ((ident_eq x x) && b) = b.
Proof. destruct (ident_eq x x); intuition. Qed. 
Lemma sigeq_or x b: ((signature_eq x x) || b) = true.
Proof. destruct (signature_eq x x); intuition. Qed. 
Lemma sigeq_or' x b: (b || (signature_eq x x)) = true.
Proof. destruct (signature_eq x x); intuition. Qed. 

Lemma ident_sig_eq_elim b name name' sg sg': 
  ((b || (ident_eq name name' && signature_eq sg sg')) = true)
<->
  (b=true \/ (name=name' /\ sg=sg')).
Proof.
destruct b; simpl. intuition. 
destruct (ident_eq name name'); simpl.
destruct (signature_eq sg sg'); simpl. intuition. intuition. intuition. 
Qed.

Lemma is64helper_char hf (name:ident) (sg:signature) :
   is_I64_helperP hf name sg <-> (is_I64_helper hf name sg = true).
Proof.
split; intros.
unfold is_I64_helper.
inv H; rewrite identeq_and; try rewrite sigeq_or'; trivial. 
unfold is_I64_helper in H. 
  repeat rewrite ident_sig_eq_elim in H.
  intuition; try solve [subst; constructor]. 
    destruct (ident_eq name (i64_dtos hf)); try inv H.
    destruct (signature_eq sg sig_f_l); try inv H1. constructor.
Qed.