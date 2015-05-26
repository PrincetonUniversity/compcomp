Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import Axioms.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert_imports. Import CompcertCommon.
Require Import Clight.
Require Import Clight_coop.
Require Import Clight_eff.

Require Import sepcomp. Import SepComp.
Require Import mem_welldefined.
Require Import arguments.

Require Import pred_lemmas.
Require Import nucular_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Nucular Clight *)

Module CLIGHT_NUKE. Section ClightNuke.

Variable hf : I64Helpers.helper_functions.

Notation clsem := (CL_eff_sem1 hf).

Definition cl_state_inv (m : mem) e te := 
  [/\ forall x b (ty : Ctypes.type), 
        PTree.get x e = Some (b,ty) -> Mem.valid_block m b
    , forall x v, PTree.get x te = Some v -> val_valid v m
    & mem_wd m
  ].

Fixpoint cl_cont_inv (k : cont) (m : mem) := 
  match k with
    | Kstop => True
    | Kseq s k' => cl_cont_inv k' m
    | Kloop1 s1 s2 k' => cl_cont_inv k' m
    | Kloop2 s1 s2 k' => cl_cont_inv k' m
    | Kswitch k' => cl_cont_inv k' m
    | Kcall oid f e te k' => [/\ cl_state_inv m e te & cl_cont_inv k' m]
  end.

Definition cl_core_inv (c : CL_core) (m : mem) := 
  match c with
    | CL_State f s k e te => 
        [/\ cl_state_inv m e te 
          & cl_cont_inv k m]
    | CL_Callstate f args k => 
        [/\ Forall (val_valid^~ m) args 
          , mem_wd m
          & cl_cont_inv k m]
    | CL_Returnstate v k => 
        [/\ val_valid v m
          , mem_wd m
          & cl_cont_inv k m]
  end.

Lemma getBlocksP l b : reflect (exists ofs, List.In (Vptr b ofs) l) (b \in getBlocks l).
Proof.
case e: (b \in getBlocks l).
+ by apply: ReflectT; move: e; rewrite /in_mem /= /is_true /= getBlocks_char.
+ apply: ReflectF=> [][]ofs C.
rewrite /in_mem /= /is_true /= in e; move: C e; elim: l=> //= a l IH; case.
by move=> ->; rewrite /getBlocks /= /eq_block; case: (Coqlib.peq b b).
move=> Hin Hget; apply: IH=> //.
by move: Hget; rewrite getBlocksD; case: a=> // ? ?; rewrite orb_false_iff; case.
Qed.

Lemma sem_cast_getBlocks v v' ty ty' : 
  Cop.sem_cast v ty ty' = Some v' -> 
  {subset getBlocks [:: v'] <= getBlocks [:: v]}.
Proof.
rewrite /Cop.sem_cast.
case: (Cop.classify_cast ty ty')=> //; try solve 
 [ case: v=> // ?; [by case; move=> ->|by move=> ?; case; move=> ->]
 | by move=> ? ?; case: v=> //; move=> ?; case=> <-
 | by move=> ?; case: v=> //; move=> ?; case=> <-
 | by move=> ? ?; case: v=> // ?; case: (Cop.cast_float_int _ _)=> // ?; case=> <-
 | by move=> ? ?; case: v=> // ?; case: (Cop.cast_float_int _ _)=> // ?; case=> <-
 | by case: v=> // ?; case=> <-
 | by move=> ?; case: v=> // ?; case: (Cop.cast_float_long _ _)=> // ?; case=> <- 
 | by case: v=> // ?; [by case=> // <-|by move=> ?; case=> // <-]
 | by move=> ? ? ? ?; case: v=> // ? ?; case: (_ && _)=> //; case=> <-
 | by case=> <-].
Qed.

Lemma sem_cast_val_valid m v v' ty ty' : 
  Cop.sem_cast v ty ty' = Some v' -> 
  val_valid v m -> val_valid v' m.
Proof.
move/sem_cast_getBlocks; case: v'=> //= b i Hsub Hval.
move: (Hsub b); move {Hsub}; rewrite /getBlocks /in_mem /=.
have eq: is_true true by []; case: (eq_block _ _)=> //= pf; move/(_ eq).
by case: v Hval=> //= b0 _ Hval; case: (eq_block _ _)=> //= H; subst.
Qed.

Lemma eval_expr_valid' ge m e te a v (VGENV: valid_genv ge m) : 
  cl_state_inv m e te ->    
  eval_expr ge e te m a v -> 
  val_valid v m.
Proof.
set (P := fun (a0 : expr) v0 => val_valid v0 m).
set (P0 := fun (a0 : expr) b0 i0 => val_valid (Vptr b0 i0) m).
case=> H H2 H3.
case: (eval_expr_lvalue_ind ge e te m P P0)=> //.

{ by move=> id ty v0; apply/H2. }

{ move=> op a0 ty v1 v0 H4 H5 H6; elim: op H6=> /=.
  + rewrite /Cop.sem_notbool.
    case: (Cop.classify_bool (typeof a0))=> //.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _ _).
    case: v1 H4 H5=> // i H8 H9. 
    case=> Heq; subst v0.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    by move=> _; case=> Heq; subst v0.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.                                            
    by rewrite /Val.of_bool; case: (Integers.Int64.eq _ _).  
  + rewrite /Cop.sem_notint.
    case: (Cop.classify_notint (typeof a0))=> // _.
    by case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    by case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
  + rewrite /Cop.sem_neg.
    case Hcl: (Cop.classify_neg (typeof a0))=> // [sgn||].
    case Hv1: v1 H4 H5=> // [v0']; subst.
    by move=> H8 H9; case=> Heq; subst v0.
    by case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0. }

{ move=> op a1 a2 ty v1 v2 v0 H4 H5 H6 H7 H8; elim: op H6 H8=> /=.
  { rewrite /Cop.sem_add. 
    case: (Cop.classify_add _ _)=> //.
    move=> ? ? Heval; case: v1 H4 H5=> // b0 i H4 H5; case: v2 H7 Heval=> // i0 ? ?.
    by case=> Heq; subst v0. 
    move=> ? ? Heval; case: v1 H4 H5=> // i H4 H5; case: v2 H7 Heval=> // ? ? H7 Heval.
    by case=> Heq; subst v0. 
    move=> ? ? Heval; case: v1 H4 H5=> // ? ? H4 H5; case: v2 H7 Heval=> // ? ? ?; case=> ?; subst.
    by apply: H5. 
    move=> ? ? Heval; case: v1 H4 H5=> // i H4 H5; case: v2 H7 Heval=> // ? ? H7 Heval.
    by case=> Heq; subst v0; apply: H7. 
    move=> Heval; rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    by move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by case: a'=> // i; case: a''=> // ?; case=> ?; subst. }
  { move=> Heval; rewrite /Cop.sem_sub.
    case: (Cop.classify_sub _ _)=> //.
    move=> ty'.                                     
    case: v1 H4 H5=> // ? ? Heval' Hp ?; case: v2 H7 Heval=> // i Hp' Heval''; case=> ?; subst.
    by apply: Hp; apply/getBlocksP; eexists; econstructor; eauto.
    move=> ty'.                                     
    case: v1 H4 H5=> // ? ? Heval' Hp; case: v2 H7 Heval=> // ? ? Hp' Heval''.
    case: (eq_block _ _)=> // ?; subst.
    by case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> ty'.                                     
    move=> ?; case: v1 H4 H5=> // ? ? Heval' Hp; case: v2 H7 Heval=> // ? Hp' Heval''. 
    case=> ?; subst.
    by apply: Hp; apply/getBlocksP; eexists; econstructor; eauto.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    by move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by case: a'=> // i; case: a''=> // ?; case=> ?; subst. }
  { move=> Heval; rewrite /Cop.sem_mul.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    by move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by move=> ?; case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by case: a'=> // i; case: a''=> // ?; case=> ?; subst. }
  { move=> Heval; rewrite /Cop.sem_div.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    by case: (_ || _)=> //; case=> ?; subst.
    by case: (Integers.Int.eq _ _)=> //; case=> // ?; subst.                            
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    by case: (_ || _)=> //; case=> ?; subst.
    by case: (Integers.Int64.eq _ _)=> //; case=> // ?; subst.  
    by case: a'=> // i; case: a''=> // ?; case=> ?; subst. }
  { move=> Heval; rewrite /Cop.sem_mod.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    by case: (_ || _)=> //; case=> ?; subst.
    by case: (Integers.Int.eq _ _)=> //; case=> // ?; subst.    
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //.
    by case: (_ || _)=> //; case=> ?; subst.
    by case: (Integers.Int64.eq _ _)=> //; case=> // ?; subst.  
    by case: a'=> // i; case: a''=> // ?; case=> ?; subst. }
  { move=> Heval; subst; rewrite /Cop.sem_and.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    by move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> <-.
    by move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> <-.
    by case: a'=> // i; case: a''=> // ?; case: s=> //. }
  { move=> Heval; subst; rewrite /Cop.sem_or.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    by move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst. }
  { move=> Heval; subst; rewrite /Cop.sem_xor.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    by move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst. }
  { move=> Heval; subst; rewrite /Cop.sem_shl.
    rewrite /Cop.sem_shift.
    case: (Cop.classify_shift _ _)=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int.ltu _ _)=> //; case=> ?; subst.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int.ltu _ _)=> //; case=> ?; subst. }
  { move=> Heval; subst; rewrite /Cop.sem_shr.
    rewrite /Cop.sem_shift.
    case: (Cop.classify_shift _ _)=> //.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int.ltu _ _)=> //; case=> ?; subst.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int64.ltu _ _)=> //; case=> ?; subst.
    move=> s; case: v1 H4 H5=> // i Heval' Hp.
    case: v2 H7 Heval=> // i' Heval'' Hp'.
    by case: (Integers.Int.ltu _ _)=> //; case=> ?; subst. }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    by move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    by case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> ?; subst. 
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    by case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.                        
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    by move=> ? /=; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    case: v1 H4 H5=> // ? ? ?. 
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    by case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _). }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    by move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    by case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    by case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.                        
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    by move=> ? /=; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    case: v1 H4 H5=> // ? ? ?. 
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    by case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.eq _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _). }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    by move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    by case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> H9; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.                        
    case: (Integers.Int.ltu _ _)=> //.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?. 
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    case: (Integers.Int.lt _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _). }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    by move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> H9; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.                        
    case: (Integers.Int.ltu _ _)=> //.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?. 
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    case: (Integers.Int.lt _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _). }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> H9; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.                        
    case: (Integers.Int.ltu _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?. 
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    case: (Integers.Int.lt _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _). }
  { move=> Heval; rewrite/Cop.sem_cmp.
    case: (Cop.classify_cmp _ _)=> //.
    rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? Heval' Hp.
    case: v2 H7 Heval=> // ? Hp' Heval''.
    case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    move=> Heval'''; case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Hp'; case: v2 H7 Heval=> // ? ? ? /=.
    case: (Integers.Int.eq _ _)=> //; case=> ?; subst.
    move=> Heval'''; case: (eq_block _ _)=> // ?; subst.
    case: (_ && _)=> //; case=> H9; subst.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.ltu _ _)=> //.
    case: (_ && _)=> //; case=> ?; subst.
    case: v2 H7 Heval=> // ? ? ?; rewrite /Val.cmpu_bool.
    case: v1 H4 H5=> // ? ? ?.
    case=> ?; subst.                        
    case: (Integers.Int.ltu _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.eq _ _)=> // ?; subst.
    case: v1 H4 H5=> // ? ? ?. 
    rewrite /Val.cmpu_bool.
    case: v2 H7 Heval=> // ? ? ?.
    case=> ?; subst.
    case: (Integers.Int.ltu _ _)=> //.
    case: (Integers.Int.eq _ _)=> // ?; case=> ?; subst.
    rewrite /Cop.sem_binarith.
    case: (Cop.sem_cast _ _ _)=> // a'.
    case: (Cop.sem_cast _ _ _)=> // a''.
    case: (Cop.classify_binarith _ _)=> //.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    case: (Integers.Int.lt _ _)=> //.
    rewrite /Val.of_bool; case: (Integers.Int.ltu _ _)=> // ?; subst.
    move=> s; case: a'=> // i; case: a''=> // ?; case: s=> //; case=> ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.lt _ _)=> // ?; subst.
    rewrite /Val.of_bool; case: (Integers.Int64.ltu _ _)=> // ?; subst.
    case: a'=> // i; case: a''=> // ?; case=> ?; subst.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _). }
}

{ by move=> a0 ty v1 v0 H4 H5; move/sem_cast_val_valid; move/(_ m); apply. }

{ move=> a0 loc ofs v0 H4 H5 H6.
  case: {v0} H6=> //.
  move=> ch v1 H8 H9.
  rewrite /Mem.loadv in H9.
  by apply: (mem_wd_load _ _ _ _ _ H9 H3). }

{ move=> id l ty H4 H5; move: (find_symbol_isGlobal _ _ _ H5)=> isGlob _. 
  by case: VGENV=> A B; apply: (A _ isGlob). }

{ by move=> H4 H5 H6; apply: (H4 _ _ H6). }
Qed.

Lemma eval_lvalue_valid ge m e te a b ofs (VGENV: valid_genv ge m) :
  cl_state_inv m e te -> 
  eval_lvalue ge e te m a b ofs -> 
  Mem.valid_block m b.
Proof.
move=> H; case.
+ by case: H=> H ? ? ? ? ?; apply: H.
+ move=> id l ty H5 H6 H7; move: (find_symbol_isGlobal _ _ _ H6)=> isGlob. 
  by case: VGENV=> A B; apply: (A _ isGlob). 
+ by move=> a0 ty l ofs0; move/(eval_expr_valid' VGENV H). 
+ by move=> a0 i ty l ofs0 id fList att delta; move/(eval_expr_valid' VGENV H). 
+ by move=> a0 i ty l ofs0 id fList att; move/(eval_expr_valid' VGENV H).
Qed.

Lemma eval_exprlist_valid' ge m e te aa tys vv (VGENV: valid_genv ge m) : 
  cl_state_inv m e te ->    
  eval_exprlist ge e te m aa tys vv -> 
  Forall (val_valid^~ m) vv.
Proof.
move=> H; elim=> // a bl ty tyl v1 v2 vl H2 H3 H4 H5; constructor=> //.
by apply: (sem_cast_val_valid H3); apply: (eval_expr_valid' VGENV H H2).
Qed.

Lemma cont_inv_call_cont k m : 
  cl_cont_inv k m -> 
  cl_cont_inv (call_cont k) m.
Proof. by elim: k. Qed.

Scheme statement_ind := Induction for statement Sort Prop
  with labeled_statements_ind := Induction for labeled_statements Sort Prop.

Lemma cont_inv_find_label' lbl s k s' k' m :
  cl_cont_inv k m -> 
  find_label lbl s k = Some (s', k') -> 
  cl_cont_inv k' m.
Proof.
set (P := fun s : statement => 
  forall k m,
  cl_cont_inv k m -> 
  find_label lbl s k = Some (s', k') -> 
  cl_cont_inv k' m).
set (P0 := fix F (ls : labeled_statements) :=
  match ls with
    | LSdefault s => P s
    | LScase i s ls => P s /\ F ls
  end).
apply: (@statement_ind P P0)=> //.
+ move=> s0 Hp0 s1 Hp1 k0 m0 Inv /=.
  case Hf: (find_label lbl s0 (Kseq s1 k0))=> [[x y]|].
  by case=> ? ?; subst; apply: (Hp0 _ _ _ Hf).
  by apply/Hp1.
+ move=> e s0 Hp0 s1 Hp1 k'' s'' Inv /=.
  case Hf: (find_label lbl s0 k'')=> [[x y]|].
  by case=> ? ?; subst; apply: (Hp0 _ _ _ Hf).
  by apply/Hp1.
+ move=> s0 Hp0 s1 Hp1 k'' s'' Inv /=.
  case Hf: (find_label lbl s0 (Kloop1 s0 s1 k''))=> [[x y]|].
  by case=> ? ?; subst; apply: (Hp0 _ _ _ Hf).
  by apply/Hp1.
+ move=> e l Hp k'' m'' Inv; elim: l Hp k'' m'' Inv=> /=.
  by move=> s0 Hp0 k'' m'' Inv /=; apply/(Hp0 _ m'').
  move=> i s0 l IH []H H2 k'' m'' Inv.
  case Hf: (find_label _ _ _)=> // [[? ?]|].
  by case=> ? ?; subst; apply: (H _ _ _ Hf).
  by apply: IH.
+ move=> l s0 H k'' m'' Inv /=.  
  case Hid: (ident_eq lbl l)=> // [v|].
  by case=> ? ?; subst s0 k''.
  by move=> Hf; apply: (H _ _ Inv).
Qed.

Lemma cont_inv_find_label lbl s k s' k' m :
  cl_cont_inv k m -> 
  find_label lbl s (call_cont k) = Some (s', k') -> 
  cl_cont_inv k' m.
Proof.
by move=> H H2; apply: (cont_inv_find_label' (cont_inv_call_cont H) H2).
Qed.

Lemma mem_forward_valid m m' b : 
  mem_forward m m' -> 
  Mem.valid_block m b -> 
  Mem.valid_block m' b.
Proof. by move=> A B; case: (A b B). Qed.

Lemma mem_forward_val_valid m m' v : 
  mem_forward m m' -> 
  val_valid v m -> 
  val_valid v m'.
Proof. by case: v=> // b i /=; apply: mem_forward_valid. Qed.

Lemma cl_state_inv_fwd m m' e te :
  cl_state_inv m e te -> 
  (mem_wd m -> mem_wd m') -> 
  mem_forward m m' -> 
  cl_state_inv m' e te.
Proof.
case=> A B X C D; split.
by move=> ???; move/(A _); move/mem_forward_valid; move/(_ _ D).
by move=> ? v; move/(B _); case: v=> // ??; move/mem_forward_valid; move/(_ _ D).
by apply: (C X).
Qed.

Lemma cl_cont_inv_fwd k m m' : 
  cl_cont_inv k m -> 
  (mem_wd m -> mem_wd m') -> 
  mem_forward m m' -> 
  cl_cont_inv k m'.
Proof.
elim: k=> // o f e te c IH /= [] A B C; split.
by apply: cl_state_inv_fwd.
by apply: IH.
Qed.

Lemma create_undef_temps_undef l x v : 
  (create_undef_temps l) ! x = Some v -> v = Vundef.
Proof.
elim: l=> //=; first by rewrite PTree.gempty.
case=> a ? l IH; case: (ident_eq a x).
{ by move=> ?; subst a; rewrite PTree.gss; case. }
{ by move=> Hneq; rewrite PTree.gso=> // ?; subst. }
Qed.

(*TODO: move elsewhere*)
Lemma alloc_variables_valid0 vars E m e m1 b :
  alloc_variables E m vars e m1 -> 
  Mem.valid_block m b -> 
  Mem.valid_block m1 b.
Proof.
elim: vars E m m1.
by move=> E m m1; inversion 1; subst.
case=> b' t' l IH E m m1; inversion 1; subst=> H2.
apply: (IH (PTree.set b' (b1,t') E) m2)=> //.
by apply: (Mem.valid_block_alloc _ _ _ _ _ H7).
Qed.

Lemma bind_parameters_valid0 vars E m vs m1 b :
  bind_parameters E m vars vs m1 -> 
  Mem.valid_block m b -> 
  Mem.valid_block m1 b.
Proof.
elim: vars vs E m m1.
by move=> vs E m m1; inversion 1; subst.
case=> b' t' l IH E m m1; inversion 1; subst=> H2.
move: H; inversion 1; subst.
apply: (IH vl m m3)=> //.
by move: (assign_loc_forward _ _ _ _ _ _ H7); case/(_ _ H2).
Qed.

Lemma alloc_variables_freshblocks: forall vars E m e m1
      (AL: alloc_variables E m vars e m1)
      id b t (Hid: e!id = Some (b,t)),
      E!id = Some (b,t) \/ (~Mem.valid_block m b /\ Mem.valid_block m1 b).
Proof. intros vars.
  induction vars; simpl; intros; inversion AL; subst; simpl in *.
    left; trivial.
  destruct (IHvars _ _ _ _ H6 _ _ _ Hid); clear IHvars.
    rewrite PTree.gsspec in H. 
    destruct (Coqlib.peq id id0); subst. 
      inversion H; subst. right. 
      split.
      eapply Mem.fresh_block_alloc; eassumption.
      apply Mem.valid_new_block in H3.
      eapply alloc_variables_valid0; eauto.
      left; trivial.
    right.
      destruct H.
      split; auto.
      intros N; elim H; clear H.
      eapply Mem.valid_block_alloc; eassumption.
Qed. 

Lemma mem_wd_nonobservables: forall {F V: Type} (ge:Genv.t F V) 
      hf m m' ef t args v (OBS: ~BuiltinEffects.observableEF hf ef)
      (EC: external_call ef ge args m t v m') (WD: mem_wd m),
      mem_wd m'.
Proof. intros.
       destruct ef; simpl in OBS; try solve [elim OBS; trivial];
        inv EC; trivial.
       eapply mem_wd_store; try eapply H0. 
                eapply mem_wd_alloc; eassumption.
                simpl; trivial.
       eapply mem_wd_free; eassumption.
       eapply mem_wd_storebytes; try eassumption.
                eapply loadbytes_valid; eassumption. 
Qed.
(*end move*)

Lemma assign_loc_mem_wd ty m b v1 m2 ofs :
  mem_wd m ->
  val_valid v1 m -> 
  assign_loc ty m b ofs v1 m2 ->
  mem_wd m2.
Proof.
move=> WD A B; inv B; first by apply: (mem_wd_store _ _ _ _ _ _ WD H0 A).
apply: (mem_wd_storebytes _ _ _ _ _ WD H4)=> v IN.
by apply: (loadbytes_valid _ WD _ _ _ _ H3 _ IN).
Qed.

Lemma function_entry1_state_inv f vargs m e te m' (WD: mem_wd m) : 
  Forall (val_valid^~ m) vargs -> 
  function_entry1 f vargs m e te m' -> 
  cl_state_inv m' e te.
Proof.
move=> Hall; case=> m1 Hno Halloc Hbind ->; split.
{ move=> x b ty He.
  case: (alloc_variables_freshblocks Halloc He).
  by rewrite PTree.gempty.
  by case=> _; move/bind_parameters_valid0; move/(_ _ _ _ _ Hbind). }
{ by move=> x v Hundef; move: (create_undef_temps_undef Hundef)=> ->. }
have WD1: mem_wd m1.
{ clear -Halloc WD; elim: Halloc WD=> // e0 m0 id ty vars m2 b1 m3 e2.
  by move=> A B IH C; apply: IH; apply: (mem_wd_alloc _ _ _ _ _ A). }
have Hall1: Forall (val_valid^~ m1) vargs.
{ move: (alloc_variables_forward _ _ _ _ _ Halloc)=> FWD; clear -FWD Hall.
  elim: vargs Hall FWD=> // ?? IH FWD; inv FWD=> FWD; constructor.
  by apply: (mem_forward_val_valid FWD H1).
  by apply: (IH H2 FWD). }
elim: Hbind WD1 Hall1=> // m0 id ty params v1 vl b m2 m3 A B C IH D E.
inv E; apply: IH; first by apply: (assign_loc_mem_wd D H1 B).
move: (assign_loc_forward _ _ _ _ _ _ B)=> FWD.
clear -H2 FWD; elim: vl H2=> // a l IH FWD'; inv FWD'.
constructor; first by apply: (mem_forward_val_valid FWD H1).
by apply: IH.
Qed.

Lemma function_entry1_mem_wd f vargs m e te m' : 
  mem_wd m -> 
  Forall (val_valid^~ m) vargs -> 
  function_entry1 f vargs m e te m' -> 
  mem_wd m'.
Proof. by move=> WD A B; case: (function_entry1_state_inv WD A B). Qed.

Lemma assign_loc_valid ge e le m a1 a2 v2 v loc ofs m' f k :
  valid_genv ge m -> 
  eval_expr ge e le m a2 v2 ->
  Cop.sem_cast v2 (typeof a2) (typeof a1) = Some v ->
  assign_loc (typeof a1) m loc ofs v m' ->
  cl_core_inv (CL_State f (Sassign a1 a2) k e le) m ->
  cl_core_inv (CL_State f Sskip k e le) m'.
Proof.
move=> V A B C D. 
have WD: mem_wd m'.
{ suff: mem_wd m. move=> WD.
  suff: val_valid v m. move=> VAL.
  apply: (assign_loc_mem_wd WD VAL C).
  apply: (sem_cast_val_valid B).
  by case: D=> S _; apply: (eval_expr_valid' V S A).
  by case: D; case. }
have ST: cl_state_inv m' e le.
{ inv C; case: D=> []S; move: (eval_expr_valid' V S A)=> VAL.
  { case: S=> C D E F; split=> //.
    by move=> x b ty G; apply: (Mem.store_valid_block_1 _ _ _ _ _ _ H0 _ (C _ _ _ G)).
    move=> x v0 G; case: v0 G=> // b i G.
    by apply: (Mem.store_valid_block_1 _ _ _ _ _ _ H0 _ (D _ _ G)). }
  { case: S=> C D E F; split=> //.
    move=> x b ty G; apply/(mem_forward_valid (m:=m)).
    by apply: (storebytes_forward _ _ _ _ _ H4).
    by apply: (C _ _ _ G).
    move=> x v G; apply/(mem_forward_val_valid (m:=m)).
    by apply: (storebytes_forward _ _ _ _ _ H4).
    by apply: (D _ _ G). }
}
case: D=> E F; split=> //.
apply: (cl_cont_inv_fwd F)=> //.
by apply: (assign_loc_forward _ _ _ _ _ _ C).
Qed.

Lemma vals_valid_i64helpers
      F V (ge : Genv.t F V) m vals t v m' name sg: forall   
      (EC : extcall_io_sem name sg ge vals m t v m')
      (i : I64Helpers.is_I64_helper hf name sg),
   val_valid v m'.
Proof. intros; inv i; inv EC; simpl in *; try solve[inv H0; simpl; auto]. Qed.

Lemma vals_valid_nonobservables 
      F V (ge : Genv.t F V) m ef vals t v m': forall    
      (OBS: ~ BuiltinEffects.observableEF hf ef)
      (EC: external_call ef ge vals m t v m'),
      val_valid v m'.
Proof. intros. 
destruct ef; simpl in *; try solve [elim OBS; trivial].
destruct (I64Helpers.is_I64_helper_dec hf name sg);
    try solve [elim (OBS n)]; clear OBS.
  eapply vals_valid_i64helpers; eassumption.
destruct (I64Helpers.is_I64_helper_dec hf name sg);
    try solve [elim (OBS n)]; clear OBS.
  eapply vals_valid_i64helpers; eassumption.
inv EC. apply Mem.valid_new_block in H. simpl. eapply store_forward; eassumption.
inv EC. simpl; auto.
inv EC. simpl; auto.
Qed.
(*END move*)

Lemma nuke_step ge c m c' m' :
  clight_corestep hf function_entry1 ge c m c' m' -> 
  valid_genv ge m -> 
  cl_core_inv c m ->
  cl_core_inv c' m'.
Proof.
case; move {c m c' m'}.

{ move=> f a1 a2 k e le m0 loc ofs v2 v m0' H H2 H3 H4 H5 H6.
  by apply: (assign_loc_valid (m:=m0)(v2:=v2)(a1:=a1)). }

{ move=> f id a k e le m' v Heval Hginv; case; case=> A B C D; split=> //. 
  split=> // x v0; case: (eq_block x id)=> eq; 
    first by subst id; rewrite PTree.gss; case=> <-; apply: eval_expr_valid'.
  by rewrite PTree.gso=> //; apply: B. }   

{ move=> f optid a a1 k e te m0 tyargs tyres vf vargs fd H H2 H3 H4 H5 H6.
  case=> A B; split=> //; first by apply: (eval_exprlist_valid' H6 A H3).
  by case: A. }

{ move=> f optid ef tyargs a1 k e te m0 vargs t vres m0' H2 H3 H4 H5.
  case; case=> A B C D; split=> //. 
  split=> //; first by move=> *; apply: (external_call_valid_block _ _ _ _ _ _ H3); apply: A.
  move=> x v; case: optid=> /=.
  move=> a; case: (eq_block x a).
  move=> ?; subst a; rewrite PTree.gss; case=> <-.
  by apply: (vals_valid_nonobservables (m:=m0) (ge:=ge)).
  move=> Hneq; rewrite PTree.gso=> //; case: v=> // b ? Hte.
  by apply: (external_call_valid_block _ _ _ _ _ _ H3); apply: (B _ _ Hte).
  by case: v=> // b ? Hte; apply: (external_call_valid_block _ _ _ _ _ _ H3); apply: (B _ _ Hte).
  by apply: (mem_wd_nonobservables H4 H3).
  apply: (cl_cont_inv_fwd (m:=m0))=> //.  
  + by move=> WD; apply: (mem_wd_nonobservables H4 H3).
  + by apply: (external_call_mem_forward _ _ _ _ _ _ _ _ _ H3). }

{ by move=> f s1 s2 k e te m H2; case=> A B; split. }
{ by move=> f s1 s2 k e te m; case=> A B; split. }
{ by move=> f s1 s2 k e te m; case=> A B; split. }
{ by move=> f s1 s2 k e te m; case=> A B; split. }
{ by move=> f a s1 s2 k e te m v1 b H2 H3 H4; case=> A B; split. }
{ by move=> f s1 s2 k e te m H2; case=> A B; split. }
{ by move=> f s1 s2 k e te m x; case=> ?; subst=> H2; case=> A B; split. }
{ by move=> f s1 s2 k e te m H2; case=> A B; split. }
{ by move=> f s1 s2 k e te m H2; case=> A B; split. }
{ by move=> f s1 s2 k e te m H2; case=> A B; split. }
{ move=> f k e te m m' Hfree H2; case; case=> A B C D; split=> //.
  by apply: (freelist_mem_wd _ _ _ Hfree).
  apply: (cl_cont_inv_fwd (m:=m))=> //; first by apply: (cont_inv_call_cont D).
  by move=> _; apply: (freelist_mem_wd _ _ _ Hfree).
  by apply: (freelist_forward _ _ _ Hfree). }
{ move=> f a k e te m v v' m' H H2 Hfree H4; case=> A B; split=> //.
  have Hval: val_valid v' m
    by apply: (sem_cast_val_valid H2); apply: (eval_expr_valid' H4 A H).
  case: v' Hval H2=> //= ? ?; move/(mem_forward_valid _); move/(_ m')=> C D; apply: C.
  by apply: (freelist_forward _ _ _ Hfree).
  by apply: (freelist_mem_wd _ _ _ Hfree); case: A.  
  apply: cont_inv_call_cont; apply: (cl_cont_inv_fwd B).
  by apply: (freelist_mem_wd _ _ _ Hfree).
  by apply: (freelist_forward _ _ _ Hfree). }
{ move=> f k e te m m' H Hfree H2; case=> A B; split=> //.
  by apply: (freelist_mem_wd _ _ _ Hfree); case: A.
  apply: (cl_cont_inv_fwd B); first by apply: (freelist_mem_wd _ _ _ Hfree).
  by apply: (freelist_forward _ _ _ Hfree). }
{ by move=> f a s1 k e te m n H H2 []A B; split. }
{ by move=> f x k e te m []-> H2 []A B; split. }
{ by move=> f k e te m H []A B; split. }
{ by move=> f lbl s k e te m H []A B; split. }
{ move=> f lbl k e te m s' k' H H2 []A B; split=> //.
  by apply: (cont_inv_find_label B H). }
{ move=> f vargs k m e te m' Hfun H []A B; split=> //.
  apply: (function_entry1_state_inv B A Hfun).
  apply: (cl_cont_inv_fwd p)=> WD; first by apply: (function_entry1_mem_wd WD A Hfun).
  by apply: (function_entry1_forward _ _ _ _ _ _ Hfun). }
{ move=> v optid f e te k m H []A B /= [][]C D E; split=> //.
  split=> // x v0; case: optid=> /=.
  move=> a; case: (eq_block x a).
  + by move=> <-; rewrite PTree.gss; case=> <-.
  + move=> ?; rewrite PTree.gso=> //; apply: D.
  by apply: D. }
Qed.  

Program Definition Clight_Nuke : Nuke_sem.t clsem := 
  Nuke_sem.Build_t (I:=cl_core_inv) _ _ _ _ _.
Next Obligation.
move: H2; case: v=> // b i /=.
case: (Int.eq_dec _ _)=> // ?; subst.
case: (Genv.find_funct_ptr _ _)=> //; case=> // f.
case: (type_of_fundef _)=> // t ?.
by case: (_ && _ && _)=> //; case=> <-; split.
Qed.
Next Obligation. by apply: (nuke_step H H0). Qed.
Next Obligation. 
move: H0 H; case: c=> // fd args0 k; case: fd=> //= e t t0.
by case: (_ && _)=> //; case=> ???; subst; case.
Qed.
Next Obligation.
move: H0; case: c H=> //[][]//=?????[]A B C; case: ov H1=> /=.
move=> a D; case=> <- /=; split=> //; first by apply: (cl_cont_inv_fwd (m:=m)).
by move=> _; case=> <-; split=> //; apply: (cl_cont_inv_fwd (m:=m)).
Qed.
Next Obligation.
by move: H0; case: c H=> //=?[]//[]A B C; case: (~~ _)=> //=[][]=> <-; split.
Qed.

End ClightNuke. End CLIGHT_NUKE.
