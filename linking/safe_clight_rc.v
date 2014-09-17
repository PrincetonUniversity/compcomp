Require Import Bool.
Require Import ZArith.
Require Import BinPos.

Require Import Axioms.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert. Import CompcertCommon.
Require Import Clight.
Require Import Clight_coop.
Require Import Clight_eff.

Require Import sepcomp. Import SepComp.
Require Import arguments.

Require Import core_semantics_tcs.
Require Import rc_semantics.
Require Import effect_simulations. Import SM_simulation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module SAFE_CLIGHT_RC. Section SafeClightRC.
Variable hf : I64Helpers.helper_functions.

Notation clsem := (CL_eff_sem1 hf).

Notation rcsem := (RC.effsem clsem).

Variable Z : Type.

Variable espec : external_specification mem external_function Z.

Variable ge : Genv.t fundef Ctypes.type.

Definition cl_state_inv (c : RC.state CL_core) (m : mem) e te := 
  [/\ forall x b (ty : Ctypes.type), 
        PTree.get x e = Some (b,ty) -> 
        RC.roots ge c b
    & forall x v,
        PTree.get x te = Some v -> 
        {subset getBlocks [:: v] <= RC.reach_set ge c m}
  ].

Definition cl_core_inv (c : RC.state CL_core) (m : mem) := 
  match RC.core c with
    | CL_State f s k e te => cl_state_inv c m e te
    | CL_Callstate f args k => {subset getBlocks args <= RC.reach_set ge c m}
    | CL_Returnstate v k => {subset getBlocks [:: v] <= RC.reach_set ge c m}
  end.

Lemma getBlocksP l b : reflect (exists ofs, List.In (Vptr b ofs) l) (b \in getBlocks l).
Proof.
case e: (b \in getBlocks l).
+ by apply: ReflectT; move: e; rewrite /in_mem /= /is_true /= getBlocks_char.
+ apply: ReflectF=> [][]ofs C.
rewrite /in_mem /= /is_true /= in e.
move: C e; elim: l=> //= a l IH; case.
Admitted.

Lemma sem_cast_getBlocks v v' ty ty' : 
  Cop.sem_cast v ty ty' = Some v' -> 
  {subset getBlocks [:: v'] <= getBlocks [:: v]}.
Admitted.

Lemma eval_expr_reach' c m e te a v : 
  cl_state_inv c m e te ->    
  eval_expr ge e te m a v -> 
  {subset getBlocks [:: v] <= RC.reach_set ge c m}.
Proof.
set (P := fun (a0 : expr) v0 => 
            {subset getBlocks [:: v0] <= RC.reach_set ge c m}).
set (P0 := fun (a0 : expr) b0 i0 => 
            {subset getBlocks [:: Vptr b0 i0] <= RC.reach_set ge c m}).
case=> H H2 H3.
case: (eval_expr_lvalue_ind ge e te m P P0)=> //.

{ by move=> id ty v0 H5 b H6; apply: (H2 id v0 H5). }

{ move=> op a0 ty v1 v0 H4 H5 H6 b H7.
  admit. (*unary ops*) }

{ move=> op a1 a2 ty v1 v2 v0 H4 H5 H6 H7 H8 b H9.
  admit. (*binary ops*) }

{ move=> a0 ty v1 v0 H4 H5 H6 b H7; apply: H5.
  by apply: (sem_cast_getBlocks H6 H7). }

{ move=> a0 loc ofs v0 H4 H5 H6 b H7.
  case: {v0} H6 H7. 
  + move=> ch v1 H8 H9 H10.
    have H11: {subset getBlocks [:: v1] <= RC.reach_set ge c m}. 
    { admit. }
    apply: H11.
    by apply: H10.
  + move=> H6; case/getBlocksP=> ofs'; case=> //; case=> <- _.
    by apply: H5; apply/getBlocksP; exists ofs; constructor.
  + move=> H6; case/getBlocksP=> ofs'; case=> //; case=> <- _.
    by apply: H5; apply/getBlocksP; exists ofs; constructor.
}

{ move=> id l ty H4 b; case/getBlocksP=> ofs; case=> //; case=> <- _.
  by apply: REACH_nil; apply: (H _ _ _ H4). }

{ move=> id l ty H4 H5 H6 b; case/getBlocksP=> ofs; case=> //; case=> <- _.
  apply: REACH_nil; apply/orP; left; apply/orP; left; apply/orP; left.
  by apply: (find_symbol_isGlobal _ _ _ H5). }

{ by move/(_ a v H3)=> H4 _; apply: H4. }
Qed.

Lemma eval_lvalue_reach c m e te a b ofs :
  cl_state_inv c m e te -> 
  eval_lvalue ge e te m a b ofs -> 
  {subset getBlocks [:: Vptr b ofs] <= RC.reach_set ge c m}.
Proof.
move=> H H2 b'; case/getBlocksP=> ofs'; case=> //; case=> <- _; case: H2=> //.

{ by case: H=> H ? ? ? ? ?; apply: REACH_nil; apply: H. }

{ move=> id l ty H5 H6 H7.
  apply: REACH_nil; apply/orP; left; apply/orP; left; apply/orP; left.
  by apply: (find_symbol_isGlobal _ _ _ H6). }

{ move=> a0 ty l ofs0; move/(eval_expr_reach' H). 
  move/(_ l); apply; apply/getBlocksP.
  by exists ofs0; constructor. }

{ move=> a0 i ty l ofs0 id fList att delta; move/(eval_expr_reach' H).
  move/(_ l)=> H2 ? ?; apply: H2; apply/getBlocksP.
  by exists ofs0; constructor. }

{ move=> a0 i ty l ofs0 id fList att; move/(eval_expr_reach' H).
  move/(_ l)=> H2 ?; apply: H2; apply/getBlocksP.
  by exists ofs0; constructor. }
Qed.

Lemma eval_expr_reach c m a v : 
  cl_core_inv c m -> 
  match RC.core c with 
    | CL_State f s k e te => 
        eval_expr ge e te m a v -> 
        {subset getBlocks [:: v] <= RC.reach_set ge c m}
    | _ => True
  end.
Proof.
rewrite /cl_core_inv; case: (RC.core c)=> //. 
by move=> f s k e te; apply: eval_expr_reach'.
Qed.

Lemma rc_safe z c m :
  cl_core_inv c m -> 
  (forall n, safeN clsem espec ge n z (RC.core c) m) -> 
  (forall n, safeN rcsem espec ge n z c m).
Proof.
move=> Inv H n; move: z c m Inv {H} (H n); elim: n=> // n IH z c m Inv H /=.
rewrite /RC.at_external /RC.halted; move: H=> /=.
case Hatext: (Clight_coop.CL_at_external _ _)=> // [[[ef sig] args]|].
have Hhlt: Clight_coop.CL_halted (RC.core c) = None.
{ admit. }
rewrite Hhlt; case=> x []Hpre Hpost.
have Hdef: vals_def args.
{ admit. }
rewrite Hdef; exists x; split=> // ret' m' z' Hpost'.
case: (Hpost _ _ _ Hpost')=> c' []Haft HsafeN; move {Hpost Hpost'}.
rewrite /RC.after_external /=; case: ret' Haft.
{ move=> v Haft; exists (RC.mk c' (RC.args c) (v::RC.rets c) (RC.locs c)).
  rewrite Haft; split=> //; apply: IH=> //. 
  admit. }
{ move=> ->; exists (RC.mk c' (RC.args c) (RC.rets c) (RC.locs c)); split=> //.
  apply: IH=> //.
  admit. }
case Hhlt: (Clight_coop.CL_halted (RC.core c))=> [v|].
{ move=> Hexit. 
  have Hdef: ~~is_vundef v by admit.
  by rewrite Hdef. }
case=> c' []m' []step Hsafe.
rewrite /RC.corestep /RC.effstep /=.

have [f [s [k [e [te Heq]]]]]:
  exists f s k e te,
  RC.core c = CL_State f s k e te.
{ admit. }

move: Heq step Inv Hsafe Hatext Hhlt; case: c; case=> //=.
move=> x y z' w u args rets locs; case=> -> -> -> -> -> step; move {x y z' w u}.
case: step=> //; move {f s k e te}.

{ move=> f a1 a2 k e le m0 loc ofs v2 v m0' H H2 H3 H4 Inv Hsafe _ _.
  set (c'' := Clight_coop.CL_State f Clight.Sskip k e le).
  set (c := {|
           RC.core := CL_State f (Sassign a1 a2) k e le;
           RC.args := args;
           RC.rets := rets;
           RC.locs := locs |}).
  set (locs'' :=  fun b : block =>
         RC.locs c b || freshloc m0 m0' b || RC.reach_set ge c m0 b).
  exists (RC.mk c'' (RC.args c) (RC.rets c) locs''), m0'=> /=.
  split.
  exists (assign_loc_Effect (Clight.typeof a1) loc ofs).
  split.
  econstructor; eauto.
  split=> //.

  move=> b ofs'.
  rewrite /assign_loc_Effect.
  case Hac: (Ctypes.access_mode _)=> // [ch|].
  + case/andP.
    case/andP.
    move=> Heq _ _.
    have Heq': loc = b. 
    { admit. }
    subst loc.
    move {Heq}.
    rewrite /cl_core_inv /= in Inv.
    apply: (eval_lvalue_reach Inv H).
    apply/getBlocksP.
    by exists ofs; constructor.
  + case/andP.
    case/andP.
    move=> Heq _ _.
    have Heq': loc = b. 
    { admit. }
    subst loc.
    move {Heq}.
    rewrite /cl_core_inv /= in Inv.
    apply: (eval_lvalue_reach Inv H).
    apply/getBlocksP.
    by exists ofs; constructor.

  apply: IH=> //. 
  
  (*reestablish invariant*)
  move: Inv; rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> H5 H6; split=> //=.
  admit. (*easy*)
  admit. (*easy*)
}

Admitted. (*TODO*)

End SafeClightRC. End SAFE_CLIGHT_RC.