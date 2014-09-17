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

Lemma REACH_mono' U V (H: {subset U <= V}) m : {subset REACH m U <= REACH m V}.
Proof.
move=> b; rewrite /in_mem /= /is_true /=.
by apply: REACH_mono; apply: H.
Qed.

Lemma loadv_reach_set ch (c : RC.state CL_core) m b ofs v :
  Mem.loadv ch m (Vptr b ofs) = Some v -> 
  b \in RC.reach_set ge c m -> 
  {subset getBlocks [:: v] <= RC.reach_set ge c m}.
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

{ move=> op a0 ty v1 v0 H4 H5 H6 b H7; elim: op H6=> /=.
  + rewrite /Cop.sem_notbool.
    case: (Cop.classify_bool (typeof a0))=> //.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Floats.Float.cmp _ _ _).
    case: v1 H4 H5=> // i H8 H9. 
    case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Integers.Int.eq _ _).
    move=> _; case=> Heq; subst v0.
    move: H7; case/getBlocksP=> x; case=> //.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.                                            
    move: H7; case/getBlocksP=> x; case=> //.
    by rewrite /Val.of_bool; case: (Integers.Int64.eq _ _).  
  + rewrite /Cop.sem_notint.
    case: (Cop.classify_notint (typeof a0))=> // _.
    case: v1 H4 H5=> // i H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
  + rewrite /Cop.sem_neg.
    case Hcl: (Cop.classify_neg (typeof a0))=> // [sgn||].
    case Hv1: v1 H4 H5=> // [v0']; subst.
    move=> H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case.
    case: v1 H4 H5=> // f H8 H9; case=> Heq; subst v0.
    by move: H7; case/getBlocksP=> x; case. }    

{ move=> op a1 a2 ty v1 v2 v0 H4 H5 H6 H7 H8 b H9; elim: op H6 H8=> /=.
  + rewrite /Cop.sem_add. 
    case: (Cop.classify_add _ _)=> //.
    move=> ? ? Heval; case: v1 H4 H5=> // b0 i H4 H5; case: v2 H7 Heval=> // i0 ? ?.
    case=> Heq; subst v0; move: H9; case/getBlocksP=> ?; case=> //; case=> ? ?; subst b0.
    by apply: H5; apply/getBlocksP; exists i; constructor.
    move=> ? ? Heval; case: v1 H4 H5=> // i H4 H5; case: v2 H7 Heval=> // ? ? H7 Heval.
    case=> Heq; subst v0; apply: H7; case: (getBlocksP _ _ H9)=> ?; case; case=> Heq' _; subst.
    by apply/getBlocksP; eexists; eauto; econstructor; eauto.
    move=> ? ? Heval; case: v1 H4 H5=> // ? ? H4 H5; case: v2 H7 Heval=> // ? ? ?; case=> ?; subst.
    apply: H5; case: (getBlocksP _ _ H9)=> ?; case; case=> <- _.
    by apply/getBlocksP; eexists; eauto; econstructor; eauto.
    move=> ? ? Heval; case: v1 H4 H5=> // i H4 H5; case: v2 H7 Heval=> // ? ? H7 Heval.
    case=> Heq; subst v0; apply: H7; case: (getBlocksP _ _ H9)=> ?; case; case=> Heq' _; subst.
    by apply/getBlocksP; eexists; eauto; econstructor; eauto.
    admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit. }

{ move=> a0 ty v1 v0 H4 H5 H6 b H7; apply: H5.
  by apply: (sem_cast_getBlocks H6 H7). }

{ move=> a0 loc ofs v0 H4 H5 H6 b H7.
  case: {v0} H6 H7. 
  + move=> ch v1 H8 H9 H10.
    have H11: {subset getBlocks [:: v1] <= RC.reach_set ge c m}. 
    { have H12: loc \in getBlocks [:: Vptr loc ofs]. 
      { by apply/getBlocksP; exists ofs; constructor. }
      move: {H12}(H5 _ H12)=> H12.
      by apply: (loadv_reach_set H9). }
    by apply: H11; apply: H10.
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
  
move: step Inv Hsafe Hatext Hhlt; case: c=> /= core args rets locs; case.

{ move=> f a1 a2 k e le m0 loc ofs v2 v m0' H H2 H3 H4 Inv Hsafe _ _.
  set (c'' := Clight_coop.CL_State f Clight.Sskip k e le).
  set (c := {|
         RC.core := CL_State f (Sassign a1 a2) k e le;
         RC.args := args;
         RC.rets := rets;
         RC.locs := locs |}).
  set (locs'' :=  fun b : block =>
         RC.locs c b || freshloc m0 m0' b || RC.reach_set ge c m0 b).
  exists (RC.mk c'' (RC.args c) (RC.rets c) locs''), m0'=> /=; split.
  exists (assign_loc_Effect (Clight.typeof a1) loc ofs); split; first by econstructor; eauto.
  split=> //.

  { move=> b ofs'; rewrite /assign_loc_Effect.
  case Hac: (Ctypes.access_mode _)=> // [ch|].
  + case/andP; case/andP=> Heq _ _.
    have Heq': loc = b by rewrite /eq_block in Heq; case: (Coqlib.peq loc b) Heq.
    subst loc; move {Heq}; rewrite /cl_core_inv /= in Inv.
    by apply: (eval_lvalue_reach Inv H); apply/getBlocksP; exists ofs; constructor.
  + case/andP; case/andP=> Heq _ _.
    have Heq': loc = b by rewrite /eq_block in Heq; case: (Coqlib.peq b loc) Heq.
    subst loc; move {Heq}; rewrite /cl_core_inv /= in Inv.
    by apply: (eval_lvalue_reach Inv H); apply/getBlocksP; exists ofs; constructor. }
  
  { apply: IH=> //.
  (*reestablish invariant*)
  move: Inv; rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> H5 H6; split=> //=.
  { rewrite /locs''=> x b ty H7.
    move: (H5 _ _ _ H7); case/orP; first by move=> ->.
    by rewrite /= => ->; apply/orP; right. }
  { move=> x v0 H7; move: (H6 _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
    by apply: REACH_nil; apply/orP; right; apply/orP; right. } }
}

{ move=> f id a k e te m0 v H Inv H2 _ _.
  set (c'' := CL_State f Sskip k e (PTree.set id v te)).
  set (c := {|
         RC.core := CL_State f (Sset id a) k e te;
         RC.args := args;
         RC.rets := rets;
         RC.locs := locs |}).
  set (locs'' :=  fun b : block =>
         RC.locs c b || freshloc m0 m0 b || RC.reach_set ge c m0 b).
  exists (RC.mk c'' (RC.args c) (RC.rets c) locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.
  
  apply: IH=> //.
  (*reestablish invariant*)
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    by rewrite /= => ->; apply/orP; right. }
  { move=> x v0 H7 b H8; case Heq: (ident_eq x id).
    + subst x; rewrite PTree.gss in H7; case: H7=> Heq'; subst v0.
      move: (eval_expr_reach _ _ Inv H); move/(_ b H8).
      rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
      by apply: REACH_nil; apply/orP; right; apply/orP; right. 
    + rewrite PTree.gso in H7=> //; move: (Hte _ _ H7); move/(_ b H8).
      rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
      by apply: REACH_nil; apply/orP; right; apply/orP; right.  }
}

{ move=> f optid a a1 k e te m0 tyargs tyres vf vargs fd H H2 H3 H4 H5 Inv H6 _ _.
  set (c'' := CL_Callstate fd vargs (Kcall optid f e te k)).
  set (c := {|
         RC.core := CL_State f (Scall optid a a1) k e te;
         RC.args := args;
         RC.rets := rets;
         RC.locs := locs |}).
  set (locs'' :=  fun b : block =>
         RC.locs c b || freshloc m0 m0 b || RC.reach_set ge c m0 b).
  exists (RC.mk c'' (RC.args c) (RC.rets c) locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.
  
Admitted. (*TODO*)

End SafeClightRC. End SAFE_CLIGHT_RC.