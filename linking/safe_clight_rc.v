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

Require Import pred_lemmas.
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
        {subset getBlocks [:: v] <= RC.roots ge c}
  ].

Fixpoint cl_cont_inv (c : RC.state CL_core) (k : cont) (m : mem) := 
  match k with
    | Kstop => True
    | Kseq s k' => cl_cont_inv c k' m
    | Kloop1 s1 s2 k' => cl_cont_inv c k' m
    | Kloop2 s1 s2 k' => cl_cont_inv c k' m
    | Kswitch k' => cl_cont_inv c k' m
    | Kcall oid f e te k' => [/\ cl_state_inv c m e te & cl_cont_inv c k' m]
  end.

Definition cl_core_inv (c : RC.state CL_core) (m : mem) := 
  match RC.core c with
    | CL_State f s k e te => 
        [/\ cl_state_inv c m e te 
          , {subset RC.reach_set ge c m <= RC.roots ge c}
          & cl_cont_inv c k m]
    | CL_Callstate f args k => 
        [/\ {subset getBlocks args <= RC.reach_set ge c m} 
          , {subset RC.reach_set ge c m <= RC.roots ge c}
          & cl_cont_inv c k m]
    | CL_Returnstate v k => 
        [/\ {subset getBlocks [:: v] <= RC.reach_set ge c m} 
          & cl_cont_inv c k m]
  end.

Lemma getBlocksP l b : reflect (exists ofs, List.In (Vptr b ofs) l) (b \in getBlocks l).
Proof.
case e: (b \in getBlocks l).
+ by apply: ReflectT; move: e; rewrite /in_mem /= /is_true /= getBlocks_char.
+ apply: ReflectF=> [][]ofs C.
rewrite /in_mem /= /is_true /= in e.
move: C e; elim: l=> //= a l IH; case.
move=> ->; rewrite /getBlocks /= /eq_block.
have ->: Coqlib.peq b b = left erefl. admit.
discriminate.
move/IH.
Admitted.

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
  {subset RC.reach_set ge c m <= RC.roots ge c} ->
  eval_expr ge e te m a v -> 
  {subset getBlocks [:: v] <= RC.roots ge c}.
Proof.
set (P := fun (a0 : expr) v0 => 
            {subset getBlocks [:: v0] <= RC.roots ge c}).
set (P0 := fun (a0 : expr) b0 i0 => 
            {subset getBlocks [:: Vptr b0 i0] <= RC.roots ge c}).
case=> H H2 Hclosed H3.
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
      move: {H12}(H5 _ H12)=> H12 b' Hget.
      by apply: (loadv_reach_set H9)=> //; apply: REACH_nil. }
    by apply: Hclosed; apply: H11; apply: H10.
  + move=> H6; case/getBlocksP=> ofs'; case=> //; case=> <- _.
    by apply: H5; apply/getBlocksP; exists ofs; constructor.
  + move=> H6; case/getBlocksP=> ofs'; case=> //; case=> <- _.
    by apply: H5; apply/getBlocksP; exists ofs; constructor.
}

{ move=> id l ty H4 b; case/getBlocksP=> ofs; case=> //; case=> <- _.
  by apply: (H _ _ _ H4). }

{ move=> id l ty H4 H5 H6 b; case/getBlocksP=> ofs; case=> //; case=> <- _.
  by apply/orP; left; apply: (find_symbol_isGlobal _ _ _ H5). }

{ by move=> H4 H5 b H7; apply: (H4 _ _ H3). }
Qed.

Lemma eval_lvalue_reach c m e te a b ofs :
  cl_state_inv c m e te -> 
  {subset RC.reach_set ge c m <= RC.roots ge c} ->
  eval_lvalue ge e te m a b ofs -> 
  {subset getBlocks [:: Vptr b ofs] <= RC.roots ge c}.
Proof.
move=> H Hclosed H2 b'; case/getBlocksP=> ofs'; case=> //; case=> <- _; case: H2=> //.

{ by case: H=> H ? ? ? ? ?; apply: H. }

{ move=> id l ty H5 H6 H7.
  apply/orP; left.
  by apply: (find_symbol_isGlobal _ _ _ H6). }

{ move=> a0 ty l ofs0; move/(eval_expr_reach' H). 
  move/(_ Hclosed l)=> X; apply: X; apply/getBlocksP.
  by exists ofs0; constructor. }

{ move=> a0 i ty l ofs0 id fList att delta; move/(eval_expr_reach' H).
  move/(_ Hclosed l)=> H2 ? ?; apply: H2; apply/getBlocksP.
  by exists ofs0; constructor. }

{ move=> a0 i ty l ofs0 id fList att; move/(eval_expr_reach' H).
  move/(_ Hclosed l)=> H2 ?; apply: H2; apply/getBlocksP.
  by exists ofs0; constructor. }
Qed.

Lemma eval_exprlist_reach' c m e te aa tys vv : 
  cl_state_inv c m e te ->    
  {subset RC.reach_set ge c m <= RC.roots ge c} ->
  eval_exprlist ge e te m aa tys vv -> 
  {subset getBlocks vv <= RC.roots ge c}.
Proof.
move=> H Hclosed; elim=> // a bl ty tyl v1 v2 vl H2 H3 H4 H5.
move=> b; case/getBlocksP=> ofs; case.
+ move=> Heq; subst v2.
apply: (eval_expr_reach' H Hclosed H2).
apply: (sem_cast_getBlocks H3). 
by apply/getBlocksP; exists ofs; constructor.
+ move=> H6; apply: H5; clear -H6.
elim: vl H6=> // a vl' H7; case.
by move=> Heq; subst a; apply/getBlocksP; exists ofs; constructor.
by move=> H8; apply/getBlocksP; exists ofs; right.
Qed.

Lemma freelist_effect_reach b ofs f k e te locs m :
  let: c := {|
     RC.core := CL_State f (Sreturn None) k e te;
     RC.locs := locs |} in
   FreelistEffect m (blocks_of_env e) b ofs ->
   cl_state_inv c m e te -> 
   {subset RC.reach_set ge c m <= RC.roots ge c} ->
   RC.reach_set ge c m b.
Admitted.

(*FIXME*)
Lemma builtin_effects_reach (c : RC.state CL_core) ef vargs m b ofs :
  BuiltinEffects.BuiltinEffect ge ef vargs m b ofs -> 
  REACH m (getBlocks vargs) b.
Admitted.

Lemma eval_expr_reach c m a v : 
  cl_core_inv c m -> 
  match RC.core c with 
    | CL_State f s k e te => 
        eval_expr ge e te m a v -> 
        {subset getBlocks [:: v] <= RC.roots ge c}
    | _ => True
  end.
Proof.
rewrite /cl_core_inv; case: (RC.core c)=> //. 
by move=> f s k e te []H U V W; move: H U W; apply: eval_expr_reach'.
Qed.

Lemma external_call_reach l (ef : external_function) vargs m t v m' : 
  ~BuiltinEffects.observableEF hf ef -> 
  external_call ef ge vargs m t v m' -> 
  {subset getBlocks vargs <= REACH m l} -> 
  {subset getBlocks [:: v] <= [predU REACH m l & freshloc m m']}.
Admitted.

Lemma cont_inv_call_cont c k m : 
  cl_cont_inv c k m -> 
  cl_cont_inv c (call_cont k) m.
Proof. by elim: k. Qed.

Lemma cont_inv_find_label c lbl s k s' k' m :
  cl_cont_inv c k m -> 
  find_label lbl s (call_cont k) = Some (s', k') -> 
  cl_cont_inv c k' m.
Admitted.

Lemma state_inv_freshlocs c0 c' m m' locs e te :
  let: c := {|RC.core := c0;
              RC.locs := locs |} in
  cl_state_inv c m e te ->
  cl_state_inv {|
     RC.core := c';
     RC.locs := REACH m' (fun b : block =>
            freshloc m m' b || 
            RC.reach_set ge c m b)|} m' e te.
Proof.
+ rewrite /cl_state_inv; case=> He Hte; split.
move=> x b ty H; apply/orP; right.
by apply: REACH_nil; apply/orP; right; apply: REACH_nil; apply: (He _ _ _ H).
move=> x v H b H2; apply/orP; right; apply: REACH_nil.
by apply/orP; right; apply: REACH_nil; apply: (Hte _ _ H _ H2).
Qed.

Lemma cont_inv_freshlocs c0 c' k m m' locs :
   let: c := {|RC.core := c0;
               RC.locs := locs |} in
   cl_cont_inv c k m -> 
   cl_cont_inv
        {|RC.core := c';
          RC.locs := REACH m' (fun b : block =>
            freshloc m m' b || 
            RC.reach_set ge c m b)|} k m'.
Proof.
elim: k=> //= _ _ e te k' H []H2 H3; split=> //.
+ by apply: state_inv_freshlocs.
+ by apply: H.
Qed.

Lemma cont_inv_mem c k m m' : 
  cl_cont_inv c k m -> 
  cl_cont_inv c k m'.
Proof.
elim: k m m'=> //= _ _ e te k IH m m' []H H2; split=> //.
by apply: (IH _ _ H2).
Qed.

Lemma cont_inv_ext1 c c' locs k m :
  cl_cont_inv {| RC.core := c; RC.locs := locs |} k m -> 
  cl_cont_inv {| RC.core := c'; RC.locs := locs |} k m.
Proof.
elim: k=> // ? ? ? ? ? IH /= [] ? ?; split=> //.
by apply: IH.
Qed.
        
Lemma cont_inv_retv c k v m :
  cl_cont_inv c k m ->
  cl_cont_inv
     {|
     RC.core := CL_Returnstate v k;
     RC.locs := [predU getBlocks [:: v] & RC.locs c] |} k m.
Proof.
elim: k=> //=.
by move=> s k IH H; move: (IH H); apply: cont_inv_ext1.
by move=> s s' k IH H; move: (IH H); apply: cont_inv_ext1.
by move=> s s' k IH H; move: (IH H); apply: cont_inv_ext1.
by move=> k IH H; move: (IH H); apply: cont_inv_ext1.
move=> oid f e te k IH []H H2; split=> //.
case: H=> He Hte; split.
move=> x b ty H; case: (orP (He _ _ _ H))=> X; apply/orP; first by left.
by right; apply/orP; right.
move=> x v0 H b Hget; case: (orP (Hte _ _ H _ Hget))=> X; apply/orP.
by left.
by right; apply/orP; right.
by move: (IH H2); apply: cont_inv_ext1.
Qed.

Lemma core_inv_freshlocs locs m m' f s k s' e te :
  let: c := {| RC.core := CL_State f s k e te; RC.locs := locs |} in
  let: locs' := REACH m' (fun b : block => freshloc m m' b || RC.reach_set ge c m b) in
  cl_core_inv c m -> 
  cl_core_inv {| RC.core := CL_State f s' k e te; RC.locs := locs' |} m'.
Proof.
rewrite /cl_core_inv /cl_state_inv /RC.roots /=.
case=> [][]He Hte Hsub; split=> //=.
split.
{ move=> x b ty H7.
  move: (He _ _ _ H7); case/orP; first by move=> ->.
  move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
  by apply: REACH_nil; apply/orP; right. }
{ move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
  rewrite /RC.reach_set /RC.roots /= => H10. 
  by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
{ move=> b X; apply/orP; right.
  rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
  by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
  by apply: REACH_is_closed. }
{ by move: p; apply cont_inv_freshlocs. }
Qed.

Lemma function_entry1_state_inv (c0 : RC.state CL_core) c1 f vargs m e te m' locs : 
  let: c := {| RC.core := c0;
               RC.locs := locs |} in
  let: c' := {| RC.core := c1;
               RC.locs := REACH m' (fun b : block =>
                           freshloc m m' b || 
                           RC.reach_set ge c m b)|} in
  {subset getBlocks vargs <= RC.reach_set ge c m} -> 
  function_entry1 f vargs m e te m' -> 
  cl_state_inv c' m' e te.
Admitted.

Lemma rc_safe z c m :
  cl_core_inv c m -> 
  (forall n, safeN clsem espec ge n z (RC.core c) m) -> 
  (forall n, safeN rcsem espec ge n z c m).
Proof.
move=> Inv H n; move: z c m Inv {H} (H n); elim: n=> // n IH z c m Inv H /=.
rewrite /RC.at_external /RC.halted; move: H=> /=.
case Hatext: (Clight_coop.CL_at_external _ _)=> // [[[ef sig] args]|].
have Hhlt: Clight_coop.CL_halted (RC.core c) = None.
{ case: (CL_at_external_halted_excl hf (RC.core c))=> //.
  rewrite Hatext; discriminate. }
rewrite Hhlt; case=> x []Hpre Hpost.
have Hdef: vals_def args.
{ admit. }
rewrite Hdef; exists x; split=> // ret' m' z' Hpost'.
case: (Hpost _ _ _ Hpost')=> c' []Haft HsafeN; move {Hpost Hpost'}.
rewrite /RC.after_external /=; case: ret' Haft.
{ move=> v Haft; exists (RC.mk c' [predU getBlocks [::v] & RC.locs c]).
  rewrite Haft; split=> //; apply: IH=> //. 
  move: Inv; rewrite /cl_core_inv /=.                                          
  move: Haft; rewrite /CL_after_external; case: (RC.core c)=> // fd vs k.
  case: fd=> // ef' tys ty; case=> <-; case=> H H2 H3 /=. 
  split. 
  + admit.
  + move: (@cont_inv_mem c k m m' H3); clear.
    by apply: cont_inv_retv. }
{ move=> Heq; rewrite Heq; exists (RC.mk c' (RC.locs c)); split=> //.
  apply: IH=> //.
  rewrite /CL_after_external in Heq.
  move: Inv Heq; rewrite /cl_core_inv.
  case: (RC.core c)=> // fd args' k []H H2 H3.
  case: fd=> // ef' tys ty; case=> <- /=.
  move: (@cont_inv_mem c k m m' H3).                                      
  split. 
  + admit.
  + by apply: cont_inv_retv. }              
case Hhlt: (Clight_coop.CL_halted (RC.core c))=> [v|].
{ move=> Hexit. 
  have Hdef: ~~is_vundef v by admit.
  by rewrite Hdef. }
case=> c' []m' []step Hsafe.
rewrite /RC.corestep /RC.effstep /=.
  
move: step Inv Hsafe Hatext Hhlt; case: c=> /= core locs; case.

{ move=> f a1 a2 k e le m0 loc ofs v2 v m0' H H2 H3 H4 Inv Hsafe _ _.
  set (c'' := Clight_coop.CL_State f Clight.Sskip k e le).
  set (c := {|
         RC.core := CL_State f (Sassign a1 a2) k e le;
         RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0'=> /=; split.
  exists (assign_loc_Effect (Clight.typeof a1) loc ofs); split; first by econstructor; eauto.
  split=> //.

  { move=> b ofs'; rewrite /assign_loc_Effect.
  case Hac: (Ctypes.access_mode _)=> // [ch|].
  + case/andP; case/andP=> Heq _ _.
    have Heq': loc = b by rewrite /eq_block in Heq; case: (Coqlib.peq loc b) Heq.
    subst loc; move {Heq}; rewrite /cl_core_inv /= in Inv.
    case: Inv=> Inv Inv2 Inv3; apply: REACH_nil. 
    by apply: (eval_lvalue_reach Inv Inv2 H); apply/getBlocksP; exists ofs; constructor.
  + case/andP; case/andP=> Heq _ _.
    have Heq': loc = b by rewrite /eq_block in Heq; case: (Coqlib.peq b loc) Heq.
    subst loc; move {Heq}; rewrite /cl_core_inv /= in Inv.
    case: Inv=> Inv Inv2 Inv3; apply: REACH_nil.
    by apply: (eval_lvalue_reach Inv Inv2 H); apply/getBlocksP; exists ofs; constructor. }
  { by apply: IH=> //; apply: core_inv_freshlocs. } }

{ move=> f id a k e te m0 v H Inv H2 _ _.
  set (c'' := CL_State f Sskip k e (PTree.set id v te)).
  set (c := {|
         RC.core := CL_State f (Sset id a) k e te;
         RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //.
  (*reestablish invariant*)
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case; case=> He Hte Hsub Hk; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7 b H8; case Heq: (ident_eq x id).
    + subst x; rewrite PTree.gss in H7; case: H7=> Heq'; subst v0.
      move: (eval_expr_reach _ _ Inv H); move/(_ b H8).
      rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
      by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. 
    + rewrite PTree.gso in H7=> //; move: (Hte _ _ H7); move/(_ b H8).
      rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
      by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. } 

{ move=> f optid a a1 k e te m0 tyargs tyres vf vargs fd H H2 H3 H4 H5 Inv H6 _ _.
  set (c'' := CL_Callstate fd vargs (Kcall optid f e te k)).
  set (c := {|
         RC.core := CL_State f (Scall optid a a1) k e te;
         RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //. 

  apply: IH=> //.
  (*reestablish invariant*)
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=.                        
  case=> He Hte //; split. 
  move=> b H7; move: (eval_exprlist_reach' Inv Hsub H3).
  move/(_ b H7); rewrite /locs'' /RC.reach_set /RC.roots /= => H10.
  by apply: REACH_nil; apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  split; last by move: Hk; apply: cont_inv_freshlocs. 
  by move: Inv; apply: state_inv_freshlocs. }

{ (*builtins*)
  move=> f optid ef tyargs a1 k e te m0 vargs t vres m0' H2 H3 H4 Inv H6 _ _.
  set (c'' := CL_State f Sskip k e (set_opttemp optid vres te)).
  set (c := {|
          RC.core := CL_State f (Sbuiltin optid ef tyargs a1) k e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0'=> /=; split.
  exists (BuiltinEffects.BuiltinEffect ge ef vargs m0); split; first by econstructor; eauto.
  split=> //; first by apply: builtin_effects_reach.

  apply: IH=> //.
  (*reestablish invariant*)
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /set_opttemp /=; move {locs'' c c''}.
    move {Hk}; case: optid Inv H6 Hte Hsub.
    { move=> a Inv H6 Hte Hsub x v.
      move: (eval_exprlist_reach' Inv Hsub H2)=> H7.
      have X: {subset getBlocks vargs
            <= RC.reach_set ge 
                 {|
                 RC.core := CL_State f (Sbuiltin (Some a) ef tyargs a1) k e te;
                 RC.locs := locs |} m0}.
      { by move=> b Hget; move: (H7 _ Hget)=> H7'; apply: REACH_nil. }
      move: (external_call_reach H4 H3 X)=> H8.
      case: (ident_eq a x)=> Heq H9.
      + subst x; rewrite PTree.gss in H9; case: H9=> Heq'; subst vres.
        move=> b H9; move: (H8 _ H9); rewrite in_predU; case/orP=> H10.
        by apply/orP; right; apply: REACH_nil; apply/orP; right.
        by apply/orP; right; apply: REACH_nil; apply/orP; left.
      + rewrite PTree.gso in H9.
        move=> b H10; move: (Hte _ _ H9); move/(_ b H10); case/orP=> H.
        by apply/orP; left.
        apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
        by apply/orP; right.
        by move=> C; apply: Heq; rewrite C. }
    { move=> Inv H6 Hte Hsub x v H7 b H8; move: (Hte _ _ H7); move/(_ b H8); case/orP=> H.
      by apply/orP; left.
      apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
      by apply/orP; right. } }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f s1 (Kseq s2 k) e te).
  set (c := {|
          RC.core := CL_State f (Ssequence s1 s2) k e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //.
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10. 
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f s k e te).
  set (c := {|
          RC.core := CL_State f Sskip (Kseq s k) e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //.
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10. 
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f Scontinue k e te).
  set (c := {|
          RC.core := CL_State f Scontinue (Kseq s k) e te;
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //.
  case: Inv=> Inv Hsub Hk.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10. 
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f Sbreak k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk.

  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots /=. 
  case=> He Hte; split=> //=.
  split.
  { rewrite /locs''=> x b ty H7.
    move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> X; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { move=> x v0 H7; move: (Hte _ _ H7)=> H8 b H9; move: (H8 b H9).
    rewrite /locs'' /RC.reach_set /RC.roots /= => H10. 
    by apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil. }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f a s1 s2 k e te m0 v1 b Heval H2 Inv Hsafe _ _.
  set (c'' := CL_State f (if b then s1 else s2) k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.
  by apply: IH=> //; apply: (core_inv_freshlocs _ _ Inv). }

{ move=> f s1 s2 k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f s1 (Kloop1 s1 s2 k) e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 x H Inv Hsafe _ _.
  set (c'' := CL_State f s2 (Kloop2 s1 s2 k) e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f Sskip k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f (Sloop s1 s2) k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f s1 s2 k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f Sskip k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f k e te m0 m0' Hfree Inv Hsafe _ _.
  set (c'' := CL_Returnstate Vundef (call_cont k)).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0'=> /=; split.
  exists (FreelistEffect m0 (blocks_of_env e)); split; first by econstructor; eauto.
  split=> //.

  case: Inv=> Inv Hsub Hk.
  by move=> b ofs Hfree'; apply: (freelist_effect_reach Hfree' Inv).
  apply: IH=> //.
  move: Inv; case=> Hs Hsub Hk; split.
  by move=> ?; move/getBlocksP; case=> ?; case.
  apply: cont_inv_call_cont.
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f a k e te m0 v v' m0' Heval Hcast Hfree Inv Hsafe _ _.
  set (c'' := CL_Returnstate v' (call_cont k)).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0'=> /=; split.
  exists (FreelistEffect m0 (blocks_of_env e)); split; first by econstructor; eauto.
  split=> //.
  case: Inv=> Inv Hsub Hk.
  by move=> b ofs Hfree'; apply: (freelist_effect_reach Hfree' Inv).
  apply: IH=> //.
  move: Inv; case=> Hs Hsub Hk; split. 
  admit.
  apply: cont_inv_call_cont.
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f k e te m0 m0' Hcall Hfree Inv Hsafe _ _.
  set (c'' := CL_Returnstate Vundef k).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0'=> /=; split.
  exists (FreelistEffect m0 (blocks_of_env e)); split; first by econstructor; eauto.
  split=> //.
  case: Inv=> Inv Hsub Hk.
  by move=> b ofs Hfree'; apply: (freelist_effect_reach Hfree' Inv).
  apply: IH=> //.
  split; first by move=> ?; move/getBlocksP; case=> ?; case.
  move: Inv; case=> Hs Hsub Hk; apply cont_inv_freshlocs.
  by move: Hk; apply: cont_inv_ext1. }

{ move=> f s1 s2 k e te m0 n0 Heval Inv Hsafe _ _.
  set (c'' := CL_State f (seq_of_labeled_statement (select_switch n0 s2))
               (Kswitch k) e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f x k e te m0 Hx Inv Hsafe _ _.
  set (c'' := CL_State f Sskip k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f Scontinue k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f lbl s k e te m0 Inv Hsafe _ _.
  set (c'' := CL_State f s k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f lbl k e te m0 s' k' Hfnd Inv Hsafe _ _.
  set (c'' := CL_State f s' k' e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  move: (Inv); rewrite /cl_core_inv /cl_state_inv /RC.roots.
  case=> He Hte; split=> //=.
  { rewrite /locs''=> x' b' ty H7; move: (He _ _ _ H7); case/orP; first by move=> ->.
    move=> /= H8; apply/orP; right; apply: REACH_nil; apply/orP; right.
    by apply: REACH_nil; apply/orP; right. }
  { rewrite /c'' /locs'' /c /= => x' v H7 b' H8; move {locs'' c}.
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H7 _ H8). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  move: Hfnd; apply: cont_inv_find_label.
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> f vargs k m0 e te m0' Hentry Inv Hsafe _ _.
  set (c'' := CL_State f (fn_body f) k e te).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0' (fun b : block =>
         freshloc m0 m0' b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0'=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Inv Hsub Hk; split.
  split.
  { move=> x b ty H.
    set (c''' := {| RC.core := c''; RC.locs := locs'' |}).
    case: (@function_entry1_state_inv c''' (CL_Callstate (Internal f) vargs k) 
                                  _ _ _ _ _ _ _ Inv Hentry)=> /=.
    by move=> He Hte; apply: (He _ _ _ H). }
  { move=> x v H. 
    set (c''' := {| RC.core := c''; RC.locs := locs'' |}).
    case: (@function_entry1_state_inv c''' (CL_Callstate (Internal f) vargs k) 
                                  _ _ _ _ _ _ _ Inv Hentry)=> /=.
    by move=> He Hte; apply: (Hte _ _ H). }
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

{ move=> v optid f e te k m0 Inv Hsafe _ _.
  set (c'' := CL_State f Sskip k e (set_opttemp optid v te)).
  set (c := {|
          RC.core := c'';
          RC.locs := locs |}).
  set (locs'' :=  REACH m0 (fun b : block =>
         freshloc m0 m0 b || RC.reach_set ge c m0 b)).
  exists (RC.mk c'' locs''), m0=> /=; split.
  exists EmptyEffect; split; first by econstructor; eauto.
  split=> //.

  apply: IH=> //. 
  case: Inv=> Hsub Inv.
  rewrite /cl_core_inv /= in Inv; case: Inv; case=> He Hte Hk; split.

  split.
  { move=> x b ty H; apply/orP; right; rewrite /locs'' /=.
    by apply: REACH_nil; move: H; move/He=> X; apply/orP; right; apply: REACH_nil. }
  { move=> x v0; rewrite /set_opttemp /locs'' /c /c''; move {locs'' c'' c}.
    case: optid Hsub Hsafe Hk He Hte=> a. 
    case: (ident_eq a x).
    + move=> Heq Hsub Hsafe Hk He Hte; subst x; rewrite PTree.gss.
      case=> ?; subst v0=> b Hget; apply/orP; right.
      by apply: REACH_nil; apply/orP; right; apply: (Hsub _ Hget).
    + move=> Hneq Hsafe Hsub Hk He Hte; rewrite PTree.gso=> H.
      move=> b Hget; apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
      by apply: (Hte _ _ H _ Hget).
      by subst x. 
    move=> Inv Hk He Hte H b Hget. 
    apply/orP; right; apply: REACH_nil; apply/orP; right; apply: REACH_nil.
    by apply: (Hte _ _ H _ Hget). } 
  { rewrite /locs''; move=> b X; apply/orP; right.
    rewrite /in_mem /= /is_true /= in X; apply REACH_split in X; case: X.
    by apply: REACH_mono'=> ? ?; apply/orP; right; apply: REACH_nil; apply/orP; left.
    by apply: REACH_is_closed. }
  by move: Hk; apply: cont_inv_freshlocs. }

Qed.

End SafeClightRC. End SAFE_CLIGHT_RC.