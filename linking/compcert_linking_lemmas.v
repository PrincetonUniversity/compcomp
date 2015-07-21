Require Import Axioms.

Require Import effect_semantics.

Require Import pos.
Require Import compcert_linking.

Require Import ssreflect ssrbool ssrnat ssrfun seq fintype.
Set Implicit Arguments.

Require Import AST. (*for ident*)
Require Import Values. 
Require Import Globalenvs. 

Section linkingLemmas.

Import Linker.
Import Modsem.

Variable N : pos.
Variable cores : 'I_N -> Modsem.t. 
Variable fun_tbl : ident -> option 'I_N.
Variable my_ge : ge_ty.

Let linker := effsem N cores fun_tbl.

Lemma upd_upd (st : Linker.t N cores) c c' :
  updCore (updCore st c) c' = updCore st c'.
Proof. 
rewrite /updCore /updStack /=; f_equal.
move: (updCore_obligation_1 _ _); simpl.
rewrite collection.COL.theory.unbumpbump=> w2.
by have ->: w2 = updCore_obligation_1 _ _ by apply: proof_irr.
Qed.

Lemma step_STEP {U st1 m1 c1' m1'} : 
  let: c1 := peekCore st1 in
  effect_semantics.effstep 
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof.
move=> STEP; move: (@effstep_corestep _ _ _ _ _ _ _ _ _ STEP)=> STEP'; split.
by left; exists c1'; split.
by move=> ?; exists c1'; split.
by move=> H b ofs; case: H; rewrite/LinkerSem.corestep0; exists c1'; split.
Qed.

Lemma stepN_STEPN {U st1 m1 c1' m1' n} :
  let: c1 := peekCore st1 in
  effect_semantics.effstepN 
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) n U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstepN linker my_ge 
    n U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof.
move: st1 c1' m1 U; elim: n.
move=> st1 c1' m1 U /= [][] <- <- <-; split=> //; f_equal. 
{ have H: Core.upd (peekCore st1) (Core.c (peekCore st1))
        = peekCore st1.
  { by clear; rewrite /Core.upd; case: (peekCore st1). }
  by rewrite H LinkerSem.updPeekCore.
}
move=> n IH st1 c1' m1 U /= => [][]c1'' []m1'' []U1 []U2 []B []C D.
exists (updCore st1 (Core.upd (peekCore st1) c1'')), m1'',U1,U2; split.
by apply: (step_STEP B).
have H: Core.i (peekCore st1)
      = Core.i (peekCore (updCore st1 (Core.upd (peekCore st1) c1''))).
{ admit. }
admit.
(*move: (IH (updCore st1 (Core.upd (peekCore st1) c1'')) c1' m1'' U2).
by rewrite upd_upd=> H; split=> //; move: H; apply; apply: C.*)
Qed.

Lemma stepPLUS_STEPPLUS {U st1 m1 c1' m1'} :
  let: c1 := peekCore st1 in
  effect_semantics.effstep_plus 
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep_plus linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof. by rewrite/effstep_plus=> [][]n; move/stepN_STEPN=> B; exists n. Qed.

Lemma stepSTAR_STEPSTAR {U st1 m1 c1' m1'} :
  let: c1 := peekCore st1 in
  effect_semantics.effstep_star
    (sem (cores (Core.i c1))) 
    (ge (cores (Core.i c1))) U (Core.c c1) m1 c1' m1' -> 
  effect_semantics.effstep_star linker my_ge 
  U st1 m1 (updCore st1 (Core.upd c1 c1')) m1'.
Proof. by rewrite/effstep_star=> [][]n; move/stepN_STEPN=> B; exists n. Qed.

End linkingLemmas.
