Require Import Axioms.

Require Import sepcomp. Import SepComp.
Require Import semantics.
Require Import semantics_lemmas.
Require Import simulations. 

Require Import pos.
Require Import stack. 
Require Import cast.
Require Import compcert_linking.
Require Import compcert_threads.
Require Import thread_inv.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import AST.    (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Memory.
Require Import Integers.

Require Import ZArith.

Module ThreadsSimulate. Section ThreadsSimulate.

Import SM_simulation.

Variables semS semT : Modsem.t.

Variable pS : ThreadPool.t semS.

Variable pT : ThreadPool.t semT.

Import ThreadPool.

Import SM_simulation.

Notation SIM semS semT geS geT := (SM_simulation_inject semS semT geS geT).

Variable sim : 
  SIM (Modsem.sem semS) (Modsem.sem semT) (Modsem.ge semS) (Modsem.ge semT). 

Variable schedule : nat -> nat.

Variables aggelosS : nat -> PermMap.t.

Lemma threads_safe Z Espec mu c m d tm (z : Z) :
  @ThreadInv.t semS semT c d sim mu m tm ->
  (forall n, safeN (@Concur.semantics semS aggelosS schedule) Espec
               (Modsem.ge semS) n z c m) ->
  (forall n, 
   exists aggelosT : nat -> PermMap.t,
     safeN (@Concur.semantics semT aggelosT schedule) Espec
               (Modsem.ge semT) n z d tm).  
Proof.
move=> INV SAFE n; move: mu c m d tm z INV SAFE; elim: n.
{ by move=> /= ??????; exists (fun _ => aggelosS 0). 
}
{ move=> n IH mu c m d tm z INV SAFE /=.
  move: (SAFE)=> SAFE0.
  move: (SAFE (S n))=> /=.
  case atS : (Concur.at_external _ c)=> [[[ef sg] argsS]|]. 
  { admit. (*TODO*) }
  { have ->: Concur.at_external schedule d = None.
    { admit. }
    case=> c' []m' []STEP SAFE'.
    inversion STEP; subst.
    { (*step0*)
      move: H0=> step0; move: H=> getS.
      have [U estep0]: 
        exists U, effstepN (Modsem.sem semS) (Modsem.ge semS) n0.+1 U
                           c0 m c'0 m'.
      { admit. }
      case: (ThreadInv.krun_inv INV (Ordinal tid0_lt_pf) getS).
      move=> d0 []getT []cd MATCH.
      have [d'0 [tm' [n1 [T [mu' [tstep0 [tcant MATCH']]]]]]]:
        exists d'0 tm' n1 T mu',
          effstepN (Modsem.sem semT) (Modsem.ge semT) n1.+1 T
                   d0 tm d'0 tm'
          /\ cant_step (Modsem.sem semT) d'0
          /\ match_state sim cd mu' c'0 m' d'0 tm'.
      { admit. }
      set (c' := updThread c
                 (Ordinal (n:=num_threads c) (m:=schedule (counter c)) tid0_lt_pf) 
                 (Krun c'0)).
      have tid0_lt_pf' : schedule (counter d) < num_threads d.
      { admit. }
      set (d' := updThread d
                 (Ordinal (n:=num_threads d) (m:=schedule (counter d)) tid0_lt_pf')
                 (Krun d'0)).
      have INV': ThreadInv.t c' d' sim mu' m' tm'.
      { admit. }
      have SAFE0': forall n : nat,
        safeN (Concur.semantics aggelosS schedule) Espec (Modsem.ge semS) n z c' m'.
      { admit. }
      case: (IH mu' c' m' d' tm' z INV' SAFE0')=> aggelosT TSAFE.
      exists aggelosT, d', tm'; split; last by [].
      apply Concur.step_congr with d0 n1=> //.
      { admit. (*dependent types*) }
      { by apply: effstepN_corestepN. }
    }
    { 
      set (c' := schedNext (updThread c
                  (Ordinal (n:=num_threads c) (m:=schedule (counter c))
                     tid0_lt_pf) (Kstage ef args c0))) in *.
      case: (ThreadInv.krun_inv INV _ H)=> d0 []H' []cd MATCH.
      case: (core_at_external sim cd mu _ _ _ _ MATCH H0)=> inj []args2.
      case=> hfor []at2 H2. 
      have tid1_lt_pf: schedule (counter d) < num_threads d.
      { admit. }
      set (d' := schedNext (updThread d
                  (Ordinal (n:=num_threads d) (m:=schedule (counter d))
                     tid1_lt_pf) (Kstage ef args2 d0))) in *.
      set (pubSrc' :=
             (fun b : block =>
                locBlocksSrc mu b && REACH m' (exportedSrc mu args) b)) in *.
      set (pubTgt' :=
             (fun b : block =>
                   locBlocksTgt mu b && REACH tm (exportedTgt mu args2) b)) in *.
      set (nu := replace_locals mu pubSrc' pubTgt').
      case: (H2 pubSrc' pubTgt' erefl erefl nu erefl)=> MATCH' INJ'.
      have INV': ThreadInv.t c' d' sim nu m' tm.
      { admit. }
      have SAFE'': (forall n0 : nat,
                      safeN (Concur.semantics aggelosS schedule) Espec 
                            (Modsem.ge semS) n0 z c' m').
      { admit. }
      case: (IH _ _ _ _ _ _ INV' SAFE'')=> aggelosT TSAFE.
      exists aggelosT, d', tm; split=> //.
      apply: Concur.step_stage=> //.
      move: H'. admit. (*dependent type stuff*)                                     
    }
    { 
      set (c' := updThread c
                  (Ordinal (n:=num_threads c) (m:=schedule (counter c))
                     tid0_lt_pf) (Krun c'0)) in *.
      case: (ThreadInv.kstage_inv INV _ H)=> d0 []argsT []H' []vinj []at2 []cd MATCH.
      have [b' [delta [inj vinj']]]:
        exists b' delta, 
          as_inj mu b = Some (b', delta)
          /\ argsT = [:: Vptr b' (Int.add ofs (Int.repr delta))].
      { admit. }
      rewrite vinj' in H'; move {vinj vinj' argsT}.
      have tid0'_lt_pf: schedule (counter d) < num_threads d.
      { admit. }
      have [d'0 H2']:
        exists d'0,
          after_external (Modsem.sem semT) (Some (Vint Int.zero)) d0 = Some d'0.
      { admit. }
      set (d' := updThread d
                   (Ordinal (n:=num_threads d) (m:=schedule (counter d)) 
                      tid0'_lt_pf) (Krun d'0)) in *.
      have H0': 
        Mem.load Mint32 tm b' (Int.intval (Int.add ofs (Int.repr delta)))
          = Some (Vint Int.one).
      { admit. }
      have [tm'' H1']:
        exists tm'', 
          Mem.store Mint32 tm b' (Int.intval (Int.add ofs (Int.repr delta))) (Vint Int.zero)
            = Some tm''.
      { admit. }
      set (pubSrc' :=
             (fun b : block =>
                locBlocksSrc mu b && REACH m' (exportedSrc mu [:: Vptr b ofs]) b)) in *.
      set (pubTgt' :=
             (fun b : block =>
                locBlocksTgt mu b 
                && REACH tm 
                   (exportedTgt mu [:: Vptr b' (Int.add ofs (Int.repr delta))]) b)) in *.
      set (nu := replace_locals mu pubSrc' pubTgt').
      have [mu' [tm' [pm [H3' inj']]]]: 
        exists mu' tm' pm,
          updPermMap tm'' pm = Some tm'
          /\ Mem.inject (as_inj mu') m' tm'. 
      { admit. }
      have INV': ThreadInv.t c' d' sim mu' m' tm'.
      { admit. }
      have SAFE'': (forall n0 : nat,
                      safeN (Concur.semantics aggelosS schedule) Espec 
                            (Modsem.ge semS) n0 z c' m').
      { admit. }
      case: (IH _ _ _ _ _ _ INV' SAFE'')=> aggelosT TSAFE'.
      set (aggelosT' := fun n => if eq_nat_dec n (counter d) then pm else aggelosT n).
      exists aggelosT', d', tm'; split=> //.
      eapply Concur.step_lock; eauto.
      { admit. (*dependent types stuff*) }
      { by rewrite /aggelosT'; case: (eq_nat_dec _ _). }
      { clear - TSAFE'; rewrite /aggelosT'.
        admit. (*by [counter d' = counter d.+1] and an aux. lemma about 
                 safety in concurrent machine, namely: 
                  if two angels [x] and [y] are equal at positions [counter d'] 
                  and greater, then [d'] is safe in [x] iff safe in [y]. *) }
    }
    { admit. (*UNLOCK, symmetric*) }
    { admit. (*thread_create*) }
  }
}
Qed. 

End ThreadsSimulate. End ThreadsSimulate.
