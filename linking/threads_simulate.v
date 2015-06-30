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

Variable aggelosS : nat -> PermMap.t.

Variable schedule : nat -> nat.

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
{ by move=> /= *; exists (fun _ => aggelosS 0). 
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
      have [d'0 [tm' [n1 [T [mu' [tstep0 [tcant [MATCH' incr]]]]]]]]:
        exists d'0 tm' n1 T mu',
          effstepN (Modsem.sem semT) (Modsem.ge semT) n1.+1 T
                   d0 tm d'0 tm'
          /\ cant_step (Modsem.sem semT) d'0
          /\ match_state sim cd mu' c'0 m' d'0 tm'
          /\ intern_incr mu mu'. 
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
    admit.
    admit.
    admit.
    admit.
  }
}
Qed. 

End ThreadsSimulate. End ThreadsSimulate.
