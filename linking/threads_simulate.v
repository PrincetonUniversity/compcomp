Require Import Axioms.

Require Import sepcomp. Import SepComp.
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
  admit. (*TODO*)
}
Qed. 

End ThreadsSimulate. End ThreadsSimulate.
