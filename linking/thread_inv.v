Require Import Axioms.

Require Import sepcomp. Import SepComp.
Require Import simulations. 

Require Import pos.
Require Import stack. 
Require Import cast.
Require Import compcert_linking.
Require Import compcert_threads.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import AST.    (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Memory.
Require Import Integers.

Require Import ZArith.

Module ThreadInv. Section ThreadInv.

Variables semS semT : Modsem.t.

Variable pS : ThreadPool.t semS.

Variable pT : ThreadPool.t semT.

Import ThreadPool.

Import SM_simulation.

Notation SIM semS semT geS geT := (SM_simulation_inject semS semT geS geT).

Variable sim : 
  SIM (Modsem.sem semS) (Modsem.sem semT) (Modsem.ge semS) (Modsem.ge semT). 

Variable mu : SM_Injection.

Variables mS mT : mem.

Notation MATCH cd c d := (match_state sim cd mu c mS d mT).

Lemma ord_eq (j k : pos) : j = k -> 'I_j = 'I_k.
Proof. by move=> ->. Qed.

Record t : Prop := mk
  { num_threads_eq : 
      num_threads pS = num_threads pT 

  ; krun_inv : 
      forall (tid : 'I_(num_threads pS)) c,
      pool pS tid = Krun c ->
      exists d,
        pool pT (cast_ty (ord_eq num_threads_eq) tid) = Krun d
        /\ exists cd, MATCH cd c d

  ; kstage_inv :
      forall (tid : 'I_(num_threads pS)) ef argsS c,
      pool pS tid = Kstage ef argsS c ->
      exists d argsT,
        pool pT (cast_ty (ord_eq num_threads_eq) tid) = Kstage ef argsT d
        /\ val_list_inject (as_inj mu) argsS argsT
        /\ at_external (Modsem.sem semS) c = Some (ef, ef_sig ef, argsS)
        /\ exists cd, MATCH cd c d
  }.

End ThreadInv. End ThreadInv.



