Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import juicy_mem.

Require Import pos.
Require Import core_semantics_tcs.

Require Import linking.
Require Import compcert_linking.
Require Import wholeprog_simulations. Import Wholeprog_simulation.

Module JuicyCoreSem : CORESEM.

Definition M := juicy_mem.

Definition t G C := CoreSemantics G C M.

Definition instance G C (x : t G C) := core_instance x.

End JuicyCoreSem.

Module J := CoreLinker JuicyCoreSem.

Section erasure.

Variable N : pos.

Variable plt : ident -> option 'I_N.

Variable sems_S : 'I_N -> J.Modsem.t.

Variable sems_T : 'I_N -> Modsem.t.

Notation source := (J.LinkerSem.coresem N sems_S plt).

Notation target := (LinkerSem.coresem N sems_T plt).

(*TODO: wholeprog_simulations: fix so no longer restricted 
 to effect semantics. This will make it possible to state the 
 right simulation here, source <= target. *)

End erasure.

