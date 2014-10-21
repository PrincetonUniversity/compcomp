(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import pos.
Require Import rc_semantics.
Require Import nucular_semantics.
Require Import compcert_linking. Import Modsem.
Require Import simulations. Import SM_simulation.
Require Import semantics_lemmas.

(** The (deterministic) context [C]. Assumptions on [C] are: 
- [sim_C]: C self-simulates ([C <= C]) (cf. Definition 2, pg. 10). 
- [det_C]: C is deterministic (cf. Definition 2, pg. 10). This is true,
      e.g., of all Clight and assembly contexts. 
- [rclosed_C] restricts to reach-closed contexts (cf. linking/rc_semantics.v).
- [nuke_C] restricts contexts to those that store only valid blocks.  This is
      footnote 5 on pg. 9 of the paper (one reviewer suggested we describe this
      condition in a bit more detail in the paper; we tend to agree and plan to
      do so in the final version). It turns out that this condition holds of all
      assembly contexts; see backend/Asm_nucular.v for the proof. 
- [domeq_C]: The global environment attached to the [C] module semantics 
      has the same domain (set of blocks marked "global") as [ge_top]. *)

Module Ctx. 
Record t (ge_top : ge_ty) : Type := {
    C : Modsem.t
  ; sim_C : SM_simulation_inject C.(sem) C.(sem) C.(ge) C.(ge)
  ; rclosed_C : RCSem.t (sem C) (ge C)
  ; valid_C : Nuke_sem.t (sem C)
  ; det_C : corestep_fun (sem C)
  ; domeq_C : genvs_domain_eq ge_top (ge C)
  }.
End Ctx.
