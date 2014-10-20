(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

Require Import pos.
Require Import compcert_linking.
Require Import rc_semantics.
Require Import rc_semantics_lemmas.
Require Import linking_spec.

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import nucular_semantics.
Require Import Values.   
Require Import closed_simulations_lemmas.
Require Import closed_safety.
Require Import semantics_lemmas.

Import Wholeprog_sim.
Import SM_simulation.
Import Linker. 
Import Modsem.

(** * Reach-Closed Contextual Equivalence *)

Module ContextEquiv (LS : LINKING_SIMULATION).                  
                                                                       
Import LS.                                                             
                                                                       
Lemma pos_incr' (p : pos) : (0 < (p+1))%nat.                           
Proof. omega. Qed.                                                     
                                                                       
Definition pos_incr (p : pos) := mkPos (pos_incr' p).                  

Section ContextEquiv.

Variable (N0 : pos) (sems_S0 sems_T0 : 'I_N0 -> Modsem.t).

Variable rclosed_S0 : forall ix : 'I_N0, RCSem.t (sems_S0 ix).(sem) (sems_S0 ix).(ge).
Variable nucular_T0 : forall ix : 'I_N0, Nuke_sem.t (sems_T0 ix).(sem).

Variable plt0 : ident -> option 'I_N0.
Variable sims0 : forall ix : 'I_N0,                                          
                 let s := sems_S0 ix in                                              
                 let t := sems_T0 ix in                                              
                 SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).

Variable ge_top : ge_ty.                                                     
Variable domeq_S0 : forall ix : 'I_N0, genvs_domain_eq ge_top (sems_S0 ix).(ge).
Variable domeq_T0 : forall ix : 'I_N0, genvs_domain_eq ge_top (sems_T0 ix).(ge). 

Variable find_symbol_ST : 
  forall (i : 'I_N0) id bf, 
  Genv.find_symbol (ge (sems_S0 i)) id = Some bf -> 
  Genv.find_symbol (ge (sems_T0 i)) id = Some bf.

Variable C : Modsem.t.   
Variable sim_C : SM_simulation_inject C.(sem) C.(sem) C.(ge) C.(ge).
Variable domeq_C : genvs_domain_eq ge_top C.(ge).
Variable rclosed_C : RCSem.t (sem C) (ge C).
Variable nuke_C : Nuke_sem.t (sem C).

Let N := pos_incr N0.

Lemma lt_ssrnatlt n m : lt n m -> ssrnat.leq (S n) m.
Proof. by move=> H; apply/ssrnat.ltP. Qed.

Definition extend_sems (f : 'I_N0 -> Modsem.t) (ix : 'I_N) : Modsem.t :=
  match lt_dec ix N0 with
    | left pf => let ix' : 'I_N0 := Ordinal (lt_ssrnatlt pf) in f ix'
    | right _ => C
  end.

(** [sems_S] extends the source semantics with context [C], by mapping all
functions that are not defined by any of the modules in [sems_S0] to [C]
(cf. [extend_sems] above). *)

Let sems_S := extend_sems sems_S0.

(** [sems_T] does the same for the target semantics [sems_T0]. *)

Let sems_T := extend_sems sems_T0.

Lemma find_symbol_ST' : 
  forall (i : 'I_N) id bf, 
  Genv.find_symbol (ge (sems_S i)) id = Some bf -> 
  Genv.find_symbol (ge (sems_T i)) id = Some bf.
Proof.
rewrite /sems_S /sems_T /extend_sems=> i id bf.
by case: (lt_dec i N0)=> // pf; apply: find_symbol_ST.
Qed.

Lemma sims (ix : 'I_N) :
  let s := sems_S ix in
  let t := sems_T ix in
  SM_simulation_inject (sem s) (sem t) (ge s) (ge t).
Proof.
rewrite /sems_S /sems_T /extend_sems; case e: (lt_dec ix N0)=> [pf|//].
by apply: (sims0 (Ordinal (lt_ssrnatlt pf))).
Qed.

Lemma leq_N0_N : ssrnat.leq N0 N.
Proof. by rewrite /N /= plus_comm. Qed.

Lemma leq_SN0_N : ssrnat.leq (S N0) N.
Proof. by rewrite /N /= plus_comm. Qed.

(** [plt] is the new procedure table equal to [plt0] on [dom(plt0)], but which
otherwise maps function [id]s to the module index assigned to the context
[C]. *)

Definition plt (id : ident) := 
  match plt0 id with
    | None => Some (Ordinal leq_SN0_N)
    | Some ix => Some (widen_ord leq_N0_N ix)
  end.

(** [linker_S] and [linker_T] define the extended source--target semantics,
resp., in which [sems_S0] and [sems_T0] are linked with the context [C]. *)

Definition linker_S := effsem N sems_S plt.

Definition linker_T := effsem N sems_T plt.

Lemma rclosed_S (ix : 'I_N) : RCSem.t (sem (sems_S ix)) (ge (sems_S ix)).
Proof. by rewrite /sems_S /extend_sems; case e: (lt_dec ix N0). Qed.

Lemma nucular_T (ix : 'I_N) : Nuke_sem.t (sem (sems_T ix)).
Proof. by rewrite /sems_T /extend_sems; case e: (lt_dec ix N0). Qed.

(** Prove the existence of pairwise simulations between source and target 
module semantics in the extended semantics. *)

Lemma sm_inject (ix : 'I_N) :
 let s := sems_S ix in
 let t0 := sems_T ix in
 SM_simulation_inject (sem s) (sem t0) (ge s) (ge t0).
Proof.
rewrite /= /sems_S /sems_T /extend_sems; case e: (lt_dec _ _)=> [//|].
by apply: sim_C.
Qed.

Lemma genvs_domeq_S (ix : 'I_N) : genvs_domain_eq ge_top (ge (sems_S ix)).
Proof. 
rewrite /sems_S /extend_sems; case e: (lt_dec _ _)=> [//|].
by apply: domeq_C.
Qed.

Lemma genvs_domeq_T (ix : 'I_N) : genvs_domain_eq ge_top (ge (sems_T ix)).
Proof. 
rewrite /sems_T /extend_sems; case e: (lt_dec _ _)=> [//|].
by apply: domeq_C.
Qed.

(** [lifted_sim] proves a closed simulation on the source and target programs,
after they are (independently) linked with the context [C]. *)

Lemma lifted_sim (main : val) :
  CompCert_wholeprog_sim linker_S linker_T ge_top ge_top main.
Proof.
apply: link=> //. 
by apply: find_symbol_ST'.
by apply: rclosed_S.
by apply: nucular_T.
by apply: sm_inject.
by apply: genvs_domeq_S.
by apply: genvs_domeq_T.
Qed.

Import Wholeprog_sim.

(** ** Proof of Corollary 1 *)

Lemma context_equiv 
    (main : val)  
    (targets_det : forall ix : 'I_N, corestep_fun (sem (sems_T ix))) 
    cd mu l1 m1 l2 m2 
    (source_safe : forall n, safeN linker_S ge_top n l1 m1) 
    (match12 : match_state (lifted_sim main) cd mu l1 m1 l2 m2) :
  (terminates linker_S ge_top l1 m1 <-> terminates linker_T ge_top l2 m2).
Proof.
have target_det: corestep_fun linker_T by apply: linking_det.
by apply (equitermination _ _ target_det _ _ _ _ _ _ source_safe match12).
Qed.

(** ** Corollary 1, Specialized to Initial States *)

Lemma init_context_equiv l1 m1 m2 j vals1 vals2 
  (main : val)
  (targets_det : forall ix : 'I_N, corestep_fun (sem (sems_T ix))) 
  (source_safe : forall n, closed_safety.safeN linker_S ge_top n l1 m1)
  (init1 : initial_core linker_S ge_top main vals1 = Some l1)
  (init1_inv : cc_init_inv j ge_top vals1 m1 ge_top vals2 m2) :
  exists l2, 
  [/\ initial_core linker_T ge_top main vals2 = Some l2 
    & (terminates linker_S ge_top l1 m1 <-> terminates linker_T ge_top l2 m2)].
Proof.
eapply @core_initial 
  with (Sem1 := linker_S) (Sem2 := linker_T) 
       (ge1 := ge_top) (ge2 := ge_top) 
       (halt_inv := cc_halt_inv)
       (j := j)
       (main := main)
       (m1 := m1)
       (m2 := m2)
       (w := lifted_sim main)
  in init1; eauto.
case init1=> mu []cd []c2 []H []H2 H3; exists c2; split=> //.
eapply context_equiv; eauto.
Qed.

End ContextEquiv.

End ContextEquiv.



