Require Import Bool.

Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.

Require Import mem_lemmas. (*needed for definition of mem_forward etc*)
Require Import semantics.
Require Import semantics_lemmas.
Require Import structured_injections.
Require Import reach.
Require Import mem_welldefined.

Require Import effect_semantics. (*for specialization below*)

(** * Closed (Whole) Program Simulations *)

(** Closed simulations differ from the open simulations of [simulations.v] in
that they lack clauses for [at_external] and [after_external] (closed programs
do not call external functions). *)

(** Also, previously, we retained effects even in closed program simulations.
But this meant we had to paramterize over [EffectSemantics] (specialized to
CompCert memories), and not over just [CoreSemantics]. Since the paper, we have
updated closed simulations to remove the effects, which has made it possible to
use the same simulation structure in a wider variety of situations (e.g., to 
relate semantics that may not use CompCert memories). *)

Module Wholeprog_sim. Section Wholeprog_sim.

Context {G1 C1 M1 G2 C2 M2 V T : Type}

(Sem1 : @CoreSemantics G1 C1 M1 V T)
(Sem2 : @CoreSemantics G2 C2 M2 V T)

(ge1 : G1)
(ge2 : G2)

(main : V).

Variable ge_inv : G1 -> G2 -> Prop.

Variable init_inv : meminj -> G1 -> list V -> M1 -> G2 -> list V -> M2 -> Prop.

Variable halt_inv : SM_Injection -> G1 -> V -> M1 -> G2 -> V -> M2 -> Prop.

Record Wholeprog_sim := 
{ core_data : Type
; match_state : core_data -> SM_Injection -> C1 -> M1 -> C2 -> M2 -> Prop
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord
; genv_inv : ge_inv ge1 ge2
; core_initial : 
    forall j c1 vals1 m1 vals2 m2,
    initial_core Sem1 ge1 main vals1 = Some c1 ->
    init_inv j ge1 vals1 m1 ge2 vals2 m2 ->
    exists mu cd c2,
      as_inj mu = j 
      /\ initial_core Sem2 ge2 main vals2 = Some c2 
      /\ match_state cd mu c1 m1 c2 m2
; core_diagram : 
    forall st1 m1 st1' m1', 
    corestep Sem1 ge1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
    match_state cd' mu' st1' m1' st2' m2' 
    /\ (corestep_plus Sem2 ge2 st2 m2 st2' m2' 
        \/ (corestep_star Sem2 ge2 st2 m2 st2' m2' /\ core_ord cd' cd))
; core_halted : 
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 = Some v1 ->
    exists j v2, 
       halt_inv j ge1 v1 m1 ge2 v2 m2 
    /\ halted Sem2 c2 = Some v2 }.

End Wholeprog_sim.

End Wholeprog_sim.

Section CompCert_wholeprog_sim.

Context {F1 V1 C1 F2 V2 C2 : Type}

(Sem1 : @EffectSem (Genv.t F1 V1) C1)
(Sem2 : @EffectSem (Genv.t F2 V2) C2)

(ge1 : Genv.t F1 V1)
(ge2 : Genv.t F2 V2)

(main : val).

Definition cc_init_inv j (ge1 : Genv.t F1 V1) vals1 m1 (ge2 : Genv.t F2 V2) vals2 m2 :=
  Mem.inject j m1 m2 /\ Forall2 (val_inject j) vals1 vals2 
  /\ meminj_preserves_globals ge1 j /\ globalfunction_ptr_inject ge1 j 
  /\ mem_wd m2 /\ valid_genv ge2 m2 /\ Forall (fun v2 => val_valid v2 m2) vals2.
  
Definition cc_halt_inv j (ge1 : Genv.t F1 V1) v1 m1 (ge2 : Genv.t F2 V2) v2 m2 :=
  meminj_preserves_globals ge1 (as_inj j)
  /\ val_inject (as_inj j) v1 v2
  /\ Mem.inject (as_inj j) m1 m2.

Definition CompCert_wholeprog_sim :=
  @Wholeprog_sim.Wholeprog_sim _ _ _ _ _ _ _ _
    Sem1 Sem2
    ge1 ge2
    main
    genvs_domain_eq
    cc_init_inv
    cc_halt_inv.

End CompCert_wholeprog_sim.