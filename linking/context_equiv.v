(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

Require Import pos.
Require Import compcert_linking.
Require Import rc_semantics.
Require Import rc_semantics_lemmas.
Require Import context.
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

Import SM_simulation.
Import Wholeprog_sim.
Import Linker. 
Import Modsem.

Lemma pos_incr' (p : pos) : (0 < (p+1))%nat.                           
Proof. omega. Qed.                                                     
                                                                       
Definition pos_incr (p : pos) := mkPos (pos_incr' p).                  

Module Prog.
Record t (N : pos) : Type := mk {sems :> 'I_N -> Modsem.t}.
End Prog.

Section ExtendSems.

Variable ge : ge_ty.
Variable C : Ctx.t ge.
Variable N0 : pos.

Let N := pos_incr N0.

Lemma lt_ssrnatlt n m : lt n m -> ssrnat.leq (S n) m.
Proof. by move=> H; apply/ssrnat.ltP. Qed.

Definition extend_sems (f : 'I_N0 -> Modsem.t) (ix : 'I_N) : Modsem.t :=
  match lt_dec ix N0 with
    | left pf => let ix' : 'I_N0 := Ordinal (lt_ssrnatlt pf) in f ix'
    | right _ => C.(Ctx.C)
  end.

End ExtendSems.

(** * Reach-Closed Contextual Equivalence *)

Definition apply_ctx (ge : ge_ty) (C : Ctx.t ge) 
                     (N : pos) (p : Prog.t N) : Prog.t (pos_incr N) :=
  Prog.mk (extend_sems C p.(Prog.sems)).

Lemma leq_N_Nincr (N : pos) : ssrnat.leq N (pos_incr N).
Proof. by rewrite /= plus_comm. Qed.

Lemma leq_SN_Nincr (N : pos) : ssrnat.leq (S N) (pos_incr N).
Proof. by rewrite /= plus_comm. Qed.

Definition link_ctx (ge : ge_ty) (C : Ctx.t ge) (N : pos) (p : Prog.t N) plt : EffectSem :=
  let extended_plt (id : ident) := 
    match plt id with
      | None => Some (Ordinal (leq_SN_Nincr N))
      | Some ix => Some (widen_ord (leq_N_Nincr N) ix)
    end
  in effsem (pos_incr N) (Prog.sems (apply_ctx C p)) extended_plt.

Definition Equiv_ctx (ge : ge_ty) (N : pos) plt (p1 p2 : Prog.t N) :=
  forall C : Ctx.t ge,
  forall (main : val) (args1 args2 : list val) m1 m2,
  forall j, cc_init_inv j ge args1 m1 ge args2 m2 -> 
  forall c1, initial_core (link_ctx C p1 plt) ge main args1 = Some c1 -> 
  forall c2, initial_core (link_ctx C p2 plt) ge main args2 = Some c2 -> 
  (forall n, safeN (link_ctx C p1 plt) ge n c1 m1) -> 
      (terminates (link_ctx C p1 plt) ge c1 m1 
   <-> terminates (link_ctx C p2 plt) ge c2 m2).

(** An alternate of contextual equivalence, in which the initial memory [m]
 is equal in source and target (this is possible, e.g., if [m] contains just
 globals). [m] must self-inject. 

 The advantage of this alternate notion is that it is easily shown reflexive and
 transitive. *)

Definition Equiv_ctx2 (ge : ge_ty) (N : pos) plt (p1 p2 : Prog.t N) :=
  forall C : Ctx.t ge,
  forall (main : val) (args : list val) m,
  cc_init_inv (Mem.flat_inj (Mem.nextblock m)) ge args m ge args m -> 
  forall c1, initial_core (link_ctx C p1 plt) ge main args = Some c1 -> 
  (forall n, safeN (link_ctx C p1 plt) ge n c1 m) -> 
  exists c2, 
  [/\ initial_core (link_ctx C p2 plt) ge main args = Some c2 
    , (forall n, safeN (link_ctx C p2 plt) ge n c2 m) 
    & (terminates (link_ctx C p1 plt) ge c1 m 
   <-> terminates (link_ctx C p2 plt) ge c2 m)].

Lemma Equiv_ctx2_refl ge N plt (p : Prog.t N) : Equiv_ctx2 ge plt p p.
Proof. by move=> C main args m Inv c1 -> Hsafe; exists c1; split. Qed.

Lemma Equiv_ctx2_trans ge N plt (p1 p2 p3 : Prog.t N) : 
  Equiv_ctx2 ge plt p1 p2 -> 
  Equiv_ctx2 ge plt p2 p3 -> 
  Equiv_ctx2 ge plt p1 p3.
Proof. 
move=> H1 H2 C main args m Inv c1 Init1 Hsafe.
case (H1 C main args m Inv c1 Init1 Hsafe)=> c2 []Init2 Hsafe2 Hterm12.
case: (H2 C main args m Inv c2 Init2 Hsafe2)=> c3 []Init3 Hsafe3 Hterm23.
by exists c3; split=> //; rewrite Hterm12 Hterm23.
Qed.

(** Prove that Simulation implies Equiv_ctx *)

Module ContextEquiv (LS : LINKING_SIMULATION). 
                                                                       
Import LS.                                                             
                                                                       
Section ContextEquiv.

Variable N : pos.
Variable pS pT : Prog.t N.
Variable rclosed_S : forall ix : 'I_N, RCSem.t (Prog.sems pS ix).(sem) (Prog.sems pS ix).(ge).
Variable valid_T : forall ix : 'I_N, Nuke_sem.t (Prog.sems pT ix).(sem).
Variable targets_det : forall ix : 'I_N, corestep_fun (Prog.sems pT ix).(sem).
Variable plt : ident -> option 'I_N.
Variable sims : 
  forall ix : 'I_N,                                          
  let s := Prog.sems pS ix in                                              
  let t := Prog.sems pT ix in                                              
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).
Variable ge_top : ge_ty.                                                     
Variable domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pS ix).(ge).
Variable domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pT ix).(ge). 
Variable find_symbol_ST : 
  forall (ix : 'I_N) id bf, 
  Genv.find_symbol (ge (Prog.sems pS ix)) id = Some bf -> 
  Genv.find_symbol (ge (Prog.sems pT ix)) id = Some bf.

Lemma equiv : Equiv_ctx ge_top plt pS pT.
Proof.
rewrite /Equiv_ctx=> C main args1 args2 m1 m2 j Inv c1 Init1 c2 Init2 Hsafe.
have sim: CompCert_wholeprog_sim (link_ctx C pS plt) (link_ctx C pT plt) ge_top ge_top main.
{ apply: link=> ix; rewrite /Prog.sems/apply_ctx/extend_sems. 
  by move=> ??; case e: (lt_dec ix N)=> [pf|pf] //; apply find_symbol_ST.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.rclosed_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.valid_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.sim_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C). }
have target_det: corestep_fun (link_ctx C pT plt). 
{ apply: linking_det=> ix; rewrite /Prog.sems/apply_ctx/extend_sems.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply Ctx.det_C. }
eapply @core_initial 
  with (Sem1 := link_ctx C pS plt) (Sem2 := link_ctx C pT plt) 
       (ge1 := ge_top) (ge2 := ge_top) (halt_inv := cc_halt_inv)
       (j := j) (main := main) (m1 := m1) (m2 := m2) (w := sim)
  in Init1; eauto.
case: Init1=> mu []cd []x []_ []Init2' Hmatch.
rewrite Init2 in Init2'; case: Init2'=> ->.
by apply equitermination in Hmatch.
Qed.

End ContextEquiv.

End ContextEquiv.

(** Prove that Simulation implies Equiv_ctx2 *)

Module ContextEquiv2 (LS : LINKING_SIMULATION). 
                                                                       
Import LS.                                                             
                                                                       
Section ContextEquiv.

Variable N : pos.
Variable pS pT : Prog.t N.
Variable rclosed_S : forall ix : 'I_N, RCSem.t (Prog.sems pS ix).(sem) (Prog.sems pS ix).(ge).
Variable valid_T : forall ix : 'I_N, Nuke_sem.t (Prog.sems pT ix).(sem).
Variable targets_det : forall ix : 'I_N, corestep_fun (Prog.sems pT ix).(sem).
Variable plt : ident -> option 'I_N.
Variable sims : 
  forall ix : 'I_N,                                          
  let s := Prog.sems pS ix in                                              
  let t := Prog.sems pT ix in                                              
  SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge).
Variable ge_top : ge_ty.                                                     
Variable domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pS ix).(ge).
Variable domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (Prog.sems pT ix).(ge). 
Variable find_symbol_ST : 
  forall (ix : 'I_N) id bf, 
  Genv.find_symbol (ge (Prog.sems pS ix)) id = Some bf -> 
  Genv.find_symbol (ge (Prog.sems pT ix)) id = Some bf.

Lemma equiv : Equiv_ctx2 ge_top plt pS pT.
Proof.
rewrite /Equiv_ctx=> C main args m Init c1 Init1 Hsafe.
have sim: CompCert_wholeprog_sim (link_ctx C pS plt) (link_ctx C pT plt) ge_top ge_top main.
{ apply: link=> ix; rewrite /Prog.sems/apply_ctx/extend_sems. 
  by move=> ??; case e: (lt_dec ix N)=> [pf|pf] //; apply find_symbol_ST.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.rclosed_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.valid_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.sim_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C).
  by case e: (lt_dec ix N)=> [pf|pf] //; apply: (Ctx.domeq_C C). }
have target_det: corestep_fun (link_ctx C pT plt). 
{ apply: linking_det=> ix; rewrite /Prog.sems/apply_ctx/extend_sems.
  by case e: (lt_dec ix N)=> [pf|pf] //; apply Ctx.det_C. }
eapply @core_initial 
  with (Sem1 := link_ctx C pS plt) (Sem2 := link_ctx C pT plt) 
       (ge1 := ge_top) (ge2 := ge_top) (halt_inv := cc_halt_inv)
       (j := Mem.flat_inj (Mem.nextblock m)) (main := main) (m1 := m) (m2 := m) (w := sim)
  in Init1; eauto.
case: Init1=> mu []cd []c2 []_ []Init2' Hmatch.
exists c2; split=> //; first by eapply safety_preservation; eauto.
by apply equitermination in Hmatch.
Qed.

End ContextEquiv.

End ContextEquiv2.



