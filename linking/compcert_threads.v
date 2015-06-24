Require Import Axioms.

Require Import sepcomp. Import SepComp.

Require Import pos.
Require Import stack. 
Require Import cast.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import AST.     (*for typ*)
Require Import Values. (*for val*)
Require Import Globalenvs. 
Require Import Memory.
Require Import Integers.

Require Import ZArith.

Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation READ := 
  (EF_external 3%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
  (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).

Require Import compcert_linking.

Definition access_map := Maps.PMap.t (Z -> perm_kind -> option permission).

Module PermMap. Section PermMap.

Record t := mk
  { next : block
  ;  map : access_map 
  ;  max : forall (b : positive) (ofs : Z),
                 Mem.perm_order'' (Maps.PMap.get b map ofs Max)
                 (Maps.PMap.get b map ofs Cur)
  ; nextblock : forall (b : positive) (ofs : Z) (k : perm_kind),
                       ~ Coqlib.Plt b next -> Maps.PMap.get b map ofs k = None
  }. 

End PermMap. End PermMap.

Section permMapDefs.

Definition updPermMap (m : mem) (p : PermMap.t) : option mem :=
  match positive_eq_dec (Mem.nextblock m) (PermMap.next p) with
    | left pf => 
        Some (Mem.mkmem 
                        (Mem.mem_contents m) 
                        (PermMap.map p) 
                        (Mem.nextblock m)
                        (PermMap.max p) 
                        (eq_rect_r 
                           (fun n => forall (b : positive) (ofs : Z) (k : perm_kind),
                             ~ Coqlib.Plt b n -> Maps.PMap.get b (PermMap.map p) ofs k = None)
                           (PermMap.nextblock p) pf)
                        (Mem.contents_default m))
    | right _ => None
  end.

End permMapDefs.

Module ThreadPool. Section ThreadPool.

Variable sem : Modsem.t.

Notation cT := (Modsem.C sem).

Inductive ctl : Type :=
  | Krun : cT -> ctl
  | Kstage : external_function -> list val -> cT -> ctl.

Record t := mk
  { num_threads : pos
  ; pool         :> 'I_num_threads -> ctl
  ; counter   : nat
  }.

End ThreadPool. End ThreadPool.

Arguments ThreadPool.Krun [sem] _.
Arguments ThreadPool.Kstage [sem] _ _ _.

Notation pool := ThreadPool.t.

Section poolDefs.

Context {sem : Modsem.t} {next : block}.

Variable (tp : ThreadPool.t sem).

Import ThreadPool.

Notation cT := (Modsem.C sem).
Notation ctl := (ctl sem).
Notation num_threads := (num_threads tp).
Notation thread_pool := (t sem).

Definition addThread (c : ctl) : thread_pool :=
  let: new_num_threads := pos_incr num_threads in
  let: new_tid := ordinal_pos_incr num_threads in
  @mk sem new_num_threads  (fun (n : 'I_new_num_threads) => 
      match unlift new_tid n with
        | None => c
        | Some n' => tp n'
      end) 
   (counter tp).+1.

Definition updThread (tid : 'I_num_threads) (c' : ctl) : thread_pool :=
  @mk sem num_threads (fun (n : 'I_num_threads) => 
      if n == tid then c' else tp n) 
  (counter tp).

Definition schedNext : thread_pool :=
  @mk sem num_threads (pool tp) (counter tp).+1.

Definition getThread (tid : 'I_num_threads) : ctl := tp tid.
  
End poolDefs.

Section poolLemmas.

Context {sem : Modsem.t} {next : block} (tp : ThreadPool.t sem).

Import ThreadPool.

Lemma gssThread (tid : 'I_(num_threads tp)) c' : 
  getThread (updThread tp tid c') tid = c'.
Proof. by rewrite /getThread /updThread /= eq_refl. Qed.

Lemma gsoThread (tid tid' : 'I_(num_threads tp)) c' :
  tid' != tid -> getThread (updThread tp tid c') tid' = getThread tp tid'.
Proof. by rewrite /getThread /updThread /=; case Heq: (tid' == tid). Qed.

Lemma getAddThread c tid :
  tid = ordinal_pos_incr (num_threads tp) ->
  getThread (addThread tp c) tid = c.
Proof. by rewrite /getThread /addThread /= => <-; rewrite unlift_none. Qed.

End poolLemmas.

Inductive Handled : external_function -> Prop :=
  | HandledLock : Handled LOCK
  | HandledUnlock : Handled UNLOCK
  | HandledCreate : Handled CREATE
  (*...*) .

Definition handled (ef : external_function) : bool :=
  match extfunct_eqdec ef LOCK with
    | left _ => true
    | right _ => 
      match extfunct_eqdec ef UNLOCK with
        | left _ => true
        | right _  => 
          match extfunct_eqdec ef CREATE with
            | left _ => true
            | right _  => false
          end
      end
  end.

Lemma extfunct_eqdec_refl ef : exists pf, extfunct_eqdec ef ef = left pf.
Proof. by case H: (extfunct_eqdec _ _)=> [pf|//]; exists pf. Qed.

Lemma handledP ef : reflect (Handled ef) (handled ef).
Proof.
case Hhdl: (handled ef); [apply: ReflectT|apply: ReflectF].
{ move: Hhdl; rewrite /handled; case: (extfunct_eqdec _ _).
   by move=> ->; constructor.
   move=> H; case: (extfunct_eqdec _ _)=> //.
   by move=> ->; constructor.
   move=> H2; case: (extfunct_eqdec _ _)=> //.
   by move=> ->; constructor.
}
{ inversion 1; subst; rewrite /handled in Hhdl. 
   by move: Hhdl; case: (extfunct_eqdec_refl LOCK)=> pf ->.
   by move: Hhdl; case: (extfunct_eqdec_refl UNLOCK)=> pf ->.   
   by move: Hhdl; case: (extfunct_eqdec_refl CREATE)=> pf ->.   
}
Qed.   

Module Concur. Section Concur.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable aggelos : nat -> perm_map.
Variable schedule : nat -> nat.

Section Corestep.

Variable the_ge : Genv.t (Modsem.F sem) (Modsem.V sem).

Inductive step : thread_pool -> mem -> thread_pool -> mem -> Prop :=
  | step_congr : 
      forall tp m c m' (c' : Modsem.C sem),
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Krun c ->
      semantics.corestep the_sem the_ge c m c' m' ->
      step tp m (updThread tp tid (Krun c')) m'

  | step_stage :
      forall tp m c ef args,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Krun c ->
      semantics.at_external the_sem c = Some (ef, ef_sig ef, args) ->
      handled ef ->
      step tp m (schedNext (updThread tp tid (Kstage ef args c))) m

  | step_lock :
      forall tp m c m'' c' m' b ofs,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Kstage LOCK (Vptr b ofs::nil) c ->
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one) ->
      Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      updPermMap m'' (aggelos n) = Some m' -> 
      step tp m (updThread tp tid (Krun c')) m'

  | step_unlock :
      forall tp m c m'' c' m' b ofs,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Kstage UNLOCK (Vptr b ofs::nil) c ->
      Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero) ->
      Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      updPermMap m'' (aggelos n) = Some m' -> 
      step tp m (updThread tp tid (Krun c')) m

  | step_create :
      forall tp m c c' c_new vf arg,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Kstage CREATE (vf::arg::nil) c ->
      semantics.initial_core the_sem the_ge vf (arg::nil) = Some c_new ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      step tp m (addThread (updThread tp tid (Krun c')) (Krun c_new)) m.

End Corestep.

Lemma step_inv the_ge tp c m tp' m' ef sig args : 
  let: n := counter tp in
  let: tid0 := schedule n in
  forall (tid0_lt_pf :  tid0 < num_threads tp),
  let: tid := Ordinal tid0_lt_pf in
  getThread tp tid = Krun c ->
  semantics.at_external the_sem c = Some (ef, sig, args) -> 
  handled ef = false -> 
  ~ step the_ge tp m tp' m'.
Proof. 
move=> pf get Hat; move/handledP=> Hhdl step. 
case: step pf get Hat Hhdl; move {tp m tp' m'}.
{ move=> ????? pf get step pf'; have ->: pf' = pf by apply: proof_irr.
   by rewrite get; case=> <-; erewrite corestep_not_at_external; eauto.
}
{ move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
   by rewrite get; case=> <-; rewrite Hat; case=> <- /= _ _; apply; apply/handledP.
}
{ move=> ???????? pf get Hat ??? pf'; have ->: pf' = pf by apply: proof_irr.
   by rewrite get.
}
{ move=> ???????? pf get Hat ??? pf'; have ->: pf' = pf by apply: proof_irr.
   by rewrite get.
}
{ move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
   by rewrite get.
}
Qed.

Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
Proof. by move/ltP. Qed.

Definition at_external (tp : thread_pool) 
  : option (external_function * signature * seq val) := 
  let: n := counter tp in
  let: tid0 := schedule n in
  match lt_dec tid0 (num_threads tp) with
    | left lt_pf => 
      let: tid := Ordinal (my_ltP lt_pf) in
      match getThread tp tid with 
        | Krun c => 
          match semantics.at_external the_sem c with
            | None => None
            | Some (ef, sg, args) => 
              if handled ef then None 
              else Some (ef, sg, args)
          end
        | Kstage _ _ _ => None
      end
    | right _ => None
  end.

Definition after_external (ov : option val) (tp : thread_pool) :=
  let: n := counter tp in
  let: tid0 := schedule n in
  match lt_dec tid0 (num_threads tp) with
    | left lt_pf => 
      let: tid := Ordinal (my_ltP lt_pf) in
      match getThread tp tid with 
        | Krun c => 
          match semantics.after_external the_sem ov c with
            | None => None
            | Some c' => Some (schedNext (updThread tp tid (Krun c')))
          end
        | Kstage _ _ _ => None
      end
    | right _ => None
  end.

Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

Section InitialCore.

Variable ge : Genv.t (Modsem.F sem) (Modsem.V sem).

Definition initial_core (f : val) (args : list val) : option thread_pool :=
  match initial_core the_sem ge f args with
    | None => None
    | Some c => 
      Some (ThreadPool.mk 
                   one_pos 
                   (fun tid => if tid == ord0 then Krun c 
                                     else Krun c (*bogus value; can't occur*))
                   0)
  end.

End InitialCore.

Definition halted (tp : thread_pool) : option val := None.

Program Definition semantics :
  CoreSemantics (Genv.t (Modsem.F sem) (Modsem.V sem)) thread_pool mem :=
  Build_CoreSemantics _ _ _
    initial_core 
    at_external
    after_external
    halted
    step
    _ _ _.
Next Obligation.
rewrite /at_external.
case Hlt: (lt_dec _ _)=> //[a].
case Hget: (getThread _ _)=> //[c].
case Hat: (semantics.at_external _ _)=>[[[ef sg]  args]|//].
case Hhdl: (handled _)=> //.
elimtype False; apply: (step_inv (my_ltP a) Hget Hat Hhdl H).
Qed.
  
End Concur. End Concur.

Section ConcurLemmas.

Import ThreadPool.

Context {sem : Modsem.t}.

Notation thread_pool := (t sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable  aggelos : nat -> perm_map.
Variable schedule : nat -> nat.

Notation thread_sem := (@Concur.semantics sem aggelos schedule).

Lemma thread_det :
  semantics_lemmas.corestep_fun the_sem ->
  semantics_lemmas.corestep_fun thread_sem.
Proof. 
move=> Hfun m m' m'' ge tp tp' tp''; case; move {tp tp' m m'}.
{ move=> tp m c m' c' pf get step0 step.
   case: step pf get step0; move {tp tp'' m''}.
   + move=> tp m'' c'' m''' c''' pf get step pf'; move: get step.
      have ->: pf' = pf by apply: proof_irr.
      move=> -> step; case=> <- step'.
      by case: (Hfun _ _ _ _ _ _ _ step step')=> <- <-; split.
   + move {m}=> tp m c'' b ofs pf get Hat Hhdl pf'.
      have ->: pf' = pf by apply: proof_irr.
      rewrite get; case=> <- step.
      by move: (corestep_not_at_external _ _ _ _ _ _ step); rewrite Hat.
   + move {m}=> tp m c'' m'' c''' m''' b ofs pf get load store aft upd pf'.
      have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move {m}=> tp m c'' m'' c''' m''' b ofs pf get load store aft upd pf'.
      have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
}
{ move=> tp m c b ofs pf get Hat Hhdl step; case: step pf get Hat Hhdl; move {tp m tp'' m''}.
   + move=> ????? pf' get step pf; have <-: pf' = pf by apply: proof_irr.
      by rewrite get; case=> <-; erewrite corestep_not_at_external; eauto.
   + move=> ????? pf' get Hat Hhdl pf; have <-: pf' = pf by apply: proof_irr.
      by rewrite get; case=> <-; rewrite Hat; case=> -> _ -> _; split.
   + move=> ???????? pf get ???? pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ???????? pf get ???? pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
}
{ move=> tp m c m''' c' m' b ofs pf get load store aft upd step.
   case: step pf get upd load store; move {tp m tp'' m''}.
   + move=> ????? pf get step0 pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ???????? pf get load store aft' upd pf'; have ->: pf' = pf by apply: proof_irr.
      rewrite get; case=> <- <- cs_eq upd' load'; rewrite store; case=> mem_eq; subst.
      by move: aft'; rewrite aft; case=> ->; move: upd'; rewrite upd; case=> ->; split.
   + move=> tp m c'' m'' c'''' m'''' b' ofs' pf get ? store aft' upd' pf'.
      have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
}
{ move=> tp m c m''' c' m' b ofs pf get load store aft upd step. 
   case: step pf get load store aft upd; move {tp m tp'' m''}.
   + move=> ????? pf get step pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ???????? pf get load store aft upd pf'. 
      have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ???????? pf get ? store aft upd pf'.
      have ->: pf' = pf by apply: proof_irr.
      rewrite get; case=> <- <- <- _; rewrite store; case=> <-.
      by rewrite aft; case=> <-; rewrite upd; split.
   + move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
}
{ move=> tp m c c' c_new vf arg pf get init aft step.
   case: step pf get init aft; move {tp m tp'' m''}.
   + move=> ????? pf get ? pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ????? pf get Hat Hhdl pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ???????? pf get ? store aft upd pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ???????? pf get ? store aft upd pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get.
   + move=> ??????? pf get init aft pf'; have ->: pf' = pf by apply: proof_irr.
      by rewrite get; case=> <- <- <-; rewrite init; case=> <-; rewrite aft; case=> <-.
}      
Qed.

End ConcurLemmas.