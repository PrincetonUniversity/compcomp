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
Notation FORK := 
  (EF_external 2%positive 
  (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint))).
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
  | Klock : block -> Z -> cT -> ctl.

Record t := mk
  { num_threads : pos
  ; pool         :> 'I_num_threads -> ctl
  ; counter   : nat
  }.

End ThreadPool. End ThreadPool.

Arguments ThreadPool.Krun [sem] _.
Arguments ThreadPool.Klock [sem] _ _ _.

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
  (counter tp).+1.

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

Module Concur. Section Concur.

Import ThreadPool.

Context {sem : Modsem.t} (tp : ThreadPool.t sem).

Notation thread_pool := (t sem).
Notation the_ge := (Modsem.ge sem).
Notation the_sem := (Modsem.sem sem).
Notation perm_map := PermMap.t.

Variable  aggelos : nat -> perm_map.
Variable schedule : nat -> nat.

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

  | step_lock_into :
      forall tp m c b ofs,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Krun c ->
      semantics.at_external the_sem c = Some (LOCK, LOCK_SIG, Vptr b (Int.repr ofs)::nil) ->
      step tp m (updThread tp tid (Klock b ofs c)) m

  | step_lock_exec :
      forall tp m c m'' c' m' b ofs,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Klock b ofs c ->
      semantics.at_external the_sem c = Some (LOCK, LOCK_SIG, Vptr b (Int.repr ofs)::nil) ->
      Mem.load Mint32 m b ofs = Some (Vint Int.one) ->
      Mem.store Mint32 m b ofs (Vint Int.zero) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      updPermMap m'' (aggelos n) = Some m' -> 
      step tp m (updThread tp tid (Krun c')) m'

  | step_unlock :
      forall tp m c m'' c' m' b ofs,
      let: n := counter tp in
      let: tid0 := schedule n in
      forall (tid0_lt_pf :  tid0 < num_threads tp),
      let: tid := Ordinal tid0_lt_pf in
      getThread tp tid = Krun c ->
      semantics.at_external the_sem c = Some (UNLOCK, UNLOCK_SIG, Vptr b (Int.repr ofs)::nil) ->
      Mem.load Mint32 m b ofs = Some (Vint Int.zero) ->
      Mem.store Mint32 m b ofs (Vint Int.one) = Some m'' ->
      semantics.after_external the_sem (Some (Vint Int.zero)) c = Some c' ->
      updPermMap m'' (aggelos n) = Some m' -> 
      step tp m (updThread tp tid (Krun c')) m'.

End Concur. End Concur.
