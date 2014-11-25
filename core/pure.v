Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.
Require Import Axioms.
Require Import Memory.
Require Import StructuredInjections.
Require Import reach.

Definition valid_location m b ofs:= Mem.perm m b ofs Max Nonempty.

(*Parameter pure_composition: SM_Injection -> SM_Injection -> mem -> mem -> mem -> Prop.*)



Definition pure_composition_locat (j12 j23:meminj) m1 m2:=
  forall b2 b3 ofs23 delta,
         j23 b2 = Some (b3, ofs23) ->
         valid_location m2 b2 delta ->
         exists b1 ofs12,
           j12 b1 = Some (b2, ofs12) /\
           valid_location m1 b1 (delta - ofs12).
Definition pure_composition_block (j12 j23: meminj):=
  forall b2 b3 ofs23,
         j23 b2 = Some (b3, ofs23) ->
         exists b1 ofs12,
           j12 b1 = Some (b2, ofs12).

Definition pure_composition j12 j23 m1 m2 :=
  pure_composition_locat j12 j23 m1 m2 /\ pure_composition_block j12 j23.

Definition pure_comp_ext mu12 mu23 m1 m2 := pure_composition (extern_of mu12) (extern_of mu23) m1 m2 .

(*Making stuff up here: *)
(*Lemma pure_frgn: forall mu12 mu23 m1 m2 m3, 
                   SM_wd mu23 ->
                   pure_composition mu12 mu23 m1 m2 m3 ->
                   forall b',
                   frgnBlocksSrc mu23 b' = true ->
                   exists b ofs, 
                     extern_of mu12 b = Some (b', ofs) /\
                     frgnBlocksSrc mu12 b = true.
intros ? ? ? ? ? SMWD pure b' frgn.
apply pureAX in pure; destruct pure as [pure_loc pure_block].
unfold pure_composition_block in pure_block.
assert (frgn':= frgn).
apply SMWD in frgn; destruct frgn as [b2 [ofs23 [extof frgn]]].
destruct (pure_block b' b2 ofs23 extof frgn') as [b1 [ofs12 extof']].
exists b1, ofs12.
split; auto.

assert (HH:as_inj mu23 b' = Some (b2, ofs23)) by admit. (* follows from extof and SMWD*)


Admitted.*)