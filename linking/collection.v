Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype fintype finfun tuple.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import cast.

Require Import Axioms Arith Omega.

Lemma lt_incr n : n < n.+1. Proof. by []. Qed.

Module COL. 
Record class (T t : Type) := Class 
  { size_ : t -> nat
  ; sizeinv_ : forall (r : t), 0 < size_ r 

  ; singl_: T -> t

  ; get_  : forall (r : t), 'I_(size_ r) -> T
  ; set_  : forall (r : t), 'I_(size_ r) -> T -> t
  ; setsize_ : 
      forall (r : t) (i : 'I_(size_ r)) x, 
      size_ r = size_ (@set_ r i x)
  ; gss_ : 
      forall (r : t) (i : 'I_(size_ r)) x, 
      @get_ (@set_ r i x) (cast_ord (setsize_ i x) i) = x
  ; gso_ : forall (r : t) (i j : 'I_(size_ r)) x, 
      i != j ->       
      @get_ (@set_ r i x) (cast_ord (setsize_ i x) j) = @get_ r j

  ; bump_ : t -> T -> t
  ; bumpoldord_ : forall (r : t) (i : 'I_(size_ r)) x, 'I_(size_ (bump_ r x))
  ; bumpneword_ : forall (r : t) x, 'I_(size_ (bump_ r x))
  ; bumpneword_charact_ : 
      forall (r : t) x, nat_of_ord (bumpneword_ r x) = size_ r
  ; bumpsize_ : forall (r : t) x, size_ (bump_ r x) = (size_ r).+1
  ; bumpgetold_ :
      forall (r : t) (i : 'I_(size_ r)) x, 
      @get_ (bump_ r x) (bumpoldord_ i x) = @get_ r i
  ; bumpgetnew_ : forall (r : t) x, @get_ (bump_ r x) (bumpneword_ r x) = x
  ; unbump_ : forall (r : t), 1 < size_ r -> t
  ; unbumpsize_ :
      forall (r : t) (pf : 1 < size_ r), 
      size_ (@unbump_ r pf) = (size_ r).-1

  ; all_  : t -> pred T -> bool
  ; allget_ : 
      forall (r : t) (i : 'I_(size_ r)) p, 
      all_ r p -> p (get_ i)
  ; allset_ : 
      forall (r : t) (i : 'I_(size_ r)) p x,
      all_ r p -> p x -> all_ (set_ i x) p 
  ; allbump_ : 
      forall (r : t) p x, 
      all_ r p -> p x -> all_ (bump_ r x) p
  ; allunbump_ : 
      forall (r : t) p (pf : 1 < size_ r), 
      all_ r p -> all_ (@unbump_ r pf) p
  }.
Structure type := Pack { val : Type; col : Type; class_of : class val col }.
Definition size (e : type) : col e -> nat :=
  let 'Pack _ _ r0 := e in size_ r0.
Definition sizeinv (e : type) : forall (r : col e), 0 < size r :=
  let 'Pack _ _ r0 := e in sizeinv_ r0.
Definition singl (e : type) : val e -> col e :=
  let 'Pack _ _ r0 := e in singl_ r0.
Definition get (e : type) : forall (r : col e), 'I_(size r) -> val e :=
  let 'Pack _ _ r0 := e in @get_ _ _ r0.
Definition set (e : type) : forall (r : col e), 'I_(size r) -> val e -> col e :=
  let 'Pack _ _ r0 := e in @set_ _ _ r0.
Definition setsize (e : type) : 
  forall (r : col e) (i : 'I_(size r)) x, size r = size (set i x) :=
  let 'Pack _ _ r0 := e in @setsize_ _ _ r0.
Definition bump (e : type) : col e -> val e -> col e :=
  let 'Pack _ _ r0 := e in bump_ r0.
Definition bumpoldord (e : type) : 
  forall r : col e, 'I_(size r) -> forall x : val e, 'I_(size (bump r x)) :=
  let 'Pack _ _ r0 := e in @bumpoldord_ _ _ r0.
Definition bumpneword (e : type) : 
  forall (r : col e) (x : val e), 'I_(size (bump r x)) :=
  let 'Pack _ _ r0 := e in @bumpneword_ _ _ r0.
Definition bumpneword_charact (e : type) : 
  forall (r : col e) (x : val e), 
  nat_of_ord (bumpneword r x) = size r :=
  let 'Pack _ _ r0 := e in @bumpneword_charact_ _ _ r0.
Definition unbump (e : type) (r : col e) (pf : 1 < @size_ _ _ (class_of e) r) 
  : col e := unbump_ pf.
Definition all (e : type) : col e -> pred (val e) -> bool :=
  let 'Pack _ _ r := e in all_ r.
Arguments size {e} _ : simpl never.
Arguments sizeinv {e} _ : simpl never.
Arguments singl {e} _ : simpl never.
Arguments get {e} _ _ : simpl never.
Arguments set {e} _ _ _ : simpl never.
Arguments setsize {e} _ _ _ : simpl never.
Arguments bump {e} _ _ : simpl never.
Arguments bumpoldord {e} _ _ _ : simpl never.
Arguments bumpneword {e} _ _ : simpl never.
Arguments bumpneword_charact {e} _ _ : simpl never.
Arguments unbump {e} _ _ : simpl never.
Arguments all {e} _ _ : simpl never.
Arguments Class {T} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Module theory.
  Lemma gss e (r : col e) i x : 
    get (set r i x) (cast_ord (setsize r i x) i) = x.
  Proof. move: r i x; refine (let 'Pack _ _ r := e in _)=> /= r0 i x.
         apply: (@gss_ _ _ r r0 i x). Qed.
  Lemma gso e (r : col e) i j x : 
    i != j -> 
    get (set r i x) (cast_ord (setsize r i x) j) = get r j.
  Proof. move: r i j x; refine (let 'Pack _ _ r := e in _)=> /= r0 i j x.
         apply: (@gso_ _ _ r r0 i j x). Qed.

  Lemma bumpsize e (r : col e) x : size (bump r x) = (size r).+1.
  Proof. move: r x; refine (let 'Pack _ _ r := e in _)=> /= r0 x.
         apply: (@bumpsize_ _ _ r r0 x). Qed.
  Lemma bumpgetold e (r : col e) x i : 
    get (bump r x) (bumpoldord r i x) = get r i.
  Proof. move: r x i; refine (let 'Pack _ _ r := e in _)=> /= r0 x i.
         apply: (@bumpgetold_ _ _ r r0 i). Qed.
  Lemma bumpgetnew e (r : col e) x : get (bump r x) (bumpneword r x) = x.
  Proof. move: r x; refine (let 'Pack _ _ r := e in _)=> /= r0 x.
         apply: (@bumpgetnew_ _ _ r r0 x). Qed.
  Lemma unbumpsize e (r : col e) pf : size (unbump r pf) = (size r).-1.
  Proof. move: r pf; refine (let 'Pack _ _ r := e in _)=> /= r0 pf.
         apply: (@unbumpsize_ _ _ r r0 pf). Qed.

  Lemma allget e (r : col e) p i : all r p -> p (get r i).
  Proof. move: r p i; refine (let 'Pack _ _ r := e in _)=> /= r0 p i.
         apply: (@allget_ _ _ r r0 i). Qed.
  Lemma allset e (r : col e) (p : pred (val e)) i x : 
    all r p -> p x -> all (set r i x) p.
  Proof. move: r p i x; refine (let 'Pack _ _ r := e in _)=> /= r0 p i x.
         apply: (@allset_ _ _ r r0 i p x). Qed.
  Lemma allbump e (r : col e) p x : all r p -> p x -> all (bump r x) p.
  Proof. move: r p x; refine (let 'Pack _ _ r := e in _)=> /= r0 p x.
         apply: (@allbump_ _ _ r r0 p x). Qed.
  Lemma allunbump e (r : col e) p pf : all r p -> all (unbump r pf) p.
  Proof. move: r p pf; refine (let 'Pack _ _ r := e in _)=> /= r0 p pf.
         apply: (@allunbump_ _ _ r r0 p pf). Qed.

  (* derived operations *)

  Lemma lastord (e : type) (r : col e) : {i : 'I_(size r) | i.+1 = size r}.
  Proof.
    move: (sizeinv r)=> lt0.
    have ltpf : (size r).-1 < size r by case: (size r) lt0.
    by exists (Ordinal ltpf)=> /=; rewrite prednK.
  Qed.

  Definition peek (e : type) (r : col e) : val e := get r (projT1 (lastord r)).

  Lemma pushpeek (e : type) (r : col e) x : peek (bump r x) = x.
  Proof. 
    rewrite /peek. 
    case: (lastord (e:=e) (bump r x))=> /= x0 H.
    have H2: x0 = bumpneword r x.
    { suff: nat_of_ord x0 = nat_of_ord (bumpneword r x); 
        first by apply: ord_inj.
      rewrite (bumpneword_charact r x).
      by move: x0 H; rewrite bumpsize=> x0; case. }
    by subst x0; rewrite bumpgetnew.
  Qed.
End theory.
End COL.
Import COL.theory.

Module FunCollection. Section FunCollection.
Variable T : Type.

Record col : Type := mk { 
  size  : nat;
  sizeinv : 0 < size;
  thefun: size.-tuple T
}.

Program Definition singl (v : T) : col := mk _ [tuple v].

Definition get (r : col) (i : 'I_(size r)) := tnth (thefun r) i.

Program Definition set (r : col) (i : 'I_(size r)) (v : T) :=
  mk _ [tuple (if i0 == i then v else tnth (thefun r) i0) | i0 < size r].
Next Obligation. by move {i}; case: r. Qed.

Lemma setsize r (i : 'I_(size r)) x : size r = size (set i x).
Proof. by []. Qed.

Lemma gss r (i : 'I_(size r)) x : get (cast_ord (setsize i x) i) = x.
Proof. by rewrite /get /= tnth_mktuple cast_ord_id eq_refl. Qed.

Lemma gso r (i j : 'I_(size r)) x : 
  i != j -> get (cast_ord (setsize i x) j) = get j.
Proof.
rewrite /get /= tnth_mktuple cast_ord_id; case H: (j == i)=> //.
by rewrite eq_sym in H; rewrite H.
Qed.

Program Definition bump (r : col) (v : T) := 
  let: new_size := (size r).+1 in
  let: new_idx  := Ordinal (lt_incr (size r)) in
  mk _ [ tuple (match unlift new_idx i with
                  | None => v
                  | Some i' => tnth (thefun r) i'
                end)
       | i < new_size ].

Program Definition bumpoldord r (i : 'I_(size r)) (v : T) : 
  'I_(size (bump r v)) :=
  @widen_ord (size r) (size (bump r v)) _ i.

Definition bumpneword r (v : T) : 'I_(size (bump r v)) :=  ord_max.

Lemma bumpneword_charact r x : nat_of_ord (bumpneword r x) = size r.
Proof. by []. Qed.

Lemma bumpsize r x : size (bump r x) = (size r).+1.
Proof. by []. Qed.

Lemma bumpgetold r (i : 'I_(size r)) v : get (bumpoldord i v) = get i.
Proof. 
rewrite /get /bumpoldord tnth_mktuple /=.
case: (unliftP 
  (Ordinal (n:=(size r).+1) (m:=size r) (lt_incr (size r)))
  (widen_ord (m:=(size r).+1) (bumpoldord_obligation_1 (r:=r) i v) i)).
{ rewrite /widen_ord /lift /= => j; case=> H.
  have ->: i = j.
  { apply: ord_inj; rewrite H /fintype.bump /nat_of_bool.
    by have ->: (size r <= j) = false
    by move {H}; case: j=> /= m /ltP=> H; apply/leP; omega.
  } by [].
}
rewrite /widen_ord; case; case: i=> m H /= H2.
by elimtype False; subst; move: (ltP H)=> H2; omega.
Qed.

Lemma bumpgetnew r x : get (bumpneword r x) = x.
Proof.
rewrite /get /bumpneword /bump /= tnth_mktuple.
case: (unliftP 
  (Ordinal (n:=(size r).+1) (m:=size r) (lt_incr (size r))) ord_max)=> //.
move=> /= j; case; rewrite /fintype.bump /nat_of_bool.
have H: (size r <= j) = false
by case: j=> /= m /ltP=> H; apply/leP; omega.
rewrite H=> H2; elimtype False; rewrite /addn /= in H2.
by move: H; case: j H2=> m pf; case: r pf=> /= size0 H _ H2 ->; move/leP.
Qed.

Program Definition unbump (r : col) (pf : 1 < size r) :=
  mk _ [ tuple (tnth (thefun r) (lift (@ord_max (size r).-1) i)) 
       | i < (size r).-1 ].
Next Obligation. move: (ltP pf)=> H; apply/ltP; omega. Qed.
Next Obligation. 
rewrite prednK=> //; last by apply/ltP; move: (ltP pf)=> H; omega.
Qed.

Lemma unbumpsize (r : col) (pf : 1 < size r) : size (unbump pf) = (size r).-1.
Proof. by []. Qed.

Definition all (r : col) (p : pred T) : bool := all p (thefun r).

Lemma allget r (i : 'I_(size r)) p : all r p -> p (get i).
Proof. by rewrite /all /get /= -forallb_tnth => /forallP/(_ i). Qed.

Lemma allset r (i : 'I_(size r)) p x : all r p -> p x -> all (set i x) p.
Proof.
rewrite /all /set -forallb_tnth=> /forallP=> H H2.
apply/all_tnthP; rewrite /= => i0; rewrite tnth_mktuple.
by case H3: (i0 == i).
Qed.

Lemma allbump r p x : all r p -> p x -> all (bump r x) p.
Proof.
rewrite /all /bump -forallb_tnth=> /forallP=> H H2.
apply/all_tnthP; rewrite /= => i0; rewrite tnth_mktuple.
by case H3: (unlift _ _).
Qed.

Lemma allunbump r p (pf : 1 < size r) : all r p -> all (unbump pf) p.
Proof.
rewrite /all /unbump -forallb_tnth=> /forallP=> H.
apply/all_tnthP; rewrite /= => i0; rewrite tnth_mktuple.
by case H3: (lift _ _).
Qed.

End FunCollection. 

End FunCollection.

Section FunCollectionClass.

Import FunCollection.

Variable T : Type.

Definition fun_COLcl : COL.class T (col T) := 
  COL.Class (col T) 
    (@size T) (@sizeinv T) (@singl T) (@get T) (@set T) 
    (@setsize T) (@gss T) (@gso T) 
    (@bump T) (@bumpoldord T) (@bumpneword T) (@bumpneword_charact T)
    (@bumpsize T) (@bumpgetold T) (@bumpgetnew T) 
    (@unbump T) (@unbumpsize T) 
    (@all T) (@allget T) (@allset T) (@allbump T) (@allunbump T).

End FunCollectionClass.

Canonical Structure fun_COLty (T : Type) : COL.type := 
  COL.Pack (fun_COLcl T).

Notation "[ 'collection' aTy ]" := (COL.col (fun_COLty aTy)).

Section test.

Import COL.

Lemma xx : peek (bump (singl 0) 0) = 0.
Proof. by rewrite pushpeek. Qed.

End test.  
