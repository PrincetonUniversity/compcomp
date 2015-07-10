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
      @get_ (@set_ r i x) (cast_ord (setsize_ i x) j) = 
      @get_ r j

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
  Lemma gss e (r : col e) i x : get (set r i x) (cast_ord (setsize r i x) i) = x.
  Proof. move: r i x; refine (let 'Pack _ _ r := e in _)=> /= r0 i x.
         apply: (@gss_ _ _ r r0 i x). Qed.
  Lemma gso e (r : col e) i j x : 
    get (set r i x) (cast_ord (setsize r i x) j) =
    get r j.
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
    { suff: nat_of_ord x0 = nat_of_ord (bumpneword r x); first by apply: ord_inj.
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

Definition singl : col := mk [tuple].

Definition get (t : col) (i : 'I_(size t)) :=


Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
Proof. by move/ltP. Qed.

Definition get (t : col) (i : nat) :=
  match lt_dec i t.(size) with
    | left lt_pf => 
      let: idx := Ordinal (my_ltP lt_pf) 
      in Some (thefun _ idx)
    | right _ => None
  end.

Definition set (t : col) (i : nat) (x : T) :=
  match lt_dec i t.(size) with
    | left lt_pf => 
      let: idx := Ordinal (my_ltP lt_pf) 
      in mk (finfun (fun j => if idx == j then x else thefun _ j))
    | right _ => t
  end.

Definition all (t : col) (p : pred T) := 
 [forall i : 'I_(size t), p (thefun _ i)].

Lemma gss t i x (pf : i < t.(size)) : get (set t i x) i = Some x.
Proof.
rewrite /get /set; case lt_pf: (lt_dec i (size t))=> [H|H]; rewrite lt_pf /=.
2: by elimtype False; move {lt_pf}; apply: H; apply/ltP.
f_equal. 

by f_equal=> /=; rewrite eq_refl.
Qed.

Lemma gso t i j x (pf : i != j) : get (set t i x) j = get t j.
Proof.
rewrite /get /set. 
case lt_pf: (lt_dec i (size t))=> [/=H|H]. 
case lt_pf':(lt_dec j (size t))=> [H1|//]. 
f_equal.
have H2: (Ordinal (my_ltP H) == Ordinal (my_ltP H1) = false).
{ by apply/eqP; case=> pf'; rewrite pf' eq_refl in pf. }
by rewrite H2.
by case lt_pf':(lt_dec j (size t)).
Qed.

Lemma allget t p i x : all t p -> get t i = Some x -> p x.
Proof.
rewrite /all /get=> H; case pf: (lt_dec _ _)=> [H2|H2]; last by discriminate.
by case=> <-; apply: H.
Qed.

Lemma allset t p i x : all t p -> p x -> all (set t i x) p.
Proof.
rewrite /all /set=> H; case pf: (lt_dec _ _)=> [H2|//].
by move=> H3 /= i0; case: (_ == _).
Qed.

Definition push (t : col) (x : T) :=
  let: new_size := (size t).+1 in
  let: new_idx  := Ordinal (lt_incr (size t)) in
  mk (fun i : 'I_new_size =>
        match unlift new_idx i with
          | None => x
          | Some i' => thefun i'
        end).

Definition pop_fun size (f : 'I_(size.+1) -> T) : 'I_size -> T :=
  fun i : 'I_size => f (lift (Ordinal (lt_incr size)) i).

Definition pop (t : col) : col :=
  (match size t as n return size t = n -> col with
    | O => fun pf => t
    | S n' => fun pf => 
        @mk n' (pop_fun 
          (cast_ty (lift_eq (fun idx => 'I_idx -> T) pf) (@thefun t)))
  end) erefl.

Lemma pushpop t x : pop (push t x) = t.
Proof.
rewrite /pop /push /=; case: t=> //= y z.
rewrite /pop_fun cast_ty_erefl; f_equal; extensionality i.
by rewrite liftK.
Qed.

Lemma pushget t x : get (push t x) t.(size) = Some x.
Proof.
rewrite /get /push /=.
case: (lt_dec _ _)=> //.
{ move=> lt_pf /=. 
  have ->: lt_incr (size t) = my_ltP lt_pf by apply: proof_irr.
  by rewrite unlift_none.
}
by move=> Contra; elimtype False; apply: Contra.
Qed.

Lemma allpush t p x : all t p -> p x -> all (push t x) p.
Proof.
by rewrite /all /push /= => H H2 i0; case: (unlift _ _).
Qed.

Lemma allpop t p : all t p -> all (pop t) p.
Proof.
rewrite /all /pop; case: t=> n f /= H.
by case H: n f H=> //[x] f H2 /= i; apply: H2.
Qed.

Lemma getsize t i x : get t i = Some x -> size t > 0.
Proof. 
rewrite /get; case: (lt_dec _ _)=> // H; case=> _.
elim: i H; first by apply: my_ltP.
by move=> n IH H; apply: IH; omega.
Qed.

Lemma getsize' t i : size t > i -> isSome (get t i).
Proof. 
rewrite /get; case: (lt_dec _ _)=> // H H2.
by elimtype False; apply: H; apply/ltP.
Qed.

Lemma pushsize t x : size (push t x) = (size t).+1.
Proof. by []. Qed.

Lemma popsize t : size t > 0 -> (size (pop t)).+1 = size t.
Proof. 
rewrite /pop /pop_fun; case: t=> s t /=; destruct s; first by discriminate.
by simpl.
Qed.

End FunCollection. 

End FunCollection.

Section FunCollectionClass.

Import FunCollection.

Variable T : Type.

Definition fun_COLcl : COL.class T (col T) := 
  COL.Class (col T) 
    (@size T) (@empty T) (@get T) (@set T) 
    (@push T) (@pop T) (@all T)
    (@gss T) (@gso T) (@allget T) (@allset T)  (@allpush T) (@allpop T)
    (@pushpop T) (@pushget T) (@getsize T) (@getsize' T) 
    (@pushsize T) (@popsize T).

End FunCollectionClass.

Canonical Structure fun_COLty (T : Type) : COL.type := 
  COL.Pack (fun_COLcl T).

Notation "[ 'collection' aTy ]" := (COL.col (fun_COLty aTy)).

Section test.

Import COL.

Lemma xx : peek (push empty 0) = Some 0.
Proof. by rewrite pushpeek. Qed.

End test.  
