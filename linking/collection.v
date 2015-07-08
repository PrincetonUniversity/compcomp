Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype fintype finfun.
Set Implicit Arguments.
Unset Strict Implicit.

Require Import cast.

Require Import Axioms Arith.

Definition Pred (T : Type) := T -> Prop.

Module COL. 
Record class (T t : Type) := Class 
  { size' : t -> nat
  ; empty': t
  ; get'  : t -> nat -> option T
  ; set'  : t -> nat -> T -> t
  ; push' : t -> T -> t
  ; pop'  : t -> t
  ; peek' : t -> option T
  ; all'  : t -> Pred T -> Prop

  ; _ : forall t i x (pf : i < size' t), get' (set' t i x) i = Some x
  ; _ : forall t i j x (pf : i != j), get' (set' t i x) j = get' t j
  ; _ : forall t p i x, all' t p -> get' t i = Some x -> p x
  ; _ : forall t p i x, all' t p -> p x -> all' (set' t i x) p
  ; _ : forall t x, get' (push' t x) (size' t) = Some x
  ; _ : forall t p x, all' t p -> p x -> all' (push' t x) p
  ; _ : forall t p x, all' t p -> peek' t = Some x -> p x
  ; _ : forall t x, peek' (push' t x) = Some x
  }.
Structure type := Pack { val : Type; col : Type; class_of : class val col }.
Definition size (e : type) : col e -> nat :=
  let 'Pack _ _ (Class the_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) := e 
  in the_size.
Definition empty (e : type) : col e :=
  let 'Pack _ _ (Class _ the_empty _ _ _ _ _ _ _ _ _ _ _ _ _ _) := e 
  in the_empty.
Definition get (e : type) : col e -> nat -> option (val e) :=
  let 'Pack _ _ (Class _ _ the_get _ _ _ _ _ _ _ _ _ _ _ _ _) := e 
  in the_get.
Definition set (e : type) : col e -> nat -> val e -> col e :=
  let 'Pack _ _ (Class _ _ _ the_set _ _ _ _ _ _ _ _ _ _ _ _) := e 
  in the_set.
Definition push (e : type) : col e -> val e -> col e :=
  let 'Pack _ _ (Class _ _ _ _ the_push _ _ _ _ _ _ _ _ _ _ _) := e 
  in the_push.
Definition pop (e : type) : col e -> col e :=
  let 'Pack _ _ (Class _ _ _ _ _ the_pop _ _ _ _ _ _ _ _ _ _) := e 
  in the_pop.
Definition peek (e : type) : col e -> option (val e) :=
  let 'Pack _ _ (Class _ _ _ _ _ _ the_peek _ _ _ _ _ _ _ _ _) := e 
  in the_peek.
Definition all (e : type) : col e -> Pred (val e) -> Prop :=
  let 'Pack _ _ (Class _ _ _ _ _ _ _ the_all _ _ _ _ _ _ _ _) := e 
  in the_all.
Arguments size {e} _ : simpl never.
Arguments empty {e} : simpl never.
Arguments get {e} _ _ : simpl never.
Arguments set {e} _ _ _ : simpl never.
Arguments push {e} _ _ : simpl never.
Arguments pop {e} _ : simpl never.
Arguments peek {e} _ : simpl never.
Arguments all {e} _ _ : simpl never.
Arguments Class {T} _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Module theory.
  Lemma gss (e : type) (t : col e) i x : i < size t -> get (set t i x) i = Some x. 
  Proof. rewrite/get/set; case:e t x=>/=??; case=>???????? H ?????????; apply:H. Qed.
  Lemma gso (e : type) (t : col e) i j x : i != j -> get (set t i x) j = get t j.
  Proof. rewrite/get/set; case:e t x=>/=??; case=>????????? H ????????; apply:H. Qed.
  Lemma allget (e : type) (t : col e) p i x : all t p -> get t i = Some x -> p x.
  Proof. rewrite/get/set; case:e t p x=>/=??; case=>?????????? H ????????; apply:H. Qed.
  Lemma allset (e : type) (t : col e) p i x : all t p -> p x -> all (set t i x) p.
  Proof. rewrite/get/set; case:e t p x=>/=??; case=>??????????? H ???????; apply:H. Qed.
  Lemma pushget (e : type) (t : col e) x : get (push t x) (size t) = Some x.
  Proof. rewrite/get/set; case:e t x=>/=??; case=>???????????? H ?????; apply:H. Qed.
  Lemma allpush (e : type) (t : col e) p x : all t p -> p x -> all (push t x) p.
  Proof. rewrite/get/set; case:e t p x=>/=??; case=>????????????? H ????; apply:H. Qed.
  Lemma allpeek (e : type) (t : col e) p x : all t p -> peek t = Some x -> p x.
  Proof. rewrite/get/set; case:e t p x=>/=??; case=>?????????????? H ????; apply:H. Qed.
  Lemma pushpeek (e : type) (t : col e) x : peek (push t x) = Some x.
  Proof. rewrite/get/set; case:e t x=>/=??; case=>??????????????? H ??; apply: H. Qed.
End theory.
End COL.
Import COL.theory.

Module FunCollection. Section FunCollection.
Variable T : Type.

Record col : Type := mk { 
  size  : nat;
  thefun: 'I_size -> T
}.

Lemma zero_lt_T : 'I_0 -> T.
Proof. case=> ?; discriminate. Qed.

Definition empty : col := mk [ffun pf : 'I_0 => zero_lt_T pf].

Lemma my_ltP m n : (m < n)%coq_nat -> (m < n).
Proof. by move/ltP. Qed.

Definition get (t : col) (i : nat) :=
  match lt_dec i t.(size) with
    | left lt_pf => 
      let: idx := Ordinal (my_ltP lt_pf) 
      in Some (thefun idx)
    | right _ => None
  end.

Definition set (t : col) (i : nat) (x : T) :=
  match lt_dec i t.(size) with
    | left lt_pf => 
      let: idx := Ordinal (my_ltP lt_pf) 
      in mk (fun j => if idx == j then x else thefun j)
    | right _ => t
  end.

Definition all (t : col) (p : Pred T) := 
  forall i : 'I_(size t), p (thefun i).

Lemma gss t i x (pf : i < t.(size)) : get (set t i x) i = Some x.
Proof.
rewrite /get /set; case lt_pf: (lt_dec i (size t))=> [H|H]; rewrite lt_pf.
f_equal=> /=.
by f_equal=> /=; rewrite eq_refl.
by elimtype False; move {lt_pf}; apply: H; apply/ltP.
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

Lemma lt_incr n : n < n.+1. Proof. by []. Qed.

Definition push (t : col) (x : T) :=
  let: new_size := (size t).+1 in
  let: new_idx  := Ordinal (lt_incr (size t)) in
  mk (fun i : 'I_new_size =>
        match unlift new_idx i with
          | None => x
          | Some i' => thefun i'
        end).

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

Definition pop_fun size (f : 'I_(size.+1) -> T) : 'I_size -> T :=
  fun i : 'I_size => f (lift (Ordinal (lt_incr size)) i).

Definition pop (t : col) : col :=
  (match size t as n return size t = n -> col with
    | O => fun pf => t
    | S n' => fun pf => 
        @mk n' (pop_fun 
          (cast_ty (lift_eq (fun idx => 'I_idx -> T) pf) (@thefun t)))
  end) erefl.

Lemma allpop t p : all t p -> all (pop t) p.
Proof.
rewrite /all /pop; case: t=> n f /= H.
by case H: n f H=> //[x] f H2 /= i; apply: H2.
Qed.

Definition peek (t : col) : option T :=
  match size t with
    | O   => None
    | S n => get t n
  end.

Lemma allpeek t p x : all t p -> peek t = Some x -> p x.
Proof.
rewrite /all /peek; case: t=> n f /= H.
case: n f H=> // n f H; rewrite /get /=.
by case H2: (lt_dec _ _)=> // [y]; case=> <-.
Qed.

Lemma pushpeek t x : peek (push t x) = Some x.
Proof.
rewrite /peek /push /get /=; case H: (lt_dec _ _)=> //[pf|pf].
have ->: lt_incr (size t) = my_ltP pf by apply: proof_irr.
by rewrite unlift_none.
by elimtype False; clear H; apply: pf.
Qed.

End FunCollection. 

End FunCollection.

Section FunCollectionClass.

Import FunCollection.

Variable T : Type.

Definition fun_COLcl : COL.class T (col T) := 
  COL.Class (col T) 
    (@size T) (@empty T) (@get T) (@set T) 
    (@push T) (@pop T) (@peek T) (@all T)
    (@gss T) (@gso T) (@allget T) (@allset T) 
    (@pushget T) (@allpush T) (@allpeek T) (@pushpeek T).

End FunCollectionClass.

Section test.

Canonical Structure natfun_COLty : COL.type := COL.Pack (fun_COLcl nat).

Import COL.

Lemma xx : peek (push empty 0) = Some 0.
Proof. by rewrite pushpeek. Qed.

End test.  
