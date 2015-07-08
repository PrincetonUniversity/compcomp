Require Import ssreflect ssrbool ssrnat ssrfun seq eqtype fintype finfun.
Set Implicit Arguments.

Require Import cast.

Require Import Axioms Arith.

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
      in Some (thefun t idx)
    | right _ => None
  end.

Definition set (t : col) (i : nat) (x : T) :=
  match lt_dec i t.(size) with
    | left lt_pf => 
      let: idx := Ordinal (my_ltP lt_pf) 
      in mk (fun j => if idx == j then x else thefun t j)
    | right _ => t
  end.

Definition all (t : col) (p : pred T) := 
  forall i : 'I_(size t), p (thefun t i).

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
          | Some i' => thefun t i'
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
          (cast_ty (lift_eq (fun idx => 'I_idx -> T) pf) (thefun t)))
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

Arguments size {T} _ /.
Arguments empty / {T}.
Arguments get {T} _ _ /.
Arguments set {T} _ _ _ /.
Arguments push {T} _ _ /.
Arguments pop {T} _ /.
Arguments peek {T} _ /.
Arguments all {T} _ _ /.
Arguments gss {T} _ _ _ _ /. 
Arguments gso {T} _ _ _ _ _ /. 
Arguments allget {T} _ _ _ _ _ _ /.
Arguments allset {T} _ _ _ _ _ _ _ /.
Arguments pushget {T} _ _ /.
Arguments allpush {T} _ _ _ _ _ _ /.
Arguments allpeek {T} _ _ _ _ _ /.
Arguments pushpeek {T} _ _ /.

End FunCollection.

Module COL. 

Record type (T : Type) : Type := 
  { t : Type
  ; size : t -> nat
  ; empty: t
  ; get  : t -> nat -> option T
  ; set  : t -> nat -> T -> t
  ; push : t -> T -> t
  ; pop  : t -> t
  ; peek : t -> option T
  ; all  : t -> pred T -> Prop

  ; gss  : forall t i x (pf : i < size t), get (set t i x) i = Some x
  ; gso  : forall t i j x (pf : i != j), get (set t i x) j = get t j
  ; allget : forall t p i x, all t p -> get t i = Some x -> p x
  ; allset : forall t p i x, all t p -> p x -> all (set t i x) p
  ; pushget : forall t x, get (push t x) (size t) = Some x
  ; allpush : forall t p x, all t p -> p x -> all (push t x) p
  ; allpeek : forall t p x, all t p -> peek t = Some x -> p x
  ; pushpeek : forall t x, peek (push t x) = Some x
  }.

End COL.

Arguments COL.empty / {T _}.
Arguments COL.size {T _} _ /.
Arguments COL.get {T _} _ _ /.
Arguments COL.set {T _} _ _ _ /.
Arguments COL.push {T _} _ _ /.
Arguments COL.peek {T _} _ /.
Arguments COL.all {T _} _ _ /.
Arguments COL.gss {T _ _ _ _} _ /. 
Arguments COL.gso {T _ _ _ _ _} _ /. 
Arguments COL.allget {T _ _ _ _ _ _ _} /. 
Arguments COL.allset {T _ _ _ _ _ _ _} /. 
Arguments COL.pushget {T _ _ _} /. 
Arguments COL.allpush {T _ _ _ _ _ _} /. 
Arguments COL.allpeek {T _ _ _ _ _ _} /. 
Arguments COL.pushpeek {T _ _ _} /. 

Coercion COL.t : COL.type >-> Sortclass.

Module Collection.

Import FunCollection.

Section Collection.

Variable T : Type.

Definition t : COL.type T := 
  @COL.Build_type T (col T) 
    size empty get set push pop peek all 
    gss gso allget allset pushget allpush allpeek pushpeek.

End Collection.

End Collection.

Canonical Structure fun_colTy T : COL.type T := Collection.t T.
