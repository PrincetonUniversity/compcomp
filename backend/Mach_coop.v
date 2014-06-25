Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Events.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import Conventions.
Require Stacklayout.

Require Import Mach. 
Require Import Stacking.

Require Import mem_lemmas. (*for mem_forward*)
Require Import core_semantics.
Require Import val_casted.
Require Import BuiltinEffects.

Definition genv := Genv.t fundef unit.

Notation "a ## b" := (List.map a b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)       (**r pointer to argument frame *)
           (args: list val)  (**r initial program arguments *)
           (tys: list typ),  (**r initial argument types *)
    load_frame.

Section MACH_COOPSEM.
Variable hf : I64Helpers.helper_functions.

Variable return_address_offset: function -> code -> int -> Prop.

Inductive Mach_core: Type :=
  | Mach_State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (loader: load_frame),     (**r program loader frame *)
      Mach_core

  | Mach_Callstate:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (loader: load_frame),     (**r program loader frame *)
      Mach_core

  (*Auxiliary state: for marshalling arguments INTO memory*)
  | Mach_CallstateIn: 
      forall (f: block)                (**r pointer to function to call *)
             (args: list val)          (**r arguments passed to initial_core *)
             (tys: list typ),          (**r argument types *)
      Mach_core

  (*Auxiliary state: for marshalling arguments OUT OF memory*)
  | Mach_CallstateOut: 
      forall (stack: list stackframe)  (**r call stack *)
             (b: block)                (**r global block address of the external 
                                            function to be called*)
             (f: external_function)    (**r external function to be called *)
             (vals: list val)          (**r at_external arguments *)
             (rs: regset)              (**r register state *)
             (loader: load_frame),     (**r program loader frame *)
      Mach_core

  | Mach_Returnstate:
      forall (stack: list stackframe)  (**r call stack *)
             (retty: option typ)       (**r optional return register int-floatness *)
             (rs: regset)              (**r register state *)
             (loader: load_frame),     (**r program loader frame *)
      Mach_core.

(*NOTE [store_args_simple] is used to model program loading of
  initial arguments.  Cf. NOTE [loader] below. *)

Fixpoint store_args0 (m: mem) (sp: val) (ofs: Z) (args: list val) (tys: list typ) 
         : option mem :=
  match args,tys with
    | nil,nil => Some m
    | a::args',ty::tys' => 
      match store_stack m sp ty (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) a with
        | None => None
        | Some m' => store_args0 m' sp (ofs+typesize ty) args' tys'
      end
    | _,_ => None
  end.

(* [store_args_rec] is more complicated, but more precise than, 
   [store_args (encode_longs args) (encode_typs tys)]. Still, it's not totally
   satisfactory that argument encoding code is duplicated like this. *)

Fixpoint store_args_rec m sp ofs args tys : option mem :=
  let vsp := Vptr sp Int.zero in
  match tys, args with
    | nil, nil => Some m
    | ty'::tys',a'::args' => 
      match ty', a' with 
        | Tlong, Vlong n => 
          match store_stack m vsp Tint (Int.repr (Stacklayout.fe_ofs_arg + 4*(ofs+1))) 
                            (Vint (Int64.hiword n)) with
            | None => None
            | Some m' => 
              match store_stack m' vsp Tint (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) 
                                (Vint (Int64.loword n)) with
                | None => None
                | Some m'' => store_args_rec m'' sp (ofs+2) args' tys' 
              end
          end
        | Tlong, _ => None
        | _,_ => 
          match store_stack m vsp ty' (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) a' with
            | None => None
            | Some m' => store_args_rec m' sp (ofs+typesize ty') args' tys' 
          end
      end
    | _, _ => None
  end.

(*Fixpoint encode_longs' (tyl : list typ) (vl : list val) {struct tyl} : list val :=
  match tyl with
  | nil => nil
  | Tint :: tyl' =>
      match vl with
      | nil => nil
      | v :: vl' => v :: encode_longs' tyl' vl'
      end
  | Tfloat :: tyl' =>
      match vl with
      | nil => nil
      | v :: vl' => v :: encode_longs' tyl' vl'
      end
  | Tlong :: tyl' =>
      match vl with
      | nil => nil
      | Vundef :: vl' => Vundef :: Vundef :: encode_longs' tyl' vl'
      | Vint _ :: vl' => Vundef :: Vundef :: encode_longs' tyl' vl'
      | Vlong n :: vl' =>
          Vint (Int64.loword n)
          :: Vint (Int64.hiword n) :: encode_longs' tyl' vl'
      | Vfloat _ :: vl' => Vundef :: Vundef :: encode_longs' tyl' vl'
      | Vptr _ _ :: vl' => Vundef :: Vundef :: encode_longs' tyl' vl'
      end
  | Tsingle :: tyl' =>
      match vl with
      | nil => nil
      | v :: vl' => v :: encode_longs' tyl' vl'
      end
  end.
*)

(*Lemma store_args_store_args_rec m stk ofs args tys m' : 
  vals_defined args=true ->
  val_has_type_list_func args tys=true -> 
  store_args0 m (Vptr stk Int.zero) ofs 
                (encode_longs tys args) (encode_typs tys) = Some m' ->
  exists m'', store_args_rec m stk ofs args tys = Some m''.
Proof.
revert args ofs m. induction tys. destruct args; simpl; auto. intros; congruence. 
destruct args. simpl; intros; congruence. 
simpl. intros ofs m. rewrite andb_true_iff. intros DEF [A B]. destruct a.
- simpl. generalize (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                             | Z.neg y' => Z.neg y'~0~0 end) as z.
intros z. case_eq (store_stack m (Vptr stk Int.zero) Tint z v).
2: intros; congruence.
intros m0 STORE. intros. apply IHtys; auto. destruct v; auto. congruence.
- simpl. generalize (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                             | Z.neg y' => Z.neg y'~0~0 end) as z.
intros z. case_eq (store_stack m (Vptr stk Int.zero) Tfloat z v).
2: intros; congruence.
intros m0 STORE. intros. apply IHtys; auto. destruct v; auto. congruence.
- simpl. rewrite <-val_has_type_funcP in A. 
destruct v; try solve[congruence|inv A]. simpl.
generalize (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                             | Z.neg y' => Z.neg y'~0~0 end) as z.
generalize (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                             | Z.neg y' => Z.neg y'~0~0 end) as z'.
intros z' z. 
case_eq (store_stack m (Vptr stk Int.zero) Tint z' (Vint (Int64.hiword i))).
intros m0 STORE.
case_eq (store_stack m0 (Vptr stk Int.zero) Tint z (Vint (Int64.loword i))).
intros m1 STORE'.

case_eq (store_stack m (Vptr stk Int.zero) Tint z (Vint (Int64.loword i))).
intros m0' STORE''. 
case_eq (store_stack m0' (Vptr stk Int.zero) Tint z' (Vint (Int64.hiword i))).
intros m1' STORE'''.
assert (m1' = m1) as ->. 
assert (ofs+1+1 = ofs+2) as -> by omega. 
rewrite IHtys; auto. split; auto. *)

Lemma store_stack_fwd m sp t i a m' :
  store_stack m sp t i a = Some m' -> 
  mem_forward m m'.
Proof.
unfold store_stack, Mem.storev.
destruct (Val.add sp (Vint i)); try solve[inversion 1].
apply store_forward.
Qed.

Lemma store_args_fwd sp ofs args tys m m' :
  store_args_rec m sp ofs args tys = Some m' -> 
  mem_forward m m'.
Proof.
revert args ofs m; induction tys.
simpl. destruct args. intros ofs. inversion 1; subst. 
solve[apply mem_forward_refl].
intros ofs m. simpl. inversion 1. 
destruct args; try solve[inversion 1]. 
destruct a; simpl; intros ofs m. 
- case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence. 
- case_eq (store_stack m (Vptr sp Int.zero) Tfloat
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.
- destruct v; try solve[congruence].
case_eq (store_stack m (Vptr sp Int.zero) Tint
           (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                      | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.hiword i))).
intros m0 EQ. apply store_stack_fwd in EQ. 
case_eq (store_stack m0 (Vptr sp Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end)
        (Vint (Int64.loword i))). intros m1 H H2.
eapply mem_forward_trans; eauto. 
eapply mem_forward_trans; eauto. 
eapply store_stack_fwd; eauto. intros; congruence. intros; congruence.
- case_eq (store_stack m (Vptr sp Int.zero) Tsingle
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. apply store_stack_fwd in EQ. intros H.
eapply mem_forward_trans; eauto. intros; congruence.
Qed.

Lemma store_stack_unch_on stk z t i a m m' :
  store_stack m (Vptr stk z) t i a = Some m' ->
  Mem.unchanged_on (fun b ofs => b<>stk) m m'.
Proof.
unfold store_stack, Mem.storev. 
case_eq (Val.add (Vptr stk z) (Vint i)); try solve[inversion 1].
intros b i0 H H2. eapply Mem.store_unchanged_on in H2; eauto.
intros i2 H3 H4. inv H. apply H4; auto.
Qed.

Lemma store_args_unch_on stk ofs args tys m m' :
  store_args_rec m stk ofs args tys = Some m' -> 
  Mem.unchanged_on (fun b ofs => b<>stk) m m'.
Proof.
revert args ofs m; induction tys.
simpl. destruct args. intros ofs. inversion 1; subst. 
  solve[apply Mem.unchanged_on_refl].
intros ofs m. simpl. inversion 1. 
destruct args; try solve[inversion 1]. 
destruct a; simpl; intros ofs m. 
- case_eq (store_stack m (Vptr stk Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H. 
eapply unchanged_on_trans with (m2 := m0); eauto. 
solve[eapply store_stack_fwd; eauto]. intros; congruence.
- case_eq (store_stack m (Vptr stk Int.zero) Tfloat
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H. 
eapply unchanged_on_trans with (m2 := m0); eauto. 
solve[eapply store_stack_fwd; eauto]. intros; congruence.
- destruct v; try solve[inversion 1].
case_eq (store_stack m (Vptr stk Int.zero) Tint
           (Int.repr match ofs+1 with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                      | Z.neg y' => Z.neg y'~0~0 end) 
        (Vint (Int64.hiword i))).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. 
case_eq (store_stack m0 (Vptr stk Int.zero) Tint
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) 
        (Vint (Int64.loword i))).
intros m1 EQ2. generalize EQ2 as EQ2'. intro. apply store_stack_unch_on in EQ2. intros H.
eapply unchanged_on_trans with (m2 := m0); eauto. 
eapply unchanged_on_trans with (m2 := m1); eauto. 
eapply store_stack_fwd; eauto. eapply store_stack_fwd; eauto.
intros; congruence. intros; congruence.
- case_eq (store_stack m (Vptr stk Int.zero) Tsingle
           (Int.repr match ofs with | 0 => 0 | Z.pos y' => Z.pos y'~0~0
                                    | Z.neg y' => Z.neg y'~0~0 end) v).
intros m0 EQ. generalize EQ as EQ'. intro. apply store_stack_unch_on in EQ. intros H. 
eapply unchanged_on_trans with (m2 := m0); eauto. 
solve[eapply store_stack_fwd; eauto]. intros; congruence.
Qed.

Fixpoint args_len_rec args tys : option Z :=
  match tys, args with
    | nil, nil => Some 0
    | ty'::tys',a'::args' => 
      match ty', a' with 
        | Tlong, Vlong n => 
          match args_len_rec args' tys' with
            | None => None
            | Some z => Some (2+z)
          end
        | Tlong, _ => None
        | _,_ => 
          match args_len_rec args' tys' with
            | None => None
            | Some z => Some (1+z)
          end
      end
    | _, _ => None
  end.

Lemma args_len_rec_succeeds args tys 
      (VALSDEF: val_casted.vals_defined args=true)
      (HASTY: Val.has_type_list args tys) : 
  exists z, args_len_rec args tys = Some z.
Proof.
rewrite val_casted.val_has_type_list_func_charact in HASTY.
revert args VALSDEF HASTY; induction tys. destruct args; auto. 
simpl. exists 0; auto. simpl. intros; congruence.
destruct args. simpl. intros; congruence. 
unfold val_has_type_list_func; rewrite andb_true_iff. intros VD [H H2].
fold val_has_type_list_func in H2. 
apply IHtys in H2. destruct H2 as [z H2]. simpl.
destruct a; try solve [rewrite H2; eexists; eauto].
destruct v; simpl in H; try solve [simpl in VD; congruence].
rewrite H2. eexists; eauto.
simpl in VD. destruct v; auto. congruence.
Qed.

Lemma range_perm_shift m b lo sz n k p :
  0 <= lo -> 0 <= sz -> 0 <= n -> 
  Mem.range_perm m b lo (lo+sz+n) k p -> 
  Mem.range_perm m b (lo+n) (lo+sz+n) k p.
Proof. intros A B C RNG ofs [H H2]; apply RNG; omega. Qed.

Inductive only_stores (sp: block) : mem -> mem -> Type :=
| only_stores_nil m : only_stores sp m m
| only_stores_cons m ch ofs v m'' m' : 
    Mem.store ch m sp ofs v = Some m'' -> 
    only_stores sp m'' m' -> 
    only_stores sp m m'.

Lemma only_stores_fwd sp m m' : 
  only_stores sp m m' -> mem_forward m m'.
Proof.
induction 1. apply mem_forward_refl. 
eapply mem_forward_trans. eapply store_forward; eauto. apply IHX.
Qed.

Lemma store_args_rec_only_stores m sp args tys z m' :
  store_args_rec m sp z args tys = Some m' -> 
  only_stores sp m m'.
Proof.
revert args z m. induction tys. destruct args; simpl.
intros ? ?; inversion 1. constructor.
intros ? ? ?; congruence.
destruct args; simpl. intros; congruence. intros z m. 
generalize
 (Int.repr match z with
             | 0 => 0 | Z.pos y' => Z.pos y'~0~0
             | Z.neg y' => Z.neg y'~0~0 end) as z'.
generalize
 (Int.repr match z+1 with
             | 0 => 0 | Z.pos y' => Z.pos y'~0~0
             | Z.neg y' => Z.neg y'~0~0 end) as z''.
intros z'' z'. destruct a.
- case_eq (store_stack m (Vptr sp Int.zero) Tint z' v); 
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H. 
solve[eapply only_stores_cons; eauto].
- case_eq (store_stack m (Vptr sp Int.zero) Tfloat z' v); 
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H. 
solve[eapply only_stores_cons; eauto].
- destruct v; try solve[intros; congruence].
case_eq (store_stack m (Vptr sp Int.zero) Tint z'' (Vint (Int64.hiword i))); 
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE.
case_eq (Mem.store Mint32 m0 sp (Int.unsigned (Int.add Int.zero z'))
                   (Vint (Int64.loword i)));
  try solve[intros; congruence].
intros m1 STORE' H.
eapply only_stores_cons; eauto.
eapply only_stores_cons; eauto.
- case_eq (store_stack m (Vptr sp Int.zero) Tsingle z' v); 
  try solve[intros; congruence].
unfold store_stack, Mem.storev. simpl. intros m0 STORE H. 
solve[eapply only_stores_cons; eauto].
Qed.

Lemma args_len_recD: forall v args tp tys sz,
     args_len_rec (v :: args) (tp :: tys) = Some sz ->
     exists z1 z2, sz = z1+z2 /\ args_len_rec args tys = Some z2 /\
        match tp with Tlong => z1=2 | _ => z1=1 end.
Proof.
simpl. intros. 
destruct tp; simpl in *. 
destruct (args_len_rec args tys); inv H. 
  exists 1, z; repeat split; trivial.
destruct (args_len_rec args tys); inv H. 
  exists 1, z; repeat split; trivial.
destruct v; inv H.
  destruct (args_len_rec args tys); inv H1. 
  exists 2, z; repeat split; trivial.
destruct (args_len_rec args tys); inv H. 
  exists 1, z; repeat split; trivial.
Qed. 

Lemma args_len_rec_nonneg: forall tys args sz,
     args_len_rec args tys = Some sz -> 0 <= sz.
Proof.
intros tys; induction tys; intros. 
  destruct args; inv H. omega. 
destruct args; inv H. 
  destruct a; specialize (IHtys args).
  destruct (args_len_rec args tys); inv H1. 
    specialize (IHtys _ (eq_refl _)). 
    destruct z. omega. destruct p; xomega. 
    xomega. 
  destruct (args_len_rec args tys); inv H1. 
    specialize (IHtys _ (eq_refl _)). 
    destruct z. omega. destruct p; xomega. 
    xomega. 
  destruct v; inv H1. 
    destruct (args_len_rec args tys); inv H0. 
    specialize (IHtys _ (eq_refl _)). 
    destruct z. omega. destruct p; xomega. 
    xomega. 
  destruct (args_len_rec args tys); inv H1. 
    specialize (IHtys _ (eq_refl _)). 
    destruct z. omega. destruct p; xomega. 
    xomega. 
Qed.

Lemma args_len_rec_pos: forall v args tp tys sz,
     args_len_rec (v :: args) (tp :: tys) = Some sz -> 0 < sz.
Proof. intros.
apply args_len_recD in H. destruct H as [? [? [? [? ?]]]]; subst.
apply args_len_rec_nonneg in H0.
destruct tp; omega.
Qed. 

Definition store_arg m sp ofs ty' a' :=
      match ty', a' with 
        | Tlong, Vlong n => 
          match store_stack m (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(ofs+1))) 
                            (Vint (Int64.hiword n)) with
            | None => None
            | Some m' => 
                match  store_stack m' (Vptr sp Int.zero) Tint
                      (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) 
                                (Vint (Int64.loword n)) with
                | None => None
                | Some m'' => Some (m'',ofs+2) 
                end
          end
        | Tlong, _ => None
        | _,_ => 
          match store_stack m (Vptr sp Int.zero) ty' 
                 (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs)) a' with
            | None => None
            | Some m' => Some (m', ofs+typesize ty')
          end
      end.

Lemma store_argSZ m sp z ty v m' ofs:
      store_arg m sp z ty v = Some(m',ofs) -> ofs = z + typesize ty.
Proof. destruct ty; simpl; intros.
  remember (store_stack m (Vptr sp Int.zero) Tint
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in H. clear Heqs.
    destruct s; inv H. trivial. 
  remember (store_stack m (Vptr sp Int.zero) Tfloat
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in H. clear Heqs.
    destruct s; inv H. trivial.
  destruct v; inv H.
  remember (store_stack m (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(z+1))) 
                            (Vint (Int64.hiword i))) as s1. 
    unfold Stacklayout.fe_ofs_arg in Heqs1. simpl in Heqs1.
    rewrite <- Heqs1 in *. clear Heqs1.
    destruct s1; inv H1.
    remember (store_stack m0 (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*z)) 
                            (Vint (Int64.loword i))) as s2. 
    unfold Stacklayout.fe_ofs_arg in Heqs2. simpl in Heqs2.
    rewrite <- Heqs2 in *. clear Heqs2.
    destruct s2; inv H0. trivial. 
  remember (store_stack m (Vptr sp Int.zero) Tsingle
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs in *. clear Heqs.
    destruct s; inv H. trivial. 
Qed.
  
Lemma store_args_cons m sp z v args ty tys m1 z1: 
  store_arg m sp z ty v = Some(m1, z1) ->
  (exists m', store_args_rec m1 sp z1 args tys = Some m') ->
  exists m', store_args_rec m sp z (v :: args) (ty :: tys) = Some m'. 
Proof. intros.
simpl. unfold store_arg in H.
destruct ty.
  remember (store_stack m (Vptr sp Int.zero) Tint
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
  remember (store_stack m (Vptr sp Int.zero) Tfloat
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
  destruct v; inv H.
  remember (store_stack m (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(z+1))) 
                            (Vint (Int64.hiword i))) as s1. 
    unfold Stacklayout.fe_ofs_arg in Heqs1. simpl in Heqs1.
    rewrite <- Heqs1 in *. clear Heqs1.
    destruct s1; inv H2.
    remember (store_stack m0 (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*z)) 
                            (Vint (Int64.loword i))) as s2. 
    unfold Stacklayout.fe_ofs_arg in Heqs2. simpl in Heqs2.
    rewrite <- Heqs2 in *. clear Heqs2.
    destruct s2; inv H1. assumption.
  remember (store_stack m (Vptr sp Int.zero) Tsingle
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    unfold Stacklayout.fe_ofs_arg in Heqs. simpl in Heqs.
    rewrite <- Heqs. clear Heqs.
    destruct s; inv H. simpl. assumption.
Qed.  

Lemma store_arg_perm1: forall m sp z ty v mm zz
      (STA: store_arg m sp z ty v = Some (mm, zz)),
       forall (b' : block) (ofs' : Z) (k : perm_kind) (p : permission),
       Mem.perm m b' ofs' k p -> Mem.perm mm b' ofs' k p.
Proof. intros.
simpl. unfold store_arg in STA.
destruct ty.
  remember (store_stack m (Vptr sp Int.zero) Tint
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs. 
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
  remember (store_stack m (Vptr sp Int.zero) Tfloat
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s. 
    destruct s; inv STA. apply eq_sym in Heqs. 
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
  destruct v; inv STA.
  remember (store_stack m (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*(z+1))) 
                            (Vint (Int64.hiword i))) as s1. 
    unfold Stacklayout.fe_ofs_arg in Heqs1. simpl in Heqs1.
    rewrite <- Heqs1 in *. apply eq_sym in Heqs1.
    destruct s1; inv H1.
    remember (store_stack m0 (Vptr sp Int.zero) Tint 
                  (Int.repr (Stacklayout.fe_ofs_arg + 4*z)) 
                            (Vint (Int64.loword i))) as s2. 
    unfold Stacklayout.fe_ofs_arg in Heqs2. simpl in Heqs2.
    rewrite <- Heqs2 in *. apply eq_sym in Heqs2.
    destruct s2; inv H2.
    unfold store_stack in *; simpl in *.
    eapply Mem.perm_store_1; try eassumption. 
    eapply Mem.perm_store_1; eassumption. 
  remember (store_stack m (Vptr sp Int.zero) Tsingle
          (Int.repr (Stacklayout.fe_ofs_arg + 4 * z)) v) as s.
    destruct s; inv STA. apply eq_sym in Heqs. 
    unfold store_stack in Heqs; simpl in Heqs.
    eapply Mem.perm_store_1; eassumption.
Qed.     

Lemma store_args_rec_succeeds_aux sp: 
  forall tys args 
      (VALSDEF: val_casted.vals_defined args=true)
      (HASTY: Val.has_type_list args tys) sz
      (ALR: args_len_rec args tys = Some sz)
      z (POS: 0 <= z)
      (REP: 4*(z+sz) < Int.modulus) m
      (RP: Mem.range_perm m sp (4*z) (4*z + 4*sz) Cur Writable),
  exists m', store_args_rec m sp z args tys = Some m'.
Proof. 
(*generalize dependent m. generalize dependent z.
generalize dependent sz. generalize dependent args.*)
intros tys. induction tys.
  intros.
  destruct args; simpl in *; inv ALR. rewrite Zplus_0_r in *.
     eexists; reflexivity.
  destruct args. intros. inv ALR. 
  intros. destruct HASTY. 
  assert (ArgsDef: vals_defined args = true). 
    destruct v; try inv VALSDEF; trivial.
 apply args_len_recD in ALR. 
 destruct ALR as [sizeA [sz' [SZ [AL SzA]]]].
 assert (sizeA = typesize a).
  clear - SzA. destruct a; try solve[trivial]. simpl. admit. (*TODO*)
 clear SzA.
 subst sz sizeA.
 assert (STARG: exists mm zz, store_arg m sp z a v = Some(mm,zz)).
 { clear IHtys H0.
   destruct (Mem.valid_access_store m (chunk_of_type a) sp (4*z) v)
   as [mm ST]. 
      split. red; intros. eapply RP; clear RP.
        split. omega.
        assert (size_chunk (chunk_of_type a) <= 4 * (typesize a + sz')).  
         { clear - AL. apply args_len_rec_nonneg in AL.
            unfold typesize. destruct a; simpl in *. 
               destruct sz'; xomega. destruct sz'. xomega. 
               destruct p; xomega. xomega. 
               destruct sz'; try xomega. destruct p; xomega. 
               destruct sz'; try xomega. } 
         remember (size_chunk (chunk_of_type a)) as p1. 
         remember (typesize a + sz') as p2. clear - H0 H1. omega. 
      clear - POS. assert (0 < z). admit. clear POS. 
         destruct a; simpl. 
           destruct z. omega. exists (Z.pos p). xomega. xomega.
           destruct z. omega. exists (Z.pos p). xomega. xomega.
           destruct z. omega. admit. xomega. 
           destruct z. omega. exists (Z.pos p). xomega. xomega. 
   clear RP.
   destruct a; simpl in ST; simpl.
    unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST. 
       exists mm, (z+1); trivial.
       admit.
    unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST. 
       exists mm, (z+2); trivial. 
       clear - POS REP AL. 
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega. 
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tfloat + sz').
           simpl. destruct sz'. omega. xomega. xomega. 
         remember (typesize Tfloat + sz') as q. clear  AL Heqq sz'. 
           unfold Int.max_unsigned. xomega. 
    destruct v; inv H; inv VALSDEF.
       unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr.
       rewrite Int.add_zero_l, Int.unsigned_repr. 
       apply Mem.store_int64_split in ST. 
       destruct ST as [m1 [ST1 ST2]]. admit.

       clear - POS REP AL.
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega. 
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tlong + sz').
           simpl. destruct sz'. omega. xomega. xomega. 
         remember (typesize Tlong + sz') as q. clear  AL Heqq sz'. 
           unfold Int.max_unsigned. xomega. 
       clear - POS REP AL.
       apply args_len_rec_nonneg in AL.
       destruct z; simpl; try xomega. 
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tlong + sz').
           simpl. destruct sz'. omega. xomega. xomega. 
         remember (typesize Tlong + sz') as q. clear  AL Heqq sz'. 
           unfold Int.max_unsigned. xomega. 
    unfold store_stack. simpl.
       rewrite Int.add_zero_l, Int.unsigned_repr, ST. 
       exists mm, (z+1); trivial. 
       clear - POS REP AL. 
       apply args_len_rec_nonneg in AL.
       destruct z; try xomega. 
         unfold Int.max_unsigned; simpl; omega.
         assert (0 < typesize Tsingle + sz').
           simpl. destruct sz'. omega. xomega. xomega. 
         remember (typesize Tsingle + sz') as q. clear  AL Heqq sz'. 
           unfold Int.max_unsigned. xomega.
 }
 specialize (IHtys _ ArgsDef H0 _ AL).
 rewrite Zplus_assoc in REP.
 assert (POS' : 0 <= z+typesize a). destruct a; simpl; omega.
 specialize (IHtys _ POS' REP).
 destruct STARG as [mm [zz STARG]].
 specialize (store_argSZ _ _ _ _ _ _ _ STARG). intros ZZ; subst zz.
 eapply store_args_cons. eassumption.
 apply IHtys; clear IHtys.
 red; intros. eapply store_arg_perm1; eauto. 
 clear STARG. eapply RP; clear RP. 
 specialize (typesize_pos a); intros. omega.
Qed.

Lemma store_args_rec_succeeds sz m sp args tys 
      (VALSDEF: val_casted.vals_defined args=true)
      (HASTY: Val.has_type_list args tys) 
      (REP: 4*sz < Int.modulus) m'' :
  args_len_rec args tys = Some sz -> 
  Mem.alloc m 0 (4*sz) = (m'',sp) -> 
  exists m', store_args_rec m'' sp 0 args tys = Some m'.
Proof.
intros H H2. exploit store_args_rec_succeeds_aux; eauto. omega. omega.
intros ofs [H3 H4]. apply Mem.perm_alloc_2 with (ofs := ofs) (k := Cur) in H2; auto.
eapply Mem.perm_implies; eauto. constructor.
Qed.

Definition store_args m sp args tys := store_args_rec m sp 0 args tys.

Definition parent_sp0 (sp0 : block) (s: list stackframe) : val :=
  match s with
  | nil => Vptr sp0 Int.zero
  | Stackframe f sp ra c :: s' => sp
  end.

Inductive mach_step (ge:genv): Mach_core -> mem -> Mach_core -> mem -> Prop :=
  | Mach_exec_Mlabel:
      forall s f sp lbl c rs m lf,
      mach_step ge (Mach_State s f sp (Mlabel lbl :: c) rs lf) m
                (Mach_State s f sp c rs lf) m

  | Mach_exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v lf,
      load_stack m sp ty ofs = Some v ->
      mach_step ge (Mach_State s f sp (Mgetstack ofs ty dst :: c) rs lf) m
                (Mach_State s f sp c (rs#dst <- v) lf) m

  | Mach_exec_Msetstack:
      forall s f sp src ofs ty c rs m m' rs' lf,
      store_stack m sp ty ofs (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_setstack ty) rs ->
      mach_step ge (Mach_State s f sp (Msetstack src ofs ty :: c) rs lf) m
                (Mach_State s f sp c rs' lf) m'

  | Mach_exec_Mgetparam:
      forall s fb f sp ofs ty dst c rs m v rs' sp0 args0 tys0,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m sp Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (parent_sp0 sp0 s) ty ofs = Some v ->
      rs' = (rs # temp_for_parent_frame <- Vundef # dst <- v) ->
      mach_step ge (Mach_State s fb sp (Mgetparam ofs ty dst :: c) rs 
                                    (mk_load_frame sp0 args0 tys0)) m
                (Mach_State s fb sp c rs' (mk_load_frame sp0 args0 tys0)) m

  | Mach_exec_Mop:
      forall s f sp op args res c rs m v rs' lf,
      eval_operation ge sp op rs##args m = Some v ->
      rs' = ((undef_regs (destroyed_by_op op) rs)#res <- v) ->
      mach_step ge (Mach_State s f sp (Mop op args res :: c) rs lf) m
                (Mach_State s f sp c rs' lf) m

  | Mach_exec_Mload:
      forall s f sp chunk addr args dst c rs m a v rs' lf,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = ((undef_regs (destroyed_by_load chunk addr) rs)#dst <- v) ->
      mach_step ge (Mach_State s f sp (Mload chunk addr args dst :: c) rs lf) m
                (Mach_State s f sp c rs' lf) m

  | Mach_exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a rs' lf,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      mach_step ge (Mach_State s f sp (Mstore chunk addr args src :: c) rs lf) m
                (Mach_State s f sp c rs' lf) m'

  (*NOTE [loader]*)
  | Mach_exec_Minitialize_call: 
      forall m args tys m1 stk m2 fb z,
      args_len_rec args tys = Some z -> 
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 -> 
      mach_step ge (Mach_CallstateIn fb args tys) m
        (Mach_Callstate nil fb (Regmap.init Vundef) (mk_load_frame stk args tys)) m2

  | Mach_exec_Mcall_internal:
      forall s fb sp sig ros c rs m f f' ra callee lf,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      (*NEW: check that the block f' actually contains a (internal) function:*)
      Genv.find_funct_ptr ge f' = Some (Internal callee) ->
      mach_step ge (Mach_State s fb sp (Mcall sig ros :: c) rs lf) m
                (Mach_Callstate (Stackframe fb sp (Vptr fb ra) c :: s) f' rs lf) m

  | Mach_exec_Mcall_external:
      forall s fb sp sig ros c rs m f f' ra callee args lf,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      return_address_offset f c ra ->
      (*NEW: check that the block f' actually contains a (external)
             function, and perform the "extra step":*)
      Genv.find_funct_ptr ge f' = Some (External callee) ->
      extcall_arguments rs m sp (ef_sig callee) args ->
      mach_step ge (Mach_State s fb sp (Mcall sig ros :: c) rs lf) m
                (Mach_CallstateOut (Stackframe fb sp (Vptr fb ra) c :: s) 
                  f' callee args rs lf) m

  | Mach_exec_Mtailcall_internal:
      forall s fb stk soff sig ros c rs m f f' m' callee sp0 args0 tys0,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      (*NEW: check that the block f' actually contains a function:*)
      Genv.find_funct_ptr ge f' = Some (Internal callee) ->
      mach_step ge (Mach_State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs
                                 (mk_load_frame sp0 args0 tys0)) m
                (Mach_Callstate s f' rs (mk_load_frame sp0 args0 tys0)) m'

  | Mach_exec_Mtailcall_external:
      forall s fb stk soff sig ros c rs m f f' m' callee args sp0 args0 tys0,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      (*NEW: check that the block f' actually contains a function:*)
      Genv.find_funct_ptr ge f' = Some (External callee) ->
      extcall_arguments rs m' (parent_sp0 sp0 s) (ef_sig callee) args ->
      mach_step ge (Mach_State s fb (Vptr stk soff) (Mtailcall sig ros :: c) rs
                                 (mk_load_frame sp0 args0 tys0)) m
                (Mach_CallstateOut s f' callee args rs 
                                   (mk_load_frame sp0 args0 tys0)) m'

  | Mach_exec_Mbuiltin:
      forall s f sp rs m ef args res b t vl rs' m' lf,
      external_call' ef ge rs##args m t vl m' ->
      ~ observableEF hf ef ->
      rs' = set_regs res vl (undef_regs (destroyed_by_builtin ef) rs) ->
      mach_step ge (Mach_State s f sp (Mbuiltin ef args res :: b) rs lf) m
                (Mach_State s f sp b rs' lf) m'

(*NO SUPPORT FOR ANNOT YET
  | Mach_exec_Mannot:
      forall s f sp rs m ef args b vargs t v m',
      annot_arguments rs m sp args vargs ->
      external_call' ef ge vargs m t v m' ->
      mach_step (Mach_State s f sp (Mannot ef args :: b) rs) m
         t (Mach_State s f sp b rs) m'*)

  | Mach_exec_Mgoto:
      forall s fb f sp lbl c rs m c' lf,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      mach_step ge (Mach_State s fb sp (Mgoto lbl :: c) rs lf) m
                (Mach_State s fb sp c' rs lf) m

  | Mach_exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c' rs' lf,
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      mach_step ge (Mach_State s fb sp (Mcond cond args lbl :: c) rs lf) m
                (Mach_State s fb sp c' rs' lf) m

  | Mach_exec_Mcond_false:
      forall s f sp cond args lbl c rs m rs' lf,
      eval_condition cond rs##args m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      mach_step ge (Mach_State s f sp (Mcond cond args lbl :: c) rs lf) m
                (Mach_State s f sp c rs' lf) m

  | Mach_exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c' rs' lf,
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      rs' = undef_regs destroyed_by_jumptable rs ->
      mach_step ge (Mach_State s fb sp (Mjumptable arg tbl :: c) rs lf) m
                (Mach_State s fb sp c' rs' lf) m

  | Mach_exec_Mreturn:
      forall s fb stk soff c rs m f m' sp0 args0 tys0,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      load_stack m (Vptr stk soff) Tint f.(fn_link_ofs) = Some (parent_sp0 sp0 s) ->
      load_stack m (Vptr stk soff) Tint f.(fn_retaddr_ofs) = Some (parent_ra s) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      mach_step ge (Mach_State s fb (Vptr stk soff) (Mreturn :: c) rs
                            (mk_load_frame sp0 args0 tys0)) m
                (Mach_Returnstate s (sig_res (fn_sig f)) rs
                            (mk_load_frame sp0 args0 tys0)) m'

  | Mach_exec_function_internal:
      forall s fb rs m f m1 m2 m3 stk rs' sp0 args0 tys0,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      Mem.alloc m 0 f.(fn_stacksize) = (m1, stk) ->
      let sp := Vptr stk Int.zero in
      store_stack m1 sp Tint f.(fn_link_ofs) (parent_sp0 sp0 s) = Some m2 ->
      store_stack m2 sp Tint f.(fn_retaddr_ofs) (parent_ra s) = Some m3 ->
      rs' = undef_regs destroyed_at_function_entry rs ->
      mach_step ge (Mach_Callstate s fb rs (mk_load_frame sp0 args0 tys0)) m
                (Mach_State s fb sp f.(fn_code) rs' (mk_load_frame sp0 args0 tys0)) m3
(*
  | Mach_exec_function_external:
      forall s fb rs m t rs' ef args res m' lf
      (OBS: observableEF hf ef = false),
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      extcall_arguments rs m (parent_sp s) (ef_sig ef) args ->
      external_call' ef ge args m t res m' ->
      rs' = set_regs (loc_result (ef_sig ef)) res rs ->
      mach_step ge (Mach_Callstate s fb rs lf) m
         (Mach_Returnstate s (sig_res (ef_sig ef)) rs' lf) m'
*)
  | Mach_exec_function_external:
      forall cs f' rs m t rs' callee args res m' lf
      (OBS: EFisHelper hf callee),
      Genv.find_funct_ptr ge f' = Some (External callee) ->
      external_call' callee ge args m t res m' ->
      rs' = set_regs (loc_result (ef_sig callee)) res rs ->
      mach_step ge
      (Mach_CallstateOut cs f' callee args rs lf) m
      (Mach_Returnstate cs (sig_res (ef_sig callee)) rs' lf) m'

  | Mach_exec_return:
      forall s f sp ra c retty rs m lf,
      mach_step ge (Mach_Returnstate (Stackframe f sp ra c :: s) retty rs lf) m
                (Mach_State s f sp c rs lf) m.

(*NOTE value encoding, which was formerly done here, in Mach_initial_core, 
  is now handled by the simulation invariant [agree_args_match_aux] 
  (cf. StackingproofEFF.v). *)

Definition Mach_initial_core (ge:genv) (v: val) (args:list val)
           : option Mach_core := 
  match v with
    | Vptr b i => 
      if Int.eq_dec i Int.zero 
      then match Genv.find_funct_ptr ge b with
             | None => None
             | Some f => 
               match f with 
                 | Internal fi =>
                   let tyl := sig_args (funsig f) in
                   if val_has_type_list_func args (sig_args (funsig f))
                      && vals_defined args
                   then Some (Mach_CallstateIn b args tyl)
                   else None
                 | External _ => None
               end
           end
      else None
    | _ => None
   end.

(*NOTE Halted when the stack contains just a single stack frame 
  (modeling the program loader)*)

Definition Mach_halted (q : Mach_core): option val :=
    match q with 
      (*Return Tlong, which must be decoded*)
      | Mach_Returnstate nil (Some Tlong) rs lf => 
           match loc_result (mksignature nil (Some Tlong)) with
             | nil => None
             | r1 :: r2 :: nil => 
                 match decode_longs (Tlong::nil) (rs r1::rs r2::nil) with
                   | v :: nil => Some v
                   | _ => None
                 end
             | _ => None
           end

      (*Return a value of any other typ*)
      | Mach_Returnstate nil (Some retty) rs lf => 
           match loc_result (mksignature nil (Some retty)) with
            | nil => None
            | r :: TL => match TL with 
                           | nil => Some (rs r)
                           | _ :: _ => None
                         end
           end

      (*Return Tvoid - modeled as integer return*)
      | Mach_Returnstate nil None rs lf => Some (rs AX)

      | _ => None
    end.

Definition Mach_at_external (c: Mach_core):
          option (external_function * signature * list val) :=
  match c with
  | Mach_State _ _ _ _ _ _ => None
  | Mach_Callstate _ _ _ _ => None
  | Mach_CallstateOut s fb ef args rs lf => 
        if observableEF_dec hf ef
        then Some (ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) args)
        else None
  | Mach_CallstateIn _ _ _ => None
  | Mach_Returnstate _ _ _ _ => None
 end.

Definition Mach_after_external (vret: option val)(c: Mach_core) : option Mach_core :=
  match c with 
    Mach_CallstateOut s fb ef args rs lf => 
      match vret with
            | None => Some (Mach_Returnstate s (sig_res (ef_sig ef))
                             (set_regs (loc_result (ef_sig ef))
                               (encode_long (sig_res (ef_sig ef)) Vundef) rs)
                             lf)
            | Some v => Some (Mach_Returnstate s (sig_res (ef_sig ef))
                               (set_regs (loc_result (ef_sig ef))
                                 (encode_long (sig_res (ef_sig ef)) v) rs)
                               lf)
          end
  | _ => None
  end.

Lemma Mach_at_external_halted_excl :
       forall q, Mach_at_external q = None \/ Mach_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma Mach_after_at_external_excl : forall retv q q',
      Mach_after_external retv q = Some q' -> Mach_at_external q' = None.
  Proof. intros.
    destruct q; simpl in *; try inv H.
    destruct retv; inv H1; simpl; trivial.
  Qed.

(*Variable return_address_offset: function -> code -> int -> Prop.*)

Lemma Mach_corestep_not_at_external ge m q m' q':
      mach_step ge q m q' m' -> Mach_at_external q = None.
Proof. intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec hf callee); simpl; trivial. 
  exfalso. eapply EFhelpers; eassumption. 
Qed.  

Lemma Mach_corestep_not_halted ge m q m' q': 
      mach_step ge q m q' m' -> Mach_halted q = None.
Proof. intros. inv H; auto. Qed.

Definition Mach_core_sem : CoreSemantics genv Mach_core mem.
  eapply (@Build_CoreSemantics _ _ _ 
            Mach_initial_core
            Mach_at_external
            Mach_after_external
            Mach_halted
            mach_step).
    apply Mach_corestep_not_at_external.
    apply Mach_corestep_not_halted.
    apply Mach_at_external_halted_excl.
Defined.

(******NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Lemma Mach_forward ge c m c' m': forall
      (CS: mach_step ge c m c' m'), mem_forward m m'.
  Proof. intros.
   inv CS; try apply mem_forward_refl.
   (*Msetstack*)
     unfold store_stack in H; simpl in *.
     destruct sp; inv H.
     eapply store_forward; eassumption. 
   (*Mstore*)
     destruct a; simpl in H0; inv H0. 
     eapply store_forward. eassumption. 
   (*initialize*)
     eapply store_args_fwd in H1.
     eapply mem_forward_trans; eauto.
     solve[eapply alloc_forward; eauto].
   (*Mtailcall_internal*)
     eapply free_forward; eassumption.
   (*Mtailcall_external*)
     eapply free_forward; eassumption.
   (*Mbuiltin**)
      inv H.
      eapply external_call_mem_forward; eassumption.
    (*Mannot
      inv H. 
      eapply external_call_mem_forward; eassumption.*)
    (*Mreturn*)
      eapply free_forward; eassumption.
    (*internal function*)
     unfold store_stack in *; simpl in *.
     eapply mem_forward_trans.
       eapply alloc_forward; eassumption.
     eapply mem_forward_trans.
       eapply store_forward; eassumption. 
       eapply store_forward; eassumption. 
    (*external unobservable function*)
      inv H0. eapply external_call_mem_forward; eassumption.
Qed.

Program Definition Mach_coop_sem : 
  CoopCoreSem genv Mach_core.
apply Build_CoopCoreSem with (coopsem := Mach_core_sem).
  apply Mach_forward.
Defined.

End MACH_COOPSEM.