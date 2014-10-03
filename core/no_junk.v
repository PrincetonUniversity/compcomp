

Require Import Memory.
Require Import Maps.
Require Import Coqlib.
Require Import Values.

Require Import StructuredInjections.
Require Import effect_simulations_lemmas.
Require Import mem_interpolation_defs.
 
Load Santiago_tactics.

Local Notation "a # b" := (PMap.get b a) (at level 1).
Local Notation "a ## b" := (ZMap.get b a) (at level 1).

Definition junk_inv_r mu m1 m2 m2' :=
  (forall (b2: block) delta ofs,
    locBlocksTgt mu b2 = true  ->
    (Mem.perm m2 b2 (delta + ofs) = Mem.perm m2' b2 (delta + ofs) ) /\
    ((Mem.mem_contents m2) # b2 ## (delta + ofs) = (Mem.mem_contents m2') # b2 ## (delta + ofs) )) /\
  (forall (b1 b2: block) delta ofs,
    extern_of mu b1 = Some( b2, delta) ->
    Mem.perm m1 b1 ofs Max Nonempty -> 
    (Mem.perm m2 b2 (delta + ofs) = Mem.perm m2' b2 (delta + ofs) ) /\
    ((Mem.mem_contents m2) # b2 ## (delta + ofs) = (Mem.mem_contents m2') # b2 ## (delta + ofs) )).

Lemma junk_inv_r_refl: forall mu m1 m2, junk_inv_r mu m1 m2 m2.
  unfold junk_inv_r; intros; auto.
Qed.

Lemma junk_inv_r_sym: forall mu m1 m2 m2', junk_inv_r mu m1 m2 m2' -> junk_inv_r mu m1 m2' m2.
  
  unfold junk_inv_r; intros mu m1 m2 m2' H; split; intros;
  destruct H as [loc ext].
  split ; symmetry; specialize (loc b2 delta ofs H0); destruct loc; assumption.
  split ; symmetry; specialize (ext b1 b2 delta ofs H0 H1); destruct ext; assumption.
Qed.

Lemma junk_inv_r_trans: forall mu m1 m2 m2' m2'', junk_inv_r mu m1 m2 m2' -> junk_inv_r mu m1 m2' m2'' -> junk_inv_r mu m1 m2 m2''.
  unfold junk_inv_r; intros mu m1 m2 m2' m2'' H1 H2; split; intros;
  destruct H1 as [loc1 ext1];  destruct H2 as [loc2 ext2].
  specialize (loc1 b2 delta ofs H); destruct loc1;
  specialize (loc2 b2 delta ofs H); destruct loc2; split; rewriter; auto.
  specialize (ext1 b1 b2 delta ofs H H0); destruct ext1;
  specialize (ext2 b1 b2 delta ofs H H0); destruct ext2;
  split; rewriter; eauto.
Qed.

Definition junk_inv_l mu m m' :=
  forall (b1 b1': block) delta ofs,
    (as_inj mu) b1 = Some (b1', delta)  ->
    (Mem.perm m b1 (ofs) = Mem.perm m' b1 (ofs) ) /\
    ((Mem.mem_contents m) # b1 ## (ofs) = (Mem.mem_contents m') # b1 ## (ofs) ).

Lemma junk_inv_l_refl: forall mu m, junk_inv_l mu m m.
  unfold junk_inv_l; intros; auto.
Qed.

Lemma junk_inv_l_sym: forall mu m m', junk_inv_l mu m m' -> junk_inv_l mu m' m.
  unfold junk_inv_l; intros mu m m' H; intros;
  split ; symmetry; specialize (H b1 b1' delta ofs H0); destruct H; assumption.
Qed.

Lemma junk_inv_l_trans: forall mu m m' m'', junk_inv_l mu m m' -> junk_inv_l mu m' m'' -> junk_inv_l mu m m''.
  unfold junk_inv_l; intros mu m m' m'' H1 H2; split; intros;
  specialize (H1 b1 b1' delta ofs H); destruct H1;
  specialize (H2 b1 b1' delta ofs H); destruct H2; rewriter; auto.
Qed.


(** *No Junk *)
Definition no_junk_r (mu12:SM_Injection)(m1 m2: mem): Prop :=
  forall b2 ofs, 
            Mem.perm m2 b2 ofs Max Nonempty ->
            extBlocksTgt mu12 b2 = true ->
            exists b1 delta12,
            (extern_of mu12) b1 = Some (b2, delta12 ) /\
            Mem.perm m1 b1 (ofs - delta12) Max Nonempty.


(** *Transitivity when the middle memory doesn't change*)
Lemma no_junk_r_trans: forall mu mu12 mu23,
                       SM_wd mu12 ->
                       SM_wd mu23 ->
                       mu = compose_sm mu12 mu23 ->
                       extBlocksTgt mu12 = extBlocksSrc mu23 ->
                       forall m1 m2 m3 m3',
                         junk_inv_r mu m1 m3 m3' ->
                         no_junk_r mu12 m1 m2 ->
                         junk_inv_r mu23 m2 m3 m3'.
  unfold junk_inv_r;
  intros mu mu12 mu23 WD12 WD23 comp extB m1 m2 m3 m3' JINV NJNK.
  unfold no_junk_r in NJNK.
  
  split.
  {(*locals*)
    intros b2 delta ofs loc_of.
    destruct JINV as [JINVloc JINVext].
    eapply JINVloc; eauto.
    rewrite comp; unfold compose_sm, compose_meminj; simpl; assumption.
  }
  { (*externals*) intros b1 b2 delta ofs ext_of perm.
  destruct (NJNK b1 ofs) as [b0 [delta12 [ext_of' perm']]]; eauto.
  rewrite extB; apply WD23 in ext_of; destruct ext_of; assumption.
  
  assert (arith: delta + ofs = (delta12 + delta) + (ofs - delta12)) by xomega;
    rewrite arith.
  eapply JINV; eauto.
  rewrite comp; unfold compose_sm, compose_meminj; simpl.
  erewrite ext_of', ext_of; reflexivity. 
  }
Qed.

(** *Clean memory: a mem with no junk*)

Definition is_not_mapped mu m1 b' ofs :=
  match source (as_inj mu) m1 b' ofs with
      Some _ => false
    | None => true
  end.

(* checks if a location is external and NOT  mapped *)
Definition is_junk m mu b' ofs:=
  (extBlocksTgt mu b') && (is_not_mapped mu m b' ofs).
                       

(*Removes all junk from one block in m2. i.e. Removes permition to locations that are not mapped from m1 *)
Definition clean_block_access (mu: SM_Injection) m1 b' (access2: Z -> perm_kind -> option permission): Z -> perm_kind -> option permission :=
  fun ofs pk =>
    match access2 ofs pk with
        | None => None
        | Some perm => if is_junk m1 mu b' ofs then None else Some perm 
    end.

(*
Definition filter2 (A: Type) (pred: elt -> bool) (m: t A) {struct m} : t A :=
    match m with
    | Leaf => Leaf
    | Node l o r =>
        let o' := match o with None => None | Some x => if pred x then o else None end in
        Node' (filter1 pred l) o' (filter1 pred r)
    end.

Definition clean_block_content mu m1 b' (content2: ZMap.t memval):=
  map1 (fun ofs => if is_junk m1 mu b' ofs then None else )

  *)



Definition clean (mu: SM_Injection) (m1 m2:mem) : mem.
  Admitted.

Lemma clean_junk_inv_r: forall mu m1 m2, junk_inv_r mu m1 m2 (clean mu m1 m2).
Admitted.

Lemma clean_junk_inv_l: forall mu m1 m2, junk_inv_l mu m2 (clean mu m1 m2).
Admitted.

Lemma clean_no_junk: forall mu m1 m2, no_junk_r mu m1 (clean mu m1 m2).
Admitted.

Theorem ex_clean_mem: forall mu m1 m2, exists m2', junk_inv_r mu m1 m2 m2' /\ no_junk_r mu m1 m2'.
  intros.
  exists (clean mu m1 m2).
  split; [apply clean_junk_inv_r | apply clean_no_junk].
Qed.

Theorem ex_clean_mem_mid: forall mu12 m1 m2, exists m2', junk_inv_r mu12 m1 m2 m2' /\ no_junk_r mu12 m1 m2'.
  intros.
  exists (clean mu12 m1 m2).
  split; [apply clean_junk_inv_r | apply clean_no_junk].
Qed.
