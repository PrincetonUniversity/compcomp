Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Registers.

Require Import semantics.
Require Import val_casted.

Require Import RTL.
Require Import BuiltinEffects.

Inductive RTL_core : Type :=
  | RTL_State:
      forall (stack: list stackframe) (**r call stack *)
             (f: function)            (**r current function *)
             (sp: val)                (**r stack pointer *)
             (pc: node)               (**r current program point in [c] *)
             (rs: regset),             (**r register state *)
      RTL_core
  | RTL_Callstate:
      forall (stack: list stackframe) (**r call stack *)
             (f: fundef)              (**r function to call *)
             (args: list val),         (**r arguments to the call *)
      RTL_core
  | RTL_Returnstate:
      forall (stack: list stackframe) (**r call stack *)
             (v: val),                 (**r return value for the call *)
      RTL_core.

(* Transformations between the new and the old definitions of state *)
Definition core2state (q:RTL_core)(m:mem): state:=
  match q with
      RTL_State stack f sp pc rs => State stack f sp pc rs m
    | RTL_Callstate stack f args => Callstate stack f args m
    | RTL_Returnstate stack v => Returnstate stack v m
  end.

Definition state2core (s:state): RTL_core * mem :=
  match s with
      State stack f sp pc rs m => (RTL_State stack f sp pc rs, m)
    | Callstate stack f args m => (RTL_Callstate stack f args, m)
    | Returnstate stack v m => (RTL_Returnstate stack v, m)
  end.

Section RELSEM.
Variable hf : I64Helpers.helper_functions.

Inductive RTL_corestep (ge:genv): RTL_core -> mem -> RTL_core -> mem -> Prop :=
  | rtl_corestep_exec_Inop:
      forall s f sp pc rs m pc',
      (fn_code f)!pc = Some(Inop pc') ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_corestep_exec_Iop:
      forall s f sp pc rs m op args res pc' v,
      (fn_code f)!pc = Some(Iop op args res pc') ->
      eval_operation ge sp op rs##args m = Some v ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' (rs#res <- v)) m
  | rtl_corestep_exec_Iload:
      forall s f sp pc rs m chunk addr args dst pc' a v,
      (fn_code f)!pc = Some(Iload chunk addr args dst pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' (rs#dst <- v)) m
  | rtl_corestep_exec_Istore:
      forall s f sp pc rs m chunk addr args src pc' a m',
      (fn_code f)!pc = Some(Istore chunk addr args src pc') ->
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a rs#src = Some m' ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m'
  | rtl_corestep_exec_Icall:
      forall s f sp pc rs m sig ros args res pc' fd,
      (fn_code f)!pc = Some(Icall sig ros args res pc') ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_Callstate (Stackframe res f sp pc' rs :: s) fd rs##args) m
  | rtl_corestep_exec_Itailcall:
      forall s f stk pc rs m sig ros args fd m',
      (fn_code f)!pc = Some(Itailcall sig ros args) ->
      find_function ge ros rs = Some fd ->
      funsig fd = sig ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      RTL_corestep ge (RTL_State s f (Vptr stk Int.zero) pc rs) m
        (RTL_Callstate s fd rs##args) m'

  | rtl_corestep_exec_Ibuiltin:
      forall s f sp pc rs m ef args res pc' t v m',
      (fn_code f)!pc = Some(Ibuiltin ef args res pc') ->
      external_call ef ge rs##args m t v m' ->
      ~ observableEF hf ef ->      
      RTL_corestep ge (RTL_State s f sp pc rs) m
         (RTL_State s f sp pc' (rs#res <- v)) m'

  | rtl_corestep_exec_Icond:
      forall s f sp pc rs m cond args ifso ifnot b pc',
      (fn_code f)!pc = Some(Icond cond args ifso ifnot) ->
      eval_condition cond rs##args m = Some b ->
      pc' = (if b then ifso else ifnot) ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_corestep_exec_Ijumptable:
      forall s f sp pc rs m arg tbl n pc',
      (fn_code f)!pc = Some(Ijumptable arg tbl) ->
      rs#arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some pc' ->
      RTL_corestep ge (RTL_State s f sp pc rs) m
        (RTL_State s f sp pc' rs) m
  | rtl_corestep_exec_Ireturn:
      forall s f stk pc rs m or m',
      (fn_code f)!pc = Some(Ireturn or) ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      RTL_corestep ge (RTL_State s f (Vptr stk Int.zero) pc rs) m
        (RTL_Returnstate s (regmap_optget or Vundef rs)) m'
  | rtl_corestep_exec_function_internal:
      forall s f args m m' stk,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      RTL_corestep ge (RTL_Callstate s (Internal f) args) m
        (RTL_State s
                  f
                  (Vptr stk Int.zero)
                  f.(fn_entrypoint)
                  (init_regs args f.(fn_params)))
        m'

  | rtl_corestep_exec_function_external:
      forall s ef args res t m m'
      (OBS: EFisHelper hf ef),
      external_call ef ge args m t res m' ->
      RTL_corestep ge (RTL_Callstate s (External ef) args) m
          (RTL_Returnstate s res) m'
  | rtl_corestep_exec_return:
      forall res f sp pc rs s vres m,
      RTL_corestep ge (RTL_Returnstate (Stackframe res f sp pc rs :: s) vres) m
        (RTL_State s f sp pc (rs#res <- vres)) m.

(* New initial state *)
Definition RTL_initial_core (ge: genv) (v:val)(args: list val): option RTL_core:=
  match v with
    | Vptr b i =>
      if Int.eq_dec i Int.zero
      then match Genv.find_funct_ptr ge b with
             | None => None
             | Some f => 
               match f with Internal fi =>
                 let tyl := sig_args (funsig f) in
                 if val_has_type_list_func args (sig_args (funsig f))
                    && vals_defined args
                    && zlt (4*(2*(Zlength args))) Int.max_unsigned
                 then Some (RTL_Callstate nil f args)
                 else None
               | External _ => None
               end
           end
      else None
    | _ => None
  end.

(** A final state is a [Returnstate] with an empty call stack. *)

(*LENB: in shared-memory compcert, we should allow arbitrary 
  return values, not just integers*)
Definition RTL_halted (c: RTL_core ): option val :=
  match c with
(*      RTL_Returnstate nil (Vint i) => Some (Vint i)*)
      RTL_Returnstate nil v => Some v
    | _ => None
  end.


(* New definition of semantics *)
Definition RTL_at_external (c: RTL_core): option (external_function * signature * list val) :=
  match c with
    | RTL_State stack f sp pc rs => None
    | RTL_Callstate stack f args => 
        match f with
          Internal _ => None
        | External ef =>  if observableEF_dec hf ef 
                          then Some(ef, ef_sig ef, args)
                          else None
        end
    | RTL_Returnstate stack v => None
  end.

Definition RTL_after_external (vret: option val)(c: RTL_core): option RTL_core :=
  match c with
    | RTL_State stack f sp pc rs => None
    | RTL_Callstate stack f args => 
      match f with
          Internal _ => None
        | External f' => match vret with
                             None => Some (RTL_Returnstate stack Vundef)
                           | Some v => Some (RTL_Returnstate stack v)
                         end
      end
    | RTL_Returnstate stack v => None
  end.           

Lemma corestep_not_external: forall (ge : genv) (m : mem) (q : RTL_core) (m' : mem) (q' : RTL_core),
                               RTL_corestep ge q m q' m' -> RTL_at_external q = None.
Proof.
  intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec hf ef); simpl; trivial. 
  exfalso. eapply EFhelpers; eassumption. 
Qed.

Lemma corestep_not_halted: forall (ge : genv) (m : mem) (q : RTL_core) (m' : mem) (q' : RTL_core),
                             RTL_corestep ge q m q' m' -> RTL_halted q = None.
Proof. intros. inv H; try reflexivity. Qed.

Lemma external_xor_halted: forall q : RTL_core, RTL_at_external q = None \/ RTL_halted q = None.
Proof.
  destruct q; simpl; try (left; reflexivity); try (right; reflexivity).
Qed.

Lemma after_xor_at_external: forall (retv : option val) (q q' : RTL_core),
                               RTL_after_external retv q = Some q' -> RTL_at_external q' = None.
Proof.
  intros. destruct q; destruct q'; try destruct f; destruct retv; simpl in *; try discriminate; try reflexivity.
Qed.

Definition RTL_core_sem : CoreSemantics genv RTL_core mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _ 
            RTL_initial_core
            RTL_at_external
            RTL_after_external
            RTL_halted
            RTL_corestep).
  eapply corestep_not_external.
  eapply corestep_not_halted.
  eapply external_xor_halted.
Defined.

(************************NOW SHOW THAT WE ALSO HAVE A COOPSEM******)

Require Import mem_lemmas. (*for mem_forward*)

Lemma rtl_coop_forward : forall g c m c' m' (CS: RTL_corestep g c m c' m'), 
      mem_forward m m'.
Proof. intros.
       inv CS; try apply mem_forward_refl.
         (*Storev*)
          destruct a; simpl in H1; inv H1. 
          eapply store_forward. eassumption. 
         eapply free_forward; eassumption.
         (*builtin*) 
         eapply external_call_mem_forward; eassumption.
         eapply free_forward; eassumption.
         eapply alloc_forward; eassumption.
         eapply external_call_mem_forward; eassumption.
Qed.

Lemma rtl_coop_rdonly g c m c' m'
            (CS: RTL_corestep g c m c' m') b 
            (VB: Mem.valid_block m b):  
             readonly m b m'.
  Proof. 
     inv CS; simpl in *; try apply readonly_refl.
          destruct a; inv H1. eapply store_readonly; eauto.
          eapply free_readonly; eauto.
          eapply ec_readonly_strong; eauto.
          eapply free_readonly; eauto.
          eapply alloc_readonly; eauto.
          eapply ec_readonly_strong; eauto.
Qed.

Program Definition rtl_coop_sem : 
  CoopCoreSem genv RTL_core.
Proof.
apply Build_CoopCoreSem with (coopsem := RTL_core_sem).
  apply rtl_coop_forward.
  apply rtl_coop_rdonly.
Defined.

Lemma rtl_coop_decay g c m c' m'
            (CS: RTL_corestep g c m c' m'): decay m m'.
  Proof. 
     inv CS; simpl in *; try apply decay_refl.
          destruct a; inv H1. eapply store_decay; eauto.
          eapply free_decay; eauto.
          eapply ec_decay; eauto.
          eapply free_decay; eauto.
          eapply alloc_decay; eauto.
          eapply ec_decay; eauto.
Qed.

Program Definition rtl_decay_sem : 
  @DecayCoreSem genv RTL_core.
Proof.
apply Build_DecayCoreSem with (decaysem := rtl_coop_sem).
  apply rtl_coop_decay.
Defined.

End RELSEM.

Lemma RTL_initial_coreD (g: genv) (v:val)(args: list val) c:
  RTL_initial_core g v args = Some c -> 
  exists b f, v= Vptr b Int.zero /\ 
   Genv.find_funct_ptr g b = Some (Internal f) /\ 
   val_casted.val_has_type_list_func args (sig_args (fn_sig f)) = true /\
   val_casted.vals_defined args = true /\ Z.lt (4*(2*(Zlength args))) Int.max_unsigned
  /\ c = RTL_Callstate nil (Internal f) args.
intros. destruct v; inv H.
destruct (Int.eq_dec i Int.zero); inv H1. exists b. 
destruct (Genv.find_funct_ptr g b); inv H0. 
destruct f; inv H1. exists f. 
remember (4 * (2 * Zlength args)) as l. simpl in *. rewrite <- Heql in *. clear Heql.
remember (val_casted.val_has_type_list_func args (sig_args (fn_sig f)) &&
         val_casted.vals_defined args &&
        (zlt l Int.max_unsigned)) as z. simpl in *.
destruct z; inv H0.  
apply andb_true_eq in Heqz. destruct Heqz.
apply andb_true_eq in H. destruct H. intuition.
unfold zlt in H0.  destruct (Z_lt_dec l Int.max_unsigned). trivial. inv H0. 
Qed.
(*
Lemma rtl_coop_readonly hf g c m c' m'
            (CS: RTL_corestep hf g c m c' m')
            (GV: forall b, isGlobalBlock g b = true -> Mem.valid_block m b):  
         RDOnly_fwd m m' (ReadOnlyBlocks g).
  Proof. intros. red; intros.
     unfold ReadOnlyBlocks in Hb.
     remember (Genv.find_var_info g b) as d; symmetry in Heqd.
     destruct d; try discriminate.
     apply find_var_info_isGlobal in Heqd. apply GV in Heqd.  
     (*destruct (MRR _ _ Heqd Hb) as [_ [VB _]].     *)
     inv CS; simpl in *; try apply readonly_refl.
          destruct a; inv H1. eapply store_readonly; eassumption.
          eapply free_readonly; eassumption.
          eapply ec_readonly_strong; eassumption.
          eapply free_readonly; eassumption.
          eapply alloc_readonly; eassumption.
          eapply ec_readonly_strong; eassumption.
Qed.

Lemma rtl_coop_readonlyT hf g c m c' m'
            (CS: RTL_corestep hf g c m c' m') B
            (GV: forall b, B b = true -> Mem.valid_block m b):  
         RDOnly_fwd m m' B.
  Proof. intros. red; intros.
(*     unfold ReadOnlyBlocks in Hb.
     remember (Genv.find_var_info g b) as d; symmetry in Heqd.
     destruct d; try discriminate.
     apply find_var_info_isGlobal in Heqd. apply GV in Heqd.  
     (*destruct (MRR _ _ Heqd Hb) as [_ [VB _]].     *)*)
     inv CS; simpl in *; try apply readonly_refl.
          destruct a; inv H1. eapply store_readonly; eauto.
          eapply free_readonly; eauto.
          eapply ec_readonly_strong; eauto.
          eapply free_readonly; eauto.
          eapply alloc_readonly; eauto.
          eapply ec_readonly_strong; eauto.
Qed.
(*
Require Import semantics_lemmas.
Lemma rtl_coopN_readonly hf g: forall n c m c' m'
            (CS: corestepN (rtl_coop_sem hf) g n c m c' m')
            (MRR: mem_respects_readonly g m),
         RDOnly_fwd m m' (ReadOnlyBlocks g).
Proof.
  induction n; simpl; intros; red; intros.
  inv CS. apply readonly_refl.
  destruct CS as [cc [mm [CS CSN]]].
  specialize (rtl_coop_forward _ _ _ _ _ _ CS). intros.
  apply rtl_coop_readonly in CS; trivial.
  eapply readonly_trans. eapply CS. eassumption.
  eapply IHn; try eassumption.
  eapply mem_respects_readonly_forward'; eassumption.
Qed.

Lemma rtl_coop_plus_readonly hf g: forall c m c' m'
            (CS: corestep_plus (rtl_coop_sem hf) g c m c' m')
            (MRR: mem_respects_readonly g m),
         RDOnly_fwd m m' (ReadOnlyBlocks g).
Proof. intros.
  destruct CS. eapply rtl_coopN_readonly; eassumption.
Qed.
 
Lemma rtl_coop_star_readonly hf g: forall c m c' m'
            (CS: corestep_star (rtl_coop_sem hf) g c m c' m')
            (MRR: mem_respects_readonly g m),
         RDOnly_fwd m m' (ReadOnlyBlocks g).
Proof. intros.
  destruct CS. eapply rtl_coopN_readonly; eassumption.
Qed.
 *)
*)
