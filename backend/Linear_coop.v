Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Import LTL.
Require Import Conventions.

Require Import Linear.

Require Import semantics.
Require Import semantics_lemmas.
Require Import val_casted.
Require Import BuiltinEffects.

Inductive load_frame: Type :=
| mk_load_frame:
    forall (rs0: Linear.locset)  (**r location state at program entry *)
           (f: Linear.function), (**r initial function *)
    load_frame.

(** Linear execution states. *)

Inductive Linear_core: Type :=
  | Linear_State:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (f: Linear.function)            (**r function currently executing *)
             (sp: val)                       (**r stack pointer *)
             (c: Linear.code)                (**r current program point *)
             (rs: Linear.locset)             (**r location state *)
             (lf: load_frame),           (**r location state at program entry *)
      Linear_core
  (*A dummy corestate, to facilitate the stacking proof.*)
  | Linear_CallstateIn:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (f: Linear.fundef)              (**r function to call *)
             (rs: Linear.locset)             (**r location state at point of call *)
             (lf: load_frame),           (**r location state at program entry *)
      Linear_core
  | Linear_Callstate:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (f: Linear.fundef)              (**r function to call *)
             (rs: Linear.locset)             (**r location state at point of call *)
             (lf: load_frame),           (**r location state at program entry *)
      Linear_core
  | Linear_Returnstate:
      forall (stack: list Linear.stackframe) (**r call stack *)
             (retty: option typ)      (**r optional return register int-floatness *)
             (rs: Linear.locset)             (**r location state at point of return *)
             (lf: load_frame),           (**r location state at program entry *)
      Linear_core.

Definition call_regs' (callee : LTL.locset) (l : loc) :=
  match l with
    | R r => callee (R r)
    | S Local _ _ => Vundef
    | S Outgoing ofs ty => callee (S Incoming ofs ty)
    | S Incoming _ _ => Vundef
  end.

Lemma call_regs_regs' callee ofs ty : 
  call_regs' (call_regs callee) (S Outgoing ofs ty) = callee (S Outgoing ofs ty). 
Proof. simpl; auto. Qed.

(** [parent_locset0 ls0 cs] returns the mapping of values for locations
    of the caller function, bottoming out with locset ls0. *)
Definition parent_locset0 (ls0: locset) (stack: list Linear.stackframe) : locset :=
  match stack with
  | nil => call_regs' ls0
  | Linear.Stackframe f sp ls c :: stack' => ls
  end.

Section LINEAR_MEM.
Variable hf : I64Helpers.helper_functions.

Inductive Linear_step (ge:genv): Linear_core -> mem -> Linear_core -> mem -> Prop :=
  | lin_exec_Lgetstack:
      forall s f sp sl ofs ty dst b rs m rs' lf,
      rs' = Locmap.set (R dst) (rs (S sl ofs ty)) (undef_regs (destroyed_by_getstack sl) rs) ->
      Linear_step ge (Linear_State s f sp (Lgetstack sl ofs ty dst :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_exec_Lsetstack:
      forall s f sp src sl ofs ty b rs m rs' lf,
      rs' = Locmap.set (S sl ofs ty) (rs (R src)) (undef_regs (destroyed_by_setstack ty) rs) ->
      Linear_step ge (Linear_State s f sp (Lsetstack src sl ofs ty :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_exec_Lop:
      forall s f sp op args res b rs m v rs' lf,
      eval_operation ge sp op (reglist rs args) m = Some v ->
      rs' = Locmap.set (R res) v (undef_regs (destroyed_by_op op) rs) ->
      Linear_step ge (Linear_State s f sp (Lop op args res :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_exec_Lload:
      forall s f sp chunk addr args dst b rs m a v rs' lf,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.loadv chunk m a = Some v ->
      rs' = Locmap.set (R dst) v (undef_regs (destroyed_by_load chunk addr) rs) ->
      Linear_step ge (Linear_State s f sp (Lload chunk addr args dst :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_exec_Lstore:
      forall s f sp chunk addr args src b rs m m' a rs' lf,
      eval_addressing ge sp addr (reglist rs args) = Some a ->
      Mem.storev chunk m a (rs (R src)) = Some m' ->
      rs' = undef_regs (destroyed_by_store chunk addr) rs ->
      Linear_step ge (Linear_State s f sp (Lstore chunk addr args src :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m'
  | lin_exec_Lcall:
      forall s f sp sig ros b rs m f' lf,
      find_function ge ros rs = Some f' ->
      sig = funsig f' ->
      Linear_step ge (Linear_State s f sp (Lcall sig ros :: b) rs lf) m
        (Linear_Callstate (Stackframe f sp rs b:: s) f' rs lf) m
  | lin_exec_Ltailcall:
      forall s f stk sig ros b rs m rs' f' m' rs0 f0,
      rs' = return_regs (parent_locset0 rs0 s) rs ->
      find_function ge ros rs' = Some f' ->
      sig = funsig f' ->
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Linear_step ge (Linear_State s f (Vptr stk Int.zero) (Ltailcall sig ros :: b) rs (mk_load_frame rs0 f0)) m
        (Linear_Callstate s f' rs' (mk_load_frame rs0 f0)) m'
  | lin_exec_Lbuiltin:
      forall s f sp rs m ef args res b t vl rs' m' lf,
      external_call' ef ge (reglist rs args) m t vl m' ->
      ~ observableEF hf ef ->
      rs' = Locmap.setlist (map R res) vl (undef_regs (destroyed_by_builtin ef) rs) ->
      Linear_step ge (Linear_State s f sp (Lbuiltin ef args res :: b) rs lf) m
         (Linear_State s f sp b rs' lf) m'

(* annotations are observable, so now handled by atExternal
  | lin_exec_Lannot:
      forall s f sp rs m ef args b t v m',
      external_call' ef ge (map rs args) m t v m' ->
      Linear_step (Linear_State s f sp (Lannot ef args :: b) rs) m
         (Linear_State s f sp b rs) m'*)

  | lin_exec_Llabel:
      forall s f sp lbl b rs m lf,
      Linear_step ge (Linear_State s f sp (Llabel lbl :: b) rs lf) m
        (Linear_State s f sp b rs lf) m
  | lin_exec_Lgoto:
      forall s f sp lbl b rs m b' lf,
      find_label lbl f.(fn_code) = Some b' ->
      Linear_step ge (Linear_State s f sp (Lgoto lbl :: b) rs lf) m
        (Linear_State s f sp b' rs lf) m
  | lin_exec_Lcond_true:
      forall s f sp cond args lbl b rs m rs' b' lf,
      eval_condition cond (reglist rs args) m = Some true ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      find_label lbl f.(fn_code) = Some b' ->
      Linear_step ge (Linear_State s f sp (Lcond cond args lbl :: b) rs lf) m
        (Linear_State s f sp b' rs' lf) m
  | lin_exec_Lcond_false:
      forall s f sp cond args lbl b rs m rs' lf,
      eval_condition cond (reglist rs args) m = Some false ->
      rs' = undef_regs (destroyed_by_cond cond) rs ->
      Linear_step ge (Linear_State s f sp (Lcond cond args lbl :: b) rs lf) m
        (Linear_State s f sp b rs' lf) m
  | lin_exec_Ljumptable:
      forall s f sp arg tbl b rs m n lbl b' rs' lf,
      rs (R arg) = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      find_label lbl f.(fn_code) = Some b' ->
      rs' = undef_regs (destroyed_by_jumptable) rs ->
      Linear_step ge (Linear_State s f sp (Ljumptable arg tbl :: b) rs lf) m
        (Linear_State s f sp b' rs' lf) m
  | lin_exec_Lreturn:
      forall s f stk b rs m m' rs0 f0,
      let lf := mk_load_frame rs0 f0 in 
      Mem.free m stk 0 f.(fn_stacksize) = Some m' ->
      Linear_step ge (Linear_State s f (Vptr stk Int.zero) (Lreturn :: b) rs lf) m
        (Linear_Returnstate s (sig_res (fn_sig f)) (return_regs (parent_locset0 rs0 s) rs) lf) m'
  (*A dummy corestep, to facilitate the stacking proof.*)
  | lin_exec_function_internal0:
      forall s f rs m rs0 f0,
      Linear_step ge (Linear_CallstateIn s (Internal f) rs (mk_load_frame rs0 f0)) m
                  (Linear_Callstate s (Internal f) rs (mk_load_frame (call_regs rs0) f0)) m
  | lin_exec_function_internal:
      forall s f rs m rs' m' stk lf,
      Mem.alloc m 0 f.(fn_stacksize) = (m', stk) ->
      rs' = undef_regs destroyed_at_function_entry (call_regs rs) ->
      Linear_step ge (Linear_Callstate s (Internal f) rs lf) m
        (Linear_State s f (Vptr stk Int.zero) f.(fn_code) rs' lf) m'

  | lin_exec_function_external:
      forall s ef args res rs1 rs2 m t m' lf
      (OBS: EFisHelper hf ef),
      args = map rs1 (loc_arguments (ef_sig ef)) ->
      external_call' ef ge args m t res m' ->
      rs2 = Locmap.setlist (map R (loc_result (ef_sig ef))) res rs1 ->
      Linear_step ge (Linear_Callstate s (External ef) rs1 lf) m
          (Linear_Returnstate s (sig_res (ef_sig ef)) rs2 lf) m'

  | lin_exec_return:
      forall s f sp lf c rs retty m rs_init,
      Linear_step ge (Linear_Returnstate (Stackframe f sp lf c :: s) retty rs rs_init) m
         (Linear_State s f sp c rs rs_init) m.

Definition init_locset tys args :=
  Locmap.setlist (loc_arguments_rec tys 0) (encode_longs tys args) (Locmap.init Vundef).

Definition Linear_initial_core (ge:genv) (v: val) (args:list val): 
           option Linear_core :=match v with
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
                     then let ls0 := init_locset (sig_args (funsig f)) args 
                          in Some (Linear_CallstateIn nil f ls0 (mk_load_frame ls0 fi))
                     else None
                    | External _ => None
                     end
               end
          else None
     | _ => None
    end.
(*Compcert's original definition is for initial PROGRAM states
Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = mksignature nil (Some Tint) ->
      initial_state p (Callstate nil f (Locmap.init Vundef) m0).
*)

(*Maybe generalize to other types?*)
Definition Linear_halted (q : Linear_core): option val :=
    match q with Linear_Returnstate nil _ rs (mk_load_frame _ f) => 
      match sig_res (fn_sig f) with
      (*Return Tlong, which must be decoded*)
      | Some Tlong => 
           match loc_result (mksignature nil (Some Tlong)) with
             | nil => None
             | r1 :: r2 :: nil => 
                 match decode_longs (Tlong::nil) (rs (R r1)::rs (R r2)::nil) with
                   | v :: nil => Some v
                   | _ => None
                 end
             | _ => None
           end

      (*Return a value of any other typ*)
      | Some retty => 
           match loc_result (mksignature nil (Some retty)) with
            | nil => None
            | r :: TL => match TL with 
                           | nil => Some (rs (R r))
                           | _ :: _ => None
                         end
           end

      (*Return Tvoid - modeled as integer return*)
      | None => Some (rs (R AX))
      end 
    | _ => None end.

(*Original had this:
Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall rs m r retcode,
      loc_result (mksignature nil (Some Tint)) = r :: nil ->
      rs (R r) = Vint retcode ->
      final_state (Returnstate nil rs m) retcode.
*)

Definition Linear_at_external (c: Linear_core) : option (external_function * signature * list val) :=
  match c with
  | Linear_State _ _ _ _ _ _ => None
  | Linear_Callstate s f rs _ => 
      match f with
        | Internal f => None
        | External ef => 
            if observableEF_dec hf ef
            then Some (ef, ef_sig ef, decode_longs (sig_args (ef_sig ef)) 
                                   (map rs (loc_arguments (ef_sig ef))))
            else None
      end
  | Linear_CallstateIn _ _ _ _ => None
  | Linear_Returnstate _ _ _ _ => None
 end.

Definition Linear_after_external (vret: option val) (c: Linear_core) : option Linear_core :=
  match c with 
    | Linear_Callstate s f rs lf => 
      match f with
        | Internal f => None
        | External ef => 
          match vret with
            | None => Some (Linear_Returnstate s (sig_res (ef_sig ef))
                             (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                               (encode_long (sig_res (ef_sig ef)) Vundef) rs) lf)
            | Some v => Some (Linear_Returnstate s (sig_res (ef_sig ef))
                               (Locmap.setlist (map R (loc_result (ef_sig ef))) 
                                 (encode_long (sig_res (ef_sig ef)) v) rs) lf)
          end
      end
    | _ => None
  end.

Lemma Linear_corestep_not_at_external ge m q m' q':
      Linear_step ge q m q' m' -> Linear_at_external q = None.
  Proof. intros. inv H; try reflexivity. 
  simpl. destruct (observableEF_dec hf ef); simpl; trivial. 
  exfalso. eapply EFhelpers; eassumption. 
Qed.

Lemma Linear_corestep_not_halted ge m q m' q' :
       Linear_step ge q m q' m' -> Linear_halted q = None.
  Proof. intros. inv H; reflexivity. Qed.
    
Lemma Linear_at_external_halted_excl q:
      Linear_at_external q = None \/ Linear_halted q = None.
   Proof. intros. destruct q; auto. Qed.

Lemma Linear_after_at_external_excl retv q q':
      Linear_after_external retv q = Some q' -> Linear_at_external q' = None.
  Proof. intros.
       destruct q; simpl in *; try inv H.
       destruct f; try inv H1; simpl.
         destruct retv; inv H0; simpl; trivial.
  Qed.

Definition Linear_core_sem : CoreSemantics genv Linear_core mem.
Proof.
  eapply (@Build_CoreSemantics _ _ _ 
           Linear_initial_core
           Linear_at_external
           Linear_after_external
           Linear_halted
           Linear_step).
    apply Linear_corestep_not_at_external.
    apply Linear_corestep_not_halted.
    apply Linear_at_external_halted_excl.
Defined.

Program Definition Linear_memsem : @MemSem genv Linear_core.
Proof.
eapply Build_MemSem with (csem := Linear_core_sem).
  intros.
  destruct CS; try apply mem_step_refl.
  + destruct a; inv H0. eapply mem_step_store; eassumption.
  + eapply mem_step_free; eassumption.
  + inv H. eapply extcall_mem_step; eassumption.
  + eapply mem_step_free; eassumption.
  + eapply mem_step_alloc; eassumption.
  + inv H0. eapply extcall_mem_step; eassumption.
Defined.

End LINEAR_MEM.