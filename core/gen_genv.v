(* A generalization of CompCert's global environments. *)
Require Import Globalenvs.
Require Import AST.
Require Import Values.
Require Import Integers.
Require Import ZArith.
Require Import Floats.

Class GlobalEnv {G V : Type} := 
  { find_symbol   : (* should we parameterize by ident as well? *) 
                    G -> ident -> option V;
    invert_symbol : G -> V -> option ident }.

Instance GenvGlobal F V : @GlobalEnv (Genv.t F V) val :=
  { find_symbol := fun ge i => option_map (fun bf => Vptr bf Int.zero) 
                               (Genv.find_symbol ge i);
    invert_symbol := fun ge v => match v with
      | Vptr bf ofs => if Int.eq ofs Int.zero then Genv.invert_symbol ge bf
                       else None
      | _ => None
      end }.

Class TypeSys {T V : Type} :=
  { has_type : V -> T -> bool; main_typ : T }.
(* Can't make a CompCert instance of this here because it needs 
   val_has_type_func from val_casted, which imports semantics. The specific
   function doesn't actually depend on semantics, though, so this is fixable. *)


Record g_signature (T : Type) : Type := {
  g_sig_args: list T;
  g_sig_res: T
}.
Arguments g_sig_args {T} _.
Arguments g_sig_res {T} _.

(* When should a typeclass be used, and when is a record better? *)
Definition g_sig_of_sig (sg : signature) := 
  {| g_sig_args := sig_args sg; g_sig_res := proj_sig_res sg |}.
(* Does the result type need to be an option? None seems to be coerced
   to int in the CompCert version. *)

(* External functions with generalized signatures. 
   These are still tied to CompCert memory_chunks for now. *)
Inductive g_external_function (T : Type) : Type :=
  | GEF_external (name: ident) (sg: g_signature T)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | GEF_builtin (name: ident) (sg: g_signature T)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | GEF_vload (chunk: memory_chunk)
     (** A volatile read operation.  If the adress given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | GEF_vstore (chunk: memory_chunk)
     (** A volatile store operation.   If the adress given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | GEF_vload_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile load operation from a global variable. 
         Specialized version of [EF_vload]. *)
  | GEF_vstore_global (chunk: memory_chunk) (id: ident) (ofs: int)
     (** A volatile store operation in a global variable. 
         Specialized version of [EF_vstore]. *)
  | GEF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | GEF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | GEF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | GEF_annot (text: ident) (targs: list (g_annot_arg T))
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | GEF_annot_val (text: ident) (targ: T)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | GEF_inline_asm (text: ident)
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)

with g_annot_arg (T : Type) : Type :=
  | GAA_arg (ty: T)
  | GAA_int (n: int)
  | GAA_float (n: float).

Definition gsig_to_sig (gsg : g_signature typ) : signature :=
  {| sig_args := g_sig_args gsg; sig_res := Some (g_sig_res gsg) |}.

Definition gaa_to_aa gaa :=
  match gaa with 
  | GAA_arg ty => AA_arg ty
  | GAA_int n => AA_int n
  | GAA_float n => AA_float n
  end.

Definition gef_to_ef (gef : g_external_function typ) : external_function :=
  match gef with
  | GEF_external name sg => EF_external name (gsig_to_sig sg)
  | GEF_builtin name sg => EF_builtin name (gsig_to_sig sg)
  | GEF_vload chunk => EF_vload chunk
  | GEF_vstore chunk => EF_vstore chunk
  | GEF_vload_global chunk id ofs => EF_vload_global chunk id ofs
  | GEF_vstore_global chunk id ofs => EF_vstore_global chunk id ofs
  | GEF_malloc => EF_malloc
  | GEF_free => EF_free
  | GEF_memcpy sz al => EF_memcpy sz al
  | GEF_annot text targs => EF_annot text (List.map gaa_to_aa targs)
  | GEF_annot_val text targ => EF_annot_val text targ
  | GEF_inline_asm text => EF_inline_asm text
  end.
