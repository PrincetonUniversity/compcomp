(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Wfsimpl.
Require Nan.
Require AST.
Require Iteration.
Require Floats.
Require SelectLong.
Require RTLgen.
Require Inlining.
Require ConstpropOp.
Require Constprop.
Require Tailcall.
Require Allocation.
Require Compiler.
Require CompositionalCompiler.

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* Wfsimpl *)
Extraction Inline Wfsimpl.Fix Wfsimpl.Fixm.

(* Floats *)
Extract Constant Floats.Float.default_pl => "Nan.default_pl".
Extract Constant Floats.Float.choose_binop_pl => "Nan.choose_binop_pl".

(* AST *)
Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

(* Memdata *)
Extract Constant Memdata.big_endian => "Memdataaux.big_endian".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Iteration *)

Extract Constant Iteration.GenIter.iterate =>
  "let rec iter f a =
     match f a with Coq_inl b -> Some b | Coq_inr a' -> iter f a'
   in iter".

(* Selection *)

Extract Constant SelectLong.get_helper =>
  "fun ge s sg ->
     Errors.OK (Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s))".
Extract Constant SelectLong.get_builtin =>
  "fun s sg ->
     Errors.OK (Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s))".

(* RTLgen *)
Extract Constant RTLgen.compile_switch => "RTLgenaux.compile_switch".
Extract Constant RTLgen.more_likely => "RTLgenaux.more_likely".
Extraction Inline RTLgen.ret RTLgen.error RTLgen.bind RTLgen.bind2.

(* Inlining *)
Extract Inlined Constant Inlining.should_inline => "Inliningaux.should_inline".
Extraction Inline Inlining.ret Inlining.bind.

(* Constprop *)
Extract Constant ConstpropOp.propagate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 1".
Extract Constant Constprop.generate_float_constants =>
  "fun _ -> !Clflags.option_ffloatconstprop >= 2".

(* Tailcall *)
Extract Constant Tailcall.eliminate_tailcalls =>
  "fun _ -> !Clflags.option_ftailcalls".

(* Allocation *)
Extract Constant Allocation.regalloc => "Regalloc.regalloc".

(* Linearize *)
Extract Constant Linearize.enumerate_aux => "Linearizeaux.enumerate_aux".

(* SimplExpr *)
Extract Constant SimplExpr.first_unused_ident => "Camlcoq.first_unused_ident".
Extraction Inline SimplExpr.ret SimplExpr.error SimplExpr.bind SimplExpr.bind2.

(* I64Helpers *)
Extract Constant I64Helpers.get_helper =>
  "fun s sg ->
     Errors.OK (Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s))".
Extract Constant I64Helpers.get_builtin =>
  "fun s sg ->
     Errors.OK (Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s))".

(* CompositionalCompiler *)
Extract Constant CompositionalCompiler.print_Clight => "PrintClight.print_if".
Extract Constant CompositionalCompiler.print_Cminor => "PrintCminor.print_if".
Extract Constant CompositionalCompiler.print_RTL => "PrintRTL.print_rtl".
Extract Constant CompositionalCompiler.print_RTL_tailcall => "PrintRTL.print_tailcall".
(*Extract Constant CompositionalCompiler.print_RTL_inline => "PrintRTL.print_inlining".*)
(*Extract Constant CompositionalCompiler.print_RTL_constprop => "PrintRTL.print_constprop".*)
(*Extract Constant CompositionalCompiler.print_RTL_cse => "PrintRTL.print_cse".*)
Extract Constant CompositionalCompiler.print_LTL => "PrintLTL.print_if".
Extract Constant CompositionalCompiler.print_Mach => "PrintMach.print_if".
Extract Constant CompositionalCompiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".
(*Extraction Inline CompositionalCompiler.apply_total CompositionalCompiler.apply_partial.*)

(* Processor-specific extraction directives *)

Require Asm.
Require Asm_comp.

(*Load extractionMachdep.*)

(* Additional extraction directives specific to the IA32 port 
(originally from ia32/extractionMachdep.v, copied here temporarily. *)

Require SelectOp.

(* SelectOp *)

Extract Constant SelectOp.symbol_is_external =>
  "fun id -> Configuration.system = ""macosx"" && C2C.atom_is_extern id".

(* END additional directives *)

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Cutting the dependancy to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

(* Needed in Coq 4.00 to avoid problems with Function definitions. *)
Set Extraction AccessOpaque.

(* Go! *)
Cd "extraction".
(* Recursive Extraction Library CompositionalCompiler. *)
Separate Extraction
   CompositionalCompiler.transf_c_program CompositionalCompiler.transf_cminor_program
   Cexec.do_initial_state Cexec.do_step Cexec.at_final_state
   Initializers.transl_init Initializers.constval
   Csyntax.Eindex Csyntax.Epreincr
   Conventions1.dummy_int_reg Conventions1.dummy_float_reg
   RTL.instr_defs RTL.instr_uses
   Machregs.mregs_for_operation Machregs.mregs_for_builtin
   Machregs.two_address_op
   Nan.default_pl Nan.choose_binop_pl
   Coqlib.sum_left_map.
