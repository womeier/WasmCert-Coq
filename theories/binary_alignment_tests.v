(** Phase-classification evidence for the five failing pinned align.wast cases.
    Wasm 2.0 (spec tag opam-2.0.2, commit 95fa5b3261820ac411e0fd81392ee95e11811fff)
    encodes memarg as two u32 values. These modules therefore decode, but fail
    the natural-alignment validation bound. No assertion in the original suite
    is changed by these proofs. The Wasm 3.0 memory-index flag grammar is a
    separate integration obligation. *)
From Stdlib Require Import Strings.Byte NArith List.
From Wasm Require Import binary_format_parser binary_format_printer instantiation_func
  datatypes_properties.

Definition alignment_module (align : N) := {|
  mod_types := Tf nil nil :: nil;
  mod_funcs :=
    {| modfunc_type := 0%N; modfunc_locals := nil;
       modfunc_body :=
         BI_const_num (VAL_int32 Wasm_int.Int32.zero) ::
         BI_load T_i32 None
           {| memarg_offset := 0%N; memarg_align := align |} ::
         BI_drop :: nil |} :: nil;
  mod_tables := nil;
  mod_mems := Build_module_mem (Build_limits 1%N None) :: nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

(** Exact bytes of pinned align.wast lines 891, 910, 929, 948 and 967.
    Only the single-byte alignment/flags immediate differs between cases. *)
Definition alignment_wire (flags : Byte.byte) :=
  x00 :: x61 :: x73 :: x6d :: x01 :: x00 :: x00 :: x00 ::
  x01 :: x04 :: x01 :: x60 :: x00 :: x00 ::
  x03 :: x02 :: x01 :: x00 ::
  x05 :: x03 :: x01 :: x00 :: x01 ::
  x0a :: x0a :: x01 :: x08 :: x00 :: x41 :: x00 :: x28 ::
  flags :: x00 :: x1a :: x0b :: nil.

Lemma alignment_wire_cases_decode_but_are_invalid :
    List.Forall
      (fun '(align, flags) =>
        run_parse_module (alignment_wire flags) = Some (alignment_module align) /\
        fst (module_type_checker (alignment_module align)) = None)
      ((32%N, x20) :: (33%N, x21) :: (63%N, x3f) ::
       (64%N, x40) :: (65%N, x41) :: nil).
Proof.
  do 5 (apply List.Forall_cons; [split; vm_compute; reflexivity |]).
  constructor.
Qed.

Lemma alignment_cases_decode_but_are_invalid :
    List.Forall
      (fun align =>
        run_parse_module (binary_of_module (alignment_module align)) =
          Some (alignment_module align) /\
        fst (module_type_checker (alignment_module align)) = None)
      (32%N :: 33%N :: 63%N :: 64%N :: 65%N :: nil).
Proof.
  do 5 (apply List.Forall_cons; [split; vm_compute; reflexivity |]).
  constructor.
Qed.
