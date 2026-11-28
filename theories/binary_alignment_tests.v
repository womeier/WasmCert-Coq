(** Exact-byte evidence for the five stale malformed expectations in pinned
    align.wast. Final Wasm 3.0 Bmemarg accepts flags <64 directly and 64..127
    with an explicit memory index, followed by a u64 offset. In the latter two
    cases the old drop byte is now the offset: validation fails for a leftover
    stack value, not alignment. Original suite assertions remain unchanged. *)
From Stdlib Require Import Strings.Byte NArith List.
From Wasm Require Import binary_format_parser binary_format_printer instantiation_func
  datatypes_properties.

Definition alignment_module_at (align offset : N) (drop : bool) := {|
  mod_types := Tf nil nil :: nil;
  mod_funcs :=
    {| modfunc_type := 0%N; modfunc_locals := nil;
       modfunc_body :=
         BI_const_num (VAL_int32 Wasm_int.Int32.zero) ::
         BI_load T_i32 None
            (Build_memarg offset align 0%N) ::
          (if drop then BI_drop :: nil else nil) |} :: nil;
  mod_tables := nil;
  mod_mems := Build_module_mem (Build_limits 1%N None) :: nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Definition alignment_module (align : N) := alignment_module_at align 0%N true.

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
      (fun '(align, offset, drop, flags) =>
        run_parse_module (alignment_wire flags) =
          Some (alignment_module_at align offset drop) /\
        fst (module_type_checker (alignment_module_at align offset drop)) = None)
      ((32%N, 0%N, true, x20) :: (33%N, 0%N, true, x21) ::
       (63%N, 0%N, true, x3f) ::
       (0%N, 26%N, false, x40) :: (1%N, 26%N, false, x41) :: nil).
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
      (32%N :: 33%N :: 63%N :: nil).
Proof.
  do 3 (apply List.Forall_cons; [split; vm_compute; reflexivity |]).
  constructor.
Qed.

Lemma alignment_reserved_flags_are_malformed :
    List.Forall
      (fun flags => run_parse_bes (x28 :: List.app flags (x00 :: nil)) = None)
      ((x80 :: x01 :: nil) :: (x81 :: x01 :: nil) ::
       (xff :: x7f :: nil) :: nil).
Proof.
  do 3 (apply List.Forall_cons; [vm_compute; reflexivity |]).
  constructor.
Qed.
