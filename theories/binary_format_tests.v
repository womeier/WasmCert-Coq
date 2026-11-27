(** Tests for the binary parser. **)
From Stdlib Require Import Strings.Byte ZArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
                         binary_uleb128_printer datatypes_properties check_toks.

Open Scope string_scope.
Import Stdlib.Strings.String.StringSyntax.
Open Scope list_scope.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton BI_unreachable.
Proof. vm_compute. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton BI_nop.
Proof. vm_compute. reflexivity. Qed.

(** Final tail-call opcodes. Internal indirect operands are table/type, whereas
    the wire format is type/table. Distinct multi-byte indices catch swaps. *)
Lemma return_call_opcode : forall x,
    binary_of_be (BI_return_call x) = x12 :: binary_of_tailidx x.
Proof. reflexivity. Qed.

Lemma return_call_indirect_opcode : forall table type,
    binary_of_be (BI_return_call_indirect table type) =
      x13 :: binary_of_tailidx type ++ binary_of_tailidx table.
Proof. reflexivity. Qed.

Lemma return_call_multibyte :
    run_parse_be (x12 :: x80 :: x01 :: nil) = Some (BI_return_call 128%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_multibyte :
    run_parse_be (x13 :: x80 :: x01 :: x81 :: x02 :: nil) =
      Some (BI_return_call_indirect 257%N 128%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_u32_max_roundtrip :
    run_parse_be (binary_of_be (BI_return_call 4294967295%N)) =
      Some (BI_return_call 4294967295%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_roundtrip :
    run_parse_be (binary_of_be (BI_return_call_indirect 257%N 128%N)) =
      Some (BI_return_call_indirect 257%N 128%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_padded_index :
    run_parse_be (x12 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil) =
      Some (BI_return_call 0%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_canonical_index_64 :
    binary_of_be (BI_return_call 64%N) = x12 :: x40 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_legacy_padded_index_64 :
    run_parse_be (x12 :: xc0 :: x00 :: nil) = Some (BI_return_call 64%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_truncated :
    run_parse_be (x12 :: x80 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_missing_table :
    run_parse_be (x13 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_index_overflow :
    run_parse_be (x12 :: xff :: xff :: xff :: xff :: x10 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_index_overlong :
    run_parse_be (x12 :: x80 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_trailing_bytes :
    run_parse_be (x12 :: x00 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_u32_max_roundtrip :
    run_parse_be
      (binary_of_be (BI_return_call_indirect 4294967295%N 4294967295%N)) =
      Some (BI_return_call_indirect 4294967295%N 4294967295%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_padded_indices :
    run_parse_be
      (x13 :: x80 :: x80 :: x80 :: x80 :: x00 ::
       x81 :: x80 :: x80 :: x80 :: x00 :: nil) =
      Some (BI_return_call_indirect 1%N 0%N).
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_type_overflow :
    run_parse_be
      (x13 :: xff :: xff :: xff :: xff :: x10 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma return_call_indirect_table_overflow :
    run_parse_be
      (x13 :: x00 :: xff :: xff :: xff :: xff :: x10 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

(** An example program. **)
Definition test :=
  BI_if (BT_valtype None) (BI_testop T_i64 TO_eqz :: nil) (BI_testop T_i64 TO_eqz :: nil).

(** Its byte representation. **)
Definition test_bytes : list Byte.byte :=
  x04 :: x40
  :: x50
  :: x05
  :: x50
  :: x0b
  :: x0b
  :: nil.

(** It is possible to display lists of bytes in a nice way using the following command:
[[
Compute hex_small_no_prefix_of_bytes test_bytes.
]]
**)

Lemma text_binary_correct : binary_of_expr (test :: nil) = test_bytes.
Proof. vm_compute. reflexivity. Qed.

Lemma text_parse_correct : run_parse_expr test_bytes = Some (test :: nil).
Proof. vm_compute. reflexivity. Qed.

(** It is possible to display programs in a nice way using the following command:
[[
Compute option_map pp_basic_instructions (run_parse_expr test_bytes).
]]
**)

(** Example from Wikipedia: https://en.wikipedia.org/wiki/WebAssembly#Code_representation
  This is the representation of a factorial function. **)
Definition test_wikipedia_byte : list Byte.byte :=
  x20 :: x00
  :: x50
  :: x04 :: x7e
  :: x42 :: x01
  :: x05
  :: x20 :: x00
  :: x20 :: x00
  :: x42 :: x01
  :: x7d
  :: x10 :: x00
  :: x7e
  :: x0b
  :: nil.

Definition test_wikipedia :=
  (BI_local_get 0%N
   :: BI_testop T_i64 TO_eqz
   :: BI_if (BT_valtype (Some (T_num T_i64)))
        (BI_const_num (VAL_int64 Wasm_int.Int64.one) :: nil)
        (BI_local_get 0%N
         :: BI_local_get 0%N
         :: BI_const_num (VAL_int64 Wasm_int.Int64.one)
         :: BI_binop T_i64 (Binop_i BOI_sub)
         :: BI_call 0%N
         :: BI_binop T_i64 (Binop_i BOI_mul) :: nil) :: nil).

Lemma test_wikipedia_correct : run_parse_bes test_wikipedia_byte = Some test_wikipedia.
Proof. vm_compute. reflexivity. Qed.

Definition empty_module := {|
  mod_types := nil;
  mod_funcs := nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma empty_module_round_trip : run_parse_module (binary_of_module empty_module) = Some empty_module.
Proof. vm_compute. reflexivity. Qed.

Definition module_type := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs := nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_type_round_trip :
  run_parse_module (binary_of_module module_type) = Some module_type.
Proof. vm_compute. reflexivity. Qed.

Definition module_type_fun := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_type_fun_round_trip :
  run_parse_module (binary_of_module module_type_fun) = Some module_type_fun.
Proof. vm_compute. reflexivity. Qed.

Definition module_42 := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 42))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_42_round_trip :
  run_parse_module (binary_of_module module_42) = Some module_42.
Proof. vm_compute. reflexivity. Qed.

Definition module_tail_calls := {|
  mod_types := mod_types module_42;
  mod_funcs := mod_funcs module_42 ++
    {| modfunc_type := 0%N; modfunc_locals := nil;
       modfunc_body := BI_return_call 0%N :: nil |} ::
    {| modfunc_type := 0%N; modfunc_locals := nil;
       modfunc_body :=
         BI_const_num (VAL_int32 Wasm_int.Int32.zero) ::
         BI_return_call_indirect 0%N 0%N :: nil |} :: nil;
  mod_tables :=
    Build_module_table
      (Build_table_type (Build_limits 1%N None) T_funcref) :: nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma module_tail_calls_round_trip :
  run_parse_module (binary_of_module module_tail_calls) = Some module_tail_calls.
Proof. vm_compute. reflexivity. Qed.

Definition module_42_exported := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 42))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := nil;
  mod_mems := nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := cons {| modexp_name := String.list_byte_of_string "hello"; modexp_desc := MED_func 0%N; |} nil;
|}.

Lemma module_42_exported_round_trip :
  run_parse_module (binary_of_module module_42_exported) = Some module_42_exported.
Proof. vm_compute. reflexivity. Qed.

Definition module_tableops := {|
  mod_types := cons (Tf nil (cons (T_num T_i32) nil)) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := (cons (Build_module_table (Build_table_type (Build_limits 0%N (Some 4%N)) T_funcref)) nil);
  mod_mems := nil;
                               mod_globals := nil;
  mod_elems := (cons (Build_module_element T_funcref (cons (cons (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1)))) nil) nil) (ME_active 0%N (cons (BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1)))) nil))) nil);
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := cons {| modexp_name := String.list_byte_of_string "hello"; modexp_desc := MED_func 0%N; |} nil;
|}.

Lemma module_tableops_exported_round_trip :
  run_parse_module (binary_of_module module_tableops) = Some module_tableops.
Proof. vm_compute. reflexivity. Qed.
