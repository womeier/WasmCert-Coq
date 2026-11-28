(** Tests for the binary parser. **)
From Stdlib Require Import Strings.Byte ZArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
                         datatypes_properties check_toks.

Open Scope string_scope.
Import Stdlib.Strings.String.StringSyntax.
Open Scope list_scope.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton BI_unreachable.
Proof. vm_compute. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton BI_nop.
Proof. vm_compute. reflexivity. Qed.

Lemma test_ref_as_non_null :
  run_parse_bes (xd4 :: nil) = Some (BI_ref_as_non_null :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma print_ref_as_non_null :
  binary_of_expr (BI_ref_as_non_null :: nil) = xd4 :: x0b :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma test_call_ref :
  run_parse_bes (x14 :: x00 :: nil) = Some (BI_call_ref 0%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma test_return_call_ref :
  run_parse_bes (x15 :: x01 :: nil) = Some (BI_return_call_ref 1%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma test_call_ref_noncanonical_index :
  run_parse_bes (x14 :: x80 :: x00 :: nil) = Some (BI_call_ref 0%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma test_call_ref_truncated_index :
  run_parse_bes (x14 :: x80 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma test_call_ref_overflow_index :
  run_parse_bes (x14 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma test_return_call_ref_max_index :
  run_parse_bes (x15 :: xff :: xff :: xff :: xff :: x0f :: nil) =
    Some (BI_return_call_ref 4294967295%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma print_call_refs :
  binary_of_expr (BI_call_ref 0%N :: BI_return_call_ref 1%N :: nil) =
    x14 :: x00 :: x15 :: x01 :: x0b :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma print_nullable_indexed_reference :
  binary_of_reference_type (Ref_type true (HT_type 64%N)) =
    x63 :: xc0 :: x00 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma print_non_null_indexed_reference :
  binary_of_reference_type (Ref_type false (HT_type 0%N)) =
    x64 :: x00 :: nil.
Proof. vm_compute. reflexivity. Qed.

(* Exhaustive bounded-domain correctness for the actual parser entry point,
   not a replacement decoder: a single-byte immediate has exactly 128 valid
   encodings; all continuation bytes are rejected when the input ends here.
   General multi-byte LEB128/parser correctness remains a separate obligation. *)
Lemma parse_reference_call_single_byte (tail : bool) (b : Byte.byte) :
  run_parse_bes ((if tail then x15 else x14) :: b :: nil) =
    if N.ltb (Byte.to_N b) 128%N then
      Some ((if tail then BI_return_call_ref (Byte.to_N b)
             else BI_call_ref (Byte.to_N b)) :: nil)
    else None.
Proof. destruct tail, b; vm_compute; reflexivity. Qed.

Lemma parse_br_on_non_null_single_byte (b : Byte.byte) :
  run_parse_bes (xd6 :: b :: nil) =
    if N.ltb (Byte.to_N b) 128%N then
      Some (BI_br_on_non_null (Byte.to_N b) :: nil)
    else None.
Proof. destruct b; vm_compute; reflexivity. Qed.

Definition initialized_funcref_table :=
  Build_module_table
    (Build_table_type (Build_limits 2%N None) T_funcref)
    (Some (BI_ref_func 0%N :: nil)).

Lemma parse_nonnullable_funcref :
  check_toks (x64 :: x70 :: nil)
    (fun n => parse_reference_type (n := n)) =
    Running.Singleton (Ref_type false HT_func).
Proof. vm_compute. reflexivity. Qed.

Lemma parse_explicit_nullable_externref :
  check_toks (x63 :: x6f :: nil)
    (fun n => parse_reference_type (n := n)) =
    Running.Singleton T_externref.
Proof. vm_compute. reflexivity. Qed.

Lemma parse_table_initializer :
  check_toks (x40 :: x00 :: x70 :: x00 :: x02 :: xd2 :: x00 :: x0b :: nil)
    (fun n => parse_module_table (n := n)) = Running.Singleton initialized_funcref_table.
Proof. vm_compute. reflexivity. Qed.

Lemma print_table_initializer :
  binary_of_module_table initialized_funcref_table =
    x40 :: x00 :: x70 :: x00 :: x02 :: xd2 :: x00 :: x0b :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma print_legacy_table :
  binary_of_module_table
    (Build_module_table
      (Build_table_type (Build_limits 2%N None) T_funcref) None) =
    x70 :: x00 :: x02 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma reject_table_reserved_byte :
  check_toks (x40 :: x01 :: x70 :: x00 :: x02 :: xd2 :: x00 :: x0b :: nil)
    (fun n => parse_module_table (n := n)) = False.
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
  mod_tables := (cons (Build_module_table (Build_table_type (Build_limits 0%N (Some 4%N)) T_funcref) None) nil);
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
