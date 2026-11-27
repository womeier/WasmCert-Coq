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

(** Memory indices are u32 LEBs, not reserved zero bytes. *)
Lemma memory_size_index_round_trip :
  run_parse_bes (binary_of_be (BI_memory_size 128%N)) =
    Some (BI_memory_size 128%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_grow_index_round_trip :
  run_parse_bes (binary_of_be (BI_memory_grow 4294967295%N)) =
    Some (BI_memory_grow 4294967295%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_size_legacy_encoding :
  run_parse_bes (x3f :: x00 :: nil) = Some (BI_memory_size 0%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_size_rejects_truncated_index :
  run_parse_bes (x3f :: x80 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma memory_grow_rejects_overflow_index :
  run_parse_bes (x40 :: xff :: xff :: xff :: xff :: x10 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Definition indexed_memarg := Build_memarg 1234%N 0%N 128%N.

Definition indexed_memory_instructions :=
  BI_load T_i32 None indexed_memarg ::
  BI_load T_i64 (Some (Tp_i32, SX_U)) indexed_memarg ::
  BI_store T_f64 None indexed_memarg ::
  BI_store T_i32 (Some Tp_i8) indexed_memarg ::
  List.map (fun lv => BI_load_vec lv indexed_memarg)
    (LVA_none ::
     LVA_extend (8%N, 8%N) SX_S :: LVA_extend (8%N, 8%N) SX_U ::
     LVA_extend (16%N, 4%N) SX_S :: LVA_extend (16%N, 4%N) SX_U ::
     LVA_extend (32%N, 2%N) SX_S :: LVA_extend (32%N, 2%N) SX_U ::
     LVA_splat 8%N :: LVA_splat 16%N ::
     LVA_splat 32%N :: LVA_splat 64%N ::
     LVA_zero 32%N :: LVA_zero 64%N :: nil) ++
  BI_store_vec indexed_memarg ::
  List.concat (List.map (fun width =>
    BI_load_vec_lane width indexed_memarg 0%N ::
    BI_store_vec_lane width indexed_memarg 0%N :: nil)
    (8%N :: 16%N :: 32%N :: 64%N :: nil)).

Lemma indexed_scalar_simd_round_trips :
  List.map (fun be => run_parse_bes (binary_of_be be)) indexed_memory_instructions =
    List.map (fun be => Some (be :: nil)) indexed_memory_instructions.
Proof. vm_compute. reflexivity. Qed.

Lemma indexed_memarg_encoding :
  (* The shared LEB encoder emits a legal padded encoding of flags 64. *)
  binary_of_memarg indexed_memarg = xc0 :: x00 :: x80 :: x01 :: xd2 :: x09 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma explicit_zero_memory_index_accepted :
  run_parse_bes (x28 :: x40 :: x00 :: x00 :: nil) =
    Some (BI_load T_i32 None (Build_memarg 0%N 0%N 0%N) :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memarg_rejects_reserved_flags :
  run_parse_bes (x28 :: x80 :: x01 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma memarg_rejects_truncated_memory_index :
  run_parse_bes (x28 :: x40 :: x80 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma memory_init_index_order :
  run_parse_bes (xfc :: x08 :: x07 :: x02 :: nil) =
    Some (BI_memory_init 2%N 7%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_init_indices_round_trip :
  run_parse_bes (binary_of_be (BI_memory_init 128%N 256%N)) =
    Some (BI_memory_init 128%N 256%N :: nil).
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
