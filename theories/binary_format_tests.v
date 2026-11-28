(** Tests for the binary parser. **)
From Stdlib Require Import Strings.Byte ZArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
                         datatypes_properties check_toks.

(** A vector's u32 length may have a non-minimal LEB128 representation.
    In particular, a padded zero length must not require an element parser
    to consume a token.  These tests use the actual whole-module parser. *)
Definition empty_module_header : list Byte.byte :=
  x00 :: x61 :: x73 :: x6d :: x01 :: x00 :: x00 :: x00 :: nil.

Lemma padded_empty_type_vector :
  run_parse_module
    (empty_module_header ++ (x01 :: x02 :: x80 :: x00 :: nil)) =
  run_parse_module empty_module_header.
Proof. vm_compute. reflexivity. Qed.

Lemma maximally_padded_empty_type_vector :
  run_parse_module
    (empty_module_header ++
      (x01 :: x05 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil)) =
  run_parse_module empty_module_header.
Proof. vm_compute. reflexivity. Qed.

Lemma overlong_empty_type_vector_rejected :
  run_parse_module
    (empty_module_header ++
      (x01 :: x06 :: x80 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil)) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma overflowing_type_vector_length_rejected :
  run_parse_module
    (empty_module_header ++
      (x01 :: x05 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil)) = None.
Proof. vm_compute. reflexivity. Qed.

(** Heap indices are unsigned indices encoded with signed LEB128. *)
Lemma heap_index_64 :
  run_parse_heap_typeidx (xc0 :: x00 :: nil) = Some 64%N.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_64_requires_positive_sign :
  run_parse_heap_typeidx (x40 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_u32_max :
  run_parse_heap_typeidx (xff :: xff :: xff :: xff :: x0f :: nil) =
  Some 4294967295%N.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_padded_zero :
  run_parse_heap_typeidx (x80 :: x80 :: x80 :: x80 :: x00 :: nil) = Some 0%N.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_overlong_zero_rejected :
  run_parse_heap_typeidx (x80 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_overflow_rejected :
  run_parse_heap_typeidx (x80 :: x80 :: x80 :: x80 :: x10 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_abstract_type_rejected :
  run_parse_heap_typeidx (x70 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma heap_index_leftovers_rejected :
  run_parse_heap_typeidx (x00 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Open Scope list_scope.

(** Block type indices are nonnegative s33 values, not unsigned LEB128. *)
Lemma negative_block_type_index_rejected :
  run_parse_be (x02 :: x41 :: x0b :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma block_type_index_64_encoding :
  binary_of_block_type (BT_id 64%N) = (xc0 :: x00 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma block_type_index_64_roundtrip :
  let be := BI_block (BT_id 64%N) nil in
  run_parse_be (binary_of_be be) = Some be.
Proof. vm_compute. reflexivity. Qed.

(** A lane immediate is one byte, even when its high bit is set. *)
Lemma lane_index_high_bit :
  @binary_format_parser.run option _ _ _ _ Byte.byte tokBytes laneidx
    (x80 :: nil) (fun _ => parse_laneidx) = Some 128%N.
Proof. vm_compute. reflexivity. Qed.

Lemma lane_index_does_not_consume_leb_padding :
  @binary_format_parser.run option _ _ _ _ Byte.byte tokBytes laneidx
    (x80 :: x00 :: nil) (fun _ => parse_laneidx) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma extract_lane_byte_roundtrip :
  let be := BI_extract_vec (VS_i VSI_8_16) (Some SX_U) 128%N in
  run_parse_be (binary_of_be be) = Some be.
Proof. vm_compute. reflexivity. Qed.

Lemma signed_positive_sign_boundary :
  leb128.encode_signed 64%Z = (xc0 :: x00 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma i32_positive_sign_boundary_roundtrip :
  let be := BI_const_num (VAL_int32 (Wasm_int.Int32.repr 64)) in
  run_parse_be (binary_of_be be) = Some be.
Proof. vm_compute. reflexivity. Qed.

Lemma signed_positive_boundaries :
  List.map leb128.encode_signed
    (63%Z :: 64%Z :: 127%Z :: 128%Z :: 8191%Z :: 8192%Z :: nil) =
  ((x3f :: nil) :: (xc0 :: x00 :: nil) :: (xff :: x00 :: nil) ::
   (x80 :: x01 :: nil) :: (xff :: x3f :: nil) ::
   (x80 :: xc0 :: x00 :: nil) :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma signed_negative_boundaries :
  List.map leb128.encode_signed
    ((-64)%Z :: (-65)%Z :: (-128)%Z :: (-8192)%Z :: (-8193)%Z :: nil) =
  ((x40 :: nil) :: (xbf :: x7f :: nil) :: (x80 :: x7f :: nil) ::
   (x80 :: x40 :: nil) :: (xff :: xbf :: x7f :: nil) :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma block_type_index_u32_max_roundtrip :
  let be := BI_block (BT_id 4294967295%N) nil in
  run_parse_be (binary_of_be be) = Some be.
Proof. vm_compute. reflexivity. Qed.

Lemma overflowing_block_type_index_rejected :
  run_parse_be
    (x02 :: x80 :: x80 :: x80 :: x80 :: x10 :: x0b :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Open Scope string_scope.
Import Stdlib.Strings.String.StringSyntax.
Open Scope list_scope.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton BI_unreachable.
Proof. vm_compute. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton BI_nop.
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
