(** Tests for the binary parser. **)
From Stdlib Require Import Strings.Byte ZArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
                         datatypes_properties check_toks addressing addressing_parseque.

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

Open Scope string_scope.
Import Stdlib.Strings.String.StringSyntax.
Open Scope list_scope.

Lemma test_unreachable : check_toks (x00 :: nil) parse_be = Running.Singleton BI_unreachable.
Proof. vm_compute. reflexivity. Qed.

Lemma test_nop : check_toks (x01 :: nil) parse_be = Running.Singleton BI_nop.
Proof. vm_compute. reflexivity. Qed.

Lemma block_type_index_64_signed_round_trip :
  run_parse_bes (binary_of_be (BI_block (BT_id 64%N) nil)) =
    Some (BI_block (BT_id 64%N) nil :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma block_type_index_128_signed_round_trip :
  run_parse_bes (binary_of_be (BI_loop (BT_id 128%N) nil)) =
    Some (BI_loop (BT_id 128%N) nil :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma block_type_maximum_u32_signed_round_trip :
  run_parse_bes (binary_of_be (BI_block (BT_id 4294967295%N) nil)) =
    Some (BI_block (BT_id 4294967295%N) nil :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma explicit_nullable_reference_is_not_only_its_printer_image :
  run_parse_prefix (fun _ => parse_reference_type) (x63 :: x70 :: nil) =
    Some (T_funcref, nil) /\
  binary_of_reference_type T_funcref <> (x63 :: x70 :: nil).
Proof. vm_compute. split; congruence. Qed.

Lemma source_declaration_index_zero_accepts_padded_s33 :
  run_parse_prefix (fun _ => parse_declaration_reference_type)
    (x63 :: x80 :: x00 :: xff :: nil) =
    Some (Ref_type true (HT_type 0%N), xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_indexed_table64_descriptor_exact_suffix :
  run_parse_prefix (fun _ => parse_table_type)
    (x63 :: x80 :: x00 :: x04 :: x80 :: x00 :: xff :: nil) =
    Some (Build_table_type (Build_limits 0%N None)
      (Ref_type true (HT_type 0%N)) Addressing.AT_i64, xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma full_source_table_parser_is_not_legacy_decoder :
  AddressingParseque.decode_table_type (x63 :: x00 :: x04 :: x00 :: nil) = None /\
  run_parse_prefix (fun _ => parse_table_type) (x63 :: x00 :: x04 :: x00 :: nil) =
    Some (Build_table_type (Build_limits 0%N None)
      (Ref_type true (HT_type 0%N)) Addressing.AT_i64, nil).
Proof. vm_compute. split; reflexivity. Qed.

Lemma source_table64_initializer_format_not_limit_validity :
  run_parse_prefix (fun _ => parse_module_table)
    (x40 :: x00 :: x64 :: x00 :: x05 :: x02 :: x01 ::
      xd2 :: x01 :: x0b :: xff :: nil) =
    Some (Build_module_table
      (Build_table_type (Build_limits 2%N (Some 1%N))
        (Ref_type false (HT_type 0%N)) Addressing.AT_i64)
      (Some (BI_ref_func 1%N :: nil)), xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_table_initializer_marker_requires_reserved_zero :
  run_parse_prefix (fun _ => parse_module_table)
    (x40 :: x01 :: x70 :: x00 :: x00 :: x0b :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma source_indexed_local_value_exact_suffix :
  run_parse_prefix (fun _ => parse_locals)
    (x01 :: x64 :: x00 :: xff :: nil) =
    Some ((1%N, T_ref (Ref_type false (HT_type 0%N))), xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_indexed_global_value_exact_suffix :
  run_parse_prefix (fun _ => parse_global_type)
    (x63 :: x00 :: x01 :: xff :: nil) =
    Some (Build_global_type MUT_var (T_ref (Ref_type true (HT_type 0%N))), xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_declaration_non_null_maximum_index :
  run_parse_prefix (fun _ => parse_declaration_reference_type)
    (x64 :: xff :: xff :: xff :: xff :: x0f :: x01 :: nil) =
    Some (Ref_type false (HT_type 4294967295%N), x01 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_recursive_struct_and_array_group :
  run_parse_prefix (fun _ => parse_recursive_type)
    (x4e :: x02 :: x5f :: x01 :: x63 :: x00 :: x00 ::
      x5e :: x78 :: x01 :: xff :: nil) =
    Some ((Sub_type true nil
      (Comp_struct ({| field_mutability := MUT_const;
        field_storage := ST_value (T_ref (Ref_type true (HT_type 0%N))) |} :: nil)) ::
      Sub_type true nil
        (Comp_array {| field_mutability := MUT_var; field_storage := ST_packed PT_i8 |})
      :: nil), xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_recursive_explicit_subtype_with_super :
  run_parse_prefix (fun _ => parse_recursive_type)
    (x50 :: x01 :: x80 :: x00 :: x60 :: x00 :: x00 :: xff :: nil) =
    Some ((Sub_type false (0%N :: nil) (Comp_func (Tf nil nil)) :: nil), xff :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma shuffle_printer_has_no_vector_length_prefix :
  binary_of_be (BI_vbinop (13%N,
    0%N :: 1%N :: 2%N :: 3%N :: 4%N :: 5%N :: 6%N :: 7%N ::
    8%N :: 9%N :: 10%N :: 11%N :: 12%N :: 13%N :: 14%N :: 15%N :: nil)) =
    xfd :: x0d :: x00 :: x01 :: x02 :: x03 :: x04 :: x05 :: x06 :: x07 ::
    x08 :: x09 :: x0a :: x0b :: x0c :: x0d :: x0e :: x0f :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma splat_printer_standard_opcodes :
  binary_of_be (BI_splat_vec (VS_i VSI_8_16)) = xfd :: x0f :: nil /\
  binary_of_be (BI_splat_vec (VS_i VSI_16_8)) = xfd :: x10 :: nil /\
  binary_of_be (BI_splat_vec (VS_i VSI_32_4)) = xfd :: x11 :: nil /\
  binary_of_be (BI_splat_vec (VS_i VSI_64_2)) = xfd :: x12 :: nil /\
  binary_of_be (BI_splat_vec (VS_f VSF_32_4)) = xfd :: x13 :: nil /\
  binary_of_be (BI_splat_vec (VS_f VSF_64_2)) = xfd :: x14 :: nil.
Proof. vm_compute. repeat split; reflexivity. Qed.

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
  (* The integrated unsigned encoder now emits canonical flags 64. *)
  binary_of_memarg indexed_memarg = x40 :: x80 :: x01 :: xd2 :: x09 :: nil.
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

Lemma memory_copy_indices_round_trip :
  run_parse_bes (binary_of_be (BI_memory_copy 128%N 256%N)) =
    Some (BI_memory_copy 128%N 256%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_fill_index_round_trip :
  run_parse_bes (binary_of_be (BI_memory_fill 128%N)) =
    Some (BI_memory_fill 128%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_copy_index_order :
  run_parse_bes (xfc :: x0a :: x02 :: x07 :: nil) =
    Some (BI_memory_copy 2%N 7%N :: nil).
Proof. vm_compute. reflexivity. Qed.

(** Lane indices are raw bytes, including syntactically valid indices which
    validation must reject. They must not consume the following opcode. *)
Lemma simd_lane_byte_255_parses :
  run_parse_bes (xfd :: x54 :: x40 :: x01 :: x00 :: xff :: nil) =
    Some (BI_load_vec_lane 8%N (Build_memarg 0%N 0%N 1%N) 255%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma simd_lane_byte_255_prints :
  binary_of_load_vec_lane 8%N (Build_memarg 0%N 0%N 0%N) 255%N =
    xfd :: x54 :: x00 :: x00 :: xff :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Legacy-compatible encodings are selected by index zero, independently of
    how many other memories the containing module declares. *)
Lemma memory_zero_scalar_legacy_bytes :
  binary_of_be (BI_load T_i32 None (Build_memarg 0%N 2%N 0%N)) =
    x28 :: x02 :: x00 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma memory_zero_store_legacy_bytes :
  binary_of_be (BI_store T_i32 None (Build_memarg 0%N 2%N 0%N)) =
    x36 :: x02 :: x00 :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma memory_zero_size_grow_legacy_bytes :
  (binary_of_be (BI_memory_size 0%N), binary_of_be (BI_memory_grow 0%N)) =
    (x3f :: x00 :: nil, x40 :: x00 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memory_zero_simd_compact_bytes :
  binary_of_be (BI_load_vec LVA_none (Build_memarg 0%N 4%N 0%N)) =
    xfd :: x00 :: x04 :: x00 :: nil.
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

Lemma parse_br_on_null_single_byte (b : Byte.byte) :
  run_parse_bes (xd5 :: b :: nil) =
    if (Byte.to_N b <? 128)%N then
      Some (BI_br_on_null (Byte.to_N b) :: nil)
    else None.
Proof. destruct b; vm_compute; reflexivity. Qed.

Lemma print_br_on_null :
  binary_of_expr (BI_br_on_null 0%N :: nil) = xd5 :: x00 :: x0b :: nil.
Proof. reflexivity. Qed.

Definition initialized_funcref_table :=
  Build_module_table
    (Build_table_type (Build_limits 2%N None) T_funcref AT_i32)
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
       (Build_table_type (Build_limits 2%N None) T_funcref AT_i32) None) =
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

(* Format-only regression: deliberately not a semantic validation witness.
   In particular the table minimum exceeds its maximum. *)
Definition indexed_source_format_module : module := {|
  mod_types := (Sub_type true nil
    (Comp_struct ({| field_mutability := MUT_const;
      field_storage := ST_value (T_ref (Ref_type true (HT_type 0%N))) |} :: nil))
    :: nil) :: nil;
  mod_funcs := nil;
  mod_tables := Build_module_table
    (Build_table_type (Build_limits 2%N (Some 1%N))
      (Ref_type false (HT_type 0%N)) Addressing.AT_i64)
    (Some (BI_ref_func 0%N :: nil)) :: nil;
  mod_mems := nil;
  mod_globals := Build_module_global
    (Build_global_type MUT_const (T_ref (Ref_type true (HT_type 0%N))))
    (BI_ref_func 0%N :: nil) :: nil;
  mod_elems := Build_module_element (Ref_type true (HT_type 0%N)) nil ME_passive :: nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma indexed_source_format_module_roundtrip :
  run_parse_module (binary_of_module indexed_source_format_module) =
    Some indexed_source_format_module.
Proof. vm_compute. reflexivity. Qed.

Lemma empty_type_section_correct_framing :
  run_parse_module (binary_of_module empty_module ++ x01 :: x01 :: x00 :: nil) =
    Some empty_module.
Proof. vm_compute. reflexivity. Qed.

Lemma empty_type_section_short_framing_rejected :
  run_parse_module (binary_of_module empty_module ++ x01 :: x00 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma empty_type_section_long_framing_rejected :
  run_parse_module (binary_of_module empty_module ++ x01 :: x02 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma custom_section_exact_payload_accepted :
  run_parse_module (binary_of_module empty_module ++ x00 :: x02 :: x00 :: xff :: nil) =
    Some empty_module.
Proof. vm_compute. reflexivity. Qed.

Lemma custom_section_truncated_positive_payload_rejected :
  run_parse_module (binary_of_module empty_module ++ x00 :: x03 :: x00 :: xff :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Definition two_memory_legacy_access := {|
  mod_types := (Sub_type true nil (Comp_func (Tf nil (T_num T_i32 :: nil))) :: nil) :: nil;
  mod_funcs := {|
    modfunc_type := 0%N;
    modfunc_locals := nil;
    modfunc_body :=
      BI_const_num (VAL_int32 Wasm_int.Int32.zero) ::
      BI_load T_i32 None (Build_memarg 0%N 2%N 0%N) :: nil
  |} :: nil;
  mod_tables := nil;
  mod_mems :=
    {| modmem_type := memory_type32 {| lim_min := 1%N; lim_max := None |} |} ::
    {| modmem_type := memory_type32 {| lim_min := 1%N; lim_max := None |} |} :: nil;
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma memory_zero_in_multimemory_uses_legacy_bytes :
  binary_of_module two_memory_legacy_access =
    x00 :: x61 :: x73 :: x6d :: x01 :: x00 :: x00 :: x00 ::
    x01 :: x05 :: x01 :: x60 :: x00 :: x01 :: x7f ::
    x03 :: x02 :: x01 :: x00 ::
    x05 :: x05 :: x02 :: x00 :: x01 :: x00 :: x01 ::
    x0a :: x09 :: x01 :: x07 :: x00 :: x41 :: x00 :: x28 :: x02 :: x00 :: x0b :: nil.
Proof. vm_compute. reflexivity. Qed.

Lemma two_memory_module_round_trip :
  run_parse_module (binary_of_module two_memory_legacy_access) =
    Some two_memory_legacy_access.
Proof. vm_compute. reflexivity. Qed.

Definition two_memory_data_init := {|
  mod_types := (Sub_type true nil (Comp_func (Tf nil nil)) :: nil) :: nil;
  mod_funcs := {|
    modfunc_type := 0%N;
    modfunc_locals := nil;
    modfunc_body :=
      BI_block (BT_valtype None)
        (BI_const_num (VAL_int32 Wasm_int.Int32.zero) ::
         BI_const_num (VAL_int32 Wasm_int.Int32.zero) ::
         BI_const_num (VAL_int32 Wasm_int.Int32.one) ::
         BI_memory_init 1%N 0%N :: nil) :: nil
  |} :: nil;
  mod_tables := nil;
  mod_mems := two_memory_legacy_access.(mod_mems);
  mod_globals := nil;
  mod_elems := nil;
  mod_datas := {|
    moddata_init := compcert_byte_of_byte x2a :: nil;
    moddata_mode := MD_passive
  |} :: nil;
  mod_start := None;
  mod_imports := nil;
  mod_exports := nil;
|}.

Lemma indexed_init_module_round_trip_includes_data_count :
  run_parse_module (binary_of_module two_memory_data_init) =
    Some two_memory_data_init.
Proof. vm_compute. reflexivity. Qed.

Definition module_type := {|
  mod_types := cons (cons (Sub_type true nil (Comp_func (Tf nil (cons (T_num T_i32) nil)))) nil) nil;
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
  mod_types := cons (cons (Sub_type true nil (Comp_func (Tf nil (cons (T_num T_i32) nil)))) nil) nil;
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
  mod_types := cons (cons (Sub_type true nil (Comp_func (Tf nil (cons (T_num T_i32) nil)))) nil) nil;
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
  mod_types := cons (cons (Sub_type true nil (Comp_func (Tf nil (cons (T_num T_i32) nil)))) nil) nil;
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
  mod_types := cons (cons (Sub_type true nil (Comp_func (Tf nil (cons (T_num T_i32) nil)))) nil) nil;
  mod_funcs :=
    let e := BI_const_num (VAL_int32 (Wasm_int.Int32.repr (Z.of_nat 1))) in
    cons {| modfunc_type := 0%N; modfunc_locals := nil; modfunc_body := cons e nil |} nil;
  mod_tables := (cons (Build_module_table (Build_table_type (Build_limits 0%N (Some 4%N)) T_funcref AT_i32) None) nil);
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
