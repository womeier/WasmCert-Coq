(** Tests for the binary parser. **)
From Stdlib Require Import Strings.Byte ZArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
                         binary_uleb128_printer datatypes_properties check_toks gc_types.
Open Scope list_scope.

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

(* Indexed source codecs do not reinterpret a module-local index as a runtime
   canonical name. Production runtime parsing awaits canonical null lowering. *)
Lemma source_nullable_index_zero :
  run_parse_source_reference_type (x63 :: x00 :: nil) =
    Some (Ref_type true (HT_type 0%N)).
Proof. vm_compute. reflexivity. Qed.

Lemma source_nonnull_index_zero :
  run_parse_source_reference_type (x64 :: x00 :: nil) =
    Some (Ref_type false (HT_type 0%N)).
Proof. vm_compute. reflexivity. Qed.

Lemma source_null_index_zero :
  run_parse_source_ref_null (xd0 :: x00 :: nil) =
    Some (BI_ref_null (HT_type 0%N)).
Proof. vm_compute. reflexivity. Qed.

Lemma source_index_64_signed_encoding :
  run_parse_source_heap_type (xc0 :: x00 :: nil) = Some (HT_type 64%N).
Proof. vm_compute. reflexivity. Qed.

Lemma source_index_u32_max :
  run_parse_source_reference_type
    (x63 :: xff :: xff :: xff :: xff :: x0f :: nil) =
    Some (Ref_type true (HT_type 4294967295%N)).
Proof. vm_compute. reflexivity. Qed.

Lemma source_null_padded_index_zero :
  run_parse_source_ref_null (xd0 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil) =
    Some (BI_ref_null (HT_type 0%N)).
Proof. vm_compute. reflexivity. Qed.

Lemma source_reference_prefix_preserves_suffix :
  run_parse_prefix (fun _ => parse_source_reference_type)
    (x63 :: x00 :: x0b :: nil) =
    Some (Ref_type true (HT_type 0%N), x0b :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_null_prefix_preserves_suffix :
  run_parse_prefix (fun _ => parse_source_ref_null)
    (xd0 :: x00 :: x15 :: x00 :: x0b :: nil) =
    Some (BI_ref_null (HT_type 0%N), x15 :: x00 :: x0b :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma source_index_overlong_rejected :
  run_parse_source_ref_null
    (xd0 :: x80 :: x80 :: x80 :: x80 :: x80 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma source_index_overflow_rejected :
  run_parse_source_reference_type
    (x63 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma source_negative_index_rejected :
  run_parse_source_heap_type (x40 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma source_truncated_index_rejected :
  run_parse_source_reference_type (x64 :: x80 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma source_null_requires_heap_not_reference_type :
  run_parse_source_ref_null (xd0 :: x63 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma source_nullable_abstract_unchanged :
  run_parse_source_reference_type (x63 :: x70 :: nil) = Some T_funcref.
Proof. vm_compute. reflexivity. Qed.

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
  (* The shared unsigned encoder now emits the canonical flags byte 64. *)
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

(** Final Bmemarg has a u64 offset even for a memory32 instruction. *)
Lemma memarg_u64_offset_max_decodes :
  run_parse_bes
    (x28 :: x00 :: xff :: xff :: xff :: xff :: xff ::
      xff :: xff :: xff :: xff :: x01 :: nil) =
    Some (BI_load T_i32 None
      (Build_memarg 18446744073709551615%N 0%N 0%N) :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memarg_explicit_index_u64_offset_decodes :
  run_parse_bes
    (x28 :: x41 :: x01 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil) =
    Some (BI_load T_i32 None
      (Build_memarg 4294967296%N 1%N 1%N) :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma memarg_rejects_u64_offset_overflow :
  run_parse_bes
    (x28 :: x00 :: xff :: xff :: xff :: xff :: xff ::
      xff :: xff :: xff :: xff :: x02 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma memarg_rejects_u64_offset_overlong_zero :
  run_parse_bes
    (x28 :: x40 :: x00 ::
      x80 :: x80 :: x80 :: x80 :: x80 :: x80 ::
      x80 :: x80 :: x80 :: x80 :: x00 :: nil) = None.
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
    {| modmem_type := {| lim_min := 1%N; lim_max := None |} |} ::
    {| modmem_type := {| lim_min := 1%N; lim_max := None |} |} :: nil;
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
      (Build_table_type (Build_limits 1%N None) T_funcref) None :: nil;
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

(** Exercise actual local/vector and function-size byte writers at distinct
    LEB128 boundaries, not just the local packer's abstract inverse. *)
Lemma local_count_64_canonical :
  binary_of_local (64%nat, T_num T_i32) = x40 :: x7f :: nil.
Proof. vm_compute. reflexivity. Qed.

Definition tail_locals_count_boundaries :=
  List.repeat (T_num T_i32) 128 ++ List.repeat (T_num T_i64) 65 ++
  (T_vec T_v128 :: T_ref T_funcref :: T_ref T_externref :: nil).

Lemma tail_code_nonempty_locals_byte_roundtrip :
  binary_format_parser.run
    (binary_of_code (Build_module_func 0%N tail_locals_count_boundaries
      (BI_return_call 128%N :: nil)))
    (fun n => (parse_code : byte_parser module_func_without_type n)) =
    Some (tail_locals_count_boundaries, BI_return_call 128%N :: nil).
Proof. vm_compute. reflexivity. Qed.

Definition tail_locals_vector_boundary :=
  List.concat (List.repeat (T_num T_i32 :: T_num T_f64 :: nil) 32).

Lemma local_vector_count_64_canonical :
  List.hd xff
    (binary_of_vec binary_of_local (bunch_locals tail_locals_vector_boundary)) =
    x40.
Proof. vm_compute. reflexivity. Qed.

Lemma tail_code_large_local_vector_byte_roundtrip :
  binary_format_parser.run
    (binary_of_code (Build_module_func 0%N tail_locals_vector_boundary
      (BI_return_call_indirect 257%N 128%N :: nil)))
    (fun n => (parse_code : byte_parser module_func_without_type n)) =
    Some (tail_locals_vector_boundary,
      BI_return_call_indirect 257%N 128%N :: nil).
Proof. vm_compute. reflexivity. Qed.

(** All ten production abstract heap types, in both nullabilities. This is a
    function-code BYTE round trip, not a claim about indexed runtime closing
    or validation/inhabitation of each nondefaultable local type. *)
Definition abstract_reference_local_codec_cases :=
  List.concat (List.map
    (fun heap =>
      T_ref (Ref_type true (shared_heap_of_abstract heap)) ::
      T_ref (Ref_type false (shared_heap_of_abstract heap)) :: nil)
    (AH_any :: AH_eq :: AH_i31 :: AH_struct :: AH_array ::
      AH_none :: AH_func :: AH_nofunc :: AH_extern :: AH_noextern :: nil)).

Lemma tail_code_abstract_reference_locals_byte_roundtrip :
  binary_format_parser.run
    (binary_of_code (Build_module_func 0%N abstract_reference_local_codec_cases
      (BI_return_call 128%N :: nil)))
    (fun n => (parse_code : byte_parser module_func_without_type n)) =
    Some (abstract_reference_local_codec_cases, BI_return_call 128%N :: nil).
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
