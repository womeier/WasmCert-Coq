(** Regressions for the UNCONDITIONAL production expression soundness theorem.
    These are syntax derivations, not claims of semantic validation. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes binary_format_parser binary_format_language_properties
  binary_format_dispatch_properties binary_format_block_properties
  binary_format_memory_complete.
Import ListNotations.

Example concrete_all_catches_expression :
  expression_encoding wasm_atomic_encoding block_type_encoding
    [x1f; x40; x04; x00; x00; x00; x01; x00; x00;
     x02; x00; x03; x00; x08; x00; x0a; x0b; x0b]
    [BI_try_table (BT_valtype None)
      [Catch_tag 0%N 0%N; Catch_tag_ref 0%N 0%N; Catch_all 0%N; Catch_all_ref 0%N]
      [BI_throw 0%N; BI_throw_ref]].
Proof. apply wasm_run_parse_expr_sound; vm_compute; reflexivity. Qed.

Example concrete_indexed_reference_expression :
  expression_encoding wasm_atomic_encoding block_type_encoding
    [x02; x63; x00; xd0; x00; x0b; x0b]
    [BI_block (BT_valtype (Some (T_ref (Ref_type true (HT_type 0%N)))))
      [BI_ref_null (HT_type 0%N)]].
Proof. apply wasm_run_parse_expr_sound; vm_compute; reflexivity. Qed.

Example concrete_reference_calls_and_i31_expression :
  expression_encoding wasm_atomic_encoding block_type_encoding
    [x14; x00; x15; x00; xd6; x00; xfb; x1c; xfb; x1d; xfb; x1e; x0b]
    [BI_call_ref 0%N; BI_return_call_ref 0%N; BI_br_on_non_null 0%N;
     BI_ref_i31; BI_i31_get SX_S; BI_i31_get SX_U].
Proof. apply wasm_run_parse_expr_sound; vm_compute; reflexivity. Qed.

Example explicit_zero_memory_padded_memarg_prefix :
  run_parse_prefix (fun n => parse_memarg (n := n))
    [x60; x80; x00; x00; x0b] =
    Some ({| memarg_offset := 0%N; memarg_align := 32%N |}, [x0b]).
Proof. vm_compute; reflexivity. Qed.

Example vector_memory_lane_is_one_raw_byte :
  expression_encoding wasm_atomic_encoding block_type_encoding
    [xfd; x54; x00; x00; x80; x0b]
    [BI_load_vec_lane 8%N {| memarg_offset := 0%N; memarg_align := 0%N |} 128%N].
Proof. apply wasm_run_parse_expr_sound; vm_compute; reflexivity. Qed.
