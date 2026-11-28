(** Binary-vs-validation phase regressions for the SIMD memory codecs.
    These execute the actual production parser and executable checker. *)
From Stdlib Require Import NArith List Strings.Byte.
From Wasm Require Import datatypes addressing operations type_checker
  binary_format_printer binary_format_simd_memory_properties.
Open Scope list_scope.

Definition simd_memory_test_context width : t_context :=
  {| tc_types := nil; tc_funcs := nil; tc_tables := nil;
     tc_mems := Build_memory_type (Build_limits 1%N None) width :: nil;
     tc_globals := nil; tc_elems := nil; tc_datas := nil;
     tc_locals := nil; tc_labels := nil; tc_return := None; tc_refs := nil |}.

Definition simd_lane_i32_stack :=
  Build_checker_type (T_vec T_v128 :: T_num T_i32 :: nil) false.
Definition simd_lane_i64_stack :=
  Build_checker_type (T_vec T_v128 :: T_num T_i64 :: nil) false.
Definition simd_lane_vector_result :=
  Some (Build_checker_type (T_vec T_v128 :: nil) false).

Definition simd_lane_zero_memarg := Build_memarg 0%N 0%N 0%N.

Example simd_lane_last_byte_is_preserved_not_truncated :
  let instruction := BI_load_vec_lane 8%N simd_lane_zero_memarg 255%N in
  run_simd_memory_prefix (binary_of_be instruction ++ Byte.x0b :: nil) =
    Some (instruction, Byte.x0b :: nil).
Proof. vm_compute. reflexivity. Qed.

Example simd_lane_255_is_rejected_by_validation :
  check_single (simd_memory_test_context Addressing.AT_i64)
    (Some simd_lane_i64_stack)
    (BI_load_vec_lane 8%N simd_lane_zero_memarg 255%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_lane_one_past_valid_still_decodes :
  let instruction := BI_store_vec_lane 64%N simd_lane_zero_memarg 2%N in
  run_simd_memory_prefix (binary_of_be instruction) = Some (instruction, nil).
Proof. vm_compute. reflexivity. Qed.

Example simd_lane_one_past_valid_is_rejected_by_validation :
  check_single (simd_memory_test_context Addressing.AT_i64)
    (Some simd_lane_i64_stack)
    (BI_store_vec_lane 64%N simd_lane_zero_memarg 2%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_memory32_lane_rejects_i64_address :
  check_single (simd_memory_test_context Addressing.AT_i32)
    (Some simd_lane_i64_stack)
    (BI_load_vec_lane 8%N simd_lane_zero_memarg 0%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_memory64_lane_rejects_i32_address :
  check_single (simd_memory_test_context Addressing.AT_i64)
    (Some simd_lane_i32_stack)
    (BI_load_vec_lane 8%N simd_lane_zero_memarg 0%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_memory64_lane_accepts_i64_address :
  check_single (simd_memory_test_context Addressing.AT_i64)
    (Some simd_lane_i64_stack)
    (BI_load_vec_lane 8%N simd_lane_zero_memarg 0%N) = simd_lane_vector_result.
Proof. vm_compute. reflexivity. Qed.

Definition simd_large_static_memarg := Build_memarg 4294967296%N 0%N 0%N.

Example simd_large_offset_is_well_formed_binary :
  let instruction := BI_load_vec_lane 8%N simd_large_static_memarg 0%N in
  run_simd_memory_prefix (binary_of_be instruction) = Some (instruction, nil).
Proof. vm_compute. reflexivity. Qed.

Example simd_large_offset_is_invalid_for_memory32 :
  check_single (simd_memory_test_context Addressing.AT_i32)
    (Some simd_lane_i32_stack)
    (BI_load_vec_lane 8%N simd_large_static_memarg 0%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_large_offset_is_valid_for_memory64 :
  check_single (simd_memory_test_context Addressing.AT_i64)
    (Some simd_lane_i64_stack)
    (BI_load_vec_lane 8%N simd_large_static_memarg 0%N) = simd_lane_vector_result.
Proof. vm_compute. reflexivity. Qed.

Definition simd_maximum_fields_memarg :=
  Build_memarg 18446744073709551615%N 63%N 4294967295%N.

Example simd_maximum_binary_fields_roundtrip :
  let instruction := BI_load_vec_lane 32%N simd_maximum_fields_memarg 3%N in
  run_simd_memory_prefix (binary_of_be instruction ++ Byte.x0b :: nil) =
    Some (instruction, Byte.x0b :: nil).
Proof. vm_compute. reflexivity. Qed.

Example simd_maximum_binary_fields_do_not_bypass_validation :
  check_single (simd_memory_test_context Addressing.AT_i64)
    (Some simd_lane_i64_stack)
    (BI_load_vec_lane 32%N simd_maximum_fields_memarg 3%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_static_offset_overflow_is_malformed :
  let instruction := BI_load_vec_lane 8%N
    (Build_memarg 18446744073709551616%N 0%N 0%N) 0%N in
  run_simd_memory_prefix (binary_of_be instruction) = None.
Proof. vm_compute. reflexivity. Qed.

Example simd_memory_index_overflow_is_malformed :
  let instruction := BI_load_vec_lane 8%N
    (Build_memarg 0%N 0%N 4294967296%N) 0%N in
  run_simd_memory_prefix (binary_of_be instruction) = None.
Proof. vm_compute. reflexivity. Qed.
