(** Regression tests for the memory64/table64 address and binary layers.
    These do not claim end-to-end proposal conformance of the legacy AST. *)
From Wasm Require Import datatypes addressing addressing_binary
  binary_format_parser check_toks.
From Stdlib Require Import Strings.Byte ZArith List.
Import ListNotations Addressing AddressingBinary.
Open Scope N_scope.

Definition lim (minimum: N) (maximum: option N) : limits :=
  {| lim_min := minimum; lim_max := maximum |}.

Example memory32_maximum :
  memory_type_valid {| memory_address_type := AT_i32;
                       memory_limits := lim 65536 (Some 65536) |} = true.
Proof. vm_compute. reflexivity. Qed.

Example memory32_excess :
  memory_type_valid {| memory_address_type := AT_i32;
                       memory_limits := lim 65537 None |} = false.
Proof. vm_compute. reflexivity. Qed.

Example memory64_maximum :
  memory_type_valid {| memory_address_type := AT_i64;
                       memory_limits := lim 281474976710656
                         (Some 281474976710656) |} = true.
Proof. vm_compute. reflexivity. Qed.

Example memory64_excess :
  memory_type_valid {| memory_address_type := AT_i64;
                       memory_limits := lim 281474976710657 None |} = false.
Proof. vm_compute. reflexivity. Qed.

Example reversed_limits :
  memory_type_valid {| memory_address_type := AT_i64;
                       memory_limits := lim 2 (Some 1) |} = false.
Proof. vm_compute. reflexivity. Qed.

Example table32_maximum :
  table_type_valid {| table_address_type := AT_i32;
                      table_limits := lim 4294967295 None;
                      table_element_type := T_funcref |} = true.
Proof. vm_compute. reflexivity. Qed.

Example table32_excess :
  table_type_valid {| table_address_type := AT_i32;
                      table_limits := lim 4294967296 None;
                      table_element_type := T_funcref |} = false.
Proof. vm_compute. reflexivity. Qed.

Example table64_maximum :
  table_type_valid {| table_address_type := AT_i64;
                      table_limits := lim 18446744073709551615 None;
                      table_element_type := T_externref |} = true.
Proof. vm_compute. reflexivity. Qed.

Example table64_excess :
  table_type_valid {| table_address_type := AT_i64;
                      table_limits := lim 18446744073709551616 None;
                      table_element_type := T_funcref |} = false.
Proof. vm_compute. reflexivity. Qed.

Example address64_above_4GiB :
  address_of_value AT_i64 (value_of_address AT_i64 4294967296) =
    Some 4294967296%N.
Proof. vm_compute. reflexivity. Qed.

Example address_width_mismatch :
  address_of_value AT_i32 (value_of_address AT_i64 1) = None.
Proof. vm_compute. reflexivity. Qed.

Example grow_failure64 :
  address_of_value AT_i64 (grow_failure AT_i64) =
    Some 18446744073709551615%N.
Proof. vm_compute. reflexivity. Qed.

Example offset64 :
  offset_valid AT_i64 4294967296 = true /\
  offset_valid AT_i32 4294967296 = false.
Proof. vm_compute. split; reflexivity. Qed.

Example address64_last_byte :
  effective_address AT_i64 18446744073709551615 0 1
    18446744073709551616 = Some 18446744073709551615%N.
Proof. vm_compute. reflexivity. Qed.

Example address64_does_not_wrap :
  effective_address AT_i64 18446744073709551615 1 1
    18446744073709551616 = None.
Proof. vm_compute. reflexivity. Qed.

Example address32_does_not_wrap :
  effective_address AT_i32 4294967295 1 1 4294967296 = None.
Proof. vm_compute. reflexivity. Qed.

Example range_zero_at_end :
  range_valid 4294967296 0 4294967296 = true.
Proof. vm_compute. reflexivity. Qed.

Example range_zero_past_end :
  range_valid 4294967297 0 4294967296 = false.
Proof. vm_compute. reflexivity. Qed.

Example copy_mixed_widths :
  copy_address_type AT_i32 AT_i64 = AT_i32 /\
  copy_address_type AT_i64 AT_i32 = AT_i32 /\
  copy_address_type AT_i64 AT_i64 = AT_i64.
Proof. repeat split. Qed.

Example copy_checks_source :
  copy_ranges_valid 0 4294967295 2 4294967296 4294967296 = false.
Proof. vm_compute. reflexivity. Qed.

Example grow64_above_4GiB :
  grow_size (lim 0 None) (memory_limit_bound AT_i64) 65536 1 =
    Some 65537%N.
Proof. vm_compute. reflexivity. Qed.

Example grow32_address_cap_without_max :
  grow_size (lim 0 None) (memory_limit_bound AT_i32) 65536 1 = None.
Proof. vm_compute. reflexivity. Qed.

Example grow64_address_cap_without_max :
  grow_size (lim 0 None) (memory_limit_bound AT_i64)
    281474976710656 1 = None.
Proof. vm_compute. reflexivity. Qed.

Example grow64_declared_max :
  grow_size (lim 0 (Some 65536)) (memory_limit_bound AT_i64)
    65536 1 = None.
Proof. vm_compute. reflexivity. Qed.

Example grow64_zero_at_max :
  grow_size (lim 0 (Some 281474976710656)) (memory_limit_bound AT_i64)
    281474976710656 0 = Some 281474976710656%N.
Proof. vm_compute. reflexivity. Qed.

Example table64_grow_max :
  grow_size (lim 0 None) (table_limit_bound AT_i64)
    18446744073709551615 1 = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_u64_max :
  decode_address AT_i64
    [xff; xff; xff; xff; xff; xff; xff; xff; xff; x01] =
    Some (18446744073709551615%N, []).
Proof. vm_compute. reflexivity. Qed.

Example decode_u64_overflow :
  decode_address AT_i64
    [x80; x80; x80; x80; x80; x80; x80; x80; x80; x02] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_u64_too_long_zero :
  decode_address AT_i64
    [x80; x80; x80; x80; x80; x80; x80; x80; x80; x80; x00] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_u64_noncanonical_zero :
  decode_address AT_i64
    [x80; x80; x80; x80; x80; x80; x80; x80; x80; x00] =
    Some (0%N, []).
Proof. vm_compute. reflexivity. Qed.

Example decode_u32_overflow :
  decode_address AT_i32 [x80; x80; x80; x80; x10] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_u32_too_long_zero :
  decode_address AT_i32 [x80; x80; x80; x80; x80; x00] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_address_truncated :
  decode_address AT_i64 [x80] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_address_preserves_suffix :
  decode_address AT_i64 [x80; x80; x80; x80; x10; xff] =
    Some (4294967296%N, [xff]).
Proof. vm_compute. reflexivity. Qed.

Example decode_limits64 :
  decode_limits [x05; x80; x80; x80; x80; x10;
                       x81; x80; x80; x80; x10; xff] =
    Some (AT_i64, lim 4294967296 (Some 4294967297), [xff]).
Proof. vm_compute. reflexivity. Qed.

Example decode_limits64_no_max :
  decode_limits [x04; x00] = Some (AT_i64, lim 0 None, []).
Proof. vm_compute. reflexivity. Qed.

Example decode_limits_invalid_not_malformed :
  decode_limits [x05; x02; x01] =
    Some (AT_i64, lim 2 (Some 1), []).
Proof. vm_compute. reflexivity. Qed.

Example decode_limits32_rejects_wide_min :
  decode_limits [x00; x80; x80; x80; x80; x10] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_limits_unknown_flag :
  decode_limits [x08; x00] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_limits_shared_not_supported :
  decode_limits [x06; x00; x01] = None.
Proof. vm_compute. reflexivity. Qed.

Example decode_limits_missing_max :
  decode_limits [x05; x00] = None.
Proof. vm_compute. reflexivity. Qed.

Example limits64_round_trip :
  decode_limits (encode_limits AT_i64
    (lim 4294967296 (Some 18446744073709551615))) =
    Some (AT_i64, lim 4294967296 (Some 18446744073709551615), []).
Proof. vm_compute. reflexivity. Qed.

Example limits32_round_trip :
  decode_limits (encode_limits AT_i32
    (lim 0 (Some 4294967295))) =
    Some (AT_i32, lim 0 (Some 4294967295), []).
Proof. vm_compute. reflexivity. Qed.

Example parser_u64_maximum :
  check_toks [xff; xff; xff; xff; xff; xff; xff; xff; xff; x01]
    (fun n => parse_u64_as_N (n := n)) = Running.Singleton 18446744073709551615%N.
Proof. vm_compute. reflexivity. Qed.

Example parser_u64_rejects_overflow :
  check_toks [x80; x80; x80; x80; x80; x80; x80; x80; x80; x02]
    (fun n => parse_u64_as_N (n := n)) = False.
Proof. vm_compute. reflexivity. Qed.

Example parser_u64_rejects_excess_length :
  check_toks [x80; x80; x80; x80; x80; x80; x80; x80; x80; x80; x00]
    (fun n => parse_u64_as_N (n := n)) = False.
Proof. vm_compute. reflexivity. Qed.

Example parser_u64_allows_noncanonical_zero :
  check_toks [x80; x80; x80; x80; x80; x80; x80; x80; x80; x00]
    (fun n => parse_u64_as_N (n := n)) = Running.Singleton 0%N.
Proof. vm_compute. reflexivity. Qed.

Example parser_u32_maximum :
  check_toks [xff; xff; xff; xff; x0f] (fun n => parse_u32_as_N (n := n)) =
    Running.Singleton 4294967295%N.
Proof. vm_compute. reflexivity. Qed.

Example parser_u32_rejects_overflow :
  check_toks [x80; x80; x80; x80; x10] (fun n => parse_u32_as_N (n := n)) = False.
Proof. vm_compute. reflexivity. Qed.

Example parser_u32_rejects_excess_length :
  check_toks [x80; x80; x80; x80; x80; x00] (fun n => parse_u32_as_N (n := n)) = False.
Proof. vm_compute. reflexivity. Qed.
