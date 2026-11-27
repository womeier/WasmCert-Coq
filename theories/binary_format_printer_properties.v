(** Non-GC scalar subset of 66719d6 and 284c24e.
    Properties of the actual binary-format printer.
    These scalar results do not assert whole-module round trips. *)
From Stdlib Require Import ZArith List Lia.
From Wasm Require Import binary_format_printer binary_format_parser
  numerics leb128_properties leb128_printer_properties
  leb128_unsigned_printer_properties binary_parser_combinator_properties.
From parseque Require Import Parseque.

Theorem binary_of_i32_roundtrip x :
  @run option _ _ _ _ Byte.byte tokBytes i32
    (binary_of_i32 x) (fun _ => parse_s32) = Some x.
Proof.
  apply (@run_parser_complete i32 (fun _ => parse_s32)
    (fun bs v => signed_leb bs (Wasm_int.Int32.signed v) /\ length bs <= 5)).
  - exact parse_s32_prefix_complete.
  - unfold binary_of_i32. split.
    + apply encode_signed_sound.
    + apply (encode_signed_length_bound 4).
      change (-17179869184 <= Wasm_int.Int32.signed x < 17179869184)%Z.
      pose proof (Wasm_int.Int32.signed_range x) as Range.
      change (-2147483648 <= Wasm_int.Int32.signed x <= 2147483647)%Z in Range.
      lia.
Qed.

Theorem binary_of_i64_roundtrip x :
  @run option _ _ _ _ Byte.byte tokBytes i64
    (binary_of_i64 x) (fun _ => parse_s64) = Some x.
Proof.
  apply (@run_parser_complete i64 (fun _ => parse_s64)
    (fun bs v => signed_leb bs (Wasm_int.Int64.signed v) /\ length bs <= 10)).
  - exact parse_s64_prefix_complete.
  - unfold binary_of_i64. split.
    + apply encode_signed_sound.
    + apply (encode_signed_length_bound 9).
      change (-590295810358705651712 <= Wasm_int.Int64.signed x <
        590295810358705651712)%Z.
      pose proof (Wasm_int.Int64.signed_range x) as Range.
      change (-9223372036854775808 <= Wasm_int.Int64.signed x <=
        9223372036854775807)%Z in Range.
      lia.
Qed.

Theorem binary_of_u32_roundtrip x :
  (x <= 4294967295)%N ->
  @run option _ _ _ _ Byte.byte tokBytes N
    (binary_of_u32 x) (fun _ => parse_u32_as_N) = Some x.
Proof.
  intro Range.
  apply (@run_parser_complete N (fun _ => parse_u32_as_N)
    (fun bs x => unsigned_leb bs x /\ (x <= 4294967295)%N /\ length bs <= 5)).
  - exact parse_u32_prefix_complete.
  - unfold binary_of_u32, binary_of_N. split.
    + apply encode_unsigned_sound.
    + split; [exact Range |].
      apply (encode_unsigned_length_bound 4).
      change (Z.of_N x < 34359738368)%Z.
      apply N2Z.inj_le in Range. lia.
Qed.

Theorem binary_of_typeidx_roundtrip x :
  (x <= 4294967295)%N ->
  @run option _ _ _ _ Byte.byte tokBytes N
    (binary_of_typeidx x) (fun _ => parse_typeidx) = Some x.
Proof.
  apply binary_of_u32_roundtrip.
Qed.
