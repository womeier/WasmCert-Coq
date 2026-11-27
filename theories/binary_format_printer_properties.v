(** Properties of the actual binary-format printer.
    These scalar results do not assert whole-module round trips. *)
From Stdlib Require Import ZArith List Lia.
From Wasm Require Import binary_format_printer binary_format_parser
  numerics leb128_properties leb128_printer_properties
  binary_parser_combinator_properties.
From parseque Require Import Parseque.

Theorem binary_of_heap_typeidx_roundtrip x bs :
  binary_of_heap_typeidx x = Some bs ->
  run_parse_heap_typeidx bs = Some x.
Proof.
  unfold binary_of_heap_typeidx.
  destruct (N.leb x 4294967295) eqn:Range; [|discriminate].
  intro E; inversion E; subst.
  apply heap_index_encoder_parser_roundtrip.
  now apply N.leb_le.
Qed.

Theorem binary_of_heap_typeidx_defined x :
  (exists bs, binary_of_heap_typeidx x = Some bs) <->
  (x <= 4294967295)%N.
Proof.
  unfold binary_of_heap_typeidx.
  destruct (N.leb x 4294967295) eqn:Range.
  - split; [intro H; now apply N.leb_le |].
    intro H. eexists; reflexivity.
  - split.
    + intros [bs E]. discriminate.
    + intro H. apply N.leb_gt in Range.
      lia.
Qed.

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
