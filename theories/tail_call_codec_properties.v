(** Universal round trips for well-formed tail-call indices through the actual
    instruction printer and run_parse_be. The underlying prefix results also
    retain arbitrary following instruction bytes. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes_properties binary_format_parser
  binary_format_printer binary_uleb128_printer tail_call_parser_properties.

Lemma return_call_print_prefix : forall index suffix,
    (index <= 4294967295)%N ->
    return_call_prefix
      (List.app (binary_of_be (BI_return_call index)) suffix)
      (BI_return_call index) suffix.
Proof.
  intros index suffix Hbound.
  cbn [binary_of_be List.app].
  constructor. now apply binary_of_tailidx_correct.
Qed.

Lemma return_call_indirect_print_prefix : forall table type suffix,
    (table <= 4294967295)%N ->
    (type <= 4294967295)%N ->
    return_call_indirect_prefix
      (List.app (binary_of_be (BI_return_call_indirect table type)) suffix)
      (BI_return_call_indirect table type) suffix.
Proof.
  intros table type suffix Htable Htype.
  cbn [binary_of_be List.app].
  rewrite <- List.app_assoc.
  eapply return_call_indirect_bytes.
  - now apply binary_of_tailidx_correct.
  - now apply binary_of_tailidx_correct.
Qed.

Theorem return_call_roundtrip : forall index,
    (index <= 4294967295)%N ->
    run_parse_be (binary_of_be (BI_return_call index)) =
      Some (BI_return_call index).
Proof.
  intros index Hbound.
  apply run_parse_tail_call_complete. left.
  pose proof (return_call_print_prefix index nil Hbound) as Hprefix.
  now rewrite List.app_nil_r in Hprefix.
Qed.

Theorem return_call_indirect_roundtrip : forall table type,
    (table <= 4294967295)%N ->
    (type <= 4294967295)%N ->
    run_parse_be (binary_of_be (BI_return_call_indirect table type)) =
      Some (BI_return_call_indirect table type).
Proof.
  intros table type Htable Htype.
  apply run_parse_tail_call_complete. right.
  pose proof (return_call_indirect_print_prefix table type nil Htable Htype)
    as Hprefix.
  now rewrite List.app_nil_r in Hprefix.
Qed.
