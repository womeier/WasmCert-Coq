(** Correctness of the unsigned integer parser primitives actually selected
    by the binary module parser.  This is not a correctness theorem for
    sections, modules, signed LEB128, or the existing binary printer. *)
From Wasm Require Import addressing addressing_binary addressing_parseque
  binary_format_parser.
From parseque Require Import Parseque.
From Stdlib Require Import Strings.Byte NArith List PeanoNat.
Import Addressing AddressingBinary AddressingParseque.

Definition run_u32_prefix (input: list byte) : option (N * list byte) :=
  flatten (runParser
    (parse_u32_as_N (Toks := SizedList byte) (M := option))
    (Nat.le_refl (List.length input)) (mkSizedList input)).

Definition run_u64_prefix (input: list byte) : option (N * list byte) :=
  flatten (runParser
    (parse_u64_as_N (Toks := SizedList byte) (M := option))
    (Nat.le_refl (List.length input)) (mkSizedList input)).

Theorem binary_u32_parser_correct input n rest :
  run_u32_prefix input = Some (n, rest) <->
  (n < address_bound AT_i32)%N /\
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= 5)%nat /\
    unsigned_leb prefix n.
Proof.
  exact (run_prefix_spec AT_i32 input n rest).
Qed.

Theorem binary_u64_parser_correct input n rest :
  run_u64_prefix input = Some (n, rest) <->
  (n < address_bound AT_i64)%N /\
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= 10)%nat /\
    unsigned_leb prefix n.
Proof.
  exact (run_prefix_spec AT_i64 input n rest).
Qed.
