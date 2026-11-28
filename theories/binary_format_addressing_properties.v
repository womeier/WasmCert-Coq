(** Correctness of the unsigned integer parser primitives actually selected
    by the binary module parser.  This is not a correctness theorem for
    sections, modules, signed LEB128, or the existing binary printer. *)
From Wasm Require Import addressing addressing_binary addressing_parseque
  binary_format_parser binary_format_printer.
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

(** Memargs select this exact primitive, independently of the selected memory;
    width-specific offset bounds are checked by validation, not by decoding. *)
Definition run_static_offset_prefix (input: list byte) : option (N * list byte) :=
  flatten (runParser
    (parse_static_offset (Toks := SizedList byte) (M := option))
    (Nat.le_refl (List.length input)) (mkSizedList input)).

Theorem binary_static_offset_parser_correct input n rest :
  run_static_offset_prefix input = Some (n, rest) <->
  (n < address_bound AT_i64)%N /\
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= 10)%nat /\
    unsigned_leb prefix n.
Proof. exact (binary_u64_parser_correct input n rest). Qed.

(** The production memory-type printer preserves the width flag and uses the
    same limits encoding as the proved bounded decoder grammar. *)
Theorem binary_memory_type_encoding mt :
  binary_of_memory_type mt =
  encode_limits (datatypes.mt_address_type mt) (datatypes.mt_limits mt).
Proof.
  destruct mt as [[minimum maximum] width].
  destruct width, maximum; unfold binary_of_memory_type, binary_of_address_limits, binary_of_limits,
    encode_limits, encode_limits_flag; cbn; try reflexivity.
  all: now rewrite app_nil_r.
Qed.

Theorem binary_table_type_encoding tt :
  binary_of_table_type tt =
  binary_of_reference_type (datatypes.tt_elem_type tt) ::
    encode_limits (datatypes.tt_address_type tt) (datatypes.tt_limits tt).
Proof.
  destruct tt as [[minimum maximum] elem width].
  destruct width, maximum; unfold binary_of_table_type, binary_of_address_limits,
    binary_of_limits, encode_limits, encode_limits_flag; cbn; try reflexivity.
  all: now rewrite app_nil_r.
Qed.
