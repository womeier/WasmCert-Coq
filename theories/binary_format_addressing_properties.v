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

Definition run_address_limits_prefix (input: list byte)
    : option (address_type * datatypes.limits * list byte) :=
  flatten_limits (runParser
    (binary_format_parser.parse_address_limits (Toks := SizedList byte) (M := option))
    (Nat.le_refl (List.length input)) (mkSizedList input)).

Theorem binary_address_limits_parser_correct input width lim rest :
  run_address_limits_prefix input = Some (width, lim, rest) <->
  limits_encoding input width lim rest.
Proof.
  change (AddressingParseque.run_limits_prefix input = Some (width, lim, rest) <->
    limits_encoding input width lim rest).
  rewrite run_limits_prefix_correct.
  split; [apply decode_limits_sound | apply decode_limits_complete].
Qed.

Definition run_memory_type_prefix (input: list byte)
    : option (datatypes.memory_type * list byte) :=
  option_map (fun s =>
    (Success.value s, @Sized.value _ (@List.length byte) _ (Success.leftovers s)))
    (runParser
      (parse_memory_type (Toks := SizedList byte) (M := option))
      (Nat.le_refl (List.length input)) (mkSizedList input)).

Theorem binary_memory_type_parser_correct input :
  run_memory_type_prefix input =
    option_map (fun '(width, lim, rest) =>
      ({| datatypes.mt_limits := lim; datatypes.mt_address_type := width |}, rest))
      (decode_limits input).
Proof.
  rewrite <- decode_limits_tokens_correct.
  unfold run_memory_type_prefix, parse_memory_type,
    binary_format_parser.parse_address_limits,
    AddressingParseque.parse_address_limits, flatten_limits.
  cbn [Combinators.map runParser].
  destruct (decode_limits_tokens (mkSizedList input)) as [result|]; last reflexivity.
  destruct result as [[width lim] size small rest]. reflexivity.
Qed.

Theorem binary_memory_type_parser_grammar input mt rest :
  run_memory_type_prefix input = Some (mt, rest) <->
  limits_encoding input (datatypes.mt_address_type mt) (datatypes.mt_limits mt) rest.
Proof.
  rewrite binary_memory_type_parser_correct.
  split.
  - destruct (decode_limits input) as [[[a lim] remaining]|] eqn:Hlimits; [|discriminate].
    intros H; inversion H; subst; clear H. now apply decode_limits_sound.
  - intros Hlimits. apply decode_limits_complete in Hlimits.
    rewrite Hlimits. destruct mt; reflexivity.
Qed.

Definition run_table_type_prefix (input: list byte)
    : option (datatypes.table_type * list byte) :=
  flatten_table_type (runParser
    (binary_format_parser.parse_table_type (Toks := SizedList byte) (M := option))
    (Nat.le_refl (List.length input)) (mkSizedList input)).

Theorem binary_table_type_parser_correct input :
  run_table_type_prefix input = decode_table_type input.
Proof.
  rewrite <- decode_table_type_tokens_correct.
  unfold run_table_type_prefix, binary_format_parser.parse_table_type,
    AddressingParseque.parse_table_type, flatten_table_type.
  cbn [runParser].
  destruct (decode_table_type_tokens (mkSizedList input)); reflexivity.
Qed.

Theorem binary_table_type_parser_grammar input tt rest :
  run_table_type_prefix input = Some (tt, rest) <->
  exists reference tail,
    input = reference :: tail /\
    decode_reference_byte reference = Some (datatypes.tt_elem_type tt) /\
    limits_encoding tail (datatypes.tt_address_type tt) (datatypes.tt_limits tt) rest.
Proof.
  rewrite binary_table_type_parser_correct.
  split.
  - destruct input as [|reference tail]; [discriminate |].
    cbn [decode_table_type].
    destruct (decode_reference_byte reference) as [elem|] eqn:Href; [|discriminate].
    destruct (decode_limits tail) as [[[a lim] remaining]|] eqn:Hlimits; [|discriminate].
    intros H; inversion H; subst; clear H.
    exists reference, tail; repeat split; try assumption.
    now apply decode_limits_sound.
  - intros [reference [tail [-> [Href Hlimits]]]].
    cbn [decode_table_type]. rewrite Href.
    apply decode_limits_complete in Hlimits. rewrite Hlimits.
    destruct tt; reflexivity.
Qed.
