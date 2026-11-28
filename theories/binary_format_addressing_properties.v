(** Correctness of the unsigned integer parser primitives actually selected
    by the binary module parser.  This is not a correctness theorem for
    sections, modules, signed LEB128, or the existing binary printer. *)
From Wasm Require Import addressing addressing_binary addressing_parseque
  binary_format_parser binary_uleb128 binary_format_parser_properties.
From parseque Require Import Parseque.
From Stdlib Require Import Strings.Byte NArith List PeanoNat Lia.
Import Addressing AddressingBinary AddressingParseque.

(** Preserve the already connected tail/local u32 reader, and prove agreement
    with the memory substrate's bounded decoder rather than assuming it. *)
Lemma bounded_unsigned_decoders_agree : forall fuel input,
  AddressingBinary.decode_uleb fuel input =
    binary_uleb128.decode_uleb fuel input.
Proof.
  induction fuel as [|fuel IH]; intros [|b input]; try reflexivity.
  cbn [AddressingBinary.decode_uleb binary_uleb128.decode_uleb].
  destruct (N.ltb (Byte.to_N b) 128); [reflexivity |].
  rewrite IH. destruct (binary_uleb128.decode_uleb fuel input) as [[n rest]|];
    reflexivity.
Qed.

Lemma bounded_u32_decoders_agree : forall input,
  AddressingBinary.decode_address AT_i32 input = decode_u32 input.
Proof.
  intro input.
  unfold AddressingBinary.decode_address, decode_u32.
  cbn [address_bytes]. rewrite bounded_unsigned_decoders_agree.
  destruct (binary_uleb128.decode_uleb 5 input) as [[n rest]|]; [|reflexivity].
  assert (Hbound : N.ltb n (address_bound AT_i32) = N.leb n 4294967295).
  { apply Bool.eq_true_iff_eq. rewrite N.ltb_lt, N.leb_le.
    change ((n < 4294967296)%N <-> (n <= 4294967295)%N). lia. }
  now rewrite Hbound.
Qed.

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
  change (option_map observe_reader
    (runParser (parse_u32_as_N :
      Parser (SizedList byte) byte option N (List.length input))
      (Nat.le_refl _) (mkSizedList input)) = Some (n, rest) <->
    (n < address_bound AT_i32)%N /\
    exists prefix, input = prefix ++ rest /\
      (List.length prefix <= 5)%nat /\ unsigned_leb prefix n).
  rewrite parse_u32_as_N_correct, <- decode_u32_correct.
  rewrite <- bounded_u32_decoders_agree.
  exact (decode_address_spec AT_i32 input n rest).
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

Lemma parse_u64_as_N_correct : forall n m (Hle : (m <= n)%nat)
    (input : SizedList byte m) value suffix,
    option_map observe_reader
      (runParser (parse_u64_as_N :
        Parser (SizedList byte) byte option N n) Hle input) =
      Some (value, suffix) <->
    AddressingBinary.decode_address AT_i64 (@Sized.value _ _ _ input) =
      Some (value, suffix).
Proof.
  intros n m Hle [input Hlength] value suffix. subst m.
  cbn [parse_u64_as_N AddressingParseque.parse_address runParser].
  cbn [Sized.value].
  rewrite <- (decode_address_tokens_correct AT_i64 input).
  unfold AddressingParseque.flatten.
  unfold mkSizedList.
  match goal with
  | |- context [decode_address_tokens AT_i64 ?tokens] =>
      destruct (@decode_address_tokens (SizedList byte) (sizedList byte)
        AT_i64 _ tokens)
  end; reflexivity.
Qed.

Definition u64_prefix input value suffix :=
  (value < address_bound AT_i64)%N /\
  exists bytes, input = List.app bytes suffix /\
    (List.length bytes <= 10)%nat /\ unsigned_leb bytes value.

Corollary parse_static_offset_correct : forall n m (Hle : (m <= n)%nat)
    (input : SizedList byte m) value suffix,
    option_map observe_reader
      (runParser (parse_static_offset :
        Parser (SizedList byte) byte option N n) Hle input) =
      Some (value, suffix) <->
    u64_prefix (@Sized.value _ _ _ input) value suffix.
Proof.
  intros. unfold parse_static_offset.
  rewrite parse_u64_as_N_correct.
  exact (decode_address_spec AT_i64 _ _ _).
Qed.
