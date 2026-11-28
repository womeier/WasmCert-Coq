(** Width-bearing source limits: byte grammar, not semantic limit validity.
    Flags 0/1/4/5 select independent u32/u64 fields. *)
From Stdlib Require Import List Strings.Byte NArith ZArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes addressing addressing_binary addressing_parseque
  binary_format_printer leb128 leb128_properties leb128_unsigned_printer_properties
  binary_format_parser binary_format_parser_properties
  binary_parser_combinator_properties binary_format_properties
  binary_parser_combinators binary_codec binary_memory_grammar_properties.
Local Notation byte := Byte.byte.

Definition width_integer_encoding width bs value :=
  (value < Addressing.address_bound width)%N /\
  (length bs <= AddressingBinary.address_bytes width)%nat /\
  AddressingBinary.unsigned_leb bs value.

Inductive width_limits_encoding :
    list byte -> (Addressing.address_type * limits) -> Prop :=
| width_limits_min : forall flag width minimum bs,
    AddressingBinary.decode_limits_flag flag = Some (width, false) ->
    width_integer_encoding width bs minimum ->
    width_limits_encoding (flag :: bs) (width, Build_limits minimum None)
| width_limits_max : forall flag width minimum maximum bs upper,
    AddressingBinary.decode_limits_flag flag = Some (width, true) ->
    width_integer_encoding width bs minimum ->
    width_integer_encoding width upper maximum ->
    width_limits_encoding (flag :: bs ++ upper)
      (width, Build_limits minimum (Some maximum)).

Definition decode_width_limits input :=
  option_map (fun '(width, lim, rest) => ((width, lim), rest))
    (AddressingBinary.decode_limits input).

Lemma width_limits_prefix_correct :
  prefix_semantics
    (fun n => (parse_address_limits :
      Parser (SizedList byte) byte option (Addressing.address_type * limits) n))
    decode_width_limits.
Proof.
  intros n input bound.
  pose proof (AddressingParseque.decode_limits_tokens_correct input) as Correct.
  unfold decode_width_limits.
  rewrite <- Correct.
  unfold observe_prefix, AddressingParseque.flatten_limits,
    parse_address_limits, AddressingParseque.parse_address_limits.
  cbn [runParser Category.fromOption].
  destruct (AddressingParseque.decode_limits_tokens (mkSizedList input));
    [destruct (Success.value s) as [width lim] eqn:Value|];
    cbn; [now rewrite Value|reflexivity].
Qed.

Definition width_limits_binary_wf width lim :=
  (lim_min lim < Addressing.address_bound width)%N /\
  match lim_max lim with
  | Some maximum => (maximum < Addressing.address_bound width)%N
  | None => True
  end.

Lemma printed_width_integer_encoding width value :
  (value < Addressing.address_bound width)%N ->
  width_integer_encoding width (encode_unsigned value) value.
Proof.
  intro Range; split; [exact Range|]; split.
  - destruct width.
    + apply (encode_unsigned_length_bound 4).
      change (value < 4294967296)%N in Range.
      change (Z.of_N value < 34359738368)%Z; lia.
    + apply (encode_unsigned_length_bound 9).
      change (value < 18446744073709551616)%N in Range.
      change (Z.of_N value < 1180591620717411303424)%Z; lia.
  - apply addressing_unsigned_leb_complete; apply encode_unsigned_sound.
Qed.

Lemma binary_of_width_limits_encoding width lim :
  width_limits_binary_wf width lim ->
  width_limits_encoding (binary_of_address_limits width lim) (width, lim).
Proof.
  destruct lim as [minimum [maximum|]]; intros [Minimum Maximum]; destruct width.
  - change (width_limits_encoding
      (AddressingBinary.encode_limits_flag Addressing.AT_i32 true ::
        encode_unsigned minimum ++ encode_unsigned maximum)
      (Addressing.AT_i32, Build_limits minimum (Some maximum))).
    apply width_limits_max; [apply AddressingBinary.limits_flag_round_trip| |];
      now apply printed_width_integer_encoding.
  - change (width_limits_encoding
      (AddressingBinary.encode_limits_flag Addressing.AT_i64 true ::
        encode_unsigned minimum ++ encode_unsigned maximum)
      (Addressing.AT_i64, Build_limits minimum (Some maximum))).
    apply width_limits_max; [apply AddressingBinary.limits_flag_round_trip| |];
      now apply printed_width_integer_encoding.
  - change (width_limits_encoding
      (AddressingBinary.encode_limits_flag Addressing.AT_i32 false :: encode_unsigned minimum)
      (Addressing.AT_i32, Build_limits minimum None)).
    apply width_limits_min; [apply AddressingBinary.limits_flag_round_trip|].
    now apply printed_width_integer_encoding.
  - change (width_limits_encoding
      (AddressingBinary.encode_limits_flag Addressing.AT_i64 false :: encode_unsigned minimum)
      (Addressing.AT_i64, Build_limits minimum None)).
    apply width_limits_min; [apply AddressingBinary.limits_flag_round_trip|].
    now apply printed_width_integer_encoding.
Qed.

Lemma decode_width_limits_sound input value rest :
  decode_width_limits input = Some (value, rest) ->
  exists prefix, input = prefix ++ rest /\ width_limits_encoding prefix value.
Proof.
  unfold decode_width_limits.
  destruct (AddressingBinary.decode_limits input) as [[[width lim] suffix]|]
    eqn:Decoded; [|discriminate].
  intro Run; inversion Run; subst value suffix.
  apply AddressingBinary.decode_limits_sound in Decoded.
  destruct Decoded as
    [width flag input minimum rest Flag Range [bs [Bytes [Length Encoded]]]|
     width flag input minimum middle maximum rest Flag Range
       [bs [Bytes [Length Encoded]]] Upper
       [upper [Bytes' [Length' Encoded']]]].
  - exists (flag :: bs); split; [now rewrite Bytes|].
    apply width_limits_min; [exact Flag|repeat split; assumption].
  - exists (flag :: bs ++ upper); split.
    + rewrite Bytes, Bytes'; simpl; now rewrite app_assoc.
    + apply width_limits_max; [exact Flag| |]; repeat split; assumption.
Qed.

Lemma decode_width_limits_complete prefix value :
  width_limits_encoding prefix value ->
  forall rest, decode_width_limits (prefix ++ rest) = Some (value, rest).
Proof.
  intro Encoding; destruct Encoding; intro rest; unfold decode_width_limits.
  - assert (Decoded : AddressingBinary.decode_limits ((flag :: bs) ++ rest) =
      Some (width, Build_limits minimum None, rest)).
    { apply AddressingBinary.decode_limits_complete.
      apply AddressingBinary.limits_without_max with (a := width).
      - exact H.
      - exact (proj1 H0).
      - exists bs; split; [reflexivity|exact (proj2 H0)]. }
    now rewrite Decoded.
  - assert (Decoded : AddressingBinary.decode_limits
      ((flag :: bs ++ upper) ++ rest) =
      Some (width, Build_limits minimum (Some maximum), rest)).
    { apply AddressingBinary.decode_limits_complete.
      apply AddressingBinary.limits_with_max with
        (a := width) (middle := upper ++ rest).
      - exact H.
      - exact (proj1 H0).
      - exists bs; split; [now rewrite app_assoc|exact (proj2 H0)].
      - exact (proj1 H1).
      - exists upper; split; [reflexivity|exact (proj2 H1)]. }
    now rewrite Decoded.
Qed.

Theorem parse_width_limits_sound n :
  parser_sound (parse_address_limits
    (Toks := SizedList byte) (M := option) (n := n)) width_limits_encoding.
Proof.
  exact (prefix_semantics_grammar_sound _ (fun n => parse_address_limits)
    decode_width_limits width_limits_encoding width_limits_prefix_correct
    decode_width_limits_sound n).
Qed.

Theorem parse_width_limits_complete n :
  parser_complete (parse_address_limits
    (Toks := SizedList byte) (M := option) (n := n)) width_limits_encoding.
Proof.
  exact (prefix_semantics_grammar_complete _ (fun n => parse_address_limits)
    decode_width_limits width_limits_encoding width_limits_prefix_correct
    decode_width_limits_complete n).
Qed.
