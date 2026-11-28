(** Correctness of the unsigned integer parser primitives actually selected
    by the binary module parser, and width-bounded printer/parser round trips.
    This is not a correctness theorem for sections, modules or signed LEB128. *)
From Wasm Require Import datatypes operations addressing addressing_binary addressing_parseque
  binary_format_parser binary_format_printer.
From Wasm Require Import leb128_properties leb128_unsigned_printer_properties.
From parseque Require Import Parseque.
From Stdlib Require Import Strings.Byte NArith ZArith List PeanoNat Lia.
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

(** General printer/production-parser round trips, including exact suffixes.
    These reuse the shared unsigned encoder proof, rather than verifying a
    second encoding implementation. *)
Lemma binary_address_unsigned_encoding width n :
  (n < address_bound width)%N ->
  AddressingBinary.unsigned_leb (leb128.encode_unsigned n) n /\
  (List.length (leb128.encode_unsigned n) <= address_bytes width)%nat.
Proof.
  intro Range; split.
  - apply addressing_unsigned_leb_complete. apply encode_unsigned_sound.
  - destruct width.
    + apply (encode_unsigned_length_bound 4).
      apply N2Z.inj_lt in Range.
      change (Z.of_N n < 4294967296)%Z in Range.
      change (Z.of_N n < 34359738368)%Z. lia.
    + apply (encode_unsigned_length_bound 9).
      apply N2Z.inj_lt in Range.
      change (Z.of_N n < 18446744073709551616)%Z in Range.
      change (Z.of_N n < 1180591620717411303424)%Z. lia.
Qed.

Lemma binary_address_decoder_roundtrip width n rest :
  (n < address_bound width)%N ->
  decode_address width (leb128.encode_unsigned n ++ rest) = Some (n, rest).
Proof.
  intro Range.
  destruct (binary_address_unsigned_encoding width n Range) as [Encoded Length].
  apply decode_address_spec. split; [exact Range|].
  exists (leb128.encode_unsigned n); repeat split; assumption || reflexivity.
Qed.

Theorem binary_u32_printer_parser_roundtrip n rest :
  (n < address_bound AT_i32)%N ->
  run_u32_prefix (binary_of_u32 n ++ rest) = Some (n, rest).
Proof.
  change ((n < address_bound AT_i32)%N ->
    run_prefix AT_i32 (leb128.encode_unsigned n ++ rest) = Some (n, rest)).
  rewrite run_prefix_correct. apply binary_address_decoder_roundtrip.
Qed.

Theorem binary_u64_printer_parser_roundtrip n rest :
  (n < address_bound AT_i64)%N ->
  run_u64_prefix (binary_of_u64 n ++ rest) = Some (n, rest).
Proof.
  change ((n < address_bound AT_i64)%N ->
    run_prefix AT_i64 (leb128.encode_unsigned n ++ rest) = Some (n, rest)).
  rewrite run_prefix_correct. apply binary_address_decoder_roundtrip.
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
  binary_of_reference_type (datatypes.tt_elem_type tt) ++
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

Lemma binary_address_limits_decoder_roundtrip width lim rest :
  (lim_min lim < address_bound width)%N ->
  (match lim_max lim with
   | Some maximum => maximum < address_bound width
   | None => True
   end)%N ->
  decode_limits (encode_limits width lim ++ rest) = Some (width, lim, rest).
Proof.
  destruct lim as [minimum [maximum|]]; cbn; intros Minimum Maximum;
    unfold encode_limits; cbn [lim_min lim_max List.app decode_limits];
    rewrite limits_flag_round_trip.
  - rewrite <- app_assoc.
    rewrite binary_address_decoder_roundtrip by exact Minimum.
    rewrite binary_address_decoder_roundtrip by exact Maximum.
    reflexivity.
  - rewrite app_nil_r.
    rewrite binary_address_decoder_roundtrip by exact Minimum.
    reflexivity.
Qed.

Theorem binary_address_limits_printer_parser_roundtrip width lim rest :
  (lim_min lim < address_bound width)%N ->
  (match lim_max lim with
   | Some maximum => maximum < address_bound width
   | None => True
   end)%N ->
  run_address_limits_prefix (encode_limits width lim ++ rest) =
    Some (width, lim, rest).
Proof.
  intros Minimum Maximum.
  change (run_limits_prefix (encode_limits width lim ++ rest) = Some (width, lim, rest)).
  rewrite run_limits_prefix_correct.
  now apply binary_address_limits_decoder_roundtrip.
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

Theorem binary_memory_type_printer_parser_roundtrip mt rest :
  (lim_min mt.(datatypes.mt_limits) <
     address_bound mt.(datatypes.mt_address_type))%N ->
  (match lim_max mt.(datatypes.mt_limits) with
   | Some maximum => maximum < address_bound mt.(datatypes.mt_address_type)
   | None => True
   end)%N ->
  run_memory_type_prefix (binary_of_memory_type mt ++ rest) = Some (mt, rest).
Proof.
  intros Minimum Maximum.
  rewrite binary_memory_type_parser_correct, binary_memory_type_encoding.
  rewrite binary_address_limits_decoder_roundtrip by assumption.
  destruct mt; reflexivity.
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
  exists tail,
    reference_encoding input (datatypes.tt_elem_type tt) tail /\
    limits_encoding tail (datatypes.tt_address_type tt) (datatypes.tt_limits tt) rest.
Proof.
  rewrite binary_table_type_parser_correct.
  split.
  - unfold decode_table_type.
    destruct (decode_reference_type input) as [[elem tail]|] eqn:Href; [|discriminate].
    destruct (decode_limits tail) as [[[a lim] remaining]|] eqn:Hlimits; [|discriminate].
    intros H; inversion H; subst; clear H.
    exists tail; split.
    + now apply decode_reference_type_spec.
    + now apply decode_limits_sound.
  - intros [tail [Href Hlimits]].
    unfold decode_table_type. apply decode_reference_type_spec in Href. rewrite Href.
    apply decode_limits_complete in Hlimits. rewrite Hlimits.
    destruct tt; reflexivity.
Qed.

Lemma binary_abstract_reference_decoder_roundtrip reference rest :
  (ref_heap reference = HT_func \/ ref_heap reference = HT_extern) ->
  decode_reference_type (binary_of_reference_type reference ++ rest) =
    Some (reference, rest).
Proof.
  destruct reference as [nullable heap]; cbn.
  intros [Func|Extern]; subst heap; destruct nullable; reflexivity.
Qed.

(* Handoff to the shared full reference decoder, including indexed forms:
   this is an exact source-byte/remainder contract, not permission to identify
   a source HT_type index with a runtime canonical name. Source closing and
   stored-descriptor agreement remain separate shared runtime obligations. *)
Theorem binary_table_type_printer_parser_roundtrip_from_reference_codec tt rest :
  (forall suffix,
    decode_reference_type (binary_of_reference_type tt.(tt_elem_type) ++ suffix) =
      Some (tt.(tt_elem_type), suffix)) ->
  (lim_min tt.(tt_limits) < address_bound tt.(tt_address_type))%N ->
  (match lim_max tt.(tt_limits) with
   | Some maximum => maximum < address_bound tt.(tt_address_type)
   | None => True
   end)%N ->
  run_table_type_prefix (binary_of_table_type tt ++ rest) = Some (tt, rest).
Proof.
  intros Reference Minimum Maximum.
  rewrite binary_table_type_parser_correct, binary_table_type_encoding.
  unfold decode_table_type.
  rewrite <- app_assoc.
  rewrite Reference.
  rewrite binary_address_limits_decoder_roundtrip by assumption.
  destruct tt; reflexivity.
Qed.

Theorem binary_table_type_printer_parser_roundtrip tt rest :
  (ref_heap tt.(tt_elem_type) = HT_func \/ ref_heap tt.(tt_elem_type) = HT_extern) ->
  (lim_min tt.(tt_limits) < address_bound tt.(tt_address_type))%N ->
  (match lim_max tt.(tt_limits) with
   | Some maximum => maximum < address_bound tt.(tt_address_type)
   | None => True
   end)%N ->
  run_table_type_prefix (binary_of_table_type tt ++ rest) = Some (tt, rest).
Proof.
  intros Reference Minimum Maximum.
  apply binary_table_type_printer_parser_roundtrip_from_reference_codec; auto.
  intro suffix. now apply binary_abstract_reference_decoder_roundtrip.
Qed.

Definition run_memarg_prefix (input: list byte) : option (datatypes.memarg * list byte) :=
  flatten_memarg (runParser
    (binary_format_parser.parse_memarg (Toks := SizedList byte) (M := option))
    (Nat.le_refl (List.length input)) (mkSizedList input)).

Theorem binary_memarg_parser_correct input :
  run_memarg_prefix input = decode_memarg input.
Proof.
  rewrite <- decode_memarg_tokens_correct.
  unfold run_memarg_prefix, binary_format_parser.parse_memarg,
    AddressingParseque.parse_memarg, flatten_memarg.
  cbn [runParser].
  destruct (decode_memarg_tokens (mkSizedList input)); reflexivity.
Qed.

Theorem binary_memarg_parser_grammar input marg rest :
  run_memarg_prefix input = Some (marg, rest) <-> memarg_encoding input marg rest.
Proof.
  rewrite binary_memarg_parser_correct.
  split; [apply decode_memarg_sound | apply decode_memarg_complete].
Qed.

Theorem binary_memarg_printer_parser_roundtrip marg rest :
  (marg.(memarg_align) < 64)%N ->
  (marg.(memarg_memory) < address_bound AT_i32)%N ->
  (marg.(memarg_offset) < address_bound AT_i64)%N ->
  run_memarg_prefix (binary_of_memarg marg ++ rest) = Some (marg, rest).
Proof.
  destruct marg as [offset align memory]; cbn.
  intros Alignment Memory Offset.
  rewrite binary_memarg_parser_correct.
  unfold binary_of_memarg, memarg_flags, binary_of_u32, binary_of_u64,
    binary_of_memidx, binary_of_idx, binary_of_N.
  cbn [memarg_align memarg_offset memarg_memory].
  unfold decode_memarg.
  destruct (N.eqb memory 0) eqn:Zero.
  - apply N.eqb_eq in Zero; subst memory; cbn [List.app].
    repeat rewrite <- app_assoc.
    rewrite binary_address_decoder_roundtrip
      by (change (align < 4294967296)%N; lia).
    unfold decode_memarg_flags.
    assert (Low : N.ltb align 64 = true) by (apply N.ltb_lt; exact Alignment).
    rewrite Low.
    cbn [List.app].
    rewrite binary_address_decoder_roundtrip by exact Offset.
    reflexivity.
  - repeat rewrite <- app_assoc.
    rewrite binary_address_decoder_roundtrip
      by (change (align + 64 < 4294967296)%N; lia).
    unfold decode_memarg_flags.
    assert (High : N.ltb (align + 64) 64 = false) by (apply N.ltb_ge; lia).
    assert (Low : N.ltb (align + 64) 128 = true) by (apply N.ltb_lt; lia).
    rewrite High, Low.
    cbn [List.app].
    rewrite binary_address_decoder_roundtrip by exact Memory.
    rewrite binary_address_decoder_roundtrip by exact Offset.
    replace (align + 64 - 64)%N with align by lia.
    reflexivity.
Qed.
