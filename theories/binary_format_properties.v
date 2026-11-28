(** Connections to the binary parser and printer extracted by the CLI. *)
From Wasm Require Import binary_codec binary_format_parser binary_format_printer datatypes_properties.
From Wasm Require Import binary_parser_combinators operations multi_memory_properties.
From Stdlib Require Import ZArith NArith Lia List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import addressing addressing_binary addressing_parseque
  binary_format_parser_properties leb128 leb128_properties
  leb128_unsigned_printer_properties binary_parser_combinator_properties.

(** Retain the local bounded u32 parser/printer while connecting the shared
    arithmetic printer and Addressing grammar by proved equality. *)
Lemma binary_of_u32_arithmetic n : binary_of_u32 n = binary_of_N n.
Proof.
  unfold binary_of_u32.
  destruct (N.ltb n 4294967296) eqn:Range; [|reflexivity].
  apply N.ltb_lt in Range. now apply bounded_u32_encoder_agrees.
Qed.

Lemma production_u32_reference_decoder n input
    (bound : (List.length input <= n)%nat) :
  observe_prefix
    (runParser
      (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))
      bound (mkSizedList input)) = decode_uint 32 5 input.
Proof.
  change (AddressingParseque.flatten
    (runParser (parse_u32_as_N (M := option)) bound (mkSizedList input)) =
    decode_uint 32 5 input).
  rewrite parse_u32_as_N_prefix_correspondence.
  change (AddressingBinary.decode_address Addressing.AT_i32 input =
    decode_uint 32 5 input).
  unfold AddressingBinary.decode_address, decode_uint.
  cbn [AddressingBinary.address_bytes Addressing.address_bound Addressing.address_bits].
  rewrite addressing_decode_uleb_codec. reflexivity.
Qed.

Theorem parse_u32_prefix_spec : forall bound input v suffix
  (Hbound: (List.length input <= bound)%nat),
  observe_prefix
    (runParser (parse_u32_as_N (Toks := SizedList byte)
      (M := option) (n := bound)) Hbound (mkSizedList input)) =
    Some (v, suffix) <->
  exists prefix,
    input = prefix ++ suffix /\
    (List.length prefix <= 5)%nat /\
     binary_codec.unsigned_leb prefix v /\ (v < u32_bound)%N.
Proof.
  intros. rewrite production_u32_reference_decoder.
  rewrite <- (parse_uint_correct 32 5 bound input Hbound).
  apply parse_uint_spec.
Qed.

Theorem binary_u32_prefix_round_trip : forall v suffix bound
  (Hbound: (List.length (binary_of_u32 v ++ suffix) <= bound)%nat),
  (v < u32_bound)%N ->
  observe_prefix
    (runParser (parse_u32_as_N (Toks := SizedList byte)
      (M := option) (n := bound)) Hbound
      (mkSizedList (binary_of_u32 v ++ suffix))) = Some (v, suffix).
Proof.
  intros v suffix bound Hbound Hrange.
  assert (Encoding : leb128_properties.unsigned_leb (binary_of_u32 v) v /\
    (v <= 4294967295)%N /\ (List.length (binary_of_u32 v) <= 5)%nat).
  { rewrite binary_of_u32_arithmetic. unfold binary_of_N.
    split; [apply encode_unsigned_sound |]. split.
    - unfold u32_bound in Hrange; cbn in Hrange; lia.
    - apply (encode_unsigned_length_bound 4).
      unfold u32_bound in Hrange. cbn in Hrange.
      change (Z.of_N v < 34359738368)%Z; lia. }
  destruct (parse_u32_prefix_complete bound _ Hbound
    (mkSizedList (binary_of_u32 v ++ suffix)) (binary_of_u32 v) suffix v
    eq_refl Encoding) as [s [Run [Value Rest]]].
  unfold observe_prefix. rewrite Run; simpl.
  unfold output_bytes, input_bytes in Rest.
  now rewrite Value, Rest.
Qed.

Lemma run_of_prefix : forall A
  (p: forall n, Parser (SizedList byte) byte option A n) input v,
  observe_prefix
    (runParser (p (List.length input)) (Nat.le_refl _) (mkSizedList input)) =
    Some (v, nil) ->
  binary_format_parser.run input p = Some v.
Proof.
  intros A p input v Hprefix.
  unfold binary_format_parser.run, fromText, tokenize.
  cbn.
  destruct (runParser (p (List.length input)) (Nat.le_refl _) (mkSizedList input))
    as [[value size Hsmall [rest Hsize]]|]; [|discriminate].
  unfold observe_prefix in Hprefix. simpl in Hprefix.
  inversion Hprefix; subst. reflexivity.
Qed.

Theorem binary_u32_run_round_trip : forall v,
  N.lt v u32_bound ->
  binary_format_parser.run (binary_of_u32 v) (fun n =>
    parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)) = Some v.
Proof.
  intros v Hrange.
  rewrite <- (List.app_nil_r (binary_of_u32 v)).
  apply run_of_prefix.
  apply binary_u32_prefix_round_trip. exact Hrange.
Qed.

Lemma prefix_u32 :
  prefix_semantics
    (fun n => (parse_u32_as_N: Parser (SizedList byte) byte option N n))
    (decode_uint 32 5).
Proof. intros n input Hbound. apply production_u32_reference_decoder. Qed.

(** Final-offset adapter, selectively reusing the width-bounded production
    interface of tail@724b72b and memory64@3bd1f1d. No address-width AST or
    alternative production decoder is imported. *)
Lemma production_u64_reference_decoder n input
    (bound : (List.length input <= n)%nat) :
  observe_prefix
    (runParser (parse_u64_as_N (Toks := SizedList byte) (M := option) (n := n))
      bound (mkSizedList input)) = decode_uint 64 10 input.
Proof.
  change (AddressingParseque.flatten
    (runParser (parse_u64_as_N (M := option)) bound (mkSizedList input)) =
    decode_uint 64 10 input).
  rewrite parse_u64_as_N_prefix_correspondence.
  change (AddressingBinary.decode_address Addressing.AT_i64 input =
    decode_uint 64 10 input).
  unfold AddressingBinary.decode_address, decode_uint.
  cbn [AddressingBinary.address_bytes Addressing.address_bound Addressing.address_bits].
  rewrite addressing_decode_uleb_codec; reflexivity.
Qed.

Lemma prefix_u64 :
  prefix_semantics
    (fun n => (parse_u64_as_N : Parser (SizedList byte) byte option N n))
    (decode_uint 64 10).
Proof. intros n input Hbound; apply production_u64_reference_decoder. Qed.

Definition u64_bound : N := 18446744073709551616%N.

Definition binary_u64 (bytes : list byte) (v : N) :=
  (List.length bytes <= 10)%nat /\
  binary_codec.unsigned_leb bytes v /\ (v < u64_bound)%N.

Lemma decode_u64_spec input v suffix :
  decode_uint 64 10 input = Some (v, suffix) <->
  exists bytes, input = bytes ++ suffix /\ binary_u64 bytes v.
Proof.
  rewrite <- (parse_uint_correct 64 10 (length input) input (Nat.le_refl _)).
  apply parse_uint_spec.
Qed.

Lemma decode_binary_u64_suffix v suffix :
  (v < u64_bound)%N ->
  decode_uint 64 10 (binary_of_u64 v ++ suffix) = Some (v, suffix).
Proof.
  intro Range.
  assert (Width : (length (binary_of_u64 v) <= 10)%nat).
  { apply (encode_unsigned_length_bound 9).
    change (Z.of_N v < 1180591620717411303424)%Z.
    change (v < 18446744073709551616)%N in Range; lia. }
  assert (Decoded : AddressingBinary.decode_address Addressing.AT_i64
    (binary_of_u64 v ++ suffix) = Some (v, suffix)).
  { apply AddressingBinary.decode_address_spec.
    split; [exact Range |]. exists (binary_of_u64 v).
    split; [reflexivity |]. split; [exact Width |].
    apply unsigned_leb_addressing; apply encode_unsigned_sound. }
  unfold AddressingBinary.decode_address in Decoded.
  cbn [AddressingBinary.address_bytes Addressing.address_bound Addressing.address_bits]
    in Decoded.
  rewrite addressing_decode_uleb_codec in Decoded; exact Decoded.
Qed.

Definition decode_memarg_tail (flags: N) (input: list byte) :=
  match decode_memarg_flags flags with
  | Some (align, false) =>
      option_map (fun '(off, rest) => (Build_memarg off align N0, rest))
        (decode_uint 64 10 input)
  | Some (align, true) =>
      option_map
        (fun '(args, tail) =>
          ((let '(x, off) := args in Build_memarg off align x), tail))
        (match decode_uint 32 5 input with
         | Some (x, rest) =>
             option_map (fun '(off, tail) => ((x, off), tail))
                (decode_uint 64 10 rest)
         | None => None
         end)
  | None => None
  end.

Definition decode_memarg (input: list byte) :=
  match decode_uint 32 5 input with
  | Some (flags, rest) => decode_memarg_tail flags rest
  | None => None
  end.

Lemma prefix_memarg_tail : forall flags,
  prefix_semantics
    (fun n => (parse_memarg_tail flags:
      Parser (SizedList byte) byte option memarg n))
    (decode_memarg_tail flags).
Proof.
  intros flags. unfold parse_memarg_tail, decode_memarg_tail.
  destruct (decode_memarg_flags flags) as [[align [|]]|].
  - apply prefix_map. apply prefix_and; [apply prefix_u32 |apply prefix_u64].
  - apply prefix_map. apply prefix_u64.
  - apply prefix_fail.
Qed.

Theorem parse_memarg_prefix_correct :
  prefix_semantics
    (fun n => (parse_memarg: Parser (SizedList byte) byte option memarg n))
    decode_memarg.
Proof.
  unfold parse_memarg, decode_memarg.
  apply prefix_bind; [apply prefix_u32|apply prefix_memarg_tail].
Qed.

Lemma decode_binary_u32_suffix : forall v suffix,
  N.lt v u32_bound ->
  decode_uint 32 5 (binary_of_u32 v ++ suffix) = Some (v, suffix).
Proof.
  intros v suffix Hrange.
  pose proof (binary_u32_prefix_round_trip v suffix
    (List.length (binary_of_u32 v ++ suffix)) (Nat.le_refl _) Hrange) as H.
  rewrite production_u32_reference_decoder in H. exact H.
Qed.

Theorem decode_binary_memarg_suffix : forall marg suffix,
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  N.lt marg.(memarg_offset) u64_bound ->
  decode_memarg (binary_of_memarg marg ++ suffix) = Some (marg, suffix).
Proof.
  intros [off align x] suffix Halign Hx Hoff.
  cbn in Halign, Hx, Hoff.
  unfold binary_of_memarg, decode_memarg.
  rewrite <- List.app_assoc.
  rewrite decode_binary_u32_suffix.
  2: { unfold memarg_flags; cbn -[N.add N.ltb N.eqb].
       destruct (N.eqb x 0); unfold u32_bound; lia. }
  unfold decode_memarg_tail.
  rewrite memarg_flags_round_trip by assumption.
  simpl.
  destruct (N.eqb x 0) eqn:Hzero.
  - apply N.eqb_eq in Hzero. subst x.
    cbn -[binary_of_u64 decode_uint].
    rewrite decode_binary_u64_suffix by assumption. reflexivity.
  - rewrite <- List.app_assoc.
    rewrite decode_binary_u32_suffix by assumption.
    rewrite decode_binary_u64_suffix by assumption. reflexivity.
Qed.

Theorem binary_memarg_prefix_round_trip : forall marg suffix bound
  (Hbound: (List.length (binary_of_memarg marg ++ suffix) <= bound)%nat),
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  N.lt marg.(memarg_offset) u64_bound ->
  observe_prefix (runParser
    (parse_memarg: Parser (SizedList byte) byte option memarg bound)
    Hbound (mkSizedList (binary_of_memarg marg ++ suffix))) = Some (marg, suffix).
Proof.
  intros. rewrite parse_memarg_prefix_correct.
  now apply decode_binary_memarg_suffix.
Qed.

Definition binary_u32 (bytes: list byte) (v: N) :=
  (List.length bytes <= 5)%nat /\
   binary_codec.unsigned_leb bytes v /\ N.lt v u32_bound.

Inductive binary_memarg : list byte -> memarg -> Prop :=
| binary_memarg_compact : forall aligns offsets align off,
    binary_u32 aligns align ->
    N.lt align 64 ->
    binary_u64 offsets off ->
    binary_memarg (aligns ++ offsets) (Build_memarg off align N0)
| binary_memarg_indexed : forall flags indices offsets flag x off,
    binary_u32 flags flag ->
    N.le 64 flag -> N.lt flag 128 ->
    binary_u32 indices x ->
    binary_u64 offsets off ->
    binary_memarg (flags ++ indices ++ offsets)
      (Build_memarg off (N.sub flag 64) x).

Lemma decode_u32_spec : forall input v suffix,
  decode_uint 32 5 input = Some (v, suffix) <->
  exists bytes, input = bytes ++ suffix /\ binary_u32 bytes v.
Proof.
  intros input v suffix.
  pose proof (parse_u32_prefix_spec (List.length input) input v suffix
    (Nat.le_refl _)) as H.
  rewrite production_u32_reference_decoder in H.
  exact H.
Qed.

Lemma decode_memarg_sound : forall input marg suffix,
  decode_memarg input = Some (marg, suffix) ->
  exists bytes, input = bytes ++ suffix /\ binary_memarg bytes marg.
Proof.
  intros input marg suffix H.
  unfold decode_memarg in H.
  destruct (decode_uint 32 5 input) as [[flags rest]|] eqn:Hflags;
    try discriminate.
  apply decode_u32_spec in Hflags.
  destruct Hflags as [flag_bytes [Hin Hflag]].
  unfold decode_memarg_tail in H.
  destruct (decode_memarg_flags flags) as [[align explicit]|] eqn:Hdecode;
    try discriminate.
  pose proof (decoded_memarg_flags_range _ _ _ Hdecode) as [Halign Heq].
  destruct explicit.
  - destruct (decode_uint 32 5 rest) as [[x tail]|] eqn:Hindex;
      try discriminate.
    destruct (decode_uint 64 10 tail) as [[off after]|] eqn:Hoffset;
      try discriminate.
    inversion H; subst marg after.
    apply decode_u32_spec in Hindex.
    apply decode_u64_spec in Hoffset.
    destruct Hindex as [index_bytes [Hrest Hx]].
    destruct Hoffset as [offset_bytes [Htail Hoff]].
    exists (flag_bytes ++ index_bytes ++ offset_bytes).
    split.
    + subst input rest tail. now repeat rewrite List.app_assoc.
    + replace align with (N.sub flags 64) by lia.
      eapply binary_memarg_indexed; try eassumption; lia.
  - destruct (decode_uint 64 10 rest) as [[off after]|] eqn:Hoffset;
      try discriminate.
    inversion H; subst marg after.
    apply decode_u64_spec in Hoffset.
    destruct Hoffset as [offset_bytes [Hrest Hoff]].
    exists (flag_bytes ++ offset_bytes). split.
    + subst input rest. now rewrite List.app_assoc.
    + replace flags with align in Hflag by lia.
      now apply binary_memarg_compact.
Qed.

Lemma decode_memarg_complete : forall bytes marg,
  binary_memarg bytes marg ->
  forall suffix, decode_memarg (bytes ++ suffix) = Some (marg, suffix).
Proof.
  intros bytes marg Hgrammar suffix.
  destruct Hgrammar as [aligns offsets align off Ha Hlo Ho |
    flags indices offsets flag x off Hf Hlo Hhi Hx Ho].
  - unfold decode_memarg. rewrite <- List.app_assoc.
    assert (Ha': decode_uint 32 5 (aligns ++ offsets ++ suffix) =
      Some (align, offsets ++ suffix)).
    { apply decode_u32_spec. exists aligns. auto. }
    rewrite Ha'. unfold decode_memarg_tail, decode_memarg_flags.
    apply N.ltb_lt in Hlo. rewrite Hlo.
    assert (Ho': decode_uint 64 10 (offsets ++ suffix) = Some (off, suffix)).
    { apply decode_u64_spec. exists offsets. auto. }
    rewrite Ho'. reflexivity.
  - unfold decode_memarg. repeat rewrite <- List.app_assoc.
    assert (Hf': decode_uint 32 5 (flags ++ indices ++ offsets ++ suffix) =
      Some (flag, indices ++ offsets ++ suffix)).
    { apply decode_u32_spec. exists flags. auto. }
    rewrite Hf'. unfold decode_memarg_tail, decode_memarg_flags.
    apply N.ltb_ge in Hlo. apply N.ltb_lt in Hhi. rewrite Hlo, Hhi.
    assert (Hx': decode_uint 32 5 (indices ++ offsets ++ suffix) =
      Some (x, offsets ++ suffix)).
    { apply decode_u32_spec. exists indices. auto. }
    rewrite Hx'.
    assert (Ho': decode_uint 64 10 (offsets ++ suffix) = Some (off, suffix)).
    { apply decode_u64_spec. exists offsets. auto. }
    rewrite Ho'. reflexivity.
Qed.

Theorem parse_memarg_prefix_spec : forall bound input marg suffix
  (Hbound: (List.length input <= bound)%nat),
  observe_prefix (runParser
    (parse_memarg: Parser (SizedList byte) byte option memarg bound)
    Hbound (mkSizedList input)) = Some (marg, suffix) <->
  exists bytes, input = bytes ++ suffix /\ binary_memarg bytes marg.
Proof.
  intros. rewrite parse_memarg_prefix_correct. split.
  - apply decode_memarg_sound.
  - intros [bytes [-> Hgrammar]]. now apply decode_memarg_complete.
Qed.

Theorem binary_memarg_run_round_trip : forall marg,
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  N.lt marg.(memarg_offset) u64_bound ->
  binary_format_parser.run (binary_of_memarg marg)
    (fun n => (parse_memarg: Parser (SizedList byte) byte option memarg n)) =
    Some marg.
Proof.
  intros marg Ha Hm Ho.
  rewrite <- (List.app_nil_r (binary_of_memarg marg)).
  apply run_of_prefix. now apply binary_memarg_prefix_round_trip.
Qed.
