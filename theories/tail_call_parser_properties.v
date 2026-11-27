(** Prefix correctness of the tail-call parsers used by parse_be and module
    decoding. The suffix is retained, so these theorems apply inside instruction
    sequences, not just to closed test binaries. *)
From Stdlib Require Import List Strings.Byte NArith PeanoNat.
From parseque Require Import Parseque Success.
From Wasm Require Import binary_format_parser binary_uleb128 datatypes_properties.

Definition decode_return_call (input : list Byte.byte) :=
  match input with
  | b :: rest =>
      if byte_eqb b x12 then
        option_map (fun '(x, suffix) => (BI_return_call x, suffix))
          (decode_u32 rest)
      else None
  | nil => None
  end.

Definition decode_return_call_indirect (input : list Byte.byte) :=
  match input with
  | b :: rest =>
      if byte_eqb b x13 then
        option_map
          (fun '((typ, tab), suffix) => (BI_return_call_indirect tab typ, suffix))
          (decode_u32_pair rest)
      else None
  | nil => None
  end.

Inductive return_call_prefix :
    list Byte.byte -> basic_instruction -> list Byte.byte -> Prop :=
| return_call_bytes : forall input index suffix,
    u32_prefix input index suffix ->
    return_call_prefix (x12 :: input) (BI_return_call index) suffix.

Inductive return_call_indirect_prefix :
    list Byte.byte -> basic_instruction -> list Byte.byte -> Prop :=
| return_call_indirect_bytes : forall input typ middle tab suffix,
    u32_prefix input typ middle ->
    u32_prefix middle tab suffix ->
    return_call_indirect_prefix (x13 :: input)
      (BI_return_call_indirect tab typ) suffix.

Lemma byte_eqb_true : forall b opcode,
    byte_eqb b opcode = true <-> b = opcode.
Proof.
  intros b opcode.
  unfold byte_eqb.
  destruct (Byte.byte_eq_dec b opcode); cbn; intuition discriminate.
Qed.

Lemma decode_return_call_correct : forall input instruction suffix,
    decode_return_call input = Some (instruction, suffix) <->
    return_call_prefix input instruction suffix.
Proof.
  intros input instruction suffix.
  split.
  - destruct input as [|b input]; [discriminate |].
    cbn [decode_return_call].
    destruct (byte_eqb b x12) eqn:Hbyte; [|discriminate].
    apply byte_eqb_true in Hbyte; subst b.
    destruct (decode_u32 input) as [[index rest]|] eqn:Hindex;
      cbn; try discriminate.
    intro H; inversion H; subst.
    constructor. now apply decode_u32_correct.
  - intro H; inversion H; subst.
    cbn [decode_return_call].
    match goal with
    | Hindex : u32_prefix _ _ _ |- _ =>
        apply decode_u32_correct in Hindex; rewrite Hindex
    end.
    reflexivity.
Qed.

Lemma decode_return_call_indirect_correct : forall input instruction suffix,
    decode_return_call_indirect input = Some (instruction, suffix) <->
    return_call_indirect_prefix input instruction suffix.
Proof.
  intros input instruction suffix.
  split.
  - destruct input as [|b input]; [discriminate |].
    cbn [decode_return_call_indirect].
    destruct (byte_eqb b x13) eqn:Hbyte; [|discriminate].
    apply byte_eqb_true in Hbyte; subst b.
    destruct (decode_u32_pair input) as [[[typ tab] rest]|] eqn:Hindices;
      cbn; try discriminate.
    intro H; inversion H; subst.
    apply decode_u32_pair_correct in Hindices.
    destruct Hindices as [middle [Htype Htable]].
    eapply return_call_indirect_bytes; eassumption.
  - intro H; inversion H; subst.
    cbn [decode_return_call_indirect].
    assert (Hr : decode_u32_pair input0 = Some ((typ, tab), suffix)).
    { apply decode_u32_pair_correct. now exists middle. }
    rewrite Hr. reflexivity.
Qed.

Lemma return_call_parser_correct : forall n m (Hle : (m <= n)%nat)
    (input : SizedList Byte.byte m),
    option_map observe_reader
      (runParser (parse_return_call :
        Parser (SizedList Byte.byte) Byte.byte option basic_instruction n) Hle input) =
    decode_return_call (@Sized.value _ _ _ input).
Proof.
  intros n m Hle [input Hlen].
  destruct input as [|b input]; cbn in Hlen; subst m.
  - reflexivity.
  - cbn [parse_return_call decode_return_call exact_byte].
    unfold Combinators.rand, Combinators.and, Combinators.andbind,
      Combinators.map, Combinators.guardM.
    cbn [runParser anyTok Success.getTok sizedList uncons listUncons
      Success.fromView Success.guardM option_map uncurry Success.value
      Success.size Success.small Success.leftovers].
    destruct (byte_eqb b x12) eqn:Hbyte;
      cbn [fromOption Success.guardM option_map Success.value pure fail
        _pure _fail optionRawApplicative optionRawAlternative];
      try rewrite Hbyte; cbn.
    + unfold parse_bounded_u32.
      cbn [runParser].
      unfold Success.guardM, fromOption.
      cbn [Success.guardM Success.value option_map fromOption
        pure fail _pure _fail optionRawApplicative optionRawAlternative].
      rewrite Hbyte.
      cbn [fromOption pure _pure optionRawApplicative option_map
        Success.value Success.leftovers Success.size Success.small option_rect].
      match goal with
      | |- context [@read_u32 ?Toks ?Hs ?m ?tail] =>
          pose proof (read_u32_correct _ tail) as Hread;
          destruct (@read_u32 Toks Hs m tail)
            as [result|]
      end; cbn in Hread; rewrite <- Hread; [destruct result |]; reflexivity.
    + unfold Success.guardM, fromOption.
      cbn [Success.value option_map].
      rewrite Hbyte.
      reflexivity.
Qed.

Theorem return_call_parser_sound_complete :
    forall n m (Hle : (m <= n)%nat) (input : SizedList Byte.byte m)
      instruction suffix,
    option_map observe_reader
      (runParser (parse_return_call :
        Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
        Hle input) = Some (instruction, suffix) <->
    return_call_prefix (@Sized.value _ _ _ input) instruction suffix.
Proof.
  intros. rewrite return_call_parser_correct.
  apply decode_return_call_correct.
Qed.

Lemma return_call_indirect_parser_correct :
    forall n m (Hle : (m <= n)%nat) (input : SizedList Byte.byte m),
    option_map observe_reader
      (runParser (parse_return_call_indirect :
        Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
        Hle input) =
    decode_return_call_indirect (@Sized.value _ _ _ input).
Proof.
  intros n m Hle [input Hlen].
  destruct input as [|b input]; cbn in Hlen; subst m.
  - reflexivity.
  - cbn [parse_return_call_indirect decode_return_call_indirect exact_byte].
    unfold Combinators.rand, Combinators.and, Combinators.andbind,
      Combinators.map, Combinators.guardM.
    cbn [runParser anyTok Success.getTok sizedList uncons listUncons
      Success.fromView Success.guardM option_map uncurry Success.value
      Success.size Success.small Success.leftovers].
    destruct (byte_eqb b x13) eqn:Hbyte;
      cbn [fromOption Success.guardM option_map Success.value pure fail
        _pure _fail optionRawApplicative optionRawAlternative];
      try rewrite Hbyte; cbn.
    + unfold parse_bounded_u32_pair.
      cbn [runParser].
      unfold Success.guardM, fromOption.
      cbn [Success.guardM Success.value option_map fromOption
        pure fail _pure _fail optionRawApplicative optionRawAlternative].
      rewrite Hbyte.
      cbn [fromOption pure _pure optionRawApplicative option_map
        Success.value Success.leftovers Success.size Success.small option_rect].
      match goal with
      | |- context [@read_u32_pair ?Toks ?Hs ?m ?tail] =>
          pose proof (read_u32_pair_correct _ tail) as Hread;
          destruct (@read_u32_pair Toks Hs m tail) as [result|]
      end; cbn in Hread; rewrite <- Hread;
        [destruct result as [[typ tab] size Hsize rest] |]; reflexivity.
    + unfold Success.guardM, fromOption.
      cbn [Success.value option_map].
      rewrite Hbyte.
      reflexivity.
Qed.

Theorem return_call_indirect_parser_sound_complete :
    forall n m (Hle : (m <= n)%nat) (input : SizedList Byte.byte m)
      instruction suffix,
    option_map observe_reader
      (runParser (parse_return_call_indirect :
        Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
        Hle input) = Some (instruction, suffix) <->
    return_call_indirect_prefix (@Sized.value _ _ _ input) instruction suffix.
Proof.
  intros. rewrite return_call_indirect_parser_correct.
  apply decode_return_call_indirect_correct.
Qed.

Definition decode_tail_call input :=
  match decode_return_call input with
  | Some result => Some result
  | None => decode_return_call_indirect input
  end.

Lemma tail_call_parser_correct :
    forall n m (Hle : (m <= n)%nat) (input : SizedList Byte.byte m),
    option_map observe_reader
      (runParser (parse_tail_call :
        Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
        Hle input) =
    decode_tail_call (@Sized.value _ _ _ input).
Proof.
  intros n m Hle input.
  unfold parse_tail_call, decode_tail_call.
  rewrite <- (return_call_parser_correct n m Hle input).
  rewrite <- (return_call_indirect_parser_correct n m Hle input).
  unfold Combinators.alt; cbn [runParser].
  destruct (runParser (parse_return_call :
    Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
    Hle input); reflexivity.
Qed.

Lemma decode_tail_call_correct : forall input instruction suffix,
    decode_tail_call input = Some (instruction, suffix) <->
    return_call_prefix input instruction suffix \/
      return_call_indirect_prefix input instruction suffix.
Proof.
  intros input instruction suffix.
  unfold decode_tail_call.
  split.
  - destruct (decode_return_call input) as [[i rest]|] eqn:Hd.
    + intro H; inversion H; subst.
      left. now apply decode_return_call_correct.
    + intro H. right. now apply decode_return_call_indirect_correct.
  - intros [Hd | Hi].
    + apply decode_return_call_correct in Hd. now rewrite Hd.
    + assert (Hnone : decode_return_call input = None).
      { inversion Hi; subst. reflexivity. }
      rewrite Hnone. now apply decode_return_call_indirect_correct.
Qed.

Theorem tail_call_parser_sound_complete :
    forall n m (Hle : (m <= n)%nat) (input : SizedList Byte.byte m)
      instruction suffix,
    option_map observe_reader
      (runParser (parse_tail_call :
        Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
        Hle input) = Some (instruction, suffix) <->
    return_call_prefix (@Sized.value _ _ _ input) instruction suffix \/
      return_call_indirect_prefix (@Sized.value _ _ _ input) instruction suffix.
Proof.
  intros. rewrite tail_call_parser_correct.
  apply decode_tail_call_correct.
Qed.

(** The verified branch is the first branch of the actual recursive dispatcher.
    Successful prefix recognition therefore survives dispatch unchanged. *)
Lemma parse_be_tail_complete :
    forall n m (Hle : (m <= n)%nat) (input : SizedList Byte.byte m) result,
    runParser (parse_tail_call :
      Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
      Hle input = Some result ->
    runParser (parse_be n) Hle input = Some result.
Proof.
  intros n m Hle input result Htail.
  unfold parse_be, language, Fix, Induction.extract.
  cbn [FixBox call _be].
  unfold Combinators.alt; cbn [runParser].
  rewrite Htail. reflexivity.
Qed.

Theorem run_parse_tail_call_complete : forall input instruction,
    return_call_prefix input instruction nil \/
      return_call_indirect_prefix input instruction nil ->
    run_parse_be input = Some instruction.
Proof.
  intros input instruction Hgrammar.
  pose proof (proj2 (tail_call_parser_sound_complete
    (List.length input) (List.length input) (Nat.le_refl _) (mkSizedList input)
    instruction nil) Hgrammar) as Hobs.
  destruct (runParser (parse_tail_call :
    Parser (SizedList Byte.byte) Byte.byte option basic_instruction
      (List.length input)) (Nat.le_refl _) (mkSizedList input))
    as [result|] eqn:Hraw; [|discriminate].
  pose proof (parse_be_tail_complete _ _ _ _ _ Hraw) as Hbe.
  unfold run_parse_be, binary_format_parser.run.
  cbn [binary_format_parser.fromText tokenize tokBytes _tokenize].
  rewrite Hbe.
  destruct result as [value remaining Hsmall [leftovers Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hobs.
  inversion Hobs; subst value leftovers.
  cbn in Hlength. subst remaining.
  reflexivity.
Qed.

(** Tail opcodes cannot fall through to an unrelated decoder, even when an
    immediate is malformed. This connects rejection to the actual dispatcher. *)
Lemma parse_be_tail_opcode_exact :
    forall n input opcode
      (Hle : (S (List.length input) <= n)%nat),
    opcode = x12 \/ opcode = x13 ->
    runParser (parse_be n) Hle (mkSizedList (opcode :: input)) =
    runParser (parse_tail_call :
      Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
      Hle (mkSizedList (opcode :: input)).
Proof.
  intros n input opcode Hle Hopcode.
  destruct Hopcode as [-> | ->];
    unfold parse_be, language, Fix, Induction.extract;
    cbn [FixBox call _be];
    unfold Combinators.alt; cbn [runParser];
    destruct (runParser (parse_tail_call :
      Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
      Hle (mkSizedList (_ :: input))) as [result|] eqn:Htail;
    reflexivity.
Qed.

Lemma run_option_parser_characterization : forall A input
    (parser : forall n,
      Parser (SizedList Byte.byte) Byte.byte option A n) result,
    binary_format_parser.run input parser = Some result <->
    option_map observe_reader
      (runParser (parser (List.length input)) (Nat.le_refl _)
        (mkSizedList input)) = Some (result, nil).
Proof.
  intros A input parser result.
  unfold binary_format_parser.run.
  cbn [binary_format_parser.fromText tokenize tokBytes _tokenize].
  destruct (runParser (parser (List.length input)) (Nat.le_refl _)
    (mkSizedList input))
    as [[value remaining Hsmall [leftovers Hlength]]|].
  - destruct leftovers as [|b rest]; cbn in Hlength; subst remaining;
      cbn [observe_reader Success.value Success.size Success.leftovers
        Sized.value].
    + split; intro H; inversion H; reflexivity.
    + split; intro H; discriminate.
  - cbn [runMonad _runMonad optionRawMonadRun mapM pure _pure
      optionRawApplicative].
    split; intro H; discriminate.
Qed.

Theorem run_parse_tail_call_sound_complete : forall opcode input instruction,
    opcode = x12 \/ opcode = x13 ->
    (run_parse_be (opcode :: input) = Some instruction <->
      return_call_prefix (opcode :: input) instruction nil \/
        return_call_indirect_prefix (opcode :: input) instruction nil).
Proof.
  intros opcode input instruction Hopcode.
  unfold run_parse_be.
  rewrite run_option_parser_characterization.
  cbn [List.length].
  rewrite (parse_be_tail_opcode_exact _ input opcode (Nat.le_refl _) Hopcode).
  apply tail_call_parser_sound_complete.
Qed.
