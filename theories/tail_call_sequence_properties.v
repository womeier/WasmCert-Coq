(** Lift tail-call prefix correctness through the actual recursive expression
    parser, including the end marker and complete-input check. *)
From Stdlib Require Import List Strings.Byte NArith PeanoNat Lia.
From parseque Require Import Parseque Success.
From Wasm Require Import datatypes_properties binary_format_parser
  binary_format_printer binary_uleb128 tail_call_parser_properties
  tail_call_codec_properties.

Lemma parse_expr_end : forall n (Hle : (1 <= n)%nat),
    option_map observe_reader
      (runParser (parse_expr :
        Parser (SizedList Byte.byte) Byte.byte option (list basic_instruction) n)
        Hle (mkSizedList (x0b :: nil))) = Some (nil, nil).
Proof.
  intros n Hle.
  unfold parse_expr, parse_bes_end_with_x0b, language, Fix, Induction.extract.
  cbn [FixBox call _bes_end_with_x0b].
  reflexivity.
Qed.

Lemma parse_expr_tail_prefix : forall n opcode b input instruction suffix
    (Hle : (List.length (opcode :: b :: input) <= n)%nat),
    opcode = x12 \/ opcode = x13 ->
    return_call_prefix (opcode :: b :: input) instruction (x0b :: suffix) \/
      return_call_indirect_prefix
        (opcode :: b :: input) instruction (x0b :: suffix) ->
    option_map observe_reader
      (runParser (parse_expr :
        Parser (SizedList Byte.byte) Byte.byte option (list basic_instruction) n)
        Hle (mkSizedList (opcode :: b :: input))) =
      Some (instruction :: nil, suffix).
Proof.
  intros n opcode b input instruction suffix Hle Hopcode Hgrammar.
  destruct n as [|n]; [cbn in Hle; lia |].
  pose proof (proj2 (tail_call_parser_sound_complete
    (S n) (List.length (opcode :: b :: input)) Hle
    (mkSizedList (opcode :: b :: input)) instruction (x0b :: suffix))
    Hgrammar) as Hobs.
  destruct (runParser (parse_tail_call :
    Parser (SizedList Byte.byte) Byte.byte option basic_instruction (S n))
    Hle (mkSizedList (opcode :: b :: input))) as [result|] eqn:Htail;
    [|discriminate].
  destruct result as [value remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hobs.
  inversion Hobs; subst value rest.
  cbn in Hlength. subst remaining.
  unfold parse_expr, parse_bes_end_with_x0b, language, Fix, Induction.extract.
  cbn [FixBox call _bes_end_with_x0b].
  unfold Combinators.alt, Combinators.app, Combinators.bind,
    Combinators.andbind, Combinators.and, Combinators.map,
    Combinators.cmap, exact_byte, Combinators.guardM.
  cbn [runParser anyTok Success.getTok sizedList uncons listUncons
    Success.fromView Success.guardM option_map uncurry Success.value
    Success.size Success.small Success.leftovers].
  destruct Hopcode as [-> | ->];
    cbn [fromOption pure fail _pure _fail optionRawApplicative
      optionRawAlternative Success.guardM Success.value option_map];
    cbn [List.length] in Htail |- *;
    rewrite Htail;
    reflexivity.
Qed.

Lemma parse_expr_single_tail : forall opcode b input instruction,
    opcode = x12 \/ opcode = x13 ->
    return_call_prefix (opcode :: b :: input) instruction (x0b :: nil) \/
      return_call_indirect_prefix (opcode :: b :: input) instruction (x0b :: nil) ->
    run_parse_expr (opcode :: b :: input) = Some (instruction :: nil).
Proof.
  intros opcode b input instruction Hopcode Hgrammar.
  unfold run_parse_expr.
  rewrite run_option_parser_characterization.
  now apply parse_expr_tail_prefix.
Qed.

Corollary parse_expr_tail_prefix_sized :
    forall n m (input : SizedList Byte.byte m)
      opcode b rest instruction suffix (Hle : (m <= n)%nat),
    @Sized.value _ _ _ input = opcode :: b :: rest ->
    opcode = x12 \/ opcode = x13 ->
    return_call_prefix (opcode :: b :: rest) instruction (x0b :: suffix) \/
      return_call_indirect_prefix
        (opcode :: b :: rest) instruction (x0b :: suffix) ->
    option_map observe_reader
      (runParser (parse_expr :
        Parser (SizedList Byte.byte) Byte.byte option (list basic_instruction) n)
        Hle input) = Some (instruction :: nil, suffix).
Proof.
  intros n m [input Hlength] opcode b rest instruction suffix
    Hle Hinput Hopcode Hgrammar.
  cbn [Sized.value] in Hinput. subst input.
  subst m. now apply parse_expr_tail_prefix.
Qed.

Theorem run_parse_tail_expr_complete : forall input instruction,
    return_call_prefix input instruction (x0b :: nil) \/
      return_call_indirect_prefix input instruction (x0b :: nil) ->
    run_parse_expr input = Some (instruction :: nil).
Proof.
  intros input instruction Hgrammar.
  destruct input as [|opcode input].
  - destruct Hgrammar as [H | H]; inversion H.
  - assert (Hopcode : opcode = x12 \/ opcode = x13).
    { destruct Hgrammar as [H | H]; inversion H; auto. }
    destruct input as [|b input].
    + destruct Hgrammar as [H | H]; inversion H; subst;
        match goal with
        | Hindex : u32_prefix nil _ _ |- _ =>
            destruct Hindex as [Hindex _]; inversion Hindex
        end.
    + now apply parse_expr_single_tail.
Qed.

Theorem return_call_expr_roundtrip : forall index,
    (index <= 4294967295)%N ->
    run_parse_expr (binary_of_expr (BI_return_call index :: nil)) =
      Some (BI_return_call index :: nil).
Proof.
  intros index Hbound.
  unfold binary_of_expr. cbn [List.map List.concat].
  rewrite List.app_nil_r.
  apply run_parse_tail_expr_complete. left.
  now apply return_call_print_prefix.
Qed.

Theorem return_call_indirect_expr_roundtrip : forall table type,
    (table <= 4294967295)%N ->
    (type <= 4294967295)%N ->
    run_parse_expr (binary_of_expr (BI_return_call_indirect table type :: nil)) =
      Some (BI_return_call_indirect table type :: nil).
Proof.
  intros table type Htable Htype.
  unfold binary_of_expr. cbn [List.map List.concat].
  rewrite List.app_nil_r.
  apply run_parse_tail_expr_complete. right.
  now apply return_call_indirect_print_prefix.
Qed.
