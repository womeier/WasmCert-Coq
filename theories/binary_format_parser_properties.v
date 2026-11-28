(** Shared prefix lemmas for the binary parser actually used by extraction.
    These verify individual building blocks, not the complete module grammar. *)
From Stdlib Require Import List Strings.Byte NArith.
From parseque Require Import Parseque Success.
From Wasm Require Import binary_format_parser binary_uleb128.

Lemma parse_u32_as_N_correct : forall n m (Hle : (m <= n)%nat)
    (input : SizedList byte m) value suffix,
    option_map observe_reader
      (runParser (parse_u32_as_N :
        Parser (SizedList byte) byte option N n) Hle input) =
      Some (value, suffix) <->
    u32_prefix (@Sized.value _ _ _ input) value suffix.
Proof. intros. apply parse_bounded_u32_correct. Qed.

Lemma sized_parser_correct : forall A n m (Hle : (m <= n)%nat)
    (parser : Parser (SizedList byte) byte option A n)
    (input : SizedList byte m) value suffix,
    option_map observe_reader (runParser parser Hle input) =
      Some (value, suffix) ->
    option_map observe_reader
      (runParser (sized_parser parser) Hle input) =
      Some ((value, N.of_nat (m - List.length suffix)), suffix).
Proof.
  intros A n m Hle parser input value suffix Hobs.
  unfold sized_parser; cbn [runParser].
  destruct (runParser parser Hle input) as [result|]; [|discriminate].
  destruct result as [v remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hobs.
  inversion Hobs; subst v rest.
  subst remaining.
  reflexivity.
Qed.

Lemma assert_sized_correct : forall A n m (Hle : (m <= n)%nat)
    (parser : Parser (SizedList byte) byte option A n)
    (input : SizedList byte m) value suffix constraint,
    option_map observe_reader (runParser parser Hle input) =
      Some (value, suffix) ->
    constraint (N.of_nat (m - List.length suffix)) = true ->
    option_map observe_reader
      (runParser (assert_sized parser constraint) Hle input) =
      Some (value, suffix).
Proof.
  intros A n m Hle parser input value suffix constraint Hobs Hconstraint.
  pose proof (sized_parser_correct A n m Hle parser input value suffix Hobs)
    as Hsized.
  unfold assert_sized, Combinators.guardM; cbn [runParser].
  destruct (runParser (sized_parser parser) Hle input) as [result|];
    [|discriminate].
  destruct result as [[v count] remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hsized.
  inversion Hsized; subst v count rest.
  unfold Category.bind, fromOption, Success.guardM.
  cbn [Success.value option_map _bind optionRawMonad option_rect].
  rewrite Hconstraint.
  reflexivity.
Qed.

Lemma assert_sized_reject : forall A n m (Hle : (m <= n)%nat)
    (parser : Parser (SizedList byte) byte option A n)
    (input : SizedList byte m) value suffix constraint,
    option_map observe_reader (runParser parser Hle input) =
      Some (value, suffix) ->
    constraint (N.of_nat (m - List.length suffix)) = false ->
    runParser (assert_sized parser constraint) Hle input = None.
Proof.
  intros A n m Hle parser input value suffix constraint Hobs Hconstraint.
  pose proof (sized_parser_correct A n m Hle parser input value suffix Hobs)
    as Hsized.
  unfold assert_sized, Combinators.guardM; cbn [runParser].
  destruct (runParser (sized_parser parser) Hle input) as [result|];
    [|discriminate].
  destruct result as [[v count] remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hsized.
  inversion Hsized; subst v count rest.
  unfold Category.bind, fromOption, Success.guardM.
  cbn [Success.value option_map _bind optionRawMonad option_rect].
  rewrite Hconstraint.
  reflexivity.
Qed.

Lemma parse_vec_zero_prefix : forall A n m (Hle : (m <= n)%nat)
    (parser : Parser (SizedList byte) byte option A n)
    (input : SizedList byte m) suffix,
    u32_prefix (@Sized.value _ _ _ input) 0 suffix ->
    option_map observe_reader
      (runParser (parse_vec parser) Hle input) = Some (nil, suffix).
Proof.
  intros A n m Hle parser [input Hlength] suffix Hgrammar.
  cbn [Sized.value] in Hgrammar.
  destruct input as [|b input]; cbn in Hlength; subst m.
  - apply decode_u32_correct in Hgrammar. discriminate.
  - destruct (Byte.byte_eq_dec b x00) as [-> | Hbyte].
    + apply decode_u32_correct in Hgrammar.
      change (Some (0%N, input) = Some (0%N, suffix)) in Hgrammar.
      inversion Hgrammar; subst suffix.
      reflexivity.
    + assert (Hneq : datatypes_properties.byte_eqb b x00 = false).
      { unfold datatypes_properties.byte_eqb.
        destruct (Byte.byte_eq_dec b x00); cbn; congruence. }
      pose proof (proj2 (parse_u32_as_N_correct n _ Hle
        (mkSizedList (b :: input)) 0 suffix) Hgrammar) as Hhead.
      unfold parse_vec, parse_vec_length, Combinators.alt,
        Combinators.cmap, Combinators.map, exact_byte, Combinators.guardM.
      cbn [runParser anyTok Success.getTok sizedList uncons listUncons
        Success.fromView Success.guardM option_map uncurry Success.value
        Success.size Success.small Success.leftovers].
      unfold Combinators.map, Category.bind, Category.alt, Category.fmap,
        fromOption, Success.guardM.
      cbn [runParser anyTok Success.getTok sizedList uncons listUncons
        Success.fromView Success.guardM option_map uncurry Success.value
        Success.size Success.small Success.leftovers
        _bind _alt _fmap _pure _fail optionRawMonad optionRawAlternative
        optionRawFunctor optionRawApplicative pure fail].
      cbn -[parse_u32_as_N].
      rewrite Hneq.
      cbn -[parse_u32_as_N].
      match goal with
      | |- context [runParser ?reader ?bound ?tokens] =>
          change (option_map observe_reader (runParser reader bound tokens) =
            Some (0%N, suffix)) in Hhead;
          destruct (runParser reader bound tokens) as [result|]
      end; [|discriminate].
      destruct result as [value remaining Hsmall [rest Hlen]].
      cbn [observe_reader Success.value Success.leftovers Sized.value] in Hhead.
      inversion Hhead; subst value rest.
      reflexivity.
Qed.

Lemma parser_map_prefix : forall A B n m (Hle : (m <= n)%nat)
    (parser : Parser (SizedList byte) byte option A n)
    (f : A -> B) (input : SizedList byte m) value suffix,
    option_map observe_reader (runParser parser Hle input) =
      Some (value, suffix) ->
    option_map observe_reader
      (runParser (Combinators.map f parser) Hle input) =
      Some (f value, suffix).
Proof.
  intros A B n m Hle parser f input value suffix Hobs.
  unfold Combinators.map; cbn [runParser].
  destruct (runParser parser Hle input) as [result|]; [|discriminate].
  destruct result as [v remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hobs.
  inversion Hobs; subst v rest.
  reflexivity.
Qed.

Lemma parser_and_prefix : forall A B n m (Hle : (m <= n)%nat)
    (first : Parser (SizedList byte) byte option A n)
    (second : Parser (SizedList byte) byte option B n)
    (input : SizedList byte m) a middle b suffix,
    option_map observe_reader (runParser first Hle input) =
      Some (a, middle) ->
    (forall k (Hkn : (k <= n)%nat) (tokens : SizedList byte k),
      @Sized.value _ _ _ tokens = middle ->
      option_map observe_reader (runParser second Hkn tokens) =
        Some (b, suffix)) ->
    option_map observe_reader
      (runParser (Combinators.and first second) Hle input) =
      Some ((a, b), suffix).
Proof.
  intros A B n m Hle first second input a middle b suffix Hfirst Hsecond.
  unfold Combinators.and, Combinators.andbind; cbn [runParser].
  destruct (runParser first Hle input) as [result|]; [|discriminate].
  destruct result as [v remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hfirst.
  inversion Hfirst; subst v rest.
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn.
  match goal with
  | |- context [runParser ?parser ?bound ?tokens] =>
      pose proof (Hsecond _ bound tokens eq_refl) as Hnext;
      change (option_map observe_reader (runParser parser bound tokens) =
        Some (b, suffix)) in Hnext;
      destruct (runParser parser bound tokens) as [result|]
  end; [|discriminate].
  destruct result as [v after Hnext_small [rest Hnext_length]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hnext.
  inversion Hnext; subst v rest.
  reflexivity.
Qed.
