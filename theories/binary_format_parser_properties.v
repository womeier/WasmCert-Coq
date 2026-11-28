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

Lemma parser_map_prefix_inv : forall A B n m (Hle : (m <= n)%nat)
    (parser : Parser (SizedList byte) byte option A n)
    (f : A -> B) (input : SizedList byte m) value suffix,
    option_map observe_reader
      (runParser (Combinators.map f parser) Hle input) =
      Some (value, suffix) ->
    exists original, f original = value /\
      option_map observe_reader (runParser parser Hle input) =
        Some (original, suffix).
Proof.
  intros A B n m Hle parser f input value suffix Hobs.
  unfold Combinators.map in Hobs; cbn [runParser] in Hobs.
  destruct (runParser parser Hle input) as [result|]; [|discriminate].
  destruct result as [original remaining Hsmall [rest Hlength]].
  change (Some (f original, rest) = Some (value, suffix)) in Hobs.
  inversion Hobs; subst value suffix.
  exists original. split; reflexivity.
Qed.

Lemma parser_alt_prefix_inv : forall A n m (Hle : (m <= n)%nat)
    (first second : Parser (SizedList byte) byte option A n)
    (input : SizedList byte m) value suffix,
    option_map observe_reader
      (runParser (Combinators.alt first second) Hle input) =
      Some (value, suffix) ->
    option_map observe_reader (runParser first Hle input) =
      Some (value, suffix) \/
    option_map observe_reader (runParser second Hle input) =
      Some (value, suffix).
Proof.
  intros A n m Hle first second input value suffix Hobs.
  unfold Combinators.alt in Hobs; cbn [runParser] in Hobs.
  destruct (runParser first Hle input).
  - left. exact Hobs.
  - right. exact Hobs.
Qed.

Lemma parser_and_prefix_sound : forall A B n
    (first : Parser (SizedList byte) byte option A n)
    (second : Parser (SizedList byte) byte option B n)
    (first_grammar : list byte -> A -> list byte -> Prop)
    (second_grammar : list byte -> B -> list byte -> Prop),
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      option_map observe_reader (runParser first Hle input) =
        Some (value, suffix) ->
      first_grammar (@Sized.value _ _ _ input) value suffix) ->
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      option_map observe_reader (runParser second Hle input) =
        Some (value, suffix) ->
      second_grammar (@Sized.value _ _ _ input) value suffix) ->
    forall m (Hle : (m <= n)%nat) (input : SizedList byte m) a b suffix,
    option_map observe_reader
      (runParser (Combinators.and first second) Hle input) =
      Some ((a, b), suffix) ->
    exists middle,
      first_grammar (@Sized.value _ _ _ input) a middle /\
      second_grammar middle b suffix.
Proof.
  intros A B n first second first_grammar second_grammar
    Hfirst Hsecond m Hle input a b suffix Hobs.
  unfold Combinators.and, Combinators.andbind in Hobs; cbn [runParser] in Hobs.
  destruct (runParser first Hle input) as [result|] eqn:Hraw;
    [|discriminate].
  destruct result as [v remaining Hsmall [middle Hlength]].
  cbn [Combinators.box le_close Combinators.le_lower call runParser] in Hobs.
  cbn in Hobs.
  match goal with
  | Hobs : context [runParser ?parser ?bound ?tokens] |- _ =>
      pose proof (Hsecond _ bound tokens) as Hsecond_at;
      change (forall value rest,
        option_map observe_reader (runParser parser bound tokens) =
          Some (value, rest) ->
        second_grammar middle value rest) in Hsecond_at;
      destruct (runParser parser bound tokens) as [result|]
  end; [|discriminate].
  destruct result as [w after Hafter_small [rest Hafter_length]].
  change (Some ((v, w), rest) = Some ((a, b), suffix)) in Hobs.
  inversion Hobs; subst a b suffix.
  exists middle. split.
  - apply Hfirst with (Hle := Hle) (input := input).
    rewrite Hraw. reflexivity.
  - apply Hsecond_at. reflexivity.
Qed.

Lemma parser_bind_prefix : forall A B n m (Hle : (m <= n)%nat)
    (first : Parser (SizedList byte) byte option A n)
    (next : A -> Parser (SizedList byte) byte option B n)
    (input : SizedList byte m) a middle b suffix,
    option_map observe_reader (runParser first Hle input) =
      Some (a, middle) ->
    (forall k (Hkn : (k <= n)%nat) (tokens : SizedList byte k),
      @Sized.value _ _ _ tokens = middle ->
      option_map observe_reader (runParser (next a) Hkn tokens) =
        Some (b, suffix)) ->
    option_map observe_reader
      (runParser (Combinators.bind first next) Hle input) =
      Some (b, suffix).
Proof.
  intros A B n m Hle first next input a middle b suffix Hfirst Hnext.
  unfold Combinators.bind, Combinators.andbind, Combinators.map.
  cbn [runParser].
  destruct (runParser first Hle input) as [result|]; [|discriminate].
  destruct result as [v remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hfirst.
  inversion Hfirst; subst v rest.
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn.
  match goal with
  | |- context [runParser ?parser ?bound ?tokens] =>
      pose proof (Hnext _ bound tokens eq_refl) as Hafter;
      change (option_map observe_reader (runParser parser bound tokens) =
        Some (b, suffix)) in Hafter;
      destruct (runParser parser bound tokens) as [result|]
  end; [|discriminate].
  destruct result as [v after Hafter_small [rest Hafter_length]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hafter.
  inversion Hafter; subst v rest.
  reflexivity.
Qed.

Lemma parser_bind_prefix_sound : forall A B n
    (first : Parser (SizedList byte) byte option A n)
    (next : A -> Parser (SizedList byte) byte option B n)
    (first_grammar : list byte -> A -> list byte -> Prop)
    (next_grammar : A -> list byte -> B -> list byte -> Prop),
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      option_map observe_reader (runParser first Hle input) =
        Some (value, suffix) ->
      first_grammar (@Sized.value _ _ _ input) value suffix) ->
    (forall a m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      option_map observe_reader (runParser (next a) Hle input) =
        Some (value, suffix) ->
      next_grammar a (@Sized.value _ _ _ input) value suffix) ->
    forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
    option_map observe_reader
      (runParser (Combinators.bind first next) Hle input) =
      Some (value, suffix) ->
    exists a middle, first_grammar (@Sized.value _ _ _ input) a middle /\
      next_grammar a middle value suffix.
Proof.
  intros A B n first next first_grammar next_grammar Hfirst Hnext
    m Hle input value suffix Hobs.
  unfold Combinators.bind, Combinators.andbind, Combinators.map in Hobs.
  cbn [runParser] in Hobs.
  destruct (runParser first Hle input) as [result|] eqn:Hraw; [|discriminate].
  destruct result as [a remaining Hsmall [middle Hlength]].
  cbn [Combinators.box le_close Combinators.le_lower call runParser] in Hobs.
  cbn in Hobs.
  match goal with
  | Hobs : context [runParser ?parser ?bound ?tokens] |- _ =>
      pose proof (Hnext a _ bound tokens) as Hafter;
      change (forall v rest,
        option_map observe_reader (runParser parser bound tokens) =
          Some (v, rest) -> next_grammar a middle v rest) in Hafter;
      destruct (runParser parser bound tokens) as [result|]
  end; [|discriminate].
  destruct result as [v after Hafter_small [rest Hafter_length]].
  change (Some (v, rest) = Some (value, suffix)) in Hobs.
  inversion Hobs; subst v rest.
  exists a, middle. split.
  - apply Hfirst with (Hle := Hle) (input := input).
    rewrite Hraw. reflexivity.
  - apply Hafter. reflexivity.
Qed.

(** Properties of the parsers used by [run_parse_module_str].

    The option instances below are the instances selected by the extracted
    module parser.  RawMonad/RawApplicative do not require laws, so these
    results must not be generalized to arbitrary instances without additional
    hypotheses.

    This file verifies the byte-count and numeric-range guards on the actual
    Parseque execution path.  It does not yet prove the recursive LEB128
    parser's correspondence to the integer encoding grammar. *)
Close Scope N_scope.
From Wasm Require Import binary_format_parser datatypes.
From Stdlib Require Import ZArith Lia.
From parseque Require Import Parseque.

Section OptionParsers.
  Context {Toks : nat -> Type}.
  Context {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  Lemma run_guardM_option {A B : Type} (f : A -> option B)
      (p : Parser Toks Byte.byte option A n) :
    runParser (Combinators.guardM f p) bound input =
    match runParser p bound input with
    | Some s => Success.guardM f s
    | None => None
    end.
  Proof.
    unfold Combinators.guardM.
    simpl. destruct (runParser p bound input) as [s|]; [|reflexivity].
    simpl. destruct (Success.guardM f s); reflexivity.
  Qed.

  Lemma run_alt_option {A : Type}
      (p q : Parser Toks Byte.byte option A n) :
    runParser (Combinators.alt p q) bound input =
    match runParser p bound input with
    | Some s => Some s
    | None => runParser q bound input
    end.
  Proof.
    unfold Combinators.alt. simpl.
    destruct (runParser p bound input); reflexivity.
  Qed.

  Lemma run_sized_parser_option {A : Type} (p : Parser Toks Byte.byte option A n) :
    runParser (sized_parser p) bound input =
    option_map
      (fun s => Success.MkSuccess
        (Success.value s, N.of_nat (m - Success.size s))
        (Success.small s) (Success.leftovers s))
      (runParser p bound input).
  Proof.
    unfold sized_parser. simpl.
    destruct (runParser p bound input) as [[a k Hk rest]|]; reflexivity.
  Qed.

  Lemma run_assert_sized_option {A : Type} (p : Parser Toks Byte.byte option A n)
      (constraint : N -> bool) :
    runParser (assert_sized p constraint) bound input =
    match runParser p bound input with
    | Some s =>
        if constraint (N.of_nat (m - Success.size s)) then Some s else None
    | None => None
    end.
  Proof.
    unfold assert_sized.
    rewrite run_guardM_option, run_sized_parser_option.
    destruct (runParser p bound input) as [[a k Hk rest]|]; simpl.
    unfold Success.guardM; simpl.
    - destruct (constraint (N.of_nat (m - k))); reflexivity.
    - reflexivity.
  Qed.

  Lemma assert_sized_option_correct {A : Type}
      (p : Parser Toks Byte.byte option A n) (constraint : N -> bool) s :
    runParser (assert_sized p constraint) bound input = Some s <->
    runParser p bound input = Some s /\
    constraint (N.of_nat (m - Success.size s)) = true.
  Proof.
    rewrite run_assert_sized_option.
    destruct (runParser p bound input) as [r|] eqn:H.
    - destruct (constraint (N.of_nat (m - Success.size r))) eqn:C.
      + split.
        * intro E; inversion E; subst. auto.
        * intros [E _]; inversion E; subst. reflexivity.
      + split; [discriminate |].
        intros [E D]; inversion E; subst. congruence.
    - split; [discriminate | intros [E _]; discriminate].
  Qed.

  Lemma guardM_option_success {A B : Type} (f : A -> option B)
      (p : Parser Toks Byte.byte option A n) s :
    runParser (Combinators.guardM f p) bound input = Some s ->
    exists r,
      runParser p bound input = Some r /\
      f (Success.value r) = Some (Success.value s) /\
      Success.size r = Success.size s.
  Proof.
    rewrite run_guardM_option.
    destruct (runParser p bound input) as [[a k Hk rest]|] eqn:H;
      [|discriminate].
    unfold Success.guardM; simpl.
    destruct (f a) as [b|] eqn:F; [|discriminate].
    intro E; inversion E; subst.
    eexists; repeat split; eauto.
  Qed.
End OptionParsers.

Section IntegerGuards.
  Context {Toks : nat -> Type} `{Sized Toks Byte.byte}.
  Context {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  (** Both guards are necessary: the value guard rejects overflow, while the
      consumed-byte guard rejects overlong encodings of an in-range value. *)
  Lemma parse_u32_as_N_guards s :
    runParser (@parse_u32_as_N Toks _ option _ _ _ n)
      bound input = Some s ->
    (Success.value s <= 4294967295)%N /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_u32_as_N, parse_bounded_u32.
    cbn [runParser]. intro Hparse.
    assert (Hread : read_u32 input = Some s).
    { destruct (read_u32 input); cbn in Hparse; congruence. }
    unfold read_u32 in Hread.
    destruct (read_uleb 5 input) as [r|] eqn:R; [|discriminate].
    destruct (N.leb (Success.value r) 4294967295) eqn:B; [|discriminate].
    inversion Hread; subst s.
    split.
    - now apply N.leb_le.
    - pose proof (read_uleb_consumed_bound 5 m input r R). lia.
  Qed.

  Lemma parse_u8_as_N_guards s :
    runParser (@parse_u8_as_N Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (Success.value s <= 255)%N /\
    (N.of_nat (m - Success.size s) <= 2)%N.
  Proof.
    unfold parse_u8_as_N. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (N.leb (Success.value r) 255) eqn:B; [|discriminate].
    inversion V.
    apply assert_sized_option_correct in R.
    destruct R as [_ W].
    split.
    - now apply N.leb_le.
    - rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_s32_guards s :
    runParser (@parse_s32 Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    exists z,
      Success.value s = Wasm_int.Int32.repr z /\
      Wasm_int.Int32.signed (Success.value s) = z /\
      (-2147483648 <= z <= 2147483647)%Z /\
      (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_s32. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (andb (Z.leb (Success.value r) 2147483647)
              (Z.leb (-2147483648) (Success.value r))) eqn:B; [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Upper Lower].
    apply Z.leb_le in Upper. apply Z.leb_le in Lower.
    inversion V.
    apply assert_sized_option_correct in R. destruct R as [_ W].
    exists (Success.value r).
    split; [reflexivity |].
    split.
    - apply Wasm_int.Int32.signed_repr.
      change (-2147483648 <= Success.value r <= 2147483647)%Z. lia.
    - split; [lia |]. rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_s64_guards s :
    runParser (@parse_s64 Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    exists z,
      Success.value s = Wasm_int.Int64.repr z /\
      Wasm_int.Int64.signed (Success.value s) = z /\
      (-9223372036854775808 <= z <= 9223372036854775807)%Z /\
      (N.of_nat (m - Success.size s) <= 10)%N.
  Proof.
    unfold parse_s64. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (andb (Z.leb (Success.value r) 9223372036854775807)
              (Z.leb (-9223372036854775808) (Success.value r))) eqn:B;
      [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Upper Lower].
    apply Z.leb_le in Upper. apply Z.leb_le in Lower.
    inversion V.
    apply assert_sized_option_correct in R. destruct R as [_ W].
    exists (Success.value r).
    split; [reflexivity |].
    split.
    - apply Wasm_int.Int64.signed_repr.
      change (-9223372036854775808 <= Success.value r <=
        9223372036854775807)%Z. lia.
    - split; [lia |]. rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_s33_guards s :
    runParser (@parse_s33 Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (-4294967296 <= Success.value s <= 4294967295)%Z /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_s33. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (andb (Z.leb (-4294967296) (Success.value r))
              (Z.leb (Success.value r) 4294967295)) eqn:B;
      [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Lower Upper].
    apply Z.leb_le in Lower. apply Z.leb_le in Upper.
    inversion V.
    apply assert_sized_option_correct in R. destruct R as [_ W].
    split; [lia |]. rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_heap_typeidx_guards s :
    runParser (@parse_heap_typeidx Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (Success.value s <= 4294967295)%N /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_heap_typeidx. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (Z.leb 0 (Success.value r)) eqn:B; [|discriminate].
    apply Z.leb_le in B.
    inversion V.
    apply parse_s33_guards in R. destruct R as [Range Width].
    split.
    - apply N2Z.inj_le. rewrite Z2N.id; lia.
    - rewrite <- S. exact Width.
  Qed.

  Lemma parse_source_heap_type_cases s :
    runParser (@parse_source_heap_type Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (exists h, Success.value s = gc_types.shared_heap_of_abstract h) \/
    (exists x, Success.value s = HT_type x /\
      (x <= 4294967295)%N /\
      (N.of_nat (m - Success.size s) <= 5)%N).
  Proof.
    unfold parse_source_heap_type.
    rewrite run_alt_option.
    intro Parsed.
    change
      (match option_map (Success.map gc_types.shared_heap_of_abstract)
        (runParser
          (@parse_gc_abstract_heap_type Toks _ option _ _ _ _ _ _ n) bound input)
       with
       | Some result => Some result
       | None => option_map (Success.map HT_type)
           (runParser (@parse_heap_typeidx Toks _ option _ _ _ _ _ _ n) bound input)
       end = Some s) in Parsed.
    destruct (runParser
      (@parse_gc_abstract_heap_type Toks _ option _ _ _ _ _ _ n) bound input)
      as [abstract|] eqn:Abstract; cbn [option_map] in Parsed.
    - inversion Parsed; subst.
      left. exists (Success.value abstract). reflexivity.
    - destruct (runParser
        (@parse_heap_typeidx Toks _ option _ _ _ _ _ _ n) bound input)
        as [index|] eqn:Index; cbn [option_map] in Parsed; [|discriminate].
      inversion Parsed; subst.
      right. exists (Success.value index). split; [reflexivity |].
      now apply parse_heap_typeidx_guards in Index.
  Qed.

  Lemma parse_source_heap_index_guards s x :
    runParser (@parse_source_heap_type Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    Success.value s = HT_type x ->
    (x <= 4294967295)%N /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    intros Parsed Value.
    apply parse_source_heap_type_cases in Parsed.
    destruct Parsed as [[h Abstract] | [index [Index Guards]]].
    - rewrite Value in Abstract. destruct h; discriminate.
    - rewrite Value in Index. inversion Index; subst. exact Guards.
  Qed.
End IntegerGuards.

Section VectorLengths.
  Context {Toks : nat -> Type} `{Sized Toks Byte.byte}.
  Context {A : Type} {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  (** This theorem covers every successful representation of a zero u32
      length, not just the canonical single zero byte. *)
  Lemma parse_vec_zero_length
      (p : Parser Toks Byte.byte option A n) s :
    runParser (@parse_vec_length Toks _ option _ _ _ n)
      bound input = Some s ->
    Success.value s = 0%N ->
    runParser (parse_vec p) bound input =
      Some (Success.map (fun _ => @nil A) s).
  Proof.
    intros R V.
    unfold parse_vec.
    rewrite run_alt_option, run_guardM_option, R.
    unfold Success.guardM. rewrite V. simpl.
    reflexivity.
  Qed.

  (** For positive counts, the previous length-and-elements parser is used
      unchanged: the zero-count case cannot swallow a nonempty vector. *)
  Lemma parse_vec_positive_length
      (p : Parser Toks Byte.byte option A n) s :
    runParser (@parse_vec_length Toks _ option _ _ _ n)
      bound input = Some s ->
    Success.value s <> 0%N ->
    runParser (parse_vec p) bound input =
    runParser
      (Combinators.bind parse_vec_length (fun k => parse_vec_aux p k))
      bound input.
  Proof.
    intros R V.
    unfold parse_vec.
    rewrite run_alt_option, run_guardM_option, R.
    unfold Success.guardM.
    destruct (N.eqb (Success.value s) 0) eqn:Z; simpl.
    - apply N.eqb_eq in Z. contradiction.
    - reflexivity.
  Qed.
End VectorLengths.

Section CompleteInputs.
  Context {A : Type}.

  (** [run] is the entry point used by [run_parse_module] and hence by the
      extracted interpreter.  In its option instance, a result is accepted
      exactly when the underlying parser succeeds and consumes all input. *)
  Lemma run_option_correct
      (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n)
      bs a :
    @run option _ _ _ _ Byte.byte tokBytes A bs p = Some a <->
    exists s,
      runParser (p (List.length bs)) (Nat.le_refl _) (mkSizedList bs) = Some s /\
      Success.value s = a /\ Success.size s = 0.
  Proof.
    unfold run, fromText, tokenize; simpl.
    destruct (runParser (p (List.length bs)) (Nat.le_refl _)
      (mkSizedList bs)) as [[v k Hk rest]|] eqn:R; simpl.
    - destruct k; simpl.
      + split.
        * intro E; inversion E; subst.
          eexists; repeat split; reflexivity.
        * intros [s [E [V S]]]; inversion E; subst.
          reflexivity.
      + split; [discriminate |].
        intros [s [E [V S]]]; inversion E; subst; discriminate.
    - split; [discriminate | intros [s [E _]]; discriminate].
  Qed.

  Lemma run_option_has_no_leftovers
      (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n)
      bs a :
    @run option _ _ _ _ Byte.byte tokBytes A bs p = Some a ->
    exists s,
      runParser (p (List.length bs)) (Nat.le_refl _) (mkSizedList bs) = Some s /\
      Success.value s = a /\
      @Sized.value _ _ _ (Success.leftovers s) = nil.
  Proof.
    rewrite run_option_correct.
    intros [s [R [V S]]]. exists s. split; [exact R |].
    split; [exact V |].
    pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as L.
    rewrite S in L.
    destruct (@Sized.value _ _ _ (Success.leftovers s));
      [reflexivity | discriminate].
  Qed.
End CompleteInputs.

Lemma run_typeidx_guards bs x :
  @run option _ _ _ _ Byte.byte tokBytes N bs (fun _ => parse_typeidx) = Some x ->
  (x <= 4294967295)%N /\ (N.of_nat (List.length bs) <= 5)%N.
Proof.
  rewrite run_option_correct.
  intros [s [R [V S]]].
  unfold parse_typeidx in R.
  apply parse_u32_as_N_guards in R.
  rewrite V, S, Nat.sub_0_r in R. exact R.
Qed.

Lemma run_heap_typeidx_guards bs x :
  run_parse_heap_typeidx bs = Some x ->
  (x <= 4294967295)%N /\ (N.of_nat (List.length bs) <= 5)%N.
Proof.
  unfold run_parse_heap_typeidx. rewrite run_option_correct.
  intros [s [R [V S]]].
  apply parse_heap_typeidx_guards in R.
  rewrite V, S, Nat.sub_0_r in R. exact R.
Qed.

Lemma run_vec_empty_count {A : Type}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) bs :
  @run option _ _ _ _ Byte.byte tokBytes N bs
    (fun _ => parse_vec_length) = Some 0%N ->
  @run option _ _ _ _ Byte.byte tokBytes (list A) bs
    (fun n => parse_vec (p n)) = Some nil.
Proof.
  rewrite run_option_correct.
  intros [s [R [V S]]].
  apply run_option_correct.
  exists (Success.map (fun _ => @nil A) s).
  split.
  - now apply parse_vec_zero_length.
  - split; [reflexivity | exact S].
Qed.
