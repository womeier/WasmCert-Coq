(** Properties of the parsers used by [run_parse_module_str].

    The option instances below are the instances selected by the extracted
    module parser.  RawMonad/RawApplicative do not require laws, so these
    results must not be generalized to arbitrary instances without additional
    hypotheses.

    This file verifies the byte-count and numeric-range guards on the actual
    Parseque execution path.  It does not yet prove the recursive LEB128
    parser's correspondence to the integer encoding grammar. *)
From Wasm Require Import binary_format_parser datatypes.
From Wasm Require Import addressing addressing_binary addressing_parseque.
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
    intro Hparse.
    cbn [parse_u32_as_N AddressingParseque.parse_address runParser
      Category.fromOption] in Hparse.
    destruct (AddressingParseque.decode_address_tokens Addressing.AT_i32 input)
      as [decoded|] eqn:Decoded; cbn in Hparse; [|discriminate].
    inversion Hparse; subst decoded.
    apply AddressingParseque.decode_address_tokens_guards in Decoded.
    destruct Decoded as [Value Bytes].
    change (Success.value s < 4294967296)%N in Value.
    change (m - Success.size s <= 5)%nat in Bytes.
    split; lia.
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
