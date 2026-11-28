(** Production custom-section iteration preserves byte grammar and values.
    These proofs follow Parseque's actual size-bounded recursion. *)
From Stdlib Require Import List Arith NArith Lia Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import binary_parser_combinator_properties
  binary_format_parser binary_format_parser_properties
  binary_format_vector_properties binary_format_optional_properties
  binary_parser_lookahead_properties
  leb128_properties utf8.

Lemma parser_sound_sized_parser {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_sound p P ->
  parser_sound (sized_parser p)
    (fun bs pair => P bs (fst pair) /\ snd pair = N.of_nat (length bs)).
Proof.
  intros H m bound input s Run.
  rewrite run_sized_parser_option in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  inversion Run; subst.
  destruct (H _ _ _ _ Raw) as [bs [Bytes Parsed]].
  exists bs; split; [exact Bytes |]. split; [exact Parsed |].
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers raw)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes raw) = Success.size raw) in Lout.
  rewrite Bytes, length_app in Lin. simpl. f_equal; lia.
Qed.

Definition name_encoding bs name :=
  utf8_valid name = true /\
  exists header, bs = header ++ name /\
    unsigned_leb header (N.of_nat (length name)) /\
    (N.of_nat (length name) <= 4294967295)%N /\ length header <= 5.

Definition custom_contents_encoding size bs result :=
  let '((name, name_size), payload) := result in
  exists name_bytes tail,
    bs = name_bytes ++ tail /\
    name_encoding name_bytes name /\
    name_size = N.of_nat (length name_bytes) /\
    optional_encoding
      (fun bytes payload => bytes = payload /\
        N.of_nat (length payload) = (size - name_size)%N) tail payload.

Definition custom_payload_encoding bs result :=
  let '(name, payload) := result in
  exists header name_bytes,
    bs = header ++ (name_bytes ++ payload) /\
    index_encoding header (N.of_nat (length name_bytes + length payload)) /\
    name_encoding name_bytes name.

Definition custom_section_encoding bs result :=
  exists payload, bs = x00 :: payload /\ custom_payload_encoding payload result.

Lemma parse_custom_contents_sound n size :
  parser_sound
    (Combinators.andmbind
      (sized_parser
        (parse_name (Toks := SizedList Byte.byte) (M := option) (n := n)))
      (fun '(name, name_size) => box
        (parse_vec_aux anyTok (size - name_size)%N)))
    (custom_contents_encoding size).
Proof.
  eapply parser_sound_andmbind with
    (P := fun bs pair =>
      name_encoding bs (fst pair) /\ snd pair = N.of_nat (length bs))
    (Q := fun pair bytes payload =>
      bytes = payload /\ N.of_nat (length payload) = (size - snd pair)%N).
  - apply parser_sound_sized_parser; apply parse_name_sound.
  - intros [name name_size] k lt; simpl.
    apply parser_sound_le_lower.
    eapply parser_sound_weaken; [apply parse_raw_bytes_sound |].
    intros bytes payload [Bytes Count]; subst payload; auto.
  - intros name_bytes tail [name name_size] payload [Name Size] Payload.
    exists name_bytes, tail.
    split; [reflexivity |]. split; [exact Name |].
    split; [exact Size |exact Payload].
Qed.

Theorem parse_customsec_sound n :
  parser_sound
    (parse_customsec (Toks := SizedList Byte.byte) (M := option) (n := n))
    custom_section_encoding.
Proof.
  unfold parse_customsec.
  apply parser_sound_prefix_byte with (Q := custom_payload_encoding).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_guardM with
      (P := fun bytes result =>
        let '(size, contents) := result in
        exists header body,
          bytes = header ++ body /\ index_encoding header size /\
          custom_contents_encoding size body contents).
    + eapply parser_sound_andbind with (P := index_encoding)
        (Q := custom_contents_encoding).
      * apply parse_index_sound.
      * intros size j lower; simpl.
        apply parser_sound_le_lower; apply parse_custom_contents_sound.
      * intros header body size contents Header Body.
        exists header, body. split; [reflexivity |]. auto.
    + intros bytes [size [[name name_size] payload]] result
        [header [body [Bytes [Header
        [name_bytes [tail [Body [Name [Size Payload]]]]]]]]] Result.
      destruct (N.ltb size name_size) eqn:Order; [discriminate |].
      apply N.ltb_ge in Order.
      destruct payload as [payload|].
      * inversion Result; subst result.
        destruct Payload as [Tail Count]; subst tail.
        exists header, name_bytes. split; [now rewrite Bytes, Body |].
        split; [|exact Name].
        replace (N.of_nat (length name_bytes + length payload)) with size;
          [exact Header |rewrite Nat2N.inj_add; lia].
      * destruct (N.eqb size name_size) eqn:Empty; [|discriminate].
        apply N.eqb_eq in Empty.
        inversion Result; subst result.
        change (tail = nil) in Payload; subst tail.
        exists header, name_bytes. split; [now rewrite Bytes, Body |].
        split; [|exact Name].
        replace (N.of_nat (length name_bytes + length nil)) with size;
          [exact Header |simpl; lia].
  - intros bs result E. exists bs; auto.
Qed.

Section Before.
Context {A : Type}.
Variable Custom : list Byte.byte -> Prop.
Variable Payload : list Byte.byte -> A -> Prop.

Inductive custom_before_encoding : list Byte.byte -> A -> Prop :=
| custom_before_payload : forall bs a,
    Payload bs a -> custom_before_encoding bs a
| custom_before_section : forall xs ys a,
    Custom xs -> custom_before_encoding ys a ->
    custom_before_encoding (xs ++ ys) a.

Definition identity_encoding bs (f : A -> A) :=
  Custom bs /\ forall a, f a = a.

Definition right_chain n :=
  @Combinators.RChain (SizedList Byte.byte) Byte.byte option A n.

Definition custom_before_step n (rec : Box right_chain n) : right_chain n :=
  fun op val => Combinators.alt (Combinators.iterater_aux n rec op val) val.

Lemma custom_before_step_sound n rec :
  (forall k (lt : k < n) op val,
    parser_sound op identity_encoding ->
    parser_sound val Payload ->
    parser_sound (call rec lt op val) custom_before_encoding) ->
  forall op val,
    parser_sound op identity_encoding ->
    parser_sound val Payload ->
    parser_sound (custom_before_step n rec op val) custom_before_encoding.
Proof.
  intros Rec op val Op Val.
  unfold custom_before_step. apply parser_sound_alt.
  - intros m bound input s Run.
    unfold Combinators.iterater_aux in Run; simpl in Run.
    destruct (runParser op bound input) as [sop|] eqn:Rop; [|discriminate].
    simpl in Run.
    match type of Run with
    | context [runParser ?tail ?lower ?tokens] =>
      assert (Tail : parser_sound tail custom_before_encoding);
      [apply Rec;
        unfold Combinators.lt_lower; apply parser_sound_le_lower; assumption
      |destruct (runParser tail lower tokens) as [res|] eqn:Rres]
    end; simpl in Run; [|discriminate].
    inversion Run; subst.
    destruct (Op _ _ _ _ Rop) as [xs [Ex [Cx Identity]]].
    destruct (Tail _ (Nat.le_refl _) _ _ Rres) as [ys [Ey Py]].
    exists (xs ++ ys); split.
    + change (input_bytes input = (xs ++ ys) ++ output_bytes res).
      rewrite Ex.
      change (xs ++ input_bytes (Success.leftovers sop) =
        (xs ++ ys) ++ output_bytes res).
      rewrite Ey; apply app_assoc.
    + change (custom_before_encoding (xs ++ ys)
        (Success.value sop (Success.value res))).
      rewrite Identity. now apply custom_before_section.
  - eapply parser_sound_weaken; [exact Val |].
    intros bs a H; now apply custom_before_payload.
Qed.

Theorem parser_sound_iterater_identity n
    (op : Parser (SizedList Byte.byte) Byte.byte option (A -> A) n)
    (val : Parser (SizedList Byte.byte) Byte.byte option A n) :
  parser_sound op identity_encoding ->
  parser_sound val Payload ->
  parser_sound (Combinators.iterater op val) custom_before_encoding.
Proof.
  change (parser_sound op identity_encoding -> parser_sound val Payload ->
    parser_sound ((Fix right_chain custom_before_step n) op val)
      custom_before_encoding).
  apply (fix_invariant custom_before_step
    (fun k chain => forall op val,
      parser_sound op identity_encoding -> parser_sound val Payload ->
      parser_sound (chain op val) custom_before_encoding)).
  exact custom_before_step_sound.
Qed.

End Before.

Definition custom_bytes bs :=
  exists result, custom_section_encoding bs result.

Lemma parse_customsec_forget_sound {A} n :
  parser_sound
    (parse_customsec_forget (Toks := SizedList Byte.byte)
      (M := option) (A := A) (n := n))
    (identity_encoding custom_bytes).
Proof.
  unfold parse_customsec_forget.
  eapply parser_sound_map; [apply parse_customsec_sound |].
  intros bs result E. split.
  - now exists result.
  - reflexivity.
Qed.

Theorem parse_with_customsec_star_before_sound {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_sound p P ->
  parser_sound (parse_with_customsec_star_before p)
    (custom_before_encoding custom_bytes P).
Proof.
  intro H. unfold parse_with_customsec_star_before.
  apply parser_sound_iterater_identity; [apply parse_customsec_forget_sound |exact H].
Qed.

Inductive custom_repetitions (Custom : list Byte.byte -> Prop) :
    list Byte.byte -> Prop :=
| custom_repetitions_nil : custom_repetitions Custom nil
| custom_repetitions_cons : forall xs ys,
    Custom xs -> custom_repetitions Custom ys ->
    custom_repetitions Custom (xs ++ ys).

Section After.
Context {A : Type}.
Variable Custom : list Byte.byte -> Prop.

Definition left_chain n :=
  @Combinators.LChain (SizedList Byte.byte) Byte.byte option A n.

Definition custom_after_step n (rec : Box left_chain n) : left_chain n :=
  fun sa op => Category.alt (Combinators.schainl_aux n rec sa op)
    (fun _ => Category.pure sa).

Definition after_chain_sound n (chain : left_chain n) :=
  forall sa op,
    (forall k (lt : k < n),
      parser_sound (call op lt) (identity_encoding Custom)) ->
    forall result, chain sa op = Some result ->
    exists bytes,
      input_bytes (Success.leftovers sa) = bytes ++ output_bytes result /\
      custom_repetitions Custom bytes /\
      Success.value result = Success.value sa.

Lemma custom_after_step_sound n rec :
  (forall k (lt : k < n), after_chain_sound k (call rec lt)) ->
  after_chain_sound n (custom_after_step n rec).
Proof.
  intros Rec sa op Op result Run.
  unfold custom_after_step in Run.
  destruct (Combinators.schainl_aux n rec sa op) as [res|] eqn:Step;
    simpl in Run.
  - inversion Run; subst result.
    unfold Combinators.schainl_aux in Step; simpl in Step.
    destruct (runParser (call op (Success.small sa))
      (Nat.le_refl _) (Success.leftovers sa)) as [sop|] eqn:Rop;
      simpl in Step; [|discriminate].
    match type of Step with
    | context [call rec ?lower ?state ?operators] =>
      assert (Tail : forall result,
        call rec lower state operators = Some result ->
        exists bytes,
          input_bytes (Success.leftovers state) = bytes ++ output_bytes result /\
          custom_repetitions Custom bytes /\
          Success.value result = Success.value state);
      [apply Rec; intros k lt; simpl; apply Op
      |destruct (call rec lower state operators) as [tail|] eqn:Rtail]
    end;
      pose proof (f_equal (option_map (Success.lt_lift (Success.small sa))) Rtail)
        as Lift;
      pose proof (eq_trans (eq_sym Lift) Step) as LiftStep;
      simpl in LiftStep; [|discriminate].
    inversion LiftStep; subst res.
    destruct (Op _ (Success.small sa) _ (Nat.le_refl _) _ _ Rop)
      as [xs [Ex [Cx Identity]]].
    destruct (Tail _ eq_refl) as [ys [Ey [Cy Value]]].
    exists (xs ++ ys); split.
    + change (input_bytes (Success.leftovers sa) =
        (xs ++ ys) ++ output_bytes tail).
      rewrite Ex.
      change (xs ++ output_bytes sop = (xs ++ ys) ++ output_bytes tail).
      change (output_bytes sop = ys ++ output_bytes tail) in Ey.
      rewrite Ey; apply app_assoc.
    + split; [now constructor |].
      change (Success.value tail = Success.value sa).
      rewrite Value. simpl. apply Identity.
  - inversion Run; subst result.
    exists nil. split; [reflexivity |]. split; [constructor |reflexivity].
Qed.

Lemma production_after_chain_sound n :
  after_chain_sound n
    (Combinators.schainl (Toks := SizedList Byte.byte) (Tok := Byte.byte)
      (M := option) (A := A) (n := n)).
Proof.
  change (after_chain_sound n (Fix left_chain custom_after_step n)).
  apply (fix_invariant custom_after_step after_chain_sound).
  exact custom_after_step_sound.
Qed.

Theorem parser_sound_iteratel_identity n
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (op : Box (Parser (SizedList Byte.byte) Byte.byte option (A -> A)) n) P :
  parser_sound p P ->
  (forall k (lt : k < n), parser_sound (call op lt) (identity_encoding Custom)) ->
  parser_sound (Combinators.iteratel p op)
    (fun bs a => exists prefix suffix,
      bs = prefix ++ suffix /\ P prefix a /\ custom_repetitions Custom suffix).
Proof.
  intros H Op m bound input s Run.
  unfold Combinators.iteratel in Run; simpl in Run.
  destruct (runParser p bound input) as [sa|] eqn:Ra; [|discriminate].
  simpl in Run.
  destruct (H _ _ _ _ Ra) as [prefix [Bytes Parsed]].
  assert (TailOp : forall k (lt : k < m),
    parser_sound
      (call (Induction.le_lower bound op) lt) (identity_encoding Custom)).
  { intros k lt; simpl; apply Op. }
  destruct (production_after_chain_sound m sa
    (Induction.le_lower bound op) TailOp s Run)
    as [suffix [Rest [Repetitions Value]]].
  exists (prefix ++ suffix); split.
  - rewrite Bytes. change (prefix ++ input_bytes (Success.leftovers sa) =
      (prefix ++ suffix) ++ output_bytes s).
    rewrite Rest; apply app_assoc.
  - exists prefix, suffix. split; [reflexivity |].
    split; [now rewrite Value |exact Repetitions].
Qed.

End After.

Theorem parse_with_customsec_star_after_sound {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_sound p P ->
  parser_sound (parse_with_customsec_star_after p)
    (fun bs a => exists prefix suffix,
      bs = prefix ++ suffix /\ P prefix a /\ custom_repetitions custom_bytes suffix).
Proof.
  intro H. unfold parse_with_customsec_star_after.
  apply parser_sound_iteratel_identity; [exact H |].
  intros k lt; simpl. apply parser_sound_le_lower.
  apply parse_customsec_forget_sound.
Qed.
