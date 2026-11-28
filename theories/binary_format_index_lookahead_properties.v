(** Ordered-choice disjointness for bounded u32 subopcode prefixes.
    Both operands retain arbitrary legal padding and arbitrary suffixes. *)
From Stdlib Require Import List Strings.Byte Arith NArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_atomic_properties binary_format_numeric_complete.
Local Notation byte := Byte.byte.

Lemma parser_complete_alt_associate {A n}
    (p q r : Parser (SizedList byte) byte option A n) R :
  parser_complete (Combinators.alt p (Combinators.alt q r)) R ->
  parser_complete (Combinators.alt (Combinators.alt p q) r) R.
Proof.
  intros Complete m bound input prefix suffix value Bytes Enc.
  destruct (Complete m bound input prefix suffix value Bytes Enc) as [s [Run Facts]].
  exists s; split; [|exact Facts].
  repeat rewrite run_alt_option in *.
  destruct (runParser p bound input); [exact Run |].
  destruct (runParser q bound input); exact Run.
Qed.

Lemma parser_initial_set_union {A n}
    (p q : Parser (SizedList byte) byte option A n) P Q :
  parser_initial_set p P -> parser_initial_set q Q ->
  parser_initial_set (Combinators.alt p q) (fun b => P b \/ Q b).
Proof.
  intros Left Right.
  apply parser_initial_set_alt.
  - intros m bound input s Run.
    destruct (Left _ _ _ _ Run) as [b [rest [Bytes Member]]].
    exists b, rest; auto.
  - intros m bound input s Run.
    destruct (Right _ _ _ _ Run) as [b [rest [Bytes Member]]].
    exists b, rest; auto.
Qed.

Definition parser_initial_index {A n}
    (p : Parser (SizedList byte) byte option A n) (Allowed : N -> Prop) :=
  forall m (bound : m <= n) input s,
    runParser p bound input = Some s ->
    exists header rest code, input_bytes input = header ++ rest /\
      index_encoding header code /\ Allowed code.

Lemma assert_u32_initial_index n code :
  parser_initial_index
    (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
    (fun actual => actual = code).
Proof.
  intros m bound input s Run.
  destruct (assert_u32_sound n code _ _ _ _ Run) as [header [Bytes [Enc Value]]].
  exists header, (output_bytes s), code; auto.
Qed.

Lemma parser_initial_index_cmap {A B n}
    (p : Parser (SizedList byte) byte option A n) (value : B) Allowed :
  parser_initial_index p Allowed ->
  parser_initial_index (Combinators.cmap value p) Allowed.
Proof.
  intros Initial m bound input s Run.
  unfold Combinators.cmap, Combinators.map in Run; simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  exact (Initial _ _ _ _ Raw).
Qed.

Definition parser_initial_extended {A n}
    (p : Parser (SizedList byte) byte option A n) tag code :=
  forall m (bound : m <= n) input s,
    runParser p bound input = Some s ->
    exists header rest, input_bytes input = tag :: header ++ rest /\
      index_encoding header code.

Lemma extended_assert_initial n tag code :
  parser_initial_extended
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) tag)
      (box (assert_u32 code))) tag code.
Proof.
  intros m bound input s Run.
  assert (Sound : parser_sound
    (Combinators.rand (exact_byte (n := n) tag) (box (assert_u32 code)))
    (fun bytes _ => exists header, bytes = tag :: header /\ index_encoding header code)).
  { apply parser_sound_prefix_byte with
      (Q := fun bytes x => index_encoding bytes code /\ x = code).
    - intros k lt; simpl; apply parser_sound_le_lower; apply assert_u32_sound.
    - intros bytes x [Enc _]; exists bytes; auto. }
  destruct (Sound _ _ _ _ Run) as [prefix [Bytes [header [Prefix Enc]]]].
  exists header, (output_bytes s); subst prefix; auto.
Qed.

Lemma parser_initial_extended_rand {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Box (Parser (SizedList byte) byte option B) n) tag code :
  parser_initial_extended p tag code ->
  parser_initial_extended (Combinators.rand p q) tag code.
Proof.
  intros Initial m bound input s Run.
  unfold Combinators.rand, Combinators.and, Combinators.map, Combinators.andbind in Run;
    simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  exact (Initial _ _ _ _ Raw).
Qed.

Lemma parser_initial_extended_cmap {A B n}
    (p : Parser (SizedList byte) byte option A n) (value : B) tag code :
  parser_initial_extended p tag code ->
  parser_initial_extended (Combinators.cmap value p) tag code.
Proof.
  intros Initial m bound input s Run.
  unfold Combinators.cmap, Combinators.map in Run; simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  exact (Initial _ _ _ _ Raw).
Qed.

Lemma parser_complete_alt_right_extended {A n}
    (p q : Parser (SizedList byte) byte option A n) tag previous actual Q :
  parser_initial_extended p tag previous -> previous <> actual ->
  (forall bytes value, Q bytes value ->
    exists header body, bytes = tag :: header ++ body /\ index_encoding header actual) ->
  parser_complete q Q -> parser_complete (Combinators.alt p q) Q.
Proof.
  intros Initial Different Head Complete.
  eapply parser_complete_alt_right_failure; [|exact Complete].
  intros m bound input prefix suffix value Bytes Enc.
  destruct (Head _ _ Enc) as [target [body [Prefix Target]]].
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [header [rest [Input Index]]].
  exfalso; apply Different.
  eapply index_encoding_prefix_injective; [exact Index |exact Target |].
  rewrite Bytes, Prefix in Input; inversion Input as [Equal].
  rewrite <- app_assoc in Equal; symmetry; exact Equal.
Qed.

Lemma parser_extended_mismatch {A n}
    (p : Parser (SizedList byte) byte option A n) tag previous actual :
  parser_initial_extended p tag previous -> previous <> actual ->
  forall m (bound : m <= n) input header rest,
    input_bytes input = tag :: header ++ rest ->
    index_encoding header actual -> runParser p bound input = None.
Proof.
  intros Initial Different m bound input target tail Bytes Target.
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [header [rest [Input Index]]].
  exfalso; apply Different.
  eapply index_encoding_prefix_injective; [exact Index |exact Target |].
  rewrite Bytes in Input; inversion Input as [Equal]; symmetry; exact Equal.
Qed.

Lemma parser_alt_failure {A n}
    (p q : Parser (SizedList byte) byte option A n)
    m (bound : m <= n) input :
  runParser p bound input = None -> runParser q bound input = None ->
  runParser (Combinators.alt p q) bound input = None.
Proof. intros Left Right; now rewrite run_alt_option, Left, Right. Qed.

Definition parser_initial_extended_set {A n}
    (p : Parser (SizedList byte) byte option A n) tag Allowed :=
  forall m (bound : m <= n) input s,
    runParser p bound input = Some s ->
    exists header rest code, input_bytes input = tag :: header ++ rest /\
      index_encoding header code /\ Allowed code.

Lemma parser_initial_extended_single {A n}
    (p : Parser (SizedList byte) byte option A n) tag code :
  parser_initial_extended p tag code ->
  parser_initial_extended_set p tag (fun actual => actual = code).
Proof.
  intros Initial m bound input s Run.
  destruct (Initial _ _ _ _ Run) as [header [rest [Bytes Enc]]].
  exists header, rest, code; auto.
Qed.

Lemma parser_initial_extended_union {A n}
    (p q : Parser (SizedList byte) byte option A n) tag P Q :
  parser_initial_extended_set p tag P -> parser_initial_extended_set q tag Q ->
  parser_initial_extended_set (Combinators.alt p q) tag (fun code => P code \/ Q code).
Proof.
  intros Left Right m bound input s Run.
  rewrite run_alt_option in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw.
  - inversion Run; subst s.
    destruct (Left _ _ _ _ Raw) as [header [rest [code [Bytes [Enc Member]]]]].
    exists header, rest, code; auto.
  - destruct (Right _ _ _ _ Run) as [header [rest [code [Bytes [Enc Member]]]]].
    exists header, rest, code; auto.
Qed.

Lemma parser_complete_alt_right_extended_set {A n}
    (p q : Parser (SizedList byte) byte option A n) tag Allowed actual Q :
  parser_initial_extended_set p tag Allowed -> ~ Allowed actual ->
  (forall bytes value, Q bytes value ->
    exists header body, bytes = tag :: header ++ body /\ index_encoding header actual) ->
  parser_complete q Q -> parser_complete (Combinators.alt p q) Q.
Proof.
  intros Initial Rejected Head Complete.
  eapply parser_complete_alt_right_failure; [|exact Complete].
  intros m bound input prefix suffix value Bytes Enc.
  destruct (Head _ _ Enc) as [target [body [Prefix Target]]].
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [header [rest [code [Input [Index Member]]]]].
  exfalso; apply Rejected.
  assert (Same : code = actual).
  { eapply index_encoding_prefix_injective; [exact Index |exact Target |].
    rewrite Bytes, Prefix in Input; inversion Input as [Equal].
    rewrite <- app_assoc in Equal; symmetry; exact Equal. }
  now subst code.
Qed.

Lemma parser_initial_index_rand {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Box (Parser (SizedList byte) byte option B) n) Allowed :
  parser_initial_index p Allowed ->
  parser_initial_index (Combinators.rand p q) Allowed.
Proof.
  intros Initial m bound input s Run.
  unfold Combinators.rand, Combinators.and, Combinators.map, Combinators.andbind in Run;
    simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  exact (Initial _ _ _ _ Raw).
Qed.

Lemma parser_initial_index_alt {A n}
    (p q : Parser (SizedList byte) byte option A n) P Q :
  parser_initial_index p P -> parser_initial_index q Q ->
  parser_initial_index (Combinators.alt p q) (fun code => P code \/ Q code).
Proof.
  intros InitialP InitialQ m bound input s Run.
  rewrite run_alt_option in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw.
  - inversion Run; subst s.
    destruct (InitialP _ _ _ _ Raw) as [header [rest [code [Bytes [Enc Member]]]]].
    exists header, rest, code; auto.
  - destruct (InitialQ _ _ _ _ Run) as [header [rest [code [Bytes [Enc Member]]]]].
    exists header, rest, code; auto.
Qed.

Lemma parser_complete_alt_right_index {A n}
    (p q : Parser (SizedList byte) byte option A n) Allowed actual Q :
  parser_initial_index p Allowed -> ~ Allowed actual ->
  (forall bytes value, Q bytes value ->
    exists header body, bytes = header ++ body /\ index_encoding header actual) ->
  parser_complete q Q ->
  parser_complete (Combinators.alt p q) Q.
Proof.
  intros Initial Rejected Head Complete m bound input prefix suffix value Bytes Enc.
  destruct (Head _ _ Enc) as [target [body [Prefix Target]]].
  assert (Absent : runParser p bound input = None).
  { destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
    destruct (Initial _ _ _ _ Run) as [header [rest [code [Input [Index Member]]]]].
    assert (Same : code = actual).
    { eapply index_encoding_prefix_injective; [exact Index |exact Target |].
      rewrite <- Input, Bytes, Prefix, <- app_assoc; reflexivity. }
    subst code; contradiction. }
  destruct (Complete m bound input prefix suffix value Bytes Enc) as [s [Run Facts]].
  exists s; split; [rewrite run_alt_option, Absent; exact Run |exact Facts].
Qed.
