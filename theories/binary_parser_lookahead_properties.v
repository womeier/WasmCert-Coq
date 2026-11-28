(** Actual Parseque lookahead/ordered-choice completeness.  Failure is
    derived from the original input's first byte, independently of any
    continuation, including recursive parsers with a size bound. *)
From Stdlib Require Import List Arith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties
  binary_parser_combinator_properties.

Definition parser_initial_byte {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) b : Prop :=
  forall m (bound : m <= n) input s,
    runParser p bound input = Some s ->
    exists tail, input_bytes input = b :: tail.

Lemma exact_byte_initial n b :
  parser_initial_byte
    (exact_byte (Toks := SizedList Byte.byte) (M := option) (n := n) b) b.
Proof.
  intros m bound input s Run.
  destruct (parser_sound_exact_byte b n _ _ _ _ Run)
    as [prefix [Bytes [Prefix _]]].
  subst prefix. exists (output_bytes s); exact Bytes.
Qed.

Lemma parser_initial_map {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) (f : A -> B) b :
  parser_initial_byte p b ->
  parser_initial_byte (Combinators.map f p) b.
Proof.
  intros H m bound input s Run.
  unfold Combinators.map in Run; simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  now apply (H _ _ _ _ Raw).
Qed.

Lemma parser_initial_cmap {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) (value : B) b :
  parser_initial_byte p b ->
  parser_initial_byte (Combinators.cmap value p) b.
Proof. unfold Combinators.cmap. apply parser_initial_map. Qed.

Lemma parser_initial_rand {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : Box (Parser (SizedList Byte.byte) Byte.byte option B) n) b :
  parser_initial_byte p b ->
  parser_initial_byte (Combinators.rand p q) b.
Proof.
  intros H m bound input s Run.
  unfold Combinators.rand, Combinators.and,
    Combinators.map, Combinators.andbind in Run; simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  now apply (H _ _ _ _ Raw).
Qed.

Lemma parser_initial_mismatch {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) expected actual :
  parser_initial_byte p expected -> expected <> actual ->
  forall m (bound : m <= n) input tail,
    input_bytes input = actual :: tail ->
    runParser p bound input = None.
Proof.
  intros H Different m bound input tail Bytes.
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (H _ _ _ _ Run) as [rest Other].
  rewrite Bytes in Other. inversion Other. congruence.
Qed.

Lemma parser_complete_rand_grammar {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : Box (Parser (SizedList Byte.byte) Byte.byte option B) n) P Q R :
  parser_complete p P ->
  (forall k (lt : k < n), parser_complete (call q lt) Q) ->
  (forall bytes b, R bytes b ->
    exists xs ys a, bytes = xs ++ ys /\ P xs a /\ Q ys b) ->
  parser_complete (Combinators.rand p q) R.
Proof.
  intros Hp Hq Split.
  change (parser_complete (Combinators.bind p (fun _ => q)) R).
  eapply parser_complete_bind; [exact Hp | |exact Split].
  intros a k lt; apply Hq.
Qed.

Lemma parser_complete_prefix_byte {A n} opcode
    (q : Box (Parser (SizedList Byte.byte) Byte.byte option A) n) Q R :
  (forall k (lt : k < n), parser_complete (call q lt) Q) ->
  (forall bytes a, R bytes a ->
    exists tail, bytes = opcode :: tail /\ Q tail a) ->
  parser_complete (Combinators.rand (exact_byte opcode) q) R.
Proof.
  intros Hq Split.
  eapply parser_complete_rand_grammar with
    (P := fun bytes b => bytes = opcode :: nil /\ b = opcode) (Q := Q).
  - apply parser_complete_exact_byte.
  - exact Hq.
  - intros bytes a E. destruct (Split bytes a E) as [tail [Bytes Qtail]].
    exists (opcode :: nil), tail, opcode. subst bytes; auto.
Qed.

Lemma parser_complete_alt_right_initial {A n}
    (p q : Parser (SizedList Byte.byte) Byte.byte option A n)
    expected actual Q :
  parser_initial_byte p expected -> expected <> actual ->
  (forall bytes a, Q bytes a -> exists tail, bytes = actual :: tail) ->
  parser_complete q Q ->
  parser_complete (Combinators.alt p q) Q.
Proof.
  intros H Different Head Complete m bound input prefix suffix a Bytes Qa.
  destruct (Head _ _ Qa) as [tail Prefix].
  assert (runParser p bound input = None) as Absent.
  { apply (parser_initial_mismatch p expected actual H Different
      m bound input (tail ++ suffix)).
    rewrite Bytes, Prefix; reflexivity. }
  destruct (Complete m bound input prefix suffix a Bytes Qa) as [s [Run Facts]].
  exists s. split; [rewrite run_alt_option, Absent; exact Run |exact Facts].
Qed.
