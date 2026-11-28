(** Production custom-section wrapper completeness for canonical printer
    sections.  No custom section is emitted by the module printer; existing
    arbitrary-custom soundness remains a separate, stronger input contract. *)
From Stdlib Require Import List Strings.Byte Arith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_custom_properties
  binary_format_parser_properties.

Section NoCustom.
Context {A : Type}.
Variable P : list Byte.byte -> A -> Prop.
Hypothesis Head : forall bytes value, P bytes value ->
  exists first rest, bytes = first :: rest /\ first <> x00.

Lemma custom_before_step_complete_without_custom n rec op val :
  parser_initial_byte op x00 ->
  parser_complete val P ->
  parser_complete (custom_before_step n rec op val) P.
Proof.
  intros Initial Complete m bound input prefix suffix value Bytes Encoding.
  destruct (Head _ _ Encoding) as [first [rest [Parts NotCustom]]].
  assert (Absent : runParser op bound input = None).
  { apply (parser_initial_mismatch op x00 first Initial) with (tail := rest ++ suffix).
    - congruence.
    - now rewrite Bytes, Parts. }
  destruct (Complete m bound input prefix suffix value Bytes Encoding)
    as [result [Parsed Facts]].
  exists result; split; [|exact Facts].
  unfold custom_before_step; rewrite run_alt_option.
  unfold Combinators.iterater_aux; simpl; now rewrite Absent.
Qed.

Theorem custom_before_complete_without_custom n
    (op : Parser (SizedList Byte.byte) Byte.byte option (A -> A) n)
    (val : Parser (SizedList Byte.byte) Byte.byte option A n) :
  parser_initial_byte op x00 -> parser_complete val P ->
  parser_complete (Combinators.iterater op val) P.
Proof.
  change (parser_initial_byte op x00 -> parser_complete val P ->
    parser_complete ((Fix (right_chain (A := A)) custom_before_step n) op val) P).
  apply (fix_invariant custom_before_step
    (fun k chain => forall op val,
      parser_initial_byte op x00 -> parser_complete val P ->
      parser_complete (chain op val) P)).
  intros k rec Rec op' val' Initial Complete.
  now apply custom_before_step_complete_without_custom.
Qed.
End NoCustom.

Theorem parse_with_customsec_star_before_complete_without_custom {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall bytes value, P bytes value ->
    exists first rest, bytes = first :: rest /\ first <> x00) ->
  parser_complete p P ->
  parser_complete (parse_with_customsec_star_before p) P.
Proof.
  intros Head Complete; unfold parse_with_customsec_star_before.
  apply custom_before_complete_without_custom; [exact Head | |exact Complete].
  unfold parse_customsec_forget, parse_customsec.
  apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
Qed.

Lemma parser_initial_empty_failure {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) first :
  parser_initial_byte p first ->
  forall m (bound : m <= n) input, input_bytes input = nil ->
    runParser p bound input = None.
Proof.
  intros Initial m bound input Empty.
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [rest Bytes].
  rewrite Empty in Bytes; discriminate.
Qed.

Section EmptyAfter.
Context {A : Type}.

Definition after_chain_complete_empty n
    (chain : left_chain (A := A) n) :=
  forall sa op, output_bytes sa = nil ->
    (forall k (lt : k < n), parser_initial_byte (call op lt) x00) ->
    chain sa op = Some sa.

Lemma custom_after_step_complete_empty n rec :
  after_chain_complete_empty n (custom_after_step n rec).
Proof.
  intros sa op Empty Initial.
  assert (Absent : runParser (call op (Success.small sa))
    (Nat.le_refl _) (Success.leftovers sa) = None).
  { apply (parser_initial_empty_failure _ x00 (Initial _ _)).
    exact Empty. }
  unfold custom_after_step, Combinators.schainl_aux.
  simpl.
  destruct (runParser (call op (Success.small sa))
    (Nat.le_refl _) (Success.leftovers sa)) eqn:Run.
  - rewrite Absent in Run; discriminate.
  - reflexivity.
Qed.

Theorem production_after_chain_complete_empty n :
  after_chain_complete_empty n
    (Combinators.schainl (Toks := SizedList Byte.byte) (Tok := Byte.byte)
      (M := option) (A := A) (n := n)).
Proof.
  change (after_chain_complete_empty n
    (Fix (left_chain (A := A)) custom_after_step n)).
  apply (fix_invariant custom_after_step after_chain_complete_empty).
  intros k rec Rec; apply custom_after_step_complete_empty.
Qed.
End EmptyAfter.

Theorem parse_with_customsec_star_after_empty_suffix {A n m}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (bound : m <= n) input result :
  runParser p bound input = Some result ->
  output_bytes result = nil ->
  runParser (parse_with_customsec_star_after p) bound input = Some result.
Proof.
  intros Parsed Empty.
  unfold parse_with_customsec_star_after, Combinators.iteratel; simpl.
  rewrite Parsed.
  apply production_after_chain_complete_empty; [exact Empty |].
  intros k lt.
  assert (Initial : forall j, parser_initial_byte
    (parse_customsec_forget (Toks := SizedList Byte.byte) (M := option)
      (A := A) (n := j)) x00).
  { intro j; unfold parse_customsec_forget, parse_customsec.
    apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial. }
  intros m0 bound0 input0 s Run.
  eapply (Initial n); exact Run.
Qed.
