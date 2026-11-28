(** Shared optional-section absence argument from bc7c190, independent of
    non-EH leaf grammars. In particular section 13 need not be numerically
    before the following section: only distinct wire identifiers matter. *)
From Stdlib Require Import List Strings.Byte Arith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_optional_properties binary_format_custom_properties
  binary_format_custom_general_complete.
Local Notation byte := Byte.byte.

Definition avoids_section tag bytes :=
  bytes = nil \/ exists first rest,
    bytes = first :: rest /\ first <> x00 /\ first <> tag.

Lemma avoids_section_failure {A n m}
    (p : Parser (SizedList byte) byte option A n) tag bound input suffix :
  parser_initial_set p (fun b => b = x00 \/ b = tag) ->
  avoids_section tag suffix -> input_bytes input = suffix ->
  @runParser _ _ _ A n p m bound input = None.
Proof.
  intros Initial Avoid Bytes.
  destruct (runParser p bound input) as [result|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [first [rest [Input Allowed]]].
  rewrite Bytes in Input.
  destruct Avoid as [Empty|[other [tail [Suffix [NotCustom Different]]]]].
  - rewrite Empty in Input; discriminate.
  - rewrite Suffix in Input; inversion Input; subst first.
    destruct Allowed; congruence.
Qed.

Definition custom_avoids_section tag bytes :=
  custom_before_encoding custom_bytes (fun bytes (_ : unit) => avoids_section tag bytes) bytes tt.

Section CustomAbsence.
Context {A : Type}.
Variable tag : byte.
Hypothesis NotCustom : tag <> x00.

Definition before_absent_property n (chain : right_chain (A := A) n) :=
  forall op val,
    parser_initial_byte op x00 -> parser_initial_byte val tag ->
    parser_complete op (fun bytes f => custom_bytes bytes /\ f = (fun a => a)) ->
    forall m (bound : m <= n) input,
      custom_avoids_section tag (input_bytes input) ->
      runParser (chain op val) bound input = None.

Lemma custom_before_step_absent n rec :
  (forall k (lt : k < n), before_absent_property k (call rec lt)) ->
  before_absent_property n (custom_before_step n rec).
Proof.
  intros Rec op val Op Val Complete m bound input Encoding.
  remember (input_bytes input) as bytes eqn:Bytes.
  destruct Encoding as [body unit Avoid|xs ys unit CustomBytes Tail].
  - assert (OpNone : runParser op bound input = None).
    { eapply (avoids_section_failure op tag).
      - intros j lower tokens s Parsed.
        destruct (Op _ _ _ _ Parsed) as [rest B].
        exists x00, rest; auto.
      - exact Avoid.
      - symmetry; exact Bytes. }
    assert (ValNone : runParser val bound input = None).
    { eapply (avoids_section_failure val tag).
      - intros j lower tokens s Parsed.
        destruct (Val _ _ _ _ Parsed) as [rest B].
        exists tag, rest; auto.
      - exact Avoid.
      - symmetry; exact Bytes. }
    unfold custom_before_step; rewrite run_alt_option.
    unfold Combinators.iterater_aux; cbn; now rewrite OpNone, ValNone.
  - destruct (Complete m bound input xs ys (fun a => a) (eq_sym Bytes)
      (conj CustomBytes Logic.eq_refl)) as [sop [Run [Value Rest]]].
    assert (ValNone : runParser val bound input = None).
    { destruct CustomBytes as [result [payload [CustomHead Grammar]]].
      eapply (parser_initial_mismatch val tag x00 Val); [congruence |].
      rewrite <- Bytes, CustomHead; reflexivity. }
    assert (TailNone : runParser
      (call rec (Nat.le_trans _ _ _ (Success.small sop) bound)
        (Combinators.lt_lower (Nat.le_trans _ _ _ (Success.small sop) bound) op)
        (Combinators.lt_lower (Nat.le_trans _ _ _ (Success.small sop) bound) val))
      (Nat.le_refl _) (Success.leftovers sop) = None).
    { apply Rec.
      - intros j lower tokens s Parsed; eapply Op; exact Parsed.
      - intros j lower tokens s Parsed; eapply Val; exact Parsed.
      - unfold Combinators.lt_lower; now apply parser_complete_le_lower.
      - change (custom_avoids_section tag (output_bytes sop)).
        rewrite Rest; destruct unit; exact Tail. }
    unfold custom_before_step; rewrite run_alt_option.
    unfold Combinators.iterater_aux; cbn; rewrite Run; cbn.
    match goal with
    | |- context [runParser ?p ?b ?t] =>
      let R := fresh "RecursiveNone" in
      assert (R : runParser p b t = None) by exact TailNone;
      rewrite R
    end; cbn; exact ValNone.
Qed.

Theorem iterater_custom_absent n :
  before_absent_property n
    (Combinators.iterater (Toks := SizedList byte) (M := option) (A := A) (n := n)).
Proof.
  change (before_absent_property n (Fix (right_chain (A := A)) custom_before_step n)).
  apply (fix_invariant custom_before_step before_absent_property).
  exact custom_before_step_absent.
Qed.
End CustomAbsence.

Theorem custom_prefixed_section_absent {A n m}
    (p : Parser (SizedList byte) byte option A n) tag bound input :
  tag <> x00 -> parser_initial_byte p tag ->
  custom_avoids_section tag (input_bytes input) ->
  @runParser _ _ _ A n (parse_with_customsec_star_before p) m bound input = None.
Proof.
  intros NotCustom Initial Encoding; unfold parse_with_customsec_star_before.
  apply (iterater_custom_absent tag NotCustom n).
  - unfold parse_customsec_forget, parse_customsec.
    apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
  - exact Initial.
  - apply parse_customsec_forget_general_complete.
  - exact Encoding.
Qed.

Lemma custom_avoids_trailing tag customs :
  custom_repetitions custom_bytes customs -> custom_avoids_section tag customs.
Proof.
  intro Customs; induction Customs.
  - apply custom_before_payload; now left.
  - now apply custom_before_section.
Qed.
