(** Completeness for arbitrary custom-section encodings, including padded
    size/name headers and empty payloads. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_custom_properties binary_format_custom_complete
  binary_format_vector_properties binary_format_numeric_complete
  binary_format_atomic_properties binary_format_language_properties
  leb128_properties.
Local Notation byte := Byte.byte.

Lemma run_andmbind_option {A B n m}
    (p : Parser (SizedList byte) byte option A n)
    (q : A -> Box (Parser (SizedList byte) byte option B) n)
    (bound : m <= n) input :
  runParser (Combinators.andmbind p q) bound input =
  match runParser p bound input with
  | None => None
  | Some sa =>
    match runParser (call (q (Success.value sa))
      (Nat.le_trans _ _ _ (Success.small sa) bound))
      (Nat.le_refl _) (Success.leftovers sa) with
    | Some sb => Some (Success.map (fun pair => (fst pair, Some (snd pair)))
        (Success.and sa sb))
    | None => Some (Success.map (fun a => (a, None)) sa)
    end
  end.
Proof.
  unfold Combinators.andmbind; simpl.
  destruct (runParser p bound input); [|reflexivity].
  simpl; destruct (runParser _ _ _); reflexivity.
Qed.

Section BeforeGeneral.
Context {A : Type}.
Variable Custom : list byte -> Prop.
Variable Payload : list byte -> A -> Prop.
Hypothesis Head : forall bytes value, Payload bytes value ->
  exists first rest, bytes = first :: rest /\ first <> x00.

Definition before_complete_property n (chain : right_chain (A := A) n) :=
  forall op val,
    parser_initial_byte op x00 ->
    parser_complete op (fun bytes f => Custom bytes /\ f = (fun a => a)) ->
    parser_complete val Payload ->
    parser_complete (chain op val) (custom_before_encoding Custom Payload).

Lemma custom_before_step_general_complete n rec :
  (forall k (lt : k < n), before_complete_property k (call rec lt)) ->
  before_complete_property n (custom_before_step n rec).
Proof.
  intros Rec op val Initial Op Val m bound input prefix suffix a Bytes Encoding.
  destruct Encoding as [body a Body|xs ys a CustomBytes Tail].
  - eapply (custom_before_step_complete_without_custom Payload Head n rec op val
      Initial Val m bound input body suffix a Bytes Body).
  - rewrite <- app_assoc in Bytes.
    destruct (Op m bound input xs (ys ++ suffix) (fun a => a) Bytes
      (conj CustomBytes Logic.eq_refl)) as [sop [Run [Value Rest]]].
    unfold custom_before_step; rewrite run_alt_option.
    assert (TailComplete : parser_complete
      (call rec (Nat.le_trans _ _ _ (Success.small sop) bound)
        (Combinators.lt_lower (Nat.le_trans _ _ _ (Success.small sop) bound) op)
        (Combinators.lt_lower (Nat.le_trans _ _ _ (Success.small sop) bound) val))
      (custom_before_encoding Custom Payload)).
    { apply Rec.
      - unfold Combinators.lt_lower.
        intros j lower tokens s Parsed; eapply Initial; exact Parsed.
      - unfold Combinators.lt_lower; now apply parser_complete_le_lower.
      - unfold Combinators.lt_lower; now apply parser_complete_le_lower. }
    destruct (TailComplete _ (Nat.le_refl _) (Success.leftovers sop) ys suffix a Rest Tail)
      as [s [TailRun [TailValue TailRest]]].
    unfold Combinators.iterater_aux; cbn.
    rewrite Run; cbn.
    cbn in TailRun.
    match goal with
    | |- context [runParser ?p ?b ?t] =>
      let R := fresh "RecursiveRun" in
      assert (R : runParser p b t = Some s) by exact TailRun;
      rewrite R
    end.
    eexists; split; [reflexivity |].
    split; [cbn; now rewrite Value, TailValue |exact TailRest].
Qed.

Theorem iterater_general_complete n op val :
  parser_initial_byte op x00 ->
  parser_complete op (fun bytes f => Custom bytes /\ f = (fun a => a)) ->
  parser_complete val Payload ->
  parser_complete
    (Combinators.iterater (Toks := SizedList byte) (M := option) (A := A) (n := n) op val)
    (custom_before_encoding Custom Payload).
Proof.
  assert (Invariant : before_complete_property n
    (Fix (right_chain (A := A)) custom_before_step n)).
  { apply (fix_invariant custom_before_step before_complete_property).
    exact custom_before_step_general_complete. }
  exact (Invariant op val).
Qed.
End BeforeGeneral.

Theorem parse_name_general_complete n :
  parser_complete (parse_name (Toks := SizedList byte) (M := option) (n := n))
    name_encoding.
Proof.
  unfold parse_name; eapply parser_complete_guardM with
    (P := vector_encoding (fun bytes b => bytes = b :: nil)).
  - apply parse_vec_complete; apply parser_complete_anyTok.
  - intros bytes name [Valid [header [Bytes [Encoding [Bound Width]]]]].
    exists name; split.
    + exists header, name; split; [exact Bytes |].
      split; [exact Encoding |].
      split; [exact Bound |].
      split; [exact Width |].
      clear Bytes Encoding Bound Width Valid header.
      induction name as [|b rest IH]; [constructor |].
      change (encoded_items (fun bytes b => bytes = b :: nil)
        ((b :: nil) ++ rest) (b :: rest)).
      constructor; [reflexivity |exact IH].
    + now rewrite Valid.
Qed.

Lemma parser_complete_sized_parser {A n}
    (p : Parser (SizedList byte) byte option A n) P :
  parser_complete p P ->
  parser_complete (sized_parser p)
    (fun bytes pair => P bytes (fst pair) /\ snd pair = N.of_nat (length bytes)).
Proof.
  intros Complete m bound input prefix suffix [a size] Bytes [Encoding Size].
  destruct (Complete m bound input prefix suffix a Bytes Encoding)
    as [s [Run [Value Rest]]].
  rewrite run_sized_parser_option, Run.
  eexists; split; [reflexivity |].
  split; [|exact Rest].
  cbn; rewrite Value; f_equal.
  pose proof (@Sized.sized _ _ _ input) as InSize.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as OutSize.
  change (length (input_bytes input) = m) in InSize.
  change (length (output_bytes s) = Success.size s) in OutSize.
  rewrite Bytes, length_app in InSize; rewrite Rest in OutSize.
  cbn in Size; subst size; f_equal; lia.
Qed.

Lemma custom_contents_complete n name_bytes name payload size :
  name_encoding name_bytes name ->
  size = N.of_nat (length name_bytes + length payload) ->
  parser_complete
    (Combinators.andmbind (sized_parser (parse_name (Toks := SizedList byte)
      (M := option) (n := n)))
      (fun '(_, name_size) => box (parse_vec_aux anyTok (size - name_size)%N)))
    (fun bytes value =>
      bytes = name_bytes ++ payload /\
      value = ((name, N.of_nat (length name_bytes)),
        match payload with nil => None | _ => Some payload end)).
Proof.
  intros Name Size m bound input prefix suffix value Bytes [Prefix Value].
  subst prefix value; rewrite <- app_assoc in Bytes.
  destruct (@parser_complete_sized_parser datatypes.name n
    (parse_name (Toks := SizedList byte) (M := option) (n := n))
    name_encoding (parse_name_general_complete n)
    m bound input name_bytes (payload ++ suffix)
    (name, N.of_nat (length name_bytes)) Bytes (conj Name Logic.eq_refl))
    as [sa [Run [Value Rest]]].
  rewrite run_andmbind_option.
  rewrite Run; cbn -[parse_vec_aux]; rewrite Value; cbn [snd].
  assert (Remaining : (size - N.of_nat (length name_bytes))%N =
    N.of_nat (length payload)).
  { rewrite Size, Nat2N.inj_add; lia. }
  rewrite Remaining.
  destruct payload as [|b tail].
  - cbn [parse_vec_aux].
    eexists; split; [reflexivity |].
    split; [cbn; now rewrite Value |exact Rest].
  - assert (TailComplete : parser_complete
      (call (box (parse_vec_aux (@anyTok (SizedList byte) byte _ option _ _ _ n)
        (N.of_nat (length (b :: tail)))))
        (Nat.le_trans _ _ _ (Success.small sa) bound))
      (fun bytes values => bytes = values /\
        N.of_nat (length bytes) = N.of_nat (length (b :: tail)))).
    { simpl; apply parser_complete_le_lower; apply parse_raw_bytes_complete.
      simpl; lia. }
    destruct (TailComplete _ (Nat.le_refl _) (Success.leftovers sa) (b :: tail)
      suffix (b :: tail) Rest (conj Logic.eq_refl Logic.eq_refl))
      as [sb [TailRun [TailValue TailRest]]].
    cbn in TailRun.
    cbn.
    rewrite TailRun.
    eexists; split; [reflexivity |].
    split; [cbn; now rewrite Value, TailValue |exact TailRest].
Qed.

Theorem parse_customsec_general_complete n :
  parser_complete (parse_customsec (Toks := SizedList byte) (M := option) (n := n))
    custom_section_encoding.
Proof.
  unfold parse_customsec.
  apply parser_complete_prefix_byte with (Q := custom_payload_encoding).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_guardM with
      (P := fun bytes pair =>
        exists header name_bytes name payload,
          bytes = header ++ name_bytes ++ payload /\
          index_encoding header (N.of_nat (length name_bytes + length payload)) /\
          name_encoding name_bytes name /\
          pair = (N.of_nat (length name_bytes + length payload),
            ((name, N.of_nat (length name_bytes)),
              match payload with nil => None | _ => Some payload end))).
    + eapply parser_complete_andbind with
        (P := index_encoding)
        (Q := fun size bytes value =>
          exists name_bytes name payload,
            bytes = name_bytes ++ payload /\ name_encoding name_bytes name /\
            size = N.of_nat (length name_bytes + length payload) /\
            value = ((name, N.of_nat (length name_bytes)),
              match payload with nil => None | _ => Some payload end)).
      * apply parse_u32_prefix_complete.
      * intros size j lower; simpl; apply parser_complete_le_lower.
        intros m bound input prefix suffix value Bytes
          [name_bytes [name [payload [Prefix [Name [Size Value]]]]]].
        exact (custom_contents_complete n name_bytes name payload size Name Size
          m bound input prefix suffix value Bytes (conj Prefix Value)).
      * intros bytes size contents
          [header [name_bytes [name [payload [Bytes [Header [Name Pair]]]]]]].
        injection Pair as Size Contents; subst size contents.
        exists header, (name_bytes ++ payload); split; [exact Bytes |].
        split; [exact Header |].
        exists name_bytes, name, payload; split; [reflexivity |].
        split; [exact Name |split; reflexivity].
    + intros bytes [name payload]
        [header [name_bytes [Bytes [Header Name]]]].
      exists (N.of_nat (length name_bytes + length payload),
        ((name, N.of_nat (length name_bytes)),
          match payload with nil => None | _ => Some payload end)).
      split.
      * exists header, name_bytes, name, payload.
        split; [exact Bytes |split; [exact Header |split; [exact Name |reflexivity]]].
      * cbn [fst snd].
        rewrite Nat2N.inj_add.
        assert (Order : N.ltb
          (N.of_nat (length name_bytes) + N.of_nat (length payload))
          (N.of_nat (length name_bytes)) = false) by (apply N.ltb_ge; lia).
        rewrite Order; destruct payload; [rewrite N.add_0_r, N.eqb_refl |]; reflexivity.
  - intros bytes value [body [Bytes Encoding]].
    exists body; auto.
Qed.

Lemma parse_customsec_forget_general_complete {A} n :
  parser_complete
    (parse_customsec_forget (Toks := SizedList byte) (M := option) (A := A) (n := n))
    (fun bytes f => custom_bytes bytes /\ f = (fun a => a)).
Proof.
  unfold parse_customsec_forget.
  eapply parser_complete_map; [apply parse_customsec_general_complete |].
  intros bytes f [[result Encoding] Value].
  exists result; auto.
Qed.

Theorem parse_with_customsec_star_before_general_complete {A n}
    (p : Parser (SizedList byte) byte option A n) P :
  (forall bytes value, P bytes value ->
    exists first rest, bytes = first :: rest /\ first <> x00) ->
  parser_complete p P ->
  parser_complete (parse_with_customsec_star_before p)
    (custom_before_encoding custom_bytes P).
Proof.
  intros Head Complete; unfold parse_with_customsec_star_before.
  apply iterater_general_complete; [exact Head | | |exact Complete].
  - unfold parse_customsec_forget, parse_customsec.
    apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
  - apply parse_customsec_forget_general_complete.
Qed.

Section AfterGeneral.
Context {A : Type}.
Variable Custom : list byte -> Prop.

Definition after_complete_property n (chain : left_chain (A := A) n) :=
  forall sa op,
    (forall k (lt : k < n), parser_initial_byte (call op lt) x00) ->
    (forall k (lt : k < n),
      parser_complete (call op lt) (fun bytes f => Custom bytes /\ f = (fun a => a))) ->
    custom_repetitions Custom (output_bytes sa) ->
    exists result, chain sa op = Some result /\
      Success.value result = Success.value sa /\ output_bytes result = nil.

Lemma custom_after_step_general_complete n rec :
  (forall k (lt : k < n), after_complete_property k (call rec lt)) ->
  after_complete_property n (custom_after_step n rec).
Proof.
  intros Rec sa op Initial Complete Encoding.
  remember (output_bytes sa) as bytes eqn:Bytes.
  destruct Encoding as [|xs ys CustomBytes Tail].
  - assert (Absent : runParser (call op (Success.small sa))
      (Nat.le_refl _) (Success.leftovers sa) = None).
    { apply (parser_initial_empty_failure _ x00 (Initial _ _)).
      symmetry; exact Bytes. }
    exists sa; split.
    + unfold custom_after_step, Combinators.schainl_aux; cbn.
      cbn in Absent.
      match goal with
      | |- context [runParser ?p ?b ?t] =>
        let R := fresh "AbsentRun" in
        assert (R : runParser p b t = None) by exact Absent;
        rewrite R
      end; reflexivity.
    + split; [reflexivity |symmetry; exact Bytes].
  - destruct (Complete _ (Success.small sa) _ (Nat.le_refl _)
      (Success.leftovers sa) xs ys (fun a => a)
      (eq_sym Bytes) (conj CustomBytes Logic.eq_refl))
      as [sop [Run [Value Rest]]].
    assert (TailEncoding : custom_repetitions Custom
      (output_bytes (Success.map (fun f => f (Success.value sa)) sop))).
    { change (custom_repetitions Custom (output_bytes sop)).
      now rewrite Rest. }
    destruct (Rec _ (Success.small sa)
      (Success.map (fun f => f (Success.value sa)) sop)
      (Induction.lt_lower (Success.small sa) op))
      as [result [TailRun [TailValue TailRest]]].
    + intros k lt; simpl; apply Initial.
    + intros k lt; simpl; apply Complete.
    + exact TailEncoding.
    + exists (Success.lt_lift (Success.small sa) result); split.
      * unfold custom_after_step, Combinators.schainl_aux; cbn.
        cbn in Run.
        match goal with
        | |- context [runParser ?p ?b ?t] =>
          let R := fresh "OperatorRun" in
          assert (R : runParser p b t = Some sop) by exact Run;
          rewrite R
        end; cbn.
        change (option_rect
          (fun _ : option (Success.Success (SizedList byte) byte A n) =>
            (unit -> option (Success.Success (SizedList byte) byte A n)) ->
            option (Success.Success (SizedList byte) byte A n))
          (fun x _ => Some x) (fun x => x tt)
          (option_rect (fun _ => option (Success.Success (SizedList byte) byte A n))
            (fun r => Some (Success.lt_lift (Success.small sa) r)) None
            (call rec (Success.small sa)
              (Success.map (fun f => f (Success.value sa)) sop)
              (Induction.lt_lower (Success.small sa) op)))
          (fun _ => Some sa) = Some (Success.lt_lift (Success.small sa) result)).
        now rewrite TailRun.
      * split; [change (Success.value result = Success.value sa) |exact TailRest].
        rewrite TailValue; cbn; now rewrite Value.
Qed.

Theorem production_after_chain_general_complete n :
  after_complete_property n
    (Combinators.schainl (Toks := SizedList byte) (M := option) (A := A) (n := n)).
Proof.
  change (after_complete_property n (Fix (left_chain (A := A)) custom_after_step n)).
  apply (fix_invariant custom_after_step after_complete_property).
  exact custom_after_step_general_complete.
Qed.
End AfterGeneral.

Theorem parse_with_customsec_star_after_general_complete_eof {A n m}
    (p : Parser (SizedList byte) byte option A n) P
    (bound : m <= n) input prefix customs a :
  parser_complete p P ->
  input_bytes input = prefix ++ customs ->
  P prefix a ->
  custom_repetitions custom_bytes customs ->
  exists result,
    runParser (parse_with_customsec_star_after p) bound input = Some result /\
    Success.value result = a /\ output_bytes result = nil.
Proof.
  intros Complete Bytes Encoding Customs.
  destruct (Complete m bound input prefix customs a Bytes Encoding)
    as [sa [Run [Value Rest]]].
  assert (Tail : custom_repetitions custom_bytes (output_bytes sa)) by now rewrite Rest.
  destruct (production_after_chain_general_complete custom_bytes m sa
    (Induction.le_lower bound (box parse_customsec_forget)))
    as [result [TailRun [TailValue TailRest]]].
  - intros k lt.
    assert (Initial : parser_initial_byte
      (parse_customsec_forget (Toks := SizedList byte) (M := option) (A := A) (n := n)) x00).
    { unfold parse_customsec_forget, parse_customsec.
      apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial. }
    intros j lower tokens s Parsed; eapply Initial; exact Parsed.
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_customsec_forget_general_complete.
  - exact Tail.
  - exists result; split; [|split; [congruence |exact TailRest]].
    unfold parse_with_customsec_star_after, Combinators.iteratel; cbn.
    now rewrite Run.
Qed.
