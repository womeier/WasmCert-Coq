(** Completeness of the actual mutually recursive production language. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_dispatch_properties
  binary_format_atomic_properties binary_format_numeric_properties
  binary_format_type_properties binary_format_primitive_complete
  binary_memory_grammar_properties binary_format_block_properties.
Local Notation byte := Byte.byte.

Definition instruction_head bytes :=
  exists first rest, bytes = first :: rest /\ first <> x05 /\ first <> x0b.

Lemma wasm_atomic_encoding_head bytes be :
  wasm_atomic_encoding bytes be -> instruction_head bytes.
Proof.
  intros [Control|[Bulk|[Numeric|Memory]]].
  - { destruct Control.
      - unfold fixed_control_opcodes in H; cbn [In] in H.
        repeat (destruct H as [E|H]); try contradiction;
          inversion E; subst opcode be;
          eexists; exists nil; repeat split; discriminate.
      - unfold single_index_opcodes in H; cbn [In] in H.
        repeat (destruct H as [E|H]);
          try contradiction; inversion E; subst opcode make;
          eexists; exists bytes; repeat split; discriminate.
      - exists x11, (types ++ tables); repeat split; discriminate.
      - exists x13, (types ++ tables); repeat split; discriminate.
      - exists x0e, (targets ++ fallback); repeat split; discriminate.
       - eexists; eexists; repeat split; discriminate.
       - exists xfb, bs; repeat split; discriminate.
       - exists xfb, bs; repeat split; discriminate.
      - exists x1c, bytes; repeat split; discriminate. }
  - destruct Bulk; destruct H0 as [header [Parts E]]; subst prefix;
      exists xfc; eexists; repeat split; discriminate.
  - destruct Numeric as
      [opcode be Lower Opcode
      |payload v E Count
      |payload v E Count
      |payload Count
      |payload Count
      |header payload E Count
      |prefix code be E Opcode
      |body be E].
    + exists opcode, nil; split; [reflexivity |].
      split; intro Equal; subst opcode; cbn in Lower; lia.
    + exists x41, payload; repeat split; discriminate.
    + exists x42, payload; repeat split; discriminate.
    + exists x43, payload; repeat split; discriminate.
    + exists x44, payload; repeat split; discriminate.
    + exists xfd, (header ++ payload); repeat split; discriminate.
    + destruct E as [header [Parts E]]; subst prefix.
      exists xfc, header; repeat split; discriminate.
    + exists xfd, body; repeat split; discriminate.
  - destruct (memory_grammar_initial bytes be Memory)
      as [first [rest [Bytes Allowed]]].
    exists first, rest; split; [exact Bytes |].
    unfold memory_initial in Allowed.
    split; intro Equal; subst first; intuition (try discriminate; cbn in *; lia).
Qed.

Lemma instruction_head_app xs ys :
  instruction_head xs -> instruction_head (xs ++ ys).
Proof.
  intros [first [rest [Bytes Facts]]]; subst xs.
  exists first, (rest ++ ys); auto.
Qed.

Lemma after_delimiter_complete {A n}
    (p q : Parser (SizedList byte) byte option A n) tag R :
  parser_initial_byte p tag ->
  (tag = x05 \/ tag = x0b) ->
  (forall bytes value, R bytes value -> instruction_head bytes) ->
  parser_complete q R -> parser_complete (Combinators.alt p q) R.
Proof.
  intros Initial Tag Head Complete.
  eapply parser_complete_alt_right_failure; [|exact Complete].
  intros m bound input prefix suffix value Bytes Encoding.
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [rest Input].
  destruct (Head _ _ Encoding) as [first [tail [Prefix [NotElse NotEnd]]]].
  rewrite Bytes, Prefix in Input. inversion Input; subst first.
  destruct Tag; subst tag; contradiction.
Qed.

Lemma wasm_instruction_encoding_head bytes be :
  instruction_encoding wasm_atomic_encoding block_type_encoding bytes be ->
  instruction_head bytes.
Proof.
  intro E; destruct E.
  - now apply wasm_atomic_encoding_head in H.
  - exists x02, (xs ++ ys); repeat split; discriminate.
  - exists x03, (xs ++ ys); repeat split; discriminate.
  - exists x04, (xs ++ ys); repeat split; discriminate.
Qed.

Local Notation Instruction := (instruction_encoding wasm_atomic_encoding block_type_encoding).
Local Notation Expression := (expression_encoding wasm_atomic_encoding block_type_encoding).
Local Notation ElseExpression := (else_expression_encoding wasm_atomic_encoding block_type_encoding).
Local Notation IfBody := (if_body_encoding wasm_atomic_encoding block_type_encoding).

Definition language_complete n
    (lang : Language (Toks := SizedList byte) (M := option) n) :=
  parser_complete (_be n lang) Instruction /\
  parser_complete (_bes_end_with_x0b n lang) Expression /\
  parser_complete (_bes_end_with_x05 n lang) ElseExpression /\
  parser_complete (_bes_end_with_x0b_or_x05_ctd n lang) IfBody.

Lemma structured_prefix_complete {A} n tag
    (make : block_type -> A -> basic_instruction)
    (body : Box (Parser (SizedList byte) byte option A) n)
    (Grammar : list byte -> A -> Prop) :
  (forall k (lt : k < n), parser_complete (call body lt) Grammar) ->
  parser_complete
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) tag)
      (box (Combinators.app (Combinators.map make parse_block_type) body)))
    (fun bytes be => exists types rest bt value,
      bytes = tag :: types ++ rest /\ block_type_encoding types bt /\
      Grammar rest value /\ be = make bt value).
Proof.
  intro Body.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists types rest bt value,
      bytes = types ++ rest /\ block_type_encoding types bt /\
      Grammar rest value /\ be = make bt value).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_app with
      (P := fun bytes f => exists bt, block_type_encoding bytes bt /\ f = make bt)
      (Q := Grammar).
    + eapply parser_complete_map; [apply parse_block_type_complete |].
      intros bytes f [bt [E Value]]; exists bt; auto.
    + exact Body.
    + intros bytes be [types [rest [bt [value [Bytes [T [G Value]]]]]]].
      exists types, rest, (make bt), value.
      split; [exact Bytes |]. split; [exists bt; auto |].
      split; assumption.
  - intros bytes be [types [rest [bt [value [Bytes Facts]]]]].
    exists (types ++ rest); split; [exact Bytes |].
    exists types, rest, bt, value; auto.
Qed.

Ltac skip_structural tag :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p _) _ =>
    let AllowedSet := open_constr:(_ : byte -> Prop) in
    let Initial := fresh "Initial" in
    assert (Initial : parser_initial_set p AllowedSet) by layer_initial_set;
    eapply parser_complete_alt_right_initial_set with
      (Allowed := AllowedSet) (opcode := tag);
    [exact Initial |solve [reject_layer_initial] |
      intros bytes result [types [rest [t [value [Parts _]]]]];
      now exists (types ++ rest) |]
  end.

Lemma language_step_instruction_complete n rec :
  (forall k (lt : k < n), language_complete k (call rec lt)) ->
  parser_complete (_be n (language_step n rec)) Instruction.
Proof.
  intro Rec.
  set (ends := Induction.map _bes_end_with_x0b n rec).
  set (branches := Induction.map _bes_end_with_x0b_or_x05_ctd n rec).
  assert (Ends : forall k (lt : k < n), parser_complete (call ends lt) Expression).
  { intros k lt; exact (proj1 (proj2 (Rec k lt))). }
  assert (Branches : forall k (lt : k < n), parser_complete (call branches lt) IfBody).
  { intros k lt; exact (proj2 (proj2 (proj2 (Rec k lt)))). }
  change (parser_complete (parse_be_layer ends branches) Instruction).
  intros m bound input prefix suffix be EncodingBytes E.
  destruct E.
  - now apply (wasm_parse_be_layer_atomic_complete n ends branches
      m bound input _ suffix _ EncodingBytes).
  - assert (Complete : parser_complete (parse_be_layer ends branches)
      (fun bytes be => exists types rest bt value,
        bytes = x02 :: types ++ rest /\ block_type_encoding types bt /\
        Expression rest value /\ be = BI_block bt value)).
    { unfold parse_be_layer.
      do 2 (skip_structural x02). apply parser_complete_alt_left.
      now apply structured_prefix_complete. }
    apply (Complete m bound input _ suffix _ EncodingBytes).
    exists xs, ys, bt, es; auto.
  - assert (Complete : parser_complete (parse_be_layer ends branches)
      (fun bytes be => exists types rest bt value,
        bytes = x03 :: types ++ rest /\ block_type_encoding types bt /\
        Expression rest value /\ be = BI_loop bt value)).
    { unfold parse_be_layer.
      do 3 (skip_structural x03). apply parser_complete_alt_left.
      now apply structured_prefix_complete. }
    apply (Complete m bound input _ suffix _ EncodingBytes).
    exists xs, ys, bt, es; auto.
  - assert (Complete : parser_complete (parse_be_layer ends branches)
      (fun bytes be => exists types rest bt value,
        bytes = x04 :: types ++ rest /\ block_type_encoding types bt /\
        IfBody rest value /\ be = BI_if bt (fst value) (snd value))).
    { unfold parse_be_layer.
      do 4 (skip_structural x04). apply parser_complete_alt_left.
      eapply parser_complete_map with
        (P := fun bytes pair => exists types rest t value,
          bytes = x04 :: types ++ rest /\ block_type_encoding types t /\
          IfBody rest value /\ pair = (t, value)).
      - apply parser_complete_prefix_byte with
          (Q := fun bytes pair => exists types rest bt value,
            bytes = types ++ rest /\ block_type_encoding types bt /\
            IfBody rest value /\ pair = (bt, value)).
        + intros k lt; simpl. apply parser_complete_le_lower.
          eapply parser_complete_app with
            (P := fun bytes f => exists bt, block_type_encoding bytes bt /\
              f = (fun body => (bt, body))) (Q := IfBody).
          * eapply parser_complete_map; [apply parse_block_type_complete |].
            intros bytes f [t [T Value]]; exists t; auto.
          * exact Branches.
          * intros bytes pair [types [rest [t [value [Bytes [T [G Value]]]]]]].
            exists types, rest, (fun body => (t, body)), value.
            split; [exact Bytes |]. split; [exists t; auto |].
            split; assumption.
        + intros bytes pair [types [rest [t [value [Bytes Facts]]]]].
          exists (types ++ rest); split; [exact Bytes |].
          exists types, rest, t, value; auto.
      - intros bytes be [types [rest [t [[ls rs] [Bytes [T [G Value]]]]]]].
        exists (t, (ls, rs)); split; [|exact Value].
        exists types, rest, t, (ls, rs); auto. }
    apply (Complete m bound input _ suffix _ EncodingBytes).
    exists xs, ys, bt, (left, right); auto.
Qed.

Definition instruction_sequence_encoding
    (Tail : list byte -> list basic_instruction -> Prop) bytes values :=
  exists first rest be es, bytes = first ++ rest /\
    Instruction first be /\ Tail rest es /\ values = be :: es.

Lemma instruction_sequence_complete n p body Tail :
  @parser_complete basic_instruction n p Instruction ->
  (forall k (lt : k < n), parser_complete (call body lt) Tail) ->
  parser_complete
    (Combinators.app (Combinators.map (@cons basic_instruction) p) body)
    (instruction_sequence_encoding Tail).
Proof.
  intros Be Body.
  eapply parser_complete_app with
    (P := fun bytes f => exists be, Instruction bytes be /\ f = cons be)
    (Q := Tail).
  - eapply parser_complete_map; [exact Be |].
    intros bytes f [be [E Value]]; exists be; auto.
  - exact Body.
  - intros bytes values [first [rest [be [es [Bytes [E [T Value]]]]]]].
    exists first, rest, (cons be), es.
    split; [exact Bytes |]. split; [exists be; auto |].
    split; assumption.
Qed.

Lemma instruction_sequence_head Tail bytes values :
  instruction_sequence_encoding Tail bytes values -> instruction_head bytes.
Proof.
  intros [first [rest [be [es [Bytes [E _]]]]]]; subst bytes.
  apply instruction_head_app. now apply (wasm_instruction_encoding_head first be).
Qed.

Lemma language_step_complete n rec :
  (forall k (lt : k < n), language_complete k (call rec lt)) ->
  language_complete n (language_step n rec).
Proof.
  intro Rec.
  pose proof (language_step_instruction_complete n rec Rec) as Be.
  assert (End : parser_complete (_bes_end_with_x0b n (language_step n rec)) Expression).
  { intros m bound input prefix suffix es Bytes Encoding.
    destruct Encoding.
    - unfold language_step; cbn [_bes_end_with_x0b].
      eapply parser_complete_alt_left.
      + apply binary_format_numeric_complete.fixed_instruction_complete.
      + exact Bytes.
      + split; reflexivity.
    - assert (Complete : parser_complete
        (_bes_end_with_x0b n (language_step n rec))
        (instruction_sequence_encoding Expression)).
      { unfold language_step; cbn [_bes_end_with_x0b].
        apply after_delimiter_complete with (tag := x0b).
        - apply parser_initial_cmap; apply exact_byte_initial.
        - now right.
        - apply instruction_sequence_head.
        - apply instruction_sequence_complete.
          + exact Be.
          + intros k lt; exact (proj1 (proj2 (Rec k lt))). }
      apply (Complete m bound input _ suffix _ Bytes).
      exists xs, ys, be, es; auto. }
  split; [exact Be |]. split; [exact End |]. split.
  - intros m bound input prefix suffix es Bytes Encoding.
    destruct Encoding.
    + unfold language_step; cbn [_bes_end_with_x05].
      eapply parser_complete_alt_left.
      * apply binary_format_numeric_complete.fixed_instruction_complete.
      * exact Bytes.
      * split; reflexivity.
    + assert (Complete : parser_complete
        (_bes_end_with_x05 n (language_step n rec))
        (instruction_sequence_encoding ElseExpression)).
      { unfold language_step; cbn [_bes_end_with_x05].
        apply after_delimiter_complete with (tag := x05).
        - apply parser_initial_cmap; apply exact_byte_initial.
        - now left.
        - apply instruction_sequence_head.
        - apply instruction_sequence_complete.
          + exact Be.
          + intros k lt; exact (proj1 (proj2 (proj2 (Rec k lt)))). }
      apply (Complete m bound input _ suffix _ Bytes).
      exists xs, ys, be, es; auto.
  - intros m bound input prefix suffix pair Bytes Encoding.
    destruct Encoding.
    + unfold language_step; cbn [_bes_end_with_x0b_or_x05_ctd].
      eapply parser_complete_alt_left.
      * apply binary_format_numeric_complete.fixed_instruction_complete.
      * exact Bytes.
      * split; reflexivity.
    + assert (Complete : parser_complete
        (_bes_end_with_x0b_or_x05_ctd n (language_step n rec))
        (fun bytes pair => exists body es,
          bytes = x05 :: body /\ Expression body es /\ pair = (nil, es))).
      { unfold language_step; cbn [_bes_end_with_x0b_or_x05_ctd].
        eapply parser_complete_alt_right_initial with (actual := x05).
        - apply parser_initial_cmap; apply exact_byte_initial.
        - discriminate.
        - intros bytes value [body [elements [Parts _]]]; now exists body.
        - apply parser_complete_alt_left.
          eapply parser_complete_app with
            (P := fun bytes f => bytes = x05 :: nil /\
              f = (fun es : list basic_instruction => (nil, es)))
            (Q := Expression).
          + apply binary_format_numeric_complete.fixed_instruction_complete.
          + intros k lt; simpl. apply parser_complete_le_lower; exact End.
          + intros bytes value [body [elements [Parts [E Value]]]].
            exists (x05 :: nil), body,
              (fun es : list basic_instruction => (nil, es)), elements.
            split; [exact Parts |]. split; [split; reflexivity |].
            split; assumption. }
      apply (Complete m bound input _ suffix _ Bytes).
      exists bs, es; auto.
    + assert (Complete : parser_complete
        (_bes_end_with_x0b_or_x05_ctd n (language_step n rec))
        (fun bytes pair => exists first rest be ls rs,
          bytes = first ++ rest /\ Instruction first be /\
          IfBody rest (ls, rs) /\ pair = (be :: ls, rs))).
      { unfold language_step; cbn [_bes_end_with_x0b_or_x05_ctd].
        apply after_delimiter_complete with (tag := x0b).
        - apply parser_initial_cmap; apply exact_byte_initial.
        - now right.
        - intros bytes value [first [rest [a [ls [rs [Parts [E _]]]]]]].
          subst bytes; apply instruction_head_app.
          now apply (wasm_instruction_encoding_head first a).
        - apply after_delimiter_complete with (tag := x05).
          + apply parser_initial_app; apply parser_initial_cmap; apply exact_byte_initial.
          + now left.
          + intros bytes value [first [rest [a [ls [rs [Parts [E _]]]]]]].
            subst bytes; apply instruction_head_app.
            now apply (wasm_instruction_encoding_head first a).
          + eapply parser_complete_app with
              (P := fun bytes f => exists be, Instruction bytes be /\
                f = (fun '(ls, rs) => (be :: ls, rs)))
              (Q := IfBody).
            * eapply parser_complete_map; [exact Be |].
              intros bytes f [a [E Value]]; exists a; auto.
            * intros k lt; exact (proj2 (proj2 (proj2 (Rec k lt)))).
            * intros bytes value [first [rest [a [ls [rs [Parts [E [T Value]]]]]]]].
              exists first, rest, (fun '(ls, rs) => (a :: ls, rs)), (ls, rs).
              split; [exact Parts |]. split; [exists a; auto |].
              split; assumption. }
      apply (Complete m bound input _ suffix _ Bytes).
      exists xs, ys, be, left, right; auto.
Qed.

Theorem wasm_production_language_complete n :
  language_complete n (language n).
Proof.
  apply (fix_invariant language_step language_complete).
  exact language_step_complete.
Qed.

Theorem wasm_production_parse_expr_complete n :
  parser_complete
    (parse_expr (Toks := SizedList byte) (M := option) (n := n)) Expression.
Proof. exact (proj1 (proj2 (wasm_production_language_complete n))). Qed.
