(** Recursive byte grammar for the production [Fix Language] parser.
    Atomic instruction and block-type encodings are explicit parameters:
    none of these grammar rules mentions a parser run.  Contextual initializer
    validity (including preceding globals) is a separate validation judgment. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties.

Local Notation byte := Byte.byte.

Lemma parser_sound_cmap {A B n}
    (p : Parser (SizedList byte) byte option A n) (b : B) P Q :
  parser_sound p P ->
  (forall bs a, P bs a -> Q bs b) ->
  parser_sound (Combinators.cmap b p) Q.
Proof. unfold Combinators.cmap. apply parser_sound_map. Qed.

Lemma parser_sound_prefix_byte {A n} b
    (q : Box (Parser (SizedList byte) byte option A) n) Q R :
  (forall k (lt : k < n), parser_sound (call q lt) Q) ->
  (forall bs a, Q bs a -> R (b :: bs) a) ->
  parser_sound (Combinators.rand (exact_byte b) q) R.
Proof.
  intros Hq Combine. unfold Combinators.rand, Combinators.and.
  eapply parser_sound_map with (P := fun bs pair => R bs (snd pair)).
  - eapply parser_sound_andbind with
      (P := fun bs a => bs = b :: nil /\ a = b) (Q := fun _ => Q).
    + apply parser_sound_exact_byte.
    + intros a k lt. apply Hq.
    + intros xs ys a value [Bytes _] Parsed. subst xs; simpl.
      apply Combine; exact Parsed.
  - auto.
Qed.

Section Grammar.
Variable Atom : list byte -> basic_instruction -> Prop.
Variable BlockType : list byte -> block_type -> Prop.

Inductive instruction_encoding : list byte -> basic_instruction -> Prop :=
| instruction_atom : forall bs be,
    Atom bs be -> instruction_encoding bs be
| instruction_block : forall xs ys bt es,
    BlockType xs bt -> expression_encoding ys es ->
    instruction_encoding (x02 :: xs ++ ys) (BI_block bt es)
| instruction_loop : forall xs ys bt es,
    BlockType xs bt -> expression_encoding ys es ->
    instruction_encoding (x03 :: xs ++ ys) (BI_loop bt es)
| instruction_if : forall xs ys bt left right,
    BlockType xs bt -> if_body_encoding ys (left, right) ->
    instruction_encoding (x04 :: xs ++ ys) (BI_if bt left right)
with expression_encoding : list byte -> list basic_instruction -> Prop :=
| expression_end : expression_encoding (x0b :: nil) nil
| expression_cons : forall xs ys be es,
    instruction_encoding xs be -> expression_encoding ys es ->
    expression_encoding (xs ++ ys) (be :: es)
with else_expression_encoding : list byte -> list basic_instruction -> Prop :=
| else_expression_end : else_expression_encoding (x05 :: nil) nil
| else_expression_cons : forall xs ys be es,
    instruction_encoding xs be -> else_expression_encoding ys es ->
    else_expression_encoding (xs ++ ys) (be :: es)
with if_body_encoding :
    list byte -> (list basic_instruction * list basic_instruction) -> Prop :=
| if_body_end : if_body_encoding (x0b :: nil) (nil, nil)
| if_body_else : forall bs es,
    expression_encoding bs es ->
    if_body_encoding (x05 :: bs) (nil, es)
| if_body_cons : forall xs ys be left right,
    instruction_encoding xs be -> if_body_encoding ys (left, right) ->
    if_body_encoding (xs ++ ys) (be :: left, right).

Definition language_sound n
    (lang : Language (Toks := SizedList byte) (M := option) n) : Prop :=
  parser_sound (_be n lang) instruction_encoding /\
  parser_sound (_bes_end_with_x0b n lang) expression_encoding /\
  parser_sound (_bes_end_with_x05 n lang) else_expression_encoding /\
  parser_sound (_bes_end_with_x0b_or_x05_ctd n lang) if_body_encoding.

Definition primitive_parsers n :
    list (Parser (SizedList byte) byte option basic_instruction n) :=
  parse_tail_call :: parse_unreachable :: parse_nop :: parse_br :: parse_br_if ::
  parse_br_table :: parse_return :: parse_call :: parse_call_indirect ::
  parse_call_ref :: parse_return_call_ref ::
  parse_reference_instruction :: parse_parametric_instruction ::
  parse_variable_instruction :: parse_table_instruction ::
  parse_memory_instruction :: parse_numeric_instruction :: nil.

Hypothesis PrimitiveSound : forall n p,
  In p (primitive_parsers n) -> parser_sound p Atom.
Hypothesis BlockSound : forall n,
  parser_sound
    (parse_block_type (Toks := SizedList byte) (M := option) (n := n)) BlockType.

Lemma language_step_sound n rec :
  (forall k (lt : k < n), language_sound k (call rec lt)) ->
  language_sound n (language_step n rec).
Proof.
  intro Rec.
  assert (Be : parser_sound (_be n (language_step n rec)) instruction_encoding).
  {
    unfold language_step, parse_be_layer; cbn [_be].
    do 19 (apply parser_sound_alt; [shelve |]).
    Unshelve.
    all: try (eapply parser_sound_weaken;
      [apply PrimitiveSound; unfold primitive_parsers; simpl; tauto
      |intros bs be H; now apply instruction_atom]).
    - apply parser_sound_prefix_byte with
        (Q := fun bs be => exists xs ys bt es,
          bs = xs ++ ys /\ be = BI_block bt es /\
          BlockType xs bt /\ expression_encoding ys es).
      + intros k lt; simpl. apply parser_sound_le_lower.
        eapply parser_sound_app with
          (P := fun bs f => exists bt, BlockType bs bt /\ f = BI_block bt)
          (Q := expression_encoding).
        * eapply parser_sound_map; [apply BlockSound |].
          intros bs bt H. exists bt; auto.
        * intros j lower; simpl. exact (proj1 (proj2 (Rec j lower))).
        * intros xs ys f es [bt [B F]] E; subst f.
          exists xs, ys, bt, es. auto.
      + intros bs be [xs [ys [bt [es [Bytes [Value [B E]]]]]]].
        subst bs be. now apply instruction_block.
    - apply parser_sound_prefix_byte with
        (Q := fun bs be => exists xs ys bt es,
          bs = xs ++ ys /\ be = BI_loop bt es /\
          BlockType xs bt /\ expression_encoding ys es).
      + intros k lt; simpl. apply parser_sound_le_lower.
        eapply parser_sound_app with
          (P := fun bs f => exists bt, BlockType bs bt /\ f = BI_loop bt)
          (Q := expression_encoding).
        * eapply parser_sound_map; [apply BlockSound |].
          intros bs bt H. exists bt; auto.
        * intros j lower; simpl. exact (proj1 (proj2 (Rec j lower))).
        * intros xs ys f es [bt [B F]] E; subst f.
          exists xs, ys, bt, es. auto.
      + intros bs be [xs [ys [bt [es [Bytes [Value [B E]]]]]]].
        subst bs be. now apply instruction_loop.
    - eapply parser_sound_map with
        (P := fun bs pair => exists xs ys bt left right,
          bs = x04 :: xs ++ ys /\ pair = (bt, (left, right)) /\
          BlockType xs bt /\ if_body_encoding ys (left, right)).
      + apply parser_sound_prefix_byte with
          (Q := fun bs pair => exists xs ys bt left right,
            bs = xs ++ ys /\ pair = (bt, (left, right)) /\
            BlockType xs bt /\ if_body_encoding ys (left, right)).
        * intros k lt; simpl. apply parser_sound_le_lower.
          eapply parser_sound_app with
            (P := fun bs f => exists bt, BlockType bs bt /\
              f = (fun body => (bt, body)))
            (Q := if_body_encoding).
          -- eapply parser_sound_map; [apply BlockSound |].
             intros bs bt B. exists bt; auto.
          -- intros j lower; simpl.
             exact (proj2 (proj2 (proj2 (Rec j lower)))).
          -- intros xs ys f [left right] [bt [B F]] E; subst f.
             exists xs, ys, bt, left, right. auto.
        * intros bs pair [xs [ys [bt [left [right [Bytes Facts]]]]]].
          exists xs, ys, bt, left, right. subst bs; auto.
      + intros bs [bt [left right]]
          [xs [ys [t [l [r [Bytes [Value [B E]]]]]]]].
        inversion Value; subst. now apply instruction_if.
  }
  assert (End : parser_sound (_bes_end_with_x0b n (language_step n rec))
    expression_encoding).
  {
    unfold language_step; cbn [_bes_end_with_x0b].
    apply parser_sound_alt.
    - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; subst; constructor.
    - eapply parser_sound_app with
        (P := fun bs f => exists be,
          instruction_encoding bs be /\ f = cons be)
        (Q := expression_encoding).
      + eapply parser_sound_map; [exact Be |].
        intros bs be H. exists be; auto.
      + intros k lt; simpl. exact (proj1 (proj2 (Rec k lt))).
      + intros xs ys f es [be [B F]] E; subst f.
        now apply expression_cons.
  }
  split; [exact Be |]. split; [exact End |]. split.
  - unfold language_step; cbn [_bes_end_with_x05].
    apply parser_sound_alt.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; subst; constructor.
    + eapply parser_sound_app with
        (P := fun bs f => exists be,
          instruction_encoding bs be /\ f = cons be)
        (Q := else_expression_encoding).
      * eapply parser_sound_map; [exact Be |].
        intros bs be H. exists be; auto.
      * intros k lt; simpl. exact (proj1 (proj2 (proj2 (Rec k lt)))).
      * intros xs ys f es [be [B F]] E; subst f.
        now apply else_expression_cons.
  - unfold language_step; cbn [_bes_end_with_x0b_or_x05_ctd].
    apply parser_sound_alt; [|apply parser_sound_alt].
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; subst; constructor.
    + eapply parser_sound_app with
        (P := fun bs f => bs = x05 :: nil /\ f = (fun es => (nil, es)))
        (Q := expression_encoding).
      * eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
        intros bs b [Bytes _]; auto.
      * intros k lt; simpl. apply parser_sound_le_lower. exact End.
      * intros xs ys f es [Bytes F] E; subst xs f; simpl.
        now apply if_body_else.
    + eapply parser_sound_app with
        (P := fun bs f => exists be, instruction_encoding bs be /\
          f = (fun '(l, r) => (be :: l, r)))
        (Q := if_body_encoding).
      * eapply parser_sound_map; [exact Be |].
        intros bs be H. exists be; auto.
      * intros k lt; simpl. exact (proj2 (proj2 (proj2 (Rec k lt)))).
      * intros xs ys f [left right] [be [B F]] E; subst f.
        now apply if_body_cons.
Qed.

Theorem production_language_sound n :
  language_sound n (language n).
Proof.
  apply (fix_invariant language_step language_sound).
  exact language_step_sound.
Qed.

Theorem production_parse_expr_sound n :
  parser_sound
    (parse_expr (Toks := SizedList byte) (M := option) (n := n))
    expression_encoding.
Proof. exact (proj1 (proj2 (production_language_sound n))). Qed.

Lemma expression_encoding_terminated bs es :
  expression_encoding bs es ->
  exists body, bs = body ++ (x0b :: nil).
Proof.
  intro E. induction E.
  - exists nil; reflexivity.
  - destruct IHE as [body Bytes].
    exists (xs ++ body). rewrite Bytes, app_assoc. reflexivity.
Qed.

Theorem run_parse_expr_grammar bs es :
  run_parse_expr bs = Some es -> expression_encoding bs es.
Proof.
  unfold run_parse_expr. apply run_parser_sound.
  exact production_parse_expr_sound.
Qed.

Theorem run_parse_expr_terminated bs es :
  run_parse_expr bs = Some es ->
  exists body, bs = body ++ (x0b :: nil).
Proof.
  intro Parsed.
  exact (expression_encoding_terminated bs es
    (run_parse_expr_grammar bs es Parsed)).
Qed.

End Grammar.
