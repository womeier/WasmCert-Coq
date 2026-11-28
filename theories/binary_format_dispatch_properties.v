(** Concrete primitive dispatch for the actual recursive language.
    The separately owned memory grammar is the only parameter of this layer;
    all other primitive families are discharged here against byte grammars. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_block_properties binary_format_atomic_properties
  binary_format_numeric_properties binary_memory_grammar_properties
  binary_format_tail_properties.
Local Notation byte := Byte.byte.

Definition atomic_encoding
    (Memory : list byte -> basic_instruction -> Prop) bs be :=
  control_atomic_encoding bs be \/
  bulk_atomic_encoding bs be \/
  numeric_atomic_encoding bs be \/
  Memory bs be.

Theorem primitive_dispatch_sound Memory :
  (forall n,
    parser_sound
      (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
      Memory) ->
  forall n p, In p (primitive_parsers n) ->
    parser_sound p (atomic_encoding Memory).
Proof.
  intros MemorySound n p Member.
  assert (Control : forall q,
    @parser_sound basic_instruction n q control_atomic_encoding ->
    parser_sound q (atomic_encoding Memory)).
  { intros q H. eapply parser_sound_weaken; [exact H |].
    intros bs be E; now left. }
  unfold primitive_parsers in Member.
  destruct Member as [Member|[Member|[Member|[Member|[Member|[Member|
    [Member|[Member|[Member|[Member|[Member|[Member|[Member|[Member|
    [Member|Member]]]]]]]]]]]]]]];
    try contradiction; subst p.
  - apply Control. apply parse_tail_call_control_sound.
  - apply Control. unfold parse_unreachable.
    apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control. unfold parse_nop.
    apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control. unfold parse_br, parse_labelidx, extract_labelidx.
    apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - apply Control. unfold parse_br_if, parse_labelidx, extract_labelidx.
    apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - apply Control. apply parse_br_table_sound.
  - apply Control. unfold parse_return.
    apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control. unfold parse_call, parse_funcidx, extract_funcidx.
    apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - apply Control. unfold parse_call_indirect.
    apply parse_indirect_calls_sound. left; auto.
  - apply Control; apply parse_reference_instruction_sound.
  - apply Control; apply parse_parametric_instruction_sound.
  - apply Control; apply parse_variable_instruction_sound.
  - eapply parser_sound_weaken; [apply parse_table_instruction_sound |].
    intros bs be [E|E]; [now left |right; now left].
  - eapply parser_sound_weaken; [apply MemorySound |].
    intros bs be E; right; right; now right.
  - eapply parser_sound_weaken; [apply parse_numeric_instruction_sound |].
    intros bs be E; right; right; now left.
Qed.

Definition wasm_atomic_encoding :=
  atomic_encoding binary_memory_instruction.

Theorem wasm_primitive_parsers_sound n p :
  In p (primitive_parsers n) -> parser_sound p wasm_atomic_encoding.
Proof.
  apply primitive_dispatch_sound.
  exact parse_memory_instruction_binary_sound.
Qed.

Theorem wasm_production_parse_expr_sound n :
  parser_sound
    (parse_expr (Toks := SizedList byte) (M := option) (n := n))
    (expression_encoding wasm_atomic_encoding block_type_encoding).
Proof.
  apply production_parse_expr_sound.
  - exact wasm_primitive_parsers_sound.
  - exact parse_block_type_sound.
Qed.

Theorem wasm_run_parse_expr_sound bs es :
  run_parse_expr bs = Some es ->
  expression_encoding wasm_atomic_encoding block_type_encoding bs es.
Proof.
  unfold run_parse_expr. apply run_parser_sound.
  exact wasm_production_parse_expr_sound.
Qed.

Theorem wasm_run_parse_expr_terminated bs es :
  run_parse_expr bs = Some es ->
  exists body, bs = body ++ (x0b :: nil).
Proof.
  intro Run.
  exact (expression_encoding_terminated wasm_atomic_encoding
    block_type_encoding bs es (wasm_run_parse_expr_sound bs es Run)).
Qed.

Theorem production_parse_expr_sound_with_memory Memory :
  (forall n,
    parser_sound
      (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
      Memory) ->
  forall n,
    parser_sound
      (parse_expr (Toks := SizedList byte) (M := option) (n := n))
      (expression_encoding (atomic_encoding Memory) block_type_encoding).
Proof.
  intro MemorySound.
  apply production_parse_expr_sound.
  - now apply primitive_dispatch_sound.
  - exact parse_block_type_sound.
Qed.
