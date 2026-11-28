(** Concrete discharge of EVERY production primitive soundness contract.
    This is not the parameterized structural expression theorem. The memory
    relation describes the actual existing memory-zero/u32-offset profile. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_block_properties binary_format_atomic_properties
  binary_format_numeric_properties binary_format_memory_properties.
Local Notation byte := Byte.byte.

Definition wasm_atomic_encoding bytes be :=
  control_atomic_encoding bytes be \/
  bulk_atomic_encoding bytes be \/
  numeric_atomic_encoding bytes be \/
  memory_instruction_encoding bytes be.

Theorem wasm_primitive_parsers_sound n p :
  In p (primitive_parsers n) -> parser_sound p wasm_atomic_encoding.
Proof.
  intro Member.
  assert (Control : forall q,
    @parser_sound basic_instruction n q control_atomic_encoding ->
    parser_sound q wasm_atomic_encoding).
  { intros q Sound; eapply parser_sound_weaken; [exact Sound |].
    intros bytes be Enc; now left. }
  unfold primitive_parsers in Member.
  do 20 (destruct Member as [Member|Member]; [subst p; shelve |]).
  contradiction. Unshelve.
  - apply Control; unfold parse_unreachable; apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control; unfold parse_nop; apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control; unfold parse_br, parse_labelidx, extract_labelidx.
    apply single_index_instruction_sound; unfold single_index_opcodes; simpl; tauto.
  - apply Control; unfold parse_br_if, parse_labelidx, extract_labelidx.
    apply single_index_instruction_sound; unfold single_index_opcodes; simpl; tauto.
  - apply Control; apply parse_br_table_sound.
  - apply Control; unfold parse_return; apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control; unfold parse_throw; apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - apply Control; unfold parse_throw_ref; apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply Control; unfold parse_call, parse_funcidx, extract_funcidx.
    apply single_index_instruction_sound; unfold single_index_opcodes; simpl; tauto.
  - apply Control; unfold parse_call_indirect; apply parse_indirect_calls_sound; now left.
  - apply Control; unfold parse_return_call, parse_funcidx, extract_funcidx.
    apply single_index_instruction_sound; unfold single_index_opcodes; simpl; tauto.
  - apply Control; unfold parse_return_call_indirect; apply parse_indirect_calls_sound; now right.
  - apply Control; unfold parse_call_ref, parse_typeidx.
    apply single_index_instruction_sound; unfold single_index_opcodes; simpl; tauto.
  - apply Control; unfold parse_return_call_ref, parse_typeidx.
    apply single_index_instruction_sound; unfold single_index_opcodes; simpl; tauto.
  - apply Control; apply parse_reference_instruction_sound.
  - apply Control; apply parse_parametric_instruction_sound.
  - apply Control; apply parse_variable_instruction_sound.
  - eapply parser_sound_weaken; [apply parse_table_instruction_sound |].
    intros bytes be [Enc|Enc]; [now left |right; now left].
  - eapply parser_sound_weaken; [apply parse_memory_instruction_sound |].
    intros bytes be Enc; right; right; now right.
  - eapply parser_sound_weaken; [apply parse_numeric_instruction_sound |].
    intros bytes be Enc; right; right; now left.
Qed.

Theorem wasm_production_parse_expr_sound n :
  parser_sound (parse_expr (Toks := SizedList byte) (M := option) (n := n))
    (expression_encoding wasm_atomic_encoding block_type_encoding).
Proof.
  apply production_parse_expr_sound.
  - exact wasm_primitive_parsers_sound.
  - exact parse_block_type_sound.
Qed.

Theorem wasm_run_parse_expr_sound bytes es :
  run_parse_expr bytes = Some es ->
  expression_encoding wasm_atomic_encoding block_type_encoding bytes es.
Proof.
  unfold run_parse_expr; apply run_parser_sound; exact wasm_production_parse_expr_sound.
Qed.

Theorem wasm_run_parse_expr_terminated bytes es :
  run_parse_expr bytes = Some es ->
  exists body, bytes = body ++ (x0b :: nil).
Proof.
  intro Parsed.
  exact (expression_encoding_terminated wasm_atomic_encoding block_type_encoding
    bytes es (wasm_run_parse_expr_sound bytes es Parsed)).
Qed.
