(** Concrete function-type and function-index section codecs. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_type_properties binary_format_block_properties binary_format_print_encoding
  binary_format_vector_properties binary_format_section_properties
  binary_format_code_properties binary_format_custom_complete.
Local Notation byte := Byte.byte.
From Wasm Require Import binary_format_declaration_properties
  binary_format_declaration_print.

Definition function_type_encoding bytes ft :=
  exists arguments results ins outs, bytes = x60 :: arguments ++ results /\
    vector_encoding declaration_value_encoding arguments ins /\
    vector_encoding declaration_value_encoding results outs /\ ft = Tf ins outs.

Definition function_type_body_encoding bytes (pair : result_type * result_type) :=
  exists arguments results, bytes = arguments ++ results /\
    vector_encoding declaration_value_encoding arguments (fst pair) /\
    vector_encoding declaration_value_encoding results (snd pair).

Theorem parse_function_type_complete n :
  parser_complete
    (parse_function_type (Toks := SizedList byte) (M := option) (n := n))
    function_type_encoding.
Proof.
  unfold parse_function_type.
  apply parser_complete_prefix_byte with
    (Q := fun bytes ft => exists arguments results ins outs,
      bytes = arguments ++ results /\
      vector_encoding declaration_value_encoding arguments ins /\
      vector_encoding declaration_value_encoding results outs /\ ft = Tf ins outs).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map with (P := function_type_body_encoding).
    + unfold Combinators.and.
      eapply parser_complete_andbind with
        (P := vector_encoding declaration_value_encoding)
        (Q := fun _ => vector_encoding declaration_value_encoding).
      * apply parse_vec_complete; apply parse_declaration_value_complete.
      * intros ins j lower; simpl; apply parser_complete_le_lower.
        apply parse_vec_complete; apply parse_declaration_value_complete.
      * intros bytes ins outs [arguments [results [Bytes [Ins Outs]]]].
        exists arguments, results; auto.
    + intros bytes ft [arguments [results [ins [outs [Bytes [Ins [Outs Value]]]]]]].
      exists (ins, outs); split; [exists arguments, results; auto |exact Value].
  - intros bytes ft [arguments [results [ins [outs [Bytes Facts]]]]].
    exists (arguments ++ results); split; [exact Bytes |].
    exists arguments, results, ins, outs; auto.
Qed.

Theorem parse_function_type_sound n :
  parser_sound
    (parse_function_type (Toks := SizedList byte) (M := option) (n := n))
    function_type_encoding.
Proof.
  unfold parse_function_type.
  apply parser_sound_prefix_byte with
    (Q := fun bytes ft => exists arguments results ins outs,
      bytes = arguments ++ results /\
      vector_encoding declaration_value_encoding arguments ins /\
      vector_encoding declaration_value_encoding results outs /\ ft = Tf ins outs).
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_map with (P := function_type_body_encoding).
    + unfold Combinators.and.
      eapply parser_sound_andbind with
        (P := vector_encoding declaration_value_encoding)
        (Q := fun _ => vector_encoding declaration_value_encoding).
      * apply parse_vec_sound; apply parse_declaration_value_sound.
      * intros ins j lower; simpl; apply parser_sound_le_lower.
        apply parse_vec_sound; apply parse_declaration_value_sound.
      * intros arguments results ins outs Ins Outs.
        exists arguments, results; auto.
    + intros bytes [ins outs] [arguments [results [Bytes [Ins Outs]]]].
      exists arguments, results, ins, outs; auto.
  - intros bytes ft [arguments [results [ins [outs [Bytes Facts]]]]].
    exists arguments, results, ins, outs; subst bytes; auto.
Qed.

Definition function_type_binary_wf ft :=
  match ft with Tf ins outs =>
    Forall declaration_value_binary_wf ins /\ Forall declaration_value_binary_wf outs /\
    binary_vector_length_wf ins /\ binary_vector_length_wf outs
  end.

Theorem binary_of_functype_encoding ft :
  function_type_binary_wf ft ->
  function_type_encoding (binary_of_functype ft) ft.
Proof.
  destruct ft as [ins outs]; intros [Ins [Outs [InsCount OutsCount]]].
  exists (binary_of_result_type ins), (binary_of_result_type outs), ins, outs.
  split; [reflexivity |]. split.
  - now apply binary_of_declaration_values_encoding.
  - split; [now apply binary_of_declaration_values_encoding |reflexivity].
Qed.

Definition type_section_encoding bytes types :=
  exists payload, bytes = x01 :: payload /\
    section_payload_encoding (vector_encoding declaration_recursive_encoding) payload types.

Theorem parse_typesec_complete n :
  parser_complete (parse_typesec (Toks := SizedList byte) (M := option) (n := n))
    type_section_encoding.
Proof.
  unfold parse_typesec; apply parser_complete_prefix_byte with
    (Q := section_payload_encoding (vector_encoding declaration_recursive_encoding)).
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_section_payload_complete; apply parse_vec_complete;
      apply parse_recursive_type_source_complete.
  - intros bytes types E; exact E.
Qed.

Theorem parse_typesec_sound n :
  parser_sound (parse_typesec (Toks := SizedList byte) (M := option) (n := n))
    type_section_encoding.
Proof.
  unfold parse_typesec; apply parser_sound_prefix_byte with
    (Q := section_payload_encoding (vector_encoding declaration_recursive_encoding)).
  - intros k lt; simpl; apply parser_sound_le_lower.
    apply parse_section_payload_sound; apply parse_vec_sound;
      apply parse_recursive_type_source_sound.
  - intros bytes types E; exists bytes; auto.
Qed.

Theorem binary_of_typesec_encoding types :
  Forall recursive_type_binary_wf types -> binary_vector_length_wf types ->
  binary_vector_length_wf (binary_of_vec binary_of_recursive_type types) ->
  type_section_encoding (binary_of_typesec types) types.
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_recursive_type types)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size; induction Wf; constructor;
    [now apply binary_of_recursive_type_encoding |assumption].
Qed.

Theorem parse_typesec_wrapper_complete_canonical n :
  parser_complete
    (parse_typesec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    type_section_encoding.
Proof.
  unfold parse_typesec_wrapper.
  apply parse_with_customsec_star_before_complete_without_custom.
  - intros bytes types [payload [Bytes _]].
    exists x01, payload; split; [exact Bytes |discriminate].
  - apply parse_typesec_complete.
Qed.

Corollary binary_of_typesec_wrapper_roundtrip types :
  Forall recursive_type_binary_wf types -> binary_vector_length_wf types ->
  binary_vector_length_wf (binary_of_vec binary_of_recursive_type types) ->
  run (binary_of_typesec types) (fun _ => parse_typesec_wrapper) = Some types.
Proof.
  intros Wf Count Size; apply (run_parser_complete _ type_section_encoding).
  - exact parse_typesec_wrapper_complete_canonical.
  - now apply binary_of_typesec_encoding.
Qed.
