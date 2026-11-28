(** Concrete function-type and function-index section codecs. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_type_properties binary_format_block_properties binary_format_print_encoding
  binary_format_vector_properties binary_format_section_properties
  binary_format_code_properties binary_format_custom_complete
  binary_format_declaration_properties.
Local Notation byte := Byte.byte.

Definition function_type_encoding := declaration_function_encoding.

Theorem parse_function_type_complete n :
  parser_complete
    (parse_function_type (Toks := SizedList byte) (M := option) (n := n))
    function_type_encoding.
Proof. apply parse_declaration_function_complete. Qed.

Theorem parse_function_type_sound n :
  parser_sound
    (parse_function_type (Toks := SizedList byte) (M := option) (n := n))
    function_type_encoding.
Proof. apply parse_declaration_function_sound. Qed.

Definition function_type_binary_wf := declaration_function_binary_wf.

Theorem binary_of_functype_encoding ft :
  function_type_binary_wf ft ->
  function_type_encoding (binary_of_functype ft) ft.
Proof. apply declaration_function_printer. Qed.

Definition type_section_encoding bytes types :=
  exists payload, bytes = x01 :: payload /\
    section_payload_encoding (vector_encoding recursive_type_encoding) payload types.

Theorem parse_typesec_complete n :
  parser_complete (parse_typesec (Toks := SizedList byte) (M := option) (n := n))
    type_section_encoding.
Proof.
  unfold parse_typesec; apply parser_complete_prefix_byte with
    (Q := section_payload_encoding (vector_encoding recursive_type_encoding)).
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_section_payload_complete; apply parse_vec_complete;
      apply parse_recursive_type_complete.
  - intros bytes types E; exact E.
Qed.

Theorem parse_typesec_sound n :
  parser_sound (parse_typesec (Toks := SizedList byte) (M := option) (n := n))
    type_section_encoding.
Proof.
  unfold parse_typesec; apply parser_sound_prefix_byte with
    (Q := section_payload_encoding (vector_encoding recursive_type_encoding)).
  - intros k lt; simpl; apply parser_sound_le_lower.
    apply parse_section_payload_sound; apply parse_vec_sound;
      apply parse_recursive_type_sound.
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
