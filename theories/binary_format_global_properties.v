(** Concrete global initializer and global-section codec composition. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_type_properties binary_format_block_properties
  binary_format_dispatch_properties binary_format_numeric_complete
  binary_format_recursive_complete binary_format_expression_print
  binary_format_print_encoding binary_format_vector_properties
  binary_format_section_properties binary_format_code_properties
  binary_format_custom_complete.
Local Notation byte := Byte.byte.
Local Notation Expression := (expression_encoding wasm_atomic_encoding block_type_encoding).

Lemma parse_mut_complete n :
  parser_complete (parse_mut (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes mut => bytes = binary_of_mutability mut).
Proof.
  intros m bound input prefix suffix mut Bytes Encoding; destruct mut.
  - unfold parse_mut.
    eapply parser_complete_alt_left.
    + apply fixed_instruction_complete.
    + exact Bytes.
    + split; [exact Encoding |reflexivity].
  - assert (Complete : parser_complete
      (parse_mut (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes mut => bytes = x01 :: nil /\ mut = MUT_var)).
    { unfold parse_mut.
      byte_type_dispatch x01 (fixed_instruction_complete n x01 MUT_var)
        (fixed_encoding_head x01 MUT_var). }
    apply (Complete m bound input prefix suffix MUT_var Bytes).
    split; [exact Encoding |reflexivity].
Qed.

Lemma parse_mut_sound n :
  parser_sound (parse_mut (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes mut => bytes = binary_of_mutability mut).
Proof.
  unfold parse_mut; apply parser_sound_alt.
  all: eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  all: intros bytes b [Bytes _]; exact Bytes.
Qed.

Definition global_type_encoding bytes gt :=
  bytes = binary_of_global_type gt /\ gt.(tg_t) <> T_bot.

Theorem parse_global_type_complete n :
  parser_complete
    (parse_global_type (Toks := SizedList byte) (M := option) (n := n))
    global_type_encoding.
Proof.
  unfold parse_global_type.
  eapply parser_complete_app with
    (P := fun bytes f => exists t, value_type_encoding bytes t /\
      f = (fun mut => Build_global_type mut t))
    (Q := fun bytes mut => bytes = binary_of_mutability mut).
  - eapply parser_complete_map; [apply parse_value_type_complete |].
    intros bytes f [t [E Value]]; exists t; auto.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_mut_complete.
  - intros bytes [mut t] [Bytes Valid].
    exists (binary_of_value_type t :: nil), (binary_of_mutability mut),
      (fun mut => Build_global_type mut t), mut.
    split; [exact Bytes |]. split.
    + exists t; split; [split; [reflexivity |exact Valid] |reflexivity].
    + split; reflexivity.
Qed.

Theorem parse_global_type_sound n :
  parser_sound
    (parse_global_type (Toks := SizedList byte) (M := option) (n := n))
    global_type_encoding.
Proof.
  unfold parse_global_type.
  eapply parser_sound_app with
    (P := fun bytes f => exists t, value_type_encoding bytes t /\
      f = (fun mut => Build_global_type mut t))
    (Q := fun bytes mut => bytes = binary_of_mutability mut).
  - eapply parser_sound_map; [apply parse_value_type_sound |].
    intros bytes t E; exists t; auto.
  - intros k lt; simpl; apply parser_sound_le_lower; apply parse_mut_sound.
  - intros first second f mut [t [[Bytes Valid] Value]] Mut.
    subst first second f; split; [reflexivity |exact Valid].
Qed.

Definition global_encoding bytes g :=
  exists types body, bytes = types ++ body /\
    global_type_encoding types g.(modglob_type) /\
    Expression body g.(modglob_init).

Theorem parse_module_global_complete n :
  parser_complete
    (parse_module_global (Toks := SizedList byte) (M := option) (n := n))
    global_encoding.
Proof.
  unfold parse_module_global.
  eapply parser_complete_app with
    (P := fun bytes f => exists gt, global_type_encoding bytes gt /\
      f = (fun es => Build_module_global gt es)) (Q := Expression).
  - eapply parser_complete_map; [apply parse_global_type_complete |].
    intros bytes f [gt [E Value]]; exists gt; auto.
  - intros k lt; simpl; apply parser_complete_le_lower.
    exact (wasm_production_parse_expr_complete n).
  - intros bytes [gt es] [types [body [Bytes [T E]]]].
    exists types, body, (fun es => Build_module_global gt es), es.
    split; [exact Bytes |]. split; [exists gt; auto |].
    split; [exact E |reflexivity].
Qed.

Theorem parse_module_global_sound n :
  parser_sound
    (parse_module_global (Toks := SizedList byte) (M := option) (n := n))
    global_encoding.
Proof.
  unfold parse_module_global.
  eapply parser_sound_app with
    (P := fun bytes f => exists gt, global_type_encoding bytes gt /\
      f = (fun es => Build_module_global gt es)) (Q := Expression).
  - eapply parser_sound_map; [apply parse_global_type_sound |].
    intros bytes gt E; exists gt; auto.
  - intros k lt; simpl; apply parser_sound_le_lower.
    exact (wasm_production_parse_expr_sound n).
  - intros types body f es [gt [T Value]] E; subst f.
    exists types, body; auto.
Qed.

Definition global_binary_wf g :=
  g.(modglob_type).(tg_t) <> T_bot /\ expression_binary_wf g.(modglob_init).

Theorem binary_of_module_global_encoding g :
  global_binary_wf g -> global_encoding (binary_of_module_global g) g.
Proof.
  intros [TypeWf ExprWf].
  exists (binary_of_global_type g.(modglob_type)), (binary_of_expr g.(modglob_init)).
  split; [reflexivity |]. split.
  - split; [reflexivity |exact TypeWf].
  - now apply binary_of_expr_encoding.
Qed.

Definition global_section_encoding bytes globals :=
  exists payload, bytes = x06 :: payload /\
    section_payload_encoding (vector_encoding global_encoding) payload globals.

Theorem parse_globalsec_complete n :
  parser_complete (parse_globalsec (Toks := SizedList byte) (M := option) (n := n))
    global_section_encoding.
Proof.
  unfold parse_globalsec; apply parser_complete_prefix_byte with
    (Q := section_payload_encoding (vector_encoding global_encoding)).
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_section_payload_complete; apply parse_vec_complete;
      apply parse_module_global_complete.
  - intros bytes globals E; exact E.
Qed.

Theorem parse_globalsec_sound n :
  parser_sound (parse_globalsec (Toks := SizedList byte) (M := option) (n := n))
    global_section_encoding.
Proof.
  unfold parse_globalsec; apply parser_sound_prefix_byte with
    (Q := section_payload_encoding (vector_encoding global_encoding)).
  - intros k lt; simpl; apply parser_sound_le_lower.
    apply parse_section_payload_sound; apply parse_vec_sound;
      apply parse_module_global_sound.
  - intros bytes globals E; exists bytes; auto.
Qed.

Theorem binary_of_globalsec_encoding globals :
  Forall global_binary_wf globals -> binary_vector_length_wf globals ->
  binary_vector_length_wf (binary_of_vec binary_of_module_global globals) ->
  global_section_encoding (binary_of_globalsec globals) globals.
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_module_global globals)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size.
  induction Wf; constructor; [now apply binary_of_module_global_encoding |assumption].
Qed.

Theorem parse_globalsec_wrapper_complete_canonical n :
  parser_complete
    (parse_globalsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    global_section_encoding.
Proof.
  unfold parse_globalsec_wrapper.
  apply parse_with_customsec_star_before_complete_without_custom.
  - intros bytes globals [payload [Bytes _]].
    exists x06, payload; split; [exact Bytes |discriminate].
  - apply parse_globalsec_complete.
Qed.

Corollary binary_of_globalsec_wrapper_roundtrip globals :
  Forall global_binary_wf globals -> binary_vector_length_wf globals ->
  binary_vector_length_wf (binary_of_vec binary_of_module_global globals) ->
  run (binary_of_globalsec globals) (fun _ => parse_globalsec_wrapper) = Some globals.
Proof.
  intros Wf Count Size; apply (run_parser_complete _ global_section_encoding).
  - exact parse_globalsec_wrapper_complete_canonical.
  - now apply binary_of_globalsec_encoding.
Qed.
