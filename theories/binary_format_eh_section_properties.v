(** Actual tag-section grammar, with arbitrary custom prefixes and framing.
    No assumption about the old non-EH AST or numeric section ordering. *)
From Stdlib Require Import List Strings.Byte Arith NArith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_eh_properties
  binary_format_vector_properties binary_format_section_properties
  binary_format_custom_properties binary_format_custom_general_complete
  binary_format_custom_optional_properties binary_format_printer
  binary_format_printer_properties.
Local Notation byte := Byte.byte.

Definition tag_section_encoding :=
  eh_prefixed x0d (section_payload_encoding (vector_encoding tag_type_encoding)).
Definition tag_section_with_custom_encoding :=
  custom_before_encoding custom_bytes tag_section_encoding.

Theorem parse_tagsec_sound n :
  parser_sound (parse_tagsec (Toks := SizedList byte) (M := option) (n := n))
    tag_section_encoding.
Proof.
  unfold parse_tagsec, tag_section_encoding.
  apply eh_prefixed_sound; apply parse_section_payload_sound.
  apply parse_vec_sound; apply parse_tag_sound.
Qed.

Theorem parse_tagsec_complete n :
  parser_complete (parse_tagsec (Toks := SizedList byte) (M := option) (n := n))
    tag_section_encoding.
Proof.
  unfold parse_tagsec, tag_section_encoding.
  apply eh_prefixed_complete; apply parse_section_payload_complete.
  apply parse_vec_complete; apply parse_tag_complete.
Qed.

Theorem parse_tagsec_wrapper_sound n :
  parser_sound (parse_tagsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    tag_section_with_custom_encoding.
Proof.
  unfold parse_tagsec_wrapper, tag_section_with_custom_encoding.
  apply parse_with_customsec_star_before_sound; apply parse_tagsec_sound.
Qed.

Theorem parse_tagsec_wrapper_complete n :
  parser_complete (parse_tagsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    tag_section_with_custom_encoding.
Proof.
  unfold parse_tagsec_wrapper, tag_section_with_custom_encoding.
  apply parse_with_customsec_star_before_general_complete.
  - intros bytes values [payload [Bytes _]].
    exists x0d, payload; split; [exact Bytes |discriminate].
  - apply parse_tagsec_complete.
Qed.

Theorem parse_tagsec_wrapper_absent n m (bound : m <= n) input :
  custom_avoids_section x0d (input_bytes input) ->
  runParser (parse_tagsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    bound input = None.
Proof.
  intro Avoid; unfold parse_tagsec_wrapper.
  eapply custom_prefixed_section_absent with (tag := x0d);
    [discriminate | |exact Avoid].
  unfold parse_tagsec; apply parser_initial_rand; apply exact_byte_initial.
Qed.

Theorem run_parse_tagsec_wrapper_correct bytes tags rest :
  run_parse_prefix (fun n => parse_tagsec_wrapper (n := n)) bytes = Some (tags, rest) <->
  exists prefix, bytes = prefix ++ rest /\ tag_section_with_custom_encoding prefix tags.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_tagsec_wrapper_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_tagsec_wrapper_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest tags Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (tags, rest)).
    now rewrite Value, Rest.
Qed.

Lemma printed_eh_index_encoding x :
  (x <= 4294967295)%N -> eh_index_encoding (binary_of_u32 x) x.
Proof.
  intro Bound.
  eapply (run_parser_sound (fun n => parse_u32_as_N (n := n)) eh_index_encoding).
  - exact eh_index_sound.
  - now apply binary_of_u32_roundtrip.
Qed.

Lemma printed_tag_encoding x :
  (x <= 4294967295)%N -> tag_type_encoding (binary_of_tag x) x.
Proof.
  intro Bound; exists (binary_of_u32 x); split; [reflexivity |].
  now apply printed_eh_index_encoding.
Qed.

Theorem binary_of_tagsec_encoding tags :
  Forall (fun x => (x <= 4294967295)%N) tags ->
  (N.of_nat (length tags) <= 4294967295)%N ->
  (N.of_nat (length (binary_of_vec binary_of_tag tags)) <= 4294967295)%N ->
  tag_section_encoding (binary_of_tagsec tags) tags.
Proof.
  intros Bounds Count Size.
  assert (Items : vector_encoding tag_type_encoding (binary_of_vec binary_of_tag tags) tags).
  { apply (run_vec_sound (fun n => parse_tag (n := n)) tag_type_encoding
      parse_tag_sound).
    apply (binary_of_vec_roundtrip (fun n => parse_tag (n := n))
      binary_of_tag tag_type_encoding tags).
    - exact parse_tag_complete.
    - intros x Member; apply printed_tag_encoding.
      exact (proj1 (Forall_forall _ _) Bounds x Member).
    - exact Count. }
  pose proof (printed_eh_index_encoding _ Size) as Header.
  unfold tag_section_encoding, binary_of_tagsec.
  exists (with_length (binary_of_vec binary_of_tag tags)); split; [reflexivity |].
  exists (binary_of_u32 (N.of_nat (length (binary_of_vec binary_of_tag tags)))),
    (binary_of_vec binary_of_tag tags).
  split; [unfold with_length; rewrite printer_bin_of_nat; reflexivity |].
  destruct Header as [Encoding [Range Width]].
  repeat split; assumption.
Qed.

Theorem binary_of_tagsec_roundtrip tags :
  Forall (fun x => (x <= 4294967295)%N) tags ->
  (N.of_nat (length tags) <= 4294967295)%N ->
  (N.of_nat (length (binary_of_vec binary_of_tag tags)) <= 4294967295)%N ->
  run (binary_of_tagsec tags) (fun n => parse_tagsec (n := n)) = Some tags.
Proof.
  intros Bounds Count Size.
  apply (run_parser_complete (fun n => parse_tagsec (n := n)) tag_section_encoding).
  - exact parse_tagsec_complete.
  - now apply binary_of_tagsec_encoding.
Qed.
