(** Concrete current-AST limits/table/memory codecs. Static offsets are
    final u64; these module types still describe memory32/table32 only. *)
From Stdlib Require Import List Strings.Byte NArith.
From parseque Require Import Parseque.
From mathcomp Require Import ssrnat.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_type_properties binary_format_block_properties
  binary_format_numeric_complete binary_format_print_encoding
  binary_format_vector_properties binary_format_section_properties
  binary_format_code_properties binary_format_custom_complete.
Local Notation byte := Byte.byte.

Definition limits_encoding bytes lim :=
  match lim.(lim_max) with
  | None => exists minimum, bytes = x00 :: minimum /\
      index_encoding minimum lim.(lim_min)
  | Some maximum => exists minimum upper,
      bytes = x01 :: minimum ++ upper /\
      index_encoding minimum lim.(lim_min) /\ index_encoding upper maximum
  end.

Lemma parse_limits_min_complete n :
  parser_complete
    (Combinators.rand (exact_byte (M := option) (Toks := SizedList byte) (n := n) x00)
      (box (Combinators.map (fun min => Build_limits min None) parse_u32_as_N)))
    (fun bytes lim => exists minimum min,
      bytes = x00 :: minimum /\ index_encoding minimum min /\
      lim = Build_limits min None).
Proof.
  apply parser_complete_prefix_byte with
    (Q := fun bytes lim => exists min,
      index_encoding bytes min /\ lim = Build_limits min None).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply leb128_properties.parse_u32_prefix_complete |].
    intros bytes lim [min [E Value]]; exists min; auto.
  - intros bytes lim [minimum [min [Bytes Facts]]].
    exists minimum; split; [exact Bytes |exists min; exact Facts].
Qed.

Lemma parse_limits_max_complete n :
  parser_complete
    (Combinators.app
      (Combinators.rand (exact_byte (M := option) (Toks := SizedList byte) (n := n) x01)
        (box (Combinators.map (fun min max => Build_limits min (Some max)) parse_u32_as_N)))
      (box parse_u32_as_N))
    (fun bytes lim => exists minimum upper min max,
      bytes = x01 :: minimum ++ upper /\
      index_encoding minimum min /\ index_encoding upper max /\
      lim = Build_limits min (Some max)).
Proof.
  eapply parser_complete_app with
    (P := fun bytes f => exists minimum min,
      bytes = x01 :: minimum /\ index_encoding minimum min /\
      f = (fun max => Build_limits min (Some max))) (Q := index_encoding).
  - apply parser_complete_prefix_byte with
      (Q := fun bytes f => exists min, index_encoding bytes min /\
        f = (fun max => Build_limits min (Some max))).
    + intros k lt; simpl; apply parser_complete_le_lower.
      eapply parser_complete_map; [apply leb128_properties.parse_u32_prefix_complete |].
      intros bytes f [min [E Value]]; exists min; auto.
    + intros bytes f [minimum [min [Bytes Facts]]].
      exists minimum; split; [exact Bytes |exists min; exact Facts].
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply leb128_properties.parse_u32_prefix_complete.
  - intros bytes lim [minimum [upper [min [max [Bytes [Min [Max Value]]]]]]].
    exists (x01 :: minimum), upper, (fun max => Build_limits min (Some max)), max.
    split; [exact Bytes |]. split; [exists minimum, min; auto |].
    split; assumption.
Qed.

Theorem parse_limits_complete n :
  parser_complete (parse_limits (Toks := SizedList byte) (M := option) (n := n))
    limits_encoding.
Proof.
  intros m bound input prefix suffix [min [max|]] Bytes Encoding.
  - assert (Complete : parser_complete
      (parse_limits (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes lim => exists minimum upper min max,
        bytes = x01 :: minimum ++ upper /\
        index_encoding minimum min /\ index_encoding upper max /\
        lim = Build_limits min (Some max))).
    { unfold parse_limits.
      eapply parser_complete_alt_right_initial with (actual := x01).
      - numeric_initial.
      - discriminate.
      - intros bytes lim [minimum [upper [lower_value [upper_value [Parts _]]]]].
        now exists (minimum ++ upper).
      - apply parse_limits_max_complete. }
    apply (Complete m bound input prefix suffix (Build_limits min (Some max)) Bytes).
    destruct Encoding as [minimum [upper [Parts [Min Max]]]].
    exists minimum, upper, min, max; auto.
  - unfold parse_limits.
    eapply parser_complete_alt_left.
    + apply parse_limits_min_complete.
    + exact Bytes.
    + destruct Encoding as [minimum [Parts Min]].
      exists minimum, min; auto.
Qed.

Definition limits_binary_wf lim :=
  binary_index_wf lim.(lim_min) /\
  match lim.(lim_max) with None => True | Some max => binary_index_wf max end.

Theorem binary_of_limits_encoding lim :
  limits_binary_wf lim -> limits_encoding (binary_of_limits lim) lim.
Proof.
  destruct lim as [min [max|]]; intros [Min Max];
    unfold binary_of_limits, limits_encoding; cbn [lim_min lim_max].
  -
    rewrite !ssrnat.nat_of_binK.
    exists (binary_of_idx min), (binary_of_idx max).
    split; [reflexivity |]. split; now apply binary_of_index_encoding.
  - rewrite ssrnat.nat_of_binK.
    exists (binary_of_idx min); split; [reflexivity |now apply binary_of_index_encoding].
Qed.

Definition table_type_encoding bytes tt :=
  exists limits, bytes = binary_of_reference_type tt.(tt_elem_type) :: limits /\
    limits_encoding limits tt.(tt_limits).

Theorem parse_table_type_complete n :
  parser_complete (parse_table_type (Toks := SizedList byte) (M := option) (n := n))
    table_type_encoding.
Proof.
  unfold parse_table_type.
  eapply parser_complete_app with
    (P := fun bytes f => exists rt, bytes = binary_of_reference_type rt :: nil /\
      f = (fun limits => Build_table_type limits rt)) (Q := limits_encoding).
  - eapply parser_complete_map; [apply parse_reference_type_complete |].
    intros bytes f [rt [E Value]]; exists rt; auto.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_limits_complete.
  - intros bytes [limits rt] [body [Bytes E]].
    exists (binary_of_reference_type rt :: nil), body,
      (fun limits => Build_table_type limits rt), limits.
    split; [exact Bytes |]. split; [exists rt; auto |].
    split; [exact E |reflexivity].
Qed.

Theorem parse_memory_type_complete n :
  parser_complete (parse_memory_type (Toks := SizedList byte) (M := option) (n := n))
    limits_encoding.
Proof.
  unfold parse_memory_type.
  eapply parser_complete_map; [apply parse_limits_complete |].
  intros bytes lim E; exists lim; auto.
Qed.

Theorem binary_of_table_type_encoding tt :
  limits_binary_wf tt.(tt_limits) ->
  table_type_encoding (binary_of_table_type tt) tt.
Proof.
  intro Wf; exists (binary_of_limits tt.(tt_limits)).
  split; [reflexivity |now apply binary_of_limits_encoding].
Qed.

Definition module_table_encoding bytes table := table_type_encoding bytes table.(modtab_type).
Definition module_memory_encoding bytes memory := limits_encoding bytes memory.(modmem_type).

Theorem parse_module_table_complete n :
  parser_complete (parse_module_table (Toks := SizedList byte) (M := option) (n := n))
    module_table_encoding.
Proof.
  unfold parse_module_table.
  eapply parser_complete_map; [apply parse_table_type_complete |].
  intros bytes [tt] E; exists tt; auto.
Qed.

Theorem parse_module_memory_complete n :
  parser_complete (parse_module_mem (Toks := SizedList byte) (M := option) (n := n))
    module_memory_encoding.
Proof.
  unfold parse_module_mem.
  eapply parser_complete_map; [apply parse_memory_type_complete |].
  intros bytes [mt] E; exists mt; auto.
Qed.

Definition table_section_encoding bytes tables :=
  exists payload, bytes = x04 :: payload /\
    section_payload_encoding (vector_encoding module_table_encoding) payload tables.
Definition memory_section_encoding bytes memories :=
  exists payload, bytes = x05 :: payload /\
    section_payload_encoding (vector_encoding module_memory_encoding) payload memories.

Theorem parse_tablesec_complete n :
  parser_complete (parse_tablesec (Toks := SizedList byte) (M := option) (n := n))
    table_section_encoding.
Proof.
  unfold parse_tablesec; apply parser_complete_prefix_byte with
    (Q := section_payload_encoding (vector_encoding module_table_encoding)).
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_section_payload_complete; apply parse_vec_complete; apply parse_module_table_complete.
  - intros bytes tables E; exact E.
Qed.

Theorem parse_memsec_complete n :
  parser_complete (parse_memsec (Toks := SizedList byte) (M := option) (n := n))
    memory_section_encoding.
Proof.
  unfold parse_memsec; apply parser_complete_prefix_byte with
    (Q := section_payload_encoding (vector_encoding module_memory_encoding)).
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_section_payload_complete; apply parse_vec_complete; apply parse_module_memory_complete.
  - intros bytes memories E; exact E.
Qed.

Theorem binary_of_tablesec_encoding tables :
  Forall (fun t => limits_binary_wf t.(modtab_type).(tt_limits)) tables ->
  binary_vector_length_wf tables ->
  binary_vector_length_wf (binary_of_vec binary_of_module_table tables) ->
  table_section_encoding (binary_of_tablesec tables) tables.
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_module_table tables)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size; induction Wf; constructor; [|assumption].
  now apply binary_of_table_type_encoding.
Qed.

Theorem binary_of_memsec_encoding memories :
  Forall (fun m => limits_binary_wf m.(modmem_type)) memories ->
  binary_vector_length_wf memories ->
  binary_vector_length_wf (binary_of_vec binary_of_module_mem memories) ->
  memory_section_encoding (binary_of_memsec memories) memories.
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_module_mem memories)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size; induction Wf; constructor; [|assumption].
  now apply binary_of_limits_encoding.
Qed.

Theorem parse_tablesec_wrapper_complete_canonical n :
  parser_complete
    (parse_tablesec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    table_section_encoding.
Proof.
  unfold parse_tablesec_wrapper.
  apply parse_with_customsec_star_before_complete_without_custom.
  - intros bytes tables [payload [Bytes _]].
    exists x04, payload; split; [exact Bytes |discriminate].
  - apply parse_tablesec_complete.
Qed.

Theorem parse_memsec_wrapper_complete_canonical n :
  parser_complete
    (parse_memsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    memory_section_encoding.
Proof.
  unfold parse_memsec_wrapper.
  apply parse_with_customsec_star_before_complete_without_custom.
  - intros bytes memories [payload [Bytes _]].
    exists x05, payload; split; [exact Bytes |discriminate].
  - apply parse_memsec_complete.
Qed.

Corollary binary_of_tablesec_wrapper_roundtrip tables :
  Forall (fun t => limits_binary_wf t.(modtab_type).(tt_limits)) tables ->
  binary_vector_length_wf tables ->
  binary_vector_length_wf (binary_of_vec binary_of_module_table tables) ->
  run (binary_of_tablesec tables) (fun _ => parse_tablesec_wrapper) = Some tables.
Proof.
  intros Wf Count Size; apply (run_parser_complete _ table_section_encoding).
  - exact parse_tablesec_wrapper_complete_canonical.
  - now apply binary_of_tablesec_encoding.
Qed.

Corollary binary_of_memsec_wrapper_roundtrip memories :
  Forall (fun m => limits_binary_wf m.(modmem_type)) memories ->
  binary_vector_length_wf memories ->
  binary_vector_length_wf (binary_of_vec binary_of_module_mem memories) ->
  run (binary_of_memsec memories) (fun _ => parse_memsec_wrapper) = Some memories.
Proof.
  intros Wf Count Size; apply (run_parser_complete _ memory_section_encoding).
  - exact parse_memsec_wrapper_complete_canonical.
  - now apply binary_of_memsec_encoding.
Qed.
