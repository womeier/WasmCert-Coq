(** Width-aware table/memory declarations and optional table initializers.
    Source binary encodability is separate from semantic limit validation. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_type_properties binary_format_block_properties
  binary_format_numeric_complete binary_format_print_encoding
  binary_format_vector_properties binary_format_section_properties
  binary_format_code_properties binary_format_custom_complete.
Local Notation byte := Byte.byte.
From Wasm Require Import binary_format_declaration_properties
  binary_format_table_type_properties binary_format_width_properties
  binary_format_dispatch_properties binary_format_recursive_complete
  binary_format_expression_print.
Local Notation Expression :=
  (expression_encoding wasm_atomic_encoding block_type_encoding).

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
    exists (binary_of_idx min), (binary_of_idx max).
    split; [reflexivity |]. split; now apply binary_of_index_encoding.
  -
    exists (binary_of_idx min); split; [reflexivity |now apply binary_of_index_encoding].
Qed.

Definition table_type_encoding := binary_format_table_type_properties.table_type_encoding.

Theorem parse_table_type_complete n :
  parser_complete (parse_table_type (Toks := SizedList byte) (M := option) (n := n))
    table_type_encoding.
Proof.
  apply parse_table_type_source_complete.
Qed.

Definition memory_type_encoding :=
  source_unary (fun '(width, lims) => Build_memory_type lims width)
    width_limits_encoding.

Theorem parse_memory_type_complete n :
  parser_complete (parse_memory_type (Toks := SizedList byte) (M := option) (n := n))
    memory_type_encoding.
Proof.
  unfold parse_memory_type.
  apply source_unary_complete; apply parse_width_limits_complete.
Qed.

Theorem binary_of_table_type_encoding tt :
  table_type_binary_wf tt ->
  table_type_encoding (binary_of_table_type tt) tt.
Proof.
  apply binary_of_table_type_source_encoding.
Qed.

Definition module_table_encoding bytes table :=
  source_prefixed x40 (source_prefixed x00
    (source_binary (fun ty es => Build_module_table ty (Some es))
      table_type_encoding Expression)) bytes table \/
  source_unary (fun ty => Build_module_table ty None) table_type_encoding bytes table.
Definition module_memory_encoding :=
  source_unary Build_module_mem memory_type_encoding.

Theorem parse_module_table_complete n :
  parser_complete (parse_module_table (Toks := SizedList byte) (M := option) (n := n))
    module_table_encoding.
Proof.
  unfold parse_module_table; apply source_alt_complete.
  - apply parser_sound_rand_grammar with
      (P := fun bs b => bs = x40 :: x00 :: nil)
      (Q := source_binary (fun ty es => Build_module_table ty (Some es))
        table_type_encoding Expression).
    + apply parser_sound_prefix_byte with (Q := fun bs b => bs = x00 :: nil /\ b = x00).
      * intros k lt; simpl; apply parser_sound_le_lower; apply parser_sound_exact_byte.
      * intros bs b [Bytes _]; now subst bs.
    + intros k lt; simpl; apply parser_sound_le_lower; apply source_binary_sound.
      * apply parse_table_type_source_sound.
      * apply wasm_production_parse_expr_sound.
    + intros xs ys a b Bytes E; subst xs.
      exists (x00 :: ys); split; [reflexivity|]; exists ys; auto.
  - apply parser_complete_rand_grammar with
      (P := fun bs b => bs = x40 :: x00 :: nil /\ b = x00)
      (Q := source_binary (fun ty es => Build_module_table ty (Some es))
        table_type_encoding Expression).
    + apply parser_complete_prefix_byte with
        (Q := fun bs b => bs = x00 :: nil /\ b = x00).
      * intros k lt; simpl; apply parser_complete_le_lower; apply parser_complete_exact_byte.
      * intros bs b [Bytes Value]; exists (x00 :: nil); auto.
    + intros k lt; simpl; apply parser_complete_le_lower; apply source_binary_complete.
      * apply parse_table_type_complete.
      * apply wasm_production_parse_expr_complete.
    + intros bs b [payload [Bytes [body [Payload Encoding]]]].
      exists (x40 :: x00 :: nil), body, x00.
      subst bs payload; auto.
  - apply source_unary_complete; apply parse_table_type_complete.
  - intros xs ys tail1 tail2 a b [payload [X _]]
      [ty [[refs [lims [reference [widths [Y [R [L V]]]]]]] _]] Same.
    destruct (declaration_reference_head refs reference R)
      as [first [rest [Head Bounds]]].
    subst xs ys refs; simpl in Same; inversion Same; subst first.
    change (N.le 99 64 /\ N.lt 64 123) in Bounds; lia.
Qed.

Theorem parse_module_memory_complete n :
  parser_complete (parse_module_mem (Toks := SizedList byte) (M := option) (n := n))
    module_memory_encoding.
Proof.
  unfold parse_module_mem.
  apply source_unary_complete; apply parse_memory_type_complete.
Qed.

Definition memory_type_binary_wf mt :=
  width_limits_binary_wf mt.(mt_address_type) mt.(mt_limits).

Theorem parse_module_table_sound n :
  parser_sound (parse_module_table (Toks := SizedList byte) (M := option) (n := n))
    module_table_encoding.
Proof.
  unfold parse_module_table; apply parser_sound_alt.
  - eapply parser_sound_weaken with
      (P := source_prefixed x40 (source_prefixed x00
        (source_binary (fun ty es => Build_module_table ty (Some es))
          table_type_encoding Expression))).
    + apply parser_sound_rand_grammar with
        (P := fun bs b => bs = x40 :: x00 :: nil)
        (Q := source_binary (fun ty es => Build_module_table ty (Some es))
          table_type_encoding Expression).
      * apply parser_sound_prefix_byte with
          (Q := fun bs b => bs = x00 :: nil /\ b = x00).
        -- intros k lt; simpl; apply parser_sound_le_lower; apply parser_sound_exact_byte.
        -- intros bs b [Bytes _]; now subst bs.
      * intros k lt; simpl; apply parser_sound_le_lower; apply source_binary_sound.
        -- apply parse_table_type_source_sound.
        -- apply wasm_production_parse_expr_sound.
      * intros xs ys a b Bytes E; subst xs.
        exists (x00 :: ys); split; [reflexivity|]; exists ys; auto.
    + intros bs table E; left; exact E.
  - eapply parser_sound_weaken; [apply source_unary_sound; apply parse_table_type_source_sound|].
    intros bs table E; right; exact E.
Qed.

Definition module_table_binary_wf table :=
  table_type_binary_wf table.(modtab_type) /\
  match table.(modtab_init) with
  | Some es => expression_binary_wf es
  | None => True
  end.

Lemma binary_of_memory_type_encoding mt :
  memory_type_binary_wf mt -> memory_type_encoding (binary_of_memory_type mt) mt.
Proof.
  intro Wf; exists (mt.(mt_address_type), mt.(mt_limits)); split.
  - apply binary_of_width_limits_encoding; exact Wf.
  - destruct mt; reflexivity.
Qed.

Lemma binary_of_module_table_encoding table :
  module_table_binary_wf table -> module_table_encoding (binary_of_module_table table) table.
Proof.
  destruct table as [ty [es|]]; intros [TypeWf Expr].
  - left; exists (x00 :: binary_of_table_type ty ++ binary_of_expr es).
    split; [reflexivity|].
    exists (binary_of_table_type ty ++ binary_of_expr es); split; [reflexivity|].
    exists (binary_of_table_type ty), (binary_of_expr es), ty, es.
    split; [reflexivity|]; split; [now apply binary_of_table_type_encoding|].
    split; [now apply binary_of_expr_encoding|reflexivity].
  - right; exists ty; split; [now apply binary_of_table_type_encoding|reflexivity].
Qed.

Lemma binary_of_module_memory_encoding memory :
  memory_type_binary_wf memory.(modmem_type) ->
  module_memory_encoding (binary_of_module_mem memory) memory.
Proof.
  destruct memory as [mt]; intro Wf; exists mt; split;
    [now apply binary_of_memory_type_encoding|reflexivity].
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
  Forall module_table_binary_wf tables ->
  binary_vector_length_wf tables ->
  binary_vector_length_wf (binary_of_vec binary_of_module_table tables) ->
  table_section_encoding (binary_of_tablesec tables) tables.
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_module_table tables)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size; induction Wf; constructor; [|assumption].
  now apply binary_of_module_table_encoding.
Qed.

Theorem binary_of_memsec_encoding memories :
  Forall (fun m => memory_type_binary_wf m.(modmem_type)) memories ->
  binary_vector_length_wf memories ->
  binary_vector_length_wf (binary_of_vec binary_of_module_mem memories) ->
  memory_section_encoding (binary_of_memsec memories) memories.
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_module_mem memories)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size; induction Wf; constructor; [|assumption].
  now apply binary_of_module_memory_encoding.
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
  Forall module_table_binary_wf tables ->
  binary_vector_length_wf tables ->
  binary_vector_length_wf (binary_of_vec binary_of_module_table tables) ->
  run (binary_of_tablesec tables) (fun _ => parse_tablesec_wrapper) = Some tables.
Proof.
  intros Wf Count Size; apply (run_parser_complete _ table_section_encoding).
  - exact parse_tablesec_wrapper_complete_canonical.
  - now apply binary_of_tablesec_encoding.
Qed.

Corollary binary_of_memsec_wrapper_roundtrip memories :
  Forall (fun m => memory_type_binary_wf m.(modmem_type)) memories ->
  binary_vector_length_wf memories ->
  binary_vector_length_wf (binary_of_vec binary_of_module_mem memories) ->
  run (binary_of_memsec memories) (fun _ => parse_memsec_wrapper) = Some memories.
Proof.
  intros Wf Count Size; apply (run_parser_complete _ memory_section_encoding).
  - exact parse_memsec_wrapper_complete_canonical.
  - now apply binary_of_memsec_encoding.
Qed.
