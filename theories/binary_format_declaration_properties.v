(** Actual recursive declaration groups, not flat function-type sections.
    Source references are the full indexed source codecs. *)
From Stdlib Require Import List Strings.Byte NArith Arith.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer gc_binary
  binary_format_grammar_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_index_lookahead_properties
  binary_format_reference_properties binary_format_vector_properties
  binary_format_control_complete binary_format_atomic_properties leb128_properties
  binary_format_vector_print binary_format_global_properties binary_format_section_properties.
From Wasm Require Import binary_format_printer_properties.
Local Notation byte := Byte.byte.

Definition source_function_encoding :=
  wire_tag x60 (wire_map (uncurry Tf)
    (wire_pair (vector_encoding source_value_encoding) (vector_encoding source_value_encoding))).
Definition source_mutability_encoding :=
  wire_choice (wire_fixed x00 MUT_const) (wire_fixed x01 MUT_var).
Definition source_storage_encoding :=
  wire_choice (wire_fixed x78 (ST_packed PT_i8))
    (wire_choice (wire_fixed x77 (ST_packed PT_i16))
      (wire_map ST_value source_value_encoding)).
Definition source_field_encoding :=
  wire_app
    (wire_map (fun storage mut =>
      {| field_mutability := mut; field_storage := storage |}) source_storage_encoding)
    source_mutability_encoding.
Definition source_composite_encoding :=
  wire_choice (wire_map Comp_func source_function_encoding)
    (wire_choice
      (wire_tag x5f (wire_map Comp_struct (vector_encoding source_field_encoding)))
      (wire_tag x5e (wire_map Comp_array source_field_encoding))).
Definition source_subtype_encoding :=
  wire_choice
    (wire_app (wire_map (Sub_type false) (wire_tag x50 (vector_encoding index_encoding)))
      source_composite_encoding)
    (wire_choice
      (wire_app (wire_map (Sub_type true) (wire_tag x4f (vector_encoding index_encoding)))
        source_composite_encoding)
      (wire_map (Sub_type true nil) source_composite_encoding)).
Definition source_recursive_encoding :=
  wire_choice (wire_tag x4e (vector_encoding source_subtype_encoding))
    (wire_map (fun t => t :: nil) source_subtype_encoding).

Lemma source_value_codec n :
  parser_codec (parse_declaration_value_type (n := n)) source_value_encoding.
Proof. split; [apply parse_declaration_value_sound |apply parse_declaration_value_complete]. Qed.

Lemma source_index_codec n :
  parser_codec (parse_u32_as_N (n := n)) index_encoding.
Proof. split; [apply parse_index_sound |apply parse_u32_prefix_complete]. Qed.

Ltac declaration_initial :=
  lazymatch goal with
  | |- parser_initial_set (Combinators.alt _ _) _ =>
      eapply parser_initial_set_union; [declaration_initial |declaration_initial]
  | |- parser_initial_set (Combinators.map _ _) _ =>
      apply grammar_initial_map; declaration_initial
  | |- parser_initial_set (Combinators.app _ _) _ =>
      eapply parser_initial_exact_set; apply parser_initial_app; control_initial
  | |- parser_initial_set (parse_gc_heap_type) _ => apply parse_gc_heap_initial
  | _ =>
    first
      [eapply parser_initial_exact_set; control_initial
      |progress unfold parse_declaration_value_type; declaration_initial
      |progress unfold parse_number_type; declaration_initial
      |progress unfold parse_vector_type; declaration_initial
      |progress unfold parse_declaration_reference_type; declaration_initial
      |progress unfold parse_declaration_abstract_heap_type; declaration_initial
      |progress unfold parse_function_type; declaration_initial
      |progress unfold parse_storage_type; declaration_initial
      |progress unfold parse_field_type; declaration_initial
      |progress unfold parse_composite_type; declaration_initial
      |progress unfold parse_subtype; declaration_initial
      |progress unfold parse_recursive_type; declaration_initial
      |progress unfold parse_mut; declaration_initial]
  end.

Ltac declaration_disjoint :=
  cbn; intuition (try congruence;
    repeat match goal with
    | H : exists _, _ |- _ => destruct H as [? H]
    | H : abstract_heap_encoding _ _ |- _ => inversion H; subst; clear H
    end; congruence).

Ltac declaration_choice :=
  eapply wire_choice_codec;
    [| |declaration_initial |declaration_initial |declaration_disjoint].

Theorem parse_source_function_codec n :
  parser_codec (parse_function_type (n := n)) source_function_encoding.
Proof.
  unfold parse_function_type, source_function_encoding.
  apply wire_tag_codec; apply wire_map_codec; apply wire_pair_codec.
  all: apply wire_vec_codec; apply source_value_codec.
Qed.

Theorem parse_source_mutability_codec n :
  parser_codec (parse_mut (n := n)) source_mutability_encoding.
Proof.
  unfold parse_mut, source_mutability_encoding.
  declaration_choice; apply wire_fixed_codec.
Qed.

Theorem parse_source_storage_codec n :
  parser_codec (parse_storage_type (n := n)) source_storage_encoding.
Proof.
  unfold parse_storage_type, source_storage_encoding.
  declaration_choice; [apply wire_fixed_codec |].
  declaration_choice; [apply wire_fixed_codec |].
  apply wire_map_codec; apply source_value_codec.
Qed.

Theorem parse_source_field_codec n :
  parser_codec (parse_field_type (n := n)) source_field_encoding.
Proof.
  unfold parse_field_type, source_field_encoding.
  apply wire_app_codec; [apply wire_map_codec; apply parse_source_storage_codec
    |apply parse_source_mutability_codec].
Qed.

Theorem parse_source_composite_codec n :
  parser_codec (parse_composite_type (n := n)) source_composite_encoding.
Proof.
  unfold parse_composite_type, source_composite_encoding.
  declaration_choice.
  - apply wire_map_codec; apply parse_source_function_codec.
  - declaration_choice; apply wire_tag_codec; apply wire_map_codec.
    + apply wire_vec_codec; apply parse_source_field_codec.
    + apply parse_source_field_codec.
Qed.

Theorem parse_source_subtype_codec n :
  parser_codec (parse_subtype (n := n)) source_subtype_encoding.
Proof.
  unfold parse_subtype, source_subtype_encoding.
  declaration_choice.
  - apply wire_app_codec; [apply wire_map_codec; apply wire_tag_codec;
      apply wire_vec_codec; apply source_index_codec |apply parse_source_composite_codec].
  - declaration_choice.
    + apply wire_app_codec; [apply wire_map_codec; apply wire_tag_codec;
        apply wire_vec_codec; apply source_index_codec |apply parse_source_composite_codec].
    + apply wire_map_codec; apply parse_source_composite_codec.
Qed.

Theorem parse_source_recursive_codec n :
  parser_codec (parse_recursive_type (n := n)) source_recursive_encoding.
Proof.
  unfold parse_recursive_type, source_recursive_encoding.
  declaration_choice.
  - apply wire_tag_codec; apply wire_vec_codec; apply parse_source_subtype_codec.
  - apply wire_map_codec; apply parse_source_subtype_codec.
Qed.

Theorem run_parse_recursive_type_correct bytes group :
  run bytes (fun n => parse_recursive_type (n := n)) = Some group <->
  source_recursive_encoding bytes group.
Proof.
  split.
  - apply run_parser_sound; intros n; exact (proj1 (parse_source_recursive_codec n)).
  - apply run_parser_complete; intros n; exact (proj2 (parse_source_recursive_codec n)).
Qed.

Theorem parse_recursive_type_prefix_correct bytes group rest :
  run_parse_prefix (fun n => parse_recursive_type (n := n)) bytes = Some (group, rest) <->
  exists prefix, bytes = prefix ++ rest /\ source_recursive_encoding prefix group.
Proof.
  split.
  - apply run_parse_prefix_sound; intros n; exact (proj1 (parse_source_recursive_codec n)).
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (proj2 (parse_source_recursive_codec (length (prefix ++ rest))) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest group Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (group, rest)).
    now rewrite Value, Rest.
Qed.

Definition source_function_binary_wf ft :=
  match ft with Tf ins outs =>
    Forall source_value_binary_wf ins /\ Forall source_value_binary_wf outs /\
    binary_vector_length_wf ins /\ binary_vector_length_wf outs
  end.
Definition source_storage_binary_wf storage :=
  match storage with ST_value t => source_value_binary_wf t | ST_packed _ => True end.
Definition source_field_binary_wf field := source_storage_binary_wf field.(field_storage).
Definition source_composite_binary_wf comp :=
  match comp with
  | Comp_func ft => source_function_binary_wf ft
  | Comp_struct fields => Forall source_field_binary_wf fields /\ binary_vector_length_wf fields
  | Comp_array field => source_field_binary_wf field
  end.
Definition source_subtype_binary_wf t :=
  Forall binary_index_wf t.(subtype_supers) /\
  binary_vector_length_wf t.(subtype_supers) /\
  source_composite_binary_wf t.(subtype_composite).
Definition source_recursive_binary_wf group :=
  Forall source_subtype_binary_wf group /\ binary_vector_length_wf group.

Lemma source_values_printer_membership ts :
  Forall source_value_binary_wf ts -> binary_vector_length_wf ts ->
  vector_encoding source_value_encoding (binary_of_result_type ts) ts.
Proof.
  intros Values Count; apply binary_of_vec_encoding; [|exact Count].
  clear Count.
  induction Values; constructor; [now apply source_value_printer_membership |assumption].
Qed.

Theorem source_function_printer_membership ft :
  source_function_binary_wf ft -> source_function_encoding (binary_of_functype ft) ft.
Proof.
  destruct ft as [ins outs]; intros [Ins [Outs [InsCount OutsCount]]].
  exists (binary_of_result_type ins ++ binary_of_result_type outs); split; [reflexivity |].
  exists (ins, outs); split; [|reflexivity].
  exists (binary_of_result_type ins), (binary_of_result_type outs).
  split; [reflexivity |split; now apply source_values_printer_membership].
Qed.

Theorem source_storage_printer_membership storage :
  source_storage_binary_wf storage ->
  source_storage_encoding (binary_of_storage_type storage) storage.
Proof.
  destruct storage as [value|packed]; intro Wf.
  - right; right; exists value; split; [now apply source_value_printer_membership |reflexivity].
  - destruct packed; [left |right; left]; split; reflexivity.
Qed.

Theorem source_field_printer_membership field :
  source_field_binary_wf field ->
  source_field_encoding (binary_of_field_type field) field.
Proof.
  destruct field as [mut storage]; intro Wf.
  exists (binary_of_storage_type storage),
    ((match mut with MUT_const => x00 | MUT_var => x01 end) :: nil),
    (fun m => {| field_mutability := m; field_storage := storage |}), mut.
  split; [reflexivity |]. split.
  - exists storage; split; [now apply source_storage_printer_membership |reflexivity].
  - split; [destruct mut; [left |right]; split; reflexivity |reflexivity].
Qed.

Theorem source_composite_printer_membership comp :
  source_composite_binary_wf comp ->
  source_composite_encoding (binary_of_composite_type comp) comp.
Proof.
  destruct comp as [ft|fields|field]; intro Wf.
  - left; exists ft; split; [now apply source_function_printer_membership |reflexivity].
  - right; left; exists (binary_of_vec binary_of_field_type fields); split; [reflexivity |].
    exists fields; split; [|reflexivity].
    destruct Wf as [Fields Count]; apply binary_of_vec_encoding; [|exact Count].
    clear Count.
    induction Fields; constructor; [now apply source_field_printer_membership |assumption].
  - right; right; exists (binary_of_field_type field); split; [reflexivity |].
    exists field; split; [now apply source_field_printer_membership |reflexivity].
Qed.

Theorem source_subtype_printer_membership t :
  source_subtype_binary_wf t ->
  source_subtype_encoding (binary_of_subtype t) t.
Proof.
  destruct t as [final supers comp]; intros [Supers [Count Comp]].
  cbn in Supers, Count, Comp.
  assert (Indices : vector_encoding index_encoding (binary_of_vec binary_of_typeidx supers) supers).
  { apply binary_of_vec_encoding; [|exact Count].
    clear Count.
    induction Supers; constructor; [now apply binary_of_index_encoding |assumption]. }
  assert (Composite : source_composite_encoding (binary_of_composite_type comp) comp)
    by now apply source_composite_printer_membership.
  destruct final.
  - destruct supers as [|super supers].
    + right; right; exists comp; auto.
    + right; left.
      exists (x4f :: binary_of_vec binary_of_typeidx (super :: supers)),
        (binary_of_composite_type comp), (Sub_type true (super :: supers)), comp.
      split; [reflexivity |]. split.
      * exists (super :: supers); split; [|reflexivity].
        exists (binary_of_vec binary_of_typeidx (super :: supers)); auto.
      * auto.
  - left.
    exists (x50 :: binary_of_vec binary_of_typeidx supers),
      (binary_of_composite_type comp), (Sub_type false supers), comp.
    split; [reflexivity |]. split.
    + exists supers; split; [|reflexivity].
      exists (binary_of_vec binary_of_typeidx supers); auto.
    + auto.
Qed.

Theorem source_recursive_printer_membership group :
  source_recursive_binary_wf group ->
  source_recursive_encoding (binary_of_recursive_type group) group.
Proof.
  intros [Groups Count].
  assert (Vector : vector_encoding source_subtype_encoding (binary_of_vec binary_of_subtype group) group).
  { apply binary_of_vec_encoding; [|exact Count].
    clear Count.
    induction Groups; constructor; [now apply source_subtype_printer_membership |assumption]. }
  destruct group as [|t [|u rest]].
  - left; exists (binary_of_vec binary_of_subtype nil); auto.
  - right; exists t; split; [|reflexivity].
    inversion Groups; subst; now apply source_subtype_printer_membership.
  - left; exists (binary_of_vec binary_of_subtype (t :: u :: rest)); auto.
Qed.

Corollary source_recursive_printer_roundtrip group :
  source_recursive_binary_wf group ->
  run (binary_of_recursive_type group) (fun n => parse_recursive_type (n := n)) = Some group.
Proof.
  intro Wf; apply run_parse_recursive_type_correct; now apply source_recursive_printer_membership.
Qed.

Definition source_type_section_encoding :=
  wire_tag x01 (section_payload_encoding (vector_encoding source_recursive_encoding)).

Theorem parse_source_type_section_codec n :
  parser_codec (parse_typesec (n := n)) source_type_section_encoding.
Proof.
  unfold parse_typesec, source_type_section_encoding; apply wire_tag_codec; split.
  - apply parse_section_payload_sound; apply parse_vec_sound.
    exact (proj1 (parse_source_recursive_codec n)).
  - apply parse_section_payload_complete; apply parse_vec_complete.
    exact (proj2 (parse_source_recursive_codec n)).
Qed.

Definition source_type_section_binary_wf groups :=
  Forall source_recursive_binary_wf groups /\ binary_vector_length_wf groups /\
  binary_vector_length_wf (binary_of_vec binary_of_recursive_type groups).

Theorem source_type_section_printer_membership groups :
  source_type_section_binary_wf groups ->
  source_type_section_encoding (binary_of_typesec groups) groups.
Proof.
  intros [Groups [Count Size]].
  exists (with_length (binary_of_vec binary_of_recursive_type groups)); split; [reflexivity |].
  exists (binary_of_u32 (N.of_nat (length (binary_of_vec binary_of_recursive_type groups)))),
    (binary_of_vec binary_of_recursive_type groups).
  split; [unfold with_length, binary_of_u32, binary_of_N; now rewrite printer_bin_of_nat |].
  destruct (binary_of_index_encoding _ Size) as [Header [Range Width]].
  split; [exact Header |]. split; [exact Range |]. split; [exact Width |].
  apply binary_of_vec_encoding; [|exact Count].
  clear Count Size Header Range Width.
  induction Groups; constructor; [now apply source_recursive_printer_membership |assumption].
Qed.

Corollary source_type_section_printer_roundtrip groups :
  source_type_section_binary_wf groups ->
  run (binary_of_typesec groups) (fun n => parse_typesec (n := n)) = Some groups.
Proof.
  intro Wf; apply (run_parser_complete _ source_type_section_encoding).
  - intros n; exact (proj2 (parse_source_type_section_codec n)).
  - now apply source_type_section_printer_membership.
Qed.
