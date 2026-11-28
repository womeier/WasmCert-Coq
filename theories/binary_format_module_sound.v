(** Soundness for arbitrary accepted production module bytes, not only the
    printer image. Noncanonical integer headers and custom bytes are kept. *)
From Stdlib Require Import List Strings.Byte NArith Arith Sorting.Sorted.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_format_parser_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_block_properties binary_format_type_properties
  binary_format_dispatch_properties binary_format_vector_properties
  binary_format_function_properties binary_format_limits_properties
  binary_format_global_properties binary_format_code_properties
  binary_format_section_properties binary_format_custom_properties
  binary_format_optional_properties binary_format_segment_properties
  binary_format_module_properties binary_format_module_grammar.
Local Notation byte := Byte.byte.
From Wasm Require Import binary_format_table_type_properties
  binary_format_declaration_properties binary_format_width_properties.

Lemma parse_limits_general_sound n :
  parser_sound (parse_limits (Toks := SizedList byte) (M := option) (n := n)) limits_encoding.
Proof.
  unfold parse_limits; apply parser_sound_alt.
  - eapply parser_sound_weaken.
    + apply grammar_sound_tag; apply grammar_sound_map; apply parse_index_sound.
    + intros bytes lim [body [Bytes [min [Index Value]]]]; subst lim.
      exists body; auto.
  - eapply parser_sound_weaken.
    + apply grammar_sound_app; [apply grammar_sound_tag; apply grammar_sound_map |];
        apply parse_index_sound.
    + intros bytes lim [first [upper [f [max [Bytes [[minimum [First [min [Index Value]]]] [Max Result]]]]]]].
      subst f lim first.
      exists minimum, upper; auto.
Qed.

Lemma parse_table_type_general_sound n :
  parser_sound (parse_table_type (Toks := SizedList byte) (M := option) (n := n))
    table_type_encoding.
Proof.
  apply parse_table_type_source_sound.
Qed.

Lemma parse_memory_type_general_sound n :
  parser_sound (parse_memory_type (Toks := SizedList byte) (M := option) (n := n))
    memory_type_encoding.
Proof.
  unfold parse_memory_type; apply source_unary_sound; apply parse_width_limits_sound.
Qed.

Lemma parse_module_table_general_sound n :
  parser_sound (parse_module_table (Toks := SizedList byte) (M := option) (n := n))
    module_table_encoding.
Proof.
  apply parse_module_table_sound.
Qed.

Lemma parse_module_memory_general_sound n :
  parser_sound (parse_module_mem (Toks := SizedList byte) (M := option) (n := n))
    module_memory_encoding.
Proof.
  unfold parse_module_mem; apply source_unary_sound; apply parse_memory_type_general_sound.
Qed.

Lemma parse_elemkind_general_sound n :
  parser_sound (parse_elemkind (Toks := SizedList byte) (M := option) (n := n))
    elemkind_encoding.
Proof.
  unfold parse_elemkind; eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  intros bytes b [Bytes _]; split; [exact Bytes |reflexivity].
Qed.

Ltac module_grammar_parser_head term :=
  lazymatch term with ?f ?arg => module_grammar_parser_head f | _ => term end.

Ltac module_leaf_sound :=
  lazymatch goal with
  | |- parser_sound ?p _ =>
    let head := module_grammar_parser_head p in
    first
      [constr_eq head (@parse_expr); apply wasm_production_parse_expr_sound
       |constr_eq head (@parse_declaration_reference_type); apply parse_declaration_reference_sound
      |constr_eq head (@parse_elemkind); apply parse_elemkind_general_sound
      |constr_eq head (@parse_name); apply parse_name_sound
      |constr_eq head (@parse_table_type); apply parse_table_type_general_sound
      |constr_eq head (@parse_memory_type); apply parse_memory_type_general_sound
      |constr_eq head (@parse_global_type); apply parse_global_type_sound
       |constr_eq head (@parse_recursive_type); apply parse_recursive_type_source_sound
      |constr_eq head (@parse_module_table); apply parse_module_table_general_sound
      |constr_eq head (@parse_module_mem); apply parse_module_memory_general_sound
      |constr_eq head (@parse_module_global); apply parse_module_global_sound
      |constr_eq head (@parse_code); apply parse_code_sound
      |constr_eq head (@parse_u32_as_N); apply parse_index_sound
      |constr_eq head (@parse_typeidx); apply parse_index_sound
      |constr_eq head (@parse_funcidx); apply parse_index_sound
      |constr_eq head (@parse_tableidx); apply parse_index_sound
      |constr_eq head (@parse_memidx); apply parse_index_sound
      |constr_eq head (@parse_globalidx); apply parse_index_sound
      |constr_eq head (@anyTok); apply parser_sound_anyTok
      |lazymatch p with
       | Combinators.map _ _ => apply grammar_sound_map; module_leaf_sound
       | Combinators.app _ _ => apply grammar_sound_app; [module_leaf_sound |module_leaf_sound]
       | Combinators.and _ _ => apply grammar_sound_sequence; [module_leaf_sound |module_leaf_sound]
       | Combinators.alt _ _ => apply grammar_sound_choice; [module_leaf_sound |module_leaf_sound]
       | Combinators.rand (exact_byte _) _ => apply grammar_sound_tag; module_leaf_sound
       | Combinators.rand (assert_u32 _) _ => apply grammar_sound_subopcode; module_leaf_sound
       | parse_vec _ => apply parse_vec_sound; module_leaf_sound
       end]
  end.

Theorem parse_import_descriptor_general_sound n :
  parser_sound (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
    import_descriptor_encoding.
Proof.
  unfold parse_import_desc, import_descriptor_encoding; module_leaf_sound.
Qed.

Theorem parse_import_general_sound n :
  parser_sound (parse_module_import (Toks := SizedList byte) (M := option) (n := n))
    module_import_encoding.
Proof.
  unfold parse_module_import, module_import_encoding.
  apply grammar_sound_map; apply grammar_sound_sequence.
  - apply grammar_sound_sequence; apply parse_name_sound.
  - apply parse_import_descriptor_general_sound.
Qed.

Theorem parse_export_descriptor_general_sound n :
  parser_sound (parse_module_export_desc (Toks := SizedList byte) (M := option) (n := n))
    export_descriptor_encoding.
Proof.
  unfold parse_module_export_desc, export_descriptor_encoding; module_leaf_sound.
Qed.

Theorem parse_export_general_sound n :
  parser_sound (parse_module_export (Toks := SizedList byte) (M := option) (n := n))
    module_export_encoding.
Proof.
  unfold parse_module_export, module_export_encoding.
  apply grammar_sound_app.
  - apply grammar_sound_map; apply parse_name_sound.
  - apply parse_export_descriptor_general_sound.
Qed.

Theorem parse_start_general_sound n :
  parser_sound (parse_module_start (Toks := SizedList byte) (M := option) (n := n))
    module_start_encoding.
Proof.
  unfold parse_module_start, module_start_encoding; module_leaf_sound.
Qed.

Theorem parse_element_general_sound n :
  parser_sound (parse_module_element (Toks := SizedList byte) (M := option) (n := n))
    module_element_encoding.
Proof.
  unfold parse_module_element, module_element_encoding,
    parse_module_element_0, parse_module_element_1, parse_module_element_2, parse_module_element_3,
    parse_module_element_4, parse_module_element_5, parse_module_element_6, parse_module_element_7,
    element0_encoding, element1_encoding, element2_encoding, element3_encoding,
    element4_encoding, element5_encoding, element6_encoding, element7_encoding;
    module_leaf_sound.
Qed.

Theorem parse_data_general_sound n :
  parser_sound (parse_module_data (Toks := SizedList byte) (M := option) (n := n))
    module_data_encoding.
Proof.
  unfold parse_module_data, module_data_encoding,
    parse_module_data_0, parse_module_data_1, parse_module_data_2,
    data0_encoding, data1_encoding, data2_encoding;
    module_leaf_sound.
Qed.

Lemma known_bytes_sound_rand {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) xs ys a b :
  parser_sound p (fun bytes value => bytes = xs /\ value = a) ->
  parser_sound q (fun bytes value => bytes = ys /\ value = b) ->
  parser_sound (Combinators.rand p (box q)) (fun bytes value => bytes = xs ++ ys /\ value = b).
Proof.
  intros P Q; apply parser_sound_rand_grammar with
    (P := fun bytes value => bytes = xs /\ value = a)
    (Q := fun bytes value => bytes = ys /\ value = b).
  - exact P.
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros first second av bv [First _] [Second Value]; subst first second; auto.
Qed.

Lemma module_header_general_sound n :
  parser_sound
    (Combinators.rand (parse_magic (Toks := SizedList byte) (M := option) (n := n))
      (box parse_version))
    (fun bytes (_ : unit) => bytes = magic ++ version).
Proof.
  assert (Magic : parser_sound (parse_magic (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes (_ : unit) => bytes = magic)).
  { pose proof (known_bytes_sound_rand _ _ _ _ x00 x61
      (parser_sound_exact_byte x00 n) (parser_sound_exact_byte x61 n)) as First.
    pose proof (known_bytes_sound_rand _ _ _ _ x61 x73 First (parser_sound_exact_byte x73 n)) as Second.
    pose proof (known_bytes_sound_rand _ _ _ _ x73 x6d Second (parser_sound_exact_byte x6d n)) as Third.
    unfold parse_magic; eapply parser_sound_cmap; [exact Third |].
    intros bytes value [Bytes _]; exact Bytes. }
  assert (Version : parser_sound (parse_version (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes (_ : unit) => bytes = version)).
  { pose proof (known_bytes_sound_rand _ _ _ _ x01 x00
      (parser_sound_exact_byte x01 n) (parser_sound_exact_byte x00 n)) as First.
    pose proof (known_bytes_sound_rand _ _ _ _ x00 x00 First (parser_sound_exact_byte x00 n)) as Second.
    pose proof (known_bytes_sound_rand _ _ _ _ x00 x00 Second (parser_sound_exact_byte x00 n)) as Third.
    unfold parse_version; eapply parser_sound_cmap; [exact Third |].
    intros bytes value [Bytes _]; exact Bytes. }
  apply parser_sound_rand_grammar with
    (P := fun bytes (_ : unit) => bytes = magic)
    (Q := fun bytes (_ : unit) => bytes = version).
  - exact Magic.
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros first second a b First Second; now subst first second.
Qed.

Ltac module_section_sound :=
  unfold parse_typesec_wrapper, parse_importsec_wrapper, parse_funcsec_wrapper,
    parse_tablesec_wrapper, parse_memsec_wrapper, parse_globalsec_wrapper,
    parse_exportsec_wrapper, parse_startsec_wrapper, parse_elemsec_wrapper,
    parse_datacountsec_wrapper, parse_codesec_wrapper, parse_datasec_wrapper;
  apply parse_with_customsec_star_before_sound;
  unfold ordinary_section_encoding;
  unfold parse_typesec, parse_importsec, parse_funcsec, parse_tablesec,
    parse_memsec, parse_globalsec, parse_exportsec, parse_startsec,
    parse_elemsec, parse_datacountsec, parse_codesec, parse_datasec;
  apply grammar_sound_tag; apply parse_section_payload_sound;
  first [apply parse_vec_sound;
    first [apply parse_recursive_type_source_sound |apply parse_import_general_sound
      |apply parse_index_sound |apply parse_module_table_general_sound
      |apply parse_module_memory_general_sound |apply parse_module_global_sound
      |apply parse_export_general_sound |apply parse_element_general_sound
      |apply parse_code_sound |apply parse_data_general_sound]
    |apply parse_start_general_sound |apply parse_index_sound].

Theorem production_module_sections_general_sound n :
  parser_sound
    (parse_module_section_sequence_after
      (Combinators.rand (parse_magic (Toks := SizedList byte) (M := option) (n := n))
        (box parse_version)))
    module_sections_encoding.
Proof.
  unfold parse_module_section_sequence_after, module_sections_encoding, after_custom_encoding.
  apply parse_with_customsec_star_after_sound.
  repeat (apply grammar_sound_optional; [|solve [module_section_sound]]).
  apply module_header_general_sound.
Qed.

Lemma finish_module_sections_erasure sections modul :
  finish_module_sections sections = Some modul ->
  module_sections_erasure sections modul.
Proof.
  destruct sections as [[[[[[[[[[[[initial types] imports] fts] tables] memories]
    globals] exports] start] elems] count] codes] data].
  unfold finish_module_sections, module_sections_erasure.
  destruct (Nat.eqb (length (option_to_list fts)) (length (option_to_list codes)))
    eqn:Lengths; [|discriminate].
  destruct (datacount_agree (N.of_nat (length (option_to_list data))) count)
    eqn:DataCount; [|discriminate].
  destruct (datacount_presence_agree (option_to_list codes) count)
    eqn:Presence; [|discriminate].
  intro Parsed; inversion Parsed; subst modul.
  split; [now apply Nat.eqb_eq |].
  split.
  - destruct count as [n|]; [now apply N.eqb_eq |exact I].
  - split; [|reflexivity].
    intro NoneCount; subst count.
    unfold datacount_presence_agree in Presence.
    destruct (codes_datacount_required (option_to_list codes)); [discriminate |reflexivity].
Qed.

Lemma module_sections_erasure_finish sections modul :
  module_sections_erasure sections modul ->
  finish_module_sections sections = Some modul.
Proof.
  destruct sections as [[[[[[[[[[[[initial types] imports] fts] tables] memories]
    globals] exports] start] elems] count] codes] data].
  unfold module_sections_erasure, finish_module_sections.
  intros [Lengths [Count [Presence Result]]].
  rewrite (proj2 (Nat.eqb_eq _ _) Lengths).
  assert (Agree : datacount_agree (N.of_nat (length (option_to_list data))) count = true).
  { destruct count; [now apply N.eqb_eq |reflexivity]. }
  assert (Present : datacount_presence_agree (option_to_list codes) count = true).
  { destruct count; [reflexivity |].
    unfold datacount_presence_agree; rewrite (Presence Logic.eq_refl); reflexivity. }
  rewrite Agree, Present; now subst modul.
Qed.

Theorem production_parse_module_general_sound n :
  parser_sound (parse_module (Toks := SizedList byte) (M := option) (n := n))
    module_binary_encoding.
Proof.
  unfold parse_module, parse_module_sections_after.
  eapply parser_sound_guardM with (P := module_sections_encoding).
  - apply production_module_sections_general_sound.
  - intros bytes sections modul Encoding Parsed.
    exists sections; split; [exact Encoding |now apply finish_module_sections_erasure].
Qed.

Theorem run_parse_module_general_sound bytes modul :
  run_parse_module bytes = Some modul -> module_binary_encoding bytes modul.
Proof.
  unfold run_parse_module; apply run_parser_sound.
  exact production_parse_module_general_sound.
Qed.

Theorem run_parse_module_str_general_sound source modul :
  run_parse_module_str source = Some modul ->
  module_binary_encoding (String.list_byte_of_string source) modul.
Proof. unfold run_parse_module_str; apply run_parse_module_general_sound. Qed.

Corollary run_parse_module_general_invariants bytes modul :
  run_parse_module bytes = Some modul ->
  exists sections,
    module_sections_encoding bytes sections /\
    module_sections_erasure sections modul /\
    NoDup (module_section_trace sections) /\
    StronglySorted (fun first second =>
      module_section_rank first < module_section_rank second)
      (module_section_trace sections).
Proof.
  intro Parsed; destruct (run_parse_module_general_sound bytes modul Parsed)
    as [sections [Encoding Erasure]].
  exists sections; split; [exact Encoding |].
  split; [exact Erasure |].
  split; [apply module_section_trace_unique |apply module_section_trace_ordered].
Qed.
