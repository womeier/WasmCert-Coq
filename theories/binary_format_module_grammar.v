(** Independent consumed-byte module grammar. Semantic actions construct
    source AST fields only; no grammar production mentions parser execution. *)
From Stdlib Require Import List Strings.Byte NArith Arith Sorting.Sorted Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes bytes operations
  binary_format_parser binary_format_printer binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_block_properties binary_format_reference_properties binary_format_eh_properties
  binary_format_dispatch_properties binary_format_vector_properties
  binary_format_declaration_properties binary_format_limits_properties
  binary_format_global_properties binary_format_global_section_properties binary_format_code_properties
  binary_format_section_properties binary_format_custom_properties
  binary_format_optional_properties binary_format_segment_properties
  binary_format_module_properties.
Local Notation byte := Byte.byte.
Local Notation Expression := (expression_encoding wasm_atomic_encoding block_type_encoding).

Definition mapped_encoding {A B} (f : A -> B) (P : list byte -> A -> Prop) bytes value :=
  exists a, P bytes a /\ value = f a.
Definition sequence_encoding {A B} (P : list byte -> A -> Prop)
    (Q : list byte -> B -> Prop) bytes (value : A * B) :=
  exists xs ys, bytes = xs ++ ys /\ P xs (fst value) /\ Q ys (snd value).
Definition application_encoding {A B} (P : list byte -> (A -> B) -> Prop)
    (Q : list byte -> A -> Prop) bytes value :=
  exists xs ys f a, bytes = xs ++ ys /\ P xs f /\ Q ys a /\ value = f a.
Definition tagged_encoding {A} tag (P : list byte -> A -> Prop) bytes value :=
  exists body, bytes = tag :: body /\ P body value.
Definition optional_sequence_encoding {A B} (P : list byte -> A -> Prop)
    (Q : list byte -> B -> Prop) bytes (value : A * option B) :=
  exists xs ys, bytes = xs ++ ys /\ P xs (fst value) /\ optional_encoding Q ys (snd value).
Definition after_custom_encoding {A} (P : list byte -> A -> Prop) bytes value :=
  exists prefix suffix, bytes = prefix ++ suffix /\ P prefix value /\
    custom_repetitions custom_bytes suffix.

Lemma grammar_sound_map {A B n} (f : A -> B)
    (p : Parser (SizedList byte) byte option A n) P :
  parser_sound p P -> parser_sound (Combinators.map f p) (mapped_encoding f P).
Proof.
  intro Sound; eapply parser_sound_map; [exact Sound |].
  intros bytes value E; exists value; auto.
Qed.

Lemma grammar_sound_app {A B n}
    (p : Parser (SizedList byte) byte option (A -> B) n)
    (q : Parser (SizedList byte) byte option A n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound (Combinators.app p (box q)) (application_encoding P Q).
Proof.
  intros Pp Qq; eapply parser_sound_app with (P := P) (Q := Q); [exact Pp | |].
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros xs ys f a Pf Qa; exists xs, ys, f, a; auto.
Qed.

Lemma grammar_sound_sequence {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound (Combinators.and p (box q)) (sequence_encoding P Q).
Proof.
  intros Pp Qq; unfold Combinators.and.
  eapply parser_sound_andbind with (P := P) (Q := fun _ => Q); [exact Pp | |].
  - intros a k lt; simpl; now apply parser_sound_le_lower.
  - intros xs ys a b Pa Qb; exists xs, ys; auto.
Qed.

Lemma grammar_sound_tag {A n} tag
    (p : Parser (SizedList byte) byte option A n) P :
  parser_sound p P ->
  parser_sound (Combinators.rand (exact_byte tag) (box p)) (tagged_encoding tag P).
Proof.
  intro Sound; apply parser_sound_prefix_byte with (Q := P).
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros bytes value E; exists bytes; auto.
Qed.

Lemma grammar_sound_subopcode {A n} code
    (p : Parser (SizedList byte) byte option A n) P :
  parser_sound p P ->
  parser_sound (Combinators.rand (assert_u32 code) (box p)) (subopcode_encoding code P).
Proof.
  intro Sound; apply parser_sound_rand_grammar with
    (P := fun bytes value => index_encoding bytes code /\ value = code) (Q := P).
  - apply assert_u32_sound.
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros header body code' value [E _] B; exists header, body; auto.
Qed.

Lemma grammar_sound_choice {A n}
    (p q : Parser (SizedList byte) byte option A n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound (Combinators.alt p q) (fun bytes value => P bytes value \/ Q bytes value).
Proof.
  intros Pp Qq; apply parser_sound_alt.
  - eapply parser_sound_weaken; [exact Pp |]; intros bytes value E; now left.
  - eapply parser_sound_weaken; [exact Qq |]; intros bytes value E; now right.
Qed.

Lemma grammar_sound_optional {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound (Combinators.andm p (box q)) (optional_sequence_encoding P Q).
Proof.
  intros Pp Qq; apply parser_sound_andm with (P := P) (Q := Q); [exact Pp | |].
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros xs ys a b Pa Qb; exists xs, ys; auto.
Qed.

Definition reference_encoding := source_reference_encoding.
Definition mutability_encoding bytes mut := bytes = binary_of_mutability mut.
Definition elemkind_encoding bytes rt := bytes = x00 :: nil /\ rt = T_funcref.

Definition import_descriptor_encoding :=
  fun bytes desc =>
    tagged_encoding x00 (mapped_encoding MID_func index_encoding) bytes desc \/
    tagged_encoding x01 (mapped_encoding MID_table table_type_encoding) bytes desc \/
    tagged_encoding x02 (mapped_encoding MID_mem limits_encoding) bytes desc \/
    tagged_encoding x03 (mapped_encoding MID_global global_type_encoding) bytes desc \/
    tagged_encoding x04 (tagged_encoding x00 (mapped_encoding MID_tag index_encoding)) bytes desc.
Definition module_import_encoding :=
  mapped_encoding (fun '(modul, name, desc) => Build_module_import modul name desc)
    (sequence_encoding (sequence_encoding name_encoding name_encoding) import_descriptor_encoding).
Definition export_descriptor_encoding :=
  fun bytes desc =>
    tagged_encoding x00 (mapped_encoding MED_func index_encoding) bytes desc \/
    tagged_encoding x01 (mapped_encoding MED_table index_encoding) bytes desc \/
    tagged_encoding x02 (mapped_encoding MED_mem index_encoding) bytes desc \/
    tagged_encoding x03 (mapped_encoding MED_global index_encoding) bytes desc \/
    tagged_encoding x04 (mapped_encoding MED_tag index_encoding) bytes desc.
Definition module_export_encoding :=
  application_encoding (mapped_encoding Build_module_export name_encoding) export_descriptor_encoding.
Definition module_start_encoding := mapped_encoding Build_module_start index_encoding.

Definition element_indices_encoding := vector_encoding index_encoding.
Definition element_expressions_encoding := vector_encoding Expression.
Definition element_legacy_initializers indices :=
  List.map (fun index => BI_ref_func index :: nil) indices.

Definition element0_encoding :=
  application_encoding
    (mapped_encoding (fun es indices => Build_module_element T_funcref
      (element_legacy_initializers indices) (ME_active 0%N es)) Expression)
    element_indices_encoding.
Definition element1_encoding :=
  application_encoding
    (mapped_encoding (fun rt indices => Build_module_element rt
      (element_legacy_initializers indices) ME_passive) elemkind_encoding)
    element_indices_encoding.
Definition element2_encoding :=
  application_encoding (application_encoding (application_encoding
    (mapped_encoding (fun index es rt indices => Build_module_element rt
      (element_legacy_initializers indices) (ME_active index es)) index_encoding)
      Expression) elemkind_encoding) element_indices_encoding.
Definition element3_encoding :=
  application_encoding
    (mapped_encoding (fun rt indices => Build_module_element rt
      (element_legacy_initializers indices) ME_declarative) elemkind_encoding)
    element_indices_encoding.
Definition element4_encoding :=
  application_encoding
    (mapped_encoding (fun es inits => Build_module_element T_funcref inits (ME_active 0%N es))
      Expression) element_expressions_encoding.
Definition element5_encoding :=
  application_encoding
    (mapped_encoding (fun rt inits => Build_module_element rt inits ME_passive)
      reference_encoding) element_expressions_encoding.
Definition element6_encoding :=
  application_encoding (application_encoding (application_encoding
    (mapped_encoding (fun index es rt inits => Build_module_element rt inits (ME_active index es))
      index_encoding) Expression) reference_encoding) element_expressions_encoding.
Definition element7_encoding :=
  application_encoding
    (mapped_encoding (fun rt inits => Build_module_element rt inits ME_declarative)
      reference_encoding) element_expressions_encoding.

Definition module_element_encoding bytes elem :=
  subopcode_encoding 0%N element0_encoding bytes elem \/
  subopcode_encoding 1%N element1_encoding bytes elem \/
  subopcode_encoding 2%N element2_encoding bytes elem \/
  subopcode_encoding 3%N element3_encoding bytes elem \/
  subopcode_encoding 4%N element4_encoding bytes elem \/
  subopcode_encoding 5%N element5_encoding bytes elem \/
  subopcode_encoding 6%N element6_encoding bytes elem \/
  subopcode_encoding 7%N element7_encoding bytes elem.

Definition data0_encoding :=
  application_encoding
    (mapped_encoding (fun es raw => Build_module_data (List.map compcert_byte_of_byte raw)
      (MD_active 0%N es)) Expression) raw_vector_encoding.
Definition data1_encoding :=
  mapped_encoding (fun raw => Build_module_data (List.map compcert_byte_of_byte raw) MD_passive)
    raw_vector_encoding.
Definition data2_encoding :=
  application_encoding (application_encoding
    (mapped_encoding (fun index es raw => Build_module_data (List.map compcert_byte_of_byte raw)
      (MD_active index es)) index_encoding) Expression) raw_vector_encoding.
Definition module_data_encoding bytes data :=
  subopcode_encoding 0%N data0_encoding bytes data \/
  subopcode_encoding 1%N data1_encoding bytes data \/
  subopcode_encoding 2%N data2_encoding bytes data.

Definition ordinary_section_encoding {A} tag (P : list byte -> A -> Prop) :=
  tagged_encoding tag (section_payload_encoding P).
Definition section_with_custom_encoding {A} tag (P : list byte -> A -> Prop) :=
  custom_before_encoding custom_bytes (ordinary_section_encoding tag P).

Definition module_sections_encoding : list byte -> module_section_results unit -> Prop :=
  let header := fun bytes (_ : unit) => bytes = magic ++ version in
  let types := optional_sequence_encoding header
    (section_with_custom_encoding x01 (vector_encoding source_recursive_encoding)) in
  let imports := optional_sequence_encoding types
    (section_with_custom_encoding x02 (vector_encoding module_import_encoding)) in
  let functions := optional_sequence_encoding imports
    (section_with_custom_encoding x03 (vector_encoding index_encoding)) in
  let tables := optional_sequence_encoding functions
    (section_with_custom_encoding x04 (vector_encoding module_table_encoding)) in
  let memories := optional_sequence_encoding tables
    (section_with_custom_encoding x05 (vector_encoding module_memory_encoding)) in
  let tags := optional_sequence_encoding memories
    (section_with_custom_encoding x0d (vector_encoding tag_type_encoding)) in
  let globals := optional_sequence_encoding tags
    (section_with_custom_encoding x06 (vector_encoding global_encoding)) in
  let exports := optional_sequence_encoding globals
    (section_with_custom_encoding x07 (vector_encoding module_export_encoding)) in
  let start := optional_sequence_encoding exports
    (section_with_custom_encoding x08 module_start_encoding) in
  let elements := optional_sequence_encoding start
    (section_with_custom_encoding x09 (vector_encoding module_element_encoding)) in
  let count := optional_sequence_encoding elements
    (section_with_custom_encoding x0c index_encoding) in
  let codes := optional_sequence_encoding count
    (section_with_custom_encoding x0a (vector_encoding (section_payload_encoding code_func_encoding))) in
  let data := optional_sequence_encoding codes
    (section_with_custom_encoding x0b (vector_encoding module_data_encoding)) in
  after_custom_encoding data.

(** Pure cross-section erasure/consistency judgment. Optional empty sections
    and absent sections have the same semantic lists. Customs disappear only
    from the semantic result, never from consumed-byte accounting. *)
Definition module_sections_erasure (sections : module_section_results unit) result : Prop :=
  match sections with
  | (_, otypes, oimports, ofts, otables, omems, otags, oglobals, oexports, ostart,
      oelems, ocount, ocodes, odatas) =>
    let fts := option_to_list ofts in
    let codes := option_to_list ocodes in
    let datas := option_to_list odatas in
    length fts = length codes /\
    (match ocount with Some n => N.of_nat (length datas) = n | None => True end) /\
    (ocount = None -> codes_datacount_required codes = false) /\
    result = {|
      mod_types := option_to_list otypes;
      mod_funcs := List.map
        (fun '(ty, (locals, es)) => Build_module_func ty locals es) (List.combine fts codes);
      mod_tables := option_to_list otables;
      mod_mems := option_to_list omems;
      mod_globals := option_to_list oglobals;
      mod_elems := option_to_list oelems;
      mod_datas := datas;
      mod_start := ostart;
      mod_imports := option_to_list oimports;
      mod_exports := option_to_list oexports;
      mod_tags := option_to_list otags |}
  end.

Definition module_binary_encoding bytes result :=
  exists sections, module_sections_encoding bytes sections /\ module_sections_erasure sections result.

Definition section_present {A} (value : option A) :=
  match value with Some _ => true | None => false end.

Definition module_section_presence (sections : module_section_results unit) :=
  match sections with
  | (_, types, imports, fts, tables, mems, tags, globals, exports, start, elems, count, codes, data) =>
    (x01, section_present types) :: (x02, section_present imports) ::
    (x03, section_present fts) :: (x04, section_present tables) ::
    (x05, section_present mems) :: (x0d, section_present tags) :: (x06, section_present globals) ::
    (x07, section_present exports) :: (x08, section_present start) ::
    (x09, section_present elems) :: (x0c, section_present count) ::
    (x0a, section_present codes) :: (x0b, section_present data) :: nil
  end.

Definition module_section_trace sections :=
  List.map fst (List.filter snd (module_section_presence sections)).
Definition module_section_rank tag :=
  if Byte.eqb tag x0d then 6 else
  if Byte.eqb tag x0c then 11 else
  if Byte.eqb tag x0a then 12 else
  if Byte.eqb tag x0b then 13 else
  if N.leb 6 (Byte.to_N tag) then S (N.to_nat (Byte.to_N tag))
  else N.to_nat (Byte.to_N tag).

Lemma map_filter_included {A B} (f : A -> B) test values :
  incl (List.map f (List.filter test values)) (List.map f values).
Proof.
  intros value Member; apply in_map_iff in Member.
  destruct Member as [a [Value Member]]; apply filter_In in Member.
  apply in_map_iff; exists a; split; [exact Value |exact (proj1 Member)].
Qed.

Lemma map_filter_nodup {A B} (f : A -> B) test values :
  NoDup (List.map f values) -> NoDup (List.map f (List.filter test values)).
Proof.
  induction values as [|a rest IH]; simpl; [constructor |].
  intro Unique; inversion Unique as [|head tail NotIn Rest]; subst.
  destruct (test a); simpl; [constructor |now apply IH].
  - intro Member; apply NotIn; now apply (map_filter_included f test rest).
  - now apply IH.
Qed.

Lemma map_filter_forall {A B} (f : A -> B) test P values :
  Forall P (List.map f values) -> Forall P (List.map f (List.filter test values)).
Proof.
  intro All; apply Forall_forall.
  intros value Member; apply (proj1 (Forall_forall _ _) All value).
  now apply (map_filter_included f test values).
Qed.

Lemma map_filter_sorted {A B} (f : A -> B) test R values :
  StronglySorted R (List.map f values) ->
  StronglySorted R (List.map f (List.filter test values)).
Proof.
  induction values as [|a rest IH]; simpl; [constructor |].
  intro Sorted; inversion Sorted as [|head tail TailSorted After]; subst.
  destruct (test a); simpl; [constructor |now apply IH].
  - now apply IH.
  - now apply map_filter_forall.
Qed.

Theorem module_section_trace_unique sections :
  NoDup (module_section_trace sections).
Proof.
  unfold module_section_trace; apply map_filter_nodup.
  destruct sections as [[[[[[[[[[[[[initial types] imports] fts] tables] mems] tags]
    globals] exports] start] elems] count] codes] data].
  cbn [module_section_presence List.map].
  repeat (constructor; [simpl; intuition discriminate |]); constructor.
Qed.

Theorem module_section_trace_ordered sections :
  StronglySorted (fun first second => module_section_rank first < module_section_rank second)
    (module_section_trace sections).
Proof.
  unfold module_section_trace; apply map_filter_sorted.
  destruct sections as [[[[[[[[[[[[[initial types] imports] fts] tables] mems] tags]
    globals] exports] start] elems] count] codes] data].
  cbn [module_section_presence List.map].
  repeat constructor; vm_compute; lia.
Qed.
