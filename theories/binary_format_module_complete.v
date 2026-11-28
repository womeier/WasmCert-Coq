(** Arbitrary-byte completeness and whole-input characterization for the
    actual production module parser. Optional absence is proved across custom
    prefixes, not assumed; no canonical/printer-image domain is required.
    This is source binary syntax correctness, not semantic validation or
    runtime reference closing. *)
From Stdlib Require Import List Strings.Byte NArith Arith.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_parser_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_recursive_complete
  binary_format_type_properties binary_format_block_properties
  binary_format_vector_properties binary_format_limits_properties
  binary_format_global_properties binary_format_function_properties
  binary_format_code_properties binary_format_segment_properties
  binary_format_section_properties binary_format_module_roundtrip
  binary_format_optional_properties binary_format_module_properties
  binary_format_custom_properties binary_format_custom_complete
  binary_format_module_grammar binary_format_module_sound
  binary_format_custom_general_complete.
Local Notation byte := Byte.byte.
From Wasm Require Import binary_format_declaration_properties.

Lemma grammar_complete_map {A B n} (f : A -> B)
    (p : Parser (SizedList byte) byte option A n) P :
  parser_complete p P -> parser_complete (Combinators.map f p) (mapped_encoding f P).
Proof.
  intro Complete; eapply parser_complete_map; [exact Complete |].
  intros bytes value Encoding; exact Encoding.
Qed.

Lemma grammar_complete_app {A B n}
    (p : Parser (SizedList byte) byte option (A -> B) n)
    (q : Parser (SizedList byte) byte option A n) P Q :
  parser_complete p P -> parser_complete q Q ->
  parser_complete (Combinators.app p (box q)) (application_encoding P Q).
Proof.
  intros Pp Qq; eapply parser_complete_app with (P := P) (Q := Q); [exact Pp | |].
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes value Encoding; exact Encoding.
Qed.

Lemma grammar_complete_sequence {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) P Q :
  parser_complete p P -> parser_complete q Q ->
  parser_complete (Combinators.and p (box q)) (sequence_encoding P Q).
Proof.
  intros Pp Qq; unfold Combinators.and.
  eapply parser_complete_andbind with (P := P) (Q := fun _ => Q); [exact Pp | |].
  - intros a k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes a b Encoding; exact Encoding.
Qed.

Lemma grammar_complete_tag {A n} tag
    (p : Parser (SizedList byte) byte option A n) P :
  parser_complete p P ->
  parser_complete (Combinators.rand (exact_byte tag) (box p)) (tagged_encoding tag P).
Proof.
  intro Complete; apply parser_complete_prefix_byte with (Q := P).
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes value Encoding; exact Encoding.
Qed.

Lemma parse_elemkind_general_complete n :
  parser_complete (parse_elemkind (Toks := SizedList byte) (M := option) (n := n))
    elemkind_encoding.
Proof.
  unfold parse_elemkind; eapply parser_complete_map; [apply parser_complete_exact_byte |].
  intros bytes rt [Bytes Value]; exists x00; split; [split; reflexivity || assumption |exact Value].
Qed.

Ltac general_leaf_complete :=
  lazymatch goal with
  | |- parser_complete ?p _ =>
    first
      [apply grammar_complete_map; general_leaf_complete
      |apply grammar_complete_app; [general_leaf_complete |general_leaf_complete]
      |apply grammar_complete_sequence; [general_leaf_complete |general_leaf_complete]
      |apply grammar_complete_tag; general_leaf_complete
      |lazymatch p with parse_vec _ => apply parse_vec_complete; general_leaf_complete end
      |apply wasm_production_parse_expr_complete
       |apply parse_declaration_reference_complete
      |apply parse_elemkind_general_complete
      |apply parse_name_general_complete
      |apply parse_table_type_complete
      |apply parse_memory_type_complete
      |apply parse_global_type_complete
      |apply leb128_properties.parse_u32_prefix_complete
      |apply parser_complete_anyTok]
  end.

Ltac general_subopcode_case n E Bytes m bound input prefix suffix value :=
  lazymatch type of E with
  | subopcode_encoding ?code ?Body prefix value =>
    let p := lazymatch code with
      | 0%N => constr:(@parse_module_element_0)
      | 1%N => constr:(@parse_module_element_1)
      | 2%N => constr:(@parse_module_element_2)
      | 3%N => constr:(@parse_module_element_3)
      | 4%N => constr:(@parse_module_element_4)
      | 5%N => constr:(@parse_module_element_5)
      | 6%N => constr:(@parse_module_element_6)
      | 7%N => constr:(@parse_module_element_7)
      end in
    let Complete := fresh "Complete" in
    assert (Complete : parser_complete (parse_module_element (Toks := SizedList byte)
      (M := option) (n := n)) (subopcode_encoding code Body)) by
      (unfold parse_module_element;
       let Leaf := fresh "Leaf" in
       assert (Leaf : parser_complete
         (Combinators.rand (assert_u32 code) (box (p _ _ _ _ _ _ _ _ _ n)))
         (subopcode_encoding code Body)) by
         (apply asserted_body_complete;
          unfold parse_module_element_0, parse_module_element_1, parse_module_element_2,
            parse_module_element_3, parse_module_element_4, parse_module_element_5,
            parse_module_element_6, parse_module_element_7,
            element0_encoding, element1_encoding, element2_encoding, element3_encoding,
            element4_encoding, element5_encoding, element6_encoding, element7_encoding;
          general_leaf_complete);
       subopcode_dispatch code Leaf);
    exact (Complete m bound input prefix suffix value Bytes E)
  end.

Theorem parse_element_general_complete n :
  parser_complete (parse_module_element (Toks := SizedList byte) (M := option) (n := n))
    module_element_encoding.
Proof.
  intros m bound input prefix suffix value Bytes Encoding.
  destruct Encoding as [E|[E|[E|[E|[E|[E|[E|E]]]]]]].
  all: general_subopcode_case n E Bytes m bound input prefix suffix value.
Qed.

Theorem parse_data_general_complete n :
  parser_complete (parse_module_data (Toks := SizedList byte) (M := option) (n := n))
    module_data_encoding.
Proof.
  intros m bound input prefix suffix value Bytes Encoding.
  destruct Encoding as [E|[E|E]].
  all: lazymatch type of E with
  | subopcode_encoding ?code ?Body _ _ =>
    let p := lazymatch code with
      | 0%N => constr:(parse_module_data_0 (Toks := SizedList byte) (M := option) (n := n))
      | 1%N => constr:(parse_module_data_1 (Toks := SizedList byte) (M := option) (n := n))
      | 2%N => constr:(parse_module_data_2 (Toks := SizedList byte) (M := option) (n := n))
      end in
    let Leaf := fresh "Leaf" in
    assert (Leaf : parser_complete (Combinators.rand (assert_u32 code) (box p))
      (subopcode_encoding code Body)) by
      (apply asserted_body_complete;
       unfold parse_module_data_0, parse_module_data_1, parse_module_data_2,
         data0_encoding, data1_encoding, data2_encoding; general_leaf_complete);
    let Complete := fresh "Complete" in
    assert (Complete : parser_complete
      (parse_module_data (Toks := SizedList byte) (M := option) (n := n))
      (subopcode_encoding code Body)) by
      (unfold parse_module_data; subopcode_dispatch code Leaf);
    exact (Complete m bound input prefix suffix value Bytes E)
  end.
Qed.

Lemma tagged_encoding_head {A} tag (P : list byte -> A -> Prop) bytes value :
  tagged_encoding tag P bytes value -> exists rest, bytes = tag :: rest.
Proof. intros [rest [Bytes Encoding]]; now exists rest. Qed.

Ltac descriptor_case parser n E Bytes m bound input prefix suffix value :=
  lazymatch type of E with
  | tagged_encoding ?tag (mapped_encoding ?make ?P) _ _ =>
    let p := lazymatch P with
      | index_encoding => constr:(parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))
      | table_type_encoding => constr:(parse_table_type (Toks := SizedList byte) (M := option) (n := n))
       | memory_type_encoding => constr:(parse_memory_type (Toks := SizedList byte) (M := option) (n := n))
      | global_type_encoding => constr:(parse_global_type (Toks := SizedList byte) (M := option) (n := n))
      end in
    let Leaf := fresh "Leaf" in
    assert (Leaf : parser_complete
      (Combinators.rand (exact_byte tag) (box (Combinators.map make p)))
      (tagged_encoding tag (mapped_encoding make P))) by
      (apply grammar_complete_tag; apply grammar_complete_map; general_leaf_complete);
    let Complete := fresh "Complete" in
    assert (Complete : parser_complete parser (tagged_encoding tag (mapped_encoding make P))) by
      (unfold parse_import_desc, parse_module_export_desc;
       byte_type_dispatch tag Leaf (tagged_encoding_head tag (mapped_encoding make P)));
    exact (Complete m bound input prefix suffix value Bytes E)
  end.

Theorem parse_import_descriptor_general_complete n :
  parser_complete (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
    import_descriptor_encoding.
Proof.
  intros m bound input prefix suffix value Bytes Encoding.
  destruct Encoding as [E|[E|[E|E]]].
  all: descriptor_case (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
    n E Bytes m bound input prefix suffix value.
Qed.

Theorem parse_export_descriptor_general_complete n :
  parser_complete (parse_module_export_desc (Toks := SizedList byte) (M := option) (n := n))
    export_descriptor_encoding.
Proof.
  intros m bound input prefix suffix value Bytes Encoding.
  destruct Encoding as [E|[E|[E|E]]].
  all: descriptor_case (parse_module_export_desc (Toks := SizedList byte) (M := option) (n := n))
    n E Bytes m bound input prefix suffix value.
Qed.

Theorem parse_import_general_complete n :
  parser_complete (parse_module_import (Toks := SizedList byte) (M := option) (n := n))
    module_import_encoding.
Proof.
  unfold parse_module_import, module_import_encoding.
  apply grammar_complete_map; apply grammar_complete_sequence.
  - apply grammar_complete_sequence; apply parse_name_general_complete.
  - apply parse_import_descriptor_general_complete.
Qed.

Theorem parse_export_general_complete n :
  parser_complete (parse_module_export (Toks := SizedList byte) (M := option) (n := n))
    module_export_encoding.
Proof.
  unfold parse_module_export, module_export_encoding.
  apply grammar_complete_app.
  - apply grammar_complete_map; apply parse_name_general_complete.
  - apply parse_export_descriptor_general_complete.
Qed.

Theorem parse_start_general_complete n :
  parser_complete (parse_module_start (Toks := SizedList byte) (M := option) (n := n))
    module_start_encoding.
Proof. unfold parse_module_start, module_start_encoding; general_leaf_complete. Qed.

Lemma section_with_custom_general_complete {A n} tag
    (p : Parser (SizedList byte) byte option A n) P :
  tag <> x00 ->
  parser_complete p P ->
  parser_complete
    (parse_with_customsec_star_before
      (Combinators.rand (exact_byte tag) (box (parse_section_payload p))))
    (section_with_custom_encoding tag P).
Proof.
  intros NotCustom Complete.
  apply parse_with_customsec_star_before_general_complete.
  - intros bytes value [body [Bytes Encoding]].
    exists tag, body; auto.
  - apply grammar_complete_tag; now apply parse_section_payload_complete.
Qed.

Ltac general_section_complete :=
  unfold parse_typesec_wrapper, parse_importsec_wrapper, parse_funcsec_wrapper,
    parse_tablesec_wrapper, parse_memsec_wrapper, parse_globalsec_wrapper,
    parse_exportsec_wrapper, parse_startsec_wrapper, parse_elemsec_wrapper,
    parse_datacountsec_wrapper, parse_codesec_wrapper, parse_datasec_wrapper;
  unfold parse_typesec, parse_importsec, parse_funcsec, parse_tablesec,
    parse_memsec, parse_globalsec, parse_exportsec, parse_startsec,
    parse_elemsec, parse_datacountsec, parse_codesec, parse_datasec;
  apply section_with_custom_general_complete; [discriminate |];
  first [apply parse_vec_complete;
    first [apply parse_recursive_type_source_complete |apply parse_import_general_complete
      |apply leb128_properties.parse_u32_prefix_complete
      |apply parse_module_table_complete
      |apply parse_module_memory_complete
      |apply parse_module_global_complete
      |apply parse_export_general_complete |apply parse_element_general_complete
      |apply parse_code_complete |apply parse_data_general_complete]
    |apply parse_start_general_complete |apply leb128_properties.parse_u32_prefix_complete].

Definition custom_avoids_section tag bytes :=
  custom_before_encoding custom_bytes (fun bytes (_ : unit) => avoids_section tag bytes) bytes tt.

Section CustomAbsence.
Context {A : Type}.
Variable tag : byte.
Hypothesis NotCustom : tag <> x00.

Definition before_absent_property n (chain : right_chain (A := A) n) :=
  forall op val,
    parser_initial_byte op x00 -> parser_initial_byte val tag ->
    parser_complete op (fun bytes f => custom_bytes bytes /\ f = (fun a => a)) ->
    forall m (bound : m <= n) input,
      custom_avoids_section tag (input_bytes input) ->
      runParser (chain op val) bound input = None.

Lemma custom_before_step_absent n rec :
  (forall k (lt : k < n), before_absent_property k (call rec lt)) ->
  before_absent_property n (custom_before_step n rec).
Proof.
  intros Rec op val Op Val Complete m bound input Encoding.
  remember (input_bytes input) as bytes eqn:Bytes.
  destruct Encoding as [body unit Avoid|xs ys unit CustomBytes Tail].
  - assert (OpNone : runParser op bound input = None).
    { eapply (avoids_section_failure op tag).
      - intros j lower tokens s Parsed.
        destruct (Op _ _ _ _ Parsed) as [rest B].
        exists x00, rest; auto.
      - exact Avoid.
      - symmetry; exact Bytes. }
    assert (ValNone : runParser val bound input = None).
    { eapply (avoids_section_failure val tag).
      - intros j lower tokens s Parsed.
        destruct (Val _ _ _ _ Parsed) as [rest B].
        exists tag, rest; auto.
      - exact Avoid.
      - symmetry; exact Bytes. }
    unfold custom_before_step; rewrite run_alt_option.
    unfold Combinators.iterater_aux; cbn; now rewrite OpNone, ValNone.
  - destruct (Complete m bound input xs ys (fun a => a) (eq_sym Bytes)
      (conj CustomBytes Logic.eq_refl)) as [sop [Run [Value Rest]]].
    assert (ValNone : runParser val bound input = None).
    { destruct CustomBytes as [result [payload [CustomHead Grammar]]].
      eapply (parser_initial_mismatch val tag x00 Val); [congruence |].
      rewrite <- Bytes, CustomHead; reflexivity. }
    assert (TailNone : runParser
      (call rec (Nat.le_trans _ _ _ (Success.small sop) bound)
        (Combinators.lt_lower (Nat.le_trans _ _ _ (Success.small sop) bound) op)
        (Combinators.lt_lower (Nat.le_trans _ _ _ (Success.small sop) bound) val))
      (Nat.le_refl _) (Success.leftovers sop) = None).
    { apply Rec.
      - intros j lower tokens s Parsed; eapply Op; exact Parsed.
      - intros j lower tokens s Parsed; eapply Val; exact Parsed.
      - unfold Combinators.lt_lower; now apply parser_complete_le_lower.
      - change (custom_avoids_section tag (output_bytes sop)).
        rewrite Rest; destruct unit; exact Tail. }
    unfold custom_before_step; rewrite run_alt_option.
    unfold Combinators.iterater_aux; cbn; rewrite Run; cbn.
    match goal with
    | |- context [runParser ?p ?b ?t] =>
      let R := fresh "RecursiveNone" in
      assert (R : runParser p b t = None) by exact TailNone;
      rewrite R
    end; cbn; exact ValNone.
Qed.

Theorem iterater_custom_absent n :
  before_absent_property n
    (Combinators.iterater (Toks := SizedList byte) (M := option) (A := A) (n := n)).
Proof.
  change (before_absent_property n (Fix (right_chain (A := A)) custom_before_step n)).
  apply (fix_invariant custom_before_step before_absent_property).
  exact custom_before_step_absent.
Qed.
End CustomAbsence.

Theorem custom_prefixed_section_absent {A n m}
    (p : Parser (SizedList byte) byte option A n) tag bound input :
  tag <> x00 -> parser_initial_byte p tag ->
  custom_avoids_section tag (input_bytes input) ->
  @runParser _ _ _ A n (parse_with_customsec_star_before p) m bound input = None.
Proof.
  intros NotCustom Initial Encoding; unfold parse_with_customsec_star_before.
  apply (iterater_custom_absent tag NotCustom n).
  - unfold parse_customsec_forget, parse_customsec.
    apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
  - exact Initial.
  - apply parse_customsec_forget_general_complete.
  - exact Encoding.
Qed.

Lemma custom_avoids_trailing tag customs :
  custom_repetitions custom_bytes customs -> custom_avoids_section tag customs.
Proof.
  intro Customs; induction Customs.
  - apply custom_before_payload; now left.
  - now apply custom_before_section.
Qed.

Lemma custom_avoids_next tag next {A} (P : list byte -> A -> Prop) bytes value suffix :
  next <> x00 -> next <> tag ->
  section_with_custom_encoding next P bytes value ->
  custom_avoids_section tag (bytes ++ suffix).
Proof.
  intros NotCustom Different Encoding; induction Encoding.
  - destruct H as [body [Bytes Encoding]]; subst bs.
    apply custom_before_payload; right; exists next, (body ++ suffix); auto.
  - rewrite <- app_assoc; now apply custom_before_section.
Qed.

Lemma custom_avoids_optional tag next {A} (P : list byte -> A -> Prop) bytes value suffix :
  next <> x00 -> next <> tag ->
  optional_encoding (section_with_custom_encoding next P) bytes value ->
  custom_avoids_section tag suffix ->
  custom_avoids_section tag (bytes ++ suffix).
Proof.
  intros NotCustom Different Encoding Tail; destruct value.
  - now apply (custom_avoids_next tag next P bytes a suffix).
  - change (bytes = nil) in Encoding; now subst bytes.
Qed.

Lemma optional_general_transition {A n}
    (p : Parser (SizedList byte) byte option A n) tag Q bytes value suffix :
  parser_complete p Q ->
  (forall m bound input, custom_avoids_section tag (input_bytes input) ->
    @runParser _ _ _ A n p m bound input = None) ->
  optional_encoding Q bytes value ->
  custom_avoids_section tag suffix ->
  forall k (lt : k < n) input,
    input_bytes input = bytes ++ suffix ->
    optional_prefix_observation (call (box p) lt) value input suffix.
Proof.
  intros Complete Absent Encoding Avoid k lt input Bytes.
  destruct value as [a|].
  - assert (Lower : parser_complete (call (box p) lt) Q)
      by (simpl; now apply parser_complete_le_lower).
    destruct (Lower k (Nat.le_refl _) input bytes suffix a Bytes Encoding)
      as [s [Run [Value Rest]]].
    unfold optional_prefix_observation; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (a, suffix)).
    now rewrite Value, Rest.
  - change (bytes = nil) in Encoding; subst bytes.
    change (input_bytes input = suffix) in Bytes.
    split; [|exact Bytes].
    apply Absent; now rewrite Bytes.
Qed.

Lemma after_custom_observation_eof {A n m}
    (p : Parser (SizedList byte) byte option A n) bound input a customs :
  option_map observe_prefix_result (@runParser _ _ _ A n p m bound input) = Some (a, customs) ->
  custom_repetitions custom_bytes customs ->
  option_map observe_prefix_result
    (runParser (parse_with_customsec_star_after p) bound input) = Some (a, nil).
Proof.
  intros Raw Customs.
  destruct (runParser p bound input) as [sa|] eqn:Run; [|discriminate].
  change (Some (Success.value sa, output_bytes sa) = Some (a, customs)) in Raw.
  injection Raw as Value Rest.
  destruct (production_after_chain_general_complete custom_bytes m sa
    (Induction.le_lower bound (box parse_customsec_forget)))
    as [result [TailRun [TailValue TailRest]]].
  - intros k lt.
    assert (Initial : parser_initial_byte
      (parse_customsec_forget (Toks := SizedList byte) (M := option) (A := A) (n := n)) x00).
    { unfold parse_customsec_forget, parse_customsec.
      apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial. }
    intros j lower tokens s Parsed; eapply Initial; exact Parsed.
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_customsec_forget_general_complete.
  - now rewrite Rest.
  - unfold parse_with_customsec_star_after, Combinators.iteratel; cbn.
    rewrite Run.
    change (option_map observe_prefix_result
      (Combinators.schainl sa (Induction.le_lower bound (box parse_customsec_forget))) =
      Some (a, nil)).
    rewrite TailRun.
    change (Some (Success.value result, output_bytes result) = Some (a, nil)).
    now rewrite TailValue, Value, TailRest.
Qed.

Ltac general_suffix_avoids :=
  lazymatch goal with
  | |- custom_avoids_section ?tag (?bytes ++ ?tail) =>
    match goal with
    | E : optional_encoding (section_with_custom_encoding ?next ?P) bytes ?value |- _ =>
      apply (custom_avoids_optional tag next P bytes value tail);
        [discriminate |discriminate |exact E |general_suffix_avoids]
    end
  | |- custom_avoids_section _ _ => apply custom_avoids_trailing; assumption
  end.

Ltac general_chain_prefix Encoding InputBytes :=
  lazymatch goal with
  | |- option_map observe_prefix_result
      (runParser (Combinators.andm ?p (Combinators.box ?q)) ?bound ?input) =
      Some ((?a, ?value), ?suffix) =>
    let xs := fresh "prefix" in let ys := fresh "section" in
    let Parts := fresh "Parts" in let Previous := fresh "Previous" in
    let Present := fresh "Present" in
    destruct Encoding as [xs [ys [Parts [Previous Present]]]];
    cbn [fst snd] in Previous, Present;
    let Q := lazymatch type of Present with optional_encoding ?Q _ _ => Q end in
    let tag := lazymatch Q with section_with_custom_encoding ?tag _ => tag end in
    eapply andm_prefix_observation with (middle := ys ++ suffix);
    [general_chain_prefix Previous InputBytes
    |eapply (optional_general_transition q tag Q ys value suffix);
      [solve [general_section_complete]
      |unfold parse_typesec_wrapper, parse_importsec_wrapper, parse_funcsec_wrapper,
         parse_tablesec_wrapper, parse_memsec_wrapper, parse_globalsec_wrapper,
         parse_exportsec_wrapper, parse_startsec_wrapper, parse_elemsec_wrapper,
         parse_datacountsec_wrapper, parse_codesec_wrapper, parse_datasec_wrapper;
       intros; eapply (custom_prefixed_section_absent _ tag);
         [discriminate |unfold parse_typesec, parse_importsec, parse_funcsec, parse_tablesec,
            parse_memsec, parse_globalsec, parse_exportsec, parse_startsec, parse_elemsec,
            parse_datacountsec, parse_codesec, parse_datasec; numeric_initial |assumption]
      |exact Present
      |general_suffix_avoids]]
  | _ =>
    apply module_header_prefix;
    cbn [fst snd] in Encoding;
    rewrite InputBytes;
    repeat match goal with
    | E : ?bytes = ?xs ++ ?ys |- context [?bytes] => rewrite E
    end;
    try rewrite Encoding;
    repeat rewrite <- app_assoc; reflexivity
  end.

Theorem production_module_sections_general_complete_eof n m (bound : m <= n)
    (input : SizedList byte m) bytes sections :
  input_bytes input = bytes ->
  module_sections_encoding bytes sections ->
  option_map observe_prefix_result
    (runParser (parse_module_section_sequence_after
      (Combinators.rand (parse_magic (Toks := SizedList byte) (M := option) (n := n))
        (box parse_version))) bound input) = Some (sections, nil).
Proof.
  intros InputBytes Encoding.
  destruct sections as [[[[[[[[[[[[initial types] imports] fts] tables] memories]
    globals] exports] start] elems] count] codes] data].
  destruct initial.
  unfold module_sections_encoding, after_custom_encoding in Encoding.
  destruct Encoding as [ordinary [customs [Parts [Encoding Customs]]]].
  unfold parse_module_section_sequence_after.
  apply after_custom_observation_eof with (customs := customs); [|exact Customs].
  general_chain_prefix Encoding InputBytes.
Qed.

Theorem production_parse_module_general_complete_eof n m (bound : m <= n)
    (input : SizedList byte m) bytes modul :
  input_bytes input = bytes ->
  module_binary_encoding bytes modul ->
  option_map observe_prefix_result
    (runParser (parse_module (Toks := SizedList byte) (M := option) (n := n))
      bound input) = Some (modul, nil).
Proof.
  intros Bytes [sections [Encoding Erasure]].
  pose proof (production_module_sections_general_complete_eof n m bound input
    bytes sections Bytes Encoding) as Raw.
  destruct (runParser (parse_module_section_sequence_after
    (Combinators.rand (parse_magic (Toks := SizedList byte) (M := option) (n := n))
      (box parse_version))) bound input) as [s|] eqn:Run; [|discriminate].
  change (Some (Success.value s, output_bytes s) = Some (sections, nil)) in Raw.
  injection Raw as Value Rest.
  unfold parse_module, parse_module_sections_after.
  rewrite run_guardM_option, Run.
  unfold Success.guardM; rewrite Value, (module_sections_erasure_finish sections modul Erasure).
  change (Some (modul, output_bytes s) = Some (modul, nil)).
  now rewrite Rest.
Qed.

Theorem run_parse_module_general_complete bytes modul :
  module_binary_encoding bytes modul -> run_parse_module bytes = Some modul.
Proof.
  intro Encoding.
  pose proof (production_parse_module_general_complete_eof _ _ (Nat.le_refl _)
    (mkSizedList bytes) bytes modul Logic.eq_refl Encoding) as Parsed.
  destruct (runParser (parse_module (Toks := SizedList byte) (M := option) (n := length bytes))
    (Nat.le_refl _) (mkSizedList bytes)) as [s|] eqn:Run; [|discriminate].
  change (Some (Success.value s, output_bytes s) = Some (modul, nil)) in Parsed.
  injection Parsed as Value Rest.
  unfold run_parse_module; apply run_option_correct.
  exists s; split; [exact Run |].
  split; [exact Value |].
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Size.
  change (length (output_bytes s) = Success.size s) in Size.
  pose proof (f_equal (@List.length byte) Rest) as EmptyLength.
  change (length (output_bytes s) = 0) in EmptyLength.
  exact (eq_trans (eq_sym Size) EmptyLength).
Qed.

Theorem run_parse_module_general_correct bytes modul :
  run_parse_module bytes = Some modul <-> module_binary_encoding bytes modul.
Proof.
  split; [apply run_parse_module_general_sound |apply run_parse_module_general_complete].
Qed.

Theorem run_parse_module_str_general_complete source modul :
  module_binary_encoding (String.list_byte_of_string source) modul ->
  run_parse_module_str source = Some modul.
Proof. unfold run_parse_module_str; apply run_parse_module_general_complete. Qed.

Theorem run_parse_module_str_general_correct source modul :
  run_parse_module_str source = Some modul <->
  module_binary_encoding (String.list_byte_of_string source) modul.
Proof. unfold run_parse_module_str; apply run_parse_module_general_correct. Qed.

Corollary run_parse_module_general_rejected bytes :
  run_parse_module bytes = None <->
  forall modul, ~ module_binary_encoding bytes modul.
Proof.
  split.
  - intros Rejected modul Encoding.
    rewrite (run_parse_module_general_complete bytes modul Encoding) in Rejected.
    discriminate.
  - intro NoEncoding; destruct (run_parse_module bytes) as [modul|] eqn:Parsed;
      [|reflexivity].
    exfalso; apply (NoEncoding modul).
    now apply run_parse_module_general_sound.
Qed.

Corollary run_parse_module_str_general_rejected source :
  run_parse_module_str source = None <->
  forall modul, ~ module_binary_encoding (String.list_byte_of_string source) modul.
Proof. unfold run_parse_module_str; apply run_parse_module_general_rejected. Qed.
