(** Canonical whole-module assembly for the actual production parser.
    All public domains are AST/type/index/length conditions, never runs. *)
From Stdlib Require Import List Strings.Byte NArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes operations
  binary_format_parser binary_format_printer binary_format_parser_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_complete
  binary_format_block_properties binary_format_reference_properties
  binary_format_print_encoding binary_format_expression_print
  binary_format_vector_properties binary_format_vector_print binary_format_section_properties
  binary_format_declaration_properties binary_format_limits_properties
  binary_format_global_properties binary_format_global_section_properties binary_format_code_properties
  binary_format_record_properties binary_format_segment_properties
  binary_format_custom_properties binary_format_custom_complete
  binary_format_optional_properties binary_format_module_properties.
Local Notation byte := Byte.byte.

Definition observe_prefix_result {A m} (s : Success.Success (SizedList byte) byte A m) :=
  (Success.value s, output_bytes s).

Definition avoids_section tag bytes :=
  bytes = nil \/ exists first rest,
    bytes = first :: rest /\ first <> x00 /\ first <> tag.

Lemma avoids_section_app tag xs ys :
  avoids_section tag xs -> avoids_section tag ys -> avoids_section tag (xs ++ ys).
Proof.
  intros [Empty|[first [rest [Bytes Facts]]]] Tail.
  - now subst xs.
  - right; exists first, (rest ++ ys); subst xs; auto.
Qed.

Lemma optional_print_avoids {A} tag first (print : A -> list byte) value :
  (forall a, exists rest, print a = first :: rest) ->
  first <> x00 -> first <> tag ->
  avoids_section tag (only_if_non_none print value).
Proof.
  intros Head NotCustom Different; destruct value as [a|]; [|now left].
  destruct (Head a) as [rest Bytes]; right; exists first, rest; auto.
Qed.

Section InitialWrapper.
Context {A : Type}.
Variable tag : byte.

Lemma custom_before_step_initial n (rec : Box (right_chain (A := A)) n) op val :
  parser_initial_byte op x00 -> parser_initial_byte val tag ->
  parser_initial_set (custom_before_step n rec op val) (fun b => b = x00 \/ b = tag).
Proof.
  intros Op Val m bound input result Run.
  unfold custom_before_step in Run; rewrite run_alt_option in Run.
  destruct (runParser (Combinators.iterater_aux n rec op val) bound input)
    as [s|] eqn:Iterate.
  - unfold Combinators.iterater_aux in Iterate; simpl in Iterate.
    destruct (runParser op bound input) as [sop|] eqn:Parsed; [|discriminate].
    destruct (Op _ _ _ _ Parsed) as [rest Bytes].
    exists x00, rest; auto.
  - destruct (Val _ _ _ _ Run) as [rest Bytes].
    exists tag, rest; auto.
Qed.

Theorem iterater_initial n
    (op : Parser (SizedList byte) byte option (A -> A) n)
    (val : Parser (SizedList byte) byte option A n) :
  parser_initial_byte op x00 -> parser_initial_byte val tag ->
  parser_initial_set (Combinators.iterater op val) (fun b => b = x00 \/ b = tag).
Proof.
  change (parser_initial_byte op x00 -> parser_initial_byte val tag ->
    parser_initial_set ((Fix (right_chain (A := A)) custom_before_step n) op val)
      (fun b => b = x00 \/ b = tag)).
  apply (fix_invariant custom_before_step
    (fun k chain => forall op val,
      parser_initial_byte op x00 -> parser_initial_byte val tag ->
      parser_initial_set (chain op val) (fun b => b = x00 \/ b = tag))).
  intros k rec Rec op' val' Op Val; now apply custom_before_step_initial.
Qed.
End InitialWrapper.

Lemma section_wrapper_initial {A n}
    (p : Parser (SizedList byte) byte option A n) tag :
  parser_initial_byte p tag ->
  parser_initial_set (parse_with_customsec_star_before p)
    (fun b => b = x00 \/ b = tag).
Proof.
  intro Initial; unfold parse_with_customsec_star_before.
  apply iterater_initial; [|exact Initial].
  unfold parse_customsec_forget, parse_customsec.
  apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
Qed.

Lemma avoids_section_failure {A n m}
    (p : Parser (SizedList byte) byte option A n) tag bound input suffix :
  parser_initial_set p (fun b => b = x00 \/ b = tag) ->
  avoids_section tag suffix -> input_bytes input = suffix ->
  @runParser _ _ _ A n p m bound input = None.
Proof.
  intros Initial Avoid Bytes.
  destruct (runParser p bound input) as [result|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [first [rest [Input Allowed]]].
  rewrite Bytes in Input.
  destruct Avoid as [Empty|[other [tail [Suffix [NotCustom Different]]]]].
  - rewrite Empty in Input; discriminate.
  - rewrite Suffix in Input; inversion Input; subst first.
    destruct Allowed; congruence.
Qed.

Definition optional_prefix_observation {A n}
    (p : Parser (SizedList byte) byte option A n)
    (value : option A) input suffix :=
  match value with
  | Some a => option_map observe_prefix_result
      (runParser p (Nat.le_refl n) input) = Some (a, suffix)
  | None => runParser p (Nat.le_refl n) input = None /\ input_bytes input = suffix
  end.

Lemma optional_section_transition {A n}
    (p : Parser (SizedList byte) byte option A n) tag Wf print value suffix :
  parser_complete p (printed_encoding Wf print) ->
  parser_initial_set p (fun b => b = x00 \/ b = tag) ->
  (match value with Some a => Wf a | None => True end) ->
  avoids_section tag suffix ->
  forall k (lt : k < n) input,
    input_bytes input = only_if_non_none print value ++ suffix ->
    optional_prefix_observation (call (box p) lt) value input suffix.
Proof.
  intros Complete Initial Valid Avoid k lt input Bytes.
  destruct value as [a|].
  - assert (Lower : parser_complete (call (box p) lt) (printed_encoding Wf print)).
    { simpl; now apply parser_complete_le_lower. }
    destruct (Lower k (Nat.le_refl _) input
      (print a) suffix a Bytes (conj Valid Logic.eq_refl)) as [s [Run [Value Rest]]].
    unfold optional_prefix_observation; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (a, suffix)).
    now rewrite Value, Rest.
  - split; [|exact Bytes].
    eapply (avoids_section_failure p tag); [exact Initial |exact Avoid |exact Bytes].
Qed.

Lemma andm_prefix_observation {A B n m}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n)
    (bound : m <= n) input a middle value suffix :
  option_map observe_prefix_result (runParser p bound input) = Some (a, middle) ->
  (forall k (lt : k < n) tokens,
    input_bytes tokens = middle ->
    optional_prefix_observation (call (box q) lt) value tokens suffix) ->
  option_map observe_prefix_result
    (runParser (Combinators.andm p (box q)) bound input) = Some ((a, value), suffix).
Proof.
  intros First Next.
  destruct (runParser p bound input) as [sa|] eqn:Parsed; [|discriminate].
  change (Some (Success.value sa, output_bytes sa) = Some (a, middle)) in First.
  injection First as Value Rest.
  specialize (Next _ (Nat.le_trans _ _ _ (Success.small sa) bound)
    (Success.leftovers sa) Rest).
  unfold Combinators.andm, Combinators.andmbind; cbn.
  rewrite Parsed; cbn.
  destruct value as [b|].
  - unfold optional_prefix_observation in Next.
    destruct (runParser
      (call (box q) (Nat.le_trans _ _ _ (Success.small sa) bound))
      (Nat.le_refl _) (Success.leftovers sa)) as [sb|] eqn:Second;
      [|discriminate].
    change (Some (Success.value sb, output_bytes sb) = Some (b, suffix)) in Next.
    injection Next as BValue BRest.
    cbn in Second.
    rewrite Second; cbn.
    change (Some ((Success.value sa, Some (Success.value sb)), output_bytes sb) =
      Some ((a, Some b), suffix)).
    now rewrite Value, BValue, BRest.
  - destruct Next as [Absent Empty].
    cbn in Absent.
    rewrite Absent.
    change (Some ((Success.value sa, (None : option B)), output_bytes sa) =
      Some ((a, (None : option B)), suffix)).
    change (output_bytes sa = suffix) in Empty.
    now rewrite Value, Empty.
Qed.

Definition binary_of_raw_code (code : module_func_without_type) :=
  with_length (binary_of_code_func (fst code) (snd code)).
Definition raw_code_binary_wf (code : module_func_without_type) :=
  code_binary_wf (Build_module_func 0%N (fst code) (snd code)).
Definition raw_codesec_print codes := x0a :: with_length (binary_of_vec binary_of_raw_code codes).
Definition function_indices_print indices := x03 :: with_length (binary_of_vec binary_of_typeidx indices).
Definition datacount_print count := x0c :: with_length (binary_of_u32 count).
Definition split_module_function f := (modfunc_locals f, modfunc_body f).

Lemma parse_codesec_wrapper_printed_complete n :
  parser_complete (parse_codesec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf raw_code_binary_wf binary_of_raw_code)
      raw_codesec_print).
Proof.
  unfold parse_codesec_wrapper, raw_codesec_print.
  apply (wrapped_list_section_printed_complete x0a); [discriminate |].
  unfold parse_codesec; apply list_section_printed_complete.
  apply (complete_printed_encoding _ (section_payload_encoding code_func_encoding)).
  - apply parse_code_complete.
  - intros [locals es] Wf.
    exact (binary_of_code_encoding (Build_module_func 0%N locals es) Wf).
Qed.

Lemma parse_typesec_wrapper_printed_complete n :
  parser_complete (parse_typesec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf source_recursive_binary_wf binary_of_recursive_type)
      binary_of_typesec).
Proof.
  apply (complete_printed_encoding _ source_type_section_encoding).
  - unfold parse_typesec_wrapper.
    apply parse_with_customsec_star_before_complete_without_custom.
    + intros bytes types [payload [Bytes _]]; exists x01, payload; split; [exact Bytes |discriminate].
    + exact (proj2 (parse_source_type_section_codec n)).
  - exact source_type_section_printer_membership.
Qed.

Lemma parse_tagsec_wrapper_printed_complete n :
  parser_complete (parse_tagsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf binary_index_wf binary_of_tag) binary_of_tagsec).
Proof.
  unfold parse_tagsec_wrapper.
  apply (wrapped_list_section_printed_complete x0d); [discriminate |].
  unfold parse_tagsec; apply list_section_printed_complete.
  unfold parse_tag, binary_of_tag.
  eapply parser_complete_prefix_byte with (Q := printed_encoding binary_index_wf binary_of_idx).
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_index_printed_complete.
  - intros bytes x [Wf Bytes]; exists (binary_of_idx x); split; [exact Bytes |split; auto].
Qed.

Lemma parse_tablesec_wrapper_printed_complete n :
  parser_complete (parse_tablesec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding
      (section_list_binary_wf (fun t => table_type_binary_wf t.(modtab_type))
        binary_of_module_table) binary_of_tablesec).
Proof.
  apply (complete_printed_encoding _ table_section_encoding).
  - apply parse_tablesec_wrapper_complete_canonical.
  - intros tables [Wf [Count Size]]; now apply binary_of_tablesec_encoding.
Qed.

Lemma parse_memsec_wrapper_printed_complete n :
  parser_complete (parse_memsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding
      (section_list_binary_wf (fun m => limits_binary_wf m.(modmem_type))
        binary_of_module_mem) binary_of_memsec).
Proof.
  apply (complete_printed_encoding _ memory_section_encoding).
  - apply parse_memsec_wrapper_complete_canonical.
  - intros memories [Wf [Count Size]]; now apply binary_of_memsec_encoding.
Qed.

Lemma parse_globalsec_wrapper_printed_complete n :
  parser_complete (parse_globalsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding
      (section_list_binary_wf global_binary_wf binary_of_module_global) binary_of_globalsec).
Proof.
  apply (complete_printed_encoding _ global_section_encoding).
  - apply parse_globalsec_wrapper_complete_canonical.
  - intros globals [Wf [Count Size]]; now apply binary_of_globalsec_encoding.
Qed.

Definition start_binary_wf s :=
  binary_index_wf s.(modstart_func) /\ binary_vector_length_wf (binary_of_module_start s).

Record module_binary_wf (m : module) : Prop := {
  mbw_types : section_list_binary_wf source_recursive_binary_wf binary_of_recursive_type m.(mod_types);
  mbw_imports : section_list_binary_wf import_binary_wf binary_of_module_import m.(mod_imports);
  mbw_functions : section_list_binary_wf binary_index_wf binary_of_typeidx
    (List.map modfunc_type m.(mod_funcs));
  mbw_tables : section_list_binary_wf (fun t => table_type_binary_wf t.(modtab_type))
    binary_of_module_table m.(mod_tables);
  mbw_memories : section_list_binary_wf (fun mm => limits_binary_wf mm.(modmem_type))
    binary_of_module_mem m.(mod_mems);
  mbw_tags : section_list_binary_wf binary_index_wf binary_of_tag m.(mod_tags);
  mbw_globals : section_list_binary_wf global_binary_wf binary_of_module_global m.(mod_globals);
  mbw_exports : section_list_binary_wf export_binary_wf binary_of_module_export m.(mod_exports);
  mbw_start : match m.(mod_start) with Some s => start_binary_wf s | None => True end;
  mbw_elements : section_list_binary_wf element_binary_wf binary_of_module_elem m.(mod_elems);
  mbw_codes : section_list_binary_wf raw_code_binary_wf binary_of_raw_code
    (List.map split_module_function m.(mod_funcs));
  mbw_data : section_list_binary_wf data_binary_wf binary_of_data m.(mod_datas)
}.

Lemma optional_list_domain {A} (P : list A -> Prop) values :
  P values -> match printed_optional_list values with Some xs => P xs | None => True end.
Proof. intro Wf; destruct values; [exact I |exact Wf]. Qed.

Lemma optional_list_bytes {A} (print : list A -> list byte) values :
  only_if_non_none print (printed_optional_list values) = only_if_non_nil print values.
Proof. destruct values; reflexivity. Qed.

Lemma raw_code_vector_printer functions :
  binary_of_vec binary_of_raw_code (List.map split_module_function functions) =
    binary_of_vec binary_of_code functions.
Proof.
  unfold binary_of_vec; rewrite length_map, List.map_map.
  reflexivity.
Qed.

Lemma function_section_printer functions :
  only_if_non_none function_indices_print
    (printed_optional_list (List.map modfunc_type functions)) =
    only_if_non_nil binary_of_funcsec functions.
Proof. destruct functions; reflexivity. Qed.

Lemma code_section_printer functions :
  only_if_non_none raw_codesec_print
    (printed_optional_list (List.map split_module_function functions)) =
    only_if_non_nil binary_of_codesec functions.
Proof.
  destruct functions as [|f rest]; [reflexivity |].
  change (raw_codesec_print (List.map split_module_function (f :: rest)) =
    binary_of_codesec (f :: rest)).
  unfold raw_codesec_print, binary_of_codesec; now rewrite raw_code_vector_printer.
Qed.

Definition printed_datacount (m : module) :=
  if existsb (fun f => bes_datacount_required f.(modfunc_body)) m.(mod_funcs)
  then Some (N.of_nat (length m.(mod_datas))) else None.

Definition canonical_module_bytes (m : module) :=
  magic ++ version ++
  only_if_non_none binary_of_typesec (printed_optional_list m.(mod_types)) ++
  only_if_non_none binary_of_importsec (printed_optional_list m.(mod_imports)) ++
  only_if_non_none function_indices_print (printed_optional_list (List.map modfunc_type m.(mod_funcs))) ++
  only_if_non_none binary_of_tablesec (printed_optional_list m.(mod_tables)) ++
  only_if_non_none binary_of_memsec (printed_optional_list m.(mod_mems)) ++
  only_if_non_none binary_of_tagsec (printed_optional_list m.(mod_tags)) ++
  only_if_non_none binary_of_globalsec (printed_optional_list m.(mod_globals)) ++
  only_if_non_none binary_of_exportssec (printed_optional_list m.(mod_exports)) ++
  only_if_non_none binary_of_startsec m.(mod_start) ++
  only_if_non_none binary_of_elemsec (printed_optional_list m.(mod_elems)) ++
  only_if_non_none datacount_print (printed_datacount m) ++
  only_if_non_none raw_codesec_print (printed_optional_list (List.map split_module_function m.(mod_funcs))) ++
  only_if_non_none binary_of_datasec (printed_optional_list m.(mod_datas)).

Lemma canonical_module_bytes_actual m :
  canonical_module_bytes m = binary_of_module m.
Proof.
  unfold canonical_module_bytes.
  rewrite function_section_printer, code_section_printer.
  repeat rewrite optional_list_bytes.
  unfold binary_of_module, printed_datacount.
  destruct (existsb (fun f => bes_datacount_required (modfunc_body f)) (mod_funcs m));
    reflexivity.
Qed.

Lemma printed_datacount_domain m :
  module_binary_wf m ->
  match printed_datacount m with
  | Some count => binary_index_wf count /\ binary_vector_length_wf (binary_of_u32 count)
  | None => True
  end.
Proof.
  intro Wf; unfold printed_datacount.
  destruct (existsb (fun f => bes_datacount_required (modfunc_body f)) (mod_funcs m));
    [|exact I].
  destruct (mbw_data m Wf) as [Data [Count Size]].
  split; [exact Count |].
  destruct (binary_of_index_encoding _ Count) as [_ [_ Width]].
  unfold binary_vector_length_wf; change (N.of_nat (length (binary_of_idx
    (N.of_nat (length (mod_datas m))))) <= 4294967295)%N.
  lia.
Qed.

Lemma concrete_byte_prefix {A n} tag
    (p : Parser (SizedList byte) byte option A n) bytes value :
  parser_complete p (fun parsed result => parsed = bytes /\ result = value) ->
  parser_complete (Combinators.rand (exact_byte tag) (box p))
    (fun parsed result => parsed = tag :: bytes /\ result = value).
Proof.
  intro Complete; apply parser_complete_prefix_byte with
    (Q := fun parsed result => parsed = bytes /\ result = value).
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros parsed result [Bytes Value]; exists bytes; auto.
Qed.

Lemma concrete_rand {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) xs ys a b :
  parser_complete p (fun parsed result => parsed = xs /\ result = a) ->
  parser_complete q (fun parsed result => parsed = ys /\ result = b) ->
  parser_complete (Combinators.rand p (box q))
    (fun parsed result => parsed = xs ++ ys /\ result = b).
Proof.
  intros P Q; apply parser_complete_rand_grammar with
    (P := fun parsed result => parsed = xs /\ result = a)
    (Q := fun parsed result => parsed = ys /\ result = b).
  - exact P.
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros parsed result [Bytes Value]; exists xs, ys, a; auto.
Qed.

Lemma module_header_complete n :
  parser_complete
    (Combinators.rand (parse_magic (Toks := SizedList byte) (M := option) (n := n))
      (box parse_version))
    (fun parsed result => parsed = magic ++ version /\ result = tt).
Proof.
  apply concrete_rand with (a := tt).
  - pose proof (concrete_rand _ _ _ _ x00 x61
      (parser_complete_exact_byte x00 n) (parser_complete_exact_byte x61 n)) as First.
    pose proof (concrete_rand _ _ _ _ x61 x73 First (parser_complete_exact_byte x73 n)) as Second.
    pose proof (concrete_rand _ _ _ _ x73 x6d Second (parser_complete_exact_byte x6d n)) as Third.
    exact (concrete_map (fun _ : byte => tt) _ _ x6d Third).
  - pose proof (concrete_rand _ _ _ _ x01 x00
      (parser_complete_exact_byte x01 n) (parser_complete_exact_byte x00 n)) as First.
    pose proof (concrete_rand _ _ _ _ x00 x00 First (parser_complete_exact_byte x00 n)) as Second.
    pose proof (concrete_rand _ _ _ _ x00 x00 Second (parser_complete_exact_byte x00 n)) as Third.
    exact (concrete_map (fun _ : byte => tt) _ _ x00 Third).
Qed.

Lemma module_header_prefix n m (bound : m <= n) (input : SizedList byte m) suffix :
  input_bytes input = magic ++ version ++ suffix ->
  option_map observe_prefix_result
    (runParser (Combinators.rand (parse_magic (M := option) (n := n)) (box parse_version))
      bound input) = Some (tt, suffix).
Proof.
  intro Bytes.
  destruct (module_header_complete n m bound input (magic ++ version) suffix tt
    ltac:(now rewrite <- app_assoc) (conj Logic.eq_refl Logic.eq_refl))
    as [s [Run [Value Rest]]].
  rewrite Run.
  change (Some (Success.value s, output_bytes s) = Some (tt, suffix)).
  now rewrite Value, Rest.
Qed.

Lemma after_empty_observation {A n m}
    (p : Parser (SizedList byte) byte option A n) bound input value :
  option_map observe_prefix_result (@runParser _ _ _ A n p m bound input) = Some (value, nil) ->
  option_map observe_prefix_result
    (runParser (parse_with_customsec_star_after p) bound input) = Some (value, nil).
Proof.
  intro Parsed; destruct (runParser p bound input) as [s|] eqn:Run; [|discriminate].
  change (Some (Success.value s, output_bytes s) = Some (value, nil)) in Parsed.
  injection Parsed as Value Empty.
  rewrite (parse_with_customsec_star_after_empty_suffix p bound input s Run Empty).
  change (Some (Success.value s, output_bytes s) = Some (value, nil)).
  now rewrite Value, Empty.
Qed.

Ltac module_parser_head term :=
  lazymatch term with ?f ?arg => module_parser_head f | _ => term end.

Ltac module_leaf_complete :=
  lazymatch goal with
  | |- parser_complete ?p _ =>
    let head := module_parser_head p in
    first
      [constr_eq head (@parse_typesec_wrapper); apply parse_typesec_wrapper_printed_complete
      |constr_eq head (@parse_importsec_wrapper); apply parse_importsec_wrapper_printed_complete
      |constr_eq head (@parse_funcsec_wrapper); apply parse_funcsec_wrapper_printed_complete
      |constr_eq head (@parse_tablesec_wrapper); apply parse_tablesec_wrapper_printed_complete
       |constr_eq head (@parse_memsec_wrapper); apply parse_memsec_wrapper_printed_complete
       |constr_eq head (@parse_tagsec_wrapper); apply parse_tagsec_wrapper_printed_complete
      |constr_eq head (@parse_globalsec_wrapper); apply parse_globalsec_wrapper_printed_complete
      |constr_eq head (@parse_exportsec_wrapper); apply parse_exportsec_wrapper_printed_complete
      |constr_eq head (@parse_startsec_wrapper); apply parse_startsec_wrapper_printed_complete
      |constr_eq head (@parse_elemsec_wrapper); apply parse_elemsec_wrapper_printed_complete
      |constr_eq head (@parse_datacountsec_wrapper); apply parse_datacountsec_wrapper_printed_complete
      |constr_eq head (@parse_codesec_wrapper); apply parse_codesec_wrapper_printed_complete
      |constr_eq head (@parse_datasec_wrapper); apply parse_datasec_wrapper_printed_complete]
  end.

Ltac module_leaf_initial :=
  unfold parse_typesec_wrapper, parse_importsec_wrapper, parse_funcsec_wrapper,
    parse_tablesec_wrapper, parse_memsec_wrapper, parse_tagsec_wrapper, parse_globalsec_wrapper,
    parse_exportsec_wrapper, parse_startsec_wrapper, parse_elemsec_wrapper,
    parse_datacountsec_wrapper, parse_codesec_wrapper, parse_datasec_wrapper;
  apply section_wrapper_initial;
  unfold parse_typesec, parse_importsec, parse_funcsec, parse_tablesec,
    parse_memsec, parse_tagsec, parse_globalsec, parse_exportsec, parse_startsec,
    parse_elemsec, parse_datacountsec, parse_codesec, parse_datasec;
  numeric_initial.

Ltac canonical_suffix_avoids :=
  lazymatch goal with
  | |- avoids_section _ nil => left; reflexivity
  | |- avoids_section _ (?xs ++ ?ys) =>
    apply avoids_section_app; [canonical_suffix_avoids |canonical_suffix_avoids]
  | |- avoids_section ?tag (only_if_non_none ?print ?value) =>
    let A := lazymatch type of value with option ?T => T end in
    let first := open_constr:(_ : byte) in
    let Head := fresh "Head" in
    assert (Head : forall a : A, exists rest, print a = first :: rest)
      by (intro a; eexists; reflexivity);
    apply (optional_print_avoids tag first print value Head); discriminate
  end.

Ltac module_chain_prefix Bytes :=
  lazymatch goal with
  | |- option_map observe_prefix_result
      (runParser (Combinators.andm ?p (Combinators.box ?q)) ?bound ?input) =
      Some ((?a, ?value), ?suffix) =>
    let B := lazymatch type of value with option ?T => T end in
    let Wf := open_constr:(_ : B -> Prop) in
    let print := open_constr:(_ : B -> list byte) in
    let Leaf := fresh "Leaf" in
    assert (Leaf : parser_complete q (printed_encoding Wf print)) by module_leaf_complete;
    let tag := open_constr:(_ : byte) in
    let Initial := fresh "Initial" in
    assert (Initial : parser_initial_set q (fun b => b = x00 \/ b = tag)) by module_leaf_initial;
    let Valid := fresh "Valid" in
    assert (Valid : match value with Some v => Wf v | None => True end)
      by first [assumption |apply optional_list_domain; assumption];
    let Avoid := fresh "Avoid" in
    assert (Avoid : avoids_section tag suffix) by canonical_suffix_avoids;
    eapply andm_prefix_observation with (middle := only_if_non_none print value ++ suffix);
    [module_chain_prefix Bytes
    |exact (optional_section_transition q tag Wf print value suffix Leaf Initial Valid Avoid)]
  | _ =>
    apply module_header_prefix;
    rewrite Bytes; unfold canonical_module_bytes;
    repeat rewrite app_nil_r; reflexivity
  end.

Theorem production_module_section_sequence_printed n m (bound : m <= n)
    (input : SizedList byte m) modul :
  module_binary_wf modul ->
  input_bytes input = canonical_module_bytes modul ->
  option_map observe_prefix_result
    (runParser
      (parse_module_section_sequence_after
        (Combinators.rand (parse_magic (M := option) (n := n)) (box parse_version)))
      bound input) =
  Some (printed_module_sections modul, nil).
Proof.
  intros Wf Bytes.
  pose proof (printed_datacount_domain modul Wf) as DataCount.
  destruct Wf as [Types Imports Functions Tables Memories Tags Globals Exports Start Elements Codes Data].
  unfold parse_module_section_sequence_after.
  apply after_empty_observation.
  unfold printed_module_sections.
  fold (printed_datacount modul).
  module_chain_prefix Bytes.
Qed.

Theorem production_module_printed n m (bound : m <= n) (input : SizedList byte m) modul :
  module_binary_wf modul ->
  input_bytes input = binary_of_module modul ->
  option_map observe_prefix_result (runParser (parse_module (M := option) (n := n)) bound input) =
    Some (modul, nil).
Proof.
  intros Wf Bytes.
  assert (Canonical : input_bytes input = canonical_module_bytes modul)
    by now rewrite canonical_module_bytes_actual.
  pose proof (production_module_section_sequence_printed n m bound input modul Wf Canonical) as Raw.
  destruct (runParser (parse_module_section_sequence_after
    (Combinators.rand (parse_magic (M := option) (n := n)) (box parse_version)))
    bound input) as [s|] eqn:Parsed; [|discriminate].
  change (Some (Success.value s, output_bytes s) =
    Some (printed_module_sections modul, nil)) in Raw.
  injection Raw as Value Rest.
  unfold parse_module, parse_module_sections_after.
  rewrite run_guardM_option, Parsed.
  unfold Success.guardM; rewrite Value, finish_printed_module_sections.
  change (Some (modul, output_bytes s) = Some (modul, nil)).
  now rewrite Rest.
Qed.

Theorem binary_of_module_roundtrip modul :
  module_binary_wf modul -> run_parse_module (binary_of_module modul) = Some modul.
Proof.
  intro Wf.
  pose proof (production_module_printed _ _ (Nat.le_refl _)
    (mkSizedList (binary_of_module modul)) modul Wf Logic.eq_refl) as Parsed.
  destruct (runParser (parse_module (M := option) (n := length (binary_of_module modul)))
    (Nat.le_refl _) (mkSizedList (binary_of_module modul))) as [s|] eqn:Run;
    [|discriminate].
  change (Some (Success.value s, output_bytes s) = Some (modul, nil)) in Parsed.
  injection Parsed as Value Rest.
  unfold run_parse_module; apply run_option_correct.
  exists s; split; [exact Run |]. split; [exact Value |].
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Size.
  change (length (output_bytes s) = Success.size s) in Size.
  pose proof (f_equal (@List.length byte) Rest) as EmptyLength.
  change (length (output_bytes s) = 0) in EmptyLength.
  exact (eq_trans (eq_sym Size) EmptyLength).
Qed.

Corollary binary_of_module_string_roundtrip modul :
  module_binary_wf modul ->
  run_parse_module_str (String.string_of_list_byte (binary_of_module modul)) = Some modul.
Proof.
  intro Wf; unfold run_parse_module_str.
  rewrite String.list_byte_of_string_of_list_byte.
  now apply binary_of_module_roundtrip.
Qed.
