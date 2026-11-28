(** Cross-section consistency of the actual production module parser.
    Selectively adapted from bc7c190's dependency layer: the final EH tag
    section is between memory and global sections, not an omitted AST field. *)
From Stdlib Require Import List Strings.Byte NArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes operations binary_format_parser
  binary_format_parser_properties binary_parser_combinator_properties.

Lemma module_function_fields fts codes :
  length fts = length codes ->
  let functions := List.map
    (fun '(a, (b, c)) =>
      {| modfunc_type := a; modfunc_locals := b; modfunc_body := c |})
    (List.combine fts codes) in
  List.map modfunc_type functions = fts /\
  List.map (fun f => (modfunc_locals f, modfunc_body f)) functions = codes.
Proof.
  revert codes; induction fts as [|t fts IH]; intros [|[locals body] codes] Count;
    try discriminate.
  - split; reflexivity.
  - simpl; destruct (IH codes ltac:(simpl in Count; lia)) as [Types Bodies].
    split; [now rewrite Types |now rewrite Bodies].
Qed.

Theorem finish_module_sections_consistent {A} (initial : A)
    types imports fts tables mems tags globals exports start elems count codes datas result :
  finish_module_sections
    (initial, types, imports, fts, tables, mems, tags, globals, exports,
      start, elems, count, codes, datas) = Some result ->
  length (option_to_list fts) = length (option_to_list codes) /\
  datacount_agree (N.of_nat (length (option_to_list datas))) count = true /\
  datacount_presence_agree (option_to_list codes) count = true /\
  List.map modfunc_type result.(mod_funcs) = option_to_list fts /\
  List.map (fun f => (modfunc_locals f, modfunc_body f)) result.(mod_funcs) =
    option_to_list codes /\
  result.(mod_datas) = option_to_list datas /\
  result.(mod_tags) = option_to_list tags /\
  result.(mod_imports) = option_to_list imports /\
  result.(mod_exports) = option_to_list exports.
Proof.
  unfold finish_module_sections.
  destruct (Nat.eqb (length (option_to_list fts)) (length (option_to_list codes)))
    eqn:Functions; [|discriminate].
  destruct (datacount_agree (N.of_nat (length (option_to_list datas))) count)
    eqn:DataCount; [|discriminate].
  destruct (datacount_presence_agree (option_to_list codes) count)
    eqn:Presence; [|discriminate].
  intro Parsed; inversion Parsed; subst result; simpl.
  apply Nat.eqb_eq in Functions.
  destruct (module_function_fields _ _ Functions) as [Types Bodies].
  split; [exact Functions |]. split; [reflexivity |].
  split; [reflexivity |]. split; [exact Types |].
  split; [exact Bodies |]. repeat split; reflexivity.
Qed.

Theorem finish_module_sections_function_count_rejected {A} (initial : A)
    types imports fts tables mems tags globals exports start elems count codes datas :
  length (option_to_list fts) <> length (option_to_list codes) ->
  finish_module_sections
    (initial, types, imports, fts, tables, mems, tags, globals, exports,
      start, elems, count, codes, datas) = None.
Proof.
  intro Different; unfold finish_module_sections.
  now rewrite (proj2 (Nat.eqb_neq _ _) Different).
Qed.

Theorem finish_module_sections_datacount_rejected {A} (initial : A)
    types imports fts tables mems tags globals exports start elems count codes datas :
  N.of_nat (length (option_to_list datas)) <> count ->
  finish_module_sections
    (initial, types, imports, fts, tables, mems, tags, globals, exports,
      start, elems, Some count, codes, datas) = None.
Proof.
  intro Different; unfold finish_module_sections, datacount_agree.
  rewrite (proj2 (N.eqb_neq _ _) Different).
  now destruct (Nat.eqb (length (option_to_list fts)) (length (option_to_list codes))).
Qed.

Theorem finish_module_sections_required_datacount_rejected {A} (initial : A)
    types imports fts tables mems tags globals exports start elems codes datas :
  codes_datacount_required (option_to_list codes) = true ->
  finish_module_sections
    (initial, types, imports, fts, tables, mems, tags, globals, exports,
      start, elems, None, codes, datas) = None.
Proof.
  intro Required; unfold finish_module_sections, datacount_agree, datacount_presence_agree.
  rewrite Required.
  now destruct (Nat.eqb (length (option_to_list fts)) (length (option_to_list codes))).
Qed.

Theorem parse_module_sections_guard_rejected {A n m}
    (first : Parser (SizedList Byte.byte) Byte.byte option A n)
    (bound : m <= n) (input : SizedList Byte.byte m)
    (raw : Success.Success (SizedList Byte.byte) Byte.byte (module_section_results A) m) :
  runParser (parse_module_section_sequence_after first) bound input = Some raw ->
  finish_module_sections (Success.value raw) = None ->
  runParser (parse_module_sections_after first) bound input = None.
Proof.
  intros Parsed Rejected.
  unfold parse_module_sections_after; rewrite run_guardM_option, Parsed.
  unfold Success.guardM; now rewrite Rejected.
Qed.

Theorem run_parse_module_guard_rejected bytes
    (raw : Success.Success (SizedList Byte.byte) Byte.byte (module_section_results unit)
      (length bytes)) :
  runParser (parse_module_section_sequence_after
    (Combinators.rand (parse_magic (M := option) (n := length bytes)) (box parse_version)))
    (Nat.le_refl _) (mkSizedList bytes) = Some raw ->
  finish_module_sections (Success.value raw) = None ->
  run_parse_module bytes = None.
Proof.
  intros Parsed Rejected.
  pose proof (parse_module_sections_guard_rejected _ _ _ raw Parsed Rejected) as Failed.
  change (runParser (parse_module (M := option) (n := length bytes))
    (Nat.le_refl _) (mkSizedList bytes) = None) in Failed.
  destruct (run_parse_module bytes) as [result|] eqn:Run; [|reflexivity].
  unfold run_parse_module in Run.
  destruct (run_option_has_no_leftovers _ _ _ Run) as [s [ParsedModule _]].
  rewrite Failed in ParsedModule; discriminate.
Qed.

Theorem parse_module_sections_raw_result {A n m}
    (first : Parser (SizedList Byte.byte) Byte.byte option A n)
    (bound : m <= n) (input : SizedList Byte.byte m)
    (result : Success.Success (SizedList Byte.byte) Byte.byte module m) :
  runParser (parse_module_sections_after first) bound input = Some result ->
  exists raw,
    runParser (parse_module_section_sequence_after first) bound input = Some raw /\
    finish_module_sections (Success.value raw) = Some (Success.value result) /\
    output_bytes raw = output_bytes result.
Proof.
  unfold parse_module_sections_after; rewrite run_guardM_option.
  destruct (runParser (parse_module_section_sequence_after first) bound input)
    as [raw|] eqn:Parsed; [|discriminate].
  unfold Success.guardM.
  destruct (finish_module_sections (Success.value raw)) as [value|] eqn:Finish;
    [|discriminate].
  intro Run; inversion Run; subst result.
  exists raw; split; [reflexivity |]. split; [exact Finish |reflexivity].
Qed.

Definition printed_optional_list {A} (xs : list A) :=
  match xs with nil => None | _ => Some xs end.

Lemma printed_optional_list_contents {A} (xs : list A) :
  option_to_list (printed_optional_list xs) = xs.
Proof. destruct xs; reflexivity. Qed.

Lemma folded_orb_exists values acc :
  fold_left orb values acc = orb acc (existsb (fun b => b) values).
Proof.
  revert acc; induction values; intro acc; simpl.
  - now rewrite Bool.orb_false_r.
  - rewrite IHvalues, Bool.orb_assoc; reflexivity.
Qed.

Lemma printed_code_datacount functions :
  codes_datacount_required
    (List.map (fun f => (modfunc_locals f, modfunc_body f)) functions) =
  existsb (fun f => bes_datacount_required (modfunc_body f)) functions.
Proof.
  unfold codes_datacount_required; rewrite folded_orb_exists.
  simpl; rewrite List.map_map.
  unfold code_datacount_required.
  induction functions; simpl; [reflexivity |now rewrite IHfunctions].
Qed.

Lemma printed_functions_reconstructed functions :
  List.map
    (fun '(a, (b, c)) =>
      {| modfunc_type := a; modfunc_locals := b; modfunc_body := c |})
    (List.combine (List.map modfunc_type functions)
      (List.map (fun f => (modfunc_locals f, modfunc_body f)) functions)) =
  functions.
Proof.
  induction functions as [|[ty locals body] rest IH]; simpl; [reflexivity |].
  now rewrite IH.
Qed.

Definition printed_module_sections (m : module) : module_section_results unit :=
  (tt, printed_optional_list m.(mod_types),
    printed_optional_list m.(mod_imports),
    printed_optional_list (List.map modfunc_type m.(mod_funcs)),
    printed_optional_list m.(mod_tables), printed_optional_list m.(mod_mems),
    printed_optional_list m.(mod_tags),
    printed_optional_list m.(mod_globals), printed_optional_list m.(mod_exports),
    m.(mod_start), printed_optional_list m.(mod_elems),
    (if existsb (fun f => bes_datacount_required (modfunc_body f)) m.(mod_funcs)
     then Some (N.of_nat (length m.(mod_datas))) else None),
    printed_optional_list (List.map (fun f => (modfunc_locals f, modfunc_body f)) m.(mod_funcs)),
    printed_optional_list m.(mod_datas)).

Theorem finish_printed_module_sections m :
  finish_module_sections (printed_module_sections m) = Some m.
Proof.
  unfold printed_module_sections, finish_module_sections.
  repeat rewrite printed_optional_list_contents.
  rewrite !length_map, Nat.eqb_refl.
  unfold datacount_agree, datacount_presence_agree.
  rewrite printed_code_datacount.
  destruct (existsb (fun f => bes_datacount_required (modfunc_body f)) (mod_funcs m));
    simpl; try rewrite N.eqb_refl.
  all: rewrite printed_functions_reconstructed.
  all: destruct m; reflexivity.
Qed.
