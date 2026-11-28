(** Contextual source validation. Reuses GC's actual closing map, canonical
    registry validity and function-kind lookup, never source indices as IDs.
    The occurrence traversal is independent of reachability/operand stacks. *)
From Stdlib Require Import List Bool NArith.
From Wasm Require Import datatypes operations instantiation_spec instantiation_func
  type_checker_reflects_typing gc_declaration_typing gc_type_context.

Theorem contextual_table_checker_correct context table :
  module_table_type_checker context table = true <->
  module_table_typing context table (modtab_type table).
Proof.
  unfold module_table_type_checker, module_table_typing.
  rewrite !Bool.andb_true_iff.
  rewrite source_heap_in_contextb_correct.
  assert (Same : modtab_type table = modtab_type table) by reflexivity.
  destruct (b_e_type_checker_reflects_typing context (module_table_init table)
    (Tf nil (T_ref (tt_elem_type (modtab_type table)) :: nil))); simpl;
    intuition discriminate.
Qed.

Theorem module_type_checker_context_equivalence m imports exports message :
  module_type_checker m = (Some (imports, exports), message) <->
  module_source_context_valid m /\
  module_components_type_checker m = (Some (imports, exports), message).
Proof.
  unfold module_type_checker.
  destruct (close_and_validate_type_groups nil (module_type_groups m))
    as [[registry names]|] eqn:Closed.
  - destruct (andb (source_type_identitiesb registry names (List.concat m.(mod_types)) names)
      (module_source_types_closingb registry names m)) eqn:Source.
    + assert (Valid : module_source_context_valid m).
      { apply module_source_context_validb_correct.
        unfold module_source_context_validb; now rewrite Closed, Source. }
      tauto.
    + split; [discriminate|].
      intros [Valid _]; apply module_source_context_validb_correct in Valid.
      unfold module_source_context_validb in Valid.
      rewrite Closed, Source in Valid; discriminate.
  - split; [discriminate|].
    intros [Valid _]; apply module_source_context_validb_correct in Valid.
    unfold module_source_context_validb in Valid; rewrite Closed in Valid; discriminate.
Qed.

Theorem module_type_checker_source_types_valid m imports exports message :
  module_type_checker m = (Some (imports, exports), message) ->
  exists registry names,
    close_and_validate_type_groups nil (module_type_groups m) = Some (registry, names) /\
    source_type_identitiesb registry names (List.concat m.(mod_types)) names = true /\
    module_source_types_valid registry names m.
Proof.
  unfold module_type_checker.
  destruct (close_and_validate_type_groups nil (module_type_groups m))
    as [[registry names]|] eqn:Closed; [|discriminate].
  destruct (andb (source_type_identitiesb registry names (List.concat m.(mod_types)) names)
    (module_source_types_closingb registry names m)) eqn:Source; [|discriminate].
  intro Checked; apply Bool.andb_true_iff in Source.
  destruct Source as [Identity Source].
  exists registry, names; split; [reflexivity|].
  split; [exact Identity|].
  now apply module_source_types_closingb_correct.
Qed.

Theorem module_type_checker_source_occurrence_closed m imports exports message value :
  module_type_checker m = (Some (imports, exports), message) ->
  In value (module_source_types m) ->
  exists registry names closed,
    close_and_validate_type_groups nil (module_type_groups m) = Some (registry, names) /\
    gc_type_context.close_value_type names 0%N value = Some closed /\
    closed_value_validb registry closed = true.
Proof.
  intros Checked Member.
  destruct (module_type_checker_source_types_valid _ _ _ _ Checked)
    as [registry [names [Closed [Identity [Values Kinds]]]]].
  apply Forall_forall with (x := value) in Values; [|exact Member].
  destruct Values as [closed [Closes Valid]].
  exists registry, names, closed; auto.
Qed.

Theorem module_type_checker_function_occurrence_kind m imports exports message index :
  module_type_checker m = (Some (imports, exports), message) ->
  In index (module_function_types m) ->
  exists ft, lookup_function_type (List.concat m.(mod_types)) index = Some ft.
Proof.
  intros Checked Member.
  destruct (module_type_checker_source_types_valid _ _ _ _ Checked)
    as [registry [names [Closed [Identity [Values Kinds]]]]].
  now apply Forall_forall with (x := index) in Kinds.
Qed.

Lemma table_source_occurrence m table :
  In table m.(mod_tables) ->
  In (T_ref table.(modtab_type).(tt_elem_type)) (module_source_types m).
Proof.
  intro Member; unfold module_source_types.
  apply in_or_app; right; apply in_or_app; left.
  apply in_concat; exists
    (T_ref table.(modtab_type).(tt_elem_type) :: expression_source_types (module_table_init table)).
  split.
  - apply in_map_iff; exists table; auto.
  - now left.
Qed.

Theorem checked_module_table_source_closed m imports exports message table :
  module_type_checker m = (Some (imports, exports), message) ->
  In table m.(mod_tables) ->
  exists registry names closed,
    close_and_validate_type_groups nil (module_type_groups m) = Some (registry, names) /\
    gc_type_context.close_value_type names 0%N
      (T_ref table.(modtab_type).(tt_elem_type)) = Some closed /\
    closed_value_validb registry closed = true.
Proof.
  intros Checked Member.
  apply (module_type_checker_source_occurrence_closed _ _ _ _ _ Checked).
  now apply table_source_occurrence.
Qed.

Lemma global_source_occurrence m global :
  In global m.(mod_globals) ->
  In global.(modglob_type).(tg_t) (module_source_types m).
Proof.
  intro Member; unfold module_source_types.
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
  apply in_concat.
  exists (global.(modglob_type).(tg_t) :: expression_source_types global.(modglob_init)).
  split; [apply in_map_iff; exists global; auto|now left].
Qed.

Lemma element_source_occurrence m element :
  In element m.(mod_elems) ->
  In (T_ref element.(modelem_type)) (module_source_types m).
Proof.
  intro Member; unfold module_source_types.
  do 4 (apply in_or_app; right); apply in_or_app; left.
  apply in_concat; exists (element_source_types element).
  split; [apply in_map_iff; exists element; auto|now left].
Qed.

Lemma import_source_occurrence m imp value :
  In imp m.(mod_imports) -> In value (import_source_types imp) ->
  In value (module_source_types m).
Proof.
  intros Member Occurs; unfold module_source_types.
  do 3 (apply in_or_app; right); apply in_or_app; left.
  apply in_concat; exists (import_source_types imp).
  split; [apply in_map_iff; exists imp; auto|exact Occurs].
Qed.

Lemma unreachable_does_not_hide_source_types tail :
  expression_source_types (BI_unreachable :: tail) = expression_source_types tail.
Proof. reflexivity. Qed.

Lemma unreachable_does_not_hide_function_kinds tail :
  expression_function_types (BI_unreachable :: tail) = expression_function_types tail.
Proof. reflexivity. Qed.
