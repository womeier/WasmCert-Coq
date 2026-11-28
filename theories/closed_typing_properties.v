(** Source entry and canonical administrative stacks.  Source indices are
    resolved here, never reconstructed from an administrative operand. *)
From Wasm Require Import typing properties gc_declaration_typing
  gc_declaration_typing_properties gc_function_subtyping_properties
  gc_runtime_type_properties gc_closed_runtime_properties
  closed_operand_properties closed_source_translation.
From Stdlib Require Import List Bool NArith Lia.
From mathcomp Require Import ssrbool.
Import ListNotations.

Section ClosedTyping.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Lemma source_entry_typing s source C bes signature closed :
  be_typing source bes signature ->
  close_t_context source = Some C ->
  gc_type_context.close_function_type source.(tc_defined_types) 0 signature = Some closed ->
  e_typing s C (to_e_list bes) (lift_closed_function_type closed).
Proof.
  intros Typed Context Signature.
  rewrite <-(interpret_closed_signature _ _ _ Signature).
  now apply source_structural_entry.
Qed.

Lemma close_context_names source C :
  close_t_context source = Some C ->
  tc_defined_types C = tc_defined_types source.
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro E. inversion E. reflexivity.
Qed.

Lemma close_context_functions_length source C :
  close_t_context source = Some C ->
  length (tc_funcs C) = length (tc_funcs source).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source)))
    as [funcs|] eqn:Funcs; try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal; subst. simpl.
  apply those_length in Funcs. rewrite List.length_map in Funcs. congruence.
Qed.

Lemma close_context_globals_length source C :
  close_t_context source = Some C ->
  length (tc_globals C) = length (tc_globals source).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source)))
    as [globals|] eqn:Globals; try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal; subst. simpl.
  apply those_length in Globals. rewrite List.length_map in Globals.
  symmetry. exact Globals.
Qed.

Lemma close_context_tables_length source C :
  close_t_context source = Some C ->
  length (tc_tables C) = length (tc_tables source).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source)))
    as [tables|] eqn:Tables; try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal; subst. simpl.
  apply those_length in Tables. rewrite List.length_map in Tables.
  symmetry. exact Tables.
Qed.

Lemma close_context_table_vector source C :
  close_t_context source = Some C ->
  those (List.map (close_table_type source.(tc_defined_types)) source.(tc_tables)) =
    Some C.(tc_tables).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source)))
    as [tables|] eqn:Tables; try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal. reflexivity.
Qed.

Lemma close_context_table_lookup source C index raw :
  close_t_context source = Some C ->
  lookup_N source.(tc_tables) index = Some raw ->
  exists closed, close_table_type source.(tc_defined_types) raw = Some closed /\
    lookup_N C.(tc_tables) index = Some closed.
Proof.
  intros Context Lookup.
  pose proof (close_context_table_vector _ _ Context) as Vector.
  unfold lookup_N in *.
  eapply those_map_lookup; eauto.
Qed.

Lemma close_context_table_lookup_inv source C index closed :
  close_t_context source = Some C ->
  lookup_N C.(tc_tables) index = Some closed ->
  exists raw, close_table_type source.(tc_defined_types) raw = Some closed /\
    lookup_N source.(tc_tables) index = Some raw.
Proof.
  intros Context Lookup.
  pose proof (close_context_table_vector _ _ Context) as Vector.
  unfold lookup_N in *.
  pose proof (those_lookup_inv Vector Lookup) as Raw.
  rewrite List.nth_error_map in Raw.
  match type of Raw with
  | option_map _ ?entry = _ => destruct entry as [raw|] eqn:Source
  end; simpl in Raw.
  2: { discriminate. }
  simpl in Raw. injection Raw as Closed.
  exists raw. now split.
Qed.

Lemma close_context_elems_length source C :
  close_t_context source = Some C ->
  length (tc_elems C) = length (tc_elems source).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source)))
    as [elems|] eqn:Elems; try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal; subst. simpl.
  apply those_length in Elems. rewrite List.length_map in Elems.
  symmetry. exact Elems.
Qed.

Lemma close_context_memories source C :
  close_t_context source = Some C -> tc_mems C = tc_mems source.
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal. reflexivity.
Qed.

Lemma close_context_datas source C :
  close_t_context source = Some C -> tc_datas C = tc_datas source.
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal. reflexivity.
Qed.

Lemma close_context_updates source C locals labels ret clocals clabels cret :
  close_t_context source = Some C ->
  close_result_type source.(tc_defined_types) locals = Some clocals ->
  List.map (interpret_operand_results source.(tc_defined_types)) labels = clabels ->
  close_return_type source.(tc_defined_types) ret = Some cret ->
  close_t_context (upd_local_label_return source locals labels ret) =
    Some (upd_local_label_return C clocals clabels cret).
Proof.
  unfold close_t_context, upd_local_label_return; simpl.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intros E Locals Labels Return. inversion E; subst.
  now rewrite Locals, Return.
Qed.

Lemma close_values_typing s names values source closed :
  values_typing s names values source = true ->
  close_result_type names source = Some closed ->
  closed_values_typing s values closed = true.
Proof.
  unfold values_typing, closed_values_typing, close_result_type.
  rewrite <- those_those0.
  revert source closed.
  induction values as [|value values IH]; destruct source as [|t source];
    intros closed Typed Closed; simpl in Typed; try discriminate.
  - simpl in Closed. inversion Closed. reflexivity.
  - cbn [List.map those0] in Closed.
    destruct (gc_type_context.close_value_type names 0 t) as [ct|] eqn:Head;
      [|discriminate].
    destruct (those0 (List.map (gc_type_context.close_value_type names 0) source))
      as [tail|] eqn:Tail; [|discriminate].
    inversion Closed; subst closed.
    apply andb_true_iff in Typed as [Value Values].
    unfold value_typing in Value. rewrite Head in Value.
    simpl. apply andb_true_iff. split; [exact Value|].
    exact (IH _ _ Values Tail).
Qed.

Lemma values_typing_closes s names values source :
  values_typing s names values source = true ->
  exists closed,
    close_result_type names source = Some closed /\
    closed_values_typing s values closed = true.
Proof.
  unfold values_typing.
  revert source.
  induction values as [|value values IH]; destruct source as [|t source];
    intros Typed; simpl in Typed; try discriminate.
  - exists []. split; reflexivity.
  - apply andb_true_iff in Typed as [Value Values].
    unfold value_typing in Value.
    destruct (gc_type_context.close_value_type names 0 t) as [closed|] eqn:Head;
      [|discriminate].
    destruct (IH _ Values) as [tail [Tail TypedTail]].
    exists (closed :: tail). split.
    + unfold close_result_type in *. rewrite <-!those_those0 in *.
      cbn [List.map those0]. now rewrite Head, Tail.
    + unfold closed_values_typing in *. simpl.
      now apply andb_true_iff.
Qed.

Lemma close_context_local_update source C locals closed :
  close_t_context source = Some C ->
  close_result_type source.(tc_defined_types) locals = Some closed ->
  close_t_context (upd_local source locals) = Some (upd_local C closed).
Proof.
  unfold close_t_context, upd_local, upd_local_label_return; simpl.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intros E Locals. inversion E; subst.
  now rewrite Locals.
Qed.

Lemma close_context_locals source C :
  close_t_context source = Some C ->
  close_result_type source.(tc_defined_types) source.(tc_locals) = Some C.(tc_locals).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)) eqn:Locals; try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro E. inversion E. reflexivity.
Qed.

Lemma close_context_locals_length source C :
  close_t_context source = Some C ->
  length (tc_locals C) = length (tc_locals source).
Proof.
  intro Context. pose proof (close_context_locals _ _ Context) as Locals.
  unfold close_result_type in Locals.
  apply those_length in Locals. rewrite List.length_map in Locals. congruence.
Qed.

Lemma close_results_append names left right cleft cright :
  close_result_type names left = Some cleft ->
  close_result_type names right = Some cright ->
  close_result_type names (left ++ right) = Some (cleft ++ cright).
Proof.
  unfold close_result_type. rewrite <-!those_those0.
  revert cleft. induction left as [|t left IH]; intros cleft Left Right.
  - inversion Left; subst. exact Right.
  - cbn [List.map those0] in Left |- *.
    destruct (gc_type_context.close_value_type names 0 t) eqn:Head; [|discriminate].
    destruct (those0 (List.map (gc_type_context.close_value_type names 0) left))
      as [tail|] eqn:Tail; [|discriminate].
    inversion Left; subst. cbn [List.app List.map those0].
    rewrite Head, (IH _ eq_refl Right). reflexivity.
Qed.

Lemma all2_closing_total {A B D : Type} (view : A -> B -> bool)
    (close : B -> option D) addresses source :
  (forall address t, view address t = true -> exists closed, close t = Some closed) ->
  List.Forall2 (fun address t => view address t = true) addresses source ->
  exists closed, those (List.map close source) = Some closed.
Proof.
  intros Total Related. rewrite <- those_those0.
  induction Related as [|address t addresses source Head Tail IH].
  - exists []. reflexivity.
  - destruct (Total _ _ Head) as [closed Closed].
    destruct IH as [rest Rest]. exists (closed :: rest).
    cbn [List.map those0]. now rewrite Closed, Rest.
Qed.

Lemma all2_forall2_true {A B : Type} (p : A -> B -> bool) xs ys :
  seq.all2 p xs ys = true ->
  List.Forall2 (fun x y => p x y = true) xs ys.
Proof.
  revert ys. induction xs; destruct ys; simpl; intros Related; try discriminate.
  - constructor.
  - apply andb_true_iff in Related as [Head Tail].
    constructor; auto.
Qed.

(** No new closure/coverage assumption is required for an already checked
    instance: its four checked component views imply total closure. *)
Lemma inst_typing_context_closes s inst source :
  inst_typing s inst = Some source ->
  exists C, close_t_context source = Some C.
Proof.
  unfold inst_typing.
  destruct (seq.all _ _ && _ && _ && _ && _ && _) eqn:Checked; [|discriminate].
  destruct (those (seq.map (ext_mem_typing s) (inst_mems inst))) as [mems|];
    [|discriminate].
  destruct (those (seq.map (fun address =>
    match lookup_N (s_datas s) address with
    | Some data => datainst_typing s data
    | None => None end) (inst_datas inst))) as [datas|]; [|discriminate].
  intro Typed. inversion Typed; subst source; clear Typed.
  repeat rewrite andb_true_iff in Checked.
  destruct Checked as [[[[[_ _] Functions] Tables] Globals] Elements].
  apply all2_forall2_true in Functions, Tables, Globals, Elements.
  destruct (all2_closing_total (instance_function_view s (inst_defined_types inst))
    (gc_type_context.close_function_type (inst_defined_types inst) 0)
    (inst_funcs inst) (tc_funcs (inst_context inst))) as [funcs Funcs].
  { intros address t View. unfold instance_function_view in View.
    destruct (lookup_func_defined_type s address); [|discriminate].
    destruct (gc_type_context.close_function_type (inst_defined_types inst) 0 t)
      as [closed|]; [eauto|discriminate]. }
  { exact Functions. }
  destruct (all2_closing_total (instance_table_view s (inst_defined_types inst))
    (close_table_type (inst_defined_types inst))
    (inst_tables inst) (tc_tables (inst_context inst))) as [tables Tabs].
  { intros address t View. unfold instance_table_view in View.
    destruct (ext_table_typing s address); [|discriminate].
    destruct (close_table_type (inst_defined_types inst) t)
      as [closed|]; [eauto|discriminate]. }
  { exact Tables. }
  destruct (all2_closing_total (instance_global_view s (inst_defined_types inst))
    (close_global_type (inst_defined_types inst))
    (inst_globals inst) (tc_globals (inst_context inst))) as [globals Globs].
  { intros address t View. unfold instance_global_view in View.
    destruct (ext_global_typing s address); [|discriminate].
    destruct (close_global_type (inst_defined_types inst) t)
      as [closed|]; [eauto|discriminate]. }
  { exact Globals. }
  destruct (all2_closing_total (instance_element_view s (inst_defined_types inst))
    (close_reference_type (inst_defined_types inst))
    (inst_elems inst) (tc_elems (inst_context inst))) as [elems Elems].
  { intros address t View. unfold instance_element_view in View.
    destruct (lookup_N (s_elems s) address); [|discriminate].
    destruct (close_reference_type (inst_defined_types inst) t)
      as [closed|]; [eauto|discriminate]. }
  { exact Elements. }
  unfold close_t_context; simpl.
  rewrite Funcs, Tabs, Globs, Elems.
  eexists. reflexivity.
Qed.

Lemma inst_typing_names s inst source :
  inst_typing s inst = Some source ->
  tc_defined_types source = inst_defined_types inst.
Proof.
  unfold inst_typing.
  destruct (seq.all _ _ && _ && _ && _ && _ && _); [|discriminate].
  destruct (those (seq.map (ext_mem_typing s) (inst_mems inst))); [|discriminate].
  destruct (those (seq.map (fun address =>
    match lookup_N (s_datas s) address with
    | Some data => datainst_typing s data
    | None => None end) (inst_datas inst))); [|discriminate].
  intro E. inversion E. reflexivity.
Qed.

Lemma source_frame_closes s frame source :
  frame_typing s frame source ->
  exists C, close_t_context source = Some C /\ closed_frame_typing s frame C.
Proof.
  unfold frame_typing.
  destruct (inst_typing s (f_inst frame)) as [base|] eqn:Instance;
    [|contradiction].
  intros [locals [Equal Values]]. subst source.
  destruct (inst_typing_context_closes _ _ _ Instance) as [closed_base Base].
  destruct (values_typing_closes _ _ _ _ Values) as [closed_locals [Locals Typed]].
  pose proof (inst_typing_names _ _ _ Instance) as Names.
  rewrite <- Names in Locals.
  exists (upd_local closed_base (closed_locals ++ tc_locals closed_base)).
  split.
  - apply close_context_local_update; [exact Base|].
    eapply close_results_append; [exact Locals|].
    now apply close_context_locals.
  - exists base, closed_base, closed_locals.
    repeat split; assumption || reflexivity.
Qed.

Lemma closed_frame_source_context s frame C :
  closed_frame_typing s frame C ->
  exists source, inst_typing s frame.(f_inst) = Some source /\
    tc_types C = tc_types source /\
    tc_defined_types C = tc_defined_types source.
Proof.
  intros [source [base [locals [Instance [Context [-> Values]]]]]].
  exists source. split; [exact Instance|].
  exact (closing_context_metadata _ _ Context).
Qed.

Lemma closed_frame_function_index s frame C index :
  closed_frame_typing s frame C ->
  (N.to_nat index < length C.(tc_funcs))%nat ->
  exists address, lookup_N frame.(f_inst).(inst_funcs) index = Some address.
Proof.
  intros [source [base [locals [Instance [Context [Equal Values]]]]]] Bound.
  subst C. simpl in Bound.
  rewrite (close_context_functions_length _ _ Context) in Bound.
  destruct (lookup_N (tc_funcs source) index) as [signature|] eqn:Lookup.
  - destruct (inst_typing_func_lookup_inv Instance Lookup) as [address [_ Address]].
    now exists address.
  - unfold lookup_N in Lookup. apply List.nth_error_None in Lookup. lia.
Qed.

Lemma closed_frame_global_exists s frame C index :
  closed_frame_typing s frame C ->
  (N.to_nat index < length C.(tc_globals))%nat ->
  exists address global,
    lookup_N frame.(f_inst).(inst_globals) index = Some address /\
    lookup_N s.(s_globals) address = Some global.
Proof.
  intros [source [base [locals [Instance [Context [Equal Values]]]]]] Bound.
  subst C. simpl in Bound.
  rewrite (close_context_globals_length _ _ Context) in Bound.
  destruct (lookup_N (tc_globals source) index) as [signature|] eqn:Lookup.
  - destruct (inst_typing_global_lookup_inv Instance Lookup) as [address [View Address]].
    unfold instance_global_view, ext_global_typing in View.
    destruct (lookup_N (s_globals s) address) as [global|] eqn:Global;
      [|discriminate].
    exists address, global. now split.
  - unfold lookup_N in Lookup. apply List.nth_error_None in Lookup. lia.
Qed.

Lemma closed_frame_table_exists s frame C index :
  closed_frame_typing s frame C ->
  (N.to_nat index < length C.(tc_tables))%nat ->
  exists table, stab s frame.(f_inst) index = Some table.
Proof.
  intros [source [base [locals [Instance [Context [Equal Values]]]]]] Bound.
  subst C. simpl in Bound.
  rewrite (close_context_tables_length _ _ Context) in Bound.
  destruct (lookup_N (tc_tables source) index) as [signature|] eqn:Lookup.
  - destruct (inst_typing_table_lookup_inv Instance Lookup) as [address [View Address]].
    unfold instance_table_view, ext_table_typing in View.
    destruct (lookup_N (s_tables s) address) as [table|] eqn:Table;
      [|discriminate].
    exists table. unfold stab. now rewrite Address, Table.
  - unfold lookup_N in Lookup. apply List.nth_error_None in Lookup. lia.
Qed.

Lemma closed_frame_table_element_typing s frame C index offset expected ref :
  store_typing s ->
  closed_frame_typing s frame C ->
  lookup_N C.(tc_tables) index = Some expected ->
  stab_elem s frame.(f_inst) index offset = Some ref ->
  closed_value_typing s (VAL_ref ref) (closed_reference_value expected.(tt_elem_type)).
Proof.
  intros Store [source [base [locals [Instance [Context [Equal Values]]]]]] Lookup Element.
  subst C. simpl in Lookup.
  destruct (close_context_table_lookup_inv _ _ _ _ Context Lookup)
    as [raw [Closed Raw]].
  pose proof (instance_table_element_typing _ _ _ _ _ _ _
    Store Instance Raw Element) as Value.
  rewrite <-(inst_typing_names _ _ _ Instance) in Value.
  destruct (close_table_type_metadata _ _ _ Closed) as [_ Reference].
  pose proof (close_reference_type_value _ _ _ Reference) as ClosedValue.
  unfold value_typing in Value. now rewrite ClosedValue in Value.
Qed.

Lemma closed_frame_funcref_table_element s frame C ret labs source index offset raw ref :
  store_typing s ->
  closed_frame_typing s frame C ->
  close_t_context source = Some (upd_label (upd_return C ret) labs) ->
  lookup_N source.(tc_tables) index = Some raw ->
  raw.(tt_elem_type) = Ref_type true HT_func ->
  stab_elem s frame.(f_inst) index offset = Some ref ->
  closed_value_typing s (VAL_ref ref) (CV_ref true (CH_abstract HT_func)).
Proof.
  intros Store Frame Context Lookup Reference Element.
  destruct (close_context_table_lookup _ _ _ _ Context Lookup)
    as [expected [Closed Expected]].
  pose proof (closed_frame_table_element_typing _ _ _ _ _ _ _
    Store Frame Expected Element) as Typed.
  destruct (close_table_type_metadata _ _ _ Closed) as [_ Ref].
  rewrite Reference in Ref.
  cbn [close_reference_type gc_type_context.close_heap_type] in Ref.
  injection Ref as Ref. rewrite <-Ref in Typed. exact Typed.
Qed.

Lemma closed_frame_elem_exists s frame C index :
  closed_frame_typing s frame C ->
  (N.to_nat index < length C.(tc_elems))%nat ->
  exists address elem,
    lookup_N frame.(f_inst).(inst_elems) index = Some address /\
    lookup_N s.(s_elems) address = Some elem.
Proof.
  intros [source [base [locals [Instance [Context [Equal Values]]]]]] Bound.
  subst C. simpl in Bound.
  rewrite (close_context_elems_length _ _ Context) in Bound.
  destruct (lookup_N (tc_elems source) index) as [signature|] eqn:Lookup.
  - destruct (inst_typing_elem_lookup_inv Instance Lookup)
      as [address [elem [Address [Elem View]]]].
    exists address, elem. now split.
  - unfold lookup_N in Lookup. apply List.nth_error_None in Lookup. lia.
Qed.

Lemma closed_frame_memory_exists s frame C :
  closed_frame_typing s frame C ->
  tc_mems C <> [] ->
  exists mem, smem s frame.(f_inst) = Some mem.
Proof.
  intros [source [base [locals [Instance [Context [Equal Values]]]]]] Nonempty.
  subst C. simpl in Nonempty.
  rewrite (close_context_memories _ _ Context) in Nonempty.
  destruct (tc_mems source) as [|limit rest] eqn:Memories; [contradiction|].
  assert (Head : lookup_N (tc_mems source) 0 = Some limit) by (rewrite Memories; reflexivity).
  destruct (inst_typing_mem_lookup_inv Instance Head) as [address [Typed Address]].
  unfold ext_mem_typing in Typed.
  destruct (lookup_N (s_mems s) address) as [mem|] eqn:Memory; [|discriminate].
  exists mem. unfold smem, smem_ind. now rewrite Address, Memory.
Qed.

Lemma closed_frame_data_exists s frame C index :
  closed_frame_typing s frame C ->
  (N.to_nat index < length C.(tc_datas))%nat ->
  exists address data,
    lookup_N frame.(f_inst).(inst_datas) index = Some address /\
    lookup_N s.(s_datas) address = Some data.
Proof.
  intros [source [base [locals [Instance [Context [Equal Values]]]]]] Bound.
  subst C. simpl in Bound.
  rewrite (close_context_datas _ _ Context) in Bound.
  destruct (lookup_N (tc_datas source) index) as [signature|] eqn:Lookup.
  - destruct (inst_typing_data_lookup_inv Instance Lookup)
      as [address [data [Address [Data View]]]].
    exists address, data. now split.
  - unfold lookup_N in Lookup. apply List.nth_error_None in Lookup. lia.
Qed.

Lemma closed_frame_expand s frame C tb :
  closed_frame_typing s frame C ->
  expand frame.(f_inst) tb = expand_t C tb.
Proof.
  intro Frame. destruct (closed_frame_source_context _ _ _ Frame)
    as [source [Instance [Types Names]]].
  eapply inst_typing_expand_eq; [exact Instance|].
  symmetry. exact Types.
Qed.

Lemma closed_value_type_valid s value expected :
  closed_value_typing s value expected = true ->
  closed_value_valid (s_types s) expected.
Proof.
  unfold closed_value_typing.
  destruct (typeof_closed_value s value); [|discriminate].
  rewrite !andb_true_iff. intros [[_ Valid] _].
  now apply closed_value_validb_correct.
Qed.

Lemma closed_results_refl registry types :
  gc_type_context_properties.canonical_registry_super_wf registry ->
  Forall (closed_value_valid registry) types ->
  closed_results_matchb registry types types = true.
Proof.
  intros WF Valid. induction Valid; simpl; [reflexivity|].
  apply andb_true_iff. split; [|exact IHValid].
  apply closed_value_matchesb_correct; [exact WF|].
  now apply closed_value_matches_refl_valid.
Qed.

Lemma closed_stack_results_refl registry types :
  closed_stack_results_subtyping registry types types.
Proof. induction types; constructor; auto using csv_refl. Qed.

Lemma closed_stack_results_trans registry a b c :
  closed_stack_results_subtyping registry a b ->
  closed_stack_results_subtyping registry b c ->
  closed_stack_results_subtyping registry a c.
Proof.
  intros First. revert c. induction First; intros c Last; inversion Last; subst;
    constructor; eauto using csv_trans.
  exact (IHFirst _ H4).
Qed.

Lemma closed_stack_results_append registry a b c d :
  closed_stack_results_subtyping registry a b ->
  closed_stack_results_subtyping registry c d ->
  closed_stack_results_subtyping registry (a ++ c) (b ++ d).
Proof. apply Forall2_app. Qed.

Lemma closed_stack_results_split_right registry xs left right :
  closed_stack_results_subtyping registry xs (left ++ right) ->
  exists pre post, xs = pre ++ post /\
    closed_stack_results_subtyping registry pre left /\
    closed_stack_results_subtyping registry post right.
Proof.
  revert xs. induction left; intros xs Related.
  - exists [], xs. split; [reflexivity|]. split; [constructor|exact Related].
  - inversion Related as [|x y xs' ys' Head Tail]; subst.
    destruct (IHleft _ Tail) as [pre [post [Equal [Left Right]]]].
    subst. exists (x :: pre), post. split; [reflexivity|].
    split; [constructor; assumption|exact Right].
Qed.

Lemma closed_stack_results_split_left registry left right xs :
  closed_stack_results_subtyping registry (left ++ right) xs ->
  exists pre post, xs = pre ++ post /\
    closed_stack_results_subtyping registry left pre /\
    closed_stack_results_subtyping registry right post.
Proof.
  revert xs. induction left; intros xs Related.
  - exists [], xs. split; [reflexivity|]. split; [constructor|exact Related].
  - inversion Related as [|x y xs' ys' Head Tail]; subst.
    destruct (IHleft _ Tail) as [pre [post [Equal [Left Right]]]].
    subst. exists (y :: pre), post. split; [reflexivity|].
    split; [constructor; assumption|exact Right].
Qed.

Lemma closed_instr_refl registry signature :
  closed_instr_subtyping registry signature signature.
Proof.
  destruct signature as [inputs outputs].
  exists [], [], inputs, outputs.
  repeat split; try reflexivity; apply closed_stack_results_refl.
Qed.

Lemma closed_operand_subtyping_prefix registry suffix actual expected :
  closed_stack_value_subtyping registry actual expected ->
  closed_stack_value_subtyping (registry ++ suffix) actual expected.
Proof.
  intro Typed. induction Typed.
  - apply csv_refl.
  - apply csv_bot.
  - apply csv_match. now apply closed_value_matchesb_prefix.
  - eapply csv_trans; eauto.
Qed.

Lemma closed_results_subtyping_prefix registry suffix actual expected :
  closed_stack_results_subtyping registry actual expected ->
  closed_stack_results_subtyping (registry ++ suffix) actual expected.
Proof.
  intro Typed. induction Typed; constructor; auto.
  now apply closed_operand_subtyping_prefix.
Qed.

Lemma closed_instr_subtyping_prefix registry suffix actual expected :
  closed_instr_subtyping registry actual expected ->
  closed_instr_subtyping (registry ++ suffix) actual expected.
Proof.
  destruct actual, expected.
  intros [p [p' [isub [osub [Inputs [Outputs [Prefix [In Out]]]]]]]].
  exists p, p', isub, osub. repeat split; try assumption;
    now apply closed_results_subtyping_prefix.
Qed.

Lemma closed_basic_typing_prefix registry suffix C instructions signature :
  closed_be_typing registry C instructions signature ->
  closed_be_typing (registry ++ suffix) C instructions signature.
Proof.
  intro Typed. induction Typed; try solve [econstructor; eauto].
  eapply cbet_subtyping; [exact IHTyped|].
  now apply closed_instr_subtyping_prefix.
Qed.

Lemma closed_instr_trans registry first middle last :
  closed_instr_subtyping registry first middle ->
  closed_instr_subtyping registry middle last ->
  closed_instr_subtyping registry first last.
Proof.
  destruct first as [fi fo], middle as [mi mo], last as [li lo].
  intros [p [p' [ix [oy [MI [MO [P [IX OY]]]]]]]]
    [q [q' [jx [jy [LI [LO [Q [JX JY]]]]]]]].
  subst mi mo li lo.
  destruct (closed_stack_results_split_right _ _ _ _ JX)
    as [a [b [JXeq [AP BIX]]]].
  destruct (closed_stack_results_split_left _ _ _ _ JY)
    as [c [d [JYeq [PC OYD]]]].
  subst jx jy.
  exists (q ++ a), (q' ++ c), b, d.
  split; [apply List.app_assoc|].
  split; [apply List.app_assoc|].
  split.
  - apply closed_stack_results_append; [exact Q|].
    eapply closed_stack_results_trans; [exact AP|].
    eapply closed_stack_results_trans; eauto.
  - split; eapply closed_stack_results_trans; eauto.
Qed.

Lemma list_equal_suffixes {A : Type} (p b q d : list A) :
  p ++ b = q ++ d -> length b = length d -> p = q /\ b = d.
Proof.
  intros Equal Length.
  assert (Prefix : length p = length q).
  { apply (f_equal (@length A)) in Equal.
    rewrite !List.length_app in Equal. lia. }
  revert q Equal Prefix. induction p; destruct q; intros Equal Prefix;
    simpl in Prefix; try discriminate.
  - now split.
  - simpl in Equal. injection Equal as Head Tail. subst.
    destruct (IHp _ Tail ltac:(lia)) as [-> Last]. now split.
Qed.

Lemma closed_instr_compose_eq registry a b b' c x y z :
  closed_instr_subtyping registry (Closed_ft a b) (Closed_ft x y) ->
  closed_instr_subtyping registry (Closed_ft b' c) (Closed_ft y z) ->
  length b = length b' ->
  closed_instr_subtyping registry (Closed_ft a c) (Closed_ft x z) /\
  closed_stack_results_subtyping registry b b'.
Proof.
  intros [p [p' [isub [osub [X [Y [P [Inputs Outputs]]]]]]]]
    [q [q' [jsub [ksub [Y' [Z [Q [Arguments Results]]]]]]]] Length.
  assert (Suffix : length osub = length jsub).
  { pose proof (List.Forall2_length Outputs).
    pose proof (List.Forall2_length Arguments). lia. }
  assert (Equal : p' ++ osub = q ++ jsub).
  { transitivity y; [symmetry; exact Y|exact Y']. }
  destruct (list_equal_suffixes _ _ _ _ Equal Suffix) as [SamePrefix SameSuffix].
  subst q jsub x z. split.
  - exists p, q', isub, ksub. repeat split; try reflexivity; try assumption.
    eapply closed_stack_results_trans; eauto.
  - eapply closed_stack_results_trans; eauto.
Qed.

Lemma closed_instr_compose_nil2 registry a b c x y z :
  closed_instr_subtyping registry (Closed_ft a b) (Closed_ft x y) ->
  closed_instr_subtyping registry (Closed_ft [] c) (Closed_ft y z) ->
  closed_instr_subtyping registry (Closed_ft a (b ++ c)) (Closed_ft x z).
Proof.
  intros [p [p' [isub [osub [X [Y [P [Inputs Outputs]]]]]]]]
    [q [q' [jsub [ksub [Y' [Z [Q [Arguments Results]]]]]]]].
  inversion Arguments; subst jsub. rewrite List.app_nil_r in Y'.
  assert (Equal : q = p' ++ osub).
  { transitivity y; [symmetry; exact Y'|exact Y]. }
  rewrite Equal in Q.
  destruct (closed_stack_results_split_left _ _ _ _ Q)
    as [q1 [q2 [Split [Q1 Q2]]]].
  subst q' x z. exists p, q1, isub, (q2 ++ ksub).
  split; [reflexivity|]. split; [symmetry; apply List.app_assoc|].
  split.
  - eapply closed_stack_results_trans; eauto.
  - split; [exact Inputs|]. apply closed_stack_results_append; [|exact Results].
    eapply closed_stack_results_trans; eauto.
Qed.

Lemma closed_instr_compose_nil1 registry a b c x y z :
  closed_instr_subtyping registry (Closed_ft a []) (Closed_ft x y) ->
  closed_instr_subtyping registry (Closed_ft b c) (Closed_ft y z) ->
  closed_instr_subtyping registry (Closed_ft (b ++ a) c) (Closed_ft x z).
Proof.
  intros [p [p' [isub [osub [X [Y [P [Inputs Outputs]]]]]]]]
    [q [q' [jsub [ksub [Y' [Z [Q [Arguments Results]]]]]]]].
  inversion Outputs; subst osub. rewrite List.app_nil_r in Y.
  assert (Equal : p' = q ++ jsub).
  { transitivity y; [symmetry; exact Y|exact Y']. }
  rewrite Equal in P.
  destruct (closed_stack_results_split_right _ _ _ _ P)
    as [p1 [p2 [Split [P1 P2]]]].
  subst p x z. exists p1, q', (p2 ++ isub), ksub.
  split; [symmetry; apply List.app_assoc|]. split; [reflexivity|].
  split.
  - eapply closed_stack_results_trans; eauto.
  - split; [|exact Results]. apply closed_stack_results_append; [|exact Inputs].
    eapply closed_stack_results_trans; eauto.
Qed.

Lemma closed_instr_compose_suffix registry a b before b' c x y z :
  closed_instr_subtyping registry (Closed_ft a b) (Closed_ft x y) ->
  closed_instr_subtyping registry (Closed_ft (before ++ b') c) (Closed_ft y z) ->
  length b = length b' ->
  closed_instr_subtyping registry (Closed_ft (before ++ a) c) (Closed_ft x z).
Proof.
  intros [p [p' [isub [osub [X [Y [P [Inputs Outputs]]]]]]]]
    [q [q' [jsub [ksub [Y' [Z [Q [Arguments Results]]]]]]]] Length.
  destruct (closed_stack_results_split_right _ _ _ _ Arguments)
    as [jbefore [jlast [Split [Before Last]]]]. subst jsub.
  assert (Suffix : length osub = length jlast).
  { pose proof (List.Forall2_length Outputs).
    pose proof (List.Forall2_length Last). lia. }
  assert (Equal : p' ++ osub = (q ++ jbefore) ++ jlast).
  { rewrite <-List.app_assoc. transitivity y; [symmetry; exact Y|exact Y']. }
  destruct (list_equal_suffixes _ _ _ _ Equal Suffix) as [Prefix SuffixEqual].
  rewrite Prefix in P.
  destruct (closed_stack_results_split_right _ _ _ _ P)
    as [p1 [p2 [Split [P1 P2]]]].
  subst p x z. exists p1, q', (p2 ++ isub), ksub.
  split; [symmetry; apply List.app_assoc|]. split; [reflexivity|].
  split.
  - eapply closed_stack_results_trans; eauto.
  - split; [|exact Results]. apply closed_stack_results_append; [|exact Inputs].
    eapply closed_stack_results_trans; eauto.
Qed.

Lemma closed_instr_split registry inputs outputs inputs' outputs' middle :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft inputs' outputs') ->
  exists middle',
    closed_instr_subtyping registry (Closed_ft inputs middle) (Closed_ft inputs' middle') /\
    closed_instr_subtyping registry (Closed_ft middle outputs) (Closed_ft middle' outputs').
Proof.
  intros [p [p' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  exists (p ++ middle). split.
  - exists p, p, isub, middle. repeat split; try reflexivity;
      try assumption; apply closed_stack_results_refl.
  - exists p, p', middle, osub. repeat split; try reflexivity;
      try assumption; apply closed_stack_results_refl.
Qed.

Lemma closed_instr_empty_input_elim registry actual inputs outputs :
  closed_instr_subtyping registry (Closed_ft [] actual) (Closed_ft inputs outputs) ->
  closed_stack_results_subtyping registry (inputs ++ actual) outputs.
Proof.
  intros [p [p' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  inversion Inputs; subst isub.
  rewrite !List.app_nil_r.
  now apply closed_stack_results_append.
Qed.

Lemma closed_instr_empty_input_intro registry actual inputs outputs :
  closed_stack_results_subtyping registry (inputs ++ actual) outputs ->
  closed_instr_subtyping registry (Closed_ft [] actual) (Closed_ft inputs outputs).
Proof.
  intro Related.
  destruct (closed_stack_results_split_left _ _ _ _ Related)
    as [prefix [rest [Equal [Prefix Rest]]]].
  subst outputs. exists inputs, prefix, [], rest.
  rewrite List.app_nil_r. repeat split; try reflexivity; try assumption; constructor.
Qed.

Lemma closed_values_append s left right ltypes rtypes :
  closed_values_typing s left ltypes = true ->
  closed_values_typing s right rtypes = true ->
  closed_values_typing s (left ++ right) (ltypes ++ rtypes) = true.
Proof.
  revert ltypes. induction left; destruct ltypes; simpl;
    intros Left Right; try discriminate; auto.
  apply andb_true_iff in Left as [Head Tail].
  rewrite Head. simpl. now apply IHleft.
Qed.

Lemma closed_values_length s values types :
  closed_values_typing s values types = true ->
  length values = length types.
Proof.
  revert types. induction values; destruct types; simpl; intro Typed;
    try discriminate; [reflexivity|].
  apply andb_true_iff in Typed as [_ Tail]. f_equal. now apply IHvalues.
Qed.

Lemma lift_closed_result_length types :
  length (lift_closed_result_type types) = length types.
Proof. apply List.length_map. Qed.

Lemma interpret_operand_results_length names types :
  length (interpret_operand_results names types) = length types.
Proof. apply List.length_map. Qed.

Lemma closed_instr_required_inputs registry inputs outputs inputs' outputs' :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft inputs' outputs') ->
  exists prefix, closed_stack_results_subtyping registry inputs' (prefix ++ inputs).
Proof.
  intros [p [p' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  exists p. apply closed_stack_results_append; [apply closed_stack_results_refl|exact Inputs].
Qed.

Lemma closed_instr_size_bound registry inputs outputs inputs' outputs' :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft inputs' outputs') ->
  (length inputs <= length inputs')%nat /\ (length outputs <= length outputs')%nat.
Proof.
  intros [p [p' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  pose proof (List.Forall2_length Inputs).
  pose proof (List.Forall2_length Outputs).
  rewrite !List.length_app. lia.
Qed.

Lemma closed_instr_size_exact registry inputs outputs inputs' outputs' :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft inputs' outputs') ->
  length inputs' + length outputs = length inputs + length outputs'.
Proof.
  intros [p [p' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  pose proof (List.Forall2_length Prefix).
  pose proof (List.Forall2_length Inputs).
  pose proof (List.Forall2_length Outputs).
  rewrite !List.length_app. lia.
Qed.

Lemma closed_stack_suffix registry a b c d :
  closed_stack_results_subtyping registry (a ++ b) (c ++ d) ->
  length b = length d ->
  closed_stack_results_subtyping registry b d.
Proof.
  intros Related Suffix.
  assert (Prefix : length a = length c).
  { pose proof (Forall2_length Related) as Length.
    rewrite !List.length_app in Length. lia. }
  revert c Related Prefix.
  induction a; destruct c; intros Related Prefix; simpl in Prefix; try discriminate.
  - exact Related.
  - inversion Related; subst. eapply IHa; [exact H4|lia].
Qed.

Lemma forall2_aligned_suffix {A B} (relation : A -> B -> Prop) a b c d :
  List.Forall2 relation (a ++ b) (c ++ d) ->
  length b = length d ->
  List.Forall2 relation b d.
Proof.
  intros Related Suffix.
  assert (Prefix : length a = length c).
  { pose proof (List.Forall2_length Related) as Length.
    rewrite !List.length_app in Length. lia. }
  revert c Related Prefix.
  induction a; destruct c; intros Related Prefix; simpl in Prefix; try discriminate.
  - exact Related.
  - inversion Related; subst. eapply IHa; [exact H4|lia].
Qed.

Lemma closed_operands_transport s values actual expected :
  canonical_registry_valid s.(s_types) ->
  closed_stack_results_subtyping s.(s_types) actual expected ->
  closed_operands_typing s values actual = true ->
  closed_operands_typing s values expected = true.
Proof.
  intros Registry Related. revert values.
  induction Related; destruct values; simpl; intro Typed; try discriminate;
    [reflexivity|].
  apply andb_true_iff in Typed as [Head Tail].
  apply andb_true_iff; split.
  - eapply operand_subtyping_acceptance; eauto.
  - now apply IHRelated.
Qed.

Lemma operands_suffix s values suffix prefix types :
  closed_operands_typing s (values ++ suffix) (prefix ++ types) = true ->
  length suffix = length types ->
  closed_operands_typing s suffix types = true.
Proof.
  intros Typed Length.
  apply all2_forall2_true in Typed.
  pose proof (forall2_aligned_suffix _ _ _ _ _ Typed Length) as Related.
  clear Typed Length.
  induction Related; simpl; [reflexivity|].
  now apply andb_true_iff.
Qed.

Lemma closed_operand_top_typing s top rest actual inputs outputs result :
  canonical_registry_valid s.(s_types) ->
  closed_values_typing s (seq.rev (top ++ rest)) actual = true ->
  closed_instr_subtyping s.(s_types) (Closed_ft inputs outputs)
    (Closed_ft (lift_closed_result_type actual) result) ->
  length top = length inputs ->
  closed_operands_typing s (seq.rev top) inputs = true.
Proof.
  intros Registry Values Subtype Length.
  destruct (closed_instr_required_inputs _ _ _ _ _ Subtype) as [prefix Required].
  rewrite lift_values_typing in Values.
  pose proof (closed_operands_transport _ _ _ _ Registry Required Values) as Whole.
  rewrite seq.rev_cat in Whole.
  eapply operands_suffix; [exact Whole|].
  rewrite length_is_size, seq.size_rev, <-length_is_size. exact Length.
Qed.

Lemma closed_operand_top_suffix s top rest actual before inputs outputs result :
  canonical_registry_valid s.(s_types) ->
  closed_values_typing s (seq.rev (top ++ rest)) actual = true ->
  closed_instr_subtyping s.(s_types) (Closed_ft (before ++ inputs) outputs)
    (Closed_ft (lift_closed_result_type actual) result) ->
  length top = length inputs ->
  closed_operands_typing s (seq.rev top) inputs = true.
Proof.
  intros Registry Values Subtype Length.
  destruct (closed_instr_required_inputs _ _ _ _ _ Subtype) as [prefix Required].
  rewrite lift_values_typing in Values.
  pose proof (closed_operands_transport _ _ _ _ Registry Required Values) as Whole.
  rewrite seq.rev_cat, List.app_assoc in Whole.
  eapply operands_suffix; [exact Whole|].
  rewrite length_is_size, seq.size_rev, <-length_is_size. exact Length.
Qed.

Lemma closed_results_match_subtyping registry actual expected :
  closed_results_matchb registry actual expected = true ->
  closed_stack_results_subtyping registry
    (lift_closed_result_type actual) (lift_closed_result_type expected).
Proof.
  revert expected. induction actual; destruct expected; simpl; intro Match;
    try discriminate; constructor.
  - apply andb_true_iff in Match as [Head _]. now apply csv_match.
  - apply andb_true_iff in Match as [_ Tail]. now apply IHactual.
Qed.

Lemma closed_stack_value_reflect registry actual expected :
  canonical_registry_valid registry ->
  closed_stack_value_subtyping registry (CO_value actual) (CO_value expected) ->
  closed_value_valid registry actual ->
  closed_value_valid registry expected /\
  closed_value_matchesb registry actual expected = true.
Proof.
  intros Registry Subtype Valid.
  destruct (operand_subtyping_reflect _ _ _ Registry Subtype Valid)
    as [concrete [Equal [Expected Match]]].
  inversion Equal; subst. now split.
Qed.

Lemma closed_instr_weakening registry inputs outputs prefix :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft (prefix ++ inputs) (prefix ++ outputs)).
Proof.
  exists prefix, prefix, inputs, outputs.
  repeat split; try reflexivity; apply closed_stack_results_refl.
Qed.

Lemma closed_instr_weaken registry inputs outputs prefix :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft (prefix ++ inputs) (prefix ++ outputs)).
Proof.
  apply closed_instr_weakening.
Qed.

Lemma closed_value_instruction s C value expected :
  closed_value_typing s value expected = true ->
  e_typing s C [v_to_e value] (Closed_ft [] [CO_value expected]).
Proof.
  destruct value as [number|vector|ref].
  - destruct expected as [nt|vt|nullable heap]; unfold closed_value_typing; simpl;
      try rewrite andb_false_r; try discriminate.
     destruct number, nt; simpl; intros; try discriminate; apply ety_num.
  - destruct expected as [nt|vt|nullable heap]; unfold closed_value_typing; simpl;
      try rewrite andb_false_r; try discriminate.
    destruct vector, vt; intros; apply ety_vec.
  - destruct expected as [nt|vt|nullable heap].
    + unfold closed_value_typing; simpl.
      destruct (typeof_closed_ref s ref); simpl;
        try rewrite andb_false_r; discriminate.
    + unfold closed_value_typing; simpl.
      destruct (typeof_closed_ref s ref); simpl;
        try rewrite andb_false_r; discriminate.
    + change (closed_value_typing s (VAL_ref ref)
        (closed_reference_value (Closed_ref nullable heap)) = true ->
        e_typing s C [v_to_e (VAL_ref ref)]
          (Closed_ft [] [CO_value (closed_reference_value (Closed_ref nullable heap))])).
      destruct ref; intro Typed; simpl v_to_e;
        [apply ety_ref_null|apply ety_ref|apply ety_ref_extern|apply ety_ref_i31];
        exact Typed.
Qed.

Lemma closed_num_expected s number expected :
  closed_value_typing s (VAL_num number) (CV_num expected) = true ->
  expected = typeof_num number.
Proof.
  destruct number, expected; simpl; intro Typed; try discriminate; reflexivity.
Qed.

Lemma closed_num_type s number expected :
  closed_value_typing s (VAL_num number) expected = true ->
  expected = CV_num (typeof_num number).
Proof.
  destruct expected as [nt|vt|nullable heap].
  - intro Typed. f_equal. exact (closed_num_expected s number nt Typed).
  - destruct number, vt; discriminate.
  - unfold closed_value_typing. simpl.
    rewrite andb_false_r. discriminate.
Qed.

Lemma closed_vec_type s vector expected :
  closed_value_typing s (VAL_vec vector) expected = true ->
  expected = CV_vec T_v128.
Proof.
  destruct expected as [nt|vt|nullable heap].
  - destruct vector, nt; discriminate.
  - destruct vector, vt; reflexivity.
  - unfold closed_value_typing. simpl.
    rewrite andb_false_r. discriminate.
Qed.

Lemma closed_num_operand_subtype registry number expected :
  closed_stack_value_subtyping registry (CO_value (CV_num number)) expected ->
  expected = CO_value (CV_num number).
Proof.
  intro Subtype. remember (CO_value (CV_num number)) as operand eqn:Operand in Subtype.
  revert number Operand. induction Subtype; intros number Equal; subst.
  - reflexivity.
  - discriminate.
  - inversion Equal; subst a.
    destruct b as [nt|vt|nullable heap]; simpl in H; try discriminate.
    destruct number, nt; simpl in H; try discriminate; reflexivity.
  - pose proof (IHSubtype1 _ eq_refl) as Middle.
    subst b. exact (IHSubtype2 _ eq_refl).
Qed.

Lemma closed_vec_operand_subtype registry vector expected :
  closed_stack_value_subtyping registry (CO_value (CV_vec vector)) expected ->
  expected = CO_value (CV_vec vector).
Proof.
  intro Subtype. remember (CO_value (CV_vec vector)) as operand eqn:Operand in Subtype.
  revert vector Operand. induction Subtype; intros vector Equal; subst.
  - reflexivity.
  - discriminate.
  - inversion Equal; subst a.
    destruct b as [nt|vt|nullable heap]; simpl in H; try discriminate.
    destruct vector, vt. reflexivity.
  - pose proof (IHSubtype1 _ eq_refl) as Middle.
    subst b. exact (IHSubtype2 _ eq_refl).
Qed.

Lemma closed_ref_not_num s ref number :
  closed_value_typing s (VAL_ref ref) (CV_num number) = false.
Proof.
  unfold closed_value_typing, typeof_closed_value.
  destruct (typeof_closed_ref s ref); simpl; [apply andb_false_r|reflexivity].
Qed.

Lemma closed_ref_not_vec s ref vector :
  closed_value_typing s (VAL_ref ref) (CV_vec vector) = false.
Proof.
  unfold closed_value_typing, typeof_closed_value.
  destruct (typeof_closed_ref s ref); simpl; [apply andb_false_r|reflexivity].
Qed.

Lemma closed_vec_not_num s vector number :
  closed_value_typing s (VAL_vec vector) (CV_num number) = false.
Proof. destruct vector, number; reflexivity. Qed.

Lemma closed_num_not_vec s number vector :
  closed_value_typing s (VAL_num number) (CV_vec vector) = false.
Proof. destruct number, vector; reflexivity. Qed.

Lemma closed_num_not_ref s number nullable heap :
  closed_value_typing s (VAL_num number) (CV_ref nullable heap) = false.
Proof.
  unfold closed_value_typing. simpl.
  now rewrite andb_false_r.
Qed.

Lemma closed_vec_not_ref s vector nullable heap :
  closed_value_typing s (VAL_vec vector) (CV_ref nullable heap) = false.
Proof.
  unfold closed_value_typing. simpl.
  now rewrite andb_false_r.
Qed.

Lemma closed_values_types_valid s values types :
  closed_values_typing s values types = true ->
  Forall (closed_value_valid (s_types s)) types.
Proof.
  unfold closed_values_typing. revert types.
  induction values; destruct types; simpl; intro Typed; try discriminate.
  - constructor.
  - apply andb_true_iff in Typed as [Head Tail]. constructor.
    + now apply (closed_value_type_valid _ _ _ Head).
    + now apply IHvalues.
Qed.

Lemma closed_values_snoc s values value types :
  closed_values_typing s (values ++ [value]) types = true ->
  exists prefix t, types = prefix ++ [t] /\
    closed_values_typing s values prefix = true /\
    closed_value_typing s value t = true.
Proof.
  revert types. induction values as [|head values IH]; destruct types as [|t types];
    simpl; intro Typed; try discriminate.
  - destruct types; simpl in Typed.
    + exists [], t. split; [reflexivity|]. split; [reflexivity|].
      now apply andb_true_iff in Typed as [Value _].
    + rewrite andb_false_r in Typed. discriminate.
  - apply andb_true_iff in Typed as [Head Tail].
    destruct (IH _ Tail) as [prefix [last [Equal [Prefix Last]]]].
    subst. exists (t :: prefix), last. split; [reflexivity|].
    split; [simpl; now apply andb_true_iff|exact Last].
Qed.

Lemma closed_values_instruction s C values types :
  closed_values_typing s values types = true ->
  e_typing s C (v_to_e_list values) (Closed_ft [] (lift_closed_result_type types)).
Proof.
  revert types.
  induction values using List.rev_ind; intros types Typed.
  - destruct types; [apply ety_empty|discriminate].
  - destruct (closed_values_snoc _ _ _ _ Typed) as [prefix [t [Equal [Prefix Value]]]].
    subst types. rewrite <-v_to_e_cat.
    unfold lift_closed_result_type. rewrite List.map_app.
    eapply ety_composition.
    + exact (IHvalues _ Prefix).
    + change (e_typing s C [v_to_e x]
        (Closed_ft (lift_closed_result_type prefix)
          (lift_closed_result_type prefix ++ [CO_value t]))).
      eapply ety_subtyping; [exact (closed_value_instruction s C x t Value)|].
      pose proof (closed_instr_weaken (s_types s) [] [CO_value t]
        (lift_closed_result_type prefix)) as Weaken.
      now rewrite List.app_nil_r in Weaken.
Qed.

(** The invocation judgement has no dependence on the current instance's name
    map. In particular, this remains true after a tail call removes a frame. *)
Lemma closed_invoke_context s caller removed address signature :
  e_typing s removed [AI_invoke address] (lift_closed_function_type signature) ->
  closed_function_view s address signature = true ->
  e_typing s caller [AI_invoke address] (lift_closed_function_type signature).
Proof. intros _ View. now apply ety_invoke. Qed.

Lemma closed_stack_composition s C values address args results :
  e_typing s C (v_to_e_list values) (Closed_ft [] (lift_closed_result_type args)) ->
  closed_function_view s address (Closed_ft args results) = true ->
  e_typing s C (v_to_e_list values ++ [AI_invoke address])
    (Closed_ft [] (lift_closed_result_type results)).
Proof.
  intros Values Invoke. eapply ety_composition; [exact Values|].
  exact (@ety_invoke hfc memory s address C (Closed_ft args results) Invoke).
Qed.

Lemma closed_tail_invoke_transport s caller values address args returns results :
  canonical_registry_validb s.(s_types) = true ->
  closed_values_typing s values args = true ->
  closed_function_view s address (Closed_ft args returns) = true ->
  closed_results_matchb s.(s_types) returns results = true ->
  e_typing s caller (v_to_e_list values ++ [AI_invoke address])
    (Closed_ft [] (lift_closed_result_type results)).
Proof.
  intros Registry Values Invoke Results.
  eapply ety_subtyping.
  - eapply closed_stack_composition; [|exact Invoke].
    now apply closed_values_instruction.
  - exists [], [], [], (lift_closed_result_type results).
    repeat split; try reflexivity; try constructor.
    now apply closed_results_match_subtyping.
Qed.

Lemma source_function_view_closes s names address source closed :
  instance_function_view s names address source = true ->
  gc_type_context.close_function_type names 0 source = Some closed ->
  closed_function_view s address closed = true.
Proof.
  unfold instance_function_view, closed_function_view.
  destruct (lookup_func_defined_type s address) as [id|]; [|discriminate].
  destruct (gc_type_context.close_function_type names 0 source) as [expected|];
    [|discriminate].
  destruct (gc_type_context.expand_function_type (s_types s) id) as [[args results]|];
    [|discriminate].
  intros View Closed. inversion Closed; subst closed.
  destruct expected. exact View.
Qed.

Lemma canonical_dispatch_closed_view s inst source_context index address source closed :
  store_typing s ->
  inst_typing s inst = Some source_context ->
  lookup_function_type source_context.(tc_types) index = Some source ->
  function_reference_match s inst address index = true ->
  gc_type_context.close_function_type inst.(inst_defined_types) 0 source = Some closed ->
  closed_function_view s address closed = true.
Proof.
  intros Store Instance Signature Match Closed.
  eapply source_function_view_closes; [|exact Closed].
  eapply function_reference_match_view; eauto.
Qed.

Lemma closed_function_view_extension s later address signature :
  store_extension s later = true ->
  closed_function_view s address signature = true ->
  closed_function_view later address signature = true.
Proof.
  intros Extension View.
  unfold closed_function_view in *.
  destruct (lookup_func_defined_type s address) as [id|] eqn:Identity;
    [|discriminate].
  rewrite (store_extension_native_function_identity _ _ _ _ Extension Identity).
  destruct (gc_type_context.expand_function_type (s_types s) id) as [[args results]|]
    eqn:Expanded; [|discriminate].
  rewrite (store_extension_function_expansion _ _ _ _ Extension Expanded).
  destruct signature as [inputs outputs].
  apply andb_true_iff in View as [Arguments Results].
  destruct (store_extension_type_groups Extension) as [suffix Prefix].
  rewrite Prefix. apply andb_true_iff; split;
    now apply closed_value_list_matchesb_prefix.
Qed.

Lemma closed_function_view_arities s address fi args results actual_args actual_results :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some fi ->
  cl_type fi = Tf actual_args actual_results ->
  closed_function_view s address (Closed_ft args results) = true ->
  length args = length actual_args /\ length results = length actual_results.
Proof.
  intros Store Lookup Signature View.
  destruct (store_typing_function_expansion_agreement _ _ _ Store Lookup)
    as [id [[aa ar] [Identity [Closed Expanded]]]].
  rewrite Signature in Closed.
  destruct (close_function_type_arities _ _ _ _ _ _ Closed) as [Arguments Results].
  unfold closed_function_view in View. rewrite Identity, Expanded in View.
  apply andb_true_iff in View as [ArgMatch ResultMatch].
  apply declaration_list_matchesb_length in ArgMatch.
  apply declaration_list_matchesb_length in ResultMatch.
  split; congruence.
Qed.

Lemma closed_values_extension s later values types :
  store_extension s later = true ->
  closed_values_typing s values types = true ->
  closed_values_typing later values types = true.
Proof.
  intros Extension. unfold closed_values_typing.
  revert types. induction values; destruct types; simpl;
    intro Typed; try discriminate; [reflexivity|].
  apply andb_true_iff in Typed as [Head Tail].
  apply andb_true_iff. split.
  - eapply closed_value_typing_store_extension; eauto.
  - now apply IHvalues.
Qed.

Lemma close_function_components names inputs outputs cinputs coutputs :
  gc_type_context.close_function_type names 0 (Tf inputs outputs) =
    Some (Closed_ft cinputs coutputs) ->
  close_result_type names inputs = Some cinputs /\
  close_result_type names outputs = Some coutputs.
Proof.
  unfold gc_type_context.close_function_type, close_result_type.
  rewrite <-!those_those0.
  destruct (those0 (List.map (gc_type_context.close_value_type names 0) inputs));
    [|discriminate].
  destruct (those0 (List.map (gc_type_context.close_value_type names 0) outputs));
    [|discriminate].
  intro E. inversion E; subst. split; reflexivity.
Qed.

(** A checked native function enters the actual administrative judgement.
    All closing witnesses are derived from store/instance typing and the
    existing executable-default obligation, not supplied by the caller. *)
Theorem closed_native_entry s address inst code inputs outputs :
  store_typing s ->
  lookup_N s.(s_funcs) address =
    Some (FC_func_native (Tf inputs outputs) inst code) ->
  exists source base cinputs coutputs clocals,
    inst_typing s inst = Some source /\
    close_t_context source = Some base /\
    gc_type_context.close_function_type inst.(inst_defined_types) 0
      (Tf inputs outputs) = Some (Closed_ft cinputs coutputs) /\
    close_result_type inst.(inst_defined_types) code.(modfunc_locals) = Some clocals /\
    e_typing s
      (upd_local_label_return base (cinputs ++ clocals)
        [lift_closed_result_type coutputs] (Some (lift_closed_result_type coutputs)))
      (to_e_list code.(modfunc_body)) (Closed_ft [] (lift_closed_result_type coutputs)).
Proof.
  intros Store Lookup.
  destruct (store_typing_function_expansion_agreement _ _ _ Store Lookup)
    as [id [[cinputs coutputs] [_ [Signature _]]]].
  simpl in Signature.
  destruct (close_function_components _ _ _ _ _ Signature) as [Inputs Outputs].
  destruct (store_typing_func_lookup Store Lookup) as [ft [Same [_ Function]]].
  simpl in Same. subst ft. simpl in Function.
  destruct (inst_typing s inst) as [source|] eqn:Instance; [|contradiction].
  destruct Function as [Function Defaults].
  destruct (runtime_default_vals (s_types s) (inst_defined_types inst)
    (modfunc_locals code)) as [defaults|] eqn:DefaultValues; [|contradiction].
  destruct (values_typing_closes _ _ _ _
    (default_values_typing DefaultValues)) as [clocals [Locals _]].
  destruct (inst_typing_context_closes _ _ _ Instance) as [base Base].
  pose proof (inst_typing_names _ _ _ Instance) as Names.
  destruct code as [index locals body]. simpl in *.
  unfold func_typing in Function; simpl in Function.
  destruct (lookup_function_type (tc_types source) index) as [[args results]|];
    [|contradiction].
  destruct Function as [Equal [Body _]]. inversion Equal; subst args results.
  exists source, base, cinputs, coutputs, clocals.
  repeat split; try assumption.
  change (e_typing s
    (upd_local_label_return base (cinputs ++ clocals)
      [lift_closed_result_type coutputs] (Some (lift_closed_result_type coutputs)))
    (to_e_list body) (lift_closed_function_type (Closed_ft [] coutputs))).
  eapply source_entry_typing; [exact Body| |].
  - apply close_context_updates; [exact Base| | |].
    + rewrite Names. now apply close_results_append.
    + cbn [List.map]. f_equal. rewrite Names.
      apply closed_operand_results_interpret. now apply close_concrete_results.
    + unfold close_return_type. rewrite Names. f_equal. f_equal.
      apply closed_operand_results_interpret. now apply close_concrete_results.
  - unfold gc_type_context.close_function_type.
    rewrite <-Names in Outputs.
    unfold close_result_type in Outputs. rewrite <-those_those0 in Outputs.
    cbn. now rewrite Outputs.
Qed.

End ClosedTyping.
