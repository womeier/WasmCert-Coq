(* Limit changes do not change canonical descriptor identities or operand
   slots. This operation is shared by source and administrative contexts. *)
From Wasm Require Import typing properties closed_typing_properties.
From Wasm Require Import gc_type_context gc_declaration_typing.
From Stdlib Require Import List Bool NArith Lia.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Fixpoint relimit_tables {R} (tables : list (table_type_gen R))
    (limits : list limits) : list (table_type_gen R) :=
  match tables, limits with
  | table :: tables, limit :: limits =>
      Build_table_type limit table.(tt_elem_type) :: relimit_tables tables limits
  | _, _ => tables
  end.

Definition relimit_context {V R F O} (C : t_context_gen V R F O)
    (limits : list limits) (memories : list memory_type) :=
  Build_t_context C.(tc_types) C.(tc_funcs)
    (relimit_tables C.(tc_tables) limits) memories C.(tc_globals)
    C.(tc_elems) C.(tc_datas) C.(tc_locals) C.(tc_labels) C.(tc_return)
    C.(tc_refs) C.(tc_defined_types).

Definition closed_context_agree (C C' : closed_t_context) : Prop :=
  exists limits memories,
    length memories = length C.(tc_mems) /\
    C' = relimit_context C limits memories.

Lemma relimit_tables_nil {R} (tables : list (table_type_gen R)) :
  relimit_tables tables nil = tables.
Proof. by destruct tables. Qed.

Lemma relimit_tables_length {R} (tables : list (table_type_gen R)) limits :
  length (relimit_tables tables limits) = length tables.
Proof.
  move: limits. induction tables; destruct limits => //=.
  by rewrite IHtables.
Qed.

Lemma relimit_tables_agree tables limits :
  all2 table_agree tables (relimit_tables tables limits).
Proof.
  move: limits. induction tables; destruct limits => //=.
  - change (all2 table_agree (a :: tables) (a :: tables)).
    apply reflexive_all2_same => table. by rewrite /table_agree eq_refl.
  - by rewrite /table_agree /= eq_refl IHtables.
Qed.

Lemma relimit_memories_agree memories memories' :
  length memories' = length memories ->
  all2 mem_agree memories memories'.
Proof.
  move: memories'. induction memories; destruct memories' => //=.
  move => Length. apply IHmemories. by injection Length.
Qed.

Lemma source_context_agree_relimit source limits memories :
  length memories = length source.(tc_mems) ->
  context_agree source (relimit_context source limits memories).
Proof.
  move => Length.
  rewrite /context_agree /relimit_context /= !eq_refl.
  have Functions : all2 func_agree (tc_funcs source) (tc_funcs source).
  { apply reflexive_all2_same => signature. by rewrite /func_agree eq_refl. }
  have Globals : all2 global_agree (tc_globals source) (tc_globals source).
  { apply reflexive_all2_same => signature. by rewrite /global_agree eq_refl. }
  by rewrite Functions Globals relimit_tables_agree (relimit_memories_agree Length).
Qed.

Lemma close_tables_relimit names tables limits closed :
  those (List.map (close_table_type names) tables) = Some closed ->
  those (List.map (close_table_type names) (relimit_tables tables limits)) =
    Some (relimit_tables closed limits).
Proof.
  rewrite -!those_those0.
  move: limits closed. induction tables as [|table tables IH];
    move => limits closed Closed; destruct limits as [|limit limits] => //=.
  - simpl in Closed. injection Closed as <-. reflexivity.
  - simpl in Closed. injection Closed as <-. reflexivity.
  - rewrite relimit_tables_nil. exact Closed.
  - simpl in Closed.
    destruct (close_table_type names table) as [head|] eqn:Head => //.
    destruct (those0 (List.map (close_table_type names) tables)) as [tail|]
      eqn:Tail => //.
    simpl in Closed.
    injection Closed as <-. simpl.
    have Relimited : close_table_type names
        (Build_table_type limit (tt_elem_type table)) =
        Some (Build_table_type limit (tt_elem_type head)).
    { unfold close_table_type in *. simpl in *.
      destruct (close_reference_type names (tt_elem_type table)) => //.
      by injection Head as <-. }
    rewrite Relimited (IH _ _ (Logic.eq_refl _)). reflexivity.
Qed.

Lemma close_context_relimit source C limits memories :
  close_t_context source = Some C ->
  close_t_context (relimit_context source limits memories) =
    Some (relimit_context C limits memories).
Proof.
  rewrite /close_t_context /relimit_context /=.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) N0)
    (tc_funcs source))) => //.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))) as [tables|] eqn:Tables => //.
  rewrite (close_tables_relimit limits Tables).
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) => //.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))) => //.
  destruct (close_result_type _ (tc_locals source)) => //.
  destruct (close_return_type _ (tc_return source)) => //.
  by move => Equal; injection Equal as <-.
Qed.

Lemma table_extension_relimit tables tables' :
  all2 table_type_extension tables tables' ->
  relimit_tables tables (List.map tt_limits tables') = tables'.
Proof.
  move: tables'. induction tables as [|table tables IH]; destruct tables' as [|table' tables']
    => //=.
  move/andP => [Head Tail].
  move: Head. rewrite /table_type_extension /table_type_extension_gen.
  move/andP => [/eqP Reference _].
  rewrite (IH _ Tail). destruct table, table'; simpl in *.
  by subst.
Qed.

Lemma context_extension_relimit source source' :
  context_extension source source' ->
  source' = relimit_context source (List.map tt_limits source'.(tc_tables))
    source'.(tc_mems).
Proof.
  move => Extension.
  unfold context_extension in Extension. remove_bools_options.
  unfold relimit_context.
  match goal with
  | Tables : is_true (all2 table_type_extension _ _) |- _ =>
    rewrite (table_extension_relimit Tables)
  end.
  destruct source, source'; simpl in *. congruence.
Qed.

Lemma context_extension_memory_length source source' :
  context_extension source source' ->
  length source'.(tc_mems) = length source.(tc_mems).
Proof.
  move => Extension.
  unfold context_extension in Extension. remove_bools_options.
  match goal with
  | Memories : is_true (all2 limits_extension _ _) |- _ =>
    have Length := all2_size Memories;
    rewrite !length_is_size; exact (esym Length)
  end.
Qed.

Lemma close_context_extension_agree source source' C C' :
  context_extension source source' ->
  close_t_context source = Some C ->
  close_t_context source' = Some C' ->
  closed_context_agree C C'.
Proof.
  move => Extension Context Context'.
  have Closed := close_context_relimit
    (List.map tt_limits (tc_tables source')) (tc_mems source') Context.
  rewrite -(context_extension_relimit Extension) Context' in Closed.
  injection Closed as Equal.
  exists (List.map tt_limits (tc_tables source')), (tc_mems source').
  split; last exact Equal.
  rewrite (close_context_memories _ _ Context).
  by apply context_extension_memory_length.
Qed.

Lemma closed_context_agree_updates C C' locals labels returns :
  closed_context_agree C C' ->
  closed_context_agree (upd_local_label_return C locals labels returns)
    (upd_local_label_return C' locals labels returns).
Proof.
  move => [limits [memories [Length ->]]].
  exists limits, memories. by split.
Qed.

Lemma close_context_global_vector source C :
  close_t_context source = Some C ->
  those (List.map (close_global_type source.(tc_defined_types)) source.(tc_globals)) =
    Some C.(tc_globals).
Proof.
  rewrite /close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) N0)
    (tc_funcs source))) => //.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))) => //.
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) => //.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))) => //.
  destruct (close_result_type _ (tc_locals source)) => //.
  destruct (close_return_type _ (tc_return source)) => //.
  by move => Equal; injection Equal as <-.
Qed.

Lemma close_context_function_vector source C :
  close_t_context source = Some C ->
  those (List.map (gc_type_context.close_function_type source.(tc_defined_types) N0)
    source.(tc_funcs)) = Some C.(tc_funcs).
Proof.
  rewrite /close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) N0)
    (tc_funcs source))) => //.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))) => //.
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) => //.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))) => //.
  destruct (close_result_type _ (tc_locals source)) => //.
  destruct (close_return_type _ (tc_return source)) => //.
  by move => Equal; injection Equal as <-.
Qed.

Lemma close_context_function_lookup source C index raw :
  close_t_context source = Some C ->
  lookup_N source.(tc_funcs) index = Some raw ->
  exists closed, gc_type_context.close_function_type source.(tc_defined_types) N0 raw = Some closed /\
    lookup_N C.(tc_funcs) index = Some closed.
Proof.
  move => Context Lookup.
  have Vector := close_context_function_vector Context.
  unfold lookup_N in *. eapply those_map_lookup; eauto.
Qed.

Lemma close_context_element_vector source C :
  close_t_context source = Some C ->
  those (List.map (close_reference_type source.(tc_defined_types)) source.(tc_elems)) =
    Some C.(tc_elems).
Proof.
  rewrite /close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) N0)
    (tc_funcs source))) => //.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))) => //.
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) => //.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))) => //.
  destruct (close_result_type _ (tc_locals source)) => //.
  destruct (close_return_type _ (tc_return source)) => //.
  by move => Equal; injection Equal as <-.
Qed.

Lemma close_context_element_lookup source C index raw :
  close_t_context source = Some C ->
  lookup_N source.(tc_elems) index = Some raw ->
  exists closed, close_reference_type source.(tc_defined_types) raw = Some closed /\
    lookup_N C.(tc_elems) index = Some closed.
Proof.
  move => Context Lookup.
  have Vector := close_context_element_vector Context.
  unfold lookup_N in *. eapply those_map_lookup; eauto.
Qed.

Lemma close_context_local_vector source C :
  close_t_context source = Some C ->
  close_result_type source.(tc_defined_types) source.(tc_locals) = Some C.(tc_locals).
Proof.
  rewrite /close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) N0)
    (tc_funcs source))) => //.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))) => //.
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) => //.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))) => //.
  destruct (close_result_type _ (tc_locals source)) => //.
  destruct (close_return_type _ (tc_return source)) => //.
  by move => Equal; injection Equal as <-.
Qed.

Lemma close_context_types source C :
  close_t_context source = Some C -> tc_types C = tc_types source.
Proof.
  rewrite /close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) N0)
    (tc_funcs source))) => //.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))) => //.
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) => //.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))) => //.
  destruct (close_result_type _ (tc_locals source)) => //.
  destruct (close_return_type _ (tc_return source)) => //.
  by move => Equal; injection Equal as <-.
Qed.

Lemma close_context_local_lookup source C index raw :
  close_t_context source = Some C ->
  lookup_N source.(tc_locals) index = Some raw ->
  exists closed, gc_type_context.close_value_type source.(tc_defined_types) N0 raw = Some closed /\
    lookup_N C.(tc_locals) index = Some closed.
Proof.
  move => Context Lookup.
  have Vector := close_context_local_vector Context.
  unfold close_result_type in Vector.
  unfold lookup_N in *. eapply those_map_lookup; eauto.
Qed.

Lemma close_context_global_lookup source C index raw :
  close_t_context source = Some C ->
  lookup_N source.(tc_globals) index = Some raw ->
  exists closed, close_global_type source.(tc_defined_types) raw = Some closed /\
    lookup_N C.(tc_globals) index = Some closed.
Proof.
  move => Context Lookup.
  have Vector := close_context_global_vector Context.
  unfold lookup_N in *. eapply those_map_lookup; eauto.
Qed.

Lemma close_context_global_lookup_inv source C index closed :
  close_t_context source = Some C ->
  lookup_N C.(tc_globals) index = Some closed ->
  exists raw, close_global_type source.(tc_defined_types) raw = Some closed /\
    lookup_N source.(tc_globals) index = Some raw.
Proof.
  move => Context Lookup.
  have Vector := close_context_global_vector Context.
  unfold lookup_N in *.
  have Raw := those_lookup_inv Vector Lookup.
  rewrite List.nth_error_map in Raw.
  match type of Raw with
  | option_map _ ?entry = _ => destruct entry as [raw|] eqn:Source
  end; simpl in Raw; last discriminate.
  injection Raw as Closed. exists raw. by split.
Qed.
