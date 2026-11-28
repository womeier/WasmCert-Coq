(** Structural entry translation. Each source composition, subsumption, and
    nested control derivation has a corresponding closed derivation node. *)
From Wasm Require Import closed_operand_properties typing.
From Stdlib Require Import List Bool NArith.
From mathcomp Require Import ssrbool.
Import ListNotations.

Section Translation.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Lemma closing_context_metadata source C :
  close_t_context source = Some C ->
  tc_types C = tc_types source /\ tc_defined_types C = tc_defined_types source.
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal. split; reflexivity.
Qed.

Lemma closing_context_labels source C labels :
  close_t_context source = Some C ->
  close_t_context (upd_label source labels) =
    Some (upd_label C (List.map (interpret_operand_results source.(tc_defined_types)) labels)).
Proof.
  unfold close_t_context, upd_label, upd_local_label_return; simpl.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal. reflexivity.
Qed.

Lemma closing_context_label_values source C :
  close_t_context source = Some C ->
  tc_labels C =
    List.map (interpret_operand_results source.(tc_defined_types)) source.(tc_labels).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  intro Equal. inversion Equal. reflexivity.
Qed.

Lemma closing_context_label_lookup source C index types :
  close_t_context source = Some C ->
  lookup_N source.(tc_labels) index = Some types ->
  lookup_N C.(tc_labels) index =
    Some (interpret_operand_results source.(tc_defined_types) types).
Proof.
  intros Context Lookup.
  rewrite (closing_context_label_values _ _ Context).
  unfold lookup_N in *. rewrite List.nth_error_map, Lookup. reflexivity.
Qed.

Lemma closing_context_return_values source C :
  close_t_context source = Some C ->
  tc_return C = option_map (interpret_operand_results source.(tc_defined_types))
    source.(tc_return).
Proof.
  unfold close_t_context.
  destruct (those (List.map (gc_type_context.close_function_type (tc_defined_types source) 0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_table_type (tc_defined_types source)) (tc_tables source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_global_type (tc_defined_types source)) (tc_globals source))); try discriminate.
  destruct (those (List.map (gc_declaration_typing.close_reference_type (tc_defined_types source)) (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (tc_return source); simpl; intro Equal; inversion Equal; reflexivity.
Qed.

Theorem source_derivation_translation registry source instructions signature :
  be_typing source instructions signature ->
  forall C, close_t_context source = Some C ->
  closed_be_typing registry C instructions
    (interpret_instr_type source.(tc_defined_types) signature).
Proof.
  intro Typed. induction Typed; intros target Context;
    try solve [eapply close_be_typing;
      [econstructor; eauto|exact I|exact Context]].
  - destruct (closing_context_metadata _ _ Context) as [Types Names].
    pose proof (closing_context_label_values _ _ Context) as Labels.
    rewrite <-Names.
    eapply cbet_block.
    + unfold expand_t in *. rewrite Types. exact H.
    + rewrite Names, Labels.
      apply IHTyped.
      exact (closing_context_labels _ _ _ Context).
  - destruct (closing_context_metadata _ _ Context) as [Types Names].
    pose proof (closing_context_label_values _ _ Context) as Labels.
    rewrite <-Names.
    eapply cbet_loop.
    + unfold expand_t in *. rewrite Types. exact H.
    + rewrite Names, Labels.
      apply IHTyped.
      exact (closing_context_labels _ _ _ Context).
  - destruct (closing_context_metadata _ _ Context) as [Types Names].
    pose proof (closing_context_label_values _ _ Context) as Labels.
    rewrite <-Names.
    eapply cbet_if.
    + unfold expand_t in *. rewrite Types. exact H.
    + rewrite Names, Labels. apply IHTyped1.
      exact (closing_context_labels _ _ _ Context).
    + rewrite Names, Labels. apply IHTyped2.
      exact (closing_context_labels _ _ _ Context).
  - apply cbet_empty.
  - unfold interpret_instr_type. eapply cbet_composition.
    + exact (IHTyped1 _ Context).
    + exact (IHTyped2 _ Context).
  - unfold interpret_instr_type. eapply cbet_subtyping.
    + exact (IHTyped _ Context).
    + exact (interpret_instr_subtyping _ _ _ _ H).
Qed.

Theorem source_structural_entry s source C instructions signature :
  be_typing source instructions signature ->
  close_t_context source = Some C ->
  e_typing s C (to_e_list instructions)
    (interpret_instr_type source.(tc_defined_types) signature).
Proof.
  intros Typed Context. apply ety_a.
  exact (source_derivation_translation _ _ _ _ Typed _ Context).
Qed.

End Translation.
