(** The internal stack domain is not the domain of storable GC values. *)
From Wasm Require Import typing gc_types gc_declaration_typing gc_declaration_typing_properties
  gc_function_subtyping_properties.
From Stdlib Require Import List Bool NArith.
From mathcomp Require Import ssrbool eqtype.
Import ListNotations.

Section Operands.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Lemma operand_bottom_uninhabited s value :
  closed_operand_typing s value CO_bot = false.
Proof. reflexivity. Qed.

Lemma operands_are_concrete s values operands :
  closed_operands_typing s values operands = true ->
  exists concrete,
    operands = lift_closed_result_type concrete /\
    closed_values_typing s values concrete = true.
Proof.
  unfold closed_operands_typing. revert operands.
  induction values; destruct operands; simpl; intro Typed; try discriminate.
  - exists []. split; reflexivity.
  - apply andb_true_iff in Typed as [Head Tail].
    destruct c as [value_type|]; [|discriminate].
    destruct (IHvalues _ Tail) as [concrete [Equal Values]].
    exists (value_type :: concrete). subst.
    split; [reflexivity|]. simpl. now apply andb_true_iff.
Qed.

Lemma lift_values_typing s values types :
  closed_values_typing s values types =
    closed_operands_typing s values (lift_closed_result_type types).
Proof.
  revert types. induction values; destruct types; simpl; auto.
  now rewrite IHvalues.
Qed.

Lemma close_bottom names : close_operand_type names T_bot = Some CO_bot.
Proof. reflexivity. Qed.

Lemma interpret_operand_acceptance s names value source :
  closed_operand_typing s value (interpret_operand_type names source) =
    value_typing s names value source.
Proof.
  destruct source as [number|vector|reference|];
    unfold interpret_operand_type, close_operand_type, value_typing; try reflexivity.
  destruct (gc_type_context.close_value_type names 0 (T_ref reference));
    reflexivity.
Qed.

Lemma unresolved_operand_uninhabited s names source :
  close_operand_type names source = None ->
  forall value, value_typing s names value source = false.
Proof.
  intros Missing value. rewrite <-interpret_operand_acceptance.
  unfold interpret_operand_type. rewrite Missing. reflexivity.
Qed.

Lemma interpret_results_acceptance s names values source :
  closed_operands_typing s values (interpret_operand_results names source) =
    values_typing s names values source.
Proof.
  revert source. induction values; destruct source; simpl; auto.
  rewrite interpret_operand_acceptance, IHvalues. reflexivity.
Qed.

Lemma interpret_value_subtyping registry names actual expected :
  value_subtyping actual expected = true ->
  closed_stack_value_subtyping registry
    (interpret_operand_type names actual) (interpret_operand_type names expected).
Proof.
  unfold value_subtyping. intro Subtype.
  apply orb_true_iff in Subtype as [Same|Bottom].
  - assert (Equal : actual = expected) by exact (elimT eqP Same).
    subst. apply csv_refl.
  - assert (Equal : actual = T_bot) by exact (elimT eqP Bottom).
    subst. apply csv_bot.
Qed.

Lemma interpret_results_subtyping registry names actual expected :
  values_subtyping actual expected = true ->
  closed_stack_results_subtyping registry
    (interpret_operand_results names actual) (interpret_operand_results names expected).
Proof.
  revert expected. induction actual; destruct expected; simpl;
    intro Subtype; try discriminate; constructor.
  - apply andb_true_iff in Subtype as [Head _].
    now apply interpret_value_subtyping.
  - apply andb_true_iff in Subtype as [_ Tail]. now apply IHactual.
Qed.

Lemma interpret_instr_subtyping registry names actual expected :
  instr_subtyping actual expected ->
  closed_instr_subtyping registry
    (interpret_instr_type names actual) (interpret_instr_type names expected).
Proof.
  destruct actual as [inputs outputs], expected as [inputs' outputs'].
  intros [prefix [prefix' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  unfold interpret_instr_type, interpret_operand_results, closed_instr_subtyping.
  rewrite !List.map_app.
  exists (List.map (interpret_operand_type names) prefix),
    (List.map (interpret_operand_type names) prefix'),
    (List.map (interpret_operand_type names) isub),
    (List.map (interpret_operand_type names) osub).
  repeat split; try reflexivity; now apply interpret_results_subtyping.
Qed.

Lemma close_concrete_operand names source concrete :
  gc_type_context.close_value_type names 0 source = Some concrete ->
  close_operand_type names source = Some (CO_value concrete).
Proof.
  destruct source as [number|vector|reference|]; intro Closed; try discriminate.
  - simpl in Closed. inversion Closed. reflexivity.
  - simpl in Closed. inversion Closed. reflexivity.
  - change (option_map CO_value
      (gc_type_context.close_value_type names 0 (T_ref reference)) =
        Some (CO_value concrete)).
    now rewrite Closed.
Qed.

Lemma close_operand_result_append names left right cleft cright :
  close_operand_result_type names left = Some cleft ->
  close_operand_result_type names right = Some cright ->
  close_operand_result_type names (left ++ right) = Some (cleft ++ cright).
Proof.
  unfold close_operand_result_type. rewrite <-!those_those0.
  revert cleft. induction left as [|t left IH]; intros cleft Left Right.
  - inversion Left; subst. exact Right.
  - cbn [List.map those0] in Left.
    destruct (close_operand_type names t) as [head|] eqn:Head; [|discriminate].
    destruct (those0 (List.map (close_operand_type names) left))
      as [tail|] eqn:Tail; [|discriminate].
    inversion Left; subst. cbn [List.app List.map those0].
    rewrite Head, (IH _ (Logic.eq_refl _) Right). reflexivity.
Qed.

Lemma close_concrete_results names source concrete :
  close_result_type names source = Some concrete ->
  close_operand_result_type names source = Some (lift_closed_result_type concrete).
Proof.
  unfold close_result_type, close_operand_result_type.
  rewrite <-!those_those0. revert concrete.
  induction source as [|t source IH]; intros concrete Closed.
  - inversion Closed. reflexivity.
  - cbn [List.map those0] in Closed |- *.
    destruct (gc_type_context.close_value_type names 0 t) as [head|] eqn:Head;
      [|discriminate].
    destruct (those0 (List.map (gc_type_context.close_value_type names 0) source))
      as [tail|] eqn:Tail; [|discriminate].
    inversion Closed; subst.
    rewrite (close_concrete_operand _ _ _ Head), (IH _ (Logic.eq_refl _)). reflexivity.
Qed.

Lemma closed_operand_results_interpret names source closed :
  close_operand_result_type names source = Some closed ->
  interpret_operand_results names source = closed.
Proof.
  unfold close_operand_result_type, interpret_operand_results.
  rewrite <-those_those0. revert closed.
  induction source as [|t source IH]; intros closed Closed.
  - inversion Closed. reflexivity.
  - cbn [List.map those0] in Closed |- *.
    destruct (close_operand_type names t) as [head|] eqn:Head; [|discriminate].
    destruct (those0 (List.map (close_operand_type names) source))
      as [tail|] eqn:Tail; [|discriminate].
    inversion Closed; subst.
    unfold interpret_operand_type at 1.
    rewrite Head, (IH _ (Logic.eq_refl _)). reflexivity.
Qed.

Lemma interpret_closed_signature names signature closed :
  gc_type_context.close_function_type names 0 signature = Some closed ->
  interpret_instr_type names signature = lift_closed_function_type closed.
Proof.
  destruct signature as [inputs outputs], closed as [cinputs coutputs].
  unfold gc_type_context.close_function_type.
  destruct (those0 (List.map (gc_type_context.close_value_type names 0) inputs))
    as [ins|] eqn:Inputs; [|discriminate].
  destruct (those0 (List.map (gc_type_context.close_value_type names 0) outputs))
    as [outs|] eqn:Outputs; [|discriminate].
  intro Equal. inversion Equal; subst.
  unfold interpret_instr_type, lift_closed_function_type.
  f_equal; apply closed_operand_results_interpret; apply close_concrete_results;
    unfold close_result_type; rewrite <-those_those0; assumption.
Qed.

Lemma closed_operand_subtyping_refl registry operands :
  closed_stack_results_subtyping registry operands operands.
Proof. induction operands; constructor; auto using csv_refl. Qed.

Lemma closed_operand_subtyping_trans registry a b c :
  closed_stack_results_subtyping registry a b ->
  closed_stack_results_subtyping registry b c ->
  closed_stack_results_subtyping registry a c.
Proof.
  intros First. revert c. induction First; intros c Last; inversion Last; subst.
  - constructor.
  - constructor; [eapply csv_trans; eauto|exact (IHFirst _ H4)].
Qed.

Lemma concrete_not_below_bottom registry a b :
  closed_stack_value_subtyping registry a b ->
  b = CO_bot -> a = CO_bot.
Proof.
  intro Subtype. induction Subtype; intro Bottom; try discriminate; auto.
Qed.

Lemma operand_subtyping_reflect registry actual expected :
  canonical_registry_valid registry ->
  closed_stack_value_subtyping registry (CO_value actual) expected ->
  closed_value_valid registry actual ->
  exists concrete, expected = CO_value concrete /\
    closed_value_valid registry concrete /\
    closed_value_matchesb registry actual concrete = true.
Proof.
  intros Registry Subtype.
  remember (CO_value actual) as operand eqn:Operand in Subtype.
  revert actual Operand. induction Subtype; intros actual Operand Valid; subst.
  - exists actual. split; [reflexivity|]. split; [exact Valid|].
    apply closed_value_matchesb_correct; [exact (proj1 (proj2 Registry))|].
    now apply closed_value_matches_refl_valid.
  - discriminate.
  - inversion Operand; subst a.
    exists b. split; [reflexivity|]. split; [|exact H].
    apply closed_value_validb_correct.
    apply (proj1 (closed_value_matchesb_validity _ _ _
      (proj1 (proj2 Registry)) H)).
    now apply closed_value_validb_correct.
  - destruct (IHSubtype1 _ (Logic.eq_refl _) Valid) as [middle [Middle [MiddleValid First]]].
    destruct (IHSubtype2 _ Middle MiddleValid) as [last [Last [LastValid Second]]].
    exists last. split; [exact Last|]. split; [exact LastValid|].
    apply closed_value_matchesb_correct; [exact (proj1 (proj2 Registry))|].
    eapply closed_value_matches_trans; [exact Registry| |].
    + exact (proj1 (closed_value_matchesb_correct _ _ _ (proj1 (proj2 Registry))) First).
    + exact (proj1 (closed_value_matchesb_correct _ _ _ (proj1 (proj2 Registry))) Second).
Qed.

Lemma operand_subtyping_acceptance s value actual expected :
  canonical_registry_valid s.(s_types) ->
  closed_operand_typing s value actual = true ->
  closed_stack_value_subtyping s.(s_types) actual expected ->
  closed_operand_typing s value expected = true.
Proof.
  destruct actual as [actual|]; [|discriminate].
  intros Registry Value Subtype.
  assert (Valid : closed_value_valid (s_types s) actual).
  { unfold closed_operand_typing, closed_value_typing in Value.
    destruct (typeof_closed_value s value); [|discriminate].
    apply andb_true_iff in Value as [Both _].
    apply andb_true_iff in Both as [_ Valid].
    now apply closed_value_validb_correct. }
  destruct (operand_subtyping_reflect _ _ _ Registry Subtype Valid)
    as [concrete [-> [Expected Match]]].
  eapply closed_value_typing_subsumption; eauto.
  now apply closed_value_validb_correct.
Qed.

End Operands.
