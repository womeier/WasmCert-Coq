(** Regression for compositionality of the source-entry closing boundary.
    This is about the mechanization's internal source bottom, not a claim
    about an executable Wasm module or the WebAssembly specification. *)
From Wasm Require Import closed_source_translation closed_operand_properties common subtyping_properties.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Stdlib Require Import Program.Equality List NArith.

Set Implicit Arguments.
Unset Strict Implicit.

Section Regression.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Local Lemma source_empty_types C inputs outputs :
  be_typing C nil (Tf inputs outputs) -> values_subtyping inputs outputs.
Proof.
  move => Typed. gen_ind_subst Typed => //; extract_premise.
  - by destruct es.
  - unfold instr_subtyping in *. by extract_premise; subst.
Qed.

Local Lemma source_subtype_bot a :
  value_subtyping a T_bot -> a = T_bot.
Proof.
  unfold value_subtyping. move/orP => [/eqP Same|/eqP Same]; exact Same.
Qed.

Local Lemma source_subtypes_contain_bot actual expected :
  values_subtyping actual expected ->
  List.In T_bot expected -> List.In T_bot actual.
Proof.
  move: expected. induction actual; destruct expected => //=.
  move/andP => [Head Tail] [Same|Member].
  - subst v. left. now apply source_subtype_bot.
  - right. exact (IHactual _ Tail Member).
Qed.

Local Lemma select_bot_consumes_bot C inputs outputs :
  be_typing C [::BI_select (Some [::T_bot])] (Tf inputs outputs) ->
  List.In T_bot inputs.
Proof.
  move => Typed.
  gen_ind_subst Typed => //=; try by left.
  - inversion Econs; subst. by left.
  - extract_listn; extract_premise.
    apply source_empty_types in Typed1.
    eapply source_subtypes_contain_bot; eauto.
  - unfold instr_subtyping in H. extract_premise; subst.
    apply List.in_or_app. right.
    eapply source_subtypes_contain_bot; eauto.
Qed.

Local Lemma closed_source_has_no_bot names source closed :
  close_result_type names source = Some closed ->
  ~ List.In T_bot source.
Proof.
  unfold close_result_type. rewrite <-those_those0.
  move: closed. induction source as [|t source IH] => closed Closed; first by [].
  cbn [List.map those0] in Closed.
  destruct (gc_type_context.close_value_type names 0 t) as [ct|] eqn:Head;
    last discriminate.
  destruct (those0 (List.map (gc_type_context.close_value_type names 0) source))
    as [tail|] eqn:Tail; last discriminate.
  move => [Same|Member].
  - subst t. discriminate.
  - exact (IH _ (Logic.eq_refl _) Member).
Qed.

Local Lemma source_bot_select_does_not_close C signature closed :
  be_typing C [::BI_select (Some [::T_bot])] signature ->
  gc_type_context.close_function_type C.(tc_defined_types) 0 signature = Some closed ->
  False.
Proof.
  destruct signature as [inputs outputs], closed as [cinputs coutputs].
  move => Typed Closed.
  unfold gc_type_context.close_function_type in Closed.
  destruct (those0 (List.map (gc_type_context.close_value_type (tc_defined_types C) 0) inputs))
    as [ci|] eqn:Inputs; last discriminate.
  destruct (those0 (List.map (gc_type_context.close_value_type (tc_defined_types C) 0) outputs));
    last discriminate.
  have Inputs' : close_result_type (tc_defined_types C) inputs = Some ci.
  { unfold close_result_type. rewrite <-those_those0. exact Inputs. }
  exact (closed_source_has_no_bot Inputs' (select_bot_consumes_bot Typed)).
Qed.

Definition closed_empty_context : closed_t_context :=
  Build_t_context nil nil nil nil nil nil nil nil nil None nil nil.

(** Before the separate operand domain, this sequence refuted composition
    inversion. It is now a positive regression with an explicit bottom middle;
    no storable value or serialized type was added. *)
Example closed_entry_with_internal_bottom s :
  e_typing s closed_empty_context
    [::AI_basic BI_unreachable; AI_basic (BI_select (Some [::T_bot]))]
    (Closed_ft nil [::CO_value (CV_num T_i32)]).
Proof.
  change (e_typing s closed_empty_context
    (to_e_list [::BI_unreachable; BI_select (Some [::T_bot])])
    (Closed_ft nil [::CO_value (CV_num T_i32)])).
  apply source_structural_entry with
    (source := empty_t_context) (signature := Tf nil [::T_num T_i32]);
    try reflexivity.
  eapply bet_subtyping with (t1s := nil) (t2s := [::T_bot]).
  - eapply bet_composition with (es := [::BI_unreachable]);
      [apply bet_unreachable|apply bet_select_Some].
  - exists nil, nil, nil, [::T_num T_i32].
    repeat split; reflexivity.
Qed.

Theorem closed_bottom_composition_middle s :
  exists middle,
    e_typing s closed_empty_context [::AI_basic BI_unreachable]
      (Closed_ft nil middle) /\
    e_typing s closed_empty_context [::AI_basic (BI_select (Some [::T_bot]))]
      (Closed_ft middle [::CO_value (CV_num T_i32)]).
Proof.
  exists [::CO_bot; CO_bot; CO_value (CV_num T_i32)].
  split.
  - change (e_typing s closed_empty_context (to_e_list [::BI_unreachable])
      (Closed_ft nil [::CO_bot; CO_bot; CO_value (CV_num T_i32)])).
    apply ety_a. apply cbet_unreachable.
  - eapply ety_subtyping with
      (t1s := [::CO_bot; CO_bot; CO_value (CV_num T_i32)])
      (t2s := [::CO_bot]).
    + change (e_typing s closed_empty_context
        (to_e_list [::BI_select (Some [::T_bot])])
        (Closed_ft [::CO_bot; CO_bot; CO_value (CV_num T_i32)] [::CO_bot])).
      apply ety_a. apply cbet_select. reflexivity.
    + exists nil, nil, [::CO_bot; CO_bot; CO_value (CV_num T_i32)],
        [::CO_value (CV_num T_i32)].
      repeat split => //.
      * apply closed_operand_subtyping_refl.
      * constructor; [apply csv_bot|constructor].
Qed.

Theorem closed_entry_bottom_composes s :
  exists C left right inputs outputs,
    e_typing s C (left ++ right) (Closed_ft inputs outputs) /\
    exists middle,
      e_typing s C left (Closed_ft inputs middle) /\
      e_typing s C right (Closed_ft middle outputs).
Proof.
  exists closed_empty_context, [::AI_basic BI_unreachable],
    [::AI_basic (BI_select (Some [::T_bot]))], nil, [::CO_value (CV_num T_i32)].
  split.
  - apply closed_entry_with_internal_bottom.
  - apply closed_bottom_composition_middle.
Qed.

End Regression.
