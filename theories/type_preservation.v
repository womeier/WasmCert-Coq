(** Proof of preservation **)

From Wasm Require Export typing_inversion tactic.
From Wasm Require Import gc_declaration_typing gc_declaration_typing_properties.
From Wasm Require Import gc_closed_runtime_properties.
From Wasm Require Import gc_runtime_type_properties.
From Wasm Require Import gc_function_subtyping_properties.
From Wasm Require Import closed_typing_properties.
From Wasm Require Import closed_source_translation.
From Wasm Require Import closed_context_properties.
From Wasm Require Import closed_bulk_properties.
From Wasm Require Import closed_operand_properties.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Stdlib Require Import Program.Equality ZArith Lia.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.

(* Equality for the stateful parts (instances) of the typing context *)
Definition closed_inst_match (C C' : closed_t_context) : bool :=
  (C.(tc_defined_types) == C'.(tc_defined_types)) &&
  (C.(tc_types) == C'.(tc_types)) &&
  (C.(tc_funcs) == C'.(tc_funcs)) &&
  ((C.(tc_tables) : list closed_table_type) == (C'.(tc_tables) : list closed_table_type)) &&
  (C.(tc_mems) == C'.(tc_mems)) &&
  ((C.(tc_globals) : list closed_global_type) == (C'.(tc_globals) : list closed_global_type)) &&
  (C.(tc_elems) == C'.(tc_elems)) &&
  (C.(tc_datas) == C'.(tc_datas)) &&
  (C.(tc_refs) == C'.(tc_refs)).

Definition inst_match (C : t_context) (C' : closed_t_context) : bool :=
  match close_t_context C with
  | Some closed => closed_inst_match closed C'
  | None => false
  end.

Lemma inst_match_defined_types C C' :
  inst_match C C' -> tc_defined_types C = tc_defined_types C'.
Proof.
  unfold inst_match.
  destruct (close_t_context C) as [closed|] eqn:Closed; last discriminate.
  move => Match. unfold closed_inst_match in Match; remove_bools_options.
  by rewrite -(close_context_names _ _ Closed).
Qed.

Lemma inst_match_metadata source C :
  inst_match source C ->
  exists base, close_t_context source = Some base /\
    tc_globals base = tc_globals C /\ tc_tables base = tc_tables C /\
    tc_mems base = tc_mems C /\ tc_elems base = tc_elems C /\
    tc_datas base = tc_datas C.
Proof.
  unfold inst_match.
  destruct (close_t_context source) as [base|] eqn:Closed; last discriminate.
  move => Match. unfold closed_inst_match in Match; remove_bools_options.
  exists base. by repeat split.
Qed.

Lemma inst_match_global_operand s source C primitive index raw value :
  inst_match source C ->
  close_t_context primitive = Some C ->
  lookup_N primitive.(tc_globals) index = Some raw ->
  is_mut raw ->
  value_typing s primitive.(tc_defined_types) value raw.(tg_t) ->
  exists actual,
    lookup_N source.(tc_globals) index = Some actual /\
    is_mut actual /\
    value_typing s source.(tc_defined_types) value actual.(tg_t).
Proof.
  move => Match Context Lookup Mutable Value.
  destruct (inst_match_metadata Match) as [base [Closed [Globals Rest]]].
  destruct (close_context_global_lookup Context Lookup)
    as [expected [Expected Slot]].
  rewrite -Globals in Slot.
  destruct (close_context_global_lookup_inv Closed Slot)
    as [actual [Actual ActualSlot]].
  destruct (close_global_type_agreement _ _ _ Expected) as [Mut Ref].
  destruct (close_global_type_agreement _ _ _ Actual) as [Mut' Ref'].
  exists actual. split; [exact ActualSlot|]. split.
  - unfold is_mut in *. by rewrite -Mut' Mut.
  - unfold value_typing in *. rewrite Ref' . by rewrite Ref in Value.
Qed.

Lemma inst_match_memory_lookup source C primitive index limit :
  inst_match source C ->
  close_t_context primitive = Some C ->
  lookup_N primitive.(tc_mems) index = Some limit ->
  lookup_N source.(tc_mems) index = Some limit.
Proof.
  move => Match Context Lookup.
  destruct (inst_match_metadata Match)
    as [base [Closed [Globals [Tables [Memories Rest]]]]].
  rewrite -(close_context_memories _ _ Closed) Memories
    (close_context_memories _ _ Context). exact Lookup.
Qed.

Lemma inst_match_table_operand s source C primitive index raw ref :
  inst_match source C ->
  close_t_context primitive = Some C ->
  lookup_N primitive.(tc_tables) index = Some raw ->
  value_typing s primitive.(tc_defined_types) (VAL_ref ref) (T_ref raw.(tt_elem_type)) ->
  exists actual,
    lookup_N source.(tc_tables) index = Some actual /\
    value_typing s source.(tc_defined_types) (VAL_ref ref) (T_ref actual.(tt_elem_type)).
Proof.
  move => Match Context Lookup Value.
  destruct (inst_match_metadata Match) as [base [Closed [Globals [Tables Rest]]]].
  destruct (close_context_table_lookup _ _ _ _ Context Lookup)
    as [expected [Expected Slot]].
  rewrite -Tables in Slot.
  destruct (close_context_table_lookup_inv _ _ _ _ Closed Slot)
    as [actual [Actual ActualSlot]].
  destruct (close_table_type_metadata _ _ _ Expected) as [_ Ref].
  destruct (close_table_type_metadata _ _ _ Actual) as [_ Ref'].
  have ExpectedValue := close_reference_type_value _ _ _ Ref.
  have ActualValue := close_reference_type_value _ _ _ Ref'.
  exists actual. split; [exact ActualSlot|].
  unfold value_typing in *. rewrite ActualValue.
  by rewrite ExpectedValue in Value.
Qed.

Lemma inst_match_updates source base locals labels returns :
  close_t_context source = Some base ->
  inst_match source (upd_local_label_return base locals labels returns).
Proof.
  move => Closed. rewrite /inst_match Closed /closed_inst_match /=.
  by repeat rewrite eq_refl.
Qed.

Lemma inst_match_table_read s inst source C primitive index offset raw ref :
  store_typing s ->
  inst_typing s inst = Some source ->
  inst_match source C ->
  close_t_context primitive = Some C ->
  lookup_N primitive.(tc_tables) index = Some raw ->
  stab_elem s inst index offset = Some ref ->
  value_typing s primitive.(tc_defined_types) (VAL_ref ref) (T_ref raw.(tt_elem_type)).
Proof.
  move => Store Instance Match Context Lookup Element.
  destruct (inst_match_metadata Match) as [base [Closed [Globals [Tables Rest]]]].
  destruct (close_context_table_lookup _ _ _ _ Context Lookup)
    as [expected [Expected Slot]].
  rewrite -Tables in Slot.
  destruct (close_context_table_lookup_inv _ _ _ _ Closed Slot)
    as [actual [Actual ActualSlot]].
  have Value := instance_table_element_typing _ _ _ _ _ _ _
    Store Instance ActualSlot Element.
  rewrite -(inst_typing_defined_types Instance) in Value.
  destruct (close_table_type_metadata _ _ _ Expected) as [_ Ref].
  destruct (close_table_type_metadata _ _ _ Actual) as [_ Ref'].
  have ExpectedValue := close_reference_type_value _ _ _ Ref.
  have ActualValue := close_reference_type_value _ _ _ Ref'.
  unfold value_typing in *. rewrite ExpectedValue.
  by rewrite ActualValue in Value.
Qed.

Lemma interpreted_value_emission s C names value source signature :
  value_typing s names value source ->
  closed_instr_subtyping (s_types s)
    (Closed_ft nil [::interpret_operand_type names source]) signature ->
  e_typing s C [::v_to_e value] signature.
Proof.
  rewrite -interpret_operand_acceptance.
  remember (interpret_operand_type names source) as operand eqn:Operand.
  destruct operand as [concrete|]; last discriminate.
  move => Value Subtype.
  by eapply et_value_typing'; eauto.
Qed.

Lemma inst_match_data_lookup source C primitive index data :
  inst_match source C ->
  close_t_context primitive = Some C ->
  lookup_N primitive.(tc_datas) index = Some data ->
  lookup_N source.(tc_datas) index = Some data.
Proof.
  move => Match Context Lookup.
  destruct (inst_match_metadata Match)
    as [base [Closed [Globals [Tables [Memories [Elems Datas]]]]]].
  rewrite -(close_context_datas _ _ Closed) Datas
    (close_context_datas _ _ Context). exact Lookup.
Qed.

(* Preservation for some less trivial operations *)
Lemma app_binop_type_preserve: forall op v1 v2 v,
    app_binop op v1 v2 = Some v ->
    typeof_num v = typeof_num v1.
Proof.
  move => op v1 v2 v.
  by elim: op; elim: v1; elim: v2 => //=; move => c1 c2 op H; destruct op; remove_bools_options.
Qed.

Lemma eval_cvt_type_preserve: forall op t1 t2 sx v1 v2,
    cvtop_valid t2 op t1 sx ->
    typeof_num v1 = t1 ->
    eval_cvt t2 op sx v1 = Some v2 ->
    typeof_num v2 = t2.
Proof.
  move => op t1 t2 sx v1 v2 Hcvtvalid Htype Heval.
  (* Just use brute force -- probably sledgehammer in some other theorem prover *)
  destruct op, t1, t2 => //; destruct sx as [[|] |] => //; cbn in Hcvtvalid => //; destruct v1 => //; simpl in * => //; by remove_bools_options => //=; inversion Heval.
Qed.

(* Typing of constants is not completely agnostic in Wasm 2.0 now -- since reference typings are dependent on the store. *)
Lemma et_const_agnostic: forall s C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es [ts1 ts2] HConst HType.
  apply const_es_exists in HConst as [vs Hve]; subst.
  invert_e_typing.
  eapply ety_subtyping; first apply et_values_typing.
  { exact H2_values. }
  done.
Qed.

Lemma v128_extract_lanes_typing: forall sh s vv vs,
    v128_extract_lanes sh s vv = vs ->
    List.Forall (fun v => typeof_num v = typeof_shape_unpacked sh) vs.
Proof.
  move => sh s vv vs; unfold v128_extract_lanes.
  destruct sh as [[] | []];
  destruct s; move => <-; apply List.Forall_map => /=;
  by apply List.Forall_forall.
Qed.
  
Lemma app_extract_vec_typing: forall sh os n v1,
    typeof_num (app_extract_vec sh os n v1) = typeof_shape_unpacked sh.
Proof.
  intros; unfold app_extract_vec.
  destruct (lookup_N _ _) eqn:Hlookup; last by destruct sh as [[] | []].
  by eapply Forall_lookup in Hlookup; last by eapply v128_extract_lanes_typing; eauto.
Qed.

(* It's better to just set `instr_subtyping` opaque and unset it when necessary, since most of the times we do not want to unfold this definition by simpl. But the simpl nomatch method doesn't prevent it from being unfolded for some reason. *)
Opaque instr_subtyping.

Theorem t_simple_preservation: forall s es es' C tf,
    e_typing s C es tf ->
    reduce_simple es es' ->
    e_typing s C es' tf.
Proof.
  move => s es es' C [ts1 ts2] HType HReduce.
  inversion HReduce; subst; (try by apply ety_trap); invert_e_typing; extract_premise => //;
    repeat (unify_closed_principal => //; unify_principal => //; resolve_e_typing => //).
  - (* Unop *)
    replace (typeof_num (app_unop op v)) with (typeof_num v); last by destruct op, v.
    by resolve_closed_subtyping.
  - (* Binop_success *)
    erewrite app_binop_type_preserve with (v1 := v1); eauto.
  - (* Cvtop *)
    erewrite eval_cvt_type_preserve; eauto.
    by resolve_closed_subtyping.
  - (* Extract_vec *)
    replace (typeof_num (app_extract_vec sh sx x v1)) with (typeof_shape_unpacked sh); first by resolve_closed_subtyping.
    by rewrite app_extract_vec_typing.
  - (* Select false: retain the selected concrete operand's derivation. *)
    fold_closed_subtyping.
    eapply et_value_typing'; first exact H2_value0.
    eapply closed_instr_trans; last exact Hprincipal.
    apply closed_instr_empty_input_intro. simpl.
    inversion H4; subst. constructor; [assumption|constructor].
  - (* Select true. *)
    fold_closed_subtyping.
    eapply et_value_typing'; first exact H2_value.
    eapply closed_instr_trans; last exact Hprincipal.
    apply closed_instr_empty_input_intro. simpl.
    constructor; [assumption|constructor].
  - (* Br *)
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite List.map_app in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal. exact Principal.
  - (* If true. *)
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite List.map_app in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal. exact Principal.
  - (* Br *)
    fold_closed_subtyping.
    eapply ety_subtyping; last exact Htisub.
    eapply et_composition'; last exact Hconjl0.
    eapply Lfilled_break_typing with (tss := nil) in Hconjl1;
      eauto => //=; try (by apply v_to_e_const); last by lias.
  - (* Br_if false *)
    fold_closed_subtyping.
    change (closed_instr_subtyping (s_types s) (Closed_ft nil nil) (Closed_ft ts1 ts2)).
    unfold interpret_operand_results in Htisub.
    rewrite List.map_app in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal.
    eapply closed_instr_trans; last exact Principal.
    pose proof (closed_instr_weakening (s_types s) nil nil
      (interpret_operand_results (tc_defined_types SourceContext) extr)) as Weak.
    now rewrite !List.app_nil_r in Weak.
  - (* Br_if true *)
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite List.map_app in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal.
    eapply ety_subtyping; last exact Principal.
    change (e_typing s C (to_e_list [::BI_br i])
      (interpret_instr_type (tc_defined_types SourceContext) (Tf extr extr))).
    eapply source_structural_entry; last exact HSourceContext.
    change extr with (nil ++ extr) at 1. apply bet_br. exact Hconjr.
  - (* Br_br_table *)
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite !List.map_app in Htisub.
    rewrite List.app_assoc in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal.
    rewrite <-List.map_app in Principal.
    eapply ety_subtyping; last exact Principal.
    change (e_typing s C (to_e_list [::BI_br j])
      (interpret_instr_type (tc_defined_types SourceContext) (Tf (extr ++ extr1) extr0))).
    eapply source_structural_entry; last exact HSourceContext.
    unfold lookup_N in *.
    eapply Forall_lookup with (x := j) (n := N.to_nat (Wasm_int.N_of_uint i32m c)) in Hconjr; eauto; last first.
    { rewrite List.nth_error_app1 => //.
      by lias.
    }
    {
      destruct Hconjr as [ts' [Hnth Hsub2]].
      eapply bet_subtyping with (t1s := extr ++ ts') (t2s := extr0).
      { by apply bet_br. }
      { Transparent instr_subtyping.
        unfold instr_subtyping. exists nil, nil, (extr ++ extr1), extr0.
        repeat split => //; by resolve_subtyping. }
    }
  - (* Br_br_table_oob *)
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite !List.map_app in Htisub.
    rewrite List.app_assoc in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal.
    rewrite <-List.map_app in Principal.
    eapply ety_subtyping; last exact Principal.
    change (e_typing s C (to_e_list [::BI_br i])
      (interpret_instr_type (tc_defined_types SourceContext) (Tf (extr ++ extr1) extr0))).
    eapply source_structural_entry; last exact HSourceContext.
    unfold lookup_N in *.
    eapply Forall_lookup with (x := i) (n := length iss) in Hconjr; eauto; last first.
    { rewrite List.nth_error_app2 => //.
      by rewrite Nat.sub_diag.
    }
    {
      destruct Hconjr as [ts' [Hnth Hsub2]].
      eapply bet_subtyping with (t1s := extr ++ ts') (t2s := extr0).
      { by apply bet_br. }
      { unfold instr_subtyping. exists nil, nil, (extr ++ extr1), extr0.
        repeat split => //; by resolve_subtyping. }
    }
  - (* Frame values retain their canonical operand subtyping chain. *)
    fold_closed_subtyping.
    change (closed_instr_subtyping (s_types s)
      (Closed_ft nil (lift_closed_result_type ts_values)) (Closed_ft ts1 ts2)).
    eapply closed_instr_trans; first exact H1_values.
    eapply closed_instr_trans; last exact Htisub.
    apply closed_instr_empty_input_intro. exact Hconjl2.
  - (* Local tee duplicates the same accepted canonical operand. *)
    fold_closed_subtyping.
    eapply ety_subtyping; last exact Hprincipal.
    apply (value_cons_e_typing H2_value).
    apply (value_cons_e_typing H2_value).
    eapply ety_subtyping with
      (t1s := [:: interpret_operand_type (tc_defined_types SourceContext) extr;
                   interpret_operand_type (tc_defined_types SourceContext) extr])
      (t2s := [:: interpret_operand_type (tc_defined_types SourceContext) extr]).
    + change (e_typing s C (to_e_list [::BI_local_set i])
        (interpret_instr_type (tc_defined_types SourceContext)
          (Tf [::extr; extr] [::extr]))).
      eapply source_structural_entry; last exact HSourceContext.
      apply bet_weakening with (ts := [::extr]) (ts1 := [::extr]) (ts2 := nil).
      by apply bet_local_set.
    + exists nil, nil, [::CO_value ts_value; CO_value ts_value],
        [::interpret_operand_type (tc_defined_types SourceContext) extr].
      repeat split => //; repeat constructor; assumption.
  - (* Frame return. *)
    eapply Frame_return_typing; try apply v_to_e_const; eauto.
    eapply ety_subtyping; last exact Htisub.
    eapply ety_frame; eauto.
    econstructor; eauto.
  - (* Non-null assertion retains the accepted operand. *)
    fold_closed_subtyping.
    change (e_typing s C [::v_to_e (VAL_ref ref)] (Closed_ft ts1 ts2)).
    eapply et_value_typing'; first exact H2_value.
    eapply closed_instr_trans; last exact Hprincipal.
    apply closed_instr_empty_input_intro. simpl.
    constructor; [exact H3|constructor].
  - (* Null branch removes only its operand. *)
    fold_closed_subtyping.
    change (closed_instr_subtyping (s_types s) (Closed_ft nil nil) (Closed_ft ts1 ts2)).
    unfold interpret_operand_results in Htisub.
    rewrite List.map_app in Htisub.
    pose proof (closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _)) as Principal.
    rewrite List.app_nil_r in Principal.
    eapply closed_instr_trans; last exact Principal.
    pose proof (closed_instr_weakening (s_types s) nil nil
      (interpret_operand_results (tc_defined_types SourceContext) extr)) as Weak.
    now rewrite !List.app_nil_r in Weak.
  - (* Non-null branch preserves the reference before branching. *)
    fold_closed_subtyping.
    change (e_typing s C ([::v_to_e (VAL_ref ref)] ++ [::AI_basic (BI_br x)])
      (Closed_ft ts1 ts2)).
    eapply et_composition'.
    + eapply et_value_typing'; eauto.
    + eapply ety_subtyping; last exact Htisub.
      change (e_typing s C (to_e_list [::BI_br x])
        (interpret_instr_type (tc_defined_types SourceContext)
          (Tf (extr ++ [::extr0]) extr))).
      eapply source_structural_entry; last exact HSourceContext.
      change (extr ++ [::extr0]) with (nil ++ (extr ++ [::extr0])) at 1.
      by apply bet_br.
  Unshelve.
  all: try by resolve_subtyping.
Qed.
Opaque instr_subtyping.

(* Various properties preserved by a store extension *)
Lemma ext_func_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_func_typing s a = Some tf ->
    ext_func_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_func_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_func in Hoption; eauto.
  by rewrite Hoption.
Qed.

Lemma ext_table_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_table_typing s a = Some tf ->
    exists tf', ext_table_typing s' a = Some tf' /\
    closed_table_type_extension tf tf'.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_table_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_table in Hoption; last by apply Hext.
  destruct Hoption as [tab [Hnth Htableext]].
  rewrite Hnth.
  unfold table_extension in Htableext.
  by remove_bools_options; exists (tableinst_type tab).
Qed.

Lemma ext_mem_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_mem_typing s a = Some tf ->
    exists tf', ext_mem_typing s' a = Some tf' /\
    limits_extension tf tf'.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_mem_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_mem in Hoption; last by apply Hext.
  destruct Hoption as [mem [Hnth Hmemext]].
  rewrite Hnth.
  unfold mem_extension in Hmemext.
  by remove_bools_options; exists (meminst_type mem).
Qed.

Lemma ext_global_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_global_typing s a = Some tf ->
    ext_global_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_global_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_global in Hoption; eauto.
  destruct Hoption as [? [Hnth Hglobalext]].
  rewrite Hnth.
  unfold global_extension in Hglobalext.
  remove_bools_options.
  by rewrite H.
Qed.

Lemma typeof_ref_extension: forall s s' v t,
    store_extension s s' ->
    typeof_ref s v = Some t ->
    typeof_ref s' v = Some t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  remove_bools_options.
  eapply ext_func_typing_extension in Hoption; eauto.
  by rewrite Hoption.
Qed.
  
Lemma value_typing_extension: forall s s' names v t,
    store_extension s s' ->
    value_typing s names v t ->
    value_typing s' names v t.
Proof.
  move => s s' names v t Hext Htype.
  unfold value_typing in *.
  destruct (gc_type_context.close_value_type names 0 t); last discriminate.
  by eapply closed_value_typing_store_extension; eauto.
Qed.
  
Lemma values_typing_extension: forall s s' names vs ts,
    store_extension s s' ->
    values_typing s names vs ts ->
    values_typing s' names vs ts.
Proof.
  move => s s' names; elim => //=.
  move => v vs IH => //=; case.
  - move => HST Hvt => //=; by apply values_typing_length in Hvt.
  - move => t ts Hext Hvt; unfold values_typing => /=.
    remove_bools_options.
    by erewrite value_typing_extension; eauto.
Qed.  

Lemma eleminst_typing_extension: forall s s' a a' tf,
    store_extension s s' ->
    elem_extension a a' ->
    eleminst_typing s a = Some tf ->
    eleminst_typing s' a' = Some tf.
Proof.
  move => s s' [et ei] [et' ei'] tf Hsext Hext Htype.
  unfold elem_extension in Hext; simpl in Hext.
  move/andP: Hext => [Elements /eqP Same]. subst et'.
  unfold eleminst_typing in Htype; simpl in Htype.
  change ((if closed_value_validb (s_types s) (closed_reference_value et) &&
    all (fun ref => closed_value_typing s (VAL_ref ref) (closed_reference_value et)) ei
    then Some et else None) = Some tf) in Htype.
  destruct (closed_value_validb (s_types s) (closed_reference_value et) &&
    all (fun ref => closed_value_typing s (VAL_ref ref) (closed_reference_value et)) ei)
    eqn:Check; last discriminate.
  injection Htype as <-.
  move/andP: Check => [Valid Refs].
  change ((if closed_value_validb (s_types s') (closed_reference_value et) &&
    all (fun ref => closed_value_typing s' (VAL_ref ref) (closed_reference_value et)) ei'
    then Some et else None) = Some et).
  rewrite (closed_value_validb_store_extension _ _ _ Hsext Valid) /=.
  have Refs' : all (fun ref => closed_value_typing s' (VAL_ref ref)
      (closed_reference_value et)) ei'.
  { move/orP: Elements => [/eqP <-|/eqP ->]; last reflexivity.
    apply/allP => ref Member. move/allP: Refs => Refs.
    eapply closed_value_typing_store_extension; [exact Hsext|exact (Refs ref Member)]. }
  by rewrite Refs'.
Qed.
  
Lemma datainst_typing_extension: forall s s' a a' tf,
    store_extension s s' ->
    data_extension a a' ->
    datainst_typing s a = Some tf ->
    datainst_typing s' a' = Some tf.
Proof.
  move => s s' d tf Hext Htype.
  by unfold datainst_typing in *.
Qed.

Lemma those_map_impl {T T1 T2: Type}: forall f g (r: T1 -> T2 -> bool) (l: list T) (l': list T1),
    (forall x y, f x = Some y -> exists z, g x = Some z /\ r y z) ->
    those (map f l) = Some l' ->
    exists l'', those (map g l) = Some l'' /\ all2 r l' l''.
Proof.
  move => f g r.
  setoid_rewrite <- those_those0.
  elim => //=; first by case => //; exists nil.
  move => x l IH l' Hr Hf.
  remove_bools_options.
  specialize (Hr x t Hoption) as Hz; destruct Hz as [z [Hg Hryz]].
  specialize (IH l0 Hr erefl) as Hl''; destruct Hl'' as [l'' [Hthose Hrall]].
  exists (z :: l'') => /=.
  by rewrite Hg Hthose Hryz Hrall => /=.
Qed.

Lemma instance_function_view_extension s s' names address source :
  store_extension s s' ->
  instance_function_view s names address source ->
  instance_function_view s' names address source.
Proof.
  move => Extension View.
  unfold instance_function_view in *.
  destruct (lookup_func_defined_type s address) as [id|] eqn:Identity; last discriminate.
  rewrite (store_extension_native_function_identity _ _ _ _ Extension Identity).
  destruct (gc_type_context.close_function_type names 0 source) as [expected|];
    last discriminate.
  destruct (gc_type_context.expand_function_type (s_types s) id) as [actual|] eqn:Expanded;
    last discriminate.
  rewrite (store_extension_function_expansion _ _ _ _ Extension Expanded).
  destruct actual as [aa ar], expected as [ea er]; simpl in *.
  destruct (store_extension_type_groups Extension) as [suffix Prefix].
  rewrite Prefix.
  move/andP: View => [Arguments Results].
  apply/andP; split; by apply closed_value_list_matchesb_prefix.
Qed.

Lemma instance_global_view_extension s s' names address source :
  store_extension s s' ->
  instance_global_view s names address source ->
  instance_global_view s' names address source.
Proof.
  move => Extension View.
  unfold instance_global_view in *.
  destruct (ext_global_typing s address) as [actual|] eqn:Actual; last discriminate.
  rewrite (ext_global_typing_extension Extension Actual).
  destruct (close_global_type names source) as [expected|]; last discriminate.
  destruct (store_extension_type_groups Extension) as [suffix Prefix].
  rewrite Prefix.
  move/andP: View => [/andP [/andP [/andP [Same AV] EV] Forward] Backward].
  apply/andP; split; last first.
  - destruct (tg_mut expected); [reflexivity|].
    exact (closed_value_matchesb_prefix _ suffix _ _ Backward).
  - apply/andP; split; last exact (closed_value_matchesb_prefix _ suffix _ _ Forward).
    apply/andP; split; last exact (closed_value_validb_prefix _ suffix _ EV).
    apply/andP; split; [exact Same|exact (closed_value_validb_prefix _ suffix _ AV)].
Qed.

Lemma instance_table_view_extension s s' names address source :
  store_extension s s' ->
  instance_table_view s names address source ->
  instance_table_view s' names address source.
Proof.
  move => Extension View.
  unfold instance_table_view in *.
  destruct (ext_table_typing s address) as [actual|] eqn:Actual; last discriminate.
  destruct (ext_table_typing_extension Extension Actual) as [later [Later Types]].
  rewrite Later.
  destruct (close_table_type names source) as [expected|]; last discriminate.
  destruct actual as [[amin amax] ar], later as [[lmin lmax] lr],
    expected as [[emin emax] er].
  unfold closed_table_type_extension, table_type_extension_gen, limits_extension in Types.
  simpl in *.
  move/andP: Types => [/eqP Same /andP [Minimum /eqP Maximum]].
  subst lr lmax.
  destruct (store_extension_type_groups Extension) as [suffix Prefix].
  rewrite Prefix.
  move/andP: View => [/andP [/andP [/andP [/andP [AV EV] Forward] Backward] Bound] MaximumBound].
  apply/andP; split; last exact MaximumBound.
  apply/andP; split; last first.
  - apply/N.leb_le. move/N.leb_le in Bound, Minimum. by lias.
  - apply/andP; split; last exact (closed_value_matchesb_prefix (s_types s) suffix
        (closed_reference_value er) (closed_reference_value ar) Backward).
    apply/andP; split; last exact (closed_value_matchesb_prefix (s_types s) suffix
        (closed_reference_value ar) (closed_reference_value er) Forward).
    apply/andP; split.
    + exact (closed_value_validb_prefix (s_types s) suffix (closed_reference_value ar) AV).
    + exact (closed_value_validb_prefix (s_types s) suffix (closed_reference_value er) EV).
Qed.

Lemma instance_element_view_extension s s' names address source :
  store_extension s s' ->
  instance_element_view s names address source ->
  instance_element_view s' names address source.
Proof.
  move => Extension View.
  unfold instance_element_view in *.
  destruct (lookup_N (s_elems s) address) as [element|] eqn:Element; last discriminate.
  destruct (close_reference_type names source) as [expected|]; last discriminate.
  destruct (eleminst_typing s element) as [actual|] eqn:Typed; last discriminate.
  destruct (store_extension_lookup_elem Extension Element) as [later [Later Elements]].
  rewrite Later (eleminst_typing_extension Extension Elements Typed).
  destruct (store_extension_type_groups Extension) as [suffix Prefix].
  rewrite Prefix.
  move/andP: View => [/andP [Valid Forward] Backward].
  apply/andP; split; last exact (closed_value_matchesb_prefix _ suffix _ _ Backward).
  apply/andP; split.
  - exact (closed_value_validb_prefix _ suffix _ Valid).
  - exact (closed_value_matchesb_prefix _ suffix _ _ Forward).
Qed.

Lemma all2_predicate_extension {A B} (old new : A -> B -> bool) xs ys :
  (forall x y, old x y -> new x y) ->
  all2 old xs ys -> all2 new xs ys.
Proof.
  move => Extend. move: ys.
  induction xs; destruct ys; simpl; try done.
  move/andP => [Head Tail]. apply/andP; split; eauto.
Qed.

Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i = Some C ->
    exists C',
      inst_typing s' i = Some C' /\
      context_extension C C'.
Proof.
  move => s s' i C HST HIT.
  pose proof (inst_typing_identities HIT) as Hidentities.
  pose proof (inst_typing_functypes_valid HIT) as Hvalid.
  destruct (store_extension_type_groups HST) as [suffix Hregistry].
  pose proof (gc_declaration_typing_properties.source_type_identitiesb_extension
    (s_types s) suffix _ _ _ Hidentities) as Hidentities'.
  assert (Hnew : gc_declaration_typing.source_type_identitiesb (s_types s')
    i.(inst_defined_types) i.(inst_types) i.(inst_defined_types) = true).
  { rewrite Hregistry. exact Hidentities'. }
  have Views :
    all2 (instance_function_view s i.(inst_defined_types)) i.(inst_funcs) i.(inst_context).(tc_funcs) /\
    all2 (instance_table_view s i.(inst_defined_types)) i.(inst_tables) i.(inst_context).(tc_tables) /\
    all2 (instance_global_view s i.(inst_defined_types)) i.(inst_globals) i.(inst_context).(tc_globals) /\
    all2 (instance_element_view s i.(inst_defined_types)) i.(inst_elems) i.(inst_context).(tc_elems).
  { unfold inst_typing in HIT. by remove_bools_options. }
  destruct Views as [Functions [Tables [Globals Elements]]].
  have Functions' : all2 (instance_function_view s' i.(inst_defined_types))
      i.(inst_funcs) i.(inst_context).(tc_funcs).
  { eapply all2_predicate_extension with (old := instance_function_view s i.(inst_defined_types));
      eauto using instance_function_view_extension. }
  have Tables' : all2 (instance_table_view s' i.(inst_defined_types))
      i.(inst_tables) i.(inst_context).(tc_tables).
  { eapply all2_predicate_extension with (old := instance_table_view s i.(inst_defined_types));
      eauto using instance_table_view_extension. }
  have Globals' : all2 (instance_global_view s' i.(inst_defined_types))
      i.(inst_globals) i.(inst_context).(tc_globals).
  { eapply all2_predicate_extension with (old := instance_global_view s i.(inst_defined_types));
      eauto using instance_global_view_extension. }
  have Elements' : all2 (instance_element_view s' i.(inst_defined_types))
      i.(inst_elems) i.(inst_context).(tc_elems).
  { eapply all2_predicate_extension with (old := instance_element_view s i.(inst_defined_types));
      eauto using instance_element_view_extension. }
  unfold inst_typing in HIT |- *.
  rewrite Hvalid Hnew Functions' Tables' Globals' Elements' /=.
  remove_bools_options.
  (* Memories *)
  eapply those_map_impl with (g := ext_mem_typing s') (r := limits_extension) in Hoption; last first.
  { move => x y Hext.
    by eapply ext_mem_typing_extension in Hext; eauto.
  }
  destruct Hoption as [tms [Hthosem Hmr]]; rewrite Hthosem.
  (* Datas *)
  eapply those_map_impl in Hoption0; last first.
  { move => x y Hext.
    instantiate (3 := fun x =>
                        match lookup_N (s_datas s') x with
                        | Some ei => datainst_typing s' ei
                        | None => None
                        end
                ).
    remove_bools_options.
    eapply store_extension_lookup_data in Hoption; eauto.
    destruct Hoption as [data [Hnth Hdataext]].
    eapply datainst_typing_extension in Hdataext; eauto.
    exists y; split; last by apply eq_refl.
    by rewrite Hnth /= Hdataext.
  }
  destruct Hoption0 as [tds [Hthosed Hdeq]]; rewrite Hthosed.
  rewrite -eqseq_all in Hdeq; move/eqP in Hdeq; subst.
  eexists; split; first by eauto.
  unfold context_extension => /=; repeat rewrite eq_refl => /=.
  rewrite Hmr !andbT.
  apply reflexive_all2_same => table.
  unfold table_type_extension, table_type_extension_gen, limits_extension.
  by rewrite !eq_refl N.leb_refl.
Qed.  

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    exists C',
      frame_typing s' f C' /\
      context_extension C C'.
Proof.
  move => s s' f C HST HIT.
  unfold frame_typing in *.
  remove_bools_options.
  destruct HIT as [ts [-> Hvts]].
  specialize (inst_typing_extension HST Hoption) as [C' [Hit Hext]].
  erewrite -> inst_t_context_local_empty in *; eauto.
  rewrite cats0.
  exists (upd_local C' ts); split => //.
  - rewrite Hit.
    exists ts.
    eapply values_typing_extension in Hvts; eauto.
    rewrite Hvts.
    by erewrite inst_t_context_local_empty; eauto; by rewrite cats0.
  - unfold context_extension in *.
    by lias.
Qed.

(* If a program fragment enclosed can be well-typed when enclosed in a
   lh context, then it can be fragment-well-typed on its own with a
   corresponding update on the typing context. *)
Lemma lfilled_es_type_exists {k}: forall (lh: lholed k) es les s C tf,
    lfill lh es = les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Closed_ft t1s t2s).
Proof.
  elim.
  - move => vs es es' LI s C [ts1 ts2] <- /= Htype.
    invert_e_typing.
    exists (tc_labels C); repeat eexists => //=.
    uapply H1_comp0.
    by destruct C.
  - move => k' vs n es lh IH es' es'' LI s C [ts1 ts2] <- /= Htype.
    rewrite -cat1s in Htype.
    invert_e_typing.
    by edestruct IH; eauto.
Qed.

Lemma update_label_agree C C' lab:
  context_agree C C' ->
  context_agree (upd_label C lab) (upd_label C' lab).
Proof.
  unfold context_agree in *; destruct C, C'; simpl in *; intros; remove_bools_options; subst.
  by lias.
Qed.

Lemma context_agree_func_type C C' n ft:
  context_agree C C' ->
  lookup_N C.(tc_funcs) n = Some ft ->
  lookup_N C'.(tc_funcs) n = Some ft.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  eapply all2_nth_impl in H9 as [ft' [Hnth' Hfext]]; eauto.
  by unfold func_agree in Hfext; remove_bools_options; subst.
Qed.
  
Lemma context_agree_table_type C C' n tabt:
  context_agree C C' ->
  lookup_N C.(tc_tables) n = Some tabt ->
  exists tabt', lookup_N C'.(tc_tables) n = Some tabt' /\
             table_agree tabt tabt'.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  by eapply all2_nth_impl in H8 as [tabt' [Hnth' Htabext]]; eauto.
Qed.

Lemma context_agree_mem_type C C' n memt:
  context_agree C C' ->
  lookup_N C.(tc_mems) n = Some memt ->
  exists memt',
    lookup_N C'.(tc_mems) n = Some memt' /\
    mem_agree memt memt'.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  by eapply all2_nth_impl in H7 as [memt' [Hnth' Hmemext]]; eauto.
Qed.

Lemma context_agree_global_type C C' n gt:
  context_agree C C' ->
  lookup_N C.(tc_globals) n = Some gt ->
  lookup_N C'.(tc_globals) n = Some gt.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  eapply all2_nth_impl in H6 as [gt' [Hnth' Hfext]]; eauto.
  by unfold global_agree in Hfext; remove_bools_options; subst.
Qed.

Ltac rewrite_context_agree:=
  repeat match goal with
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_types ?C' ] =>
        replace (tc_types C') with (tc_types C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_elems ?C' ] =>
        replace (tc_elems C') with (tc_elems C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_datas ?C' ] =>
        replace (tc_datas C') with (tc_datas C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_locals ?C' ] =>
        replace (tc_locals C') with (tc_locals C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_labels ?C' ] =>
        replace (tc_labels C') with (tc_labels C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_return ?C' ] =>
        replace (tc_return C') with (tc_return C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_refs ?C' ] =>
        replace (tc_refs C') with (tc_refs C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | _ : is_true (context_agree ?C ?C') |- is_true (context_agree (upd_label ?C ?lab) (upd_label ?C' ?lab)) =>
        by apply update_label_agree
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C'.(tc_tables) ?n = Some ?t,
      Helemtype: (tt_elem_type ?t) = ?tref |- _ =>
      let Htableagree := fresh "Htableagree" in
      specialize (context_agree_table_type Hext Hnth) as [tabt_ctxext [Hnth_ctxext Htableagree]]; unfold table_agree in Htableagree; remove_bools_options; subst; try rewrite - Htableagree
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_tables) ?n = Some ?t |- _ =>
      specialize (context_agree_table_type Hext Hnth) as [tabt_ctxext [Hnth_ctxext Htableagree]]; unfold table_agree in *; remove_bools_options; subst
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_mems) ?n = Some ?t |- _ =>
      (* Not creating fresh names to make sure this only triggers once -- a bit stupid *)
      specialize (context_agree_mem_type Hext Hnth) as [memt_ctxext [Hnth_ctxext Hmemagree]]
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_funcs) ?n = Some ?t |- _ =>
      specialize (context_agree_func_type Hext Hnth) as Hnthfunc'
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_globals) ?n = Some ?t |- _ =>
      specialize (context_agree_global_type Hext Hnth) as Hnthglobal'
    end.

(* Curiously, this lemma works in both directions *)
Lemma context_agree_be_typing: forall C C' es tf,
    context_agree C C' ->
    be_typing C es tf ->
    be_typing C' es tf.
Proof.
  move => C C' es tf Hext Hetype.
  move: C' Hext.
  induction Hetype; move => C' Hext; (try by econstructor; eauto); try (by econstructor; eauto; rewrite_context_agree; eauto); try (by rewrite_context_agree; econstructor; eauto; rewrite_context_agree).
  (* block *)
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    by apply IHHetype; rewrite_context_agree.
  (* loop *)
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    by apply IHHetype; by rewrite_context_agree.
  (* if *)
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    + apply IHHetype1; by rewrite_context_agree.
    + apply IHHetype2; by rewrite_context_agree.
  (* call_indirect *)
  - rewrite_context_agree.
    econstructor; eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
  (* return_call_indirect *)
  - rewrite_context_agree.
    econstructor; eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
    + by rewrite_context_agree.
  (* table_copy *)
  - rewrite_context_agree.
    eapply context_agree_table_type in H as [tabt [Hnth Hagree]]; eauto; unfold table_agree in *; move/eqP in Hagree.
    econstructor.
    + by apply Hnth.
    + reflexivity.
    + by apply Hnth_ctxext.
    + by rewrite - Hagree - H2.
  (* table init *)
  - rewrite_context_agree.
    econstructor; first by eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
Qed.

(* Two agreeing contexts respect typing of each other *)
Lemma context_agree_defined_types C C' :
  context_agree C C' -> tc_defined_types C = tc_defined_types C'.
Proof.
  unfold context_agree. by move => Agree; remove_bools_options.
Qed.

Lemma closed_basic_relimit registry C es tf :
    closed_be_typing registry C es tf ->
    forall limits memories,
    length memories = length C.(tc_mems) ->
    closed_be_typing registry (relimit_context C limits memories) es tf.
Proof.
  move => Typed. induction Typed; move => limits memories Length;
    try solve [econstructor; eauto].
  - change (closed_be_typing registry (relimit_context C limits memories)
      [::instruction] (interpret_instr_type
        (tc_defined_types (relimit_context source limits memories)) signature)).
    eapply close_be_typing; eauto.
    + eapply context_agree_be_typing; last exact H.
      apply source_context_agree_relimit.
      by rewrite -(close_context_memories _ _ H1).
    + by apply close_context_relimit.
  - change (tc_defined_types C) with
      (tc_defined_types (relimit_context C limits memories)).
    apply cbet_block; [exact H|]. apply IHTyped. exact Length.
  - change (tc_defined_types C) with
      (tc_defined_types (relimit_context C limits memories)).
    apply cbet_loop; [exact H|]. apply IHTyped. exact Length.
  - change (tc_defined_types C) with
      (tc_defined_types (relimit_context C limits memories)).
    apply cbet_if; [exact H| |].
    + apply IHTyped1. exact Length.
    + apply IHTyped2. exact Length.
Qed.

Lemma context_agree_typing: forall s C C' es tf,
    closed_context_agree C C' ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es tf [limits [memories [Length ->]]] Hetype.
  move: limits memories Length.
  induction Hetype; move => limits memories Length;
    try solve [econstructor; eauto].
  - apply ety_a. by apply closed_basic_relimit.
  - eapply ety_label; [by apply IHHetype1| |exact H].
    apply IHHetype2. exact Length.
Qed.

(* Context extension is a special case of context agreement. *)
Lemma context_extension_typing: forall s C C' es tf,
    closed_context_agree C C' ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  intros.
  by eapply context_agree_typing; eauto.
Qed.

(* A valid store extension preserves the fragment typing relation. *)
Lemma closed_frame_typing_extension s later frame C :
    store_extension s later ->
    closed_frame_typing s frame C ->
    exists C', closed_frame_typing later frame C' /\ closed_context_agree C C'.
Proof.
  move => Extension [source [base [locals [Instance [Context [-> Values]]]]]].
  destruct (inst_typing_extension Extension Instance) as [source' [Instance' Agree]].
  let limits := constr:(List.map tt_limits (tc_tables source')) in
  let memories := constr:(tc_mems source') in
  exists (relimit_context (upd_local base (locals ++ tc_locals base)) limits memories).
  split.
  - exists source', (relimit_context base (List.map tt_limits (tc_tables source'))
      (tc_mems source')), locals.
    split; [exact Instance'|]. split.
    + have Closed := close_context_relimit
        (List.map tt_limits (tc_tables source')) (tc_mems source') Context.
      rewrite -(context_extension_relimit Agree) in Closed. exact Closed.
    + split; [reflexivity|]. by eapply closed_values_extension; eauto.
  - exists (List.map tt_limits (tc_tables source')), (tc_mems source').
    split; [|reflexivity].
    simpl. rewrite (close_context_memories _ _ Context).
    by apply context_extension_memory_length.
Qed.

Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es tf ->
    e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 HST2 Hext HType. move: s' HST1 HST2 Hext.
  eapply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_typing s' ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs th ts (_ : thread_typing s rs th ts) => forall s',
             store_typing s ->
             store_typing s' ->
             store_extension s s' ->
             thread_typing s' rs th ts); clear HType s C es tf.
  (* basic *)
  - move=> s C bes tf HType s' HST1 HST2 Hext.
    apply ety_a.
    destruct (store_extension_type_groups Hext) as [suffix Prefix].
    rewrite Prefix. by apply closed_basic_typing_prefix.
  - move=> s C s' HST1 HST2 Hext. apply ety_empty.
  (* composition *)
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  (* subtyping *)
  - move=> s C es t1s t2s t1s' t2s' HType IHHType Hsub s' HST1 HST2 Hext.
    eapply ety_subtyping; [by apply IHHType|].
    destruct (store_extension_type_groups Hext) as [suffix Prefix].
    rewrite Prefix. by apply closed_instr_subtyping_prefix.
  (* trap *)
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_trap.
  - move=> s C number s' HST1 HST2 Hext. apply ety_num.
  - move=> s C vector s' HST1 HST2 Hext. apply ety_vec.
  (* ref_extern *)
  - move=> s C a t Typed s' HST1 HST2 Hext.
    apply ety_ref_extern. by eapply closed_value_typing_store_extension; eauto.
  (* invoke *)
  - move=> s a C tf Hextfunc s' HST1 HST2 Hext.
    eapply ety_invoke; eauto => //.
    by eapply closed_function_view_extension; eauto.
  (* return_invoke *)
  - move => s a C ts1 ts2 ts3 ts4 Hextfunc Hret s' HST1 HST2 Hext.
    eapply ety_return_invoke; eauto.
    by eapply closed_function_view_extension; eauto.
  (* Label *)
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 HST2 Hext.
    by eapply ety_label => //; eauto.
  (* Frame *)
  - move=> s C n f es ts actual_ts HType IHHType Valid Match E s' HST1 HST2 Hext.
    apply ety_frame with (actual_ts := actual_ts) => //.
    + by eapply IHHType; try apply HST1 => //.
    + exact (proj1 HST2).
    + destruct (store_extension_type_groups Hext) as [suffix Prefix].
      rewrite Prefix. by apply closed_results_subtyping_prefix.
  - move=> s C n t Typed s' HST1 HST2 Hext.
    apply ety_ref_i31. by eapply closed_value_typing_store_extension; eauto.
  - move=> s C h t Typed s' HST1 HST2 Hext.
    apply ety_ref_null. by eapply closed_value_typing_store_extension; eauto.
  - move=> s C address t Typed s' HST1 HST2 Hext.
    apply ety_ref. by eapply closed_value_typing_store_extension; eauto.
  (* Thread *)
  - move=> s f es rs ts C C' HFType HContext HType IHHType s' HST1 HST2 Hext.
    eapply closed_frame_typing_extension in HFType; eauto.
    destruct HFType as [C'' [HFType Hcext]].
    eapply mk_thread_typing with (C := C''); eauto.
    apply context_extension_typing with (C := C') => //; last by apply IHHType.
    subst C'.
    destruct Hcext as [limits [memories [Length ->]]].
    exists limits, memories. by split.
Qed.

Lemma glob_extension_update_nth: forall sglobs n g g',
  List.nth_error sglobs n = Some g ->
  global_extension g g' ->
  all2 global_extension sglobs (set_nth g' sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_global_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + by apply global_extension_refl. 
    + by eapply IHn; eauto.
Qed.

Lemma write_bytes_gen_preserve_length: forall m pos len gen m',
  write_bytes_gen m pos len gen = Some m' ->
  memory.mem_length m = memory.mem_length m'.
Proof.
  move => m pos len gen m' Hwrite.
  unfold write_bytes_gen in Hwrite.
  by apply mem_update_gen_length in Hwrite.
Qed.

Lemma write_bytes_meminst_preserve_type: forall m pos len gen m',
  write_bytes_gen_meminst m pos len gen = Some m' ->
  meminst_type m = meminst_type m' /\
  mem_length m = mem_length m'.
Proof.
  move => m pos len gen m' Hwrite.
  unfold write_bytes_gen_meminst in Hwrite.
  remove_bools_options; split => //=.
  by eapply write_bytes_gen_preserve_length; eauto.
Qed.

Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
Qed.

(** Interaction among instruction operations, store extensions, and types **)
Lemma context_extension_func_typing: forall C C' x t,
    context_extension C C' ->
    func_typing C x t ->
    func_typing C' x t.
Proof.
  move => C C' x t Hcext Hft.
  unfold func_typing in *; destruct x; remove_bools_options.
  specialize (context_extension_agree Hcext) as Hagree.
  rewrite_context_agree.
  rewrite Hoption.
  destruct f; destruct Hft as [-> [Het Hdefault]]; repeat split => //.
  eapply context_agree_be_typing; last by eauto.
  unfold context_agree in *; remove_bools_options; destruct C, C'; subst; by lias.
Qed.
  
Lemma store_extension_funcinst_typing: forall s s' x t,
    store_extension s s' ->
    funcinst_typing s x t ->
    funcinst_typing s' x t.
Proof.
  move => s s' x t Hst Hft.
  unfold funcinst_typing in *; destruct Hft as [<- Hft]; remove_bools_options; split => //.
  destruct x => //; destruct Hft as [? Hft]; split => //.
  remove_bools_options.
  eapply inst_typing_extension in Hoption; last by apply Hst.
  destruct Hoption as [C' [Hit' Hcext]].
  rewrite Hit'.
  destruct Hft as [Function Defaults]. split.
  - by eapply context_extension_func_typing; eauto.
  - intro Absent.
    destruct (runtime_default_vals (s_types s) (inst_defined_types m)
      (modfunc_locals m0)) as [values|] eqn:Present; last by apply Defaults.
    destruct (store_extension_type_groups Hst) as [suffix Prefix].
    rewrite Prefix (runtime_default_vals_prefix _ suffix _ _ _ Present) in Absent.
    discriminate.
  by eapply store_extension_host_identity; eauto.
Qed.

Lemma store_extension_tableinst_typing: forall s s' x t,
    store_extension s s' ->
    tableinst_typing s x = Some t ->
    tableinst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold tableinst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  move/allP in Hif0.
  move/inP in Hin.
  apply Hif0 in Hin.
  by eapply closed_value_typing_store_extension in Hin; eauto.
Qed.

Lemma store_extension_meminst_typing: forall s s' x t,
    store_extension s s' ->
    meminst_typing s x = Some t ->
    meminst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  by unfold meminst_typing in *; destruct x; remove_bools_options.
Qed.

Lemma store_extension_globalinst_typing: forall s s' x t,
    store_extension s s' ->
    globalinst_typing s x = Some t ->
    globalinst_typing s' x = Some t.
Proof.
  move => s s' [gt gv] t Hst Ht.
  cbn [globalinst_typing] in Ht.
  destruct (closed_value_validb (s_types s) (tg_t gt)) eqn:Valid; last discriminate.
  destruct (closed_value_typing s gv (tg_t gt)) eqn:Typed; last discriminate.
  injection Ht as <-.
  cbn [globalinst_typing].
  by rewrite (closed_value_validb_store_extension _ _ _ Hst Valid)
    (closed_value_typing_store_extension _ _ _ _ Hst Typed).
Qed.

Lemma store_extension_eleminst_typing: forall s s' x t,
    store_extension s s' ->
    eleminst_typing s x = Some t ->
    eleminst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  eapply eleminst_typing_extension; eauto.
  apply elem_extension_refl.
Qed.

Lemma store_extension_datainst_typing: forall s s' x t,
    store_extension s s' ->
    datainst_typing s x = Some t ->
    datainst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  by unfold datainst_typing in *; destruct x; remove_bools_options.
Qed.

Lemma store_extension_funcs_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, funcinst_typing s x t) xs ->
    List.Forall (fun x => exists t, funcinst_typing s' x t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_funcinst_typing; eauto.
Qed.

Lemma store_extension_tables_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, tableinst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, tableinst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_tableinst_typing; eauto.
Qed.

Lemma store_extension_mems_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, meminst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, meminst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_meminst_typing; eauto.
Qed.

Lemma store_extension_globals_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, globalinst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, globalinst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_globalinst_typing; eauto.
Qed.

Lemma store_extension_elems_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, eleminst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, eleminst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_eleminst_typing; eauto.
Qed.

Lemma store_extension_datas_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, datainst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, datainst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_datainst_typing; eauto.
Qed.

Ltac resolve_store_extension :=
  repeat lazymatch goal with
  | |- context [ gc_type_context.canonical_registry_prefixb ?x ?x ] =>
      rewrite gc_type_context_properties.canonical_registry_prefixb_refl
  | |- context [ component_extension (@operations.func_extension _) ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := func_extension); last by apply func_extension_refl
  | |- context [ component_extension table_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := table_extension); last by apply table_extension_refl
  | |- context [ component_extension mem_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := mem_extension); last by apply mem_extension_refl
  | |- context [ component_extension global_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := global_extension); last by apply global_extension_refl
  | |- context [ component_extension elem_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := elem_extension); last by apply elem_extension_refl
  | |- context [ component_extension data_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := data_extension); last by apply data_extension_refl
    | _ => repeat rewrite andbT
    end; cbn.

Ltac resolve_store_typing :=
  repeat split;
  repeat lazymatch goal with
  | |- gc_declaration_typing.canonical_registry_validb _ = true => assumption
  | |- List.Forall (fun x => exists t, funcinst_typing ?s x t) _ =>
      by eapply store_extension_funcs_typing; eauto
  | |- List.Forall (fun x => exists t, tableinst_typing ?s x = Some t) _ =>
      by eapply store_extension_tables_typing; eauto
  | |- List.Forall (fun x => exists t, meminst_typing ?s x = Some t) _ =>
      by eapply store_extension_mems_typing; eauto
  | |- List.Forall (fun x => exists t, globalinst_typing ?s x = Some t) _ =>
      by eapply store_extension_globals_typing; eauto
  | |- List.Forall (fun x => exists t, eleminst_typing ?s x = Some t) _ =>
      by eapply store_extension_elems_typing; eauto
  | |- List.Forall (fun x => exists t, datainst_typing ?s x = Some t) _ =>
      by eapply store_extension_datas_typing; eauto
    end.

Lemma mutable_global_view_operand s names address source value actual :
  store_typing s ->
  instance_global_view s names address source ->
  ext_global_typing s address = Some actual ->
  is_mut source ->
  value_typing s names value source.(tg_t) ->
  actual.(tg_mut) = MUT_var /\ closed_value_typing s value actual.(tg_t).
Proof.
  move => Store View Actual Mutable Value.
  unfold instance_global_view in View. rewrite Actual in View.
  destruct (close_global_type names source) as [expected|] eqn:Closed; last discriminate.
  destruct (close_global_type_agreement _ _ _ Closed) as [Mutability Expected].
  move/eqP: Mutable => Mutable.
  have EM : tg_mut expected = MUT_var by rewrite Mutability Mutable.
  move/andP: View => [/andP [/andP [/andP [/eqP Same AV] EV] Forward] Backward].
  split; first by rewrite Same EM.
  unfold value_typing in Value. rewrite Expected in Value.
  rewrite EM in Backward.
  eapply closed_value_typing_subsumption; eauto.
  exact (store_typing_canonical_registry _ Store).
Qed.

Lemma table_view_operand s names address source ref actual :
  store_typing s ->
  instance_table_view s names address source ->
  ext_table_typing s address = Some actual ->
  value_typing s names (VAL_ref ref) (T_ref source.(tt_elem_type)) ->
  closed_value_typing s (VAL_ref ref) (closed_reference_value actual.(tt_elem_type)).
Proof.
  move => Store View Actual Value.
  unfold instance_table_view in View. rewrite Actual in View.
  destruct (close_table_type names source) as [expected|] eqn:Closed; last discriminate.
  destruct (close_table_type_metadata _ _ _ Closed) as [_ Reference].
  pose proof (close_reference_type_value _ _ _ Reference) as Expected.
  move/andP: View =>
    [/andP [/andP [/andP [/andP [AV EV] Forward] Backward] Minimum] Maximum].
  unfold value_typing in Value. rewrite Expected in Value.
  eapply closed_value_typing_subsumption; eauto.
  exact (store_typing_canonical_registry _ Store).
Qed.

Lemma supdate_glob_extension: forall s f i v s' C gt,
  store_typing s ->
  supdate_glob s (f_inst f) i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (f_inst f).(inst_defined_types) v (tg_t gt) ->
  lookup_N (tc_globals C) i = Some gt ->
  is_mut gt ->
  store_extension s s'.
Proof.
  move => s f i v s' C gt Hst Hupd Hinst Hvaltype Hnth Hmut.
  destruct (inst_typing_global_lookup_inv Hinst Hnth) as [address [View Address]].
  unfold supdate_glob, sglob_ind in Hupd. rewrite Address in Hupd; simpl in Hupd.
  unfold supdate_glob_s in Hupd.
  destruct (lookup_N (s_globals s) address) as [global|] eqn:Global; last discriminate.
  have Actual : ext_global_typing s address = Some global.(g_type).
  { unfold ext_global_typing. by rewrite Global. }
  destruct (mutable_global_view_operand Hst View Actual Hmut Hvaltype) as [Mutable _].
  injection Hupd as <-.
  unfold store_extension; simpl; resolve_store_extension.
  eapply component_extension_update; eauto; first by apply global_extension_refl.
  destruct global as [[mut type] old]; simpl in Mutable; subst mut.
  unfold global_extension; simpl. by rewrite eq_refl.
Qed.

Lemma supdate_glob_typing: forall s f i v s' C gt,
  store_typing s ->
  supdate_glob s (f_inst f) i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (f_inst f).(inst_defined_types) v (tg_t gt) ->
  lookup_N (tc_globals C) i = Some gt ->
  is_mut gt ->
  store_typing s'.
Proof.
  move => s f i v s' C gt Hst Hupd Hinst Hvaltype Hnth Hmut.
  assert (store_extension s s') as Hstext; first by eapply supdate_glob_extension; eauto.
  destruct (inst_typing_global_lookup_inv Hinst Hnth) as [address [View Address]].
  unfold supdate_glob, sglob_ind in Hupd. rewrite Address in Hupd; simpl in Hupd.
  unfold supdate_glob_s in Hupd.
  destruct (lookup_N (s_globals s) address) as [global|] eqn:Global; last discriminate.
  have Actual : ext_global_typing s address = Some global.(g_type).
  { unfold ext_global_typing. by rewrite Global. }
  destruct (mutable_global_view_operand Hst View Actual Hmut Hvaltype) as [_ Operand].
  have Operand' := closed_value_typing_store_extension _ _ _ _ Hstext Operand.
  have NewGlobal : globalinst_typing s' (Build_globalinst global.(g_type) v) =
      Some global.(g_type).
  { have Valid : closed_value_validb (s_types s') (tg_t (g_type global)).
    { unfold closed_value_typing in Operand'.
      destruct (typeof_closed_value s' v); last discriminate.
      by move/andP: Operand' => [/andP [_ Valid] _]. }
    cbn [globalinst_typing]. by rewrite Valid Operand'. }
  injection Hupd as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Het Hdt.
  eapply Forall_set.
  - by eapply store_extension_globals_typing; eauto.
  - by exists (g_type global).
  - unfold lookup_N in Global. apply nth_error_Some_length in Global. by lias.
Qed.
    
Lemma stab_update_extension: forall s f x i v s',
  store_typing s ->
  stab_update s (f_inst f) x i v = Some s' ->
  store_extension s s'.
Proof.
  move => s f x i v s' Hst Hupd.
  unfold stab_update in Hupd.
  destruct (lookup_N (inst_tables (f_inst f)) x) as [address|] eqn:Address;
    last discriminate.
  destruct (lookup_N (s_tables s) address) as [[descriptor elements]|] eqn:Table;
    last discriminate.
  unfold tab_size in Hupd. cbn [tableinst_elem] in Hupd.
  destruct (N.ltb i (N.of_nat (length elements))) eqn:Bound; last discriminate.
  injection Hupd as <-.
  unfold store_extension; simpl; resolve_store_extension.
  eapply component_extension_update; eauto; first by apply table_extension_refl.
  unfold table_extension, closed_table_type_extension, table_type_extension_gen,
    limits_extension, tab_size => /=.
  rewrite !eq_refl N.leb_refl /=.
  erewrite set_nth_length; first apply leqnn.
  move/N.ltb_lt in Bound. by lias.
Qed.

Lemma tableinst_typing_set s descriptor elements index ref typed :
  tableinst_typing s (Build_tableinst descriptor elements) = Some typed ->
  (index < length elements)%coq_nat ->
  closed_value_typing s (VAL_ref ref) (closed_reference_value descriptor.(tt_elem_type)) ->
  tableinst_typing s (Build_tableinst descriptor (set_nth ref elements index ref)) = Some typed.
Proof.
  move => Old Bound Value.
  cbn [tableinst_typing] in Old |- *.
  destruct (closed_ref_nullable (tt_elem_type descriptor) &&
    limit_valid_range (tt_limits descriptor) table_limit_bound) eqn:Shape; last discriminate.
  destruct (N.of_nat (length elements) == lim_min (tt_limits descriptor)) eqn:Size;
    last discriminate.
  destruct (all (fun ref => closed_value_typing s (VAL_ref ref)
    (closed_reference_value (tt_elem_type descriptor))) elements) eqn:Elements;
    last discriminate.
  have Length : length (set_nth ref elements index ref) = length elements.
  { apply set_nth_length. by lias. }
  rewrite Length Size.
  have Refs : all (fun value => closed_value_typing s (VAL_ref value)
    (closed_reference_value descriptor.(tt_elem_type))) (set_nth ref elements index ref).
  { apply list_all_forall => value Member.
    have Index : index < length elements by lias.
    destruct (set_nth_In Index Member) as [->|[position [_ Lookup]]]; first exact Value.
    move/allP: Elements => Elements.
    apply Elements. apply/inP. by apply List.nth_error_In in Lookup. }
  by rewrite Refs.
Qed.

Lemma stab_update_typing: forall s f x i v s' C tabt,
  store_typing s ->
  stab_update s (f_inst f) x i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (f_inst f).(inst_defined_types) (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_typing s'.
Proof.
  move => s f x i v s' C tabt Hst Hupd Hinst Hvaltype Hnth.
  assert (store_extension s s') as Hstext; first by eapply stab_update_extension; eauto.
  destruct (inst_typing_table_lookup_inv Hinst Hnth) as [address [View Address]].
  unfold stab_update in Hupd. rewrite Address in Hupd.
  destruct (lookup_N (s_tables s) address) as [[descriptor elements]|] eqn:Table;
    last discriminate.
  unfold tab_size in Hupd. cbn [tableinst_elem] in Hupd.
  destruct (N.ltb i (N.of_nat (length elements))) eqn:Bound; last discriminate.
  have Actual : ext_table_typing s address = Some descriptor.
  { unfold ext_table_typing. by rewrite Table. }
  have Operand := table_view_operand Hst View Actual Hvaltype.
  have Operand' := closed_value_typing_store_extension _ _ _ _ Hstext Operand.
  destruct (store_typing_table_lookup Hst Table) as [typed Old].
  have Old' := store_extension_tableinst_typing Hstext Old.
  injection Hupd as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Hmt Hgt Het Hdt.
  eapply Forall_set.
  - by eapply store_extension_tables_typing; eauto.
  - exists typed. eapply tableinst_typing_set; eauto.
    move/N.ltb_lt in Bound. by lias.
  - unfold lookup_N in Table. apply nth_error_Some_length in Table. by lias.
Qed.

Lemma tableinst_typing_size s table typed :
  tableinst_typing s table = Some typed ->
  N.of_nat (length table.(tableinst_elem)) = table.(tableinst_type).(tt_limits).(lim_min).
Proof.
  destruct table. unfold tableinst_typing; simpl.
  move => Typed. remove_bools_options.
  by move/eqP in Hif.
Qed.

Lemma growtable_extension s table amount ref later typed :
  tableinst_typing s table = Some typed ->
  growtable table amount ref = Some later ->
  table_extension table later.
Proof.
  move => Typed Growth.
  have Size := tableinst_typing_size Typed.
  destruct table as [[[minimum maximum] reference] elements]; simpl in Size.
  unfold growtable, tab_size in Growth; simpl in Growth.
  remove_bools_options.
  unfold table_extension, closed_table_type_extension, table_type_extension_gen,
    limits_extension, tab_size; simpl.
  rewrite !eq_refl !andbT /=.
  apply/andP; split; first by apply/N.leb_le; lias.
  rewrite List.length_app List.repeat_length.
  by lias.
Qed.

Lemma growtable_typing s table amount ref later typed :
  tableinst_typing s table = Some typed ->
  closed_value_typing s (VAL_ref ref)
    (closed_reference_value table.(tableinst_type).(tt_elem_type)) ->
  growtable table amount ref = Some later ->
  exists later_type, tableinst_typing s later = Some later_type.
Proof.
  move => Typed Value Growth.
  destruct table as [[[minimum maximum] reference] elements].
  simpl in Value.
  unfold growtable, tab_size in Growth; simpl in Growth.
  remove_bools_options.
  unfold tableinst_typing in Typed; simpl in Typed.
  remove_bools_options.
  eexists. unfold tableinst_typing; simpl.
  match goal with
  | Shape : is_true (closed_ref_nullable reference),
    Limits : limit_valid_range _ _ = true |- _ =>
      rewrite Shape Limits /=
  end.
  have Size : N.of_nat (length (elements ++ List.repeat ref (N.to_nat amount))) =
      (N.of_nat (length elements) + amount)%N.
  { rewrite List.length_app List.repeat_length. lia. }
  rewrite Size eq_refl /= all_cat.
  match goal with Elements : all _ elements = true |- _ => rewrite Elements /= end.
  rewrite all_repeat.
  - reflexivity.
  - exact Value.
Qed.

Lemma stab_grow_extension: forall s f x i v s' sz,
  store_typing s ->
  stab_grow s (f_inst f) x i v = Some (s', sz) ->
  store_extension s s'.
Proof.
  move => s f x i v s' sz Hst Hupd.
  unfold stab_grow in Hupd.
  destruct (lookup_N (inst_tables (f_inst f)) x) as [address|]; last discriminate.
  destruct (lookup_N (s_tables s) address) as [table|] eqn:Table; last discriminate.
  destruct (growtable table i v) as [later|] eqn:Growth; last discriminate.
  injection Hupd as <- <-.
  destruct (store_typing_table_lookup Hst Table) as [typed Typed].
  have Extension := growtable_extension Typed Growth.
  unfold store_extension; simpl; resolve_store_extension.
  eapply component_extension_update; eauto; first by apply table_extension_refl.
Qed.

Lemma stab_grow_typing: forall s f x i v s' sz C tabt,
  store_typing s ->
  stab_grow s (f_inst f) x i v = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (f_inst f).(inst_defined_types) (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_typing s'.
Proof.
  move => s f x i v s' sz C tabt Hst Hupd Hinst Hvaltype Hnth.
  assert (store_extension s s') as Hstext; first by eapply stab_grow_extension; eauto.
  destruct (inst_typing_table_lookup_inv Hinst Hnth) as [address [View Address]].
  unfold stab_grow in Hupd. rewrite Address in Hupd.
  destruct (lookup_N (s_tables s) address) as [table|] eqn:Table; last discriminate.
  destruct (growtable table i v) as [later|] eqn:Growth; last discriminate.
  have Actual : ext_table_typing s address = Some table.(tableinst_type).
  { unfold ext_table_typing. by rewrite Table. }
  have Operand := table_view_operand Hst View Actual Hvaltype.
  destruct (store_typing_table_lookup Hst Table) as [typed Typed].
  destruct (growtable_typing Typed Operand Growth) as [later_type Later].
  have Later' := store_extension_tableinst_typing Hstext Later.
  injection Hupd as <- <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Hmt Hgt Het Hdt.
  eapply Forall_set.
  - by eapply store_extension_tables_typing; eauto.
  - by exists later_type.
  - unfold lookup_N in Table. apply nth_error_Some_length in Table. by lias.
Qed.

Lemma selem_drop_extension: forall s f x s',
  store_typing s ->
  selem_drop s (f_inst f) x = Some s' ->
  store_extension s s'.
Proof.
  move => s f x s' Hst Hupd.
  unfold selem_drop in Hupd.
  destruct (lookup_N (inst_elems (f_inst f)) x) as [address|]; last discriminate.
  destruct (lookup_N (s_elems s) address) as [element|] eqn:Element; last discriminate.
  injection Hupd as <-.
  unfold store_extension; simpl; resolve_store_extension.
  eapply component_extension_update; eauto; first by apply elem_extension_refl.
  unfold elem_extension => /=. by rewrite !eq_refl orbT.
Qed.

Lemma selem_drop_typing: forall s f x s',
  store_typing s ->
  selem_drop s (f_inst f) x = Some s' ->
  store_typing s'.
Proof.
  move => s f x s' Hst Hupd.
  assert (store_extension s s') as Hstext; first by eapply selem_drop_extension; eauto.
  unfold selem_drop in Hupd.
  destruct (lookup_N (inst_elems (f_inst f)) x) as [address|]; last discriminate.
  destruct (lookup_N (s_elems s) address) as [element|] eqn:Element; last discriminate.
  destruct (store_typing_elem_lookup Hst Element) as [typed Typed].
  have Extension : elem_extension element (Build_eleminst element.(eleminst_type) nil).
  { unfold elem_extension; simpl. by rewrite !eq_refl orbT. }
  have Typed' := eleminst_typing_extension Hstext Extension Typed.
  injection Hupd as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Hgt Hdt.
  eapply Forall_set.
  - by eapply store_extension_elems_typing; eauto.
  - by exists typed.
  - unfold lookup_N in Element. apply nth_error_Some_length in Element. by lias.
Qed.

Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (serialise_num v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  remove_bools_options.
  apply write_bytes_meminst_preserve_type in HStore as [Htype Hlen].
  apply/andP; split; last by lias.
  destruct m, mem.
  unfold limits_extension.
  simpl in *; subst.
  by lias.
Qed.

Lemma mem_extension_store_vec: forall m n v marg mem,
    store_vec m n v marg = Some mem ->
    mem_extension m mem.
Proof.
  move => m n v marg mem HStore.
  unfold mem_extension.
  unfold store_vec in HStore.
  remove_bools_options.
  apply write_bytes_meminst_preserve_type in HStore as [Htype Hlen].
  apply/andP; split; last by lias.
  destruct m, mem.
  unfold limits_extension.
  simpl in *; subst.
  by lias.
Qed.

Lemma mem_extension_store_vec_lane: forall m n v width marg x mem,
    store_vec_lane m n v width marg x = Some mem ->
    mem_extension m mem.
Proof.
  move => m n v width marg x mem HStore.
  unfold mem_extension.
  unfold store_vec_lane in HStore.
  remove_bools_options.
  apply write_bytes_meminst_preserve_type in HStore as [Htype Hlen].
  apply/andP; split; last by lias.
  destruct m, mem.
  unfold limits_extension.
  simpl in *; subst.
  by lias.
Qed.
  
Lemma mem_extension_grow: forall s m c mem t,
    meminst_typing s m = Some t ->
    mem_grow m c = (Some mem) ->
    mem_extension m mem /\
      exists mt, meminst_typing s mem = Some mt.
Proof.
  move => s m c mem t Htype HMGrow.
  unfold meminst_typing in Htype; destruct m.
  remove_bools_options.
  unfold mem_extension, limits_extension => /=.
  unfold mem_grow in HMGrow.
  unfold mem_size, mem_length in *.
  simpl in *.
  unfold memtype_valid, limit_valid_range in *.
  remove_bools_options; simpl in *; move/eqP in Hif0; rewrite Hif0.
  - split.
    + apply/andP; split.
      apply/andP; split => //.
      rewrite N.div_mul => //; by lias.
    + erewrite mem_grow_length; last by eauto.
      rewrite Hif0.
      by lias.
    + unfold memtype_valid, limit_valid_range => /=.
      resolve_if_true_eq => /=.
      { rewrite N.div_mul => //.
        rewrite H1.
        rewrite Hif0 in Hif1.
        rewrite N.div_mul in Hif1 => //.
        by lias.
      }
      { resolve_if_true_eq; last by eexists; eauto.
        unfold mem_length => /=.
        erewrite mem_grow_length; last by eauto.
        rewrite N.div_mul => //.
        by lias.
      }
  - split.
    + apply/andP; split.
      apply/andP; split => //.
      rewrite N.div_mul => //; by lias.
    + erewrite mem_grow_length; last by eauto.
      rewrite Hif0.
      by lias.
    + unfold memtype_valid, limit_valid_range => /=.
      resolve_if_true_eq => /=.
      { rewrite N.div_mul => //.
        rewrite Hif0 in Hif.
        rewrite N.div_mul in Hif => //.
        by lias.
      }
      { resolve_if_true_eq; last by eexists; eauto.
        unfold mem_length => /=.
        erewrite mem_grow_length; last by eauto.
        rewrite N.div_mul => //.
        by lias.
      }
Qed.

Lemma smem_store_extension: forall s f n off v s' C t mt,
  store_typing s ->
  smem_store s (f_inst f) n off v t = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n off v s' C t mt Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by apply mem_extension_store in Hoption1.
Qed.

Lemma smem_store_typing: forall s f n off v s' C t mt,
  store_typing s ->
  smem_store s (f_inst f) n off v t = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n off v s' C t mt Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_store_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    + by apply List.nth_error_In in Hnth'.
    + by apply nth_error_Some_length in Hoption2; lias.
Qed.

(* Currently same as store *)
Lemma smem_store_packed_extension: forall s f n off v tp s' C mt,
  store_typing s ->
  smem_store_packed s (f_inst f) n off v tp = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n off v tp s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by apply mem_extension_store in Hoption1.
Qed.

(* Currently store_packed is the same as store *)
Lemma smem_store_packed_typing: forall s f n off v tp s' C mt,
  store_typing s ->
  smem_store_packed s (f_inst f) n off v tp = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n off v tp s' C a Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_store_packed_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_packed, store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
  - by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_store_vec_extension: forall s f n v marg s' C mt,
  store_typing s ->
  smem_store_vec s (f_inst f) n v marg = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n v marg s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by eapply mem_extension_store_vec in Hoption1.
Qed.

Lemma smem_store_vec_typing: forall s f n v marg s' C mt,
  store_typing s ->
  smem_store_vec s (f_inst f) n v marg = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n v marg s' C a Hst Hupd Hit Hnth.

  assert (store_extension s s') as Hstext; first by eapply smem_store_vec_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_vec, store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
  - by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_store_vec_lane_extension: forall s f n v width marg x s' C mt,
  store_typing s ->
  smem_store_vec_lane s (f_inst f) n v width marg x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n v width marg x s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by eapply mem_extension_store_vec_lane in Hoption1.
Qed.

Lemma smem_store_vec_lane_typing: forall s f n v width marg x s' C mt,
  store_typing s ->
  smem_store_vec_lane s (f_inst f) n v width marg x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n v width marg x s' C a Hst Hupd Hit Hnth.

  assert (store_extension s s') as Hstext; first by eapply smem_store_vec_lane_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_vec_lane, store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
  - by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_grow_extension: forall s f n s' sz C mt,
  store_typing s ->
  smem_grow s (f_inst f) n = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n s' sz C a Hst Hupd Hit Hnth.
  unfold smem_grow in Hupd.
  unfold store_extension => /=; remove_bools_options; resolve_store_inst_lookup => /=.
  resolve_store_extension.
  remove_bools_options.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  eapply mem_extension_grow with (s := s) (t := mt) in Hoption1 as [??]; eauto.
  unfold meminst_typing.
  by rewrite Hif Hif0.
Qed.

Lemma smem_grow_typing: forall s f n s' sz C mt,
  store_typing s ->
  smem_grow s (f_inst f) n = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n s' sz C a Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_grow_extension; eauto.
  unfold smem_grow in Hupd; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin; last by apply nth_error_Some_length in Hoption2; lias.
  clear Hstext.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - eapply mem_extension_grow in Hoption1 as [??]; eauto.
    unfold meminst_typing.
    by rewrite Hif Hif0.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
Qed.
    
Lemma sdata_drop_extension: forall s f x s' C t,
  store_typing s ->
  sdata_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_datas C) x = Some t ->
  store_extension s s'.
Proof.
  move => s f x s' C t Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hoption0 in Hnthsdata; injection Hnthsdata as ->.
  rewrite Hnth in Hnthdt; injection Hnthdt as ->.
  eapply component_extension_update; eauto; first by apply data_extension_refl.
  unfold data_extension => /=; rewrite eq_refl. by lias.
Qed.

Lemma sdata_drop_typing: forall s f x s' C t,
  store_typing s ->
  sdata_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_datas C) x = Some t ->
  store_typing s'.
Proof.
  move => s f x s' C t Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply sdata_drop_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct d0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthsdata in Hoption0; injection Hoption0 as ->.
  rewrite Hnth in Hnthdt; injection Hnthdt as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Htypes [Hft [Htt [Hmt [Hgt [Het Hdt]]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Hgt Het.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin; last by apply nth_error_Some_length in Hnthsdata; lias.
  destruct Hin as [-> | [m [Hneq Hnth']]] => //=.
  - exists tt.
    by unfold datainst_typing.
  - eapply List.Forall_forall in Hdt; eauto.
    by apply List.nth_error_In in Hnthsdata; eauto.
Qed.
    
(* Note that although config_typing gives a much stronger constraint on C', we allow much more flexibility here due to the need in inductive cases. *)
Lemma store_extension_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_extension s s'.
Proof.
  move => s f es s' f' es' C C' tf hs hs' HReduce.
  move: tf C C'.
  induction HReduce => //; subst; try (move => tf C C' HIT Hmatch HType HST; intros; destruct tf; invert_e_typing => //; (try by apply store_extension_same)).
  - (* Invoke host *)
    by eapply host_application_extension; eauto.
  - (* global_set *)
    unify_closed_principal.
    have Value : value_typing s (tc_defined_types SourceContext) v (tg_t extr).
    { rewrite -interpret_operand_acceptance.
      cbn [interpret_operand_results List.map] in Hsub.
      inversion Hsub; subst.
      eapply operand_subtyping_acceptance with (actual := CO_value ts_value).
      - exact (store_typing_canonical_registry _ HST).
      - exact H2_value.
      - eassumption. }
    destruct (inst_match_global_operand Hmatch HSourceContext Hconjl0 Hconjr Value)
      as [actual [Slot [Mutable Operand]]].
    eapply supdate_glob_extension; eauto.
    by rewrite -(inst_typing_defined_types HIT).
  - (* table update *)
    by eapply stab_update_extension; eauto.
  - (* table grow *)
    by eapply stab_grow_extension; eauto.
  - (* elem drop *)
    by eapply selem_drop_extension; eauto.
  - (* memory store *)
    eapply smem_store_extension; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory store_packed *)
    eapply smem_store_packed_extension; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory store_vec *)
    eapply smem_store_vec_extension; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory store_vec_lane *)
    eapply smem_store_vec_lane_extension; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory grow *)
    eapply smem_grow_extension; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* data drop *)
    eapply sdata_drop_extension; eauto.
    by eapply inst_match_data_lookup; eauto.
  - (* label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab [t1s [t2s Hetype]]].
    by eapply IHHReduce in Hetype; eauto.
  - (* frame *)
    destruct Hframetype as [source [base [locals [Instance [Context [Equal Values]]]]]].
    subst C0.
    eapply IHHReduce in Hetype; eauto.
    unfold inst_match. rewrite Context.
    unfold closed_inst_match; simpl. by repeat rewrite eq_refl.
Qed.
    
Lemma store_typing_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_typing s'.
Proof.
  move => s f es s' f' es' C C' tf hs hs' HReduce.
  move: tf C C'.
  induction HReduce => //; subst; try (move => tf C C' HIT Hmatch HType HST; intros; destruct tf; invert_e_typing => //).
  - (* host call *)
    by eapply host_application_typing; eauto.
  - (* global_set *)
    unify_closed_principal.
    have Value : value_typing s (tc_defined_types SourceContext) v (tg_t extr).
    { rewrite -interpret_operand_acceptance.
      cbn [interpret_operand_results List.map] in Hsub.
      inversion Hsub; subst.
      eapply operand_subtyping_acceptance with (actual := CO_value ts_value).
      - exact (store_typing_canonical_registry _ HST).
      - exact H2_value.
      - eassumption. }
    destruct (inst_match_global_operand Hmatch HSourceContext Hconjl0 Hconjr Value)
      as [actual [Slot [Mutable Operand]]].
    eapply supdate_glob_typing; eauto.
    by rewrite -(inst_typing_defined_types HIT).
  - (* table update *)
    unify_closed_principal.
    cbn [interpret_operand_results List.map List.app] in Hsub.
    simplify_closed_operands.
    repeat match goal with
    | Parts : List.Forall2 (closed_stack_value_subtyping _) _ _ |- _ =>
      inversion Parts; subst; clear Parts
    end.
    have Value : value_typing s (tc_defined_types SourceContext)
        (VAL_ref tabv) (T_ref (tt_elem_type extr)).
    { rewrite -interpret_operand_acceptance.
      eapply operand_subtyping_acceptance with (actual := CO_value ts_value0).
      - exact (store_typing_canonical_registry _ HST).
      - exact H2_value0.
      - eassumption. }
    destruct (inst_match_table_operand Hmatch HSourceContext Hconjl0 Value)
      as [actual [Slot Operand]].
    eapply stab_update_typing; eauto.
    by rewrite -(inst_typing_defined_types HIT).
  - (* table grow *)
    unify_closed_principal.
    cbn [interpret_operand_results List.map List.app] in Hsub.
    simplify_closed_operands.
    repeat match goal with
    | Parts : List.Forall2 (closed_stack_value_subtyping _) _ _ |- _ =>
      inversion Parts; subst; clear Parts
    end.
    have Value : value_typing s (tc_defined_types SourceContext)
        (VAL_ref tabinit) (T_ref (tt_elem_type extr)).
    { rewrite -interpret_operand_acceptance.
      eapply operand_subtyping_acceptance with (actual := CO_value ts_value).
      - exact (store_typing_canonical_registry _ HST).
      - exact H2_value.
      - eassumption. }
    destruct (inst_match_table_operand Hmatch HSourceContext Hconjl0 Value)
      as [actual [Slot Operand]].
    eapply stab_grow_typing; eauto.
    by rewrite -(inst_typing_defined_types HIT).
  - (* elem drop *)
    by eapply selem_drop_typing; eauto.
  - (* memory store *)
    eapply smem_store_typing; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory store_packed *)
    eapply smem_store_packed_typing; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory store_vec *)
    eapply smem_store_vec_typing; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory store_vec *)
    eapply smem_store_vec_lane_typing; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* memory grow *)
    eapply smem_grow_typing; eauto.
    by eapply inst_match_memory_lookup; eauto.
  - (* data drop *)
    eapply sdata_drop_typing; eauto.
    by eapply inst_match_data_lookup; eauto.
  - (* label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab [t1s [t2s Hetype]]].
    by eapply IHHReduce in Hetype; eauto.
  - (* frame *)
    destruct Hframetype as [source [base [locals [Instance [Context [Equal Values]]]]]].
    subst C0.
    eapply IHHReduce in Hetype; eauto.
    unfold inst_match. rewrite Context.
    unfold closed_inst_match; simpl. by repeat rewrite eq_refl.
Qed.
    
Lemma inst_typing_reduce: forall hs s f es hs' s' f' es' C C' tf,
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    exists C', inst_typing s' f'.(f_inst) = Some C' /\ context_extension C C'.
Proof.
  move => hs s f es hs' s' f' es' C C' tf Hreduce Hst Hit Hmatch Htype.
  erewrite <- reduce_inst_unchanged; eauto.
  eapply inst_typing_extension; last by apply Hit.
  eapply store_extension_reduce in Hreduce; by eauto.
Qed.

(* A weakening of the store_extension_e_typing lemma, so that the new
   context only needs to be an extension of the old (instead of being equal).
*)
Lemma extensions_e_typing: forall s s' C C' es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    closed_context_agree C C' ->
    e_typing s C es tf ->
    e_typing s' C' es tf.
Proof.
  move => s s' C C' es tf Hst1 Hst2 Hsext Hcext Hetype.
  eapply context_extension_typing; eauto.
  by eapply store_extension_e_typing in Hetype; eauto.
Qed.

Lemma result_e_type: forall r ts s C,
    result_types_agree s C.(tc_defined_types) ts r ->
    e_typing s C (result_to_stack r)
      (interpret_instr_type C.(tc_defined_types) (Tf [::] ts)).
Proof.
  move => r ts s C HResType.
  destruct r => /=; last by apply ety_trap.
  simpl in *.
  rewrite -interpret_results_acceptance in HResType.
  destruct (operands_are_concrete _ _ _ HResType) as [concrete [Operands Values]].
  cbn [interpret_instr_type interpret_operand_results] .
  rewrite Operands. by apply et_values_typing.
Qed.

Lemma t_preservation_locs_type_aux: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Closed_ft t1s t2s) ->
    closed_values_typing s f.(f_locs) ts ->
    closed_values_typing s f'.(f_locs) ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT.
  move: C0 t1s t2s.
  induction HReduce => //; move => C0 t1s' t2s' Hmatch Hlocs HType Hvaltype; invert_e_typing; try by eexists; rewrite Hvaltype; split => //; resolve_subtyping.
  - unify_closed_principal.
    destruct (close_context_local_lookup HSourceContext Hconjr)
      as [expected [Closed Lookup]].
    have Value : closed_value_typing s v expected.
    { have Primitive : value_typing s (tc_defined_types SourceContext) v extr.
      { rewrite -interpret_operand_acceptance.
        cbn [interpret_operand_results List.map] in Hsub.
        inversion Hsub; subst.
        eapply operand_subtyping_acceptance with (actual := CO_value ts_value).
        - exact (store_typing_canonical_registry _ HST).
        - exact H2_value.
        - eassumption. }
      unfold value_typing in Primitive. by rewrite Closed in Primitive. }
    rewrite H1.
    unfold closed_values_typing in *.
    eapply all2_set_nth1; eauto.
  - eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [ts1 [ts2 Hetype]]].
    by eapply IHHReduce; (try apply Hetype); eauto.
Qed.

Lemma upd_local_label_return_overwrite {V R F O : Set}:
    forall (C : t_context_gen V R F O) loc1 lab1 ret1 loc2 lab2 ret2,
    upd_local_label_return (upd_local_label_return C loc2 lab2 ret2) loc1 lab1 ret1 = upd_local_label_return C loc1 lab1 ret1.
Proof.
  done.
Qed.
  
Lemma t_preservation_locs_type: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Closed_ft t1s t2s) ->
    closed_values_typing s f.(f_locs) ts ->
    closed_values_typing s' f'.(f_locs) ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT Hmatch Hlocs HType Hvaltype.
  eapply t_preservation_locs_type_aux in Hvaltype; eauto.
  eapply closed_values_extension in Hvaltype; eauto.
  by eapply store_extension_reduce; eauto.
Qed.

(* Auxiliary lemmas for dealing with tail call reduction premises *)
Lemma r_return_call_invert: forall hs s f i hs' s' f' a,
    reduce hs s f [:: AI_basic (BI_call i)] hs' s' f' [:: AI_invoke a] ->
    lookup_N (inst_funcs (f_inst f)) i = Some a.
Proof.
  move => hs s f i hs' s' f' a Hreduce.
  dependent induction Hreduce => //.
  - by inversion H.
  - by repeat (destruct ves => //).
  - destruct (lfill_singleton_invert H x) as [[? Hlheq] [-> ->]] => //.
    by apply IHHreduce.
Qed.

Lemma r_return_call_indirect_invert: forall hs s f v x y hs' s' f' a,
    reduce hs s f [:: $V v; AI_basic (BI_call_indirect x y)] hs' s' f' [:: AI_invoke a] ->
    exists cl i,
      $V v = $VN (VAL_int32 i) /\
        lookup_N (s_funcs s) a = Some cl /\
        function_reference_match s (f_inst f) a y = true /\
        stab_elem s (f_inst f) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_func a).
Proof.
  move => hs s f v x y hs' s' f' a Hreduce.
  dependent induction Hreduce => //.
  - by inversion H.
  - by exists cl, i.
  - by repeat (destruct ves => //).
  - destruct (lfill_singleton_invert H x) as [[? Hlheq] [-> ->]] => //.
    + destruct v as [v|v|v] => //=; by destruct v as [v|v|v|v] => //=.
    + by apply IHHreduce.
Qed.
  
(* Main preservation lemma *)
Lemma t_preservation_e: forall s f es s' f' es' tlocs C C' base base' t1s t2s lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_typing s' f'.(f_inst) = Some C' ->
    close_t_context C = Some base ->
    close_t_context C' = Some base' ->
    closed_values_typing s f.(f_locs) tlocs ->
    e_typing s (upd_local_label_return base tlocs lab ret) es (Closed_ft t1s t2s) ->
    e_typing s' (upd_local_label_return base' tlocs lab ret) es' (Closed_ft t1s t2s).
Proof.
  move => s f es s' f' es' tlocs C C' base base' t1s t2s lab ret hs hs' HReduce.
  move: C C' base base' ret lab t1s t2s tlocs.
  induction HReduce; move => C C' base base' ret lab tx ty tlocs HST1 HST2 HIT1 HIT2
    Hclose1 Hclose2 Hloctype HType; subst; try eauto.
  all: try (by apply ety_trap).
  all: try invert_e_typing; simpl in *; unify_closed_principal; unify_principal; resolve_e_typing => //.
  all: unfold_store_operations; resolve_store_inst_lookup; remove_bools_options => //=; simpl in *; simplify_multieq; unify_closed_principal; unify_principal; resolve_e_typing.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Ref_func *)
    fold_closed_subtyping.
    eapply ety_subtyping; last exact Htisub.
    apply ety_ref with (t := Closed_ref true (CH_abstract HT_func)).
    have Typed := function_reference_abstract_typing _ nil _ _ HST1 Hoption0.
    exact Typed.
  - (* Source null lowering in the producing instance. *)
    fold_closed_subtyping.
    have Names := close_context_names _ _ HSourceContext.
    have BaseNames := close_context_names _ _ Hclose1.
    simpl in Names.
    have Accepted : closed_operand_typing s (VAL_ref ref)
        (interpret_operand_type (tc_defined_types SourceContext)
          (T_ref (Ref_type true heap))).
    { rewrite interpret_operand_acceptance -Names BaseNames
        (inst_typing_defined_types HIT1).
      exact (lower_source_null_typed _ _ _ _ H). }
    remember (interpret_operand_type (tc_defined_types SourceContext)
      (T_ref (Ref_type true heap))) as operand eqn:Operand.
    destruct operand as [concrete|]; last discriminate.
    eapply ety_subtyping; last exact Htisub.
    change (e_typing s (upd_local_label_return base' tlocs lab ret)
      [::v_to_e (VAL_ref ref)] (Closed_ft nil [::CO_value concrete])).
    by apply et_value_typing.
  - (* Block *)
    fold_closed_subtyping.
    have RuntimeExpand : expand (f_inst f) tb = Some (Tf extr extr0).
    { have Types : tc_types C' =
          tc_types (upd_local_label_return base' tlocs lab ret).
      { symmetry. exact (close_context_types Hclose1). }
      by rewrite (inst_typing_expand_eq tb HIT1 Types). }
    rewrite RuntimeExpand in H. injection H as <- <-.
    have Hlen := closed_values_length s vs0 ts_values H2_values.
    have Length : length (lift_closed_result_type ts_values) =
        length (interpret_operand_results (tc_defined_types base') extr).
    { rewrite lift_closed_result_length interpret_operand_results_length.
      rewrite v_to_e_length in H2. by lias. }
    destruct (closed_instr_compose_eq _ _ _ _ _ _ _ _ H1_values Htisub Length)
      as [Principal Arguments].
    eapply ety_subtyping; last exact Principal.
    eapply ety_label with (ts := interpret_operand_results (tc_defined_types base') extr0).
    + eapply ety_subtyping; first apply ety_empty.
      have Weak := closed_instr_weakening (s_types s) nil nil
        (interpret_operand_results (tc_defined_types base') extr0).
      by rewrite !List.app_nil_r in Weak.
    + eapply et_composition'.
      2: { apply ety_a. exact Hconjr0. }
      eapply et_values_typing'; first exact H2_values.
      apply closed_instr_empty_input_intro. exact Arguments.
    + rewrite interpret_operand_results_length length_is_size. reflexivity.
  - (* Loop *)
    fold_closed_subtyping.
    have RuntimeExpand : expand (f_inst f) tb = Some (Tf extr extr0).
    { have Types : tc_types C' =
          tc_types (upd_local_label_return base' tlocs lab ret).
      { symmetry. exact (close_context_types Hclose1). }
      by rewrite (inst_typing_expand_eq tb HIT1 Types). }
    rewrite RuntimeExpand in H. injection H as <- <-.
    have Hlen := closed_values_length s vs0 ts_values H2_values.
    have Length : length (lift_closed_result_type ts_values) =
        length (interpret_operand_results (tc_defined_types base') extr).
    { rewrite lift_closed_result_length interpret_operand_results_length.
      rewrite v_to_e_length in H2. by lias. }
    destruct (closed_instr_compose_eq _ _ _ _ _ _ _ _ H1_values Htisub Length)
      as [Principal Arguments].
    eapply ety_subtyping; last exact Principal.
    eapply ety_label with (ts := interpret_operand_results (tc_defined_types base') extr).
    + change [::AI_basic (BI_loop tb es)] with (to_e_list [::BI_loop tb es]).
      apply ety_a.
      change (closed_be_typing (s_types s) (upd_local_label_return base' tlocs lab ret)
        [::BI_loop tb es] (interpret_instr_type
          (tc_defined_types (upd_local_label_return base' tlocs lab ret)) (Tf extr extr0))).
      by apply cbet_loop.
    + eapply et_composition'.
      2: { apply ety_a. exact Hconjr0. }
      eapply et_values_typing'; first exact H2_values.
      apply closed_instr_empty_input_intro. exact Arguments.
    + rewrite interpret_operand_results_length.
      rewrite v_to_e_length in H2. rewrite -length_is_size. exact H2.
  - (* Call *)
    eapply inst_typing_func_lookup in H as [source [View Lookup]]; eauto.
    simplify_multieq.
    destruct source as [args results].
    destruct (close_context_function_lookup HSourceContext Hconjr)
      as [expected [Expected ExpectedSlot]].
    destruct (close_context_function_lookup Hclose1 Hnthft)
      as [actual [Actual ActualSlot]].
    rewrite (inst_typing_defined_types HIT1) Hoption1 in Actual.
    injection Actual as <-.
    simpl in ExpectedSlot. rewrite ActualSlot in ExpectedSlot.
    injection ExpectedSlot as <-.
    rewrite (interpret_closed_signature _ _ _ Expected) in Htisub.
    destruct c as [inputs outputs].
    eapply ety_subtyping; last exact Htisub.
    apply ety_invoke with (tf := Closed_ft inputs outputs).
    by eapply source_function_view_closes; eauto.
  all: try solve [
    fold_closed_subtyping;
    unfold interpret_operand_results in Htisub;
    rewrite List.map_app in Htisub;
    have Principal := closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _);
    rewrite List.app_nil_r in Principal;
    have Names := Logic.eq_trans (Logic.eq_sym (close_context_names _ _ HSourceContext))
      (Logic.eq_trans (close_context_names _ _ Hclose1) (inst_typing_defined_types HIT1));
    have Types := close_context_types HSourceContext;
    simpl in Types;
    rewrite -Types (close_context_types Hclose1) in Hconjr;
    have View := function_reference_match_view _ _ _ _ _ _ HST1 HIT1 Hconjr H1;
    have InstLookup := Hconjr;
    rewrite -(inst_typing_type_lookup y HIT1) in InstLookup;
    destruct (inst_typing_function_expansion_agreement _ _ _ _ _ HIT1 InstLookup)
      as [id [[args results] [Resolved [Closed Expanded]]]];
    rewrite -Names in Closed;
    change (closed_instr_subtyping (s_types s)
      (interpret_instr_type (tc_defined_types SourceContext) (Tf extr extr0))
      (Closed_ft tx ty)) in Principal;
    rewrite (interpret_closed_signature _ _ _ Closed) in Principal;
    eapply ety_subtyping; last exact Principal;
    apply ety_invoke with (tf := Closed_ft args results);
    eapply source_function_view_closes; [exact View|rewrite Names in Closed; exact Closed]
  ].
  - (* Return_call *)
    (* Due to the opsem being defined based on the corresponding reduction
    of call, this is now an inductive case. Same for Return_call_indirect below *)
    apply r_return_call_invert in HReduce.
    eapply inst_typing_func_lookup in HReduce as [[ts1 ts2] [Hft Hnth]]; eauto.
    destruct (close_context_function_lookup HSourceContext Hconjl0)
      as [expected [Expected ExpectedSlot]].
    destruct (close_context_function_lookup Hclose1 Hnth)
      as [actual [Actual ActualSlot]].
    simpl in ExpectedSlot. rewrite ActualSlot in ExpectedSlot.
    injection ExpectedSlot as <-.
    destruct actual as [inputs outputs].
    have Interpreted := interpret_closed_signature _ _ _ Expected.
    cbn [interpret_instr_type lift_closed_function_type] in Interpreted.
    injection Interpreted as Inputs Outputs.
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite List.map_app in Htisub.
    fold (interpret_operand_results (tc_defined_types SourceContext) extr) in Htisub.
    rewrite Inputs in Htisub.
    eapply ety_subtyping; last exact Htisub.
    eapply ety_return_invoke.
    + eapply source_function_view_closes; first exact Hft.
      rewrite -(inst_typing_defined_types HIT1). exact Actual.
    + have Return := closing_context_return_values _ _ HSourceContext.
      rewrite Hconjr0 /= Outputs in Return. exact Return.
  - (* Return_call_indirect *)
    apply r_return_call_indirect_invert in HReduce.
    destruct HReduce as [cl [i [Hveq [Hnthfunc [Hnthinsttype Hstab]]]]].
    fold_closed_subtyping.
    unfold interpret_operand_results in Htisub.
    rewrite !List.map_app List.app_assoc in Htisub.
    have Principal := closed_instr_compose_suffix _ _ _ _ _ _ _ _ _
      H1_value Htisub (Logic.eq_refl _).
    rewrite List.app_nil_r in Principal.
    have Names := Logic.eq_trans (Logic.eq_sym (close_context_names _ _ HSourceContext))
      (Logic.eq_trans (close_context_names _ _ Hclose1) (inst_typing_defined_types HIT1)).
    have Types := close_context_types HSourceContext.
    simpl in Types.
    rewrite -Types (close_context_types Hclose1) in Hconjl2.
    have View := function_reference_match_view _ _ _ _ _ _ HST1 HIT1 Hconjl2 Hnthinsttype.
    have InstLookup := Hconjl2.
    rewrite -(inst_typing_type_lookup y HIT1) in InstLookup.
    destruct (inst_typing_function_expansion_agreement _ _ _ _ _ HIT1 InstLookup)
      as [id [[inputs outputs] [Resolved [Closed Expanded]]]].
    rewrite -Names in Closed.
    have Interpreted := interpret_closed_signature _ _ _ Closed.
    cbn [interpret_instr_type lift_closed_function_type] in Interpreted.
    injection Interpreted as Inputs Outputs.
    fold (interpret_operand_results (tc_defined_types SourceContext) extr) in Principal.
    rewrite Inputs in Principal.
    eapply ety_subtyping; last exact Principal.
    eapply ety_return_invoke.
    + eapply source_function_view_closes; first exact View.
      rewrite Names in Closed. exact Closed.
    + have Return := closing_context_return_values _ _ HSourceContext.
      rewrite Hconjr0 /= Outputs in Return. exact Return.
  - (* Invoke native *)
    destruct extr as [ts1' ts2'].
    destruct (closed_native_entry _ _ _ _ _ _ HST1 H)
      as [callee [callee_base [inputs [outputs [locals
        [Instance [Base [Signature [Locals Body]]]]]]]]].
    destruct (store_typing_function_expansion_agreement _ _ _ HST1 H)
      as [id [[actual_inputs actual_outputs] [Identity [Closed Expanded]]]].
    change (gc_type_context.close_function_type (inst_defined_types inst) N0
      (Tf ts1 ts2) = Some (Closed_ft actual_inputs actual_outputs)) in Closed.
    rewrite Signature in Closed. injection Closed as <- <-.
    unfold closed_function_view in Hconjr.
    rewrite Identity Expanded /= in Hconjr.
    move/andP: Hconjr => [Arguments Results].
    have Registry := store_typing_canonical_registry _ HST1.
    have ArgsLength := Arguments. apply declaration_list_matchesb_length in ArgsLength.
    have ResultsLength := Results. apply declaration_list_matchesb_length in ResultsLength.
    have Hlen := closed_values_length s vs ts_values H2_values.
    fold_closed_subtyping.
    have Length : length (lift_closed_result_type ts_values) =
        length (lift_closed_result_type ts1').
    { rewrite !lift_closed_result_length.
      have Arity := close_function_type_arities _ _ _ _ _ _ Signature.
      destruct Arity as [InputsLength OutputsLength]. by lias. }
    destruct (closed_instr_compose_eq _ _ _ _ _ _ _ _ H1_values Htisub Length)
      as [Principal Required].
    have Values : closed_values_typing s vs inputs.
    { rewrite lift_values_typing.
      eapply closed_operands_transport; [exact Registry| |].
      - apply closed_results_match_subtyping. exact Arguments.
      - eapply closed_operands_transport; [exact Registry|exact Required|].
        by rewrite -lift_values_typing. }
    have Defaults : closed_values_typing s defaults locals.
    { eapply close_values_typing; last exact Locals.
      by eapply default_values_typing. }
    have LocalEmpty : tc_locals callee_base = nil.
    { have LocalVector := close_context_local_vector Base.
      rewrite (inst_t_context_local_empty Instance) in LocalVector.
      by injection LocalVector. }
    have LabelEmpty : tc_labels callee_base = nil.
    { rewrite (closing_context_label_values _ _ Base).
      by rewrite (inst_t_context_label_empty Instance). }
    eapply ety_subtyping; last exact Principal.
    apply ety_frame with (actual_ts := lift_closed_result_type outputs).
    + eapply mk_thread_typing with
        (C := upd_local callee_base (inputs ++ locals)).
      * exists callee, callee_base, (inputs ++ locals).
        repeat split; try assumption.
        -- by rewrite LocalEmpty cats0.
        -- by apply closed_values_append.
      * reflexivity.
      * eapply ety_label with (ts := lift_closed_result_type outputs).
        -- eapply ety_subtyping; first apply ety_empty.
           have Weak := closed_instr_weakening (s_types s) nil nil
             (lift_closed_result_type outputs).
           by rewrite !List.app_nil_r in Weak.
        -- simpl. rewrite LabelEmpty /=. exact Body.
        -- destruct (close_function_type_arities _ _ _ _ _ _ Signature)
             as [_ OutputLength].
           rewrite lift_closed_result_length -length_is_size. symmetry. exact OutputLength.
    + exact (proj1 HST1).
    + by apply closed_results_match_subtyping.
    + destruct (close_function_type_arities _ _ _ _ _ _ Signature)
        as [_ OutputLength].
      rewrite lift_closed_result_length -length_is_size. by lias.
        
  - (* Invoke host *)
    destruct extr as [expected_args expected_results].
    destruct (store_typing_function_expansion_agreement _ _ _ HST1 H)
      as [id [[inputs outputs] [Identity [Signature Expanded]]]].
    change (gc_type_context.close_function_type nil N0 (Tf t1s t2s) =
      Some (Closed_ft inputs outputs)) in Signature.
    unfold closed_function_view in Hconjr.
    rewrite Identity Expanded /= in Hconjr.
    move/andP: Hconjr => [Arguments Results].
    have Registry := store_typing_canonical_registry _ HST1.
    have ArgsLength := Arguments. apply declaration_list_matchesb_length in ArgsLength.
    have Hlen := closed_values_length s vcs ts_values H2_values.
    destruct (close_function_type_arities _ _ _ _ _ _ Signature)
      as [InputsLength OutputsLength].
    fold_closed_subtyping.
    have Length : length (lift_closed_result_type ts_values) =
        length (lift_closed_result_type expected_args).
    { rewrite !lift_closed_result_length. by lias. }
    destruct (closed_instr_compose_eq _ _ _ _ _ _ _ _ H1_values Htisub Length)
      as [Principal Required].
    have Values : closed_values_typing s vcs inputs.
    { rewrite lift_values_typing.
      eapply closed_operands_transport; [exact Registry| |].
      - apply closed_results_match_subtyping. exact Arguments.
      - eapply closed_operands_transport; [exact Registry|exact Required|].
        by rewrite -lift_values_typing. }
    destruct (close_function_components _ _ _ _ _ Signature) as [Inputs Outputs].
    have HostArguments : values_typing s nil vcs t1s.
    { eapply closed_values_source_typing; last exact Values.
      unfold close_result_type in Inputs. rewrite -those_those0 in Inputs.
      exact Inputs. }
    have HostResult : result_types_agree s' nil t2s r.
    { by eapply host_application_respect; eauto. }
    have Extension : store_extension s s'.
    { by eapply host_application_extension; eauto. }
    destruct (store_extension_type_groups Extension) as [suffix Prefix].
    eapply ety_subtyping.
    2: { rewrite Prefix. apply closed_instr_subtyping_prefix. exact Principal. }
    destruct r as [results|].
    - apply et_values_typing.
      rewrite lift_values_typing.
      eapply closed_operands_transport.
      + exact (store_typing_canonical_registry _ HST2).
      + rewrite Prefix. apply closed_results_subtyping_prefix.
        apply closed_results_match_subtyping. exact Results.
      + rewrite -lift_values_typing.
        eapply close_values_typing; [exact HostResult|exact Outputs].
    - apply ety_trap.

  - (* Return_invoke *)
    eapply lfilled_es_type_exists in Hetype; eauto.
    destruct Hetype as [labs [ts1 [ts2 Hetype]]].
    invert_e_typing.
    injection Hconjr1 as Return. subst extr0.
    destruct (closed_function_view_arities _ _ _ _ _ _ _ HST1 H H0 Hconjl0)
      as [ArgsLength ResultsLength].
    have ValuesLength := closed_values_length s vs0 ts_values H2_values.
    rewrite v_to_e_length in H4.
    have Length : length (lift_closed_result_type ts_values) =
        length (lift_closed_result_type extr1).
    { rewrite !lift_closed_result_length. by lias. }
    apply closed_instr_empty_input_elim in H1_values.
    destruct (closed_instr_required_inputs _ _ _ _ _ Htisub0)
      as [prefix Required].
    have Arguments : closed_stack_results_subtyping (s_types s)
        (lift_closed_result_type ts_values) (lift_closed_result_type extr1).
    { eapply closed_stack_suffix with (a := ts1) (c := prefix ++ extr3).
      - rewrite <-List.app_assoc. eapply closed_stack_results_trans; eauto.
      - exact Length. }
    have Values : closed_values_typing s vs0 extr1.
    { rewrite lift_values_typing.
      eapply closed_operands_transport; [exact (store_typing_canonical_registry _ HST1)
        |exact Arguments|].
      by rewrite -lift_values_typing. }
    eapply ety_subtyping.
    + eapply closed_stack_composition; [apply et_values_typing; exact Values|exact Hconjl0].
    + exists extr5, extr6, extr7, extr8. repeat split => //.
      by eapply closed_stack_results_trans; eauto.
  - (* Local_get *)
    destruct (close_context_local_lookup HSourceContext Hconjr)
      as [expected [Closed Lookup]].
    simpl in Lookup.
    have Interp : interpret_operand_type (tc_defined_types SourceContext) extr =
        CO_value expected.
    { unfold interpret_operand_type. by rewrite (close_concrete_operand _ _ _ Closed). }
    rewrite Interp in Htisub. fold_closed_subtyping.
    unfold lookup_N in *.
    eapply all2_nth_impl in Hloctype; eauto.
    destruct Hloctype as [vt [Hvaltype Hnth]].
    rewrite Lookup in Hvaltype. injection Hvaltype as <-.
    by eapply et_value_typing'; eauto.
  - (* Global_get *)
    destruct (close_context_global_lookup Hclose1 Hnthgt)
      as [actual [Actual ActualSlot]].
    rewrite (inst_typing_defined_types HIT1) Hoption in Actual.
    injection Actual as <-.
    destruct (close_context_global_lookup HSourceContext Hconjl0)
      as [expected [Expected ExpectedSlot]].
    simpl in ExpectedSlot. rewrite ActualSlot in ExpectedSlot.
    injection ExpectedSlot as <-.
    destruct (close_global_type_agreement _ _ _ Expected) as [_ ValueClosed].
    have Interp : interpret_operand_type (tc_defined_types SourceContext) (tg_t extr) =
        CO_value (tg_t c).
    { unfold interpret_operand_type.
      by rewrite (close_concrete_operand _ _ _ ValueClosed). }
    rewrite Interp in Htisub. fold_closed_subtyping.
    eapply et_value_typing'; last exact Htisub.
    eapply closed_value_typing_subsumption; [exact (store_typing_canonical_registry _ HST1)
      | |exact H2|exact H1].
    destruct g; simpl in *. by remove_bools_options.
    
  all: try solve [
    fold_closed_subtyping;
    change (e_typing s (upd_local_label_return base' tlocs lab ret)
      [::v_to_e (VAL_ref tabv)] (Closed_ft tx ty));
    eapply interpreted_value_emission; last exact Hprincipal;
    eapply inst_match_table_read with (source := C') (inst := f_inst f);
      [exact HST1|exact HIT1|apply inst_match_updates; exact Hclose1
      |exact HSourceContext|exact Hconjl0|];
    unfold stab_elem; rewrite Hoption Hoption2; exact H
  ].
  all: try solve [
    destruct (close_context_table_lookup _ _ _ _ Hclose1 Hnthtabt)
      as [actual [Actual ActualSlot]];
    rewrite (inst_typing_defined_types HIT1) Hoption0 in Actual;
    injection Actual as <-;
    destruct (close_context_table_lookup _ _ _ _ HSourceContext Hconjl0)
      as [expected [Expected ExpectedSlot]];
    simpl in ExpectedSlot; rewrite ActualSlot in ExpectedSlot;
    injection ExpectedSlot as <-;
    destruct (close_table_type_metadata _ _ _ Expected) as [_ Reference];
    have ValueClosed := close_reference_type_value _ _ _ Reference;
    assert (Operand : interpret_operand_type (tc_defined_types SourceContext)
        (T_ref (tt_elem_type extr)) = CO_value (closed_reference_value (tt_elem_type c))) by
      (unfold interpret_operand_type; rewrite (close_concrete_operand _ _ _ ValueClosed); reflexivity);
    rewrite Operand in H12;
    assert (Subtype : closed_stack_value_subtyping (s_types s) (CO_value ts_value0)
        (CO_value (closed_reference_value (tt_elem_type c)))) by
      (inversion H12; subst; assumption);
    destruct (source_table_entries s HSourceContext Hconjl0 Expected)
      as [SetEntry FillEntry];
    fold_closed_subtyping;
    eapply ety_subtyping with (t1s := [::CO_value (CV_num T_i32)]) (t2s := nil);
    [eapply closed_table_fill_invariant_continuation
        with (expected := tt_elem_type c) (stored := tt_elem_type (tableinst_type tab));
        [exact (store_typing_canonical_registry _ HST1)|exact H2_value0|exact Subtype
        |eassumption|eassumption|exact SetEntry|exact FillEntry]
    |apply closed_instr_input_suffix with (inputs := nil) (outputs := nil);
      exact Hprincipal]
  ].
  all: try solve [
    destruct (close_context_table_lookup _ _ _ _ Hclose1 Hnthtabt)
      as [actual [Actual ActualSlot]];
    rewrite (inst_typing_defined_types HIT1) Hoption1 in Actual;
    injection Actual as <-;
    destruct (close_context_table_lookup _ _ _ _ HSourceContext Hconjl2)
      as [expected [Expected ExpectedSlot]];
    simpl in ExpectedSlot; rewrite ActualSlot in ExpectedSlot;
    injection ExpectedSlot as <-;
    destruct (close_table_type_metadata _ _ _ Expected) as [_ Reference];
    destruct (source_table_copy_entries s HSourceContext Hconjl0 Hconjl2
      Hconjr0 Reference) as [GetEntry [SetEntry CopyEntry]];
    fold_closed_subtyping;
    eapply ety_subtyping with
      (t1s := [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)]) (t2s := nil);
    [eapply closed_table_copy_continuation with (expected := tt_elem_type c)
        (stored := tt_elem_type (tableinst_type taby));
      [eassumption|eassumption|exact GetEntry|exact SetEntry|exact CopyEntry]
    |apply closed_instr_input_suffix with (inputs := nil) (outputs := nil);
      exact Hprincipal]
  ].
  all: try solve [
    destruct (close_context_table_lookup _ _ _ _ Hclose1 Hnthtabt)
      as [actual [Actual ActualSlot]];
    rewrite (inst_typing_defined_types HIT1) Hoption1 in Actual;
    injection Actual as <-;
    destruct (close_context_table_lookup _ _ _ _ HSourceContext Hconjl0)
      as [expected [Expected ExpectedSlot]];
    simpl in ExpectedSlot; rewrite ActualSlot in ExpectedSlot;
    injection ExpectedSlot as <-;
    destruct (close_table_type_metadata _ _ _ Expected) as [_ Reference];
    destruct (inst_typing_elem_lookup HIT1 Hoption0)
      as [raw_element [element [Element [View ElementSlot]]]];
    rewrite H0 in Element; injection Element as <-;
    destruct (close_context_element_lookup Hclose1 ElementSlot)
      as [checked_element [ElementClosed CheckedSlot]];
    destruct (close_context_element_lookup HSourceContext Hconjr)
      as [primitive_element [PrimitiveClosed PrimitiveSlot]];
    simpl in PrimitiveSlot; rewrite CheckedSlot in PrimitiveSlot;
    injection PrimitiveSlot as <-;
    rewrite Reference in PrimitiveClosed; injection PrimitiveClosed as <-;
    rewrite (inst_typing_defined_types HIT1) in ElementClosed;
    have Value := closed_element_view_read HST1 View H0 ElementClosed H4;
    destruct (source_table_init_entries s HSourceContext Hconjl0 Hconjr Expected)
      as [SetEntry InitEntry];
    fold_closed_subtyping;
    eapply ety_subtyping with (t1s := [::CO_value (CV_num T_i32)]) (t2s := nil);
    [eapply closed_table_init_invariant_continuation with
        (expected := tt_elem_type c) (stored := tt_elem_type (tableinst_type tab));
      [exact (store_typing_canonical_registry _ HST1)|exact Value|eassumption
        |eassumption|exact SetEntry|exact InitEntry]
    |apply closed_instr_input_suffix with (inputs := nil) (outputs := nil);
      exact Hprincipal]
  ].
      
  - (* Load None *)
    destruct t; exact Hprincipal.
  - (* Load Some *)
    destruct t; exact Hprincipal.
  - (* Memory fill *)
    destruct (source_memory_byte_entries s HSourceContext Hconjr)
      as [LoadEntry StoreEntry].
    have SourceEntry : be_typing SourceContext [::BI_memory_fill]
        (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] nil).
    { by eapply bet_memory_fill; eauto. }
    have FillEntry := source_structural_entry s SourceContext _ _ _
      SourceEntry HSourceContext.
    fold_closed_subtyping.
    eapply ety_subtyping with
      (t1s := [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)]) (t2s := nil).
    + by eapply closed_memory_store_continuation; eauto.
    + apply closed_instr_input_suffix with (inputs := nil) (outputs := nil).
      exact Hprincipal.
  all: try solve [
    destruct (source_memory_byte_entries s HSourceContext Hconjr)
      as [LoadEntry StoreEntry];
    assert (SourceEntry : be_typing SourceContext [::BI_memory_copy]
        (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] nil)) by
      (eapply bet_memory_copy; eauto);
    have CopyEntry := source_structural_entry s SourceContext _ _ _
      SourceEntry HSourceContext;
    fold_closed_subtyping;
    eapply ety_subtyping with
      (t1s := [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)]) (t2s := nil);
    [eapply closed_memory_copy_continuation; eauto
    |apply closed_instr_input_suffix with (inputs := nil) (outputs := nil);
      exact Hprincipal]
  ].
  - (* Memory init *)
    destruct (source_memory_byte_entries s HSourceContext Hconjl0)
      as [LoadEntry StoreEntry].
    have SourceEntry : be_typing SourceContext [::BI_memory_init x]
        (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] nil).
    { by eapply bet_memory_init; eauto. }
    have InitEntry := source_structural_entry s SourceContext _ _ _
      SourceEntry HSourceContext.
    fold_closed_subtyping.
    eapply ety_subtyping with
      (t1s := [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)]) (t2s := nil).
    + by eapply closed_memory_store_continuation; eauto.
    + apply closed_instr_input_suffix with (inputs := nil) (outputs := nil).
      exact Hprincipal.
    
  - (* Label *)
    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; (try by apply HType); eauto.
      - by eapply r_label; eauto.
      - by apply inst_match_updates.
    }
    remember HIT2 as HIT3; clear HeqHIT3.
    erewrite <- reduce_inst_unchanged in HIT2; eauto.
    specialize (inst_typing_extension Hext HIT1) as [C'' [Hit Hcext]].
    simplify_multieq.
    have BaseAgree : closed_context_agree base base'.
    { by eapply close_context_extension_agree; eauto. }
    assert (closed_values_typing s' f'.(f_locs) tlocs) as Hvaltype.
    {
      specialize (lfilled_es_type_exists erefl HType) as Hestype.
      destruct Hestype as [lab' [ts1 [ts2 Hestype]]].
      eapply t_preservation_locs_type; eauto.
      - change (inst_match C (upd_local_label_return base tlocs lab' ret)).
        apply inst_match_updates. exact Hclose1.
      - done.
    }
    destruct (store_extension_type_groups Hext) as [suffix Prefix].
    remember (lfill lh es) as les.
    remember (lfill lh es') as les'.
    generalize dependent les'.
    generalize dependent les.
    move: lh lab tx ty.
    elim.
    + move => vs es0 lab tx ty ? ? Hetype ? ?; subst; simpl in *.
      invert_e_typing.
      apply et_composition' with (t2s := ts3_comp).
      { eapply et_values_typing'.
        - by eapply closed_values_extension; eauto.
        - rewrite Prefix. apply closed_instr_subtyping_prefix. exact H1_values. }
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by apply closed_context_agree_updates.
      }
    + move => k0 vs n es1 lh' IH es2 lab tx ty ? -> /=Hetype ? ->.
      invert_e_typing.
      eapply et_composition' with (t2s := ts3_comp); eauto.
      { eapply et_values_typing'.
        - by eapply closed_values_extension; eauto.
        - rewrite Prefix. apply closed_instr_subtyping_prefix. exact H1_values. }
      rewrite -cat1s.
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by apply closed_context_agree_updates.
      }
      eapply IH in Hconjl1; eauto.
      eapply ety_subtyping.
      2: { rewrite Prefix. apply closed_instr_subtyping_prefix. exact Htisub. }
      eapply ety_label; eauto.
      eapply extensions_e_typing; (try by apply Hext); (try by apply Hconjl0); eauto.
      by apply closed_context_agree_updates.
        
  - (* r_frame *)
    destruct Hframetype as [source [inner [locals
      [Instance [Context [Equal LocalValues]]]]]].
    have Empty : tc_locals inner = nil.
    { have LocalVector := close_context_local_vector Context.
      rewrite (inst_t_context_local_empty Instance) in LocalVector.
      by injection LocalVector. }
    rewrite Empty cats0 in Equal. subst C0.
    have Labels : tc_labels inner = nil.
    { rewrite (closing_context_label_values _ _ Context).
      by rewrite (inst_t_context_label_empty Instance). }
    have InnerContext : upd_return (upd_local inner locals) (Some extr0) =
        upd_local_label_return inner locals nil (Some extr0).
    { by rewrite /upd_return /upd_local /upd_local_label_return /= Labels. }
    rewrite InnerContext in Hetype.
    have Match := inst_match_updates locals nil (Some extr0) Context.
    have Extension : store_extension s s'.
    { by eapply store_extension_reduce; eauto. }
    have LaterLocals : closed_values_typing s' (f_locs f') locals.
    { by eapply t_preservation_locs_type; eauto. }
    destruct (inst_typing_reduce HReduce HST1 Instance Match Hetype)
      as [source' [LaterInstance SourceExtension]].
    destruct (inst_typing_context_closes _ _ _ LaterInstance)
      as [later LaterContext].
    have LaterEmpty : tc_locals later = nil.
    { have LocalVector := close_context_local_vector LaterContext.
      rewrite (inst_t_context_local_empty LaterInstance) in LocalVector.
      by injection LocalVector. }
    have LaterLabels : tc_labels later = nil.
    { rewrite (closing_context_label_values _ _ LaterContext).
      by rewrite (inst_t_context_label_empty LaterInstance). }
    have Body : e_typing s'
        (upd_local_label_return later locals nil (Some extr0)) es'
        (Closed_ft nil extr0).
    { by eapply IHHReduce; eauto. }
    fold_closed_subtyping.
    destruct (store_extension_type_groups Extension) as [suffix Prefix].
    eapply ety_subtyping.
    2: { rewrite Prefix. apply closed_instr_subtyping_prefix. exact Htisub. }
    apply ety_frame with (actual_ts := extr0).
    + eapply mk_thread_typing with (C := upd_local later locals).
      * exists source', later, locals. repeat split; try assumption.
        by rewrite LaterEmpty cats0.
      * reflexivity.
      * have LaterInner : upd_return (upd_local later locals) (Some extr0) =
            upd_local_label_return later locals nil (Some extr0).
        { by rewrite /upd_return /upd_local /upd_local_label_return /= LaterLabels. }
        by rewrite LaterInner.
    + exact (proj1 HST2).
    + rewrite Prefix. by apply closed_results_subtyping_prefix.
    + by rewrite length_is_size.
Qed.

Theorem t_preservation: forall s f es s' f' es' ts hs hs',
    reduce hs s f es hs' s' f' es' ->
    config_typing s (f, es) ts ->
    config_typing s' (f', es') ts.
Proof.
  move => s f es s' f' es' ts hs hs' HReduce HType.
  destruct HType as [Store Thread].
  inversion Thread as [s0 f0 es0 rs ts0 C0 C1 Frame Equal Typing]; subst.
  destruct Frame as [source [base [locals
    [Instance [Context [Equal Values]]]]]].
  have Empty : tc_locals base = nil.
  { have LocalVector := close_context_local_vector Context.
    rewrite (inst_t_context_local_empty Instance) in LocalVector.
    by injection LocalVector. }
  rewrite Empty cats0 in Equal. subst C0.
  have Labels : tc_labels base = nil.
  { rewrite (closing_context_label_values _ _ Context).
    by rewrite (inst_t_context_label_empty Instance). }
  have InitialContext : upd_return (upd_local base locals) None =
      upd_local_label_return base locals nil None.
  { by rewrite /upd_return /upd_local /upd_local_label_return /= Labels. }
  rewrite InitialContext in Typing.
  have Match := inst_match_updates locals nil None Context.
  have Extension : store_extension s s'.
  { by eapply store_extension_reduce; eauto. }
  have LaterStore : store_typing s'.
  { by eapply store_typing_reduce; eauto. }
  have LaterValues : closed_values_typing s' (f_locs f') locals.
  { by eapply t_preservation_locs_type; eauto. }
  destruct (inst_typing_extension Extension Instance)
    as [source' [LaterInstance SourceExtension]].
  erewrite (reduce_inst_unchanged HReduce) in LaterInstance.
  destruct (inst_typing_context_closes _ _ _ LaterInstance)
    as [later LaterContext].
  have LaterEmpty : tc_locals later = nil.
  { have LocalVector := close_context_local_vector LaterContext.
    rewrite (inst_t_context_local_empty LaterInstance) in LocalVector.
    by injection LocalVector. }
  have LaterLabels : tc_labels later = nil.
  { rewrite (closing_context_label_values _ _ LaterContext).
    by rewrite (inst_t_context_label_empty LaterInstance). }
  split; first exact LaterStore.
  eapply mk_thread_typing with (C := upd_local later locals).
  - exists source', later, locals. repeat split; try assumption.
    by rewrite LaterEmpty cats0.
  - reflexivity.
  - have FinalContext : upd_return (upd_local later locals) None =
        upd_local_label_return later locals nil None.
    { by rewrite /upd_return /upd_local /upd_local_label_return /= LaterLabels. }
    rewrite FinalContext.
    by eapply t_preservation_e; eauto.
Qed.

End Host.
