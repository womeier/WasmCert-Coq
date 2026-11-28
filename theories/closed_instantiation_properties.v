(* Facts about the checked import boundary, before any initializer values
   have been assigned types. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_properties instantiation_func closed_initializer_properties
  gc_declaration_typing gc_type_context gc_declaration_typing_properties
  gc_runtime_type_properties gc_function_subtyping_properties gc_type_context_properties
  gc_closed_runtime_properties.
From Stdlib Require Import NArith Lia Arith.PeanoNat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Imports.
Context `{ho : host}.

Lemma closed_import_global_projection C imports sources registry names expected :
  List.Forall2 (module_import_typing C) imports sources ->
  those (map (close_import_desc registry names) (map imp_desc imports)) = Some expected ->
  those (map (close_global_type names) (ext_t_globals sources)) =
    Some (closed_ext_t_globals expected).
Proof.
  move => Typed.
  move: expected.
  induction Typed as [|imp source imports sources Head Tail IH];
    move => expected Closed.
  - simpl in Closed. injection Closed as <-. reflexivity.
  - destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    cbn [imp_desc map] in Closed.
    rewrite -those_those0 in Closed.
    cbn [those0] in Closed.
    destruct (close_import_desc registry names descriptor) as [external|] eqn:Entry;
      last discriminate.
    destruct (those0 (map (close_import_desc registry names)
      (map imp_desc imports))) as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-.
    have Projection := IH rest ltac:(by rewrite -those_those0).
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; simpl in *;
      try exact Projection.
    rewrite -those_those0 /=.
    rewrite -those_those0 in Projection.
    by rewrite Projection.
    injection Head as <-.
    rewrite Hoption -those_those0 /=.
    rewrite -those_those0 in Projection.
    by rewrite Projection.
Qed.

Lemma closed_import_component_lengths registry actual expected :
  List.Forall2 (closed_import_subtyping registry) actual expected ->
  length (closed_ext_t_funcs actual) = length (closed_ext_t_funcs expected) /\
  length (closed_ext_t_tables actual) = length (closed_ext_t_tables expected) /\
  length (closed_ext_t_mems actual) = length (closed_ext_t_mems expected) /\
  length (closed_ext_t_globals actual) = length (closed_ext_t_globals expected).
Proof.
  move => Typed.
  induction Typed as [|a e actual expected Head Tail IH]; first by repeat split.
  destruct IH as [Functions [Tables [Memories Globals]]].
  destruct a, e; unfold closed_import_subtyping in Head; try discriminate;
    simpl; repeat split; try assumption; by f_equal.
Qed.

Lemma closed_import_table_projection C imports sources registry names expected :
  List.Forall2 (module_import_typing C) imports sources ->
  those (map (close_import_desc registry names) (map imp_desc imports)) = Some expected ->
  those (map (close_table_type names) (ext_t_tables sources)) =
    Some (closed_ext_t_tables expected).
Proof.
  move => Typed. move: expected.
  induction Typed as [|imp source imports sources Head Tail IH];
    move => expected Closed.
  - simpl in Closed. injection Closed as <-. reflexivity.
  - destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    cbn [imp_desc map] in Closed.
    rewrite -those_those0 in Closed. cbn [those0] in Closed.
    destruct (close_import_desc registry names descriptor) as [external|] eqn:Entry;
      last discriminate.
    destruct (those0 (map (close_import_desc registry names)
      (map imp_desc imports))) as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-.
    have Projection := IH rest ltac:(by rewrite -those_those0).
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; try congruence; simpl in *;
      try exact Projection.
    match goal with Same : ET_table _ = ET_table _ |- _ =>
      injection Same as <- end.
    rewrite Hoption -those_those0 /=.
    rewrite -those_those0 in Projection.
    by rewrite Projection.
Qed.

Lemma allocated_table_context_closing registry names tables initials :
  those (map (close_table_initial registry names) tables) = Some initials ->
  those (map (close_table_type names) tables) = Some (map fst initials).
Proof.
  rewrite -!those_those0.
  move: initials.
  induction tables as [|table tables IH]; move => initials Closed.
  - simpl in Closed. injection Closed as <-. reflexivity.
  - simpl in Closed |- *.
    destruct (close_table_initial registry names table) as [[closed ref]|] eqn:Entry;
      last discriminate.
    destruct (those0 (map (close_table_initial registry names) tables))
      as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-.
    have Tail := IH _ (Logic.eq_refl _).
    unfold close_table_initial in Entry.
    destruct (close_table_type names table) as [descriptor|]; last discriminate.
    destruct (lower_closed_null registry (closed_ref_heap (tt_elem_type descriptor))) eqn:Null;
      try discriminate.
    injection Entry as <- _.
    simpl. by rewrite Tail.
Qed.

Lemma registered_type_names registry names sources :
  source_type_identitiesb registry names sources names ->
  List.Forall (fun id => defined_type_validb registry id = true) names.
Proof.
  move/source_type_identitiesb_correct => Identities.
  induction Identities as [|source id sources ids [declaration [Closed Expanded]] Tail IH].
  - constructor.
  - constructor; last exact IH.
    unfold expand_defined_type in Expanded.
    unfold defined_type_validb.
    by destruct (lookup_defined_type registry id).
Qed.

Lemma registered_source_function_closing registry names sources index signature :
  source_type_identitiesb registry names sources names ->
  lookup_function_type sources index = Some signature ->
  exists closed, close_function_type names N0 signature = Some closed.
Proof.
  move => Identities Function.
  apply lookup_function_type_kind in Function as [declaration [Lookup Composite]].
  apply source_type_identitiesb_correct in Identities.
  destruct (Forall2_lookup Identities Lookup)
    as [id [Name [closed [Closing Expanded]]]].
  have Identity : source_type_identityb registry names declaration id.
  { apply source_type_identityb_correct. by exists closed. }
  destruct (source_type_identity_function _ _ _ _ _ Composite Identity)
    as [signature' [Closed _]].
  by exists signature'.
Qed.

Lemma those_map_total {A B} (f : A -> option B) xs :
  List.Forall (fun x => exists y, f x = Some y) xs ->
  exists ys, those (List.map f xs) = Some ys.
Proof.
  move => All. induction All as [|x xs [y Head] Tail [ys Rest]].
  - by exists nil.
  - exists (y :: ys).
    rewrite -those_those0 in Rest.
    by rewrite -those_those0 /= Head Rest.
Qed.

Lemma imported_function_context_closing C imports sources registry names :
  source_type_identitiesb registry names C.(tc_types) names ->
  List.Forall2 (module_import_typing C) imports sources ->
  exists closed, those (List.map (close_function_type names N0)
    (ext_t_funcs sources)) = Some closed.
Proof.
  move => Identities Typed.
  apply those_map_total.
  induction Typed as [|imp source imports sources Head Tail IH]; first constructor.
  destruct imp as [module_name item_name descriptor].
  unfold module_import_typing, module_import_desc_typing in Head.
  destruct descriptor; destruct source; simpl in Head; try discriminate;
    remove_bools_options; subst; try congruence; simpl; try exact IH.
  constructor; last exact IH.
  eapply registered_source_function_closing; eauto.
Qed.

Lemma defined_function_context_closing C functions signatures registry names :
  source_type_identitiesb registry names C.(tc_types) names ->
  List.Forall2 (module_func_typing C) functions signatures ->
  exists closed, those (List.map (close_function_type names N0) signatures) = Some closed.
Proof.
  move => Identities Typed. apply those_map_total.
  induction Typed as [|code signature functions signatures Head Tail IH]; first constructor.
  constructor; last exact IH.
  unfold module_func_typing in Head.
  destruct code, signature. destruct Head as [Lookup _].
  eapply registered_source_function_closing; eauto.
Qed.

Definition source_import_signature types (imp : module_import) :=
  match imp.(imp_desc) with
  | MID_func index => option_map ET_func (lookup_function_type types index)
  | MID_table t => Some (ET_table t)
  | MID_mem t => Some (ET_mem t)
  | MID_global t => Some (ET_global t)
  end.

Lemma source_import_signatures C imports sources :
  List.Forall2 (module_import_typing C) imports sources ->
  those (map (source_import_signature C.(tc_types)) imports) = Some sources.
Proof.
  move => Typed. induction Typed as [|imp source imports sources Head Tail IH].
  - reflexivity.
  - rewrite -those_those0 in IH.
    rewrite -those_those0 /=.
    have Entry : source_import_signature (tc_types C) imp = Some source.
    { destruct imp as [module_name item_name descriptor].
      unfold module_import_typing, module_import_desc_typing in Head.
      unfold source_import_signature. simpl in *.
      destruct descriptor; simpl in *; remove_bools_options; subst; congruence. }
    by rewrite Entry IH.
Qed.

Lemma source_function_signatures C functions signatures :
  List.Forall2 (module_func_typing C) functions signatures ->
  those (map (fun f => lookup_function_type C.(tc_types) f.(modfunc_type))
    functions) = Some signatures.
Proof.
  move => Typed. induction Typed as [|code signature functions signatures Head Tail IH].
  - reflexivity.
  - rewrite -those_those0 in IH.
    rewrite -those_those0 /=.
    unfold module_func_typing in Head.
    destruct code, signature. destruct Head as [Lookup _].
    simpl in *. by rewrite Lookup IH.
Qed.

Lemma checked_function_import_view s names types index signature address actual expected :
  canonical_registry_valid s.(s_types) ->
  source_type_identitiesb s.(s_types) names types names ->
  lookup_function_type types index = Some signature ->
  close_import_desc s.(s_types) names (MID_func index) = Some (CET_func expected) ->
  lookup_func_defined_type s address = Some actual ->
  closed_import_subtyping s.(s_types) (CET_func actual) (CET_func expected) ->
  instance_function_view s names address signature.
Proof.
  move => Registry Identities Function Boundary Actual Matches.
  have Kind := Function.
  apply lookup_function_type_kind in Kind as [declaration [Lookup Composite]].
  apply source_type_identitiesb_correct in Identities.
  destruct (Forall2_lookup Identities Lookup)
    as [id [Name [closed [Closing Expanded]]]].
  have Identity : source_type_identityb (s_types s) names declaration id.
  { apply source_type_identityb_correct. by exists closed. }
  destruct (source_type_identity_function _ _ _ _ _ Composite Identity)
    as [[args results] [Closed Expected]].
  unfold close_import_desc, lookup_N in Boundary.
  rewrite Name Expected in Boundary. injection Boundary as <-.
  unfold closed_import_subtyping in Matches.
  rewrite Expected in Matches.
  destruct (expand_function_type (s_types s) actual) as [actual_signature|] eqn:Expansion;
    last discriminate.
  destruct (defined_function_matches_variance _ _ _ _ _ Registry Matches Expected)
    as [aa [ar [ExpandedActual [Arguments Results]]]].
  unfold instance_function_view.
  rewrite Actual Closed ExpandedActual /=.
  by rewrite Arguments Results.
Qed.

Lemma allocated_native_function_view s inst code signature address :
  canonical_registry_valid s.(s_types) ->
  source_type_identitiesb s.(s_types) inst.(inst_defined_types)
    inst.(inst_types) inst.(inst_defined_types) ->
  lookup_function_type inst.(inst_types) code.(modfunc_type) = Some signature ->
  lookup_N s.(s_funcs) address = Some (gen_func_instance code inst) ->
  instance_function_view s inst.(inst_defined_types) address signature.
Proof.
  move => Registry Identities Function Lookup.
  have Kind := Function.
  apply lookup_function_type_kind in Kind as [declaration [Slot Composite]].
  have Registered := Identities.
  apply source_type_identitiesb_correct in Registered.
  destruct (Forall2_lookup Registered Slot)
    as [id [Name [closed [Closing Expanded]]]].
  have Identity : source_type_identityb (s_types s) (inst_defined_types inst)
      declaration id.
  { apply source_type_identityb_correct. by exists closed. }
  destruct (source_type_identity_function _ _ _ _ _ Composite Identity)
    as [expected [Closed Expected]].
  eapply checked_function_import_view with
    (types := inst_types inst) (index := modfunc_type code)
    (actual := id) (expected := id); try eassumption.
  - unfold close_import_desc, lookup_N. by rewrite Name Expected.
  - unfold lookup_func_defined_type.
    rewrite Lookup /gen_func_instance Function /funcinst_defined_type.
    exact Name.
  - unfold closed_import_subtyping.
    by rewrite Expected defined_type_matches_refl.
Qed.

Lemma imported_function_views C old later names imports sources values actual expected :
  store_extension old later ->
  canonical_registry_valid later.(s_types) ->
  source_type_identitiesb later.(s_types) names C.(tc_types) names ->
  List.Forall2 (module_import_typing C) imports sources ->
  List.Forall2 (external_typing old) values actual ->
  List.Forall2 (closed_import_subtyping later.(s_types)) actual expected ->
  those (map (close_import_desc later.(s_types) names) (map imp_desc imports)) =
    Some expected ->
  all2 (instance_function_view later names) (ext_funcs values) (ext_t_funcs sources).
Proof.
  move => Extension Registry Identities Typed.
  move: values actual expected.
  induction Typed as [|imp source imports sources Head Tail IH];
    move => values actual expected Values Matches Closed.
  - simpl in Closed. injection Closed as <-.
    inversion Matches; subst. inversion Values; subst. reflexivity.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_import_desc (s_types later) names (imp_desc imp))
      as [expected_head|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_import_desc (s_types later) names)
      (map imp_desc imports))) as [expected_tail|] eqn:Entries; last discriminate.
    injection Closed as <-.
    inversion Matches as [|actual_head expected0 actual_tail expected1 MatchHead MatchTail];
      subst; clear Matches.
    inversion Values as [|value actual0 value_tail actual1 ValueHead ValueTail];
      subst; clear Values.
    have Rest := IH _ _ _ ValueTail MatchTail ltac:(by rewrite -those_those0).
    have OriginalEntry := Entry.
    have OriginalMatch := MatchHead.
    destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    unfold external_typing, ext_typing in ValueHead.
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      remove_bools_options; subst; try congruence;
      destruct value; destruct actual_head; simpl in ValueHead; try discriminate;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; try congruence;
      unfold closed_import_subtyping in MatchHead; simpl in MatchHead;
      try discriminate; simpl in *; try exact Rest.
    apply/andP; split; last exact Rest.
    eapply checked_function_import_view; try eassumption.
    eapply store_extension_native_function_identity; eauto.
Qed.

Lemma close_value_type_name_portability registry old names source closed :
  length old = length names ->
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_value_type old N0 source = Some closed ->
  exists target, close_value_type names N0 source = Some target /\
    closed_value_validb registry target = true.
Proof.
  move => Length Registered.
  destruct source as [number|vector|[nullable heap]|]; try discriminate.
  - move => _. exists (CV_num number). by split.
  - move => _. exists (CV_vec vector). by split.
  - destruct heap; cbn [close_value_type close_heap_type]; try
      (move => _; eexists; split; reflexivity).
    simpl. unfold close_type_index.
    rewrite Length.
    destruct (N.ltb t (N.of_nat (length names))) eqn:Bound.
    + move => _.
      have BoundNat : (N.to_nat t < length names)%coq_nat.
      { apply N.ltb_lt in Bound. lia. }
      destruct (List.nth_error names (N.to_nat t)) as [id|] eqn:Name.
      * exists (CV_ref nullable (CH_defined (CT_def id))). split; first reflexivity.
        rewrite List.Forall_forall in Registered.
        apply Registered. exact (List.nth_error_In _ _ Name).
      * apply List.nth_error_None in Name. lia.
    + have Zero : N.ltb (t - N.of_nat (length names)) N0 = false
        by apply N.ltb_ge; lia.
      by rewrite Zero.
Qed.

Lemma registered_closed_value_valid registry names source closed :
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_value_type names N0 source = Some closed ->
  closed_value_validb registry closed.
Proof.
  move => Registered Closed.
  destruct (close_value_type_name_portability (Logic.eq_refl _) Registered Closed)
    as [target [Same Valid]].
  rewrite Closed in Same. injection Same as <-. exact Valid.
Qed.

Lemma registered_closed_reference_valid registry names source closed :
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_reference_type names source = Some closed ->
  closed_value_validb registry (closed_reference_value closed).
Proof.
  move => Registered Closed.
  have ValueClosed : close_value_type names N0 (T_ref source) =
      Some (closed_reference_value closed).
  { unfold close_reference_type in Closed.
    destruct (close_heap_type names N0 (ref_heap source)) eqn:Heap; last discriminate.
    injection Closed as <-. by rewrite /close_value_type Heap. }
  exact (registered_closed_value_valid Registered ValueClosed).
Qed.

Lemma checked_table_import_view s names source address actual expected :
  canonical_registry_valid s.(s_types) ->
  ext_table_typing s address = Some actual ->
  close_table_type names source = Some expected ->
  closed_value_validb s.(s_types) (closed_reference_value expected.(tt_elem_type)) ->
  closed_import_subtyping s.(s_types) (CET_table actual) (CET_table expected) ->
  instance_table_view s names address source.
Proof.
  move => Registry Actual Closed Expected Matches.
  unfold closed_import_subtyping, closed_reference_equivb, limits_subtyping in Matches.
  move/andP: Matches => [/andP [Forward Backward] /andP [Minimum Maximum]].
  have ValidActual : closed_value_validb (s_types s)
      (closed_reference_value (tt_elem_type actual)).
  { exact (proj2 (closed_value_matchesb_validity _ _ _ (proj1 (proj2 Registry))
      Forward) Expected). }
  unfold instance_table_view. rewrite Actual Closed ValidActual Expected Forward Backward Minimum /=.
  destruct (lim_max (tt_limits actual)), (lim_max (tt_limits expected)); exact Maximum.
Qed.

Lemma checked_global_import_view s names source address actual expected :
  canonical_registry_valid s.(s_types) ->
  ext_global_typing s address = Some actual ->
  close_global_type names source = Some expected ->
  closed_value_validb s.(s_types) expected.(tg_t) ->
  closed_import_subtyping s.(s_types) (CET_global actual) (CET_global expected) ->
  instance_global_view s names address source.
Proof.
  move => Registry Actual Closed Expected Matches.
  unfold closed_import_subtyping in Matches.
  move/andP: Matches => [/andP [Mut Forward] Backward].
  have ValidActual : closed_value_validb (s_types s) (tg_t actual).
  { exact (proj2 (closed_value_matchesb_validity _ _ _ (proj1 (proj2 Registry))
      Forward) Expected). }
  unfold instance_global_view.
  by rewrite Actual Closed Mut ValidActual Expected Forward Backward.
Qed.

Lemma registered_closed_table_valid registry names source closed :
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_table_type names source = Some closed ->
  closed_value_validb registry (closed_reference_value closed.(tt_elem_type)).
Proof.
  move => Registered Closed.
  unfold close_table_type in Closed.
  destruct (close_reference_type names (tt_elem_type source)) as [ref|] eqn:Ref;
    last discriminate.
  injection Closed as <-.
  exact (registered_closed_reference_valid Registered Ref).
Qed.

Lemma store_extension_final_registry old later :
  store_extension old later ->
  store_extension (upd_s_types old later.(s_types)) later.
Proof.
  destruct old, later.
  unfold store_extension, upd_s_types. simpl.
  rewrite canonical_registry_prefixb_refl andbT.
  move/andP => [Components _]. exact Components.
Qed.

Lemma imported_table_views C old later names imports sources values actual expected :
  store_extension old later ->
  canonical_registry_valid later.(s_types) ->
  source_type_identitiesb later.(s_types) names C.(tc_types) names ->
  List.Forall2 (module_import_typing C) imports sources ->
  List.Forall2 (external_typing old) values actual ->
  List.Forall2 (closed_import_subtyping later.(s_types)) actual expected ->
  those (map (close_import_desc later.(s_types) names) (map imp_desc imports)) =
    Some expected ->
  all2 (instance_table_view later names) (ext_tables values) (ext_t_tables sources).
Proof.
  move => Extension Registry Identities Typed.
  have Registered := registered_type_names Identities.
  move: values actual expected.
  induction Typed as [|imp source imports sources Head Tail IH];
    move => values actual expected Values Matches Closed.
  - simpl in Closed. injection Closed as <-.
    inversion Matches; subst. inversion Values; subst. reflexivity.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_import_desc (s_types later) names (imp_desc imp))
      as [expected_head|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_import_desc (s_types later) names)
      (map imp_desc imports))) as [expected_tail|] eqn:Entries; last discriminate.
    injection Closed as <-.
    inversion Matches as [|actual_head expected0 actual_tail expected1 MatchHead MatchTail];
      subst; clear Matches.
    inversion Values as [|value actual0 value_tail actual1 ValueHead ValueTail];
      subst; clear Values.
    have Rest := IH _ _ _ ValueTail MatchTail ltac:(by rewrite -those_those0).
    have OriginalMatch := MatchHead.
    destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    unfold external_typing, ext_typing in ValueHead.
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      remove_bools_options; subst; try congruence;
      destruct value; destruct actual_head; simpl in ValueHead; try discriminate;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; try congruence;
      unfold closed_import_subtyping in MatchHead; simpl in MatchHead;
      try discriminate; simpl in *; try exact Rest.
    match goal with Same : ET_table _ = ET_table _ |- _ => injection Same as <- end.
    apply/andP; split; last exact Rest.
    eapply instance_table_view_extension; first exact (store_extension_final_registry Extension).
    eapply checked_table_import_view; try eassumption.
    eapply registered_closed_table_valid; eauto.
Qed.

Lemma registered_closed_global_valid registry names source closed :
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_global_type names source = Some closed ->
  closed_value_validb registry closed.(tg_t).
Proof.
  move => Registered Closed.
  destruct (close_global_type_agreement _ _ _ Closed) as [_ Value].
  exact (registered_closed_value_valid Registered Value).
Qed.

Lemma imported_global_views C old later names imports sources values actual expected :
  store_extension old later ->
  canonical_registry_valid later.(s_types) ->
  source_type_identitiesb later.(s_types) names C.(tc_types) names ->
  List.Forall2 (module_import_typing C) imports sources ->
  List.Forall2 (external_typing old) values actual ->
  List.Forall2 (closed_import_subtyping later.(s_types)) actual expected ->
  those (map (close_import_desc later.(s_types) names) (map imp_desc imports)) =
    Some expected ->
  all2 (instance_global_view later names) (ext_globals values) (ext_t_globals sources).
Proof.
  move => Extension Registry Identities Typed.
  have Registered := registered_type_names Identities.
  move: values actual expected.
  induction Typed as [|imp source imports sources Head Tail IH];
    move => values actual expected Values Matches Closed.
  - simpl in Closed. injection Closed as <-.
    inversion Matches; subst. inversion Values; subst. reflexivity.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_import_desc (s_types later) names (imp_desc imp))
      as [expected_head|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_import_desc (s_types later) names)
      (map imp_desc imports))) as [expected_tail|] eqn:Entries; last discriminate.
    injection Closed as <-.
    inversion Matches as [|actual_head expected0 actual_tail expected1 MatchHead MatchTail];
      subst; clear Matches.
    inversion Values as [|value actual0 value_tail actual1 ValueHead ValueTail];
      subst; clear Values.
    have Rest := IH _ _ _ ValueTail MatchTail ltac:(by rewrite -those_those0).
    have OriginalMatch := MatchHead.
    destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    unfold external_typing, ext_typing in ValueHead.
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      remove_bools_options; subst; try congruence;
      destruct value; destruct actual_head; simpl in ValueHead; try discriminate;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; try congruence;
      unfold closed_import_subtyping in MatchHead; simpl in MatchHead;
      try discriminate; simpl in *; try exact Rest.
    match goal with Same : ET_global _ = ET_global _ |- _ => injection Same as <- end.
    apply/andP; split; last exact Rest.
    eapply instance_global_view_extension; first exact (store_extension_final_registry Extension).
    eapply checked_global_import_view; try eassumption.
    eapply registered_closed_global_valid; eauto.
Qed.

Lemma canonical_value_matches_refl registry value :
  canonical_registry_valid registry ->
  closed_value_validb registry value ->
  closed_value_matchesb registry value value.
Proof.
  move => Registry Valid.
  apply (proj2 (closed_value_matchesb_correct _ _ _ (proj1 (proj2 Registry)))).
  apply closed_value_matches_refl_valid.
  by apply closed_value_validb_correct.
Qed.

Lemma defined_table_view s names source address closed :
  canonical_registry_valid s.(s_types) ->
  ext_table_typing s address = Some closed ->
  close_table_type names source = Some closed ->
  closed_value_validb s.(s_types) (closed_reference_value closed.(tt_elem_type)) ->
  instance_table_view s names address source.
Proof.
  move => Registry Actual Closed Valid.
  eapply checked_table_import_view; try eassumption.
  unfold closed_import_subtyping, closed_reference_equivb, limits_subtyping.
  rewrite (canonical_value_matches_refl Registry Valid) N.leb_refl /=.
  destruct (lim_max (tt_limits closed)); [by rewrite N.leb_refl|reflexivity].
Qed.

Lemma defined_global_view s names source address closed :
  canonical_registry_valid s.(s_types) ->
  ext_global_typing s address = Some closed ->
  close_global_type names source = Some closed ->
  closed_value_validb s.(s_types) closed.(tg_t) ->
  instance_global_view s names address source.
Proof.
  move => Registry Actual Closed Valid.
  eapply checked_global_import_view; try eassumption.
  unfold closed_import_subtyping.
  rewrite eq_refl (canonical_value_matches_refl Registry Valid) /=.
  by destruct (tg_mut closed).
Qed.

Lemma defined_element_view s names source address element closed :
  canonical_registry_valid s.(s_types) ->
  lookup_N s.(s_elems) address = Some element ->
  eleminst_typing s element = Some closed ->
  close_reference_type names source = Some closed ->
  instance_element_view s names address source.
Proof.
  move => Registry Actual Typed Closed.
  have Valid : closed_value_validb (s_types s) (closed_reference_value closed).
  { unfold eleminst_typing in Typed.
    destruct element as [descriptor refs].
    destruct (_ && _) eqn:Accepted; last discriminate.
    injection Typed as <-. by move/andP: Accepted => [Valid _]. }
  unfold instance_element_view. rewrite Actual Closed Typed Valid.
  by rewrite (canonical_value_matches_refl Registry Valid).
Qed.

Lemma accepted_closed_value_valid s value expected :
  closed_value_typing s value expected ->
  closed_value_validb s.(s_types) expected.
Proof.
  unfold closed_value_typing.
  destruct (typeof_closed_value s value); last discriminate.
  by move/andP => [/andP [_ Valid] _].
Qed.

Lemma closed_global_initial_values s names globals values closed :
  List.Forall2 (fun g v => value_typing s names v g.(modglob_type).(tg_t))
    globals values ->
  those (map (close_global_type names) (map modglob_type globals)) = Some closed ->
  List.Forall2 (fun gt v => closed_value_typing s v gt.(tg_t)) closed values.
Proof.
  move => Typed. move: closed.
  induction Typed as [|g v globals values Head Tail IH]; move => closed Closed.
  - simpl in Closed. injection Closed as <-. constructor.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_global_type names (modglob_type g)) as [descriptor|] eqn:Entry;
      last discriminate.
    destruct (those0 (map (close_global_type names) (map modglob_type globals)))
      as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-. constructor.
    + destruct (close_global_type_agreement _ _ _ Entry) as [_ Value].
      unfold value_typing in Head. by rewrite Value in Head.
    + apply IH. by rewrite -those_those0.
Qed.

Lemma closed_global_instances_typed s descriptors values :
  List.Forall2 (fun gt v => closed_value_typing s v gt.(tg_t)) descriptors values ->
  List.Forall (fun gi => exists gt, globalinst_typing s gi = Some gt)
    (map (fun '(gt, v) => gen_global_instance gt v) (List.combine descriptors values)).
Proof.
  move => Typed. induction Typed as [|gt v descriptors values Head Tail IH];
    simpl; constructor; try exact IH.
  exists gt. unfold gen_global_instance, globalinst_typing. simpl.
  by rewrite Head (accepted_closed_value_valid Head).
Qed.

Lemma closed_table_initial_typed s names source closed ref :
  tabletype_valid source ->
  close_table_initial s.(s_types) names source = Some (closed, ref) ->
  tableinst_typing s (gen_table_instance closed ref) = Some closed.
Proof.
  move => Source Closed.
  unfold close_table_initial in Closed.
  destruct (close_table_type names source) as [descriptor|] eqn:Descriptor;
    last discriminate.
  destruct (lower_closed_null (s_types s) (closed_ref_heap (tt_elem_type descriptor)))
    as [initial|] eqn:Initial; last discriminate.
  injection Closed as <- <-.
  have Value := lower_closed_null_typed s _ _ Initial.
  destruct (close_table_type_metadata _ _ _ Descriptor) as [Limits Nullable].
  have SameNullable : closed_ref_nullable (tt_elem_type descriptor) =
      ref_nullable (tt_elem_type source).
  { unfold close_reference_type in Nullable.
    destruct (close_heap_type names N0 (ref_heap (tt_elem_type source)));
      last discriminate.
    injection Nullable as <-. reflexivity. }
  move/andP: Source => [NullableSource Bounds].
  have IsNullable : closed_ref_nullable (tt_elem_type descriptor) = true
    by rewrite SameNullable.
  have Typed : closed_value_typing s (VAL_ref initial)
      (closed_reference_value (tt_elem_type descriptor)).
  { destruct (tt_elem_type descriptor) as [nullable heap].
    simpl in *. by rewrite IsNullable. }
  unfold tableinst_typing, gen_table_instance.
  destruct descriptor as [[minimum maximum] reference]. simpl in *.
  rewrite -Limits in Bounds.
  rewrite IsNullable Bounds /=.
  rewrite List.repeat_length Nnat.N2Nat.id eq_refl.
  rewrite all_repeat; [reflexivity|exact Typed].
Qed.

Lemma closed_table_instances_typed s names sources initials :
  List.Forall tabletype_valid sources ->
  those (map (close_table_initial s.(s_types) names) sources) = Some initials ->
  List.Forall (fun ti => exists t, tableinst_typing s ti = Some t)
    (map (fun '(t, ref) => gen_table_instance t ref) initials).
Proof.
  move => Valid. move: initials.
  induction Valid as [|source sources Head Tail IH]; move => initials Closed.
  - simpl in Closed. injection Closed as <-. constructor.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_table_initial (s_types s) names source)
      as [[descriptor ref]|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_table_initial (s_types s) names) sources))
      as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-. simpl. constructor.
    + exists descriptor. exact (closed_table_initial_typed Head Entry).
    + apply IH. by rewrite -those_those0.
Qed.

Lemma closed_element_instances_typed s names elements references closed :
  List.Forall (fun id => defined_type_validb s.(s_types) id = true) names ->
  List.Forall2 (fun e refs =>
    List.Forall (fun ref => value_typing s names (VAL_ref ref)
      (T_ref e.(modelem_type))) refs) elements references ->
  those (map (close_reference_type names) (map modelem_type elements)) = Some closed ->
  List.Forall (fun ei => exists t, eleminst_typing s ei = Some t)
    (map (fun '(t, refs) => Build_eleminst t refs) (List.combine closed references)).
Proof.
  move => Registered Typed. move: closed.
  induction Typed as [|element refs elements references Head Tail IH];
    move => closed Closed.
  - simpl in Closed. injection Closed as <-. constructor.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_reference_type names (modelem_type element))
      as [descriptor|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_reference_type names) (map modelem_type elements)))
      as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-. simpl. constructor.
    + exists descriptor.
      change ((if closed_value_validb (s_types s) (closed_reference_value descriptor) &&
        all (fun ref => closed_value_typing s (VAL_ref ref)
          (closed_reference_value descriptor)) refs
        then Some descriptor else None) = Some descriptor).
      have Valid := registered_closed_reference_valid Registered Entry.
      rewrite Valid /=.
      suff Values : all (fun ref => closed_value_typing s (VAL_ref ref)
        (closed_reference_value descriptor)) refs by rewrite Values.
      apply Forall_all. eapply List.Forall_impl; last exact Head.
      move => ref Accepted. unfold value_typing in Accepted.
      by rewrite (close_reference_type_value _ _ _ Entry) in Accepted.
    + apply IH. by rewrite -those_those0.
Qed.

Lemma those_map_relation {A B} (f : A -> option B) xs ys :
  those (map f xs) = Some ys ->
  List.Forall2 (fun x y => f x = Some y) xs ys.
Proof.
  move => Closed. apply Forall2_spec.
  - have Length := those_length Closed. by rewrite List.length_map in Length.
  - move => n x y X Y.
    destruct (those_map_lookup Closed X) as [actual [Entry Slot]].
    rewrite Y in Slot. by injection Slot as <-.
Qed.

Lemma appended_instance_views {A B} (prefix items : list A) (sources : list B)
    (view : N -> B -> bool) :
  List.Forall2 (fun item source => forall address,
    lookup_N (prefix ++ items) address = Some item -> view address source) items sources ->
  all2 view (iota_N (length prefix) (length items)) sources.
Proof.
  move => Typed. apply all2_spec.
  - rewrite -!length_is_size iota_N_length.
    exact (List.Forall2_length Typed).
  - move => n address source Address Source.
    destruct (Forall2_nth_impl' Typed Source) as [item [Item View]].
    apply View.
    destruct (iota_N_lookup_Some Address) as [-> Bound].
    unfold lookup_N. rewrite Nnat.Nat2N.id List.nth_error_app2; last by lias.
    replace (length prefix + n - length prefix)%coq_nat with n; last by lias.
    exact Item.
Qed.

Lemma appended_component_types {A B} (prefix items : list A) (project : A -> B) :
  those (map (fun address => option_map project (lookup_N (prefix ++ items) address))
    (iota_N (length prefix) (length items))) = Some (map project items).
Proof.
  apply those_spec.
  - by rewrite !List.length_map length_is_size size_iota.
  - move => n projected Projected.
    rewrite nth_error_map' in Projected.
    destruct (List.nth_error items n) as [item|] eqn:Item; last discriminate.
    injection Projected as <-.
    rewrite nth_error_map' iota_N_lookup; last by apply nth_error_Some_length in Item; lias.
    cbn [option_map].
    unfold lookup_N. rewrite Nnat.Nat2N.id List.nth_error_app2; last by lias.
    replace (length prefix + n - length prefix)%coq_nat with n; last by lias.
    by rewrite Item.
Qed.

Lemma closed_import_memory_projection C imports sources registry names expected :
  List.Forall2 (module_import_typing C) imports sources ->
  those (map (close_import_desc registry names) (map imp_desc imports)) = Some expected ->
  closed_ext_t_mems expected = ext_t_mems sources.
Proof.
  move => Typed. move: expected.
  induction Typed as [|imp source imports sources Head Tail IH]; move => expected Closed.
  - simpl in Closed. by injection Closed as <-.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_import_desc registry names (imp_desc imp))
      as [external|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_import_desc registry names) (map imp_desc imports)))
      as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-.
    have Projection := IH rest ltac:(by rewrite -those_those0).
    destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      remove_bools_options; subst; try congruence;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; try congruence; simpl in *;
      try exact Projection.
    match goal with Same : ET_mem _ = ET_mem _ |- _ => injection Same as <- end.
    by rewrite Projection.
Qed.

Lemma registered_type_expansions registry names sources :
  source_type_identitiesb registry names sources names ->
  List.Forall (fun id => exists declaration,
    expand_defined_type registry id = Some declaration) names.
Proof.
  move/source_type_identitiesb_correct => Typed.
  induction Typed as [|source id sources ids [declaration [_ Expanded]] Tail IH].
  - constructor.
  - constructor; [by exists declaration|exact IH].
Qed.

Lemma registered_runtime_default registry names source closed :
  List.Forall (fun id => exists declaration,
    expand_defined_type registry id = Some declaration) names ->
  close_value_type names N0 source = Some closed ->
  default_val source <> None ->
  exists value, runtime_default_val registry names source = Some value.
Proof.
  move => Registered Closed Defaultable.
  destruct source as [number|vector|[nullable heap]|]; try contradiction.
  - by eexists.
  - by eexists.
  - destruct nullable; last by exfalso; apply Defaultable.
    destruct heap; try by eexists.
    cbn [close_value_type ref_heap ref_nullable close_heap_type] in Closed.
    unfold close_type_index in Closed.
    destruct (N.ltb t (N.of_nat (length names))) eqn:Bound.
    + destruct (List.nth_error names (N.to_nat t)) as [id|] eqn:Name;
        last discriminate.
      rewrite List.Forall_forall in Registered.
      destruct (Registered id (List.nth_error_In _ _ Name)) as [declaration Expanded].
      unfold runtime_default_val, close_value_type. simpl.
      unfold close_type_index. rewrite Bound Name /=.
      unfold lower_closed_null, defined_heap_kind.
      rewrite Expanded.
      destruct (subtype_composite declaration); by eexists.
    + have Zero : N.ltb (t - N.of_nat (length names)) N0 = false
        by apply N.ltb_ge; lia.
      by rewrite Zero in Closed.
Qed.

Lemma runtime_default_val_portable old_registry old_names registry names sources source value :
  source_type_identitiesb registry names sources names ->
  length old_names = length names ->
  runtime_default_val old_registry old_names source = Some value ->
  exists target, runtime_default_val registry names source = Some target.
Proof.
  move => Identities Length Accepted.
  have Defaultable : default_val source <> None.
  { destruct source as [number|vector|[nullable heap]|].
    - discriminate.
    - discriminate.
    - destruct nullable; first discriminate.
      unfold runtime_default_val, close_value_type in Accepted. simpl in Accepted.
       destruct (close_heap_type old_names N0 heap); discriminate.
    - discriminate. }
  unfold runtime_default_val in Accepted.
  destruct (close_value_type old_names N0 source) as [closed|] eqn:Closed;
    last discriminate.
  destruct (close_value_type_name_portability Length (registered_type_names Identities) Closed)
    as [target [Target Valid]].
  exact (registered_runtime_default (registered_type_expansions Identities) Target Defaultable).
Qed.

Lemma runtime_default_vals_portable old_registry old_names registry names sources locals :
  source_type_identitiesb registry names sources names ->
  length old_names = length names ->
  runtime_default_vals old_registry old_names locals <> None ->
  runtime_default_vals registry names locals <> None.
Proof.
  move => Identities Length.
  unfold runtime_default_vals. rewrite -!those_those0.
  induction locals as [|local locals IH]; first discriminate.
  simpl.
  destruct (runtime_default_val old_registry old_names local) as [value|] eqn:Value;
    last by move => Impossible; exfalso; apply Impossible.
  destruct (those0 (map (runtime_default_val old_registry old_names) locals))
    as [values|] eqn:Values; last by move => Impossible; exfalso; apply Impossible.
  move => _.
  destruct (runtime_default_val_portable Identities Length Value) as [target Target].
  rewrite Target /=.
  have Tail : those0 (map (runtime_default_val registry names) locals) <> None.
  { apply IH. discriminate. }
  destruct (those0 (map (runtime_default_val registry names) locals)).
  - discriminate.
  - exfalso. apply Tail. reflexivity.
Qed.

Definition source_context_memories (C : t_context) memories : t_context :=
  Build_t_context C.(tc_types) C.(tc_funcs) C.(tc_tables) memories
    C.(tc_globals) C.(tc_elems) C.(tc_datas) C.(tc_locals)
    C.(tc_labels) C.(tc_return) C.(tc_refs) C.(tc_defined_types).

Lemma source_context_memories_typing C memories es tf :
  size memories = size C.(tc_mems) ->
  be_typing C es tf ->
  be_typing (source_context_memories C memories) es tf.
Proof.
  move => Length Typed.
  eapply context_agree_be_typing; last exact Typed.
  unfold context_agree, source_context_memories. simpl.
  rewrite !eq_refl /=.
  have Functions : all2 func_agree (tc_funcs C) (tc_funcs C).
  { apply reflexive_all2_same. move => function. by apply/eqP. }
  have Tables : all2 table_agree (tc_tables C) (tc_tables C).
  { apply reflexive_all2_same. move => table. by apply/eqP. }
  have Globals : all2 global_agree (tc_globals C) (tc_globals C).
  { apply reflexive_all2_same. move => global. by apply/eqP. }
  rewrite Functions Tables Globals /= !andbT.
  apply all2_spec; [symmetry; exact Length|].
  by move => n a b A B.
Qed.

Lemma scoped_heap_closes names types heap :
  length types = length names ->
  source_heap_scopedb types heap ->
  exists closed, close_heap_type names N0 heap = Some closed.
Proof.
  move => Length Scoped.
  destruct heap; try by eexists.
  unfold source_heap_scopedb in Scoped.
  destruct (lookup_N types t) as [source|] eqn:Source; last discriminate.
  have Bound : (N.to_nat t < length names)%coq_nat.
  { apply nth_error_Some_length in Source. by lias. }
  have Compare : N.ltb t (N.of_nat (length names)) = true
    by apply N.ltb_lt; lia.
  unfold close_heap_type, close_type_index. rewrite Compare.
  destruct (List.nth_error names (N.to_nat t)) as [id|] eqn:Name.
  - by eexists.
  - apply List.nth_error_None in Name. lia.
Qed.

Lemma registered_source_null_total s inst types heap :
  length types = length inst.(inst_defined_types) ->
  List.Forall (fun id => exists declaration,
    expand_defined_type s.(s_types) id = Some declaration) inst.(inst_defined_types) ->
  source_heap_scopedb types heap ->
  exists ref, lower_source_null s inst heap = Some ref.
Proof.
  move => Length Registered Scoped.
  destruct (scoped_heap_closes Length Scoped) as [closed Closed].
  have ValueClosed : close_value_type (inst_defined_types inst) N0
      (T_ref (Ref_type true heap)) = Some (CV_ref true closed).
  { by rewrite /close_value_type /= Closed. }
  destruct (registered_runtime_default Registered ValueClosed ltac:(discriminate))
    as [value Runtime].
  unfold runtime_default_val in Runtime. rewrite ValueClosed in Runtime.
  destruct (lower_closed_null (s_types s) closed) as [ref|] eqn:Lower;
    last discriminate.
  exists ref. by rewrite /lower_source_null Closed.
Qed.

Lemma closed_value_typing_world s later value expected :
  s.(s_types) = later.(s_types) ->
  s.(s_funcs) = later.(s_funcs) ->
  closed_value_typing s value expected = closed_value_typing later value expected.
Proof.
  move => Types Functions.
  unfold closed_value_typing, typeof_closed_value, typeof_closed_ref,
    lookup_func_defined_type, funcinst_defined_type.
  by rewrite Types Functions.
Qed.

Lemma function_suffix_extension s functions groups :
  store_extension s
    (Build_store_record (s_funcs s ++ functions) (s_tables s) (s_mems s)
      (s_globals s) (s_elems s) (s_datas s) (s_types s ++ groups)).
Proof.
  have Same := store_extension_same s.
  unfold store_extension in Same |- *. simpl.
  have Prefix : canonical_registry_prefixb (s_types s) (s_types s ++ groups).
  { apply canonical_registry_prefixb_correct. by exists groups. }
  have Functions : component_extension func_extension (s_funcs s) (s_funcs s ++ functions).
  { unfold component_extension.
    rewrite !length_is_size size_cat leq_addr /=.
    rewrite take_size_cat; [apply all2_func_extension_same|reflexivity]. }
  rewrite Functions Prefix /=.
  remove_bools_options. by rewrite H1 H2 H3 H4 H5.
Qed.

Lemma function_preview_properties s m imports registry names source allocated addresses :
  store_typing s ->
  close_and_validate_type_groups (s_types s) (module_type_groups m) =
    Some (registry, names) ->
  source_type_identitiesb registry names (List.concat (mod_types m)) names ->
  module_source_context m = Some source ->
  alloc_funcs s (mod_funcs m) (module_runtime_instance s m imports names source) =
    (allocated, addresses) ->
  store_extension s (upd_s_types allocated registry) /\
  canonical_registry_valid registry /\
  registered_function_references (upd_s_types allocated registry).
Proof.
  move => Store Closed Identities Source Allocated.
  destruct (close_and_validate_type_groups_sound _ _ _ _ Closed) as [Valid Closing].
  destruct (close_type_groups_extension_public _ _ _ _ Closing) as [groups Prefix].
  pose inst := module_runtime_instance s m imports names source.
  have Facts := alloc_func_iota_N Allocated.
  have World : upd_s_types allocated registry =
      Build_store_record (s_funcs s ++ map (fun code => gen_func_instance code inst)
        (mod_funcs m)) (s_tables s) (s_mems s) (s_globals s) (s_elems s) (s_datas s) registry.
  { destruct s, allocated. simpl in *.
    destruct Facts as [_ [Functions [Tables [Memories [Globals [Elements Data]]]]]].
    subst. reflexivity. }
  split.
  - rewrite World Prefix. apply function_suffix_extension.
  - split; first exact Valid.
    move => address function Lookup.
    have Original := Lookup.
    rewrite World /= in Lookup.
    unfold lookup_N in Lookup.
    destruct (Nat.lt_ge_cases (N.to_nat address) (length (s_funcs s))) as [Old|New].
    + rewrite List.nth_error_app1 in Lookup; last exact Old.
      eapply registered_references_prefix.
      * exact (checked_store_registers_function_references Store).
      * by rewrite World.
      * exact Prefix.
      * exact Lookup.
    + rewrite List.nth_error_app2 in Lookup; last exact New.
      apply List.nth_error_In in Lookup.
      apply List.in_map_iff in Lookup as [code [Same Member]]. subst function.
      destruct (module_source_function_lookup Source Member) as [signature Function].
      have Checked : source_type_identitiesb registry (inst_defined_types inst)
          (inst_types inst) (inst_defined_types inst) by exact Identities.
      destruct (source_function_registered Checked Function)
        as [id [concrete [Resolved Expanded]]].
      eapply registered_reference_from_expansion.
      * unfold lookup_func_defined_type.
        rewrite Original /gen_func_instance Function /funcinst_defined_type.
        exact Resolved.
      * exact Expanded.
Qed.

Lemma closed_import_function_count C imports sources registry names expected :
  List.Forall2 (module_import_typing C) imports sources ->
  those (map (close_import_desc registry names) (map imp_desc imports)) = Some expected ->
  length (closed_ext_t_funcs expected) = length (ext_t_funcs sources).
Proof.
  move => Typed. move: expected.
  induction Typed as [|imp source imports sources Head Tail IH]; move => expected Closed.
  - simpl in Closed. by injection Closed as <-.
  - rewrite -those_those0 in Closed. cbn [map those0] in Closed.
    destruct (close_import_desc registry names (imp_desc imp))
      as [external|] eqn:Entry; last discriminate.
    destruct (those0 (map (close_import_desc registry names) (map imp_desc imports)))
      as [rest|] eqn:Rest; last discriminate.
    injection Closed as <-.
    have Count := IH rest ltac:(by rewrite -those_those0).
    destruct imp as [module_name item_name descriptor].
    unfold module_import_typing, module_import_desc_typing in Head.
    destruct descriptor; destruct source; simpl in Head; try discriminate;
      remove_bools_options; subst; try congruence;
      unfold close_import_desc in Entry; simpl in Entry;
      remove_bools_options; subst; try congruence; simpl in *;
      try exact Count.
    by rewrite Count.
Qed.

Lemma close_reference_names_portable registry old names source closed :
  length old = length names ->
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_reference_type old source = Some closed ->
  exists target, close_reference_type names source = Some target.
Proof.
  move => Length Registered Closed.
  have Value := close_reference_type_value _ _ _ Closed.
  destruct (close_value_type_name_portability Length Registered Value)
    as [target [Target Valid]].
  unfold close_value_type in Target.
  destruct (close_heap_type names N0 (ref_heap source)) as [heap|] eqn:Heap;
    last discriminate.
  exists (Closed_ref (ref_nullable source) heap).
  by rewrite /close_reference_type Heap.
Qed.

Lemma close_global_names_portable registry old names source closed :
  length old = length names ->
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_global_type old source = Some closed ->
  exists target, close_global_type names source = Some target.
Proof.
  move => Length Registered Closed.
  destruct (close_global_type_agreement _ _ _ Closed) as [_ Value].
  destruct (close_value_type_name_portability Length Registered Value)
    as [target [Target Valid]].
  exists (Build_global_type (tg_mut source) target).
  by rewrite /close_global_type Target.
Qed.

Lemma close_table_initial_names_portable registry old names source closed :
  length old = length names ->
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  List.Forall (fun id => exists declaration,
    expand_defined_type registry id = Some declaration) names ->
  tabletype_valid source ->
  close_table_type old source = Some closed ->
  exists initial, close_table_initial registry names source = Some initial.
Proof.
  move => Length Registered Expansions Valid Closed.
  destruct (close_table_type_metadata _ _ _ Closed) as [_ Reference].
  destruct (close_reference_names_portable Length Registered Reference)
    as [reference NewReference].
  have Value := close_reference_type_value _ _ _ NewReference.
  have Defaultable : default_val (T_ref (tt_elem_type source)) <> None.
  { move/andP: Valid => [Nullable _]. by rewrite /default_val Nullable. }
  destruct (registered_runtime_default Expansions Value Defaultable)
    as [value Runtime].
  unfold runtime_default_val in Runtime. rewrite Value in Runtime.
  unfold close_table_initial, close_table_type. rewrite NewReference /=.
  destruct reference as [nullable heap].
  destruct nullable; simpl in Runtime; last discriminate.
  destruct (lower_closed_null registry heap) as [ref|] eqn:Lower;
    last discriminate.
  simpl. rewrite Lower. by eexists.
Qed.

Lemma module_storage_closings_portable old_registry old_names registry names m :
  module_runtime_types_closedb old_registry old_names m ->
  length old_names = length names ->
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  List.Forall (fun id => exists declaration,
    expand_defined_type registry id = Some declaration) names ->
  List.Forall tabletype_valid (map modtab_type (mod_tables m)) ->
  exists tables globals elements,
    those (map (close_table_initial registry names) (map modtab_type (mod_tables m))) =
      Some tables /\
    those (map (close_global_type names) (map modglob_type (mod_globals m))) =
      Some globals /\
    those (map (close_reference_type names) (map modelem_type (mod_elems m))) =
      Some elements.
Proof.
  move => Runtime Length Registered Expansions ValidTables.
  unfold module_runtime_types_closedb in Runtime.
  destruct (module_source_context m) as [source|] eqn:Source; last discriminate.
  have Imports := Logic.eq_refl
    (those (map (source_import_signature (List.concat (mod_types m))) (mod_imports m))).
  destruct (those (map (source_import_signature (List.concat (mod_types m))) (mod_imports m)))
    as [imports|] eqn:Imported.
  all: unfold module_source_context in Source.
  all: unfold source_import_signature in Imported.
  all: rewrite Imported in Source.
  all: destruct (those (map (fun f => lookup_function_type (List.concat (mod_types m))
    (modfunc_type f)) (mod_funcs m))) as [functions|] eqn:Functions;
    try discriminate.
  injection Source as <-.
  cbn [tc_tables tc_globals tc_elems] in Runtime.
  move/andP: Runtime => [/andP [/andP [Tables Globals] Elements] Defaults].
  rewrite all_cat in Tables.
  move/andP: Tables => [_ Tables].
  rewrite all_cat in Globals.
  move/andP: Globals => [_ Globals].
  have TableClosing : exists initial,
      those (map (close_table_initial registry names) (map modtab_type (mod_tables m))) =
        Some initial.
  { apply those_map_total. apply Forall_spec. move => n table Table.
    have Checked := all_projection Tables Table.
    destruct (close_table_type old_names table) as [closed|] eqn:Closed;
      last discriminate.
    have Valid : tabletype_valid table.
    { rewrite List.Forall_forall in ValidTables.
      exact (ValidTables table (List.nth_error_In _ _ Table)). }
    exact (close_table_initial_names_portable Length Registered Expansions Valid Closed). }
  have GlobalClosing : exists globals,
      those (map (close_global_type names) (map modglob_type (mod_globals m))) =
        Some globals.
  { apply those_map_total. apply Forall_spec. move => n global Global.
    have Checked := all_projection Globals Global.
    destruct (close_global_type old_names global) as [closed|] eqn:Closed;
      last discriminate.
    exact (close_global_names_portable Length Registered Closed). }
  have ElementClosing : exists elements,
      those (map (close_reference_type names) (map modelem_type (mod_elems m))) =
        Some elements.
  { apply those_map_total. apply Forall_spec. move => n element Element.
    have Checked := all_projection Elements Element.
    destruct (close_reference_type old_names element) as [closed|] eqn:Closed;
      last discriminate.
    exact (close_reference_names_portable Length Registered Closed). }
  destruct TableClosing as [tables TableClosed], GlobalClosing as [globals GlobalClosed],
    ElementClosing as [elements ElementClosed].
  exists tables, globals, elements. auto.
Qed.

End Imports.
