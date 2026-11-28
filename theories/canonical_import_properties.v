(* Final Core 3.0 external matching, on closed descriptors.  In particular,
   function imports match defined types, not just expanded function signatures.
   Spec pin: d7aada502455b3d9176ca4cbe48be4724d511d2a,
   document/core/valid/matching.rst, match-externtype and match-deftype. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Stdlib Require Import List NArith.
From Wasm Require Import instantiation_func closed_instantiation_properties
  gc_declaration_typing gc_declaration_typing_properties gc_type_context_properties
  gc_type_context.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition canonical_limits_matching (actual expected : limits) : Prop :=
  (expected.(lim_min) <= actual.(lim_min))%N /\
  match actual.(lim_max), expected.(lim_max) with
  | _, None => True
  | Some a, Some e => (a <= e)%N
  | None, Some _ => False
  end.

Definition canonical_extern_matching registry (actual expected : closed_extern_type) : Prop :=
  match actual, expected with
  | CET_func a, CET_func e =>
      exists af ef n,
        expand_function_type registry a = Some af /\
        expand_function_type registry e = Some ef /\
        declared_type_path registry n a e
  | CET_table a, CET_table e =>
      canonical_limits_matching a.(tt_limits) e.(tt_limits) /\
      closed_value_matches registry (closed_reference_value a.(tt_elem_type))
        (closed_reference_value e.(tt_elem_type)) /\
      closed_value_matches registry (closed_reference_value e.(tt_elem_type))
        (closed_reference_value a.(tt_elem_type))
  | CET_mem a, CET_mem e => canonical_limits_matching a e
  | CET_global a, CET_global e =>
      a.(tg_mut) = e.(tg_mut) /\
      closed_value_matches registry a.(tg_t) e.(tg_t) /\
      match e.(tg_mut) with
      | MUT_const => True
      | MUT_var => closed_value_matches registry e.(tg_t) a.(tg_t)
      end
  | _, _ => False
  end.

Lemma canonical_limits_matching_correct a e :
  limits_subtyping a e = true <-> canonical_limits_matching a e.
Proof.
  unfold limits_subtyping, canonical_limits_matching.
  rewrite Bool.andb_true_iff N.leb_le.
  destruct (lim_max a), (lim_max e); simpl;
    try rewrite N.leb_le; intuition congruence.
Qed.

Theorem canonical_extern_matching_correct registry actual expected :
  canonical_registry_valid registry ->
  (closed_import_subtyping registry actual expected = true <->
    canonical_extern_matching registry actual expected).
Proof.
  move => Registry.
  have WF := proj1 (proj2 Registry).
  destruct actual as [a|a|a|a], expected as [e|e|e|e];
    unfold closed_import_subtyping, canonical_extern_matching; try tauto;
    try (split; [discriminate|contradiction]).
  - destruct (expand_function_type registry a) as [af|] eqn:Actual;
      destruct (expand_function_type registry e) as [ef|] eqn:Expected.
    + split.
      * move/defined_type_matches_sound => [n Path].
        exists af, ef, n. auto.
      * move => [af' [ef' [n [_ [_ Path]]]]].
        exact (defined_type_matches_complete _ _ _ _ WF Path).
    + split; [discriminate|move => [af' [ef' [n [_ [Impossible _]]]]]; discriminate].
    + split; [discriminate|move => [af' [ef' [n [Impossible _]]]]; discriminate].
    + split; [discriminate|move => [af' [ef' [n [Impossible _]]]]; discriminate].
  - unfold closed_reference_equivb.
    rewrite Bool.andb_true_iff canonical_limits_matching_correct.
    rewrite Bool.andb_true_iff.
    rewrite (closed_value_matchesb_correct _ _ _ WF).
    rewrite (closed_value_matchesb_correct _ _ _ WF). tauto.
  - apply canonical_limits_matching_correct.
  - rewrite Bool.andb_true_iff Bool.andb_true_iff.
    rewrite (closed_value_matchesb_correct _ _ _ WF).
    have Mut : ((tg_mut a == tg_mut e) = true <-> tg_mut a = tg_mut e).
    { split; first by move/eqP. by move => ->; rewrite eq_refl. }
    rewrite Mut.
    destruct (tg_mut a), (tg_mut e); simpl;
      try rewrite (closed_value_matchesb_correct _ _ _ WF); intuition congruence.
Qed.

Section Host.
Context `{ho : host}.

(* This is a pre-instantiation import contract.  It contains no initializer
   result, output-store typing, or assumed successful instantiation. *)
Definition canonical_module_imports s m actual : Prop :=
  exists registry names expected,
    close_and_validate_type_groups s.(s_types) (module_type_groups m) =
      Some (registry, names) /\
    those (map (close_import_desc registry names) (map imp_desc m.(mod_imports))) =
      Some expected /\
    List.Forall2 (canonical_extern_matching registry) actual expected.

Definition canonical_import_checker s m values : bool :=
  match close_and_validate_type_groups s.(s_types) (module_type_groups m) with
  | Some (registry, names) =>
      match those (map (external_type_checker s) values),
            those (map (close_import_desc registry names) (map imp_desc m.(mod_imports))) with
      | Some actual, Some expected => all2 (closed_import_subtyping registry) actual expected
      | _, _ => false
      end
  | None => false
  end.

Lemma external_import_checker_correct s values actual :
  those (map (external_type_checker s) values) = Some actual <->
  List.Forall2 (external_typing s) values actual.
Proof.
  split.
  - move => Checked. exact (those_map_relation Checked).
  - move => Typed. induction Typed as [|value descriptor values actual Head Tail IH].
    + reflexivity.
    + rewrite -those_those0 in IH.
      by rewrite -those_those0 /= /external_type_checker Head IH.
Qed.

Theorem canonical_import_checker_correct s m values :
  canonical_import_checker s m values = true <->
  exists actual, List.Forall2 (external_typing s) values actual /\
    canonical_module_imports s m actual.
Proof.
  unfold canonical_import_checker.
  destruct (close_and_validate_type_groups (s_types s) (module_type_groups m))
    as [[registry names]|] eqn:Closed.
  - have Valid := proj1 (close_and_validate_type_groups_sound _ _ _ _ Closed).
    destruct (those (map (external_type_checker s) values)) as [actual|] eqn:Actual;
      destruct (those (map (close_import_desc registry names)
        (map imp_desc (mod_imports m)))) as [expected|] eqn:Expected.
    + split.
      * move => Matched. exists actual. split.
        -- by apply external_import_checker_correct.
        -- exists registry, names, expected. repeat split; try assumption.
           apply Forall2_all2_impl with (f := closed_import_subtyping registry);
             [|exact Matched].
           move => a e Match.
           exact (proj1 (canonical_extern_matching_correct _ _ Valid) Match).
      * move => [actual' [Typed [registry' [names' [expected'
          [Closed' [Expected' Matching]]]]]]].
        rewrite Closed in Closed'. injection Closed' as <- <-.
        rewrite Expected in Expected'. injection Expected' as <-.
        apply external_import_checker_correct in Typed.
        rewrite Actual in Typed. injection Typed as <-.
        apply Forall2_all2.
        eapply Forall2_impl; last exact Matching.
        move => a e Match.
        exact (proj2 (canonical_extern_matching_correct _ _ Valid) Match).
    + split; [discriminate|].
      move => [actual' [Typed [registry' [names' [expected'
        [Closed' [Expected' _]]]]]]].
      rewrite Closed in Closed'. injection Closed' as <- <-.
      by rewrite Expected in Expected'.
    + split; [discriminate|].
      move => [actual' [Typed _]].
      apply external_import_checker_correct in Typed. by rewrite Actual in Typed.
    + split; [discriminate|].
      move => [actual' [Typed _]].
      apply external_import_checker_correct in Typed. by rewrite Actual in Typed.
  - split; [discriminate|].
    move => [actual [Typed [registry [names [expected [Impossible _]]]]]].
    by rewrite Closed in Impossible.
Qed.

Theorem successful_instantiation_checks_canonical_imports hs s m values result message :
  interp_instantiate hs s m values = (Some result, message) ->
  canonical_import_checker s m values = true.
Proof.
  unfold interp_instantiate.
  destruct (module_type_checker m) as [[[impts exports]|] diagnostic]; last discriminate.
  destruct (close_and_validate_type_groups (s_types s) (module_type_groups m))
    as [[registry names]|] eqn:Closed; last discriminate.
  destruct (source_type_identitiesb registry names (List.concat (mod_types m)) names);
    last discriminate.
  destruct (those (seq.map (external_type_checker s) values)) as [actual|] eqn:Actual;
  destruct (those (seq.map (close_import_desc registry names) (seq.map imp_desc (mod_imports m))))
    as [expected|] eqn:Expected;
  destruct (module_source_context m); try discriminate.
  destruct (all2 (closed_import_subtyping registry) actual expected) eqn:Matched;
    last discriminate.
  move => _.
  have ActualCompat : those (map (external_type_checker s) values) = Some actual
    by exact Actual.
  have ExpectedCompat : those (map (close_import_desc registry names)
      (map imp_desc (mod_imports m))) = Some expected by exact Expected.
  by rewrite /canonical_import_checker Closed ActualCompat ExpectedCompat Matched.
Qed.

Lemma limits_subtyping_refl limits : limits_subtyping limits limits.
Proof.
  unfold limits_subtyping. rewrite N.leb_refl /=.
  destruct (lim_max limits); [by rewrite N.leb_refl|reflexivity].
Qed.

Lemma checked_import_descriptor_reflexive registry names source closed :
  canonical_registry_valid registry ->
  List.Forall (fun id => defined_type_validb registry id = true) names ->
  close_import_desc registry names source = Some closed ->
  closed_import_subtyping registry closed closed.
Proof.
  move => Registry Registered Closed.
  destruct source; unfold close_import_desc in Closed; remove_bools_options; subst;
    unfold closed_import_subtyping.
  - by rewrite Hoption0 defined_type_matches_refl.
  - have Valid := registered_closed_table_valid Registered Hoption.
    unfold closed_reference_equivb.
    by rewrite (canonical_value_matches_refl Registry Valid) limits_subtyping_refl.
  - exact (limits_subtyping_refl m).
  - have Valid := registered_closed_global_valid Registered Hoption.
    rewrite eq_refl (canonical_value_matches_refl Registry Valid) /=.
    by destruct (tg_mut c).
Qed.

Lemma checked_identity_imports s m actual registry names :
  close_and_validate_type_groups (s_types s) (module_type_groups m) =
    Some (registry, names) ->
  source_type_identitiesb registry names (List.concat (mod_types m)) names ->
  those (map (close_import_desc registry names) (map imp_desc (mod_imports m))) =
    Some actual ->
  canonical_module_imports s m actual.
Proof.
  move => Closed Identity Imports.
  have Valid := proj1 (close_and_validate_type_groups_sound _ _ _ _ Closed).
  have Registered := registered_type_names Identity.
  exists registry, names, actual. split; first exact Closed.
  split; first exact Imports.
  have Entries := those_map_relation Imports.
  clear Imports.
  induction Entries as [|source descriptor sources descriptors Head Tail IH]; constructor;
    try exact IH.
  apply (proj1 (canonical_extern_matching_correct _ _ Valid)).
  exact (checked_import_descriptor_reflexive Valid Registered Head).
Qed.

End Host.
