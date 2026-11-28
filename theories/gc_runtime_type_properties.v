(** Production source/closed signature agreement in composite type contexts.
    Store typing checks the identity map, and store extension preserves
    the canonical registry prefix, including across host applications. *)
From Wasm Require Import typing properties gc_type_context gc_type_context_properties
  gc_declaration_typing gc_declaration_typing_properties.
From Wasm Require Import gc_function_subtyping_properties.
From Stdlib Require Import List NArith Lia.
From mathcomp Require Import ssreflect ssrbool.
Import ListNotations.

Section Host.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Theorem store_typing_canonical_registry s :
  store_typing s -> canonical_registry_valid s.(s_types).
Proof.
  intros [Valid _]. now apply canonical_registry_validb_correct.
Qed.

Theorem instance_table_element_typing s inst C index offset source ref :
  store_typing s ->
  inst_typing s inst = Some C ->
  lookup_N C.(tc_tables) index = Some source ->
  stab_elem s inst index offset = Some ref ->
  value_typing s inst.(inst_defined_types) (VAL_ref ref) (T_ref source.(tt_elem_type)).
Proof.
  intros Store Instance Source Element.
  destruct (inst_typing_table_lookup_inv Instance Source) as [address [View Address]].
  unfold stab_elem in Element. rewrite Address in Element.
  destruct (lookup_N (s_tables s) address) as [table|] eqn:Table;
    [|discriminate].
  destruct (store_typing_table_lookup Store Table) as [actual Typed].
  pose proof (store_typing_canonical_registry _ Store) as Valid.
  unfold instance_table_view, ext_table_typing in View. rewrite Table in View.
  unfold close_table_type, close_reference_type in View.
  destruct (close_heap_type (inst_defined_types inst) 0 (ref_heap (tt_elem_type source)))
    as [heap|] eqn:Closed; [|discriminate].
  unfold tableinst_typing in Typed.
  destruct table as [descriptor elements]; simpl in *.
  remove_bools_options.
  all: match goal with H : seq.all _ _ = true |- _ =>
    eapply all_projection in H; [|exact Element]
  end.
  all: unfold value_typing; simpl; rewrite Closed; simpl.
  all: eapply closed_value_typing_subsumption; eauto.
  all: simpl; apply/andP; split; assumption.
Qed.

Theorem inst_typing_declaration_expansion_agreement s inst C index source :
  inst_typing s inst = Some C ->
  lookup_N inst.(inst_types) index = Some source ->
  exists id declaration,
    resolve_inst_type inst index = Some id /\
    close_subtype inst.(inst_defined_types) 0 0 source = Some declaration /\
    expand_inst_type s inst index = Some declaration.
Proof.
  intros Typed Lookup.
  pose proof (inst_typing_identities Typed) as Agreement.
  apply source_type_identitiesb_correct in Agreement.
  unfold lookup_N in Lookup.
  eapply Forall2_lookup in Agreement; [|exact Lookup].
  destruct Agreement as [id [Resolved [declaration [Closed Expanded]]]].
  exists id, declaration. split; [exact Resolved |].
  split; [exact Closed |]. unfold expand_inst_type.
  change (resolve_inst_type inst index = Some id) in Resolved.
  now rewrite Resolved.
Qed.

Theorem inst_typing_null_total s inst C heap :
  inst_typing s inst = Some C ->
  source_heap_scopedb C.(tc_types) heap ->
  exists ref, lower_source_null s inst heap = Some ref.
Proof.
  intros Typed Scoped.
  destruct heap; try (eexists; reflexivity).
  unfold source_heap_scopedb in Scoped.
  rewrite (inst_typing_source_types Typed) in Scoped.
  destruct (lookup_N (inst_types inst) t) as [source|] eqn:Lookup;
    [|discriminate].
  destruct (inst_typing_declaration_expansion_agreement _ _ _ _ _ Typed Lookup)
    as [id [declaration [Resolved [_ Expanded]]]].
  unfold expand_inst_type in Expanded. rewrite Resolved in Expanded.
  change (nth_error (inst_defined_types inst) (N.to_nat t) = Some id) in Resolved.
  assert (Bound : (t < N.of_nat (length (inst_defined_types inst)))%N).
  { apply nth_error_Some_length in Resolved. lia. }
  unfold lower_source_null, close_heap_type.
  rewrite (close_type_index_prior _ _ _ _ Bound Resolved). simpl.
  unfold lower_closed_null, defined_heap_kind. rewrite Expanded.
  destruct (subtype_composite declaration); eexists; reflexivity.
Qed.

Lemma lookup_function_type_kind types index signature :
  lookup_function_type types index = Some signature <->
  exists source,
    lookup_N types index = Some source /\
    subtype_composite source = Comp_func signature.
Proof.
  unfold lookup_function_type.
  destruct (lookup_N types index) as [source|] eqn:Lookup.
  - destruct (subtype_composite source) as [f|fields|field] eqn:Composite.
    + split.
      * intro E; inversion E; subst. exists source. auto.
      * intros [other [E Same]]. inversion E; subst.
        rewrite Composite in Same. now inversion Same.
    + split; [discriminate |].
      intros [other [E Same]]. inversion E; subst. rewrite Composite in Same. discriminate.
    + split; [discriminate |].
      intros [other [E Same]]. inversion E; subst. rewrite Composite in Same. discriminate.
  - split; [discriminate | intros [source [E _]]; discriminate].
Qed.

Theorem inst_typing_function_expansion_agreement s inst C index source :
  inst_typing s inst = Some C ->
  lookup_function_type inst.(inst_types) index = Some source ->
  exists id signature,
    resolve_inst_type inst index = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Typed Lookup.
  pose proof (inst_typing_identities Typed) as Agreement.
  apply source_type_identitiesb_correct in Agreement.
  unfold lookup_function_type in Lookup.
  destruct (lookup_N inst.(inst_types) index) as [declaration|] eqn:Declaration;
    [|discriminate].
  destruct (subtype_composite declaration) as [f|fields|field] eqn:Composite;
    try discriminate.
  inversion Lookup; subst f.
  unfold lookup_N in Declaration.
  eapply Forall2_lookup in Agreement; [|exact Declaration].
  destruct Agreement as [id [Resolved Identity]].
  apply (proj2 (source_type_identityb_correct _ _ _ _)) in Identity.
  destruct (source_type_identity_function _ _ _ _ _ Composite Identity)
    as [signature [Closed Expanded]].
  exists id, signature. repeat split; assumption.
Qed.

Theorem function_reference_match_view s inst C index address source :
  store_typing s ->
  inst_typing s inst = Some C ->
  lookup_function_type C.(tc_types) index = Some source ->
  function_reference_match s inst address index = true ->
  instance_function_view s inst.(inst_defined_types) address source.
Proof.
  intros Store Instance Source.
  rewrite <-(inst_typing_type_lookup index Instance) in Source.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Instance Source)
    as [expected [[args results] [Resolved [Closed Expanded]]]].
  unfold function_reference_match. rewrite Resolved Expanded.
  destruct (lookup_func_defined_type s address) as [actual|] eqn:Actual;
    [|discriminate].
  destruct (expand_function_type (s_types s) actual) as [signature|] eqn:ActualExpanded;
    [|discriminate].
  intro Matched.
  destruct (defined_function_matches_variance _ _ _ _ _
    (store_typing_canonical_registry _ Store) Matched Expanded)
    as [aa [ar [ActualSignature [Arguments Results]]]].
  unfold instance_function_view.
  rewrite Actual Closed ActualSignature. simpl.
  by rewrite Arguments Results.
Qed.

Theorem funcinst_typing_defined_type_expansion s source inst code tf :
  funcinst_typing s (FC_func_native source inst code) tf ->
  exists C id signature,
    inst_typing s inst = Some C /\
    native_func_defined_type (FC_func_native source inst code) = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros [_ [_ Typed]].
  destruct (inst_typing s inst) as [C|] eqn:Instance; [|contradiction].
  destruct Typed as [Typed _].
  unfold func_typing in Typed. destruct code as [index locals body]. simpl in *.
  destruct (lookup_function_type C.(tc_types) index) as [[args results]|] eqn:Lookup;
    [|contradiction].
  destruct Typed as [Same _]. subst source.
  rewrite <- (inst_typing_type_lookup index Instance) in Lookup.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Instance Lookup)
    as [id [signature [Resolved [Closed Expanded]]]].
  exists C, id, signature. repeat split; assumption.
Qed.

Theorem store_typing_native_function_expansion s address source inst code :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some (FC_func_native source inst code) ->
  exists id signature,
    lookup_func_defined_type s address = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Typed Lookup.
  destruct (store_typing_func_lookup Typed Lookup) as [tf Function].
  apply funcinst_typing_defined_type_expansion in Function.
  destruct Function as [C [id [signature [_ [Resolved [Closed Expanded]]]]]].
  exists id, signature. repeat split; try assumption.
  unfold lookup_func_defined_type. now rewrite Lookup.
Qed.

Theorem store_extension_function_expansion s s' id signature :
  store_extension s s' ->
  expand_function_type s.(s_types) id = Some signature ->
  expand_function_type s'.(s_types) id = Some signature.
Proof.
  intros Extends Expanded.
  destruct (store_extension_type_groups Extends) as [suffix Registry].
  rewrite Registry.
  rewrite expand_function_type_extension; [exact Expanded |].
  unfold expand_function_type, expand_defined_type in Expanded.
  destruct (lookup_defined_type s.(s_types) id) as [st|] eqn:Lookup; [|discriminate].
  unfold lookup_defined_type in Lookup.
  destruct (nth_error s.(s_types) (N.to_nat (defined_group id))) eqn:Group;
    [now apply nth_error_index_bound in Group | discriminate].
Qed.

Theorem store_extension_declaration_expansion s s' id declaration :
  store_extension s s' ->
  expand_defined_type s.(s_types) id = Some declaration ->
  expand_defined_type s'.(s_types) id = Some declaration.
Proof.
  intros Extends Expanded.
  destruct (store_extension_type_groups Extends) as [suffix Registry].
  rewrite Registry.
  rewrite expand_defined_type_extension; [exact Expanded |].
  unfold expand_defined_type in Expanded.
  destruct (lookup_defined_type s.(s_types) id) as [st|] eqn:Lookup; [|discriminate].
  unfold lookup_defined_type in Lookup.
  destruct (nth_error s.(s_types) (N.to_nat (defined_group id))) eqn:Group;
    [now apply nth_error_index_bound in Group | discriminate].
Qed.

Theorem store_extension_native_function_identity s s' address id :
  store_extension s s' ->
  lookup_func_defined_type s address = Some id ->
  lookup_func_defined_type s' address = Some id.
Proof.
  intros Extends Resolved.
  unfold lookup_func_defined_type in *.
  destruct (lookup_N s.(s_funcs) address) as [fi|] eqn:Lookup; [|discriminate].
  rewrite (store_extension_lookup_func Extends Lookup).
  destruct fi; simpl in *; [exact Resolved |].
  destruct (store_extension_type_groups Extends) as [suffix Registry].
  rewrite Registry. exact (canonical_function_identity_extension _ _ _ _ Resolved).
Qed.

Theorem store_extension_native_function_expansion s s' address source inst code :
  store_typing s ->
  store_extension s s' ->
  lookup_N s.(s_funcs) address = Some (FC_func_native source inst code) ->
  exists id signature,
    lookup_func_defined_type s' address = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s'.(s_types) id = Some signature.
Proof.
  intros Typed Extends Lookup.
  destruct (store_typing_native_function_expansion _ _ _ _ _ Typed Lookup)
    as [id [signature [Resolved [Closed Expanded]]]].
  exists id, signature. split.
  - now apply (store_extension_native_function_identity _ _ _ _ Extends).
  - split; [exact Closed |].
    now apply (store_extension_function_expansion _ _ _ _ Extends).
Qed.

Theorem inst_typing_equivalent_defined_types s inst1 C1 index1 source1
    inst2 C2 index2 source2 id1 id2 :
  store_typing s ->
  inst_typing s inst1 = Some C1 ->
  inst_typing s inst2 = Some C2 ->
  lookup_function_type inst1.(inst_types) index1 = Some source1 ->
  lookup_function_type inst2.(inst_types) index2 = Some source2 ->
  resolve_inst_type inst1 index1 = Some id1 ->
  resolve_inst_type inst2 index2 = Some id2 ->
  defined_type_equiv s.(s_types) id1 id2 = true ->
  exists signature,
    close_function_type inst1.(inst_defined_types) 0 source1 = Some signature /\
    close_function_type inst2.(inst_defined_types) 0 source2 = Some signature.
Proof.
  intros Store Typed1 Typed2 Lookup1 Lookup2 Resolved1 Resolved2 Equivalent.
  pose proof (store_typing_canonical_registry _ Store) as [_ [WF _]].
  apply (proj1 (defined_type_equiv_eq _ _ _ WF)) in Equivalent. subst id2.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Typed1 Lookup1)
    as [a [sig1 [Id1 [Closed1 Expanded1]]]].
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Typed2 Lookup2)
    as [b [sig2 [Id2 [Closed2 Expanded2]]]].
  rewrite Resolved1 in Id1. injection Id1 as Id1. subst a.
  rewrite Resolved2 in Id2. injection Id2 as Id2. subst b.
  rewrite Expanded1 in Expanded2. injection Expanded2 as Same. subst sig2.
  exists sig1. auto.
Qed.

Theorem store_extension_instantiated_function_agreement s s' inst C index source id :
  store_extension s s' ->
  inst_typing s inst = Some C ->
  lookup_function_type inst.(inst_types) index = Some source ->
  resolve_inst_type inst index = Some id ->
  exists signature,
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_inst_function_type s' inst index = Some signature.
Proof.
  intros Extension Typed Lookup Resolved.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Typed Lookup)
    as [actual [signature [Id [Closed Expanded]]]].
  rewrite Resolved in Id. injection Id as Same. subst actual.
  exists signature. split; [exact Closed |].
  unfold expand_inst_function_type. rewrite Resolved.
  now apply (store_extension_function_expansion _ _ _ _ Extension).
Qed.

Theorem funcinst_typing_expansion_agreement s fi source :
  funcinst_typing s fi source ->
  exists id signature,
    funcinst_defined_type s fi = Some id /\
    close_function_type (funcinst_type_names fi) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intro Typed. destruct fi as [ft inst code|ft host].
  - destruct Typed as [Same Rest]. simpl in Same. subst source.
    assert (Native : funcinst_typing s (FC_func_native ft inst code) ft)
      by (split; [reflexivity | exact Rest]).
    apply funcinst_typing_defined_type_expansion in Native.
    destruct Native as [C [id [signature [_ [Identity [Closed Expanded]]]]]].
    exists id, signature. repeat split; assumption.
  - destruct Typed as [Same [_ Valid]]. simpl in Same. subst source.
    unfold canonical_function_identityb in Valid.
    destruct (canonical_function_identity s.(s_types) ft) as [id|] eqn:Identity;
      [|discriminate].
    destruct (canonical_function_identity_expansion _ _ _ Identity)
      as [signature [Closed Expanded]].
    exists id, signature. repeat split; assumption.
Qed.

Theorem store_typing_function_expansion_agreement s address fi :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some fi ->
  exists id signature,
    lookup_func_defined_type s address = Some id /\
    close_function_type (funcinst_type_names fi) 0 (cl_type fi) = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Typed Lookup.
  destruct (store_typing_func_lookup Typed Lookup) as [ft Function].
  pose proof (proj1 Function) as Same.
  apply funcinst_typing_expansion_agreement in Function.
  destruct Function as [id [signature [Identity [Closed Expanded]]]].
  exists id, signature. rewrite Same.
  repeat split; try assumption.
  unfold lookup_func_defined_type. now rewrite Lookup.
Qed.

Theorem instance_function_view_source_transport s names address fi
    args results actual_args actual_results :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some fi ->
  cl_type fi = Tf actual_args actual_results ->
  instance_function_view s names address (Tf args results) ->
  source_results_matchb s.(s_types) names (funcinst_type_names fi) args actual_args /\
  source_results_matchb s.(s_types) (funcinst_type_names fi) names actual_results results.
Proof.
  intros Store Lookup Signature View.
  pose proof (store_typing_canonical_registry _ Store) as Valid.
  pose proof (proj1 (proj2 Valid)) as WF.
  destruct (store_typing_function_expansion_agreement _ _ _ Store Lookup)
    as [id [[aa ar] [Identity [ActualClosed Expanded]]]].
  destruct (expanded_function_valid _ _ _ _ Valid Expanded) as [ArgsValid ResultsValid].
  unfold instance_function_view in View. rewrite Identity Expanded in View.
  destruct (close_function_type names 0 (Tf args results)) as [[ea er]|] eqn:ExpectedClosed;
    [|discriminate].
  simpl in View. move/andP: View => [Arguments Results].
  rewrite Signature in ActualClosed.
  unfold close_function_type in ActualClosed, ExpectedClosed.
  destruct (those0 (List.map (close_value_type (funcinst_type_names fi) 0) actual_args))
    as [ca|] eqn:ActualArgs; [|discriminate].
  destruct (those0 (List.map (close_value_type (funcinst_type_names fi) 0) actual_results))
    as [cr|] eqn:ActualResults; [|discriminate].
  destruct (those0 (List.map (close_value_type names 0) args))
    as [ce|] eqn:ExpectedArgs; [|discriminate].
  destruct (those0 (List.map (close_value_type names 0) results))
    as [cf|] eqn:ExpectedResults; [|discriminate].
  inversion ActualClosed; subst ca cr.
  inversion ExpectedClosed; subst ce cf.
  split; eapply source_results_matchb_from_closed; eauto.
  - eapply closed_list_matches_validity; eauto.
  - eapply closed_list_matches_validity; eauto.
Qed.

Lemma close_function_type_arities names members args results closed_args closed_results :
  close_function_type names members (Tf args results) =
    Some (Closed_ft closed_args closed_results) ->
  length args = length closed_args /\ length results = length closed_results.
Proof.
  unfold close_function_type.
  destruct (those0 (map (close_value_type names members) args)) as [aa|] eqn:A;
    [|discriminate].
  destruct (those0 (map (close_value_type names members) results)) as [ar|] eqn:B;
    [|discriminate].
  intro E. inversion E; subst.
  rewrite those_those0 in A. rewrite those_those0 in B.
  apply those_length in A. apply those_length in B.
  rewrite List.length_map in A. rewrite List.length_map in B. auto.
Qed.

Theorem function_reference_not_i31 s names address nullable :
  store_typing s ->
  value_typing s names (VAL_ref (VAL_ref_func address))
    (T_ref (Ref_type nullable HT_i31)) = false.
Proof.
  intro Store.
  destruct (lookup_N s.(s_funcs) address) as [fi|] eqn:Lookup.
  - destruct (store_typing_function_expansion_agreement _ _ _ Store Lookup)
      as [id [signature [Identity [_ Expanded]]]].
    assert (Kind : defined_heap_kind s.(s_types) id = Some HT_func).
    { unfold expand_function_type in Expanded.
      unfold defined_heap_kind.
      destruct (expand_defined_type (s_types s) id) as [declaration|];
        [|discriminate].
      destruct (subtype_composite declaration); try discriminate; reflexivity. }
    unfold value_typing, closed_value_typing, typeof_closed_value, typeof_closed_ref.
    rewrite Identity. simpl.
    unfold closed_heap_matchesb. rewrite Kind. simpl.
    by rewrite andbF.
  - unfold value_typing, closed_value_typing, typeof_closed_value,
      typeof_closed_ref, lookup_func_defined_type.
    by rewrite Lookup.
Qed.

Theorem function_reference_abstract_typing s names address fi :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some fi ->
  value_typing s names (VAL_ref (VAL_ref_func address)) (T_ref T_funcref).
Proof.
  intros Store Lookup.
  destruct (store_typing_function_expansion_agreement _ _ _ Store Lookup)
    as [id [signature [Identity [_ Expanded]]]].
  assert (Kind : defined_heap_kind s.(s_types) id = Some HT_func).
  { unfold expand_function_type in Expanded.
    unfold defined_heap_kind.
    destruct (expand_defined_type (s_types s) id) as [declaration|];
      [|discriminate].
    destruct (subtype_composite declaration); try discriminate; reflexivity. }
  assert (Present : defined_type_validb s.(s_types) id = true).
  { unfold expand_function_type, expand_defined_type in Expanded.
    unfold defined_type_validb.
    destruct (lookup_defined_type (s_types s) id); [reflexivity|discriminate]. }
  unfold value_typing, closed_value_typing, typeof_closed_value, typeof_closed_ref.
  rewrite Identity. simpl. rewrite Present. simpl.
  unfold closed_heap_matchesb. by rewrite Kind.
Qed.

Theorem instance_function_view_arities s names address fi args results actual_args actual_results :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some fi ->
  cl_type fi = Tf actual_args actual_results ->
  instance_function_view s names address (Tf args results) ->
  length args = length actual_args /\ length results = length actual_results.
Proof.
  intros Store Lookup Signature View.
  destruct (store_typing_function_expansion_agreement _ _ _ Store Lookup)
    as [id [[aa ar] [Identity [Closed Expanded]]]].
  rewrite Signature in Closed.
  destruct (close_function_type_arities _ _ _ _ _ _ Closed) as [Arguments Results].
  unfold instance_function_view in View. rewrite Identity Expanded in View.
  destruct (close_function_type names 0 (Tf args results)) as [[ea er]|] eqn:Expected;
    [|discriminate].
  destruct (close_function_type_arities _ _ _ _ _ _ Expected) as [ExpectedArgs ExpectedResults].
  simpl in View. move/andP: View => [ArgMatch ResultMatch].
  apply declaration_list_matchesb_length in ArgMatch.
  apply declaration_list_matchesb_length in ResultMatch.
  split; congruence.
Qed.

Theorem store_extension_function_expansion_agreement s s' address fi :
  store_typing s ->
  store_extension s s' ->
  lookup_N s.(s_funcs) address = Some fi ->
  exists id signature,
    lookup_func_defined_type s' address = Some id /\
    close_function_type (funcinst_type_names fi) 0 (cl_type fi) = Some signature /\
    expand_function_type s'.(s_types) id = Some signature.
Proof.
  intros Typed Extension Lookup.
  destruct (store_typing_function_expansion_agreement _ _ _ Typed Lookup)
    as [id [signature [Identity [Closed Expanded]]]].
  exists id, signature. split.
  - now apply (store_extension_native_function_identity _ _ _ _ Extension).
  - split; [exact Closed |].
    now apply (store_extension_function_expansion _ _ _ _ Extension).
Qed.

End Host.
