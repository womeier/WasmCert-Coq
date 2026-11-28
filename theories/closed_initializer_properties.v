(* Initializer phase invariants do not assume that newly allocated global
   values have already been typed. Canonical function registration is derived
   from the allocator's checked declarations, including existing host entries. *)
From Wasm Require Import typing properties type_preservation instantiation_spec
  gc_type_context gc_type_context_properties gc_declaration_typing
  gc_declaration_typing_properties gc_runtime_type_properties
  gc_closed_runtime_properties closed_typing_properties closed_context_properties.
From Stdlib Require Import List Bool NArith Lia Arith.PeanoNat.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Initializers.
Context `{ho : host}.

Definition registered_function_references s : Prop :=
  forall address fi, lookup_N s.(s_funcs) address = Some fi ->
  closed_value_typing s (VAL_ref (VAL_ref_func address))
    (CV_ref true (CH_abstract HT_func)) = true.

Lemma checked_store_registers_function_references s :
  store_typing s -> registered_function_references s.
Proof.
  move => Store address fi Lookup.
  exact (function_reference_abstract_typing s nil address fi Store Lookup).
Qed.

Lemma registered_reference_from_expansion s address id signature :
  lookup_func_defined_type s address = Some id ->
  expand_function_type s.(s_types) id = Some signature ->
  closed_value_typing s (VAL_ref (VAL_ref_func address))
    (CV_ref true (CH_abstract HT_func)).
Proof.
  move => Identity Expanded.
  have Kind : defined_heap_kind s.(s_types) id = Some HT_func.
  { unfold expand_function_type in Expanded.
    unfold defined_heap_kind.
    destruct (expand_defined_type (s_types s) id) as [declaration|];
      last discriminate.
    destruct (subtype_composite declaration); try discriminate; reflexivity. }
  have Present : defined_type_validb s.(s_types) id = true.
  { unfold expand_function_type, expand_defined_type in Expanded.
    unfold defined_type_validb.
    destruct (lookup_defined_type (s_types s) id); [reflexivity|discriminate]. }
  unfold closed_value_typing, typeof_closed_value, typeof_closed_ref.
  rewrite Identity /= Present /=.
  by rewrite /closed_heap_matchesb Kind.
Qed.

Lemma function_reference_world s later address expected :
  s.(s_types) = later.(s_types) ->
  s.(s_funcs) = later.(s_funcs) ->
  closed_value_typing s (VAL_ref (VAL_ref_func address)) expected =
    closed_value_typing later (VAL_ref (VAL_ref_func address)) expected.
Proof.
  move => Types Functions.
  unfold closed_value_typing, typeof_closed_value, typeof_closed_ref,
    lookup_func_defined_type, funcinst_defined_type.
  by rewrite Types Functions.
Qed.

Lemma registered_references_prefix s later functions groups :
  registered_function_references s ->
  later.(s_funcs) = s.(s_funcs) ++ functions ->
  later.(s_types) = s.(s_types) ++ groups ->
  forall address fi, lookup_N s.(s_funcs) address = Some fi ->
    closed_value_typing later (VAL_ref (VAL_ref_func address))
      (CV_ref true (CH_abstract HT_func)).
Proof.
  move => Registered Functions Types address fi Lookup.
  pose extended := Build_store_record (s.(s_funcs) ++ functions)
    s.(s_tables) s.(s_mems) s.(s_globals) s.(s_elems) s.(s_datas)
    (s.(s_types) ++ groups).
  have Extension : store_extension s extended.
  { unfold store_extension, extended. simpl.
    have Same := store_extension_same s.
    unfold store_extension in Same.
    have Prefix : canonical_registry_prefixb (s_types s) (s_types s ++ groups).
    { apply canonical_registry_prefixb_correct. by exists groups. }
    have Funcs : component_extension func_extension (s_funcs s)
        (s_funcs s ++ functions).
    { unfold component_extension.
      rewrite !length_is_size size_cat leq_addr /=.
      rewrite take_size_cat; [apply all2_func_extension_same|reflexivity]. }
    rewrite Funcs Prefix /=.
    remove_bools_options.
    by rewrite H1 H2 H3 H4 H5. }
  rewrite -(function_reference_world (s := extended) (later := later) address
    (CV_ref true (CH_abstract HT_func)) ltac:(by rewrite /extended /= Types)
      ltac:(by rewrite /extended /= Functions)).
  eapply closed_value_typing_store_extension; [exact Extension|].
  exact (Registered address fi Lookup).
Qed.

Lemma allocation_projection {A B T} (project : store_record -> T)
    (allocate : store_record -> A -> store_record * B) :
  (forall s x later address, allocate s x = (later, address) ->
    project later = project s) ->
  forall xs s later addresses, alloc_Xs allocate s xs = (later, addresses) ->
    project later = project s.
Proof.
  move => Step xs.
  have Fold : forall xs s acc,
      project (fst (List.fold_left
        (fun '(s, ys) x => let '(later, address) := allocate s x in
          (later, address :: ys)) xs (s, acc))) = project s.
  { move => items. induction items as [|x items IH]; move => s acc; simpl; first reflexivity.
    destruct (allocate s x) as [later address] eqn:Allocated.
    rewrite IH. exact (Step s x later address Allocated). }
  move => s later addresses.
  unfold alloc_Xs.
  destruct (List.fold_left _ xs (s, nil)) as [result reversed] eqn:Allocated.
  move => Equal. injection Equal as <- _.
  have Result := Fold xs s nil. by rewrite Allocated in Result.
Qed.

Lemma allocated_functions s codes inst later addresses :
  alloc_funcs s codes inst = (later, addresses) ->
  later.(s_funcs) = s.(s_funcs) ++ map (fun code => gen_func_instance code inst) codes.
Proof.
  have Fold : forall codes s acc,
      s_funcs (fst (List.fold_left
        (fun '(s, ys) code => let '(later, address) := alloc_func s code inst in
          (later, address :: ys)) codes (s, acc))) =
      s_funcs s ++ map (fun code => gen_func_instance code inst) codes.
  { move => items. induction items as [|code items IH]; move => initial acc; simpl.
    - by rewrite cats0.
    - rewrite /alloc_func /= IH /add_func /= -catA. reflexivity. }
  unfold alloc_funcs, alloc_Xs.
  destruct (List.fold_left _ codes (s, nil)) as [result reversed] eqn:Allocated.
  move => Equal. injection Equal as <- _.
  have Result := Fold codes s nil. by rewrite Allocated in Result.
Qed.

Lemma source_function_registered registry inst code signature :
  source_type_identitiesb registry inst.(inst_defined_types)
    inst.(inst_types) inst.(inst_defined_types) ->
  lookup_function_type inst.(inst_types) code.(modfunc_type) = Some signature ->
  exists id closed,
    resolve_inst_type inst code.(modfunc_type) = Some id /\
    expand_function_type registry id = Some closed.
Proof.
  move => Identities Function.
  apply lookup_function_type_kind in Function as [declaration [Lookup Composite]].
  apply source_type_identitiesb_correct in Identities.
  unfold lookup_N in Lookup.
  destruct (Forall2_lookup Identities Lookup)
    as [id [Name [closed [Closed Expanded]]]].
  have Identity : source_type_identityb registry (inst_defined_types inst)
      declaration id.
  { apply source_type_identityb_correct. by exists closed. }
  destruct (source_type_identity_function _ _ _ _ _ Composite Identity)
    as [function [_ FunctionExpanded]].
  exists id, function. split; last exact FunctionExpanded.
  exact Name.
Qed.

Lemma module_source_function_lookup m source code :
  module_source_context m = Some source ->
  In code m.(mod_funcs) ->
  exists signature,
    lookup_function_type (List.concat m.(mod_types)) code.(modfunc_type) = Some signature.
Proof.
  move => Context Member.
  destruct (those (map (fun f => lookup_function_type (List.concat (mod_types m))
    (modfunc_type f)) (mod_funcs m))) as [signatures|] eqn:Functions.
  - apply List.In_nth_error in Member as [index Lookup].
    destruct (those_map_lookup Functions Lookup) as [signature [Found _]].
    by exists signature.
  - unfold module_source_context in Context. rewrite Functions in Context.
    match type of Context with
    | context [match ?imports with _ => _ end] => destruct imports
    end; discriminate.
Qed.

Theorem allocated_module_initializer_registration s m imports globals elements later inst :
  store_typing s ->
  alloc_module s m imports globals elements (later, inst) ->
  canonical_registry_valid later.(s_types) /\
  registered_function_references later.
Proof.
  move => Store Allocation.
  unfold alloc_module in Allocation.
  destruct Allocation as [registry [names [source [tables [global_types [element_types
    [Closed [Identity [Names [SourceContext [InstContext [Tables [Globals [Elements Rest]]]]]]]]]]]]]].
  destruct (alloc_funcs s (mod_funcs m) inst) as [s1 fs] eqn:Functions.
  destruct (alloc_tabs s1 tables) as [s2 ts] eqn:AllocatedTables.
  destruct (alloc_mems s2 (map modmem_type (mod_mems m))) as [s3 ms] eqn:Memories.
  destruct (alloc_globs s3 global_types globals) as [s4 gs] eqn:AllocatedGlobals.
  destruct (alloc_elems s4 element_types elements) as [s5 es] eqn:AllocatedElements.
  destruct (alloc_datas s5 (mod_datas m)) as [s6 ds] eqn:Data.
  destruct Rest as [End [Types Rest]].
  have F1 := allocated_functions Functions.
  have F2 : s_funcs s2 = s_funcs s1.
  { eapply allocation_projection; last exact AllocatedTables.
    move => initial [descriptor ref] result address Allocated.
    unfold alloc_tab, alloc_tab_ref in Allocated.
    destruct descriptor as [[minimum maximum] reference].
    injection Allocated as <- _. reflexivity. }
  have F3 : s_funcs s3 = s_funcs s2.
  { eapply allocation_projection; last exact Memories.
    move => initial [minimum maximum] result address Allocated.
    injection Allocated as <- _. reflexivity. }
  have F4 : s_funcs s4 = s_funcs s3.
  { eapply allocation_projection; last exact AllocatedGlobals.
    move => initial [descriptor value] result address Allocated.
    injection Allocated as <- _. reflexivity. }
  have F5 : s_funcs s5 = s_funcs s4.
  { eapply allocation_projection; last exact AllocatedElements.
    move => initial [descriptor refs] result address Allocated.
    injection Allocated as <- _. reflexivity. }
  have F6 : s_funcs s6 = s_funcs s5.
  { eapply allocation_projection; last exact Data.
    move => initial input result address Allocated.
    injection Allocated as <- _. reflexivity. }
  have FunctionWorld : s_funcs later =
      s_funcs s ++ map (fun code => gen_func_instance code inst) (mod_funcs m).
  { by rewrite End /= F6 F5 F4 F3 F2 F1. }
  have Registry : s_types later = registry by rewrite End.
  have Validation := close_and_validate_type_groups_sound _ _ _ _ Closed.
  destruct Validation as [Valid Closing].
  split; first by rewrite Registry.
  have Prefix := close_type_groups_extension_public _ _ _ _ Closing.
  destruct Prefix as [groups Prefix].
  have TypeWorld : s_types later = s_types s ++ groups.
  { by rewrite Registry Prefix. }
  move => address fi Lookup.
  have WholeLookup := Lookup.
  rewrite FunctionWorld in Lookup.
  unfold lookup_N in Lookup.
  destruct (Nat.lt_ge_cases (N.to_nat address) (length (s_funcs s))) as [Old|New].
  - rewrite List.nth_error_app1 in Lookup; last exact Old.
    eapply registered_references_prefix;
      [exact (checked_store_registers_function_references Store)
      |exact FunctionWorld|exact TypeWorld|exact Lookup].
  - rewrite List.nth_error_app2 in Lookup; last exact New.
    apply List.nth_error_In in Lookup.
    apply List.in_map_iff in Lookup as [code [Equal Member]]. subst fi.
    destruct (module_source_function_lookup SourceContext Member) as [signature Function].
    rewrite -Types in Function.
    have Checked : source_type_identitiesb registry (inst_defined_types inst)
        (inst_types inst) (inst_defined_types inst).
    { by rewrite Names Types. }
    destruct (source_function_registered Checked Function)
      as [id [concrete [Resolved Expanded]]].
    eapply registered_reference_from_expansion.
    + unfold lookup_func_defined_type.
      have Actual : lookup_N (s_funcs later) address =
          Some (gen_func_instance code inst).
      { exact WholeLookup. }
      rewrite Actual /gen_func_instance Function /funcinst_defined_type.
      exact Resolved.
    + rewrite Registry. exact Expanded.
Qed.

Definition append_initializer_globals {V R F O} (C : t_context_gen V R F O)
    (globals : list (global_type_gen V)) :=
  Build_t_context C.(tc_types) C.(tc_funcs) C.(tc_tables) C.(tc_mems)
    (C.(tc_globals) ++ globals) C.(tc_elems) C.(tc_datas) C.(tc_locals)
    C.(tc_labels) C.(tc_return) C.(tc_refs) C.(tc_defined_types).

Lemma close_initializer_globals source base globals closed_globals :
  close_t_context source = Some base ->
  those (List.map (close_global_type source.(tc_defined_types)) globals) =
    Some closed_globals ->
  close_t_context (const_context_add_globals source globals) =
    Some (append_initializer_globals base closed_globals).
Proof.
  move => Context Closed.
  have Old := close_context_global_vector Context.
  have Joined := those_cat Old Closed.
  unfold close_t_context in Context |- *.
  unfold const_context_add_globals, append_initializer_globals.
  cbn [tc_defined_types tc_funcs tc_tables tc_globals tc_elems tc_locals
    tc_labels tc_return tc_types tc_mems tc_datas tc_refs].
  rewrite List.map_app Joined.
  destruct (those (List.map (gc_type_context.close_function_type
    (tc_defined_types source) N0) (tc_funcs source))); try discriminate.
  destruct (those (List.map (close_table_type (tc_defined_types source))
    (tc_tables source))); try discriminate.
  destruct (those (List.map (close_global_type (tc_defined_types source))
    (tc_globals source))) eqn:Globals; try discriminate.
  injection Old as <-.
  destruct (those (List.map (close_reference_type (tc_defined_types source))
    (tc_elems source))); try discriminate.
  destruct (close_result_type _ (tc_locals source)); try discriminate.
  destruct (close_return_type _ (tc_return source)); try discriminate.
  injection Context as Equal. subst base. reflexivity.
Qed.

Lemma those_map_take {A B} (f : A -> option B) xs ys n :
  those (List.map f xs) = Some ys ->
  those (List.map f (take n xs)) = Some (take n ys).
Proof.
  rewrite -!those_those0.
  move: n ys. induction xs as [|x xs IH]; move => n ys Closed.
  - simpl in Closed. injection Closed as <-. by destruct n.
  - destruct n as [|n]; first by rewrite !take0.
    simpl in Closed |- *.
    destruct (f x) as [head|]; last discriminate.
    destruct (those0 (List.map f xs)) as [tail|] eqn:Tail; last discriminate.
    injection Closed as <-. simpl. by rewrite (IH _ _ (Logic.eq_refl _)).
Qed.

Lemma registered_references_unchanged_functions s later :
  registered_function_references s ->
  store_extension s later ->
  later.(s_funcs) = s.(s_funcs) ->
  registered_function_references later.
Proof.
  move => Registered Extension Functions address fi Lookup.
  eapply closed_value_typing_store_extension; first exact Extension.
  rewrite Functions in Lookup. exact (Registered _ _ Lookup).
Qed.

(* Source validation does not consult runtime canonical names. Rebase only
   that proof context field; checked closure still happens afterwards. *)
Definition initializer_type_names (C : t_context) names : t_context :=
  Build_t_context C.(tc_types) C.(tc_funcs) C.(tc_tables) C.(tc_mems)
    C.(tc_globals) C.(tc_elems) C.(tc_datas) C.(tc_locals)
    C.(tc_labels) C.(tc_return) C.(tc_refs) names.

Lemma initializer_source_type_names C es tf names :
  be_typing C es tf ->
  be_typing (initializer_type_names C names) es tf.
Proof.
  move => Typed.
  induction Typed; unfold initializer_type_names in *; simpl in *;
    try by econstructor; eauto.
Qed.

Lemma initializer_const_type_names C es names :
  const_exprs (initializer_type_names C names) es = const_exprs C es.
Proof.
  unfold const_exprs, const_expr, initializer_type_names.
  apply eq_all. by move => e; destruct e.
Qed.

Lemma initializer_globals_type_names C gs names :
  extended_globals_typing C gs ->
  extended_globals_typing (initializer_type_names C names) gs.
Proof.
  move: C.
  induction gs as [|g gs IH]; move => C //=.
  move => [[Constant Typed] Tail]. split.
  - split.
    + change (const_exprs (initializer_type_names C names) (modglob_init g)).
      by rewrite initializer_const_type_names.
    + by apply initializer_source_type_names.
  - exact (IH _ Tail).
Qed.

End Initializers.
