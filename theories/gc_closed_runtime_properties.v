(** Canonical runtime boundary: principal values, expected source closure,
    and two-sided import matching. These are the shared option-A primitives;
    migration of stored descriptors and contextual administrative typing is
    separate and must not be replaced with context-free source-index checks. *)
From Wasm Require Import typing instantiation_spec gc_types gc_type_context
  gc_type_context_properties gc_declaration_typing
  gc_declaration_typing_properties gc_runtime_type_properties gc_type_transport.
From Stdlib Require Import List Bool NArith.
From mathcomp Require Import ssrbool.
Import ListNotations.

Section Runtime.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Definition closed_runtime_value_typing s value expected : Prop :=
  exists actual,
    typeof_closed_value s value = Some actual /\
    closed_value_valid s.(s_types) actual /\
    closed_value_valid s.(s_types) expected /\
    closed_value_matches s.(s_types) actual expected.

Theorem closed_value_typing_correct s value expected :
  canonical_registry_super_wf s.(s_types) ->
  (closed_value_typing s value expected = true <->
    closed_runtime_value_typing s value expected).
Proof.
  intro WF. unfold closed_value_typing, closed_runtime_value_typing.
  destruct (typeof_closed_value s value) as [actual|] eqn:Principal.
  - rewrite !andb_true_iff, !closed_value_validb_correct,
      closed_value_matchesb_correct by exact WF.
    split.
    + intros [[Actual Expected] Matches]. exists actual. auto.
    + intros [other [E [Actual [Expected Matches]]]]. inversion E; subst. auto.
  - split; [discriminate | intros [actual [E _]]; discriminate].
Qed.

Theorem source_value_typing_correct s inst value source :
  canonical_registry_super_wf s.(s_types) ->
  (source_value_typing s inst value source = true <->
    exists expected,
      close_value_type inst.(inst_defined_types) 0 source = Some expected /\
      closed_runtime_value_typing s value expected).
Proof.
  intro WF. unfold source_value_typing.
  destruct (close_value_type inst.(inst_defined_types) 0 source) as [expected|] eqn:Closed.
  - rewrite closed_value_typing_correct by exact WF. split.
    + intro Typed. exists expected. auto.
    + intros [other [E Typed]]. now inversion E; subst.
  - split; [discriminate | intros [expected [E _]]; discriminate].
Qed.

Theorem typeof_closed_function_reference s address id :
  lookup_func_defined_type s address = Some id ->
  typeof_closed_value s (VAL_ref (VAL_ref_func address)) =
    Some (CV_ref false (CH_defined (CT_def id))).
Proof.
  intro Identity. unfold typeof_closed_value, typeof_closed_ref.
  now rewrite Identity.
Qed.

Theorem source_index_is_not_a_runtime_null s index :
  typeof_closed_ref s (VAL_ref_null (HT_type index)) = None.
Proof. reflexivity. Qed.

Theorem lower_closed_null_typed s expected value :
  lower_closed_null s.(s_types) expected = Some value ->
  closed_value_typing s (VAL_ref value) (CV_ref true expected) = true.
Proof.
  destruct expected as [heap|[member|id]].
  - destruct heap; simpl; intro E; try discriminate; inversion E; reflexivity.
  - discriminate.
  - unfold lower_closed_null.
    destruct (defined_heap_kind (s_types s) id) as [kind|] eqn:Kind; [|discriminate].
    assert (Present : defined_type_validb s.(s_types) id = true).
    { unfold defined_heap_kind, expand_defined_type in Kind.
      destruct (lookup_defined_type (s_types s) id) eqn:Lookup; [|discriminate].
      unfold defined_type_validb. now rewrite Lookup. }
    destruct kind; intro E; try discriminate; inversion E; subst value;
      unfold closed_value_typing, typeof_closed_value, typeof_closed_ref;
      simpl; rewrite Present; simpl;
      unfold closed_heap_matchesb; rewrite Kind; reflexivity.
Qed.

Theorem lower_source_null_typed s inst heap value :
  lower_source_null s inst heap = Some value ->
  source_value_typing s inst (VAL_ref value) (T_ref (Ref_type true heap)) = true.
Proof.
  unfold lower_source_null, source_value_typing.
  destruct (close_heap_type (inst_defined_types inst) 0 heap) as [expected|] eqn:Closed;
    [|discriminate].
  intro Lowered.
  cbn [close_value_type ref_nullable ref_heap]. rewrite Closed. simpl.
  now apply lower_closed_null_typed.
Qed.

Theorem typeof_closed_value_extension s s' value actual :
  store_extension s s' ->
  typeof_closed_value s value = Some actual ->
  typeof_closed_value s' value = Some actual.
Proof.
  intros Extension Principal.
  destruct value as [n|v|[heap|address|address|payload]]; try exact Principal.
  unfold typeof_closed_value, typeof_closed_ref in *.
  destruct (lookup_func_defined_type s address) as [id|] eqn:Identity; [|discriminate].
  rewrite (store_extension_native_function_identity _ _ _ _ Extension Identity).
  exact Principal.
Qed.

Theorem closed_value_typing_extension s s' value expected :
  store_extension s s' ->
  store_typing s ->
  store_typing s' ->
  closed_value_typing s value expected = true ->
  closed_value_typing s' value expected = true.
Proof.
  intros Extension Store Store' Typed.
  pose proof (store_typing_canonical_registry _ Store) as [_ [WF _]].
  pose proof (store_typing_canonical_registry _ Store') as [_ [WF' _]].
  apply (proj1 (closed_value_typing_correct _ _ _ WF)) in Typed.
  destruct Typed as [actual [Principal [Actual [Expected Matches]]]].
  destruct (properties.store_extension_type_groups Extension) as [suffix Prefix].
  assert (Embedding : registry_embedding (fun x => x) s.(s_types) s'.(s_types)).
  { apply registry_embedding_prefix. now exists suffix. }
  apply (proj2 (closed_value_typing_correct _ _ _ WF')).
  exists actual. split.
  - exact (typeof_closed_value_extension _ _ _ _ Extension Principal).
  - split.
    + pose proof (registry_embedding_value_valid _ _ _ _ Embedding Actual) as Result.
      now rewrite rename_value_type_identity in Result.
    + split.
      * pose proof (registry_embedding_value_valid _ _ _ _ Embedding Expected) as Result.
        now rewrite rename_value_type_identity in Result.
      * pose proof (registry_embedding_value_matches _ _ _ _ _ Embedding Matches) as Result.
        now rewrite !rename_value_type_identity in Result.
Qed.

Theorem close_reference_type_value names reference closed :
  close_reference_type names reference = Some closed ->
  close_value_type names 0 (T_ref reference) = Some (closed_reference_value closed).
Proof.
  unfold close_reference_type, close_value_type.
  destruct (close_heap_type names 0 (ref_heap reference)) as [heap|]; [|discriminate].
  intro E. inversion E; subst. reflexivity.
Qed.

Theorem close_table_type_metadata names source closed :
  close_table_type names source = Some closed ->
  closed.(tt_limits) = source.(tt_limits) /\
  close_reference_type names source.(tt_elem_type) = Some closed.(tt_elem_type).
Proof.
  unfold close_table_type.
  destruct (close_reference_type names (tt_elem_type source)); [|discriminate].
  intro E. inversion E; subst. auto.
Qed.

Theorem close_global_type_agreement names source closed :
  close_global_type names source = Some closed ->
  closed.(tg_mut) = source.(tg_mut) /\
  close_value_type names 0 source.(tg_t) = Some closed.(tg_t).
Proof.
  unfold close_global_type.
  destruct (close_value_type names 0 (tg_t source)); [|discriminate].
  intro E. inversion E; subst. auto.
Qed.

End Runtime.

Inductive closed_import_matches registry : closed_extern_type -> closed_extern_type -> Prop :=
| cim_func : forall actual expected a b n,
    expand_function_type registry actual = Some a ->
    expand_function_type registry expected = Some b ->
    declared_type_path registry n actual expected ->
    closed_import_matches registry (CET_func actual) (CET_func expected)
| cim_table : forall actual expected,
    closed_value_matches registry (closed_reference_value actual.(tt_elem_type))
      (closed_reference_value expected.(tt_elem_type)) ->
    closed_value_matches registry (closed_reference_value expected.(tt_elem_type))
      (closed_reference_value actual.(tt_elem_type)) ->
    limits_subtyping actual.(tt_limits) expected.(tt_limits) = true ->
    closed_import_matches registry (CET_table actual) (CET_table expected)
| cim_mem : forall actual expected,
    import_mem_subtyping actual expected = true ->
    closed_import_matches registry (CET_mem actual) (CET_mem expected)
| cim_global_const : forall actual expected,
    closed_value_matches registry actual expected ->
    closed_import_matches registry
      (CET_global (Build_global_type MUT_const actual))
      (CET_global (Build_global_type MUT_const expected))
| cim_global_var : forall actual expected,
    closed_value_matches registry actual expected ->
    closed_value_matches registry expected actual ->
    closed_import_matches registry
      (CET_global (Build_global_type MUT_var actual))
      (CET_global (Build_global_type MUT_var expected)).

Theorem closed_import_subtyping_correct registry actual expected :
  canonical_registry_super_wf registry ->
  (closed_import_subtyping registry actual expected = true <->
    closed_import_matches registry actual expected).
Proof.
  intro WF. split.
  - destruct actual as [a|a|a|[ma a]], expected as [b|b|b|[mb b]];
      simpl; try discriminate.
    + destruct (expand_function_type registry a) as [fa|] eqn:A; [|discriminate].
      destruct (expand_function_type registry b) as [fb|] eqn:B; [|discriminate].
      intro Match. apply defined_type_matches_sound in Match.
      destruct Match as [n Path]. now apply cim_func with (a := fa) (b := fb) (n := n).
    + unfold closed_reference_equivb. rewrite !andb_true_iff,
        !closed_value_matchesb_correct by exact WF.
      intros [[Forward Backward] Limits]. now constructor.
    + intro Limits. now constructor.
    + destruct ma, mb; simpl; try discriminate;
        rewrite ?andb_true_r, ?andb_true_iff,
          !closed_value_matchesb_correct by exact WF.
      * intro Match. now constructor.
      * intros [Forward Backward]. now constructor.
  - intro Match. destruct Match; simpl.
    + rewrite H, H0. now apply defined_type_matches_complete with (n := n).
    + unfold closed_reference_equivb.
      rewrite !andb_true_iff, !closed_value_matchesb_correct by exact WF. auto.
    + assumption.
    + rewrite andb_true_r. now apply closed_value_matchesb_correct.
    + rewrite andb_true_iff, !closed_value_matchesb_correct by exact WF. auto.
Qed.
