(** Source-local well-formedness at the actual validation boundary.
    This uses the shared closing map and closed-type validity, not a second
    runtime descriptor or context-free source-index transport rule. *)
From Stdlib Require Import List NArith.
From Wasm Require Import datatypes instantiation_spec instantiation_func.

Theorem source_local_closesb_correct registry names t :
  source_local_closesb registry names t = true <->
  exists closed,
    gc_type_context.close_value_type names 0 t = Some closed /\
    gc_declaration_typing.closed_value_validb registry closed = true.
Proof.
  unfold source_local_closesb.
  destruct (gc_type_context.close_value_type names 0 t) as [closed|] eqn:Closed.
  - split.
    + intro Valid; exists closed; auto.
    + intros [other [Same Valid]]; inversion Same; subst; exact Valid.
  - split; [discriminate |intros [closed [Impossible _]]; discriminate].
Qed.

Theorem module_locals_closingb_correct registry names m :
  module_locals_closingb registry names m = true <->
  Forall (fun f => Forall (fun t => exists closed,
    gc_type_context.close_value_type names 0 t = Some closed /\
    gc_declaration_typing.closed_value_validb registry closed = true)
    f.(modfunc_locals)) m.(mod_funcs).
Proof.
  unfold module_locals_closingb.
  rewrite forallb_forall, Forall_forall.
  split; intros All f Member.
  - apply Forall_forall; intros t Local.
    apply source_local_closesb_correct.
    apply (proj1 (forallb_forall _ _) (All f Member) t Local).
  - apply forallb_forall; intros t Local.
    apply source_local_closesb_correct.
    exact (proj1 (Forall_forall _ _) (All f Member) t Local).
Qed.

Theorem module_type_checker_locals_closed m imports exports message :
  module_type_checker m = (Some (imports, exports), message) ->
  exists registry names,
    gc_declaration_typing.close_and_validate_type_groups nil (module_type_groups m) =
      Some (registry, names) /\
    gc_declaration_typing.source_type_identitiesb registry names
      (List.concat m.(mod_types)) names = true /\
    Forall (fun f => Forall (fun t => exists closed,
      gc_type_context.close_value_type names 0 t = Some closed /\
      gc_declaration_typing.closed_value_validb registry closed = true)
      f.(modfunc_locals)) m.(mod_funcs).
Proof.
  unfold module_type_checker.
  destruct (gc_declaration_typing.close_and_validate_type_groups nil (module_type_groups m))
    as [[registry names]|] eqn:Closed; [|discriminate].
  destruct (andb
    (gc_declaration_typing.source_type_identitiesb registry names
      (List.concat m.(mod_types)) names)
    (module_locals_closingb registry names m)) eqn:Source; [|discriminate].
  intro Checked; apply Bool.andb_true_iff in Source.
  destruct Source as [Identity Locals].
  exists registry, names; split; [reflexivity |].
  split; [exact Identity |].
  now apply module_locals_closingb_correct.
Qed.

Theorem module_source_types_closingb_correct registry names m :
  module_source_types_closingb registry names m = true <->
  Forall (fun t => exists closed,
    gc_type_context.close_value_type names 0 t = Some closed /\
    gc_declaration_typing.closed_value_validb registry closed = true)
    (module_source_types m).
Proof.
  unfold module_source_types_closingb.
  rewrite forallb_forall, Forall_forall.
  split; intros All t Member.
  - apply source_local_closesb_correct; exact (All t Member).
  - apply source_local_closesb_correct; exact (All t Member).
Qed.

Theorem module_type_checker_source_types_closed m imports exports message :
  module_type_checker m = (Some (imports, exports), message) ->
  exists registry names,
    gc_declaration_typing.close_and_validate_type_groups nil (module_type_groups m) =
      Some (registry, names) /\
    forall t, In t (module_source_types m) ->
    exists closed,
      gc_type_context.close_value_type names 0 t = Some closed /\
      gc_declaration_typing.closed_value_validb registry closed = true.
Proof.
  unfold module_type_checker.
  destruct (gc_declaration_typing.close_and_validate_type_groups nil (module_type_groups m))
    as [[registry names]|] eqn:Closed; [|discriminate].
  destruct (andb (gc_declaration_typing.source_type_identitiesb registry names
      (List.concat m.(mod_types)) names) (module_locals_closingb registry names m))
    eqn:Source; [|discriminate].
  intro Checked; apply check_module_source_types_success in Checked.
  destruct Checked as [Components SourceTypes].
  exists registry, names; split; [reflexivity |].
  apply module_source_types_closingb_correct in SourceTypes.
  now apply Forall_forall.
Qed.

Lemma global_type_source_occurrence m g :
  In g m.(mod_globals) -> In g.(modglob_type).(tg_t) (module_source_types m).
Proof.
  intro Member; unfold module_source_types.
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
  apply in_concat.
  exists (g.(modglob_type).(tg_t) :: expression_source_types g.(modglob_init)).
  split.
  - apply in_map_iff; exists g; split; [reflexivity |exact Member].
  - now left.
Qed.

Theorem module_type_checker_global_source_closed m imports exports message g :
  module_type_checker m = (Some (imports, exports), message) ->
  In g m.(mod_globals) ->
  exists registry names closed,
    gc_declaration_typing.close_and_validate_type_groups nil (module_type_groups m) =
      Some (registry, names) /\
    gc_type_context.close_value_type names 0 g.(modglob_type).(tg_t) = Some closed /\
    gc_declaration_typing.closed_value_validb registry closed = true.
Proof.
  intros Checked Member.
  destruct (module_type_checker_source_types_closed _ _ _ _ Checked)
    as [registry [names [Closed Types]]].
  destruct (Types _ (global_type_source_occurrence _ _ Member)) as [t [TypeClosed Valid]].
  exists registry, names, t; auto.
Qed.

(** The compatibility import boundary is deliberately fail-closed for indexed
    source caches. It is not a replacement canonical identity model. *)
Lemma empty_context_source_index_rejected nullable x :
  gc_type_context.close_value_type nil 0 (T_ref (Ref_type nullable (HT_type x))) = None.
Proof. destruct x; reflexivity. Qed.

Lemma source_index_not_portable nullable x :
  source_local_closesb nil nil (T_ref (Ref_type nullable (HT_type x))) = false.
Proof.
  unfold source_local_closesb; rewrite empty_context_source_index_rejected; reflexivity.
Qed.

Theorem import_global_subtyping_index_rejected mut nullable x expected :
  import_global_subtyping
    (Build_global_type mut (T_ref (Ref_type nullable (HT_type x)))) expected = false.
Proof.
  unfold import_global_subtyping; simpl.
  rewrite source_index_not_portable, Bool.andb_false_r; reflexivity.
Qed.

Theorem import_table_subtyping_index_rejected limits nullable x expected :
  import_table_subtyping
    (Build_table_type limits (Ref_type nullable (HT_type x))) expected = false.
Proof.
  unfold import_table_subtyping; simpl.
  rewrite source_index_not_portable, Bool.andb_false_r; reflexivity.
Qed.

Theorem import_function_subtyping_index_rejected actual expected nullable x :
  In (T_ref (Ref_type nullable (HT_type x)))
    (let 'Tf ps rs := actual in seq.cat ps rs) ->
  import_func_subtyping actual expected = false.
Proof.
  destruct actual as [ps rs]; intro Member; unfold import_func_subtyping.
  destruct (forallb (source_local_closesb nil nil) (seq.cat ps rs)) eqn:Portable.
  - pose proof (proj1 (forallb_forall _ _) Portable _ Member) as Scope.
    rewrite source_index_not_portable in Scope; discriminate.
  - now rewrite Bool.andb_false_r.
Qed.
