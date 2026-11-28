(** Canonical identities in the actual module validator and instantiator.
    Production modules retain recursive groups; instance contexts retain the
    flattened source composite declarations and canonical identity map. *)
From Wasm Require Import operations instantiation_spec instantiation_func
  interp_instantiate_sound gc_type_context gc_type_context_properties
  gc_declaration_typing gc_declaration_typing_properties.
From Stdlib Require Import List NArith.
Import ListNotations.

Section Host.
Context `{ho : host}.

Theorem module_type_checker_closed m imports exports message :
  module_type_checker m = (Some (imports, exports), message) ->
  exists registry ids,
    close_and_validate_type_groups [] (module_type_groups m) = Some (registry, ids) /\
    canonical_registry_valid registry.
Proof.
  unfold module_type_checker.
  destruct (close_and_validate_type_groups [] (module_type_groups m))
    as [[registry ids]|] eqn:Closed; [|discriminate].
  destruct (source_type_identitiesb registry ids (List.concat (mod_types m)) ids);
    [|discriminate].
  intro Checked. exists registry, ids. split; [reflexivity |].
  now apply close_and_validate_type_groups_sound in Closed.
Qed.

Theorem alloc_module_closed_types s m imports globals elements s' inst :
  alloc_module s m imports globals elements (s', inst) ->
  close_and_validate_type_groups s.(s_types) (module_type_groups m) =
    Some (s'.(s_types), inst.(inst_defined_types)).
Proof.
  unfold alloc_module. simpl.
  intros [registry [ids [Closed [Identity [Names Rest]]]]].
  destruct (alloc_funcs _ _ _) as [s1 fs].
  destruct (alloc_tabs _ _) as [s2 ts].
  destruct (alloc_mems _ _) as [s3 ms].
  destruct (alloc_globs _ _ _) as [s4 gs].
  destruct (alloc_elems _ _ _) as [s5 es].
  destruct (alloc_datas _ _) as [s6 ds].
  destruct (alloc_tags _ _ _) as [s7 tags].
  destruct Rest as [End _]. subst s'. simpl. now rewrite Names.
Qed.

Theorem instantiate_canonical_types s m imports s' f expressions :
  instantiate s m imports (s', f, expressions) ->
  canonical_registry_valid s'.(s_types) /\
  defined_types_present s'.(s_types) f.(f_inst).(inst_defined_types) /\
  (exists suffix, s'.(s_types) = s.(s_types) ++ suffix).
Proof.
  unfold instantiate.
  intros [impts [actual [expts [hs [inst [globals [elements
    [Typed [Imports [Matches [Allocated [Globals [Elements [Frame Expr]]]]]]]]]]]]]].
  subst f.
  apply alloc_module_closed_types in Allocated.
  apply close_and_validate_type_groups_sound in Allocated.
  destruct Allocated as [Valid Closed]. split; [exact Valid |].
  split.
  - now apply close_type_groups_present_public in Closed.
  - now apply close_type_groups_extension_public in Closed.
Qed.

Theorem interp_instantiate_canonical_types hs s m imports hs' s' f expressions message :
  interp_instantiate hs s m imports = (Some (hs', s', f, expressions), message) ->
  canonical_registry_valid s'.(s_types) /\
  defined_types_present s'.(s_types) f.(f_inst).(inst_defined_types) /\
  (exists suffix, s'.(s_types) = s.(s_types) ++ suffix).
Proof.
  intro Executed. apply interp_instantiate_imp_instantiate in Executed.
  now apply instantiate_canonical_types in Executed.
Qed.

Theorem instantiated_type_expands s m imports s' f expressions index t :
  instantiate s m imports (s', f, expressions) ->
  resolve_inst_type f.(f_inst) index = Some t ->
  exists declaration,
    expand_inst_type s' f.(f_inst) index = Some declaration.
Proof.
  intros Instantiated Resolved.
  apply instantiate_canonical_types in Instantiated.
  destruct Instantiated as [_ [Present _]].
  unfold defined_types_present in Present. rewrite Forall_forall in Present.
  assert (Member : In t f.(f_inst).(inst_defined_types)).
  { unfold resolve_inst_type, lookup_N in Resolved. now apply nth_error_In in Resolved. }
  destruct (Present t Member) as [raw Lookup].
  unfold expand_inst_type. rewrite Resolved.
  unfold expand_defined_type. rewrite Lookup. eexists. reflexivity.
Qed.

End Host.
