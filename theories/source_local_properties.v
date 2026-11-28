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
