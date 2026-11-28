(* Raw source signatures are not the canonical import boundary.  In particular
   two projections with identical expanded function signatures can belong to
   different recursive groups, with no declared subtype path between them. *)
From Wasm Require Import instantiation_func typing instantiation_properties
  gc_declaration_typing gc_type_context.
From Stdlib Require Import List NArith String.
Import ListNotations.
Open Scope N_scope.

Definition boundary_producer_types : list source_subtype :=
  [Sub_type true [] (Comp_struct []);
   Sub_type true [] (Comp_func (Tf [] []))].

Definition boundary_consumer_types : list source_subtype :=
  [Sub_type true [] (Comp_array
     {| field_mutability := MUT_const; field_storage := ST_value (T_num T_i32) |});
   Sub_type true [] (Comp_func (Tf [] []))].

Definition boundary_registry : canonical_registry :=
  [[Sub_type true [] (Comp_struct []);
    Sub_type true [] (Comp_func (Closed_ft [] []))]].

Definition boundary_names := [Def_type 0 0; Def_type 0 1].

Section Host.
Context `{ho : host}.

Definition boundary_producer_instance : moduleinst :=
  Build_moduleinst boundary_producer_types [] [] [] [] [] [] [] boundary_names
    empty_t_context.

Definition boundary_function : funcinst :=
  FC_func_native (Tf [] []) boundary_producer_instance (Build_module_func 1 [] []).

Definition boundary_store : store_record :=
  Build_store_record [boundary_function] [] [] [] [] [] boundary_registry.

Definition boundary_module : module :=
  Build_module [boundary_consumer_types] [] [] [] [] [] [] None
    [Build_module_import [] [] (MID_func 1)] [].

Definition boundary_producer_context : t_context :=
  Build_t_context boundary_producer_types [] [] [] [] [] [] [] [] None [] boundary_names.

Lemma boundary_producer_instance_typed :
  inst_typing boundary_store boundary_producer_instance = Some boundary_producer_context.
Proof. vm_compute. reflexivity. Qed.

Lemma boundary_store_typed : store_typing boundary_store.
Proof.
  split; first (vm_compute; reflexivity).
  split.
  - constructor; last constructor.
    exists (Tf [] []).
    unfold funcinst_typing. simpl. split; first reflexivity.
    split; first reflexivity.
    split; last discriminate.
    unfold func_typing, boundary_producer_context. simpl.
    split; first reflexivity. split; [constructor|discriminate].
  - repeat split; constructor.
Qed.

Lemma boundary_module_validated :
  module_type_checker boundary_module =
    (Some ([ET_func (Tf [] [])], []), "ok"%string).
Proof. vm_compute. reflexivity. Qed.

Lemma boundary_legacy_raw_import_matches :
  ext_func_typing boundary_store 0 = Some (Tf [] []) /\
  import_subtyping (ET_func (Tf [] [])) (ET_func (Tf [] [])) = true.
Proof. vm_compute. auto. Qed.

Lemma boundary_actual_import_registered :
  external_typing boundary_store (EV_func 0) (CET_func (Def_type 0 1)).
Proof. vm_compute. reflexivity. Qed.

Lemma boundary_consumer_closing :
  close_and_validate_type_groups boundary_registry [boundary_consumer_types] =
    Some (boundary_registry ++
      [[Sub_type true [] (Comp_array
          {| field_mutability := MUT_const; field_storage := ST_value (CV_num T_i32) |});
        Sub_type true [] (Comp_func (Closed_ft [] []))]],
      [Def_type 1 0; Def_type 1 1]).
Proof. vm_compute. reflexivity. Qed.

Lemma boundary_executable_rejects hs :
  interp_instantiate hs boundary_store boundary_module [EV_func 0] =
    (None, "Import type checking failure"%string).
Proof. vm_compute. reflexivity. Qed.

Theorem boundary_no_success hs :
  ~ exists s' f es,
    interp_instantiate hs boundary_store boundary_module [EV_func 0] =
      (Some (hs, s', f, es), EmptyString).
Proof.
  intros [s' [f [es Success]]].
  rewrite boundary_executable_rejects in Success. discriminate.
Qed.

(* These are the FUNCTION branch of the historical external-typing premise
   and the historical source import-subtyping premise, not additional
   assumptions about the canonical boundary. They both hold in this example,
   whereas the conclusion of source-signature-only completeness does not. *)
Theorem boundary_legacy_completeness_counterexample hs :
  store_typing boundary_store /\
  module_type_checker boundary_module =
    (Some ([ET_func (Tf [] [])], []), "ok"%string) /\
  List.Forall2
    (fun value source =>
      match value with
      | EV_func address =>
          option_map ET_func (ext_func_typing boundary_store address) = Some source
      | _ => False
      end)
    [EV_func 0] [ET_func (Tf [] [])] /\
  List.Forall2 (fun actual expected => import_subtyping actual expected = true)
    [ET_func (Tf [] [])] [ET_func (Tf [] [])] /\
  ~ exists s' f es,
    interp_instantiate hs boundary_store boundary_module [EV_func 0] =
      (Some (hs, s', f, es), EmptyString).
Proof.
  split; first exact boundary_store_typed.
  split; first exact boundary_module_validated.
  split.
  - constructor; [reflexivity|constructor].
  - split.
    + constructor; [reflexivity|constructor].
    + exact (boundary_no_success hs).
Qed.

End Host.
