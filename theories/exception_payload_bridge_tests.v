(** A concrete boundary for final cross-module tag payload preservation.
    Registry portability does not transport source-indexed runtime values.
    These examples use the production registry, expansion, identity-map check,
    equivalence test and main values_typing judgment, without extra axioms. *)
From Wasm Require Import typing gc_type_context gc_declaration_typing
  gc_runtime_type_properties.
From Stdlib Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

Definition payload_registry : canonical_registry :=
  [[Sub_type true [] (Comp_func (Closed_ft [] []))];
   [Sub_type true [] (Comp_func (Closed_ft [] [CV_num T_i32]))];
   [Sub_type true [] (Comp_func
     (Closed_ft [CV_ref true (CH_defined (CT_def (Def_type 0 0)))] []))]].

Definition payload_names_a : list defined_type :=
  [Def_type 0 0; Def_type 2 0].
Definition payload_names_b : list defined_type :=
  [Def_type 1 0; Def_type 0 0; Def_type 2 0].

Definition payload_source_a : type_context :=
  [Sub_type true [] (Comp_func (Tf [] []));
   Sub_type true [] (Comp_func (Tf [T_ref (Ref_type true (HT_type 0))] []))].
Definition payload_source_b : type_context :=
  [Sub_type true [] (Comp_func (Tf [] [T_num T_i32]));
   Sub_type true [] (Comp_func (Tf [] []));
   Sub_type true [] (Comp_func (Tf [T_ref (Ref_type true (HT_type 1))] []))].

Definition payload_types_a : result_type :=
  [T_ref (Ref_type true (HT_type 0))].
Definition payload_types_b : result_type :=
  [T_ref (Ref_type true (HT_type 1))].
Definition canonical_payload_types : list closed_value_type :=
  [CV_ref true (CH_defined (CT_def (Def_type 0 0)))].

Example payload_registry_is_valid :
  canonical_registry_validb payload_registry = true.
Proof. vm_compute. reflexivity. Qed.

Example payload_both_production_identity_maps_agree :
  source_type_identitiesb payload_registry payload_names_a
    payload_source_a payload_names_a = true /\
  source_type_identitiesb payload_registry payload_names_b
    payload_source_b payload_names_b = true.
Proof. vm_compute. split; reflexivity. Qed.

Example payload_both_source_signatures_close_to_same_tag :
  close_function_type payload_names_a 0 (Tf payload_types_a []) =
    Some (Closed_ft canonical_payload_types []) /\
  close_function_type payload_names_b 0 (Tf payload_types_b []) =
    Some (Closed_ft canonical_payload_types []) /\
  expand_function_type payload_registry (Def_type 2 0) =
    Some (Closed_ft canonical_payload_types []) /\
  defined_type_equiv payload_registry (Def_type 2 0) (Def_type 2 0) = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section Host.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Definition payload_bridge_store : store_record :=
  {| s_funcs := []; s_tables := []; s_mems := []; s_globals := [];
     s_elems := []; s_datas := []; s_tags := []; s_exns := [];
     s_types := payload_registry |}.

Example payload_bridge_store_is_typed : store_typing payload_bridge_store.
Proof. split; [reflexivity |]; repeat split; constructor. Qed.

Definition source_indexed_null_payload : list value :=
  [VAL_ref (VAL_ref_null (HT_type 0))].

Example canonical_equivalence_does_not_transport_source_payload_typing :
  values_typing payload_bridge_store source_indexed_null_payload
    payload_types_a = true /\
  values_typing payload_bridge_store source_indexed_null_payload
    payload_types_b = false.
Proof. vm_compute. split; reflexivity. Qed.

(** This tempting adapter is FALSE even for a typed store and a valid
    registry with two checked source/closed identity maps. Therefore final
    tag linking cannot use it to discharge catch payload preservation. *)
Theorem source_payload_transport_counterexample :
  ~ (forall fields,
      values_typing payload_bridge_store fields payload_types_a = true ->
      values_typing payload_bridge_store fields payload_types_b = true).
Proof.
  intro Transport.
  specialize (Transport source_indexed_null_payload eq_refl).
  discriminate Transport.
Qed.

End Host.
