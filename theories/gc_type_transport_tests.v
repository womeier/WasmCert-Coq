(** A valid destination with a forward field reference. The module's first
    two groups intern in reverse destination order, and its function group
    receives a fresh identity. Portability must not assume ordered fields. *)
From Wasm Require Import datatypes gc_type_context gc_declaration_typing
  gc_declaration_typing_properties gc_type_transport.
From Stdlib Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

Definition transport_base : canonical_registry :=
  [[Sub_type true [] (Comp_struct
      [{| field_mutability := MUT_const;
          field_storage := ST_value
            (CV_ref true (CH_defined (CT_def (Def_type 1 0)))) |}])];
   [Sub_type true [] (Comp_struct [])]].

Definition transport_source : list recursive_type :=
  [[Sub_type true [] (Comp_struct [])];
   [Sub_type true [] (Comp_struct
      [{| field_mutability := MUT_const;
          field_storage := ST_value (T_ref (Ref_type true (HT_type 0))) |}])];
   [Sub_type true [] (Comp_func (Tf
     [T_ref (Ref_type true (HT_type 0))] [T_ref (Ref_type true (HT_type 1))]))]].

Example transport_forward_reference_base_valid :
  canonical_registry_valid transport_base.
Proof. apply canonical_registry_validb_correct. vm_compute. reflexivity. Qed.

Example transport_reuses_reverse_order_and_allocates_fresh :
  close_and_validate_type_groups transport_base transport_source =
    Some (transport_base ++
      [[Sub_type true [] (Comp_func (Closed_ft
          [CV_ref true (CH_defined (CT_def (Def_type 1 0)))]
          [CV_ref true (CH_defined (CT_def (Def_type 0 0)))]))]],
      [Def_type 1 0; Def_type 0 0; Def_type 2 0]).
Proof. vm_compute. reflexivity. Qed.

Example transport_full_source_substitution_agrees :
  exists registry ids,
    close_and_validate_type_groups transport_base transport_source = Some (registry, ids) /\
    source_type_identitiesb registry ids (List.concat transport_source) ids = true.
Proof.
  eapply validated_closing_portable.
  - exact transport_forward_reference_base_valid.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
Qed.
