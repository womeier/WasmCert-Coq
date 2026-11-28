From Wasm Require Import datatypes gc_type_context gc_type_context_tests
  gc_declaration_typing gc_declaration_typing_properties.
From Stdlib Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

Example validated_self_recursive_structure :
  close_and_validate_type_groups [] [self_struct_source] =
    Some ([self_struct_closed], [Def_type 0 0]).
Proof. vm_compute. reflexivity. Qed.

Example validated_declared_functions :
  close_and_validate_type_groups []
    [declared_parent_source; declared_child_source] =
    Some (declared_registry, [Def_type 0 0; Def_type 1 0]).
Proof. vm_compute. reflexivity. Qed.

Example final_parent_rejected :
  close_and_validate_type_groups []
    [[Sub_type true [] (Comp_func (Tf [] []))]; declared_child_source] = None.
Proof. vm_compute. reflexivity. Qed.

Definition const_closed_field h : field_type closed_value_type :=
  {| field_mutability := MUT_const;
     field_storage := ST_value (CV_ref true (CH_abstract h)) |}.

Example function_variance :
  closed_composite_matchesb []
    (Comp_func (Closed_ft [CV_ref true (CH_abstract HT_any)]
                         [CV_ref false (CH_abstract HT_i31)]))
    (Comp_func (Closed_ft [CV_ref true (CH_abstract HT_eq)]
                         [CV_ref true (CH_abstract HT_eq)])) = true.
Proof. vm_compute. reflexivity. Qed.

Example struct_width_and_covariance :
  closed_composite_matchesb []
    (Comp_struct [const_closed_field HT_i31; const_closed_field HT_any])
    (Comp_struct [const_closed_field HT_eq]) = true.
Proof. vm_compute. reflexivity. Qed.

Example struct_width_and_covariance_declarative :
  closed_composite_matches []
    (Comp_struct [const_closed_field HT_i31; const_closed_field HT_any])
    (Comp_struct [const_closed_field HT_eq]).
Proof.
  apply closed_composite_matchesb_correct.
  - intros a b [st [Lookup Member]]. unfold expand_defined_type,
      lookup_defined_type in Lookup. destruct (N.to_nat (defined_group a)); discriminate.
  - exact struct_width_and_covariance.
Qed.

Example mutable_covariance_rejected :
  closed_composite_matchesb []
    (Comp_array {| field_mutability := MUT_var;
      field_storage := ST_value (CV_ref true (CH_abstract HT_i31)) |})
    (Comp_array {| field_mutability := MUT_var;
      field_storage := ST_value (CV_ref true (CH_abstract HT_eq)) |}) = false.
Proof. vm_compute. reflexivity. Qed.

Example packed_width_mismatch_rejected :
  closed_composite_matchesb []
    (Comp_array {| field_mutability := MUT_const; field_storage := ST_packed PT_i8 |})
    (Comp_array {| field_mutability := MUT_const; field_storage := ST_packed PT_i16 |})
    = false.
Proof. vm_compute. reflexivity. Qed.

Example validated_registry_has_declarative_validity :
  canonical_registry_valid declared_registry.
Proof.
  apply canonical_registry_validb_correct. vm_compute. reflexivity.
Qed.
