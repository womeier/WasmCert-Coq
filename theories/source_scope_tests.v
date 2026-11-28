From Stdlib Require Import List NArith.
From Wasm Require Import datatypes operations addressing instantiation_spec
  instantiation_func gc_declaration_typing gc_type_context.
Import ListNotations.

Definition scope_function : source_subtype := Sub_type true [] (Comp_func (Tf [] [])).
Definition scope_struct : source_subtype := Sub_type true [] (Comp_struct []).
Definition scope_context types :=
  Build_t_context types [] [] [] [] [] [] [] [] None [].
Definition scope_table index width :=
  Build_module_table
    (Build_table_type (Build_limits 0%N None) (Ref_type true (HT_type index)) width) None.

Example direct_table_scope_repro_rejected :
  module_table_type_checker empty_t_context (scope_table 1%N Addressing.AT_i32) = false.
Proof. vm_compute. reflexivity. Qed.

Example direct_table_function_reference_in_scope :
  module_table_type_checker (scope_context [scope_function])
    (scope_table 0%N Addressing.AT_i64) = true.
Proof. vm_compute. reflexivity. Qed.

Example direct_table_struct_reference_in_scope :
  module_table_type_checker (scope_context [scope_struct])
    (scope_table 0%N Addressing.AT_i32) = true.
Proof. vm_compute. reflexivity. Qed.

Definition scope_module types funcs tables :=
  Build_module types funcs tables [] [] [] [] None [] [].

Example module_table_scope_repro_rejected :
  fst (module_type_checker
    (scope_module [[scope_function]] [] [scope_table 1%N Addressing.AT_i32])) = None.
Proof. vm_compute. reflexivity. Qed.

Example canonical_in_scope_table_not_blanket_rejected :
  fst (module_type_checker
    (scope_module [[scope_function]] [] [scope_table 0%N Addressing.AT_i64])) =
    Some ([], []).
Proof. vm_compute. reflexivity. Qed.

Example canonical_alias_names_are_not_source_indices :
  close_and_validate_type_groups [] [[scope_function]; [scope_function]] =
    Some ([[Sub_type true [] (Comp_func (Closed_ft [] []))]],
      [Def_type 0%N 0%N; Def_type 0%N 0%N]).
Proof. vm_compute. reflexivity. Qed.

Example table_source_alias_is_valid :
  fst (module_type_checker
    (scope_module [[scope_function]; [scope_function]] []
      [scope_table 1%N Addressing.AT_i32])) = Some ([], []).
Proof. vm_compute. reflexivity. Qed.

Example table_initializer_occurrences_are_scoped :
  module_source_types_closingb [] []
    (scope_module [] [] [Build_module_table
      (Build_table_type (Build_limits 0%N None) T_funcref Addressing.AT_i32)
      (Some [BI_ref_null (HT_type 1%N)])]) = false.
Proof. vm_compute. reflexivity. Qed.

Definition scope_names := [Def_type 0%N 0%N].
Definition scope_registry : canonical_registry :=
  [[Sub_type true [] (Comp_func (Closed_ft [] []))]].

Example unreachable_type_occurrence_is_not_erased :
  module_source_types_closingb scope_registry scope_names
    (scope_module [[scope_function]]
      [Build_module_func 0%N [] [BI_unreachable; BI_select (Some [T_ref (Ref_type true (HT_type 1%N))])]]
      []) = false.
Proof. vm_compute. reflexivity. Qed.

Example dead_typed_call_valid_index_retained_by_scope_checker :
  module_source_types_closingb scope_registry scope_names
    (scope_module [[scope_function]]
      [Build_module_func 0%N [] [BI_unreachable; BI_call_ref 0%N]] []) = true.
Proof. vm_compute. reflexivity. Qed.

Example dead_typed_call_wrong_kind_rejected_by_scope_checker :
  module_source_types_closingb [[Sub_type true [] (Comp_struct [])]] scope_names
    (scope_module [[scope_struct]]
      [Build_module_func 0%N [] [BI_unreachable; BI_call_ref 0%N]] []) = false.
Proof. vm_compute. reflexivity. Qed.
