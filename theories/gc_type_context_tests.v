From Wasm Require Import datatypes gc_type_context gc_type_context_properties.
From Stdlib Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

Definition self_struct_source : recursive_type :=
  [Sub_type true [] (Comp_struct
    [{| field_mutability := MUT_const;
        field_storage := ST_value (T_ref (Ref_type true (HT_type 0))) |}])].

Definition self_struct_closed : canonical_group :=
  [Sub_type true [] (Comp_struct
    [{| field_mutability := MUT_const;
        field_storage := ST_value (CV_ref true (CH_defined (CT_rec 0))) |}])].

Example close_self_recursive_structure :
  close_type_groups [] [self_struct_source] =
    Some ([self_struct_closed], [Def_type 0 0]).
Proof. vm_compute. reflexivity. Qed.

Example repeated_self_recursive_structure_reuses_identity :
  close_type_groups [self_struct_closed] [self_struct_source] =
    Some ([self_struct_closed], [Def_type 0 0]).
Proof. vm_compute. reflexivity. Qed.

Example expand_self_recursive_structure :
  expand_struct_type [self_struct_closed] (Def_type 0 0) =
    Some [{| field_mutability := MUT_const;
      field_storage := ST_value
        (CV_ref true (CH_defined (CT_def (Def_type 0 0)))) |}].
Proof. vm_compute. reflexivity. Qed.

Example reject_forward_reference_outside_group :
  close_type_groups []
    [[Sub_type true [] (Comp_func (Tf [] [T_ref (Ref_type true (HT_type 1))]))]]
    = None.
Proof. vm_compute. reflexivity. Qed.

Example reject_self_declared_supertype :
  close_type_groups []
    [[Sub_type false [0%N] (Comp_func (Tf [] []))]] = None.
Proof. vm_compute. reflexivity. Qed.

Example reject_bottom_in_declaration :
  close_type_groups [] [[Sub_type true [] (Comp_func (Tf [] [T_bot]))]] = None.
Proof. vm_compute. reflexivity. Qed.

Definition declared_parent_source : recursive_type :=
  [Sub_type false [] (Comp_func (Tf [] []))].
Definition declared_child_source : recursive_type :=
  [Sub_type true [0%N] (Comp_func (Tf [] []))].
Definition declared_registry : canonical_registry :=
  [[Sub_type false [] (Comp_func (Closed_ft [] []))];
   [Sub_type true [CT_def (Def_type 0 0)] (Comp_func (Closed_ft [] []))]].

Example close_declared_parent_child :
  close_type_groups [] [declared_parent_source; declared_child_source] =
    Some (declared_registry, [Def_type 0 0; Def_type 1 0]).
Proof. vm_compute. reflexivity. Qed.

Example declared_matching_direction :
  defined_type_matches declared_registry (Def_type 1 0) (Def_type 0 0) = true /\
  defined_type_matches declared_registry (Def_type 0 0) (Def_type 1 0) = false.
Proof. split; vm_compute; reflexivity. Qed.

Example declared_matching_proved_path :
  exists n, declared_type_path declared_registry n (Def_type 1 0) (Def_type 0 0).
Proof.
  apply defined_type_matches_sound.
  exact (proj1 declared_matching_direction).
Qed.

Example reject_cyclic_input_registry :
  close_type_groups
    [[Sub_type false [CT_def (Def_type 0 0)] (Comp_func (Closed_ft [] []))]]
    [] = None.
Proof. vm_compute. reflexivity. Qed.

Example reject_dangling_declared_parent_registry :
  close_type_groups
    [[Sub_type false [CT_def (Def_type 1 0)] (Comp_func (Closed_ft [] []))]]
    [] = None.
Proof. vm_compute. reflexivity. Qed.
