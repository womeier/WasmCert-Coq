(** Positive SOURCE boundary checks for the reduced closed-runtime handoff
    fixtures. These do not assert that valid modules should fail validation.
    The strict runtime checks in tests/table_reference_bridge.py remain red. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes operations addressing instantiation_spec
  binary_format_parser binary_format_printer.
Import ListNotations.

Definition bridge_void : source_subtype :=
  Sub_type true [] (Comp_func (Tf [] [])).

Definition bridge_provider : module :=
  Build_module [[bridge_void]]
    [Build_module_func 0%N [] []] [] []
    [Build_module_global
      (Build_global_type MUT_const (T_ref (Ref_type false (HT_type 0%N))))
      [BI_ref_func 0%N]]
    [] [] None [] [Build_module_export [Byte.x67] (MED_global 0%N)].

Example bridge_provider_source_roundtrip :
  run_parse_module (binary_of_module bridge_provider) = Some bridge_provider.
Proof. vm_compute. reflexivity. Qed.

Example bridge_provider_source_context_is_valid :
  module_source_context_validb bridge_provider = true.
Proof. vm_compute. reflexivity. Qed.

Definition bridge_initialized_table width : module :=
  Build_module [[bridge_void]] [Build_module_func 0%N [] []]
    [Build_module_table
      (Build_table_type (Build_limits 1%N None)
        (Ref_type false (HT_type 0%N)) width)
      (Some [BI_ref_func 0%N])]
    [] [] [] [] None [] [].

Example bridge_initialized_table_source_roundtrip width :
  run_parse_module (binary_of_module (bridge_initialized_table width)) =
    Some (bridge_initialized_table width).
Proof. destruct width; vm_compute; reflexivity. Qed.

Example bridge_initialized_table_source_context_is_valid width :
  module_source_context_validb (bridge_initialized_table width) = true.
Proof. destruct width; vm_compute; reflexivity. Qed.

Definition bridge_getter width : module :=
  Build_module
    [[bridge_void]; [Sub_type true [] (Comp_func (Tf [] [T_ref T_funcref]))]]
    [Build_module_func 1%N []
      [BI_const_num (Addressing.value_of_address width 0%N); BI_table_get 0%N]]
    [Build_module_table
      (Build_table_type (Build_limits 1%N None) (Ref_type true (HT_type 0%N)) width) None]
    [] [] [] [] None [] [Build_module_export [Byte.x67] (MED_func 0%N)].

Example bridge_getter_source_roundtrip width :
  run_parse_module (binary_of_module (bridge_getter width)) = Some (bridge_getter width).
Proof. destruct width; vm_compute; reflexivity. Qed.

Example bridge_getter_source_context_is_valid width :
  module_source_context_validb (bridge_getter width) = true.
Proof. destruct width; vm_compute; reflexivity. Qed.

Definition bridge_imported_initializer width reference : module :=
  Build_module [[bridge_void]] []
    [Build_module_table (Build_table_type (Build_limits 1%N None) reference width)
      (Some [BI_global_get 0%N])]
    [] [] [] [] None
    [Build_module_import [Byte.x4d] [Byte.x67]
      (MID_global (Build_global_type MUT_const (T_ref (Ref_type false (HT_type 0%N)))))]
    [].

Example bridge_imported_exact_source_roundtrip width :
  let m := bridge_imported_initializer width (Ref_type false (HT_type 0%N)) in
  run_parse_module (binary_of_module m) = Some m.
Proof. destruct width; vm_compute; reflexivity. Qed.

Example bridge_imported_widened_source_roundtrip width :
  let m := bridge_imported_initializer width T_funcref in
  run_parse_module (binary_of_module m) = Some m.
Proof. destruct width; vm_compute; reflexivity. Qed.

Example bridge_imported_exact_source_context_is_valid width :
  module_source_context_validb
    (bridge_imported_initializer width (Ref_type false (HT_type 0%N))) = true.
Proof. destruct width; vm_compute; reflexivity. Qed.

Example bridge_imported_widened_source_context_is_valid width :
  module_source_context_validb (bridge_imported_initializer width T_funcref) = true.
Proof. destruct width; vm_compute; reflexivity. Qed.
