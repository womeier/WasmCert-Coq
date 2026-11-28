From Wasm Require Import function_reference_call_properties gc_type_context typing.
From Stdlib Require Import List NArith.
Import ListNotations.

(* Caller index 0 and producer index 1 name the SAME existing canonical type.
   This is why a source-signature equality test cannot justify reference calls. *)
Definition call_test_id := Def_type 0%N 0%N.
Definition other_test_id := Def_type 1%N 0%N.
Definition caller_test_names := [call_test_id; other_test_id].
Definition producer_test_names := [other_test_id; call_test_id].

Definition caller_test_signature :=
  Tf [T_ref (Ref_type true (HT_type 0%N))] [T_num T_i32].
Definition producer_test_signature :=
  Tf [T_ref (Ref_type true (HT_type 1%N))] [T_num T_i32].
Definition shared_test_signature :=
  Closed_ft [CV_ref true (CH_defined (CT_def call_test_id))] [CV_num T_i32].

Example reference_call_different_source_indices_same_closed_signature :
  caller_test_signature <> producer_test_signature /\
  close_function_type caller_test_names 0 caller_test_signature =
    Some shared_test_signature /\
  close_function_type producer_test_names 0 producer_test_signature =
    Some shared_test_signature.
Proof. repeat split; try reflexivity; discriminate. Qed.

Example reference_call_same_source_index_different_closed_signatures :
  close_function_type caller_test_names 0 caller_test_signature <>
  close_function_type producer_test_names 0 caller_test_signature.
Proof. vm_compute. discriminate. Qed.

Example reference_call_nullable_operand_stays_nullable :
  close_value_type caller_test_names 0 (T_ref (Ref_type true (HT_type 0%N))) =
    Some (CV_ref true (CH_defined (CT_def call_test_id))).
Proof. reflexivity. Qed.

Example reference_call_nonnull_operand_stays_nonnull :
  close_value_type caller_test_names 0 (T_ref (Ref_type false (HT_type 0%N))) =
    Some (CV_ref false (CH_defined (CT_def call_test_id))).
Proof. reflexivity. Qed.

Example reference_call_expected_function_kind_checked :
  lookup_function_type [Sub_type true [] (Comp_struct [])] 0%N = None.
Proof. reflexivity. Qed.

Example reference_call_missing_expected_identity_rejected :
  close_value_type [] 0 (T_ref (Ref_type true (HT_type 0%N))) = None.
Proof. reflexivity. Qed.
