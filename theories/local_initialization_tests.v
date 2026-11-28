From Wasm Require Import local_initialization local_initialization_runtime typing.
From Stdlib Require Import List NArith.
Import ListNotations.

Example nondefaultable_local_starts_uninitialized :
  initial_local_state [] [T_ref (Ref_type false HT_func)] = [false].
Proof. reflexivity. Qed.

Example parameters_start_initialized :
  initial_local_state [T_ref (Ref_type false HT_func)]
    [T_ref (Ref_type false HT_func)] = [true; false].
Proof. reflexivity. Qed.

Example sequential_set_initializes :
  check_local_init_sequence [BI_local_set 0%N; BI_local_get 0%N] [false] =
    Some [true].
Proof. reflexivity. Qed.

Example sequential_tee_initializes :
  check_local_init_sequence [BI_local_tee 0%N; BI_local_get 0%N] [false] =
    Some [true].
Proof. reflexivity. Qed.

Example read_before_set_is_rejected :
  check_local_init_sequence [BI_local_get 0%N; BI_local_set 0%N] [false] = None.
Proof. reflexivity. Qed.

Example unknown_local_is_rejected :
  check_local_init_sequence [BI_local_set 1%N] [false] = None.
Proof. reflexivity. Qed.

Example block_body_sees_writes :
  check_local_init_sequence
    [BI_block (BT_valtype None) [BI_local_set 0%N; BI_local_get 0%N]] [false] =
    Some [false].
Proof. reflexivity. Qed.

Example block_does_not_export_initialization :
  check_local_init_sequence
    [BI_block (BT_valtype None) [BI_local_set 0%N]; BI_local_get 0%N] [false] =
    None.
Proof. reflexivity. Qed.

Example loop_does_not_assume_a_previous_iteration :
  check_local_init_sequence
    [BI_loop (BT_valtype None) [BI_local_get 0%N; BI_local_set 0%N]] [false] =
    None.
Proof. reflexivity. Qed.

Example conditional_arms_start_independently :
  check_local_init_sequence
    [BI_if (BT_valtype None) [BI_local_set 0%N] [BI_local_get 0%N]] [false] =
    None.
Proof. reflexivity. Qed.

Example conditional_does_not_export_arm_writes :
  check_local_init_sequence
    [BI_if (BT_valtype None) [BI_local_set 0%N] [BI_local_set 0%N];
     BI_local_get 0%N] [false] = None.
Proof. reflexivity. Qed.

Example parent_writes_are_visible_in_both_arms :
  check_local_init_sequence
    [BI_local_set 0%N;
     BI_if (BT_valtype None) [BI_local_get 0%N] [BI_local_get 0%N]] [false] =
    Some [true].
Proof. reflexivity. Qed.

Example nondefaultable_slot_is_not_an_ordinary_null :
  map default_val [T_ref (Ref_type false HT_func)] = [None].
Proof. reflexivity. Qed.
