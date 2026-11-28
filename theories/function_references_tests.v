From Wasm Require Import datatypes operations typing function_references.
From Stdlib Require Import List NArith Bool.
Import ListNotations FunctionReferences.

Example indexed_to_nullable_func :
  ref_subtypeb (Ref false (Indexed 0%N))
               (lift_reference T_funcref) = true.
Proof. reflexivity. Qed.

Example nullable_not_non_null :
  ref_subtypeb (Ref true (Indexed 0%N))
               (Ref false (Indexed 0%N)) = false.
Proof. reflexivity. Qed.

Example distinct_indices_not_equal :
  ref_subtypeb (Ref false (Indexed 0%N))
               (Ref false (Indexed 1%N)) = false.
Proof. reflexivity. Qed.

Example ordinary_call_ref_signature :
  check_call_ref [Tf [T_num T_i32] [T_num T_i64]] None false 0%N =
    Some (Tf [T_num T_i32] [T_num T_i64]).
Proof. vm_compute. reflexivity. Qed.

Example unknown_call_ref_type_rejected :
  check_call_ref [] None false 0%N = None.
Proof. reflexivity. Qed.

Example tail_call_without_return_rejected :
  check_call_ref [Tf [] []] None true 0%N = None.
Proof. reflexivity. Qed.

Example tail_call_result_mismatch_rejected :
  check_call_ref [Tf [] [T_num T_i64]]
    (Some [T_num T_i32]) true 0%N = None.
Proof. vm_compute. reflexivity. Qed.

Example tail_call_result_match_accepted :
  check_call_ref [Tf [] [T_num T_i32]]
    (Some [T_num T_i32]) true 0%N = Some (Tf [] [T_num T_i32]).
Proof. vm_compute. reflexivity. Qed.

Example extern_not_func :
  ref_subtypeb (lift_reference T_externref)
               (lift_reference T_funcref) = false.
Proof. reflexivity. Qed.

Example uninitialized_get_rejected :
  read_local [(Ref false (Indexed 0%N), false)] 0 = None.
Proof. reflexivity. Qed.

Example non_null_parameter_is_initialized :
  initial_locals nullable
    [Ref false (Indexed 0%N)]
    [Ref false (Indexed 0%N); lift_reference T_funcref] =
  [(Ref false (Indexed 0%N), true);
   (Ref false (Indexed 0%N), false);
   (lift_reference T_funcref, true)].
Proof. reflexivity. Qed.

Example initialized_get_accepted :
  initialize_local [(Ref false (Indexed 0%N), false)] 0 =
    Some [(Ref false (Indexed 0%N), true)] /\
  read_local [(Ref false (Indexed 0%N), true)] 0 =
    Some (Ref false (Indexed 0%N)).
Proof. split; reflexivity. Qed.

Example invalid_local_set_rejected :
  initialize_local [(T_num T_i32, true)] 1 = None.
Proof. reflexivity. Qed.

Example set_preserves_other_flags :
  initialize_local [(T_num T_i32, false); (T_num T_i64, true)] 0 =
    Some [(T_num T_i32, true); (T_num T_i64, true)].
Proof. reflexivity. Qed.

Example null_branch_drops_null :
  branch_on_null (VAL_ref_null HT_func) = Branch None.
Proof. reflexivity. Qed.

Example non_null_branch_keeps_value :
  branch_on_non_null (VAL_ref_func 3%N) =
    Branch (Some (VAL_ref_func 3%N)).
Proof. reflexivity. Qed.

Example null_fallthrough_drops_null :
  branch_on_non_null (VAL_ref_null HT_func) = Continue None.
Proof. reflexivity. Qed.

Example non_null_fallthrough_keeps_value :
  branch_on_null (VAL_ref_func 3%N) =
    Continue (Some (VAL_ref_func 3%N)).
Proof. reflexivity. Qed.

Example table_initializer_repeated :
  initialized_table 2 (VAL_ref_func 3%N) =
    [VAL_ref_func 3%N; VAL_ref_func 3%N].
Proof. reflexivity. Qed.

Example non_null_has_no_default :
  default_reference (Ref false (Indexed 0%N)) = None.
Proof. reflexivity. Qed.

Example nullable_indexed_default :
  default_reference (Ref true (Indexed 0%N)) =
    Some (VAL_ref_null HT_func).
Proof. reflexivity. Qed.

Example core_non_null_local_has_no_default :
  default_val (T_ref (Ref_type false HT_func)) = None.
Proof. reflexivity. Qed.

Example core_nullable_local_default :
  default_val (T_ref (Ref_type true HT_func)) =
    Some (VAL_ref (VAL_ref_null HT_func)).
Proof. reflexivity. Qed.

Section Runtime.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Lemma core_null_is_never_non_null s names h1 h2 :
  value_typing s names (VAL_ref (VAL_ref_null h1))
    (T_ref (Ref_type false h2)) = false.
Proof.
  unfold value_typing.
  cbn [gc_type_context.close_value_type ref_nullable ref_heap].
  destruct (gc_type_context.close_heap_type names 0 h2); simpl; [|reflexivity].
  unfold closed_value_typing, typeof_closed_value, typeof_closed_ref.
  destruct h1; simpl; rewrite ?Bool.andb_false_r; reflexivity.
Qed.

Lemma core_null_principal_heap s h :
  typeof_ref s (VAL_ref_null h) = Some (Ref_type true h).
Proof. reflexivity. Qed.

End Runtime.
