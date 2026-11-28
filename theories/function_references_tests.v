From Wasm Require Import datatypes operations typing function_references
                         instantiation_func gc_type_context.
From Stdlib Require Import List NArith.
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

Lemma core_null_is_never_non_null s h1 h2 :
  value_typing s (VAL_ref (VAL_ref_null h1))
    (T_ref (Ref_type false h2)) = false.
Proof.
  unfold value_typing, typeof_value, typeof_ref, value_subtyping, reference_type_match.
  simpl. apply Bool.andb_false_r.
Qed.

Lemma core_null_principal_heap s h :
  typeof_ref s (VAL_ref_null h) = Some (Ref_type true h).
Proof. reflexivity. Qed.

End Runtime.

Definition closed_i32_function : defined_type :=
  Def_type 0%N 0%N.

Definition closed_i64_function : defined_type :=
  Def_type 1%N 0%N.

Definition closed_function_registry : canonical_registry :=
  [[Sub_type true [] (Comp_func (Closed_ft [] [CV_num T_i32]))];
   [Sub_type true [] (Comp_func (Closed_ft [] [CV_num T_i64]))]].

Example closed_function_expansion :
  expand_function_type closed_function_registry closed_i32_function =
    Some (Closed_ft [] [CV_num T_i32]).
Proof. reflexivity. Qed.

Example closed_function_matching :
  defined_type_matches closed_function_registry closed_i32_function closed_i32_function = true.
Proof. vm_compute. reflexivity. Qed.

Example different_closed_function_results :
  defined_type_matches closed_function_registry closed_i32_function closed_i64_function = false.
Proof. vm_compute. reflexivity. Qed.

Example closing_without_an_environment_rejects_a_free_index :
  close_function_type [] 0%N (Tf [T_ref (Ref_type true (HT_type 0%N))] []) = None.
Proof. reflexivity. Qed.

Example resolving_flat_defined_type :
  match resolve_inst_type
    (Build_moduleinst [Sub_type true [] (Comp_func (Tf [] [T_num T_i32]))]
      [] [] [] [] [] [] [] [closed_i32_function]) 0%N with
  | Some dt => expand_function_type closed_function_registry dt =
      Some (Closed_ft [] [CV_num T_i32])
  | None => False
  end.
Proof. reflexivity. Qed.

Section HostMetadata.
Context `{ho : host}.
Variable hf : host_function.

Definition metadata_store (ft : function_type) : store_record :=
  Build_store_record [FC_func_host ft hf] [] [] [] [] [] closed_function_registry.

Example closed_host_import_type :
  external_type_checker (metadata_store (Tf [] [T_num T_i32])) (EV_func 0%N) =
    Some (ET_func (Tf [] [T_num T_i32])).
Proof. vm_compute. reflexivity. Qed.

Example free_host_type_index_rejected :
  external_type_checker
    (metadata_store (Tf [T_ref (Ref_type true (HT_type 0%N))] []))
    (EV_func 0%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example closed_runtime_function_identity :
  match ext_func_defined_type (metadata_store (Tf [] [T_num T_i32])) 0%N with
  | Some dt => expand_function_type closed_function_registry dt =
      Some (Closed_ft [] [CV_num T_i32])
  | None => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example unregistered_host_signature_is_rejected :
  external_type_checker
    (Build_store_record [FC_func_host (Tf [] [T_num T_i32]) hf]
      [] [] [] [] [] [])
    (EV_func 0%N) = None.
Proof. vm_compute. reflexivity. Qed.

Example zero_table_initializer_is_still_typechecked :
  module_table_type_checker empty_t_context
    (Build_module_table
      (Build_table_type (Build_limits 0%N None) T_funcref AT_i32)
      (Some [BI_ref_null HT_extern])) = false.
Proof. reflexivity. Qed.

Example nullable_table_default_is_valid :
  module_table_type_checker empty_t_context
    (Build_module_table
      (Build_table_type (Build_limits 0%N None) T_funcref AT_i32) None) = true.
Proof. reflexivity. Qed.

Example non_nullable_table_has_no_implicit_initializer :
  module_table_type_checker empty_t_context
    (Build_module_table
      (Build_table_type (Build_limits 0%N None) (Ref_type false HT_func) AT_i32) None) = false.
Proof. reflexivity. Qed.

End HostMetadata.

Definition table_global_context (gt : global_type) : t_context :=
  Build_t_context [] [] [] [] [gt] [] [] [] [] None [].

Definition table_from_global (i : globalidx) : module_table :=
  Build_module_table
    (Build_table_type (Build_limits 2%N None) T_externref AT_i32)
    (Some [BI_global_get i]).

Example table_immutable_import_initializer :
  module_table_type_checker
    (table_global_context (Build_global_type MUT_const (T_ref T_externref)))
    (table_from_global 0%N) = true.
Proof. reflexivity. Qed.

Example table_mutable_import_initializer_rejected :
  module_table_type_checker
    (table_global_context (Build_global_type MUT_var (T_ref T_externref)))
    (table_from_global 0%N) = false.
Proof. reflexivity. Qed.

Example table_wrong_import_type_rejected :
  module_table_type_checker
    (table_global_context (Build_global_type MUT_const (T_num T_i32)))
    (table_from_global 0%N) = false.
Proof. reflexivity. Qed.

Example table_global_outside_import_context_rejected :
  module_table_type_checker
    (table_global_context (Build_global_type MUT_const (T_ref T_externref)))
    (table_from_global 1%N) = false.
Proof. reflexivity. Qed.
