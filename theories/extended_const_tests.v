(** Executable regression checks for the extended-const foundations.
    These check the definitions, not yet end-to-end module acceptance. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func extended_const.
From Stdlib Require Import ZArith.

Section Host.
Context `{ho : host}.

Definition ec_i32 (z : Z) := BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m z)).
Definition ec_i64 (z : Z) := BI_const_num (VAL_int64 (Wasm_int.int_of_Z i64m z)).
Definition ec_op t op := BI_binop t (Binop_i op).
Definition ec_global mut t es := Build_module_global (Build_global_type mut t) es.
Definition ec_store : store_record := Build_store_record nil nil nil nil nil nil.
Definition ec_chain_values gs :=
  option_map (fun '(_, _, vs) => vs) (interp_global_chain ec_store empty_frame gs).

Example ec_i32_arithmetic s f :
  interp_get_const s f [:: ec_i32 7; ec_i32 9; ec_op T_i32 BOI_add;
    ec_i32 3; ec_op T_i32 BOI_sub; ec_i32 4; ec_op T_i32 BOI_mul] =
  Some (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m 52))).
Proof. by vm_compute. Qed.

Example ec_i64_arithmetic s f :
  interp_get_const s f [:: ec_i64 7; ec_i64 9; ec_op T_i64 BOI_add;
    ec_i64 3; ec_op T_i64 BOI_sub; ec_i64 4; ec_op T_i64 BOI_mul] =
  Some (VAL_num (VAL_int64 (Wasm_int.int_of_Z i64m 52))).
Proof. by vm_compute. Qed.

Example ec_sub_operand_order s f :
  interp_get_const s f [:: ec_i32 3; ec_i32 5; ec_op T_i32 BOI_sub] =
  Some (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (-2)))).
Proof. by vm_compute. Qed.

Example ec_i32_wrap s f :
  interp_get_const s f [:: ec_i32 4294967295; ec_i32 1; ec_op T_i32 BOI_add] =
  Some (VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m 0))).
Proof. apply/eqP; by vm_compute. Qed.

Example ec_i64_wrap s f :
  interp_get_const s f [:: ec_i64 18446744073709551615; ec_i64 1; ec_op T_i64 BOI_add] =
  Some (VAL_num (VAL_int64 (Wasm_int.int_of_Z i64m 0))).
Proof. apply/eqP; by vm_compute. Qed.

Example ec_reject_mixed_width s f :
  interp_get_const s f [:: ec_i32 1; ec_i64 1; ec_op T_i32 BOI_add] = None.
Proof. by vm_compute. Qed.

Example ec_reject_underflow s f :
  interp_get_const s f [:: ec_i32 1; ec_op T_i32 BOI_add] = None.
Proof. by vm_compute. Qed.

Example ec_reject_extra_values s f :
  interp_get_const s f [:: ec_i32 1; ec_i32 2] = None.
Proof. by vm_compute. Qed.

Example ec_reject_empty s f : interp_get_const s f nil = None.
Proof. reflexivity. Qed.

Example ec_reject_division s f :
  interp_get_const s f [:: ec_i32 1; ec_i32 1; ec_op T_i32 (BOI_div SX_U)] = None.
Proof. by vm_compute. Qed.

Example ec_reject_bitwise s f :
  interp_get_const s f [:: ec_i64 1; ec_i64 1; ec_op T_i64 BOI_and] = None.
Proof. by vm_compute. Qed.

Example ec_validate_arithmetic :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_const (T_num T_i32)
          [:: ec_i32 3; ec_i32 5; ec_op T_i32 BOI_sub]].
Proof. by vm_compute. Qed.

Example ec_validate_preceding :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_const (T_num T_i32) [:: ec_i32 3];
        ec_global MUT_const (T_num T_i32)
          [:: BI_global_get 0%N; ec_i32 5; ec_op T_i32 BOI_sub]].
Proof. by vm_compute. Qed.

Example ec_reject_mutable_preceding :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_var (T_num T_i32) [:: ec_i32 3];
        ec_global MUT_const (T_num T_i32) [:: BI_global_get 0%N]] = false.
Proof. by vm_compute. Qed.

Example ec_reject_self_reference :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_const (T_num T_i32) [:: BI_global_get 0%N]] = false.
Proof. by vm_compute. Qed.

Example ec_reject_forward_reference :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_const (T_num T_i32) [:: BI_global_get 1%N];
        ec_global MUT_const (T_num T_i32) [:: ec_i32 3]] = false.
Proof. by vm_compute. Qed.

Example ec_reject_invalid_stack :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_const (T_num T_i32) [:: ec_i32 1; ec_op T_i32 BOI_add]] = false.
Proof. by vm_compute. Qed.

Example ec_reject_wrong_result_type :
  extended_globals_type_checker empty_t_context
    [:: ec_global MUT_const (T_num T_i64) [:: ec_i32 1; ec_i32 2; ec_op T_i32 BOI_add]] = false.
Proof. by vm_compute. Qed.

Example ec_execute_preceding_chain :
  ec_chain_values
    [:: ec_global MUT_const (T_num T_i32) [:: ec_i32 7];
        ec_global MUT_const (T_num T_i32)
          [:: BI_global_get 0%N; ec_i32 9; ec_op T_i32 BOI_add];
        ec_global MUT_const (T_num T_i32)
          [:: BI_global_get 1%N; BI_global_get 0%N; ec_op T_i32 BOI_mul]] =
  Some [:: VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m 7));
           VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m 16));
           VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m 112))].
Proof. by vm_compute. Qed.

Example ec_execute_self_reference_fails :
  ec_chain_values [:: ec_global MUT_const (T_num T_i32) [:: BI_global_get 0%N]] = None.
Proof. by vm_compute. Qed.

Example ec_execute_forward_reference_fails :
  ec_chain_values
    [:: ec_global MUT_const (T_num T_i32) [:: BI_global_get 1%N];
        ec_global MUT_const (T_num T_i32) [:: ec_i32 7]] = None.
Proof. by vm_compute. Qed.

End Host.
