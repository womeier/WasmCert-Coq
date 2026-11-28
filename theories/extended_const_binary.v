(** Binary round trips for the entire extended-const arithmetic opcode fragment.
    This theorem uses the same parser and printer as extraction; it does not
    itself establish surrounding module correctness; the general whole-module
    results are in [binary_format_module_complete] and the canonical printer
    results in [binary_format_module_roundtrip]. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func binary_format_parser binary_format_printer.
From Stdlib Require Import ZArith.

Section Host.
Context `{ho : host}.

Theorem const_binop_binary_roundtrip t op :
  const_binop t op ->
  run_parse_be (binary_of_be (BI_binop t op)) = Some (BI_binop t op).
Proof.
  destruct t, op as [op|op]; destruct op => //;
    move => _; by vm_compute.
Qed.

End Host.

Example const_binop_reject_empty : run_parse_be nil = None.
Proof. by vm_compute. Qed.

Example const_binop_reject_trailing_opcode :
  run_parse_be [:: Byte.x6a; Byte.x6b] = None.
Proof. by vm_compute. Qed.

Example const_binop_expression_roundtrip :
  let es := [:: BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m 3%Z));
                BI_const_num (VAL_int32 (Wasm_int.int_of_Z i32m 5%Z));
                BI_binop T_i32 (Binop_i BOI_sub)] in
  run_parse_expr (binary_of_expr es) = Some es.
Proof. by vm_compute. Qed.

Example const_binop_reject_missing_end :
  run_parse_expr [:: Byte.x41; Byte.x03; Byte.x41; Byte.x05; Byte.x6b] = None.
Proof. by vm_compute. Qed.

Example const_binop_reject_truncated_immediate :
  run_parse_expr [:: Byte.x41; Byte.x80] = None.
Proof. by vm_compute. Qed.
