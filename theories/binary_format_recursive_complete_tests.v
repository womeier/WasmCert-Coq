(** Exercise recursive EH and shared fd/fc dispatch with legal padded headers. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes bytes binary_format_parser
  binary_format_language_properties binary_format_dispatch_properties
  binary_format_block_properties binary_format_recursive_complete.
Import ListNotations.

Definition padded_eh_expression :=
  [x1f; x40; x01; x03; x00;
   xfc; x80; x00; xfd; x8c; x00;
   x00; x00; x00; x00; x00; x00; x00; x00;
   x00; x00; x00; x00; x00; x00; x00; x00;
   x0b; x0b].

Definition padded_eh_body :=
  [BI_try_table (BT_valtype None) [Catch_all_ref 0%N]
    [BI_cvtop T_i32 CVO_trunc_sat T_f32 (Some SX_S);
     BI_const_vec (VAL_vec128 (repeat (compcert_byte_of_byte x00) 16))]].

Example padded_recursive_eh_parses :
  run_parse_expr padded_eh_expression = Some padded_eh_body.
Proof. vm_compute; reflexivity. Qed.

Example padded_recursive_eh_grammar :
  expression_encoding wasm_atomic_encoding block_type_encoding
    padded_eh_expression padded_eh_body.
Proof. apply (proj1 (wasm_run_parse_expr_correct _ _)); exact padded_recursive_eh_parses. Qed.

Example padded_recursive_eh_completeness :
  run_parse_expr padded_eh_expression = Some padded_eh_body.
Proof. apply (proj2 (wasm_run_parse_expr_correct _ _)); exact padded_recursive_eh_grammar. Qed.

Example padded_recursive_eh_suffix :
  run_parse_prefix (fun n => parse_expr (n := n))
    (padded_eh_expression ++ [xaa; xbb]) = Some (padded_eh_body, [xaa; xbb]).
Proof.
  apply (proj2 (wasm_parse_expr_prefix_correct _ _ _)).
  exists padded_eh_expression; split; [reflexivity |exact padded_recursive_eh_grammar].
Qed.
