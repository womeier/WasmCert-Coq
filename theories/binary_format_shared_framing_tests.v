(** Regression witnesses for the selectively integrated codec interfaces. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes binary_format_parser binary_format_printer.
Open Scope list_scope.

Example signed_block_index_64_printer :
  binary_of_block_type (BT_id 64%N) = xc0 :: x00 :: nil.
Proof. vm_compute. reflexivity. Qed.

Example signed_block_index_64_actual_parser :
  run_parse_be (x02 :: xc0 :: x00 :: x0b :: nil) =
    Some (BI_block (BT_id 64%N) nil).
Proof. vm_compute. reflexivity. Qed.

Definition one_tail_codesec_bytes :=
  x0a :: x06 :: x01 :: x04 :: x00 :: x12 :: x00 :: x0b :: nil.

Example exact_codesec_size_and_suffix :
  run_parse_prefix (fun _ => parse_codesec)
    (one_tail_codesec_bytes ++ xaa :: nil) =
  Some (((nil, BI_return_call 0%N :: nil) :: nil), xaa :: nil).
Proof. vm_compute. reflexivity. Qed.

Example short_codesec_size_rejected :
  run_parse_prefix (fun _ => parse_codesec)
    (x0a :: x05 :: x01 :: x04 :: x00 :: x12 :: x00 :: x0b :: xaa :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Example long_codesec_size_rejected :
  run_parse_prefix (fun _ => parse_codesec)
    (x0a :: x07 :: x01 :: x04 :: x00 :: x12 :: x00 :: x0b :: xaa :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Example truncated_code_end_rejected :
  run_parse_prefix (fun _ => parse_codesec)
    (x0a :: x06 :: x01 :: x04 :: x00 :: x12 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.
