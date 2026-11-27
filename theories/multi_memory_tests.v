(** Multi-memory validation regressions. Binary codec tests live in
    binary_format_tests.v and use the parser extracted by the CLI. *)
From Stdlib Require Import ZArith List.
From Wasm Require Import type_checker.
Import ListNotations.

Definition multi_memory_context : t_context :=
  Build_t_context nil nil nil
    ({| lim_min := 0%N; lim_max := Some 1%N |} ::
     {| lim_min := 1%N; lim_max := Some 2%N |} :: nil)
    nil nil nil nil nil None nil.

Lemma size_second_memory_valid :
  b_e_type_checker multi_memory_context (BI_memory_size 1%N :: nil)
    (Tf nil (T_num T_i32 :: nil)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma grow_second_memory_valid :
  b_e_type_checker multi_memory_context (BI_memory_grow 1%N :: nil)
    (Tf (T_num T_i32 :: nil) (T_num T_i32 :: nil)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_unknown_memory_invalid :
  b_e_type_checker multi_memory_context (BI_memory_size 2%N :: nil)
    (Tf nil (T_num T_i32 :: nil)) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma grow_unknown_memory_invalid :
  b_e_type_checker multi_memory_context (BI_memory_grow 2%N :: nil)
    (Tf (T_num T_i32 :: nil) (T_num T_i32 :: nil)) = false.
Proof. vm_compute. reflexivity. Qed.
