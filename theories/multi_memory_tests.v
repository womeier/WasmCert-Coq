(** Multi-memory validation regressions. Binary codec tests live in
    binary_format_tests.v and use the parser extracted by the CLI. *)
From Stdlib Require Import ZArith List.
From Wasm Require Import type_checker.
Import ListNotations.

Definition multi_memory_context : t_context :=
  Build_t_context nil nil nil
    (memory_type32 {| lim_min := 0%N; lim_max := Some 1%N |} ::
     memory_type32 {| lim_min := 1%N; lim_max := Some 2%N |} :: nil)
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

Lemma load_second_memory_valid :
  b_e_type_checker multi_memory_context
    [BI_load T_i32 None (Build_memarg 0%N 2%N 1%N)]
    (Tf [T_num T_i32] [T_num T_i32]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_unknown_memory_invalid :
  b_e_type_checker multi_memory_context
    [BI_store T_i32 None (Build_memarg 0%N 2%N 2%N)]
    (Tf [T_num T_i32; T_num T_i32] []) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma simd_load_second_memory_valid :
  b_e_type_checker multi_memory_context
    [BI_load_vec LVA_none (Build_memarg 0%N 4%N 1%N)]
    (Tf [T_num T_i32] [T_vec T_v128]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma simd_store_unknown_memory_invalid :
  b_e_type_checker multi_memory_context
    [BI_store_vec_lane 32%N (Build_memarg 0%N 2%N 2%N) 0%N]
    (Tf [T_num T_i32; T_vec T_v128] []) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma copy_between_memories_valid :
  b_e_type_checker multi_memory_context [BI_memory_copy 1%N 0%N]
    (Tf [T_num T_i32; T_num T_i32; T_num T_i32] []) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma copy_unknown_source_invalid :
  b_e_type_checker multi_memory_context [BI_memory_copy 1%N 2%N]
    (Tf [T_num T_i32; T_num T_i32; T_num T_i32] []) = false.
Proof. vm_compute. reflexivity. Qed.

Lemma copy_unknown_destination_invalid :
  b_e_type_checker multi_memory_context [BI_memory_copy 2%N 1%N]
    (Tf [T_num T_i32; T_num T_i32; T_num T_i32] []) = false.
Proof. vm_compute. reflexivity. Qed.
