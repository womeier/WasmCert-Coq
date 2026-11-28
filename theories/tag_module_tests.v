(** Tests for tags in the main module-instance typing relation. *)
From Stdlib Require Import List NArith.
From Wasm Require Import instantiation_func type_checker.
Import ListNotations.

Section Host.
Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.

Definition tag_test_store : store_record :=
  {| s_funcs := []; s_tables := []; s_mems := []; s_globals := [];
     s_elems := []; s_datas := []; s_tags := [[T_num T_i32]]; s_exns := [] |}.

Definition tag_test_instance (addrs : list tagaddr) : moduleinst :=
  {| inst_types := []; inst_funcs := []; inst_tables := []; inst_mems := [];
     inst_globals := []; inst_elems := []; inst_datas := []; inst_exports := [];
     inst_tags := addrs |}.

Example tag_instance_context_contains_parameters :
  inst_typing tag_test_store (tag_test_instance [0%N]) =
  Some {| tc_types := []; tc_funcs := []; tc_tables := []; tc_mems := [];
          tc_globals := []; tc_elems := []; tc_datas := []; tc_locals := [];
          tc_labels := []; tc_return := None; tc_refs := [];
          tc_tags := [[T_num T_i32]] |}.
Proof. reflexivity. Qed.

Example tag_instance_dangling_address_rejected :
  inst_typing tag_test_store (tag_test_instance [1%N]) = None.
Proof. reflexivity. Qed.

Example tag_instance_without_tags :
  inst_typing tag_test_store (tag_test_instance []) = Some empty_t_context.
Proof. reflexivity. Qed.

Example exception_payload_has_tag_parameters :
  exninst_typing tag_test_store
    {| exninst_tag := 0%N;
       exninst_fields := [VAL_num (VAL_int32 Wasm_int.Int32.one)] |}.
Proof. exists [T_num T_i32]; split; reflexivity. Qed.

Example exception_unknown_tag_rejected :
  ~ exninst_typing tag_test_store
      {| exninst_tag := 1%N; exninst_fields := [] |}.
Proof.
  intros [ps [Hlookup Hfields]]; discriminate Hlookup.
Qed.

Example exception_missing_payload_rejected :
  ~ exninst_typing tag_test_store
      {| exninst_tag := 0%N; exninst_fields := [] |}.
Proof.
  intros [ps [Hlookup Hfields]].
  inversion Hlookup; subst; discriminate Hfields.
Qed.

Definition exception_ref_context : t_context :=
  {| tc_types := []; tc_funcs := []; tc_tables := []; tc_mems := [];
     tc_globals := []; tc_elems := []; tc_datas := []; tc_locals := [];
     tc_labels := []; tc_return := None; tc_refs := [];
     tc_tags := [[T_num T_i32]] |}.

Example catch_all_ref_produces_nonnull :
  b_e_type_checker exception_ref_context
    [BI_block (BT_valtype (Some (T_ref (Ref_type false HT_exn))))
      [BI_try_table (BT_valtype (Some (T_ref (Ref_type false HT_exn)))) [Catch_all_ref 0%N]
        [BI_const_num (VAL_int32 Wasm_int.Int32.one); BI_throw 0%N]];
     BI_ref_is_null]
    (Tf [] [T_num T_i32]) = true.
Proof. vm_compute; reflexivity. Qed.

End Host.
