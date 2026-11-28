(** Tests for tags in the main module-instance typing relation. *)
From Stdlib Require Import List NArith.
From Wasm Require Import instantiation_func type_checker binary_format_printer
  binary_format_parser.
Import ListNotations.

Section Host.
Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.

Definition tag_test_store : store_record :=
  {| s_funcs := []; s_tables := []; s_mems := []; s_globals := [];
     s_elems := []; s_datas := []; s_tags := [[T_num T_i32]]; s_exns := [];
     s_types := []; s_tag_ids := [Def_type 0 0] |}.

Definition tag_test_instance (addrs : list tagaddr) : moduleinst :=
  {| inst_types := []; inst_funcs := []; inst_tables := []; inst_mems := [];
     inst_globals := []; inst_elems := []; inst_datas := []; inst_exports := [];
     inst_tags := addrs; inst_defined_types := [] |}.

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

(** Source validation uses the combined imported/local tag index space.
    This is not an assertion that concrete tag import matching is enabled. *)
Definition tag_import_export_module : module :=
  {| mod_types :=
       [[Sub_type true [] (Comp_func (Tf [T_num T_i32] []))];
        [Sub_type true [] (Comp_func (Tf [] []))]];
     mod_funcs := [{| modfunc_type := 1%N; modfunc_locals := [];
                      modfunc_body := [BI_throw 1%N] |}];
     mod_tables := []; mod_mems := []; mod_globals := [];
     mod_elems := []; mod_datas := []; mod_start := None;
     mod_imports := [{| imp_module := []; imp_name := [];
                       imp_desc := MID_tag 0%N |}];
     mod_exports := [{| modexp_name := []; modexp_desc := MED_tag 1%N |}];
     mod_tags := [1%N] |}.

Example tag_import_export_actual_module_roundtrip :
  run_parse_module (binary_of_module tag_import_export_module) =
    Some tag_import_export_module.
Proof. vm_compute. reflexivity. Qed.

Section SourceValidation.
Context `{ho : host}.

Example tag_import_export_source_validation :
  fst (module_type_checker tag_import_export_module) =
    Some ([ET_tag [T_num T_i32]], [ET_tag []]).
Proof. vm_compute. reflexivity. Qed.

Example tag_import_result_type_rejected :
  module_import_desc_typer
    [Sub_type true [] (Comp_func (Tf [] [T_num T_i32]))] (MID_tag 0%N) = None.
Proof. reflexivity. Qed.

Example tag_import_composite_kind_rejected :
  module_import_desc_typer
    [Sub_type true [] (Comp_struct [])] (MID_tag 0%N) = None.
Proof. reflexivity. Qed.

Example tag_import_unknown_type_rejected :
  module_import_desc_typer [] (MID_tag 0%N) = None.
Proof. reflexivity. Qed.

Example source_tag_caches_are_not_link_identities :
  module_tag_imports_matching tag_test_store tag_import_export_module [EV_tag 0%N] = false.
Proof. vm_compute. reflexivity. Qed.

Example equal_source_indices_cannot_bypass_closed_payload_boundary :
  portable_tag_parameters [T_ref (Ref_type true (HT_type 0%N))]
    [T_ref (Ref_type true (HT_type 0%N))] = false.
Proof. reflexivity. Qed.

End SourceValidation.

Example tag_import_attribute_must_be_zero attribute rest :
  attribute <> Byte.x00 ->
  run_parse_prefix (fun _ => parse_import_desc) (Byte.x04 :: attribute :: rest) = None.
Proof. destruct attribute; intro H; try reflexivity; contradiction. Qed.

Example tag_import_actual_descriptor_roundtrip :
  run_parse_prefix (fun _ => parse_import_desc)
    (binary_of_import_desc (MID_tag 128%N) ++ [Byte.x41; Byte.x00]) =
  Some (MID_tag 128%N, [Byte.x41; Byte.x00]).
Proof. vm_compute. reflexivity. Qed.

Example tag_export_actual_descriptor_roundtrip :
  run_parse_prefix (fun _ => parse_module_export_desc)
    (binary_of_export_desc (MED_tag 4294967295%N) ++ [Byte.x41; Byte.x00]) =
  Some (MED_tag 4294967295%N, [Byte.x41; Byte.x00]).
Proof. vm_compute. reflexivity. Qed.
