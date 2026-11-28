(** Syntax regressions, not claims of validation or indexed payload transport. *)
From Stdlib Require Import List Strings.Byte Strings.String NArith Lia.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_module_grammar binary_format_module_complete binary_format_module_roundtrip
  binary_format_declaration_tests binary_format_declaration_properties
  binary_format_vector_print binary_format_expression_print binary_format_print_encoding
  binary_format_global_properties binary_format_memory_print binary_format_memory_properties
  binary_format_atomic_properties binary_format_record_properties binary_format_code_properties
  binary_format_segment_properties binary_format_limits_properties
  binary_format_global_section_properties.
Import ListNotations.

Definition module_fixture_body :=
  [BI_try_table (BT_id 64%N)
    [Catch_tag 0%N 0%N; Catch_tag_ref 0%N 0%N; Catch_all 0%N; Catch_all_ref 0%N]
    [BI_ref_null (HT_type 0%N); BI_data_drop 0%N;
     BI_load_vec LVA_none {| memarg_offset := 0%N; memarg_align := 0%N |}]].

Example module_fixture_body_bounds : expression_binary_wf module_fixture_body.
Proof.
  constructor; [|constructor].
  apply IBW_try_table.
  - cbn; unfold binary_index_wf; lia.
  - repeat constructor; cbn; unfold binary_index_wf; lia.
  - unfold binary_vector_length_wf; cbn; lia.
  - constructor.
    + apply IBW_atomic; apply ABW_ref_null; cbn; lia.
    + constructor.
      * apply IBW_atomic; apply (ABW_bulk_single 9%N BI_data_drop 0%N).
        -- cbn; auto.
        -- unfold binary_index_wf; lia.
        -- unfold binary_index_wf; lia.
      * constructor; [|constructor].
        apply IBW_atomic; apply ABW_memory; apply (MBW_vector 0%N (BI_load_vec LVA_none)).
        -- left; reflexivity.
        -- split; cbn; unfold binary_index_wf; lia.
Qed.

Definition actual_eh_module_fixture : module :=
  {| mod_types := [source_declaration_group];
     mod_funcs := [{| modfunc_type := 0%N;
       modfunc_locals := [T_ref (Ref_type true (HT_type 1%N))];
       modfunc_body := module_fixture_body |}];
     mod_tables := [{| modtab_type :=
       {| tt_limits := {| lim_min := 0%N; lim_max := Some 1%N |};
          tt_elem_type := Ref_type true (HT_type 0%N) |} |}];
     mod_mems := [];
     mod_tags := [0%N];
     mod_globals := [{| modglob_type := {| tg_mut := MUT_const;
       tg_t := T_ref (Ref_type true (HT_type 0%N)) |};
       modglob_init := [BI_ref_null (HT_type 0%N)] |}];
     mod_elems := [{| modelem_type := Ref_type true (HT_type 0%N);
       modelem_init := [[BI_ref_null (HT_type 0%N)]]; modelem_mode := ME_passive |}];
     mod_datas := [{| moddata_init := []; moddata_mode := MD_passive |}];
     mod_start := None;
     mod_imports := [{| imp_module := []; imp_name := []; imp_desc := MID_tag 0%N |}];
     mod_exports := [{| modexp_name := []; modexp_desc := MED_tag 0%N |}] |}.

Example module_fixture_null_bounds :
  expression_binary_wf [BI_ref_null (HT_type 0%N)].
Proof.
  constructor; [apply IBW_atomic; apply ABW_ref_null; cbn; lia |constructor].
Qed.

Example actual_eh_module_fixture_bounds : module_binary_wf actual_eh_module_fixture.
Proof.
  constructor; cbn [actual_eh_module_fixture split_module_function].
  all: try unfold section_list_binary_wf.
  all: unfold actual_eh_module_fixture;
    cbn [mod_types mod_funcs mod_tables mod_mems mod_tags mod_globals mod_elems
      mod_datas mod_start mod_imports mod_exports split_module_function List.map].
  all: repeat first
    [solve [exact source_declaration_group_bounds]
    |solve [exact module_fixture_body_bounds]
    |solve [exact module_fixture_null_bounds]
    |match goal with |- Forall _ (_ :: _) => constructor end
    |match goal with |- Forall _ [] => constructor end
    |match goal with |- _ /\ _ => split end
    |solve [exact I |reflexivity]
    |progress unfold section_list_binary_wf, name_binary_wf, import_binary_wf,
        import_desc_binary_wf, export_binary_wf, export_desc_binary_wf,
        table_type_binary_wf, limits_binary_wf, global_binary_wf,
        element_binary_wf, data_binary_wf, raw_code_binary_wf, code_binary_wf,
        source_value_binary_wf, source_heap_binary_wf
    |progress cbn [section_list_binary_wf name_binary_wf import_binary_wf
        import_desc_binary_wf export_binary_wf export_desc_binary_wf
        table_type_binary_wf limits_binary_wf global_binary_wf
        element_binary_wf data_binary_wf raw_code_binary_wf code_binary_wf
        source_value_binary_wf source_heap_binary_wf to_ref_func
        imp_module imp_name imp_desc modexp_name modexp_desc modtab_type
        tt_limits tt_elem_type lim_min lim_max modglob_type modglob_init tg_t ref_heap
        modelem_type modelem_init modelem_mode moddata_init moddata_mode
        modfunc_locals modfunc_body modfunc_type split_module_function fst snd List.map]
    |progress unfold binary_index_wf, binary_vector_length_wf
    |match goal with |- (_ <= _)%N => vm_compute; discriminate end
    |match goal with |- (_ < _)%N => vm_compute; reflexivity end].
Qed.

Example actual_eh_module_fixture_general_roundtrip :
  run_parse_module (binary_of_module actual_eh_module_fixture) = Some actual_eh_module_fixture.
Proof. apply binary_of_module_roundtrip; exact actual_eh_module_fixture_bounds. Qed.

Example ordinary_simd_load_printer_repaired :
  binary_of_be (BI_load_vec LVA_none {| memarg_offset := 0%N; memarg_align := 0%N |}) =
    [xfd; x00; x00; x00].
Proof. reflexivity. Qed.

Example ordinary_simd_splat_printer_repaired :
  run_parse_expr (binary_of_expr [BI_splat_vec (VS_i VSI_8_16)]) =
    Some [BI_splat_vec (VS_i VSI_8_16)].
Proof. vm_compute; reflexivity. Qed.

Example ordinary_simd_shuffle_printer_repaired :
  run_parse_expr (binary_of_expr [BI_vbinop (13%N, repeat 0%N 16)]) =
    Some [BI_vbinop (13%N, repeat 0%N 16)].
Proof. vm_compute; reflexivity. Qed.

Example ordinary_simd_raw_lane_printer_repaired :
  run_parse_expr (binary_of_expr
    [BI_load_vec_lane 8%N {| memarg_offset := 0%N; memarg_align := 0%N |} 128%N]) =
    Some [BI_load_vec_lane 8%N {| memarg_offset := 0%N; memarg_align := 0%N |} 128%N].
Proof. vm_compute; reflexivity. Qed.

Example ordinary_simd_extract_replace_raw_lane_printer_repaired :
  run_parse_expr (binary_of_expr
    [BI_extract_vec (VS_i VSI_8_16) (Some SX_S) 128%N;
     BI_replace_vec (VS_i VSI_8_16) 128%N]) =
    Some [BI_extract_vec (VS_i VSI_8_16) (Some SX_S) 128%N;
          BI_replace_vec (VS_i VSI_8_16) 128%N].
Proof. vm_compute; reflexivity. Qed.

Example actual_eh_module_fixture_parses :
  run_parse_module (binary_of_module actual_eh_module_fixture) = Some actual_eh_module_fixture.
Proof. vm_compute; reflexivity. Qed.

Example actual_eh_module_fixture_grammar :
  module_binary_encoding (binary_of_module actual_eh_module_fixture) actual_eh_module_fixture.
Proof.
  apply (proj1 (run_parse_module_general_correct _ _)); exact actual_eh_module_fixture_parses.
Qed.

Example actual_eh_module_fixture_general_completeness :
  run_parse_module (binary_of_module actual_eh_module_fixture) = Some actual_eh_module_fixture.
Proof.
  apply (proj2 (run_parse_module_general_correct _ _)); exact actual_eh_module_fixture_grammar.
Qed.

Example actual_eh_module_fixture_string_iff :
  run_parse_module_str (String.string_of_list_byte (binary_of_module actual_eh_module_fixture)) =
    Some actual_eh_module_fixture.
Proof.
  apply (proj2 (run_parse_module_str_general_correct _ _)).
  rewrite String.list_byte_of_string_of_list_byte.
  exact actual_eh_module_fixture_grammar.
Qed.

Definition syntax_empty_module : module :=
  {| mod_types := []; mod_funcs := []; mod_tables := []; mod_mems := [];
     mod_tags := []; mod_globals := []; mod_elems := []; mod_datas := [];
     mod_start := None; mod_imports := []; mod_exports := [] |}.

Definition noncanonical_custom_tag_module :=
  [x00; x61; x73; x6d; x01; x00; x00; x00;
   x00; x02; x00; xaa;
   x0d; x82; x00; x80; x00;
   x06; x81; x00; x00;
   x00; x02; x00; xbb].

Example noncanonical_custom_tag_module_parses :
  run_parse_module noncanonical_custom_tag_module = Some syntax_empty_module.
Proof. vm_compute; reflexivity. Qed.

Example noncanonical_custom_tag_module_independent_grammar :
  module_binary_encoding noncanonical_custom_tag_module syntax_empty_module.
Proof.
  apply (proj1 (run_parse_module_general_correct _ _)).
  exact noncanonical_custom_tag_module_parses.
Qed.

Example noncanonical_custom_tag_module_complete :
  run_parse_module noncanonical_custom_tag_module = Some syntax_empty_module.
Proof.
  apply (proj2 (run_parse_module_general_correct _ _)).
  exact noncanonical_custom_tag_module_independent_grammar.
Qed.

Example tag_after_global_is_rejected :
  run_parse_module
    [x00; x61; x73; x6d; x01; x00; x00; x00;
     x06; x01; x00; x0d; x01; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example truncated_custom_at_eof_is_rejected :
  run_parse_module [x00; x61; x73; x6d; x01; x00; x00; x00; x00; x02; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example unmatched_function_section_is_rejected :
  run_parse_module [x00; x61; x73; x6d; x01; x00; x00; x00; x03; x02; x01; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example handler_data_drop_without_datacount_is_rejected :
  run_parse_module
    [x00; x61; x73; x6d; x01; x00; x00; x00; x03; x02; x01; x00;
     x0a; x0b; x01; x09; x00; x1f; x40; x00; xfc; x09; x00; x0b; x0b] = None.
Proof. vm_compute; reflexivity. Qed.

Example same_handler_bytes_with_datacount_parse :
  exists modul,
    run_parse_module
      [x00; x61; x73; x6d; x01; x00; x00; x00; x03; x02; x01; x00;
       x0c; x01; x00;
       x0a; x0b; x01; x09; x00; x1f; x40; x00; xfc; x09; x00; x0b; x0b] = Some modul.
Proof. vm_compute; eexists; reflexivity. Qed.
