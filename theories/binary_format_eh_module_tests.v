(** Concrete whole-module composition counterexamples and repairs.
    These are regressions, not substitutes for the general module theorem. *)
From Stdlib Require Import List NArith ZArith Strings.Byte Lia.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_reference_properties instantiation_func leb128_properties.
Import ListNotations.

Definition eh_assembly_module (body : expr) : module :=
  {| mod_types := repeat [Sub_type true [] (Comp_func (Tf [] []))] 65;
     mod_funcs := [Build_module_func 0%N [] body];
     mod_tables := []; mod_mems := []; mod_globals := [];
     mod_elems := []; mod_datas := [Build_module_data [] MD_passive];
     mod_start := None;
     mod_imports := [Build_module_import [x70] [x74] (MID_tag 0%N)];
     mod_exports := [Build_module_export [x74] (MED_tag 1%N)];
     mod_tags := [0%N] |}.

Definition eh_assembly_body :=
  [BI_try_table (BT_id 64%N)
    [Catch_tag 0%N 0%N; Catch_tag_ref 1%N 0%N;
     Catch_all 0%N; Catch_all_ref 0%N]
    [BI_data_drop 0%N]].

Example legacy_unsigned_block64_decodes_as_empty :
  run_parse_be (x02 :: binary_of_u32 64%N ++ [x0b]) =
    Some (BI_block (BT_valtype None) []).
Proof. vm_compute. reflexivity. Qed.

(** This is the exact old section assembly, solely to preserve the failure
    witness. The production printer below is the repaired binary_of_module. *)
Definition legacy_module_without_count (m : module) :=
  magic ++ version ++
  only_if_non_nil binary_of_typesec m.(mod_types) ++
  only_if_non_nil binary_of_importsec m.(mod_imports) ++
  only_if_non_nil binary_of_funcsec m.(mod_funcs) ++
  only_if_non_nil binary_of_tablesec m.(mod_tables) ++
  only_if_non_nil binary_of_memsec m.(mod_mems) ++
  only_if_non_nil binary_of_tagsec m.(mod_tags) ++
  only_if_non_nil binary_of_globalsec m.(mod_globals) ++
  only_if_non_nil binary_of_exportssec m.(mod_exports) ++
  only_if_non_none binary_of_startsec m.(mod_start) ++
  only_if_non_nil binary_of_elemsec m.(mod_elems) ++
  only_if_non_nil binary_of_codesec m.(mod_funcs) ++
  only_if_non_nil binary_of_datasec m.(mod_datas).

Example legacy_missing_count_inside_handler_is_rejected :
  run_parse_module (legacy_module_without_count (eh_assembly_module eh_assembly_body)) = None.
Proof. vm_compute. reflexivity. Qed.

Example actual_eh_section_assembly_roundtrip :
  run_parse_module (binary_of_module (eh_assembly_module eh_assembly_body)) =
    Some (eh_assembly_module eh_assembly_body).
Proof. vm_compute. reflexivity. Qed.

Example actual_eh_section_assembly_string_roundtrip :
  run_parse_module_str
    (String.string_of_list_byte (binary_of_module (eh_assembly_module eh_assembly_body))) =
    Some (eh_assembly_module eh_assembly_body).
Proof. vm_compute. reflexivity. Qed.

(** A concrete remaining failed leaf derivation, not a passing conformance
    case: the full source value grammar admits this in-scope indexed type,
    but the global/instruction path still uses the abstract-only decoder. *)
Definition indexed_global_source_module : module :=
  {| mod_types := [[Sub_type true [] (Comp_func (Tf [] []))]];
     mod_funcs := []; mod_tables := []; mod_mems := [];
     mod_globals := [Build_module_global
       (Build_global_type gc_storage_types.MUT_const
         (T_ref (Ref_type true (HT_type 0%N))))
       [BI_ref_null (HT_type 0%N)]];
     mod_elems := []; mod_datas := []; mod_start := None;
     mod_imports := []; mod_exports := []; mod_tags := [] |}.

Example indexed_global_source_type_is_in_grammar :
  source_value_encoding [x63; x00] (T_ref (Ref_type true (HT_type 0%N))).
Proof.
  apply source_value_reference; apply source_reference_nullable.
  apply source_heap_index.
  split; [change (signed_leb [x00] 0%Z); constructor; cbn; lia |].
  cbn; lia.
Qed.

Example indexed_global_source_type_decode_gap :
  run [x63; x00] (fun n => parse_value_type (n := n)) = None.
Proof. vm_compute. reflexivity. Qed.

Example indexed_global_source_module_validates :
  fst (module_type_checker indexed_global_source_module) <> None.
Proof. vm_compute. discriminate. Qed.

Example indexed_global_whole_module_roundtrip_gap :
  run_parse_module (binary_of_module indexed_global_source_module) = None.
Proof. vm_compute. reflexivity. Qed.

Example indexed_global_printed_bytes :
  binary_of_module indexed_global_source_module =
    magic ++ version ++
    [x01; x04; x01; x60; x00; x00;
     x06; x07; x01; x63; x00; x00; xd0; x00; x0b].
Proof. vm_compute. reflexivity. Qed.
