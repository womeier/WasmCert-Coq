(** Actual combined-module codec regressions. These are source byte syntax
    results, not validation or source-index-to-runtime closing claims. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_module_grammar binary_format_module_roundtrip binary_format_module_complete
  binary_format_segment_properties binary_format_limits_properties
  binary_format_expression_print binary_format_print_encoding gc_types.
Open Scope list_scope.

Definition wholemodule_empty : module :=
  {| mod_types := nil; mod_funcs := nil; mod_tables := nil; mod_mems := nil;
     mod_globals := nil; mod_elems := nil; mod_datas := nil; mod_start := None;
     mod_imports := nil; mod_exports := nil |}.

Definition wholemodule_recursive_source : module :=
  {| mod_types :=
       (Sub_type true nil
          (Comp_struct
            ({| field_mutability := MUT_const;
                field_storage := ST_value (T_ref (Ref_type true (HT_type 0%N))) |} :: nil)) ::
        Sub_type true nil
          (Comp_array {| field_mutability := MUT_var; field_storage := ST_packed PT_i16 |}) ::
        Sub_type true nil (Comp_func (Tf nil nil)) :: nil) :: nil;
     mod_funcs := nil;
     mod_tables :=
       Build_module_table (Build_table_type (Build_limits 0%N None) T_funcref)
         (Some (BI_ref_null HT_func :: nil)) :: nil;
     mod_mems := nil; mod_globals := nil; mod_elems := nil; mod_datas := nil;
     mod_start := None; mod_imports := nil; mod_exports := nil |}.

Lemma wholemodule_recursive_source_domain :
  module_binary_wf wholemodule_recursive_source.
Proof.
  constructor.
  - repeat constructor; vm_compute; intuition discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
  - split.
    + constructor; [|constructor].
      split.
      * split.
        -- repeat split; vm_compute; intuition discriminate.
        -- exists {| art_nullable := true; art_heap := AH_func |}; reflexivity.
      * apply EBW_cons.
        -- apply IBW_atomic.
           change (atomic_binary_wf (BI_ref_null (shared_heap_of_abstract AH_func))).
           apply ABW_ref_null.
        -- constructor.
    + split; vm_compute; discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
  - exact I.
  - repeat constructor; vm_compute; intuition discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
  - repeat constructor; vm_compute; intuition discriminate.
Qed.

Example wholemodule_recursive_source_canonical_bytes :
  run_parse_module (binary_of_module wholemodule_recursive_source) =
  Some wholemodule_recursive_source.
Proof. apply binary_of_module_roundtrip, wholemodule_recursive_source_domain. Qed.

Example wholemodule_recursive_source_canonical_string :
  run_parse_module_str
    (String.string_of_list_byte (binary_of_module wholemodule_recursive_source)) =
  Some wholemodule_recursive_source.
Proof. apply binary_of_module_string_roundtrip, wholemodule_recursive_source_domain. Qed.

Definition wholemodule_padded_custom :=
  magic ++ version ++ x00 :: x84 :: x00 :: x80 :: x00 :: xaa :: xbb :: nil.

Example wholemodule_padded_custom_actual :
  run_parse_module wholemodule_padded_custom = Some wholemodule_empty.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_padded_custom_independent_grammar :
  module_binary_encoding wholemodule_padded_custom wholemodule_empty.
Proof. apply (proj1 (run_parse_module_general_correct _ _)).
  exact wholemodule_padded_custom_actual. Qed.

Example wholemodule_truncated_custom_rejected :
  run_parse_module (magic ++ version ++ x00 :: x04 :: x00 :: xaa :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_wrong_section_size_rejected :
  run_parse_module (magic ++ version ++ x01 :: x02 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_out_of_order_sections_rejected :
  run_parse_module (magic ++ version ++ x05 :: x01 :: x00 :: x01 :: x01 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_function_code_count_rejected :
  run_parse_module (magic ++ version ++ x03 :: x02 :: x01 :: x00 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_data_count_rejected :
  run_parse_module (magic ++ version ++ x0c :: x01 :: x01 :: nil) = None.
Proof. vm_compute. reflexivity. Qed.

Definition wholemodule_datadrop_prefix :=
  magic ++ version ++
  x01 :: x04 :: x01 :: x60 :: x00 :: x00 ::
  x03 :: x02 :: x01 :: x00 :: nil.
Definition wholemodule_datadrop_codes :=
  x0a :: x07 :: x01 :: x05 :: x00 :: xfc :: x09 :: x00 :: x0b :: nil.

Example wholemodule_required_data_count_absence_rejected :
  run_parse_module (wholemodule_datadrop_prefix ++ wholemodule_datadrop_codes) = None.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_required_data_count_present_is_syntax_only :
  run_parse_module
    (wholemodule_datadrop_prefix ++ x0c :: x01 :: x00 :: wholemodule_datadrop_codes) =
  Some
    {| mod_types := (Sub_type true nil (Comp_func (Tf nil nil)) :: nil) :: nil;
       mod_funcs := Build_module_func 0%N nil (BI_data_drop 0%N :: nil) :: nil;
       mod_tables := nil; mod_mems := nil; mod_globals := nil; mod_elems := nil;
       mod_datas := nil; mod_start := None; mod_imports := nil; mod_exports := nil |}.
Proof. vm_compute. reflexivity. Qed.

Example wholemodule_malformed_has_no_general_grammar :
  forall modul, ~ module_binary_encoding
    (magic ++ version ++ x00 :: x04 :: x00 :: xaa :: nil) modul.
Proof. apply (proj1 (run_parse_module_general_rejected _)).
  exact wholemodule_truncated_custom_rejected. Qed.
