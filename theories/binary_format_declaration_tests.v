(** Recursive-group and source-indexed field regressions. Syntax only. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_declaration_properties.
From Wasm Require Import binary_format_vector_print binary_format_global_properties.
Import ListNotations.

Definition source_declaration_group : recursive_type :=
  [Sub_type true [] (Comp_struct
    [{| field_mutability := MUT_var; field_storage := ST_packed PT_i8 |};
     {| field_mutability := MUT_const;
        field_storage := ST_value (T_ref (Ref_type true (HT_type 1%N))) |}]);
   Sub_type false [0%N] (Comp_func
     (Tf [T_ref (Ref_type false HT_exn)] [T_ref (Ref_type true (HT_type 0%N))]))].

Example source_declaration_group_bounds :
  source_recursive_binary_wf source_declaration_group.
Proof.
  unfold source_recursive_binary_wf, source_declaration_group.
  split.
  - repeat constructor.
    all: cbn [source_subtype_binary_wf source_composite_binary_wf
      source_function_binary_wf source_field_binary_wf source_storage_binary_wf].
    all: unfold binary_vector_length_wf, binary_index_wf, source_value_binary_wf,
      source_heap_binary_wf; cbn; repeat constructor; lia.
Qed.

Example source_declaration_group_roundtrip :
  run (binary_of_recursive_type source_declaration_group)
    (fun n => parse_recursive_type (n := n)) = Some source_declaration_group.
Proof. apply source_recursive_printer_roundtrip; exact source_declaration_group_bounds. Qed.

Example source_declaration_section_roundtrip :
  run (binary_of_typesec [source_declaration_group])
    (fun n => parse_typesec (n := n)) = Some [source_declaration_group].
Proof.
  apply source_type_section_printer_roundtrip.
  split; [constructor; [exact source_declaration_group_bounds |constructor] |].
  split.
  - unfold binary_vector_length_wf; cbn; lia.
  - unfold binary_vector_length_wf.
    change (N.of_nat (length (binary_of_vec binary_of_recursive_type [source_declaration_group]))
      <= 4294967295)%N.
    vm_compute; discriminate.
Qed.
