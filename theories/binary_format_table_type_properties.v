(** Full source table descriptors, with width-bearing limits. These describe
    source indices, not canonical closed runtime identities. *)
From Stdlib Require Import List Strings.Byte NArith.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_format_declaration_properties
  binary_format_width_properties.

Definition table_type_encoding :=
  source_binary (fun reference '(width, lims) => Build_table_type lims reference width)
    declaration_reference_encoding width_limits_encoding.

Theorem parse_table_type_source_sound n :
  parser_sound (parse_table_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    table_type_encoding.
Proof.
  unfold parse_table_type, table_type_encoding; apply source_binary_sound.
  - apply parse_declaration_reference_sound.
  - apply parse_width_limits_sound.
Qed.

Theorem parse_table_type_source_complete n :
  parser_complete (parse_table_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    table_type_encoding.
Proof.
  unfold parse_table_type, table_type_encoding; apply source_binary_complete.
  - apply parse_declaration_reference_complete.
  - apply parse_width_limits_complete.
Qed.

Definition table_type_binary_wf table :=
  declaration_heap_binary_wf (ref_heap (tt_elem_type table)) /\
  width_limits_binary_wf (tt_address_type table) (tt_limits table).

Theorem binary_of_table_type_source_encoding table :
  table_type_binary_wf table ->
  table_type_encoding (binary_of_table_type table) table.
Proof.
  intros [Reference Limits].
  exists (binary_of_reference_type (tt_elem_type table)),
    (binary_of_address_limits (tt_address_type table) (tt_limits table)),
    (tt_elem_type table), (tt_address_type table, tt_limits table).
  split; [reflexivity|]; split.
  - now apply binary_of_declaration_reference_encoding.
  - split; [now apply binary_of_width_limits_encoding|destruct table; reflexivity].
Qed.
