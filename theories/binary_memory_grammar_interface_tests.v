(** Compile-time compatibility checks against the two public contracts in
    binary_parser_combinator_properties.v at 1d15428/ddb7f82. Only those
    contracts are now imported directly from the common framework. *)
From Wasm Require Import datatypes binary_format_parser binary_format_properties
  binary_memory_properties binary_memory_grammar_properties.
From Wasm Require Import binary_parser_combinator_properties.
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.

Module PinnedContractAudit.

Example memory_primitive_sound n :
  parser_sound (parse_memory_instruction (n := n)) binary_memory_instruction.
Proof. exact (parse_memory_instruction_binary_sound n). Qed.

Example memory_primitive_complete n :
  parser_complete (parse_memory_instruction (n := n)) binary_memory_instruction.
Proof. exact (parse_memory_instruction_binary_complete n). Qed.

Example memarg_sound n :
  parser_sound (parse_memarg (n := n)) binary_memarg.
Proof. exact (parse_memarg_binary_sound n). Qed.

Example memarg_complete n :
  parser_complete (parse_memarg (n := n)) binary_memarg.
Proof. exact (parse_memarg_binary_complete n). Qed.

Example memidx_sound n :
  parser_sound (parse_memidx (n := n)) binary_u32.
Proof. exact (parse_u32_binary_sound n). Qed.

Example memidx_complete n :
  parser_complete (parse_memidx (n := n)) binary_u32.
Proof. exact (parse_u32_binary_complete n). Qed.

Example dataidx_sound n :
  parser_sound (parse_dataidx (n := n)) binary_u32.
Proof. exact (parse_u32_binary_sound n). Qed.

Example dataidx_complete n :
  parser_complete (parse_dataidx (n := n)) binary_u32.
Proof. exact (parse_u32_binary_complete n). Qed.

Example offset_sound n :
  parser_sound (parse_static_offset (n := n)) binary_u64.
Proof. exact (parse_u64_binary_sound n). Qed.

Example offset_complete n :
  parser_complete (parse_static_offset (n := n)) binary_u64.
Proof. exact (parse_u64_binary_complete n). Qed.

End PinnedContractAudit.
