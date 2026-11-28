(** Padded dispatch and arbitrary suffix regressions for the actual memory AST. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes binary_format_parser
  binary_format_memory_properties binary_format_memory_complete.
Import ListNotations.

Example padded_vector_memory_dispatch :
  run_parse_prefix (fun n => parse_memory_instruction (n := n))
    [xfd; xd4; x00; x60; x80; x00; x00; x80; x0b] =
  Some (BI_load_vec_lane 8%N
    {| memarg_offset := 0%N; memarg_align := 32%N |} 128%N, [x0b]).
Proof. vm_compute; reflexivity. Qed.

Example padded_bulk_memory_dispatch :
  run_parse_prefix (fun n => parse_memory_instruction (n := n))
    [xfc; x8a; x00; x00; x00; x0b] = Some (BI_memory_copy, [x0b]).
Proof. vm_compute; reflexivity. Qed.

Example padded_vector_memory_grammar :
  exists prefix,
    [xfd; xd4; x00; x60; x80; x00; x00; x80; x0b] = prefix ++ [x0b] /\
    memory_instruction_encoding prefix
      (BI_load_vec_lane 8%N {| memarg_offset := 0%N; memarg_align := 32%N |} 128%N).
Proof.
  apply (proj1 (run_parse_memory_instruction_correct _ _ _)).
  exact padded_vector_memory_dispatch.
Qed.

Example padded_bulk_memory_grammar :
  exists prefix, [xfc; x8a; x00; x00; x00; x0b] = prefix ++ [x0b] /\
    memory_instruction_encoding prefix BI_memory_copy.
Proof.
  apply (proj1 (run_parse_memory_instruction_correct _ _ _)).
  exact padded_bulk_memory_dispatch.
Qed.
