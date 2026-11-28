(** Compile-time compatibility checks against the two public contracts in
    binary_parser_combinator_properties.v at 1d15428/ddb7f82. Only those
    definitions are reproduced locally; no alternate recursive framework. *)
From Wasm Require Import datatypes binary_format_parser binary_format_properties
  binary_memory_properties binary_memory_grammar_properties.
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.

Module PinnedContractAudit.

Definition input_bytes {n} (ts : SizedList Byte.byte n) : list Byte.byte :=
  @Sized.value _ _ _ ts.

Definition output_bytes {A n}
    (s : Success.Success (SizedList Byte.byte) Byte.byte A n) : list Byte.byte :=
  input_bytes (Success.leftovers s).

Definition parser_sound {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) : Prop :=
  forall m (bound : m <= n) input s,
    runParser p bound input = Some s ->
    exists prefix,
      input_bytes input = prefix ++ output_bytes s /\
      P prefix (Success.value s).

Definition parser_complete {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) : Prop :=
  forall m (bound : m <= n) input prefix suffix a,
    input_bytes input = prefix ++ suffix ->
    P prefix a ->
    exists s,
      runParser p bound input = Some s /\
      Success.value s = a /\ output_bytes s = suffix.

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
  parser_sound (parse_static_offset (n := n)) binary_u32.
Proof. exact (parse_u32_binary_sound n). Qed.

Example offset_complete n :
  parser_complete (parse_static_offset (n := n)) binary_u32.
Proof. exact (parse_u32_binary_complete n). Qed.

End PinnedContractAudit.
