(** Concrete arbitrary-suffix completeness of production memory immediates.
    No atomic parser contracts are assumed. *)
From Stdlib Require Import List Strings.Byte NArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_printer_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_memory_properties
  leb128_unsigned_printer_properties leb128_properties.
Local Notation byte := Byte.byte.

Lemma parse_offset_complete n flags :
  parser_complete
    (Combinators.map (fun offset => {| memarg_offset := offset; memarg_align := flags |})
      (parse_static_offset (Toks := SizedList byte) (M := option) (n := n)))
    (mapped_offset_encoding flags).
Proof.
  eapply parser_complete_map; [apply parse_u32_prefix_complete |].
  intros bytes marg Enc; exact Enc.
Qed.

Theorem parse_memarg_complete n :
  parser_complete (parse_memarg (Toks := SizedList byte) (M := option) (n := n))
    memarg_encoding.
Proof.
  unfold parse_memarg.
  eapply parser_complete_bind with (P := index_encoding) (Q := memarg_tail_encoding).
  - apply parse_u32_prefix_complete.
  - intros flags k lt; unfold memarg_tail_encoding.
    destruct (N.ltb flags 64); simpl.
    + apply parser_complete_le_lower; apply parse_offset_complete.
    + destruct (N.ltb flags 128); simpl.
      * apply parser_complete_le_lower.
        eapply parser_complete_rand_grammar with
          (P := fun bytes x => index_encoding bytes 0%N /\ x = 0%N)
          (Q := mapped_offset_encoding (flags - 64)%N).
        -- apply assert_u32_complete.
        -- intros j lower; simpl; apply parser_complete_le_lower; apply parse_offset_complete.
        -- intros bytes marg [memory [offset [Bytes [Memory Offset]]]].
           exists memory, offset, 0%N; split; [exact Bytes |].
           split; [auto |exact Offset].
      * intros m bound input prefix suffix marg Bytes Impossible; contradiction.
  - intros bytes marg Enc; exact Enc.
Qed.

Theorem run_parse_memarg_correct bytes marg rest :
  run_parse_prefix (fun n => parse_memarg (n := n)) bytes = Some (marg, rest) <->
  exists prefix, bytes = prefix ++ rest /\ memarg_encoding prefix marg.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_memarg_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_memarg_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest marg Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (marg, rest)).
    now rewrite Value, Rest.
Qed.

Theorem scalar_memory_instruction_complete n opcode (make : memarg -> basic_instruction) :
  parser_complete
    (Combinators.rand (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.map make parse_memarg)))
    (fun bytes be => exists body marg,
      bytes = opcode :: body /\ memarg_encoding body marg /\ be = make marg).
Proof.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists marg, memarg_encoding bytes marg /\ be = make marg).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_memarg_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be [body [marg [Bytes [Enc Value]]]].
    exists body; split; [exact Bytes |exists marg; auto].
Qed.
