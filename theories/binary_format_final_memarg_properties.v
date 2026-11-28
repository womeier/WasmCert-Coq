(** Shared final-memarg handoff: reuse the existing consumed-byte grammar,
    now with u64 offsets. No new parser or parallel memarg semantics. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes operations type_checker
  binary_format_parser binary_format_printer binary_format_properties
  binary_memory_grammar_properties binary_parser_combinator_properties
  multi_memory_properties list_extra.
Local Notation byte := Byte.byte.

Definition final_memarg_binary_wf (marg : memarg) :=
  (marg.(memarg_align) < 64)%N /\
  (marg.(memarg_memory) < u32_bound)%N /\
  (marg.(memarg_offset) < u64_bound)%N.

Theorem binary_of_final_memarg_encoding marg :
  final_memarg_binary_wf marg ->
  binary_memarg (binary_of_memarg marg) marg.
Proof.
  intros [Align [Memory Offset]].
  apply (run_parser_sound (fun n => parse_memarg) binary_memarg).
  - exact parse_memarg_binary_sound.
  - now apply binary_memarg_run_round_trip.
Qed.

Theorem final_memarg_print_prefix marg :
  final_memarg_binary_wf marg ->
  forall n m (bound : m <= n) (input : SizedList byte m) suffix,
    input_bytes input = binary_of_memarg marg ++ suffix ->
    option_map (fun s => (Success.value s, output_bytes s))
      (runParser (parse_memarg (M := option) (n := n)) bound input) =
    Some (marg, suffix).
Proof.
  intros Wf n m bound input suffix Bytes.
  destruct (parse_memarg_binary_complete n m bound input
    (binary_of_memarg marg) suffix marg Bytes
    (binary_of_final_memarg_encoding marg Wf)) as [s [Run [Value Rest]]].
  rewrite Run; simpl.
  change (Some (Success.value s, output_bytes s) = Some (marg, suffix)).
  unfold output_bytes, input_bytes; now rewrite Value, Rest.
Qed.

(** Direct constructor adapters for the tail@724b72b prefix interface.
    Headers may be padded, explicit memory index zero is retained, and
    suffixes are real leftover bytes, not a whole-input specialization. *)
Theorem final_memarg_implicit_prefix_complete n m (bound : m <= n)
    (input : SizedList byte m) flags offsets suffix align off :
  input_bytes input = (flags ++ offsets) ++ suffix ->
  binary_u32 flags align -> (align < 64)%N -> binary_u64 offsets off ->
  option_map (fun s => (Success.value s, output_bytes s))
    (runParser (parse_memarg (M := option) (n := n)) bound input) =
  Some (Build_memarg off align 0%N, suffix).
Proof.
  intros Bytes Flags Align Offset.
  destruct (parse_memarg_binary_complete n m bound input
    (flags ++ offsets) suffix (Build_memarg off align 0%N) Bytes
    (binary_memarg_compact flags offsets align off Flags Align Offset))
    as [s [Run [Value Rest]]].
  rewrite Run; simpl.
  change (Some (Success.value s, output_bytes s) =
    Some (Build_memarg off align 0%N, suffix)).
  unfold output_bytes, input_bytes; now rewrite Value, Rest.
Qed.

Theorem final_memarg_explicit_prefix_complete n m (bound : m <= n)
    (input : SizedList byte m) flags indices offsets suffix flag memory off :
  input_bytes input = (flags ++ indices ++ offsets) ++ suffix ->
  binary_u32 flags flag -> (64 <= flag < 128)%N ->
  binary_u32 indices memory -> binary_u64 offsets off ->
  option_map (fun s => (Success.value s, output_bytes s))
    (runParser (parse_memarg (M := option) (n := n)) bound input) =
  Some (Build_memarg off (flag - 64)%N memory, suffix).
Proof.
  intros Bytes Flags [Low High] Memory Offset.
  destruct (parse_memarg_binary_complete n m bound input
    (flags ++ indices ++ offsets) suffix (Build_memarg off (flag - 64)%N memory) Bytes
    (binary_memarg_indexed flags indices offsets flag memory off
      Flags Low High Memory Offset)) as [s [Run [Value Rest]]].
  rewrite Run; simpl.
  change (Some (Success.value s, output_bytes s) =
    Some (Build_memarg off (flag - 64)%N memory, suffix)).
  unfold output_bytes, input_bytes; now rewrite Value, Rest.
Qed.

Theorem final_memarg_memory32_offset_rejected marg :
  (4294967296 <= marg.(memarg_offset))%N ->
  memarg_offset32_valid marg = false.
Proof.
  intro Range; unfold memarg_offset32_valid.
  now apply N.ltb_ge.
Qed.

Theorem final_memarg_scalar_validation_rejected C ct marg t tp :
  (4294967296 <= marg.(memarg_offset))%N ->
  check_single C ct (BI_load t tp marg) = None.
Proof.
  intro Offset; destruct ct as [ts|]; [|reflexivity].
  cbn [check_single].
  destruct (lookup_N (tc_mems C) (memarg_memory marg)); [|reflexivity].
  unfold load_store_memarg_bounds.
  now rewrite (final_memarg_memory32_offset_rejected marg Offset).
Qed.

Lemma flags64_u64_grammar :
  binary_memarg (x40 :: x00 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil)
    (Build_memarg 4294967296%N 0%N 0%N).
Proof.
  destruct (decode_memarg_sound
    (x40 :: x00 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil)
    (Build_memarg 4294967296%N 0%N 0%N) nil ltac:(vm_compute; reflexivity))
    as [prefix [Bytes Grammar]].
  now rewrite app_nil_r in Bytes; subst prefix.
Qed.

Lemma flags65_u64_grammar :
  binary_memarg (x41 :: x01 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil)
    (Build_memarg 4294967296%N 1%N 1%N).
Proof.
  destruct (decode_memarg_sound
    (x41 :: x01 :: x80 :: x80 :: x80 :: x80 :: x10 :: nil)
    (Build_memarg 4294967296%N 1%N 1%N) nil ltac:(vm_compute; reflexivity))
    as [prefix [Bytes Grammar]].
  now rewrite app_nil_r in Bytes; subst prefix.
Qed.
