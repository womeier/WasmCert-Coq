(** Minimal adaptation of the 8d465bf consumed-byte handoff to the common
    independent u32 grammar.  Reuses the production grouped tail alternative
    without importing another unsigned decoder or recursive framework. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_atomic_properties tail_call_parser_properties leb128_properties.
Local Notation byte := Byte.byte.

Definition tail_instruction_encoding bytes be :=
  (exists payload index, bytes = x12 :: payload /\
    index_encoding payload index /\ be = BI_return_call index) \/
  (exists types tables typ tab, bytes = x13 :: types ++ tables /\
    index_encoding types typ /\ index_encoding tables tab /\
    be = BI_return_call_indirect tab typ).

Lemma parse_tail_call_sound n :
  parser_sound
    (parse_tail_call (Toks := SizedList byte) (M := option) (n := n))
    tail_instruction_encoding.
Proof.
  eapply parser_sound_weaken;
    [apply tail_call_parser_properties.parse_tail_call_grammar_sound |].
  intros bytes be [Direct|Indirect].
  - inversion Direct as [input index suffix [Encoding Range]]; subst.
    destruct (bounded_uleb_unsigned_sound _ _ _ _ Encoding)
      as [payload [Bytes [E Width]]].
    rewrite app_nil_r in Bytes. subst input.
    left. exists payload, index. repeat split; auto.
  - inversion Indirect as [input typ middle tab suffix
      [Types TypeRange] [Tables TableRange]]; subst.
    destruct (bounded_uleb_unsigned_sound _ _ _ _ Types)
      as [types [Bytes [E Width]]].
    destruct (bounded_uleb_unsigned_sound _ _ _ _ Tables)
      as [tables [Rest [E' Width']]].
    rewrite app_nil_r in Rest. subst middle input.
    right. exists types, tables, typ, tab. repeat split; auto.
Qed.

Theorem parse_tail_call_consumed_sound :
  forall n m (bound : m <= n) (input : SizedList byte m)
    (result : Success.Success (SizedList byte) byte basic_instruction m),
  runParser (parse_tail_call (M := option) (n := n)) bound input = Some result ->
  exists bytes,
    @Sized.value _ _ _ input =
      bytes ++ @Sized.value _ _ _ (Success.leftovers result) /\
    tail_instruction_encoding bytes (Success.value result).
Proof. exact parse_tail_call_sound. Qed.

Lemma parse_tail_call_control_sound n :
  parser_sound
    (parse_tail_call (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  eapply parser_sound_weaken; [apply parse_tail_call_sound |].
  intros bytes be [[payload [index [Bytes [E Value]]]]|
    [types [tables [typ [tab [Bytes [E [E' Value]]]]]]]];
    subst bytes be.
  - apply control_index; [unfold single_index_opcodes; simpl; tauto |exact E].
  - now apply control_return_call_indirect.
Qed.
