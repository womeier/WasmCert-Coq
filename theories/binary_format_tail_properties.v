(** Minimal adaptation of the 8d465bf consumed-byte handoff to the common
    independent u32 grammar.  Reuses the production grouped tail alternative
    without importing another unsigned decoder or recursive framework. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_atomic_properties.
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
  unfold parse_tail_call. apply parser_sound_alt.
  - unfold parse_return_call, extract_funcidx.
    apply parser_sound_prefix_byte with
      (Q := fun bs be => exists index,
        index_encoding bs index /\ be = BI_return_call index).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_map; [apply parse_index_sound |].
      intros bs index E; exists index; auto.
    + intros bs be [index [E Value]].
      left; exists bs, index; auto.
  - unfold parse_return_call_indirect.
    apply parser_sound_prefix_byte with
      (Q := fun bs be => exists types tables typ tab,
        bs = types ++ tables /\ index_encoding types typ /\
        index_encoding tables tab /\ be = BI_return_call_indirect tab typ).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_app with
        (P := fun bs f => exists typ, index_encoding bs typ /\
          f = (fun tab => BI_return_call_indirect tab typ))
        (Q := index_encoding).
      * eapply parser_sound_map; [apply parse_index_sound |].
        intros bs typ E; exists typ; auto.
      * intros j lower; simpl. apply parser_sound_le_lower; apply parse_index_sound.
      * intros types tables f tab [typ [E F]] E'; subst f.
        exists types, tables, typ, tab. split; [reflexivity |].
        split; [exact E |]. split; [exact E' |reflexivity].
    + intros bs be [types [tables [typ [tab [Bytes Facts]]]]].
      right; exists types, tables, typ, tab; subst bs; auto.
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
