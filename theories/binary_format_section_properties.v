(** Framing grammar for the actual module section payload parser. *)
From Stdlib Require Import List NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties
  binary_parser_combinator_properties binary_format_vector_properties
  leb128_properties.

Lemma parser_sound_assert_sized_exact {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P size :
  parser_sound p P ->
  parser_sound (assert_sized p (fun actual => N.eqb size actual))
    (fun bs a => P bs a /\ N.of_nat (length bs) = size).
Proof.
  intros H m bound input s Run.
  apply assert_sized_option_correct in Run.
  destruct Run as [Run Width].
  destruct (H _ _ _ _ Run) as [bs [Bytes Parsed]].
  exists bs; split; [exact Bytes |]. split; [exact Parsed |].
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes s) = Success.size s) in Lout.
  rewrite Bytes, length_app in Lin.
  apply N.eqb_eq in Width.
  replace (m - Success.size s) with (length bs) in Width by lia.
  symmetry; exact Width.
Qed.

Definition section_payload_encoding {A}
    (P : list Byte.byte -> A -> Prop) bs a : Prop :=
  exists header payload,
    bs = header ++ payload /\
    unsigned_leb header (N.of_nat (length payload)) /\
    (N.of_nat (length payload) <= 4294967295)%N /\
    length header <= 5 /\ P payload a.

Theorem parse_section_payload_sound {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_sound p P ->
  parser_sound (parse_section_payload p) (section_payload_encoding P).
Proof.
  intro H. unfold parse_section_payload.
  eapply parser_sound_bind with
    (P := fun bs sz => unsigned_leb bs sz /\
      (sz <= 4294967295)%N /\ length bs <= 5)
    (Q := fun sz bs a => P bs a /\ N.of_nat (length bs) = sz).
  - apply parse_u32_bounded_prefix_sound.
  - intros sz k lt; simpl. apply parser_sound_le_lower.
    apply parser_sound_assert_sized_exact; exact H.
  - intros header payload sz a [Encoding [Range Width]] [Pa Count].
    exists header, payload. rewrite Count. auto.
Qed.

Theorem parse_section_payload_complete {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_complete p P ->
  parser_complete (parse_section_payload p) (section_payload_encoding P).
Proof.
  intro H. unfold parse_section_payload.
  eapply parser_complete_bind with
    (P := fun bs sz => unsigned_leb bs sz /\
      (sz <= 4294967295)%N /\ length bs <= 5)
    (Q := fun sz bs a => P bs a /\ N.of_nat (length bs) = sz).
  - apply parse_u32_prefix_complete.
  - intros sz k lt; simpl. apply parser_complete_le_lower.
    apply parser_complete_assert_sized.
    + eapply parser_complete_weaken; [exact H |].
      intros bs a [Pa _]; exact Pa.
    + intros bs a [_ Count]. apply N.eqb_eq. symmetry; exact Count.
  - intros bs a [header [payload [Bytes [Encoding [Range [Width Pa]]]]]].
    exists header, payload, (N.of_nat (length payload)).
    repeat split; assumption || reflexivity.
Qed.
