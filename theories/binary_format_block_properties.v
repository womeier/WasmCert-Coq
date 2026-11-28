(** Signed block indices on the actual EH parser/printer. The unsigned
    typeidx path collides with empty/value block types (notably index 64). *)
From Stdlib Require Import List Strings.Byte NArith ZArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes gc_types gc_binary_parser_properties
  binary_format_parser binary_format_printer binary_format_reference_properties
  binary_format_eh_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties leb128_properties leb128_printer_properties.
Local Notation byte := Byte.byte.

Lemma shared_heap_byte_negative b h :
  shared_heap_encoding b h -> (64 <= Byte.to_N b < 128)%N.
Proof. intro Heap; destruct Heap; try destruct H; cbn; lia. Qed.

Lemma source_reference_first_negative bytes rt :
  source_reference_encoding bytes rt ->
  exists first rest, bytes = first :: rest /\ (64 <= Byte.to_N first < 128)%N.
Proof.
  intro Enc; destruct Enc.
  - destruct H as [b [Bytes Heap]].
    exists b, nil; split; [exact Bytes |now apply shared_heap_byte_negative in Heap].
  - exists x63, bytes; split; [reflexivity |cbn; lia].
  - exists x64, bytes; split; [reflexivity |cbn; lia].
Qed.

Lemma source_value_first_negative bytes t :
  source_value_encoding bytes t ->
  exists first rest, bytes = first :: rest /\ (64 <= Byte.to_N first < 128)%N.
Proof.
  intro Enc; destruct Enc.
  - exists (binary_of_number_type t), nil; split; [exact H |].
    destruct t; cbn; lia.
  - exists x7b, nil; split; [reflexivity |cbn; lia].
  - eapply source_reference_first_negative; exact H.
Qed.

Lemma parse_abstract_reference_source_sound n :
  parser_sound (parse_reference_type (Toks := SizedList byte) (M := option) (n := n))
    source_reference_encoding.
Proof.
  unfold parse_reference_type; apply parser_sound_alt.
  - eapply parser_sound_map.
    + apply eh_prefixed_sound; apply parse_supported_heap_sound.
    + intros bytes h [body [-> Enc]]; constructor; now constructor.
  - apply parser_sound_alt.
    + eapply parser_sound_map.
      * apply eh_prefixed_sound; apply parse_supported_heap_sound.
      * intros bytes h [body [-> Enc]]; constructor; now constructor.
    + eapply parser_sound_map; [apply parse_supported_heap_sound |].
      intros bytes h Enc; now constructor.
Qed.

Lemma parse_value_type_source_sound n :
  parser_sound (parse_value_type (Toks := SizedList byte) (M := option) (n := n))
    source_value_encoding.
Proof.
  unfold parse_value_type; apply parser_sound_alt.
  - eapply parser_sound_map; [apply parse_number_type_sound |].
    intros bytes t Enc; now constructor.
  - apply parser_sound_alt.
    + eapply parser_sound_map with (P := fun bytes (_ : vector_type) => bytes = x7b :: nil).
      * unfold parse_vector_type; eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
        intros bytes b [Bytes _]; exact Bytes.
      * intros bytes t Enc; subst bytes; destruct t; constructor.
    + eapply parser_sound_map; [apply parse_abstract_reference_source_sound |].
      intros bytes rt Enc; now constructor.
Qed.

Lemma signed_nonnegative_disjoint_negative_byte bs z b tail rest :
  signed_leb bs z -> (0 <= z)%Z ->
  (64 <= Byte.to_N b < 128)%N ->
  bs ++ rest = b :: tail -> False.
Proof.
  intros E Nonnegative Negative Bytes.
  inversion E; subst; simpl in Bytes; inversion Bytes; subst;
    pose proof (N2Z.is_nonneg (Byte.to_N b)); lia.
Qed.

Theorem parse_block_index_full_complete n :
  parser_complete (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bs bt => exists x, bt = BT_id x /\ source_heap_index_encoding bs x).
Proof.
  unfold parse_block_type.
  eapply parser_complete_alt_right with (P := fun bs _ => bs = x40 :: nil).
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bs b [Bytes _]; exact Bytes.
  - eapply parser_complete_alt_right with
      (P := fun bs bt => exists t, bt = BT_valtype (Some t) /\ source_value_encoding bs t).
    + eapply parser_sound_map; [apply parse_value_type_source_sound |].
      intros bs t H; exists t; auto.
    + eapply parser_complete_map; [apply parse_heap_typeidx_prefix_complete |].
      intros bs bt [x [Value Encoding]]; exists x; auto.
    + intros xs ys tail1 tail2 a b [t [Value Enc]] [x [Value' [Encoding _]]] Same.
      destruct (source_value_first_negative xs t Enc) as [first [rest [Bytes Negative]]].
      subst xs; eapply signed_nonnegative_disjoint_negative_byte.
      * exact Encoding.
      * apply N2Z.is_nonneg.
      * exact Negative.
      * symmetry; exact Same.
  - intros xs ys tail1 tail2 a b Bytes [x [Value [Encoding _]]] Same.
    subst xs; eapply (signed_nonnegative_disjoint_negative_byte _ _ x40 _ _).
    + exact Encoding.
    + apply N2Z.is_nonneg.
    + cbn; lia.
    + symmetry; exact Same.
Qed.

Theorem binary_of_block_type_id_roundtrip x :
  (x <= 4294967295)%N ->
  run (binary_of_block_type (BT_id x)) (fun n => parse_block_type (n := n)) =
    Some (BT_id x).
Proof.
  intro Range.
  apply (run_parser_complete _
    (fun bs bt => exists x, bt = BT_id x /\ source_heap_index_encoding bs x)).
  - exact parse_block_index_full_complete.
  - exists x; split; [reflexivity |].
    split; [apply encode_signed_sound |].
    split; [exact Range |].
    apply (encode_signed_length_bound 4).
    change (-17179869184 <= Z.of_N x < 17179869184)%Z.
    pose proof (N2Z.is_nonneg x); lia.
Qed.
