(** Nonnegative s33 block indices: not the unsigned ordinary index codec. *)
From Stdlib Require Import List NArith ZArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_format_parser_properties
  leb128 leb128_properties leb128_printer_properties.
From Wasm Require Import datatypes binary_format_language_properties.
From Wasm Require Import gc_types gc_binary gc_binary_parser_properties.

Local Notation byte := Byte.byte.

Lemma parse_number_type_sound n :
  parser_sound (parse_number_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bs t => bs = binary_of_number_type t :: nil).
Proof.
  unfold parse_number_type.
  do 3 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  all: intros bs b [Bytes _]; subst; reflexivity.
Qed.

Definition reference_type_encoding bs r :=
  exists abstract,
    abstract_reference_prefix bs abstract /\
    r = shared_reference_of_abstract abstract.

Lemma parse_reference_type_sound n :
  parser_sound (parse_reference_type (Toks := SizedList byte) (M := option) (n := n))
    reference_type_encoding.
Proof.
  unfold parse_reference_type.
  eapply parser_sound_map; [apply parse_gc_abstract_reference_sound|].
  intros bs abstract Encoding. exists abstract; auto.
Qed.

Definition source_value_type_encoding bs t :=
  match t with
  | T_num nt => bs = binary_of_number_type nt :: nil
  | T_vec vt => bs = binary_of_vector_type vt :: nil
  | T_ref r => reference_type_encoding bs r
  | T_bot => False
  end.

Lemma parse_value_type_sound n :
  parser_sound (parse_value_type (Toks := SizedList byte) (M := option) (n := n))
    source_value_type_encoding.
Proof.
  unfold parse_value_type. apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_map; [apply parse_number_type_sound |].
    intros bs t Bytes. exact Bytes.
  - eapply parser_sound_map with
      (P := fun bs t => bs = binary_of_vector_type t :: nil).
    + unfold parse_vector_type.
      eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; exact Bytes.
    + intros bs t Bytes. exact Bytes.
  - eapply parser_sound_map; [apply parse_reference_type_sound |].
    intros bs t Bytes. exact Bytes.
Qed.

Definition block_index_encoding bs x :=
  signed_leb bs (Z.of_N x) /\
  (x <= 4294967295)%N /\ length bs <= 5.

Theorem parse_block_typeidx_sound n :
  parser_sound
    (parse_block_typeidx (Toks := SizedList Byte.byte) (M := option) (n := n))
    block_index_encoding.
Proof.
  unfold parse_block_typeidx.
  eapply parser_sound_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 5).
  - intros m bound input s Run.
    apply binary_format_parser_properties.assert_sized_option_correct in Run.
    destruct Run as [Run Width].
    destruct (parser_sound_extract parse_signed signed_leb parse_signed_sound
      n m bound input s Run) as [bs [Bytes Encoding]].
    exists bs; split; [exact Bytes |]. split; [exact Encoding |].
    pose proof (@Sized.sized _ _ _ input) as Lin.
    pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
    change (length (input_bytes input) = m) in Lin.
    change (length (output_bytes s) = Success.size s) in Lout.
    rewrite Bytes, length_app in Lin.
    apply N.leb_le in Width; lia.
  - intros bs z x [Encoding Width] E.
    destruct (andb (Z.leb 0 z) (Z.leb z 4294967295)) eqn:Range;
      [|discriminate].
    apply Bool.andb_true_iff in Range.
    destruct Range as [Lower Upper].
    apply Z.leb_le in Lower; apply Z.leb_le in Upper.
    inversion E; subst x.
    unfold block_index_encoding. rewrite Z2N.id by assumption.
    split; [exact Encoding |]. split; [lia |exact Width].
Qed.

Theorem parse_block_typeidx_complete n :
  parser_complete
    (parse_block_typeidx (Toks := SizedList Byte.byte) (M := option) (n := n))
    block_index_encoding.
Proof.
  unfold parse_block_typeidx.
  eapply parser_complete_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 5).
  - apply parser_complete_assert_sized.
    + eapply parser_complete_weaken.
      * apply parser_complete_extract; exact parse_signed_complete.
      * intros bs z [Encoding _]; exact Encoding.
    + intros bs z [_ Width]. apply N.leb_le; lia.
  - intros bs x [Encoding [Range Width]].
    exists (Z.of_N x). split.
    + auto.
    + assert (Lower : Z.leb 0 (Z.of_N x) = true)
        by (apply Z.leb_le; apply N2Z.is_nonneg).
      assert (Upper : Z.leb (Z.of_N x) 4294967295 = true)
        by (apply Z.leb_le; lia).
      now rewrite Lower, Upper, N2Z.id.
Qed.

Theorem binary_of_block_index_roundtrip x :
  (x <= 4294967295)%N ->
  run (binary_of_block_type (datatypes.BT_id x))
    (fun _ => parse_block_typeidx) = Some x.
Proof.
  intro Range. apply (run_parser_complete _ block_index_encoding).
  - exact parse_block_typeidx_complete.
  - split; [apply encode_signed_sound |].
    split; [exact Range |].
    apply (encode_signed_length_bound 4).
    change (-17179869184 <= Z.of_N x < 17179869184)%Z.
    pose proof (N2Z.is_nonneg x). lia.
Qed.

Definition block_type_encoding bs bt :=
  match bt with
  | BT_id x => block_index_encoding bs x
  | BT_valtype None => bs = Byte.x40 :: nil
  | BT_valtype (Some t) =>
      source_value_type_encoding bs t
  end.

Theorem parse_block_type_sound n :
  parser_sound
    (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
    block_type_encoding.
Proof.
  unfold parse_block_type. apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bs b [Bytes _]; exact Bytes.
  - eapply parser_sound_map; [apply parse_value_type_sound |].
    intros bs t H; exact H.
  - eapply parser_sound_map; [apply parse_block_typeidx_sound |].
    intros bs x H; exact H.
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

Lemma abstract_reference_prefix_negative bs reference :
  abstract_reference_prefix bs reference ->
  exists first rest, bs = first :: rest /\ (64 <= Byte.to_N first < 128)%N.
Proof.
  unfold abstract_reference_prefix.
  intros Encoding.
  inversion Encoding as [b h rest Heap|b h rest Heap|b h rest Heap]; subst.
  - exists b, nil; split; [reflexivity|].
    destruct Heap; vm_compute; split; congruence.
  - exists Byte.x63, (b :: nil); split; [reflexivity|].
    change (64 <= 99 < 128)%N; lia.
  - exists Byte.x64, (b :: nil); split; [reflexivity|].
    change (64 <= 100 < 128)%N; lia.
Qed.

Lemma source_value_type_negative bs t :
  source_value_type_encoding bs t ->
  exists first rest, bs = first :: rest /\ (64 <= Byte.to_N first < 128)%N.
Proof.
  destruct t as [nt|vt|r|]; cbn; intros Encoding; [| | |contradiction].
  - subst bs. exists (binary_of_number_type nt), nil; split; [reflexivity|].
    destruct nt; vm_compute; split; congruence.
  - subst bs. destruct vt. exists Byte.x7b, nil; split; [reflexivity|].
    change (64 <= 123 < 128)%N; lia.
  - destruct Encoding as [abstract [Encoding _]].
    now apply abstract_reference_prefix_negative in Encoding.
Qed.

Theorem parse_block_index_full_complete n :
  parser_complete
    (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bs bt => exists x, bt = BT_id x /\ block_index_encoding bs x).
Proof.
  unfold parse_block_type.
  eapply parser_complete_alt_right with
    (P := fun bs _ => bs = Byte.x40 :: nil).
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bs b [Bytes _]; exact Bytes.
  - eapply parser_complete_alt_right with
      (P := fun bs bt => exists t, bt = BT_valtype (Some t) /\
        source_value_type_encoding bs t).
    + eapply parser_sound_map; [apply parse_value_type_sound |].
      intros bs t Encoding. exists t; auto.
    + eapply parser_complete_map; [apply parse_block_typeidx_complete |].
      intros bs bt [x [Value Encoding]]. exists x; auto.
    + intros xs ys tail1 tail2 a b
        [t [Value TypeEncoding]] [x [Value' [Encoding _]]] Same.
      destruct (source_value_type_negative xs t TypeEncoding)
        as [first [rest [Bytes Negative]]].
      subst xs.
      eapply signed_nonnegative_disjoint_negative_byte.
      * exact Encoding.
      * apply N2Z.is_nonneg.
      * exact Negative.
      * symmetry; exact Same.
  - intros xs ys tail1 tail2 a b Bytes
      [x [Value [Encoding _]]] Same.
    subst xs.
    eapply (signed_nonnegative_disjoint_negative_byte _ _ Byte.x40 _ _).
    + exact Encoding.
    + apply N2Z.is_nonneg.
    + change (64 <= 64 < 128)%N; lia.
    + symmetry; exact Same.
Qed.

Theorem binary_of_block_type_id_roundtrip x :
  (x <= 4294967295)%N ->
  run (binary_of_block_type (BT_id x)) (fun _ => parse_block_type) =
    Some (BT_id x).
Proof.
  intro Range.
  apply (run_parser_complete _
    (fun bs bt => exists x, bt = BT_id x /\ block_index_encoding bs x)).
  - exact parse_block_index_full_complete.
  - exists x. split; [reflexivity |].
    split; [apply encode_signed_sound |].
    split; [exact Range |].
    apply (encode_signed_length_bound 4).
    change (-17179869184 <= Z.of_N x < 17179869184)%Z.
    pose proof (N2Z.is_nonneg x). lia.
Qed.
