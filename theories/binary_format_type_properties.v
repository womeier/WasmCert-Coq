(** Completeness for the actual source value/block grammar. Accepted reference
    bytes include compact and explicit nullable/non-null abstract encodings;
    they are not restricted to the canonical printer image. *)
From Stdlib Require Import List Strings.Byte Arith NArith ZArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_block_properties binary_format_numeric_complete
  binary_format_language_properties leb128_printer_properties.
From Wasm Require Import gc_types gc_binary gc_binary_parser_properties.
Local Notation byte := Byte.byte.

Lemma fixed_encoding_head {A} (opcode : byte) (expected : A) bytes value :
  bytes = opcode :: nil /\ value = expected ->
  exists tail, bytes = opcode :: tail.
Proof. intros [Bytes _]; now exists nil. Qed.

Ltac byte_type_dispatch opcode Complete Head :=
  first
    [exact Complete
    |apply parser_complete_alt_left; exact Complete
    |eapply parser_complete_alt_right_initial with (actual := opcode);
     [numeric_initial
     |discriminate
     |exact Head
     |byte_type_dispatch opcode Complete Head]].

Lemma parse_number_type_byte_complete n t :
  parser_complete
    (parse_number_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => bytes = binary_of_number_type t :: nil /\ value = t).
Proof.
  destruct t; cbn [binary_of_number_type]; unfold parse_number_type;
    lazymatch goal with
    | |- parser_complete _ (fun bytes value =>
        bytes = ?opcode :: nil /\ value = ?ty) =>
      byte_type_dispatch opcode (fixed_instruction_complete n opcode ty)
        (fixed_encoding_head opcode ty)
    end.
Qed.

Theorem parse_number_type_complete n :
  parser_complete
    (parse_number_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes t => bytes = binary_of_number_type t :: nil).
Proof.
  intros m bound input prefix suffix t Bytes Encoding.
  apply (parse_number_type_byte_complete n t
    m bound input prefix suffix t Bytes); auto.
Qed.

Theorem parse_reference_type_complete n :
  parser_complete
    (parse_reference_type (Toks := SizedList byte) (M := option) (n := n))
    reference_type_encoding.
Proof.
  unfold parse_reference_type.
  eapply parser_complete_map; [apply parse_gc_abstract_reference_prefix_complete|].
  intros bs reference [abstract [Encoded Value]]; exists abstract; auto.
Qed.

Definition value_type_encoding := source_value_type_encoding.

Lemma reference_type_head_bounds bs reference :
  reference_type_encoding bs reference ->
  exists first rest, bs = first :: rest /\ (99 <= Byte.to_N first < 123)%N.
Proof.
  intros [abstract [Encoded _]].
  unfold abstract_reference_prefix in Encoded.
  inversion Encoded as [b h rest Heap|b h rest Heap|b h rest Heap]; subst.
  - exists b, nil; split; [reflexivity|].
    destruct Heap; vm_compute; split; congruence.
  - exists x63, (b :: nil); split; [reflexivity|].
    change (99 <= 99 < 123)%N; lia.
  - exists x64, (b :: nil); split; [reflexivity|].
    change (99 <= 100 < 123)%N; lia.
Qed.

Theorem parse_value_type_complete n :
  parser_complete
    (parse_value_type (Toks := SizedList byte) (M := option) (n := n))
    value_type_encoding.
Proof.
  intros m bound input prefix suffix t Bytes Encoding.
  destruct t as [nt|vt|rt|]; [| | |contradiction].
  - assert (Complete : parser_complete
      (parse_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = binary_of_number_type nt :: nil /\
        value = T_num nt)).
    { unfold parse_value_type. apply parser_complete_alt_left.
      eapply parser_complete_map; [apply parse_number_type_complete |].
      intros bs value [Enc Value]; exists nt; auto. }
    apply (Complete m bound input prefix suffix (T_num nt) Bytes); auto.
  - destruct vt.
    assert (Complete : parser_complete
      (parse_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x7b :: nil /\ value = T_vec T_v128)).
    { unfold parse_value_type.
      eapply parser_complete_alt_right with
        (P := fun bytes value => exists t,
          bytes = binary_of_number_type t :: nil /\ value = T_num t).
      - eapply parser_sound_map; [apply parse_number_type_sound |].
        intros bs t Enc; exists t; auto.
      - apply parser_complete_alt_left. eapply parser_complete_map.
        + unfold parse_vector_type. apply fixed_instruction_complete.
        + intros bs value [Enc Value]; exists T_v128; auto.
      - intros xs ys tail1 tail2 a b [t [X _]] [Y _] Same.
        subst xs ys; destruct t; discriminate. }
    apply (Complete m bound input prefix suffix (T_vec T_v128) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => reference_type_encoding bytes rt /\
        value = T_ref rt)).
    { unfold parse_value_type.
      eapply parser_complete_alt_right with
        (P := fun bytes value => exists t,
          bytes = binary_of_number_type t :: nil /\ value = T_num t).
      - eapply parser_sound_map; [apply parse_number_type_sound |].
        intros bs t Enc; exists t; auto.
      - eapply parser_complete_alt_right with
          (P := fun bytes value => bytes = x7b :: nil /\ value = T_vec T_v128).
        + eapply parser_sound_map with
            (P := fun bytes t => bytes = binary_of_vector_type t :: nil).
          * unfold parse_vector_type.
            eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
            intros bs b [Enc _]; exact Enc.
          * intros bs t Enc. destruct t; auto.
        + eapply parser_complete_map; [apply parse_reference_type_complete |].
          intros bs value [Enc Value]; exists rt; auto.
        + intros xs ys tail1 tail2 a b [X _] [Y _] Same.
          destruct (reference_type_head_bounds ys rt Y) as [first [rest [Head Bound]]].
          subst xs ys. inversion Same; subst first.
          change (99 <= 123 < 123)%N in Bound; lia.
      - intros xs ys tail1 tail2 a b [t [X _]] [Y _] Same.
        destruct (reference_type_head_bounds ys rt Y) as [first [rest [Head Bound]]].
        subst xs ys. inversion Same; subst first.
         destruct t;
           first [change (99 <= 127 < 123)%N in Bound
                 |change (99 <= 126 < 123)%N in Bound
                 |change (99 <= 125 < 123)%N in Bound
                 |change (99 <= 124 < 123)%N in Bound]; lia. }
    apply (Complete m bound input prefix suffix (T_ref rt) Bytes); auto.
Qed.

Lemma value_type_not_empty_block bytes t suffix tail :
  value_type_encoding bytes t -> bytes ++ suffix = x40 :: tail -> False.
Proof.
  destruct t as [nt|vt|rt|]; cbn; intros Encoding Same; [| | |contradiction].
  - subst bytes. destruct nt; discriminate.
  - subst bytes. destruct vt; discriminate.
  - destruct (reference_type_head_bounds bytes rt Encoding)
      as [first [rest [Head Bound]]].
    subst bytes. inversion Same; subst first.
    change (99 <= 64 < 123)%N in Bound; lia.
Qed.

Theorem parse_block_type_complete n :
  parser_complete
    (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
    block_type_encoding.
Proof.
  intros m bound input prefix suffix bt Bytes Encoding.
  destruct bt as [x|[t|]].
  - apply (parse_block_index_full_complete n
      m bound input prefix suffix (BT_id x) Bytes).
    exists x; auto.
  - assert (Complete : parser_complete
      (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes bt => exists ty,
        value_type_encoding bytes ty /\ bt = BT_valtype (Some ty))).
    { unfold parse_block_type.
      eapply parser_complete_alt_right with (P := fun bs _ => bs = x40 :: nil).
      - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
        intros bs b [E _]; exact E.
      - apply parser_complete_alt_left.
        eapply parser_complete_map; [apply parse_value_type_complete |].
        intros bs value [ty [E Value]]; exists ty; auto.
      - intros xs ys tail1 tail2 a b X [ty [Y _]] Same.
        subst xs. simpl in Same.
        eapply value_type_not_empty_block; [exact Y|symmetry; exact Same]. }
    apply (Complete m bound input prefix suffix (BT_valtype (Some t)) Bytes).
    exists t; auto.
  - assert (Complete : parser_complete
      (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x40 :: nil /\ value = BT_valtype None)).
    { unfold parse_block_type. apply parser_complete_alt_left.
      apply fixed_instruction_complete. }
    apply (Complete m bound input prefix suffix (BT_valtype None) Bytes); auto.
Qed.

Definition source_reference_binary_wf reference :=
  exists abstract, reference = shared_reference_of_abstract abstract.

Definition source_value_binary_wf t :=
  match t with
  | T_num _ | T_vec _ => True
  | T_ref reference => source_reference_binary_wf reference
  | T_bot => False
  end.

Lemma binary_of_source_value_encoding t :
  source_value_binary_wf t ->
  value_type_encoding (binary_of_value_type t) t.
Proof.
  destruct t as [nt|vt|reference|]; simpl; intro Wf; try reflexivity;
    try contradiction.
  destruct Wf as [abstract Value]; subst reference.
  exists abstract; split; [|reflexivity].
  rewrite shared_reference_printer_correspondence.
  unfold abstract_reference_prefix.
  apply decode_abstract_reference_sound.
  pose proof (abstract_reference_codec_roundtrip abstract nil) as Roundtrip.
  now rewrite app_nil_r in Roundtrip.
Qed.

Definition block_type_binary_wf bt :=
  match bt with
  | BT_id x => (x <= 4294967295)%N
  | BT_valtype (Some t) => source_value_binary_wf t
  | BT_valtype None => True
  end.

Theorem binary_of_block_type_encoding bt :
  block_type_binary_wf bt ->
  block_type_encoding (binary_of_block_type bt) bt.
Proof.
  destruct bt as [x|[t|]]; intro Wf;
    [|now apply binary_of_source_value_encoding|reflexivity].
  unfold block_type_encoding, block_index_encoding, binary_of_block_type.
  split; [apply encode_signed_sound |]. split; [exact Wf |].
  apply (encode_signed_length_bound 4).
  change (-17179869184 <= Z.of_N x < 17179869184)%Z.
  change (x <= 4294967295)%N in Wf.
  pose proof (N2Z.is_nonneg x); lia.
Qed.

Theorem binary_of_block_type_roundtrip bt :
  block_type_binary_wf bt ->
  run (binary_of_block_type bt) (fun _ => parse_block_type) = Some bt.
Proof.
  intro Wf. apply (run_parser_complete _ block_type_encoding).
  - exact parse_block_type_complete.
  - now apply binary_of_block_type_encoding.
Qed.
