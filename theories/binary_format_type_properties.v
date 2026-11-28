(** Concrete byte-type completeness for the existing non-GC type grammar. *)
From Stdlib Require Import List Strings.Byte Arith NArith ZArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_block_properties binary_format_numeric_complete
  binary_format_language_properties leb128_printer_properties
  binary_format_value_properties binary_locals_printer_properties.
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
      - intros xs ys tail1 tail2 a b X [ty [Valid _]] Same.
        destruct (value_type_encoding_head ys ty Valid)
          as [head [tail [Y [_ Nonempty]]]].
         subst xs ys. simpl in Same; inversion Same. congruence. }
    apply (Complete m bound input prefix suffix (BT_valtype (Some t)) Bytes).
    exists t; auto.
  - assert (Complete : parser_complete
      (parse_block_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x40 :: nil /\ value = BT_valtype None)).
    { unfold parse_block_type. apply parser_complete_alt_left.
      apply fixed_instruction_complete. }
    apply (Complete m bound input prefix suffix (BT_valtype None) Bytes); auto.
Qed.

Definition block_type_binary_wf bt :=
  match bt with
  | BT_id x => (x <= 4294967295)%N
  | BT_valtype (Some t) => printable_local_type t
  | BT_valtype None => True
  end.

Theorem binary_of_block_type_encoding bt :
  block_type_binary_wf bt ->
  block_type_encoding (binary_of_block_type bt) bt.
Proof.
  destruct bt as [x|[t|]]; intro Wf;
    [|now apply binary_of_value_type_encoding|reflexivity].
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
