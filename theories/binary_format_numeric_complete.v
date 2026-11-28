(** Completeness of actual scalar numeric alternatives, including ordered
    lookahead and arbitrary suffixes/bounds; not merely closed test vectors. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes numerics binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_numeric_properties binary_format_vector_properties
  binary_format_atomic_properties binary_format_language_properties leb128_properties.
Local Notation byte := Byte.byte.

Definition i32_instruction_encoding bytes be :=
  exists payload v, bytes = x41 :: payload /\
    signed_leb payload (Wasm_int.Int32.signed v) /\
    length payload <= 5 /\ be = BI_const_num (VAL_int32 v).

Definition i64_instruction_encoding bytes be :=
  exists payload v, bytes = x42 :: payload /\
    signed_leb payload (Wasm_int.Int64.signed v) /\
    length payload <= 10 /\ be = BI_const_num (VAL_int64 v).

Lemma parse_i32_const_complete n :
  parser_complete
    (parse_i32_const (Toks := SizedList byte) (M := option) (n := n))
    i32_instruction_encoding.
Proof.
  unfold parse_i32_const.
  eapply parser_complete_prefix_byte with
    (Q := fun bs be => exists v,
      signed_leb bs (Wasm_int.Int32.signed v) /\ length bs <= 5 /\
      be = BI_const_num (VAL_int32 v)).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_s32_prefix_complete |].
    intros bs be [v [Encoding [Width Value]]].
    exists v; auto.
  - intros bs be [payload [v [Bytes Facts]]].
    exists payload; split; [exact Bytes |]. exists v; exact Facts.
Qed.

Lemma parse_i64_const_complete n :
  parser_complete
    (parse_i64_const (Toks := SizedList byte) (M := option) (n := n))
    i64_instruction_encoding.
Proof.
  unfold parse_i64_const.
  eapply parser_complete_prefix_byte with
    (Q := fun bs be => exists v,
      signed_leb bs (Wasm_int.Int64.signed v) /\ length bs <= 10 /\
      be = BI_const_num (VAL_int64 v)).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_s64_prefix_complete |].
    intros bs be [v [Encoding [Width Value]]].
    exists v; auto.
  - intros bs be [payload [v [Bytes Facts]]].
    exists payload; split; [exact Bytes |]. exists v; exact Facts.
Qed.

Lemma parse_raw_bytes_complete n k :
  k <> 0%N ->
  parser_complete
    (parse_vec_aux
      (@anyTok (SizedList byte) byte _ option _ _ _ n) k)
    (fun bytes values => bytes = values /\ N.of_nat (length bytes) = k).
Proof.
  intro Nonzero.
  eapply parser_complete_weaken.
  - apply parse_vec_aux_complete; [exact Nonzero |apply parser_complete_anyTok].
  - intros bytes values [Bytes Count]; subst values.
    split; [|exact Count].
    clear Count.
    induction bytes as [|b rest IH]; [constructor |].
    change (encoded_items (fun bs b => bs = b :: nil)
      ((b :: nil) ++ rest) (b :: rest)).
    constructor; [reflexivity |apply IH].
Qed.

Definition f32_instruction_encoding bytes be :=
  exists payload, bytes = x43 :: payload /\ length payload = 4 /\
    be = BI_const_num (VAL_float32 (f32_from_bytes payload)).
Definition f64_instruction_encoding bytes be :=
  exists payload, bytes = x44 :: payload /\ length payload = 8 /\
    be = BI_const_num (VAL_float64 (f64_from_bytes payload)).

Lemma parse_f32_const_complete n :
  parser_complete
    (parse_f32_const (Toks := SizedList byte) (M := option) (n := n))
    f32_instruction_encoding.
Proof.
  unfold parse_f32_const.
  eapply parser_complete_prefix_byte with
    (Q := fun bs be => length bs = 4 /\
      be = BI_const_num (VAL_float32 (f32_from_bytes bs))).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map with
      (P := fun bs v => length bs = 4 /\ v = f32_from_bytes bs).
    + unfold parse_f32. eapply parser_complete_map.
      * apply parse_raw_bytes_complete; discriminate.
      * intros bs v [Count Value].
        exists bs; split; [split; [reflexivity |lia] |exact Value].
    + intros bs be [Count Value].
      exists (f32_from_bytes bs); split; [auto |exact Value].
  - intros bs be [payload [Bytes Facts]].
    exists payload; auto.
Qed.

Lemma parse_f64_const_complete n :
  parser_complete
    (parse_f64_const (Toks := SizedList byte) (M := option) (n := n))
    f64_instruction_encoding.
Proof.
  unfold parse_f64_const.
  eapply parser_complete_prefix_byte with
    (Q := fun bs be => length bs = 8 /\
      be = BI_const_num (VAL_float64 (f64_from_bytes bs))).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map with
      (P := fun bs v => length bs = 8 /\ v = f64_from_bytes bs).
    + unfold parse_f64. eapply parser_complete_map.
      * apply parse_raw_bytes_complete; discriminate.
      * intros bs v [Count Value].
        exists bs; split; [split; [reflexivity |lia] |exact Value].
    + intros bs be [Count Value].
      exists (f64_from_bytes bs); split; [auto |exact Value].
  - intros bs be [payload [Bytes Facts]].
    exists payload; auto.
Qed.

Lemma fixed_instruction_complete n opcode (be : basic_instruction) :
  parser_complete
    (Combinators.cmap be
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode))
    (fun bytes value => bytes = opcode :: nil /\ value = be).
Proof.
  unfold Combinators.cmap.
  eapply parser_complete_map; [apply parser_complete_exact_byte |].
  intros bytes value [Bytes Value]; subst.
  exists opcode; auto.
Qed.

Ltac numeric_initial :=
  first [apply exact_byte_initial
        |apply parser_initial_cmap; numeric_initial
        |apply parser_initial_rand; numeric_initial].

Ltac fixed_numeric_dispatch opcode be :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p ?q) _ =>
    first
      [lazymatch p with
       | Combinators.cmap ?value (exact_byte ?tag) =>
         constr_eq tag opcode; constr_eq value be
       end;
       apply parser_complete_alt_left; apply fixed_instruction_complete
      |eapply parser_complete_alt_right_initial with (actual := opcode);
       [numeric_initial
       |discriminate
       |intros bytes value [Bytes _]; exists nil; exact Bytes
       |fixed_numeric_dispatch opcode be]]
  end.

Theorem parse_numeric_fixed_complete n opcode be :
  (69 <= Byte.to_N opcode)%N ->
  nth_error fixed_numeric_instructions
    (N.to_nat (Byte.to_N opcode) - 69) = Some be ->
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => bytes = opcode :: nil /\ value = be).
Proof.
  intros Lower Opcode.
  destruct opcode;
    vm_compute in Lower, Opcode;
    try discriminate;
    try (exfalso; intuition discriminate);
    inversion Opcode; subst be; clear Opcode Lower;
    unfold parse_numeric_instruction;
    lazymatch goal with
    | |- parser_complete _ (fun bytes value =>
        bytes = ?op :: nil /\ value = ?instruction) =>
      fixed_numeric_dispatch op instruction
    end.
Qed.

Ltac constant_numeric_dispatch opcode Complete Head :=
  first
    [apply parser_complete_alt_left; exact Complete
    |eapply parser_complete_alt_right_initial with (actual := opcode);
     [numeric_initial
     |discriminate
     |exact Head
     |constant_numeric_dispatch opcode Complete Head]].

Theorem parse_numeric_i32_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    i32_instruction_encoding.
Proof.
  unfold parse_numeric_instruction.
  apply parser_complete_alt_left; apply parse_i32_const_complete.
Qed.

Theorem parse_numeric_i64_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    i64_instruction_encoding.
Proof.
  assert (Head : forall bytes be, i64_instruction_encoding bytes be ->
    exists tail, bytes = x42 :: tail).
  { intros bytes be [tail [v [Bytes _]]]; now exists tail. }
  unfold parse_numeric_instruction.
  constant_numeric_dispatch x42 (parse_i64_const_complete n) Head.
Qed.

Theorem parse_numeric_f32_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    f32_instruction_encoding.
Proof.
  assert (Head : forall bytes be, f32_instruction_encoding bytes be ->
    exists tail, bytes = x43 :: tail).
  { intros bytes be [tail [Bytes _]]; now exists tail. }
  unfold parse_numeric_instruction.
  constant_numeric_dispatch x43 (parse_f32_const_complete n) Head.
Qed.

Theorem parse_numeric_f64_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    f64_instruction_encoding.
Proof.
  assert (Head : forall bytes be, f64_instruction_encoding bytes be ->
    exists tail, bytes = x44 :: tail).
  { intros bytes be [tail [Bytes _]]; now exists tail. }
  unfold parse_numeric_instruction.
  constant_numeric_dispatch x44 (parse_f64_const_complete n) Head.
Qed.

Lemma assert_u32_complete n code :
  parser_complete
    (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
    (fun bytes value => index_encoding bytes code /\ value = code).
Proof.
  unfold assert_u32.
  eapply parser_complete_guardM; [apply parse_u32_prefix_complete |].
  intros bytes value [Encoding Value]; subst value.
  exists code. split; [exact Encoding |].
  now rewrite N.eqb_refl.
Qed.

Definition v128_instruction_encoding bytes be :=
  exists header payload, bytes = xfd :: header ++ payload /\
    index_encoding header 12%N /\ length payload = 16 /\
    be = BI_const_vec (VAL_vec128 (List.map compcert_byte_of_byte payload)).

Lemma parse_v128_const_complete n :
  parser_complete
    (parse_v128_const (Toks := SizedList byte) (M := option) (n := n))
    v128_instruction_encoding.
Proof.
  unfold parse_v128_const.
  eapply parser_complete_rand_grammar with
    (P := fun bytes code => exists header,
      bytes = xfd :: header /\ index_encoding header 12%N /\ code = 12%N)
    (Q := fun bytes be => length bytes = 16 /\
      be = BI_const_vec (VAL_vec128 (List.map compcert_byte_of_byte bytes))).
  - eapply parser_complete_prefix_byte with
      (Q := fun bytes code => index_encoding bytes 12%N /\ code = 12%N).
    + intros k lt; simpl. apply parser_complete_le_lower.
      apply assert_u32_complete.
    + intros bytes code [header [Bytes Facts]]; now exists header.
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map with
      (P := fun bytes v => length bytes = 16 /\
        v = List.map compcert_byte_of_byte bytes).
    + unfold parse_16bytes. eapply parser_complete_map.
      * apply parse_raw_bytes_complete; discriminate.
      * intros bytes v [Count Value]. exists bytes.
        split; [split; [reflexivity |lia] |exact Value].
    + intros bytes be [Count Value].
      exists (List.map compcert_byte_of_byte bytes); auto.
  - intros bytes be [header [payload [Bytes [Encoding [Count Value]]]]].
    exists (xfd :: header), payload, 12%N. split; [exact Bytes |].
    split.
    + exists header; auto.
    + auto.
Qed.

Theorem parse_numeric_v128_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    v128_instruction_encoding.
Proof.
  assert (Head : forall bytes be, v128_instruction_encoding bytes be ->
    exists tail, bytes = xfd :: tail).
  { intros bytes be [header [payload [Bytes _]]].
    now exists (header ++ payload). }
  unfold parse_numeric_instruction.
  constant_numeric_dispatch xfd (parse_v128_const_complete n) Head.
Qed.

Lemma index_encoding_prefix_injective xs ys tail1 tail2 x y :
  index_encoding xs x -> index_encoding ys y ->
  xs ++ tail1 = ys ++ tail2 -> x = y.
Proof.
  intros X Y Bytes.
  pose (input := mkSizedList (xs ++ tail1)).
  destruct (parse_u32_prefix_complete (length (xs ++ tail1))
    _ (Nat.le_refl _) input xs tail1 x eq_refl X)
    as [sx [Rx [Vx _]]].
  destruct (parse_u32_prefix_complete (length (xs ++ tail1))
    _ (Nat.le_refl _) input ys tail2 y Bytes Y)
    as [sy [Ry [Vy _]]].
  rewrite Rx in Ry; inversion Ry; subst sy. congruence.
Qed.

Lemma parser_complete_alt_right_bulk n
    (p q : Parser (SizedList byte) byte option basic_instruction n)
    expected actual Q :
  parser_sound p (fun bytes _ => bulk_prefix bytes expected) ->
  expected <> actual ->
  (forall bytes be, Q bytes be -> bulk_prefix bytes actual) ->
  parser_complete q Q -> parser_complete (Combinators.alt p q) Q.
Proof.
  intros Sound Different Prefix Complete.
  eapply parser_complete_alt_right; [exact Sound |exact Complete |].
  intros xs ys tail1 tail2 a b
    [header1 [Bytes1 Encoding1]] Qb Same.
  destruct (Prefix _ _ Qb) as [header2 [Bytes2 Encoding2]].
  subst xs ys. simpl in Same; inversion Same as [Bytes].
  apply Different.
  exact (index_encoding_prefix_injective _ _ _ _ _ _ Encoding1 Encoding2 Bytes).
Qed.

Lemma saturating_instruction_complete n code (be : basic_instruction) :
  parser_complete
    (Combinators.cmap be
      (Combinators.rand
        (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code))))
    (fun bytes value => bulk_prefix bytes code /\ value = be).
Proof.
  unfold Combinators.cmap.
  eapply parser_complete_map with
    (P := fun bytes value => bulk_prefix bytes code /\ value = code).
  - eapply parser_complete_prefix_byte with
      (Q := fun bytes value => index_encoding bytes code /\ value = code).
    + intros k lt; simpl. apply parser_complete_le_lower; apply assert_u32_complete.
    + intros bytes value [[header [Bytes Encoding]] Value].
      exists header; auto.
  - intros bytes value [Prefix Value]; subst value.
    exists code; auto.
Qed.

Ltac bulk_numeric_dispatch code be :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p ?q) _ =>
      lazymatch p with
       | Combinators.cmap ?given
           (Combinators.rand (exact_byte ?tag) (box (assert_u32 ?old))) =>
         constr_eq tag xfc;
         tryif constr_eq old code then
           (constr_eq given be;
            apply parser_complete_alt_left; apply saturating_instruction_complete)
         else
         (
         eapply parser_complete_alt_right_bulk with (expected := old) (actual := code);
         [eapply parser_sound_cmap with
            (P := fun bytes _ => bulk_prefix bytes old);
          [apply bulk_prefix_sound |];
          intros bytes parsed Prefix; exact Prefix
         |discriminate
         |intros bytes value [Prefix _]; exact Prefix
         |bulk_numeric_dispatch code be])
       | _ => eapply parser_complete_alt_right_initial with (actual := xfc);
       [numeric_initial
       |discriminate
       |intros bytes value [[header [Bytes _]] _]; exists header; exact Bytes
       |bulk_numeric_dispatch code be]
       end
  end.

Theorem parse_numeric_saturating_complete n code be :
  nth_error saturating_instructions (N.to_nat code) = Some be ->
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => bulk_prefix bytes code /\ value = be).
Proof.
  intro Opcode.
  assert (Bound : (N.to_nat code < 8)%nat).
  { change (N.to_nat code < length saturating_instructions)%nat.
    apply nth_error_Some. rewrite Opcode; discriminate. }
  assert (Cases : code = 0%N \/ code = 1%N \/ code = 2%N \/ code = 3%N \/
    code = 4%N \/ code = 5%N \/ code = 6%N \/ code = 7%N) by lia.
  destruct Cases as [C|[C|[C|[C|[C|[C|[C|C]]]]]]]; subst code;
    vm_compute in Opcode; inversion Opcode; subst be;
    unfold parse_numeric_instruction;
    lazymatch goal with
    | |- parser_complete _ (fun bytes value =>
        bulk_prefix bytes ?code /\ value = ?instruction) =>
      bulk_numeric_dispatch code instruction
    end.
Qed.
