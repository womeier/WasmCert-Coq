(** Connection to the width-indexed integer productions in Core 3.0.
    Pinned source: WebAssembly/spec d7aada502455b3d9176ca4cbe48be4724d511d2a,
    document/core/binary/values.rst, "Integers".
    In particular, the continuation production requires N > 7; numeric
    range checks alone must not admit overlong padded representations. *)
From Stdlib Require Import ZArith List Lia.
From parseque Require Import Parseque.
From Wasm Require Import leb128_properties binary_format_parser
  binary_format_parser_properties binary_parser_combinator_properties
  binary_format_printer binary_format_printer_properties.

Definition leb_bytes (bits : nat) : nat := (bits + 6) / 7.
Definition signed_limit (bits : nat) : Z := (2 ^ Z.of_nat (bits - 1))%Z.

Inductive signed_leb_width : nat -> list Byte.byte -> Z -> Prop :=
| slw_positive : forall bits b,
    0 < bits ->
    (Byte.to_N b < 64)%N ->
    (Z.of_N (Byte.to_N b) < signed_limit bits)%Z ->
    signed_leb_width bits (b :: nil) (Z.of_N (Byte.to_N b))
| slw_negative : forall bits b,
    0 < bits ->
    (64 <= Byte.to_N b < 128)%N ->
    (128 - signed_limit bits <= Z.of_N (Byte.to_N b))%Z ->
    signed_leb_width bits (b :: nil) (Z.of_N (Byte.to_N b) - 128)%Z
| slw_continuation : forall bits b bs z,
    7 < bits ->
    (128 <= Byte.to_N b)%N ->
    signed_leb_width (bits - 7) bs z ->
    signed_leb_width bits (b :: bs)
      (Z.of_N (Byte.to_N b) - 128 + 128 * z)%Z.

Lemma byte_to_Z_bounds b :
  (0 <= Z.of_N (Byte.to_N b) <= 255)%Z.
Proof. destruct b; vm_compute; split; congruence. Qed.

Lemma leb_bytes_positive bits :
  0 < bits -> 1 <= leb_bytes bits.
Proof.
  intro Positive. unfold leb_bytes.
  apply Nat.div_le_lower_bound; lia.
Qed.

Lemma leb_bytes_small bits :
  bits <= 7 -> leb_bytes bits <= 1.
Proof.
  intro Small. unfold leb_bytes.
  assert ((bits + 6) / 7 < 2).
  { apply Nat.Div0.div_lt_upper_bound; lia. }
  lia.
Qed.

Lemma leb_bytes_step bits :
  7 < bits -> leb_bytes bits = S (leb_bytes (bits - 7)).
Proof.
  intro Larger. unfold leb_bytes.
  replace (bits + 6) with ((bits - 1) + 1 * 7) by lia.
  rewrite Nat.div_add by lia.
  replace (bits - 7 + 6) with (bits - 1) by lia.
  lia.
Qed.

Definition unsigned_limit (bits : nat) : Z := (2 ^ Z.of_nat bits)%Z.

Inductive unsigned_leb_width : nat -> list Byte.byte -> N -> Prop :=
| ulw_terminal : forall bits b,
    0 < bits ->
    (Byte.to_N b < 128)%N ->
    (Z.of_N (Byte.to_N b) < unsigned_limit bits)%Z ->
    unsigned_leb_width bits (b :: nil) (Byte.to_N b)
| ulw_continuation : forall bits b bs x,
    7 < bits ->
    (128 <= Byte.to_N b)%N ->
    unsigned_leb_width (bits - 7) bs x ->
    unsigned_leb_width bits (b :: bs)
      ((Byte.to_N b - 128) + 128 * x)%N.

Lemma unsigned_limit_step bits :
  7 < bits -> unsigned_limit bits = (128 * unsigned_limit (bits - 7))%Z.
Proof.
  intro Larger. unfold unsigned_limit.
  replace (Z.of_nat bits) with (7 + Z.of_nat (bits - 7))%Z by lia.
  rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma unsigned_more_value_Z b x :
  (128 <= Byte.to_N b)%N ->
  Z.of_N ((Byte.to_N b - 128) + 128 * x) =
    (Z.of_N (Byte.to_N b) - 128 + 128 * Z.of_N x)%Z.
Proof.
  intro High. rewrite N2Z.inj_add, N2Z.inj_sub by assumption.
  rewrite N2Z.inj_mul. reflexivity.
Qed.

Lemma unsigned_leb_nonempty bs x :
  unsigned_leb bs x -> 1 <= length bs.
Proof. intro Encoding; destruct Encoding; simpl; lia. Qed.

Theorem unsigned_leb_width_sound bits bs x :
  unsigned_leb_width bits bs x ->
  unsigned_leb bs x /\
    (Z.of_N x < unsigned_limit bits)%Z /\ length bs <= leb_bytes bits.
Proof.
  intro Encoding. induction Encoding as
    [bits b Positive Byte Range | bits b bs x Larger Byte Tail IH].
  - split; [now apply uleb_end |].
    split; [exact Range | simpl; now apply leb_bytes_positive].
  - destruct IH as [Grammar [Range Width]].
    split; [now apply uleb_more |]. split.
    + rewrite unsigned_more_value_Z by assumption.
      rewrite unsigned_limit_step by assumption.
      pose proof (byte_to_Z_bounds b). nia.
    + rewrite leb_bytes_step by assumption. simpl. lia.
Qed.

Theorem unsigned_leb_width_complete bits bs x :
  0 < bits ->
  unsigned_leb bs x ->
  (Z.of_N x < unsigned_limit bits)%Z ->
  length bs <= leb_bytes bits ->
  unsigned_leb_width bits bs x.
Proof.
  intros Positive Encoding. revert bits Positive.
  induction Encoding as [b Byte|b bs x Byte Tail IH];
    intros bits Positive Range Width.
  - now apply ulw_terminal.
  - assert (Larger : 7 < bits).
    {
      pose proof (unsigned_leb_nonempty bs x Tail).
      destruct (le_dec bits 7) as [Small|Large]; [|lia].
      pose proof (leb_bytes_small bits Small). simpl in Width. lia.
    }
    apply ulw_continuation; [exact Larger | exact Byte |].
    apply IH; [lia | |].
    + rewrite unsigned_more_value_Z in Range by assumption.
      rewrite unsigned_limit_step in Range by assumption.
      assert (High : (128 <= Z.of_N (Byte.to_N b))%Z)
        by (exact (proj1 (N2Z.inj_le _ _) Byte)).
      nia.
    + rewrite leb_bytes_step in Width by assumption. simpl in Width. lia.
Qed.

Theorem unsigned_leb_width_correct bits bs x :
  0 < bits ->
  (unsigned_leb_width bits bs x <->
    unsigned_leb bs x /\
      (Z.of_N x < unsigned_limit bits)%Z /\ length bs <= leb_bytes bits).
Proof.
  intro Positive. split; [apply unsigned_leb_width_sound |].
  intros [Encoding [Range Width]].
  now apply unsigned_leb_width_complete.
Qed.

Theorem run_typeidx_spec_correct bs x :
  @run option _ _ _ _ Byte.byte tokBytes N bs (fun _ => parse_typeidx) = Some x <->
  unsigned_leb_width 32 bs x.
Proof.
  split.
  - intro R. apply unsigned_leb_width_complete; [lia | | |].
    + apply (@run_parser_sound N (fun _ => parse_typeidx) unsigned_leb).
      * exact parse_u32_prefix_sound.
      * exact R.
    + apply run_typeidx_guards in R. destruct R as [Range Width].
      change (Z.of_N x < 4294967296)%Z.
      apply N2Z.inj_le in Range. lia.
    + apply run_typeidx_guards in R. destruct R as [Range Width].
      change (length bs <= 5). lia.
  - intro Encoding.
    apply unsigned_leb_width_sound in Encoding.
    destruct Encoding as [Grammar [Range Width]].
    apply (@run_parser_complete N (fun _ => parse_typeidx)
      (fun bytes idx => unsigned_leb bytes idx /\
        (idx <= 4294967295)%N /\ length bytes <= 5)).
    + exact parse_u32_prefix_complete.
    + split; [exact Grammar |]. split.
      * apply N2Z.inj_le. change (Z.of_N x < 4294967296)%Z in Range. lia.
      * exact Width.
Qed.

Lemma signed_limit_positive bits : (0 < signed_limit bits)%Z.
Proof. unfold signed_limit. apply Z.pow_pos_nonneg; lia. Qed.

Lemma signed_limit_step bits :
  7 < bits -> signed_limit bits = (128 * signed_limit (bits - 7))%Z.
Proof.
  intro Larger. unfold signed_limit.
  replace (Z.of_nat (bits - 1)) with
    (7 + Z.of_nat (bits - 7 - 1))%Z by lia.
  rewrite Z.pow_add_r by lia. reflexivity.
Qed.

Lemma signed_leb_nonempty bs z :
  signed_leb bs z -> 1 <= length bs.
Proof. intro Encoding; destruct Encoding; simpl; lia. Qed.

Theorem signed_leb_width_sound bits bs z :
  signed_leb_width bits bs z ->
  signed_leb bs z /\
    (-signed_limit bits <= z < signed_limit bits)%Z /\
    length bs <= leb_bytes bits.
Proof.
  intro Encoding. induction Encoding as
    [bits b Positive Byte Range |
     bits b Positive Byte Range |
     bits b bs z Larger Byte Tail IH].
  - split; [now apply sleb_end_pos |].
    pose proof (byte_to_Z_bounds b).
    pose proof (signed_limit_positive bits).
    split; [lia | simpl; now apply leb_bytes_positive].
  - split; [now apply sleb_end_neg |].
    pose proof (byte_to_Z_bounds b).
    pose proof (signed_limit_positive bits).
    destruct Byte as [Low High]. apply N2Z.inj_lt in High.
    split; [lia | simpl; now apply leb_bytes_positive].
  - destruct IH as [Grammar [Range Width]].
    split; [now apply sleb_more |].
    assert (High : (128 <= Z.of_N (Byte.to_N b))%Z).
    { exact (proj1 (N2Z.inj_le _ _) Byte). }
    pose proof (byte_to_Z_bounds b).
    split.
    + rewrite signed_limit_step by assumption. nia.
    + rewrite leb_bytes_step by assumption. simpl. lia.
Qed.

Theorem signed_leb_width_complete bits bs z :
  0 < bits ->
  signed_leb bs z ->
  (-signed_limit bits <= z < signed_limit bits)%Z ->
  length bs <= leb_bytes bits ->
  signed_leb_width bits bs z.
Proof.
  intros Positive Encoding. revert bits Positive.
  induction Encoding as [b Byte|b Byte|b bs z Byte Tail IH];
    intros bits Positive Range Width.
  - apply slw_positive; auto. exact (proj2 Range).
  - apply slw_negative; auto. lia.
  - assert (Larger : 7 < bits).
    {
      pose proof (signed_leb_nonempty bs z Tail).
      destruct (le_dec bits 7) as [Small|Large]; [|lia].
      pose proof (leb_bytes_small bits Small). simpl in Width. lia.
    }
    apply slw_continuation; [exact Larger | exact Byte |].
    apply IH; [lia | |].
    + rewrite signed_limit_step in Range by assumption.
      assert (High : (128 <= Z.of_N (Byte.to_N b))%Z)
        by (exact (proj1 (N2Z.inj_le _ _) Byte)).
      pose proof (byte_to_Z_bounds b). split; nia.
    + rewrite leb_bytes_step in Width by assumption.
      simpl in Width. lia.
Qed.

Theorem signed_leb_width_correct bits bs z :
  0 < bits ->
  (signed_leb_width bits bs z <->
    signed_leb bs z /\
      (-signed_limit bits <= z < signed_limit bits)%Z /\
      length bs <= leb_bytes bits).
Proof.
  intro Positive. split; [apply signed_leb_width_sound |].
  intros [Encoding [Range Width]].
  now apply signed_leb_width_complete.
Qed.

(** The actual exported GC heap-index decoder is sound and complete for
    the spec's signed-33 production, restricted to nonnegative u32 indices. *)
Theorem run_heap_typeidx_spec_correct bs x :
  run_parse_heap_typeidx bs = Some x <->
  signed_leb_width 33 bs (Z.of_N x).
Proof.
  rewrite run_heap_typeidx_leb_correct.
  rewrite signed_leb_width_correct by lia.
  change
    (signed_leb bs (Z.of_N x) /\ (x <= 4294967295)%N /\ length bs <= 5 <->
     signed_leb bs (Z.of_N x) /\
       (-4294967296 <= Z.of_N x < 4294967296)%Z /\ length bs <= 5).
  pose proof (N2Z.is_nonneg x).
  split; intros [Encoding [Range Width]]; split; [exact Encoding | |exact Encoding |].
  - split; [apply N2Z.inj_le in Range; lia | exact Width].
  - split; [apply N2Z.inj_le; lia | exact Width].
Qed.

Theorem binary_heap_typeidx_spec x bs :
  binary_of_heap_typeidx x = Some bs ->
  signed_leb_width 33 bs (Z.of_N x).
Proof.
  intro Printed. apply run_heap_typeidx_spec_correct.
  now apply binary_of_heap_typeidx_roundtrip.
Qed.

Theorem binary_typeidx_spec x :
  (x <= 4294967295)%N ->
  unsigned_leb_width 32 (binary_of_typeidx x) x.
Proof.
  intro Range. apply run_typeidx_spec_correct.
  now apply binary_of_typeidx_roundtrip.
Qed.
