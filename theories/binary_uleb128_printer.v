(** Canonical unsigned LEB128 encoding with a proved bounded-decoder inverse.
    The five-byte instance is used for tail-call indices. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From Wasm Require Import binary_uleb128 leb128.

Open Scope N_scope.

Definition small_byte (value : N) : byte :=
  match Byte.of_N value with
  | Some b => b
  | None => x00
  end.

Lemma small_byte_correct : forall value,
    value <= 255 -> Byte.to_N (small_byte value) = value.
Proof.
  intros value Hbound.
  unfold small_byte.
  destruct (Byte.of_N value) as [b|] eqn:Hbyte.
  - now apply Byte.to_of_N in Hbyte.
  - apply Byte.of_N_None_iff in Hbyte. lia.
Qed.

Fixpoint uleb_limit (fuel : nat) : N :=
  match fuel with
  | O => 1
  | S fuel' => 128 * uleb_limit fuel'
  end.

Fixpoint encode_uleb (fuel : nat) (value : N) : option (list byte) :=
  match fuel with
  | O => None
  | S fuel' =>
      if N.ltb value 128 then Some (small_byte value :: nil)
      else option_map (cons (small_byte (value mod 128 + 128)))
        (encode_uleb fuel' (value / 128))
  end.

Lemma encode_uleb_complete : forall fuel value,
    (0 < fuel)%nat ->
    value < uleb_limit fuel ->
    exists bytes,
      encode_uleb fuel value = Some bytes /\
      forall suffix, uleb_prefix fuel (List.app bytes suffix) value suffix.
Proof.
  induction fuel as [|fuel IH]; intros value Hfuel Hbound; [lia |].
  cbn [encode_uleb].
  destruct (N.ltb value 128) eqn:Hsmall.
  - apply N.ltb_lt in Hsmall.
    exists (small_byte value :: nil).
    split; [reflexivity |].
    intro suffix. cbn.
    replace value with (Byte.to_N (small_byte value)) at 2
      by (apply small_byte_correct; lia).
    constructor. rewrite small_byte_correct; lia.
  - apply N.ltb_ge in Hsmall.
    assert (Hfuel' : (0 < fuel)%nat).
    { destruct fuel; cbn [uleb_limit] in Hbound; lia. }
    assert (Hquot : value / 128 < uleb_limit fuel).
    { apply N.div_lt_upper_bound; [discriminate | exact Hbound]. }
    destruct (IH (value / 128) Hfuel' Hquot) as [bytes [Hencode Hprefix]].
    rewrite Hencode.
    exists (small_byte (value mod 128 + 128) :: bytes).
    split; [reflexivity |].
    intro suffix. cbn.
    assert (Hmod : value mod 128 < 128) by (apply N.mod_lt; discriminate).
    assert (Hbyte : Byte.to_N (small_byte (value mod 128 + 128)) =
      value mod 128 + 128) by (apply small_byte_correct; lia).
    assert (Hvalue : value =
      Byte.to_N (small_byte (value mod 128 + 128)) - 128 +
        128 * (value / 128)).
    { pose proof (N.div_mod value 128 ltac:(discriminate)).
      rewrite Hbyte, N.add_sub. nia. }
    rewrite Hvalue at 2.
    apply uleb_more.
    + rewrite Hbyte. apply N.le_add_l.
    + apply Hprefix.
Qed.

(** Keep the existing total printer behavior for out-of-range AST indices.
    The fallback is unreachable for every well-formed u32 index. *)
Definition binary_of_tailidx (index : N) : list byte :=
  match encode_uleb 5 index with
  | Some bytes => bytes
  | None => leb128.encode_unsigned index
  end.

Theorem binary_of_tailidx_correct : forall index suffix,
    index <= 4294967295 ->
    u32_prefix (List.app (binary_of_tailidx index) suffix) index suffix.
Proof.
  intros index suffix Hbound.
  assert (Hlimit : index < uleb_limit 5).
  { cbn [uleb_limit]. lia. }
  destruct (encode_uleb_complete 5 index ltac:(lia) Hlimit)
    as [bytes [Hencode Hprefix]].
  unfold binary_of_tailidx. rewrite Hencode.
  split; [apply Hprefix | assumption].
Qed.

Corollary binary_of_tailidx_roundtrip : forall index suffix,
    index <= 4294967295 ->
    decode_u32 (List.app (binary_of_tailidx index) suffix) =
      Some (index, suffix).
Proof.
  intros index suffix Hbound.
  apply decode_u32_correct.
  now apply binary_of_tailidx_correct.
Qed.
