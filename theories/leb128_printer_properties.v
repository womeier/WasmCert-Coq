(** Correctness of the signed encoder used by binary_format_printer.
    This is the public encoder, not an unconnected replacement.
    The arithmetic implementation retains the original bit-list helpers for
    comparison but does not trust their unproved properties. *)
(* Non-GC signed scalar encoder proofs selectively integrated from 66719d6. *)
From Stdlib Require Import ZArith List Lia.
From parseque Require Import Parseque.
From Wasm Require Import leb128 leb128_properties binary_format_parser
  binary_parser_combinator_properties.

Lemma leb_byte_value n :
  (n <= 255)%N -> Byte.to_N (leb_byte n) = n.
Proof.
  intro Range. unfold leb_byte.
  destruct (Byte.of_N n) as [b|] eqn:E.
  - now apply Byte.to_of_N.
  - apply Byte.of_N_None_iff in E. lia.
Qed.

Lemma leb_byte_Z_value z :
  (0 <= z <= 255)%Z ->
  Z.of_N (Byte.to_N (leb_byte (Z.to_N z))) = z.
Proof.
  intro Range. rewrite leb_byte_value.
  - apply Z2N.id. lia.
  - apply N2Z.inj_le. rewrite Z2N.id; lia.
Qed.

Lemma signed_terminalb_correct z :
  signed_terminalb z = true <-> (-64 <= z < 64)%Z.
Proof.
  unfold signed_terminalb.
  rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. reflexivity.
Qed.

Lemma signed_terminal_encoding z :
  (-64 <= z < 64)%Z ->
  signed_leb (leb_byte (Z.to_N (z mod 128)) :: nil) z.
Proof.
  intro Range.
  pose proof (Z.mod_pos_bound z 128 ltac:(lia)) as LowRange.
  pose proof (leb_byte_Z_value (z mod 128) ltac:(lia)) as Value.
  destruct (Z_le_dec 0 z) as [Nonnegative|Negative].
  - assert (Low : (z mod 128)%Z = z) by (apply Z.mod_small; lia).
    rewrite Low in *.
    remember (leb_byte (Z.to_N z)) as b in *.
    rewrite <- Value.
    apply sleb_end_pos. apply N2Z.inj_lt. rewrite Value. exact (proj2 Range).
  - assert (Low : (z mod 128)%Z = (z + 128)%Z).
    { symmetry. apply Z.mod_unique with (q := (-1)%Z); [left; lia | ring]. }
    rewrite Low in *.
    remember (leb_byte (Z.to_N (z + 128))) as b in *.
    replace z with (Z.of_N (Byte.to_N b) - 128)%Z
      by lia.
    apply sleb_end_neg. split.
    + apply N2Z.inj_le. rewrite Value. lia.
    + apply N2Z.inj_lt. rewrite Value. lia.
Qed.

Lemma encode_signed_fuel_correct k :
  forall fuel z,
    S k <= fuel ->
    (-64 * 128 ^ Z.of_nat k <= z < 64 * 128 ^ Z.of_nat k)%Z ->
    signed_leb (encode_signed_fuel fuel z) z /\
      length (encode_signed_fuel fuel z) <= S k.
Proof.
  induction k as [|k IH]; intros fuel z Enough Range.
  - destruct fuel as [|fuel]; [lia |].
    change (-64 <= z < 64)%Z in Range.
    assert (Terminal : signed_terminalb z = true)
      by (apply signed_terminalb_correct; exact Range).
    cbn [encode_signed_fuel]. rewrite Terminal. split.
    + now apply signed_terminal_encoding.
    + simpl. lia.
  - destruct fuel as [|fuel]; [lia |].
    cbn [encode_signed_fuel].
    destruct (signed_terminalb z) eqn:Terminal.
    + apply signed_terminalb_correct in Terminal. split.
      * now apply signed_terminal_encoding.
      * simpl. lia.
    + assert (Next :
        (-64 * 128 ^ Z.of_nat k <= z / 128 <
          64 * 128 ^ Z.of_nat k)%Z).
      {
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Range by lia.
        split.
        - apply Z.div_le_lower_bound; [lia | nia].
        - apply Z.div_lt_upper_bound; [lia | nia].
      }
      destruct (IH fuel (z / 128)%Z ltac:(lia) Next) as [Tail Width].
      pose proof (Z.mod_pos_bound z 128 ltac:(lia)) as LowRange.
      pose proof (leb_byte_Z_value (z mod 128 + 128) ltac:(lia)) as Value.
      remember (leb_byte (Z.to_N (z mod 128 + 128))) as b in *.
      remember (z / 128)%Z as q eqn:Quotient in *.
      split.
      * replace z with
          (Z.of_N (Byte.to_N b) - 128 + 128 * q)%Z.
        -- apply sleb_more.
           ++ apply N2Z.inj_le. rewrite Value. lia.
           ++ exact Tail.
        -- pose proof (Z.div_mod z 128 ltac:(lia)). lia.
      * simpl. lia.
Qed.

Lemma pos_size_nat_bound p :
  (Z.pos p < 128 ^ Z.of_nat (Pos.size_nat p))%Z.
Proof.
  induction p as [p IH|p IH|].
  - cbn [Pos.size_nat]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    change (2 * Z.pos p + 1 < 128 * 128 ^ Z.of_nat (Pos.size_nat p))%Z.
    pose proof (Z.pow_pos_nonneg 128 (Z.of_nat (Pos.size_nat p))
      ltac:(lia) ltac:(lia)). nia.
  - cbn [Pos.size_nat]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    change (2 * Z.pos p < 128 * 128 ^ Z.of_nat (Pos.size_nat p))%Z.
    pose proof (Z.pow_pos_nonneg 128 (Z.of_nat (Pos.size_nat p))
      ltac:(lia) ltac:(lia)). nia.
  - reflexivity.
Qed.

Theorem encode_signed_sound z :
  signed_leb (encode_signed z) z.
Proof.
  unfold encode_signed, signed_encoder_fuel.
  destruct z as [|p|p].
  - apply (proj1 (encode_signed_fuel_correct 0 1 0 ltac:(lia)
      ltac:(change (-64 <= 0 < 64)%Z; lia))).
  - assert (Range : (-64 * 128 ^ Z.of_nat (Pos.size_nat p) <= Z.pos p <
        64 * 128 ^ Z.of_nat (Pos.size_nat p))%Z).
    {
      pose proof (pos_size_nat_bound p).
      pose proof (Z.pow_pos_nonneg 128 (Z.of_nat (Pos.size_nat p))
        ltac:(lia) ltac:(lia)). lia.
    }
    exact (proj1 (encode_signed_fuel_correct (Pos.size_nat p)
      (S (Pos.size_nat p)) (Z.pos p) ltac:(lia) Range)).
  - assert (Range : (-64 * 128 ^ Z.of_nat (Pos.size_nat p) <= Z.neg p <
        64 * 128 ^ Z.of_nat (Pos.size_nat p))%Z).
    {
      pose proof (pos_size_nat_bound p).
      pose proof (Z.pow_pos_nonneg 128 (Z.of_nat (Pos.size_nat p))
        ltac:(lia) ltac:(lia)).
      change (-64 * 128 ^ Z.of_nat (Pos.size_nat p) <= - Z.pos p <
        64 * 128 ^ Z.of_nat (Pos.size_nat p))%Z. lia.
    }
    exact (proj1 (encode_signed_fuel_correct (Pos.size_nat p)
      (S (Pos.size_nat p)) (Z.neg p) ltac:(lia) Range)).
Qed.

Lemma encode_signed_fuel_length fuel z :
  length (encode_signed_fuel fuel z) <= fuel.
Proof.
  revert z. induction fuel as [|fuel IH]; intro z; simpl; [lia |].
  destruct (signed_terminalb z); simpl; [lia |].
  pose proof (IH (z / 128)%Z). lia.
Qed.

Lemma encode_signed_length_bound k z :
  (-64 * 128 ^ Z.of_nat k <= z < 64 * 128 ^ Z.of_nat k)%Z ->
  length (encode_signed z) <= S k.
Proof.
  intro Range. unfold encode_signed.
  destruct (le_dec (signed_encoder_fuel z) (S k)) as [Short|Enough].
  - pose proof (encode_signed_fuel_length (signed_encoder_fuel z) z). lia.
  - apply (proj2 (encode_signed_fuel_correct k
      (signed_encoder_fuel z) z ltac:(lia) Range)).
Qed.

Theorem signed_encoder_parser_roundtrip z :
  @binary_format_parser.run option _ _ _ _ Byte.byte tokBytes Z
    (encode_signed z) parse_signed = Some z.
Proof.
  apply (@run_parser_complete Z parse_signed signed_leb).
  - exact parse_signed_complete.
  - apply encode_signed_sound.
Qed.
