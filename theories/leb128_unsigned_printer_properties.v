(** Correctness of the unsigned encoder used by ordinary indices, vector
    lengths and section sizes in the actual binary printer. *)
(* Non-GC unsigned scalar encoder proofs selectively integrated from 284c24e. *)
From Stdlib Require Import ZArith List Lia.
From parseque Require Import Parseque.
From Wasm Require Import leb128 leb128_properties leb128_printer_properties
  binary_format_parser binary_parser_combinator_properties.
From Wasm Require binary_codec.

(** Bridge to the bounded encoder retained by the multi-memory production
    printer. Both fuel choices produce exactly the same canonical bytes when
    they suffice; this is an equality proof, not a finite-codec test. *)
Lemma bounded_unsigned_encoder_agrees fuel :
  forall other n,
    (0 < fuel)%nat -> (0 < other)%nat ->
    (Z.of_N n < 128 ^ Z.of_nat fuel)%Z ->
    (Z.of_N n < 128 ^ Z.of_nat other)%Z ->
    binary_codec.encode_uleb fuel n = leb128.encode_unsigned_fuel other n.
Proof.
  induction fuel as [|fuel IH]; intros [|other] n Positive Other Range RangeOther;
    try lia.
  cbn [binary_codec.encode_uleb leb128.encode_unsigned_fuel].
  destruct (N.ltb n 128) eqn:Terminal.
  - reflexivity.
  - apply N.ltb_ge in Terminal.
    assert (Fuel : (0 < fuel)%nat).
    { destruct fuel; [cbn in Range; lia | lia]. }
    assert (OtherFuel : (0 < other)%nat).
    { destruct other; [cbn in RangeOther; lia | lia]. }
    assert (Next : (Z.of_N (n / 128) < 128 ^ Z.of_nat fuel)%Z).
    { rewrite N2Z.inj_div.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in Range by lia.
      apply Z.div_lt_upper_bound; lia. }
    assert (NextOther : (Z.of_N (n / 128) < 128 ^ Z.of_nat other)%Z).
    { rewrite N2Z.inj_div.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in RangeOther by lia.
      apply Z.div_lt_upper_bound; lia. }
    rewrite N.add_comm.
    f_equal. now apply IH.
Qed.

Lemma bounded_u32_encoder_agrees n :
  (n < 4294967296)%N ->
  binary_codec.encode_uleb 5 n = leb128.encode_unsigned n.
Proof.
  intro Range. unfold leb128.encode_unsigned.
  apply bounded_unsigned_encoder_agrees.
  - lia.
  - destruct n; cbn [unsigned_encoder_fuel]; lia.
  - change (Z.of_N n < 34359738368)%Z. lia.
  - destruct n as [|p]; [cbn; lia |].
    cbn [unsigned_encoder_fuel].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (pos_size_nat_bound p).
    pose proof (Z.pow_pos_nonneg 128 (Z.of_nat (Pos.size_nat p))
      ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma encode_unsigned_fuel_correct k :
  forall fuel n,
    S k <= fuel ->
    (Z.of_N n < 128 ^ Z.of_nat (S k))%Z ->
    unsigned_leb (encode_unsigned_fuel fuel n) n /\
      length (encode_unsigned_fuel fuel n) <= S k.
Proof.
  induction k as [|k IH]; intros fuel n Enough Range.
  - destruct fuel as [|fuel]; [lia |].
    change (Z.of_N n < 128)%Z in Range.
    assert (Terminal : N.ltb n 128 = true).
    { apply N.ltb_lt. apply N2Z.inj_lt. exact Range. }
    cbn [encode_unsigned_fuel]. rewrite Terminal.
    assert (Byte : Byte.to_N (leb_byte n) = n) by (apply leb_byte_value; lia).
    split.
    + rewrite <- Byte at 2. apply uleb_end. rewrite Byte. apply N.ltb_lt in Terminal.
      exact Terminal.
    + simpl. lia.
  - destruct fuel as [|fuel]; [lia |].
    cbn [encode_unsigned_fuel].
    destruct (N.ltb n 128) eqn:Terminal.
    + apply N.ltb_lt in Terminal.
      assert (Byte : Byte.to_N (leb_byte n) = n) by (apply leb_byte_value; lia).
      split.
      * rewrite <- Byte at 2. apply uleb_end. now rewrite Byte.
      * simpl. lia.
    + assert (Next : (Z.of_N (n / 128) < 128 ^ Z.of_nat (S k))%Z).
      {
        rewrite N2Z.inj_div.
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Range by lia.
        apply Z.div_lt_upper_bound; [lia | exact Range].
      }
      destruct (IH fuel (n / 128)%N ltac:(lia) Next) as [Tail Width].
      pose proof (N.mod_lt n 128 ltac:(lia)) as Low.
      assert (Byte :
        Byte.to_N (leb_byte (n mod 128 + 128)) = (n mod 128 + 128)%N).
      { apply leb_byte_value. lia. }
      remember (leb_byte (n mod 128 + 128)) as b in *.
      remember (n / 128)%N as q eqn:Quotient in *.
      split.
      * replace n with ((Byte.to_N b - 128) + 128 * q)%N.
        -- apply uleb_more; [rewrite Byte; apply N.le_add_l | exact Tail].
        -- rewrite Byte, N.add_sub, Quotient.
           pose proof (N.div_mod n 128 ltac:(lia)). lia.
      * simpl. lia.
Qed.

Theorem encode_unsigned_sound n :
  unsigned_leb (encode_unsigned n) n.
Proof.
  unfold encode_unsigned, unsigned_encoder_fuel.
  destruct n as [|p].
  - exact (proj1 (encode_unsigned_fuel_correct 0 1 0 ltac:(lia) ltac:(vm_compute; reflexivity))).
  - assert (Range : (Z.pos p < 128 ^ Z.of_nat (S (Pos.size_nat p)))%Z).
    {
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      pose proof (pos_size_nat_bound p).
      pose proof (Z.pow_pos_nonneg 128 (Z.of_nat (Pos.size_nat p))
        ltac:(lia) ltac:(lia)). lia.
    }
    exact (proj1 (encode_unsigned_fuel_correct (Pos.size_nat p)
      (S (Pos.size_nat p)) (N.pos p) ltac:(lia) Range)).
Qed.

Lemma encode_unsigned_fuel_length fuel n :
  length (encode_unsigned_fuel fuel n) <= fuel.
Proof.
  revert n. induction fuel as [|fuel IH]; intro n; simpl; [lia |].
  destruct (N.ltb n 128); simpl; [lia |].
  pose proof (IH (n / 128)%N). lia.
Qed.

Lemma encode_unsigned_length_bound k n :
  (Z.of_N n < 128 ^ Z.of_nat (S k))%Z ->
  length (encode_unsigned n) <= S k.
Proof.
  intro Range. unfold encode_unsigned.
  destruct (le_dec (unsigned_encoder_fuel n) (S k)) as [Short|Enough].
  - pose proof (encode_unsigned_fuel_length (unsigned_encoder_fuel n) n). lia.
  - apply (proj2 (encode_unsigned_fuel_correct k
      (unsigned_encoder_fuel n) n ltac:(lia) Range)).
Qed.

Theorem unsigned_encoder_parser_roundtrip n :
  @binary_format_parser.run option _ _ _ _ Byte.byte tokBytes N
    (encode_unsigned n) parse_unsigned = Some n.
Proof.
  apply (@run_parser_complete N parse_unsigned unsigned_leb).
  - exact parse_unsigned_complete.
  - apply encode_unsigned_sound.
Qed.
