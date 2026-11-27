(** Prefix soundness of the existing recursive LEB128 parsers.
    Integer-width restrictions are imposed by the actual format parser's
    guards, proved separately in [binary_format_parser_properties]. *)
From Stdlib Require Import ZArith List Lia.
From parseque Require Import Parseque.
From Wasm Require Import numerics leb128 binary_format_parser
  binary_parser_combinator_properties.

Inductive unsigned_leb : list Byte.byte -> N -> Prop :=
| uleb_end : forall b,
    (Byte.to_N b < 128)%N ->
    unsigned_leb (b :: nil) (Byte.to_N b)
| uleb_more : forall b bs n,
    (128 <= Byte.to_N b)%N ->
    unsigned_leb bs n ->
    unsigned_leb (b :: bs) ((Byte.to_N b - 128) + 128 * n)%N.

Inductive signed_leb : list Byte.byte -> Z -> Prop :=
| sleb_end_pos : forall b,
    (Byte.to_N b < 64)%N ->
    signed_leb (b :: nil) (Z.of_N (Byte.to_N b))
| sleb_end_neg : forall b,
    (64 <= Byte.to_N b < 128)%N ->
    signed_leb (b :: nil) (Z.of_N (Byte.to_N b) - 128)%Z
| sleb_more : forall b bs z,
    (128 <= Byte.to_N b)%N ->
    signed_leb bs z ->
    signed_leb (b :: bs) (Z.of_N (Byte.to_N b) - 128 + 128 * z)%Z.

Definition unsigned_continuation bs n :=
  exists b, bs = b :: nil /\ (128 <= Byte.to_N b)%N /\
    n = (Byte.to_N b - 128)%N.

Definition signed_continuation bs z :=
  exists b, bs = b :: nil /\ (128 <= Byte.to_N b)%N /\
    z = (Z.of_N (Byte.to_N b) - 128)%Z.

Lemma parse_unsigned_end_sound n :
  parser_sound (@parse_unsigned_end (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_leb.
Proof.
  unfold parse_unsigned_end.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b v E F. subst bs.
    destruct b; simpl in F; try discriminate; inversion F; subst;
      apply uleb_end; vm_compute; reflexivity.
Qed.

Lemma parse_unsigned_ctd_sound n :
  parser_sound (@parse_unsigned_ctd (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_continuation.
Proof.
  unfold parse_unsigned_ctd.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b v E F. subst bs.
    unfold unsigned_continuation. exists b. split; [reflexivity |].
    destruct b; simpl in F; try discriminate; inversion F; subst;
      split; vm_compute; congruence.
Qed.

Lemma parse_signed_end_sound n :
  parser_sound (@parse_signed_end (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_leb.
Proof.
  unfold parse_signed_end.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b v E F. subst bs.
    destruct b; simpl in F; try discriminate; inversion F; subst;
      first [apply sleb_end_pos; vm_compute; reflexivity |
             apply sleb_end_neg; vm_compute; split; congruence].
Qed.

Lemma parse_signed_ctd_sound n :
  parser_sound (@parse_signed_ctd (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_continuation.
Proof.
  unfold parse_signed_ctd.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b v E F. subst bs.
    unfold signed_continuation. exists b. split; [reflexivity |].
    destruct b; simpl in F; try discriminate; inversion F; subst;
      split; vm_compute; congruence.
Qed.

Definition unsigned_option (n : nat) :=
  @Unsigned (SizedList Byte.byte) option n.

Definition unsigned_option_step n (rec : Box unsigned_option n) :
    unsigned_option n :=
  MkUnsigned n
    (parse_unsigned_end <|>
      (((fun lsb rest => N.add lsb (N.mul 128 rest)) <$> parse_unsigned_ctd) <*>
        Induction.map _unsigned n rec)).

Lemma unsigned_option_step_sound n rec :
  (forall k (lt : k < n), parser_sound (_unsigned k (call rec lt)) unsigned_leb) ->
  parser_sound (_unsigned n (unsigned_option_step n rec)) unsigned_leb.
Proof.
  intro Rec. unfold unsigned_option_step; simpl.
  apply parser_sound_alt.
  - apply parse_unsigned_end_sound.
  - eapply parser_sound_app with
      (P := fun bs f => exists lsb,
        unsigned_continuation bs lsb /\
        f = (fun rest => N.add lsb (N.mul 128 rest)))
      (Q := unsigned_leb).
    + eapply parser_sound_map.
      * apply parse_unsigned_ctd_sound.
      * intros bs lsb H. exists lsb. auto.
    + intros k lt. simpl. apply Rec.
    + intros xs ys f rest [lsb [[b [E [B V]]] F]] Tail.
      subst xs lsb f. simpl.
      now apply uleb_more.
Qed.

Theorem parse_unsigned_sound n :
  parser_sound (@parse_unsigned (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_leb.
Proof.
  change (parser_sound
    (_unsigned n (Fix unsigned_option unsigned_option_step n)) unsigned_leb).
  apply (fix_invariant unsigned_option_step
    (fun k u => parser_sound (_unsigned k u) unsigned_leb)).
  exact unsigned_option_step_sound.
Qed.

Definition signed_option (n : nat) :=
  @Signed (SizedList Byte.byte) option n.

Definition signed_option_step n (rec : Box signed_option n) : signed_option n :=
  MkSigned n
    (parse_signed_end <|>
      (((fun lsb rest => Z.add lsb (Z.mul 128 rest)) <$> parse_signed_ctd) <*>
        Induction.map _signed n rec)).

Lemma signed_option_step_sound n rec :
  (forall k (lt : k < n), parser_sound (_signed k (call rec lt)) signed_leb) ->
  parser_sound (_signed n (signed_option_step n rec)) signed_leb.
Proof.
  intro Rec. unfold signed_option_step; simpl.
  apply parser_sound_alt.
  - apply parse_signed_end_sound.
  - eapply parser_sound_app with
      (P := fun bs f => exists lsb,
        signed_continuation bs lsb /\
        f = (fun rest => Z.add lsb (Z.mul 128 rest)))
      (Q := signed_leb).
    + eapply parser_sound_map.
      * apply parse_signed_ctd_sound.
      * intros bs lsb H. exists lsb. auto.
    + intros k lt. simpl. apply Rec.
    + intros xs ys f rest [lsb [[b [E [B V]]] F]] Tail.
      subst xs lsb f. simpl.
      now apply sleb_more.
Qed.

Theorem parse_signed_sound n :
  parser_sound (@parse_signed (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_leb.
Proof.
  change (parser_sound
    (_signed n (Fix signed_option signed_option_step n)) signed_leb).
  apply (fix_invariant signed_option_step
    (fun k s => parser_sound (_signed k s) signed_leb)).
  exact signed_option_step_sound.
Qed.

Theorem parse_s33_prefix_sound n :
  parser_sound (@parse_s33 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_leb.
Proof.
  unfold parse_s33.
  eapply parser_sound_guardM with (P := signed_leb).
  - apply parser_sound_assert_sized.
    apply parser_sound_extract. exact parse_signed_sound.
  - intros bs z v H E.
    destruct (andb (Z.leb (-4294967296) z) (Z.leb z 4294967295));
      [|discriminate].
    inversion E; subst. exact H.
Qed.

Theorem parse_u32_prefix_sound n :
  parser_sound (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_leb.
Proof.
  unfold parse_u32_as_N.
  eapply parser_sound_guardM with (P := unsigned_leb).
  - apply parser_sound_assert_sized.
    apply parser_sound_extract. exact parse_unsigned_sound.
  - intros bs z v H E.
    destruct (N.leb z 4294967295); [|discriminate].
    inversion E; subst. exact H.
Qed.

Theorem parse_u8_prefix_sound n :
  parser_sound (@parse_u8_as_N (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_leb.
Proof.
  unfold parse_u8_as_N.
  eapply parser_sound_guardM with (P := unsigned_leb).
  - apply parser_sound_assert_sized.
    apply parser_sound_extract. exact parse_unsigned_sound.
  - intros bs z v H E.
    destruct (N.leb z 255); [|discriminate].
    inversion E; subst. exact H.
Qed.

Theorem parse_s32_prefix_sound n :
  parser_sound (@parse_s32 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs v => signed_leb bs (Wasm_int.Int32.signed v)).
Proof.
  unfold parse_s32.
  eapply parser_sound_guardM with (P := signed_leb).
  - apply parser_sound_assert_sized.
    apply parser_sound_extract. exact parse_signed_sound.
  - intros bs z v H E.
    destruct (andb (Z.leb z 2147483647) (Z.leb (-2147483648) z)) eqn:B;
      [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Upper Lower].
    apply Z.leb_le in Upper. apply Z.leb_le in Lower.
    inversion E; subst.
    rewrite Wasm_int.Int32.signed_repr; [exact H |].
    change (-2147483648 <= z <= 2147483647)%Z. lia.
Qed.

Theorem parse_s64_prefix_sound n :
  parser_sound (@parse_s64 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs v => signed_leb bs (Wasm_int.Int64.signed v)).
Proof.
  unfold parse_s64.
  eapply parser_sound_guardM with (P := signed_leb).
  - apply parser_sound_assert_sized.
    apply parser_sound_extract. exact parse_signed_sound.
  - intros bs z v H E.
    destruct (andb (Z.leb z 9223372036854775807)
      (Z.leb (-9223372036854775808) z)) eqn:B; [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Upper Lower].
    apply Z.leb_le in Upper. apply Z.leb_le in Lower.
    inversion E; subst.
    rewrite Wasm_int.Int64.signed_repr; [exact H |].
    change (-9223372036854775808 <= z <= 9223372036854775807)%Z. lia.
Qed.

Theorem parse_heap_typeidx_prefix_sound n :
  parser_sound (@parse_heap_typeidx (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs x => signed_leb bs (Z.of_N x)).
Proof.
  unfold parse_heap_typeidx.
  eapply parser_sound_guardM with (P := signed_leb).
  - apply parse_s33_prefix_sound.
  - intros bs z x H E.
    destruct (Z.leb 0 z) eqn:Nonnegative; [|discriminate].
    apply Z.leb_le in Nonnegative.
    inversion E; subst. rewrite Z2N.id; assumption.
Qed.

(** This theorem connects the independent signed encoding relation to the
    decoder exported to OCaml, not to a separate replacement parser. *)
Theorem run_heap_typeidx_leb_sound bs x :
  run_parse_heap_typeidx bs = Some x -> signed_leb bs (Z.of_N x).
Proof.
  unfold run_parse_heap_typeidx.
  apply (@run_parser_sound N (fun _ => parse_heap_typeidx)
    (fun bytes idx => signed_leb bytes (Z.of_N idx))).
  exact parse_heap_typeidx_prefix_sound.
Qed.
