(** Prefix soundness of the existing recursive LEB128 parsers.
    Integer-width restrictions are imposed by the actual format parser's
    guards, proved separately in [binary_format_parser_properties]. *)
From Stdlib Require Import ZArith List Lia.
From parseque Require Import Parseque.
From Wasm Require Import numerics leb128 binary_format_parser
  binary_parser_combinator_properties.
From Wasm Require Import addressing addressing_binary addressing_parseque.

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

Lemma addressing_unsigned_leb_sound bs value :
  AddressingBinary.unsigned_leb bs value -> unsigned_leb bs value.
Proof. intro Encoded; induction Encoded; constructor; assumption. Qed.

Lemma addressing_unsigned_leb_complete bs value :
  unsigned_leb bs value -> AddressingBinary.unsigned_leb bs value.
Proof. intro Encoded; induction Encoded; constructor; assumption. Qed.

Theorem parse_u32_prefix_sound n :
  parser_sound (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n)
    unsigned_leb.
Proof.
  intros m bound input result Parsed.
  cbn [parse_u32_as_N AddressingParseque.parse_address runParser
    Category.fromOption] in Parsed.
  destruct (AddressingParseque.decode_address_tokens Addressing.AT_i32 input)
    as [decoded|] eqn:Decoded; cbn in Parsed; [|discriminate].
  inversion Parsed; subst decoded.
  pose proof (AddressingParseque.decode_address_tokens_correct_sized
    Addressing.AT_i32 m input) as Correspondence.
  unfold AddressingParseque.flatten in Correspondence.
  rewrite Decoded in Correspondence; cbn in Correspondence.
  symmetry in Correspondence.
  apply AddressingBinary.decode_address_spec in Correspondence.
  destruct Correspondence as [_ [prefix [Input [_ Encoded]]]].
  exists prefix; split; [exact Input|].
  now apply addressing_unsigned_leb_sound.
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

Definition unsigned_terminal bs n :=
  exists b, bs = b :: nil /\ (Byte.to_N b < 128)%N /\ n = Byte.to_N b.

Definition signed_terminal bs z :=
  exists b, bs = b :: nil /\
    (((Byte.to_N b < 64)%N /\ z = Z.of_N (Byte.to_N b)) \/
     ((64 <= Byte.to_N b < 128)%N /\
       z = (Z.of_N (Byte.to_N b) - 128)%Z)).

Definition unsigned_nonterminal bs n :=
  exists b tail rest,
    bs = b :: tail /\ (128 <= Byte.to_N b)%N /\
    unsigned_leb tail rest /\ n = ((Byte.to_N b - 128) + 128 * rest)%N.

Definition signed_nonterminal bs z :=
  exists b tail rest,
    bs = b :: tail /\ (128 <= Byte.to_N b)%N /\
    signed_leb tail rest /\
    z = (Z.of_N (Byte.to_N b) - 128 + 128 * rest)%Z.

Lemma parse_unsigned_end_terminal_sound n :
  parser_sound (@parse_unsigned_end (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_terminal.
Proof.
  unfold parse_unsigned_end.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b v E F. subst bs.
    exists b. split; [reflexivity |].
    destruct b; simpl in F; try discriminate; inversion F; subst;
      split; vm_compute; congruence.
Qed.

Lemma parse_signed_end_terminal_sound n :
  parser_sound (@parse_signed_end (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_terminal.
Proof.
  unfold parse_signed_end.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b v E F. subst bs.
    exists b. split; [reflexivity |].
    destruct b; simpl in F; try discriminate; inversion F; subst;
      first [left; split; vm_compute; congruence |
             right; split; [split; vm_compute; congruence | reflexivity]].
Qed.

Lemma parse_unsigned_end_complete n :
  parser_complete
    (@parse_unsigned_end (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_terminal.
Proof.
  unfold parse_unsigned_end.
  eapply parser_complete_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_complete_anyTok.
  - intros bs v [b [E [B V]]].
    exists b. split; [exact E |].
    subst v. destruct b; vm_compute in *; congruence.
Qed.

Lemma parse_unsigned_ctd_complete n :
  parser_complete
    (@parse_unsigned_ctd (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_continuation.
Proof.
  unfold parse_unsigned_ctd.
  eapply parser_complete_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_complete_anyTok.
  - intros bs v [b [E [B V]]].
    exists b. split; [exact E |].
    subst v. destruct b; vm_compute in *; congruence.
Qed.

Lemma parse_signed_end_complete n :
  parser_complete
    (@parse_signed_end (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_terminal.
Proof.
  unfold parse_signed_end.
  eapply parser_complete_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_complete_anyTok.
  - intros bs v [b [E [[B V]|[B V]]]];
      exists b; split; try exact E;
      subst v; destruct b; vm_compute in *; intuition congruence.
Qed.

Lemma parse_signed_ctd_complete n :
  parser_complete
    (@parse_signed_ctd (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_continuation.
Proof.
  unfold parse_signed_ctd.
  eapply parser_complete_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_complete_anyTok.
  - intros bs v [b [E [B V]]].
    exists b. split; [exact E |].
    subst v. destruct b; vm_compute in *; congruence.
Qed.

Lemma unsigned_option_step_complete n rec :
  (forall k (lt : k < n),
    parser_complete (_unsigned k (call rec lt)) unsigned_leb) ->
  parser_complete (_unsigned n (unsigned_option_step n rec)) unsigned_leb.
Proof.
  intro Rec.
  assert (Right : parser_complete
    (((fun lsb rest => N.add lsb (N.mul 128 rest)) <$> parse_unsigned_ctd) <*>
      Induction.map _unsigned n rec) unsigned_nonterminal).
  {
    eapply parser_complete_app with
      (P := fun bs f => exists lsb,
        unsigned_continuation bs lsb /\
        f = (fun rest => N.add lsb (N.mul 128 rest)))
      (Q := unsigned_leb).
    - eapply parser_complete_map.
      + apply parse_unsigned_ctd_complete.
      + intros bs f [lsb [H E]]. exists lsb. auto.
    - intros k lt. simpl. apply Rec.
    - intros bs v [b [tail [rest [E [B [Tail V]]]]]].
      exists (b :: nil), tail,
        (fun rest => N.add (Byte.to_N b - 128) (N.mul 128 rest)), rest.
      split; [exact E |]. split.
      + exists (Byte.to_N b - 128)%N. split; [|reflexivity].
        exists b. auto.
      + split; assumption.
  }
  intros m bound input prefix suffix a E P.
  inversion P as [b B|b tail rest B Tail]; subst.
  - eapply (parser_complete_alt_left _ _ _ (parse_unsigned_end_complete n));
      [exact E |].
    exists b. auto.
  - eapply (parser_complete_alt_right _ _ _ unsigned_nonterminal
      (parse_unsigned_end_terminal_sound n) Right).
    + intros xs ys t1 t2 x y [c [Ex [Low V]]]
        [d [ds [z [Ey [High Rest]]]]] Eq.
      subst xs ys. inversion Eq; subst d. lia.
    + exact E.
    + exists b, tail, rest. auto.
Qed.

Theorem parse_unsigned_complete n :
  parser_complete (@parse_unsigned (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    unsigned_leb.
Proof.
  change (parser_complete
    (_unsigned n (Fix unsigned_option unsigned_option_step n)) unsigned_leb).
  apply (fix_invariant unsigned_option_step
    (fun k u => parser_complete (_unsigned k u) unsigned_leb)).
  exact unsigned_option_step_complete.
Qed.

Lemma signed_option_step_complete n rec :
  (forall k (lt : k < n),
    parser_complete (_signed k (call rec lt)) signed_leb) ->
  parser_complete (_signed n (signed_option_step n rec)) signed_leb.
Proof.
  intro Rec.
  assert (Right : parser_complete
    (((fun lsb rest => Z.add lsb (Z.mul 128 rest)) <$> parse_signed_ctd) <*>
      Induction.map _signed n rec) signed_nonterminal).
  {
    eapply parser_complete_app with
      (P := fun bs f => exists lsb,
        signed_continuation bs lsb /\
        f = (fun rest => Z.add lsb (Z.mul 128 rest)))
      (Q := signed_leb).
    - eapply parser_complete_map.
      + apply parse_signed_ctd_complete.
      + intros bs f [lsb [H E]]. exists lsb. auto.
    - intros k lt. simpl. apply Rec.
    - intros bs v [b [tail [rest [E [B [Tail V]]]]]].
      exists (b :: nil), tail,
        (fun rest => Z.add (Z.of_N (Byte.to_N b) - 128) (Z.mul 128 rest)), rest.
      split; [exact E |]. split.
      + exists (Z.of_N (Byte.to_N b) - 128)%Z. split; [|reflexivity].
        exists b. auto.
      + split; assumption.
  }
  intros m bound input prefix suffix a E P.
  inversion P as [b B|b B|b tail rest B Tail]; subst.
  - eapply (parser_complete_alt_left _ _ _ (parse_signed_end_complete n));
      [exact E |].
    exists b. split; [reflexivity | left; auto].
  - eapply (parser_complete_alt_left _ _ _ (parse_signed_end_complete n));
      [exact E |].
    exists b. split; [reflexivity | right; auto].
  - eapply (parser_complete_alt_right _ _ _ signed_nonterminal
      (parse_signed_end_terminal_sound n) Right).
    + intros xs ys t1 t2 x y [c [Ex [[Low V]|[Low V]]]]
        [d [ds [z [Ey [High Rest]]]]] Eq;
        subst xs ys; inversion Eq; subst d; lia.
    + exact E.
    + exists b, tail, rest. auto.
Qed.

Theorem parse_signed_complete n :
  parser_complete (@parse_signed (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    signed_leb.
Proof.
  change (parser_complete
    (_signed n (Fix signed_option signed_option_step n)) signed_leb).
  apply (fix_invariant signed_option_step
    (fun k s => parser_complete (_signed k s) signed_leb)).
  exact signed_option_step_complete.
Qed.

Theorem parse_s33_prefix_complete n :
  parser_complete (@parse_s33 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs z => signed_leb bs z /\
      (-4294967296 <= z <= 4294967295)%Z /\ length bs <= 5).
Proof.
  unfold parse_s33.
  eapply parser_complete_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 5).
  - apply parser_complete_assert_sized.
    + eapply parser_complete_weaken.
      * apply parser_complete_extract. exact parse_signed_complete.
      * intros bs z [P _]. exact P.
    + intros bs z [_ L]. apply N.leb_le. lia.
  - intros bs z [P [Range L]].
    exists z. split; [auto |].
    assert (Lower : Z.leb (-4294967296) z = true) by (apply Z.leb_le; lia).
    assert (Upper : Z.leb z 4294967295 = true) by (apply Z.leb_le; lia).
    now rewrite Lower, Upper.
Qed.

Theorem parse_heap_typeidx_prefix_complete n :
  parser_complete
    (@parse_heap_typeidx (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs x => signed_leb bs (Z.of_N x) /\
      (x <= 4294967295)%N /\ length bs <= 5).
Proof.
  unfold parse_heap_typeidx.
  eapply parser_complete_guardM with
    (P := fun bs z => signed_leb bs z /\
      (-4294967296 <= z <= 4294967295)%Z /\ length bs <= 5).
  - apply parse_s33_prefix_complete.
  - intros bs x [P [Range L]].
    exists (Z.of_N x). split.
    + apply N2Z.inj_le in Range.
      pose proof (N2Z.is_nonneg x).
      repeat split; auto; lia.
    + assert (Nonnegative : Z.leb 0 (Z.of_N x) = true).
      { apply Z.leb_le. apply N2Z.is_nonneg. }
      now rewrite Nonnegative, N2Z.id.
Qed.

Theorem run_heap_typeidx_leb_complete bs x :
  signed_leb bs (Z.of_N x) ->
  (x <= 4294967295)%N ->
  length bs <= 5 ->
  run_parse_heap_typeidx bs = Some x.
Proof.
  intros Encoding Range Width.
  unfold run_parse_heap_typeidx.
  apply (@run_parser_complete N (fun _ => parse_heap_typeidx)
    (fun bytes idx => signed_leb bytes (Z.of_N idx) /\
      (idx <= 4294967295)%N /\ length bytes <= 5)).
  - exact parse_heap_typeidx_prefix_complete.
  - auto.
Qed.

Theorem run_heap_typeidx_leb_correct bs x :
  run_parse_heap_typeidx bs = Some x <->
  signed_leb bs (Z.of_N x) /\
    (x <= 4294967295)%N /\ length bs <= 5.
Proof.
  split.
  - intro R. split; [now apply run_heap_typeidx_leb_sound |].
    apply binary_format_parser_properties.run_heap_typeidx_guards in R.
    destruct R as [Range Width]. split; [exact Range | lia].
  - intros [Encoding [Range Width]].
    now apply run_heap_typeidx_leb_complete.
Qed.

Theorem parse_s32_prefix_complete n :
  parser_complete (@parse_s32 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs v => signed_leb bs (Wasm_int.Int32.signed v) /\ length bs <= 5).
Proof.
  unfold parse_s32.
  eapply parser_complete_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 5).
  - apply parser_complete_assert_sized.
    + eapply parser_complete_weaken.
      * apply parser_complete_extract. exact parse_signed_complete.
      * intros bs z [P _]. exact P.
    + intros bs z [_ L]. apply N.leb_le. lia.
  - intros bs v [P L].
    exists (Wasm_int.Int32.signed v). split; [auto |].
    pose proof (Wasm_int.Int32.signed_range v) as Range.
    change (-2147483648 <= Wasm_int.Int32.signed v <= 2147483647)%Z in Range.
    assert (Lower : Z.leb (-2147483648) (Wasm_int.Int32.signed v) = true)
      by (apply Z.leb_le; lia).
    assert (Upper : Z.leb (Wasm_int.Int32.signed v) 2147483647 = true)
      by (apply Z.leb_le; lia).
    rewrite Lower, Upper. simpl.
    now rewrite Wasm_int.Int32.repr_signed.
Qed.

Theorem parse_s64_prefix_complete n :
  parser_complete (@parse_s64 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs v => signed_leb bs (Wasm_int.Int64.signed v) /\ length bs <= 10).
Proof.
  unfold parse_s64.
  eapply parser_complete_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 10).
  - apply parser_complete_assert_sized.
    + eapply parser_complete_weaken.
      * apply parser_complete_extract. exact parse_signed_complete.
      * intros bs z [P _]. exact P.
    + intros bs z [_ L]. apply N.leb_le. lia.
  - intros bs v [P L].
    exists (Wasm_int.Int64.signed v). split; [auto |].
    pose proof (Wasm_int.Int64.signed_range v) as Range.
    change (-9223372036854775808 <= Wasm_int.Int64.signed v <=
      9223372036854775807)%Z in Range.
    assert (Lower : Z.leb (-9223372036854775808) (Wasm_int.Int64.signed v) = true)
      by (apply Z.leb_le; lia).
    assert (Upper : Z.leb (Wasm_int.Int64.signed v) 9223372036854775807 = true)
      by (apply Z.leb_le; lia).
    rewrite Lower, Upper. simpl.
    now rewrite Wasm_int.Int64.repr_signed.
Qed.

Theorem parse_u32_prefix_complete n :
  parser_complete (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n)
    (fun bs x => unsigned_leb bs x /\ (x <= 4294967295)%N /\ length bs <= 5).
Proof.
  intros m bound input prefix suffix x Input [Encoded [Range Length]].
  assert (Decoded : AddressingBinary.decode_address Addressing.AT_i32
      (input_bytes input) = Some (x, suffix)).
  { apply AddressingBinary.decode_address_spec.
    split.
    - change (x < 4294967296)%N. lia.
    - exists prefix. split; [exact Input|].
      split; [exact Length|].
      now apply addressing_unsigned_leb_complete. }
  pose proof (AddressingParseque.decode_address_tokens_correct_sized
    Addressing.AT_i32 m input) as Correspondence.
  unfold input_bytes in Decoded.
  rewrite Decoded in Correspondence.
  unfold AddressingParseque.flatten in Correspondence.
  destruct (AddressingParseque.decode_address_tokens Addressing.AT_i32 input)
    as [result|] eqn:Tokens; cbn in Correspondence; [|discriminate].
  exists result; split.
  - cbn [parse_u32_as_N AddressingParseque.parse_address runParser
      Category.fromOption]. now rewrite Tokens.
  - inversion Correspondence; auto.
Qed.
