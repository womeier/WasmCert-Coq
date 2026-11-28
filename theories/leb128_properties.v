(** Correspondence between the extracted option/Parseque LEB128 parsers and
    recursive byte decoders.  The decoders retain the unconsumed suffix. *)
From Wasm Require Import leb128.
From parseque Require Import Parseque.
From Stdlib Require Import Strings.Byte ZArith List Lia Arith.Peano_dec NArith.Nnat.

Local Open Scope list_scope.

Definition observe_leb {A n}
    (result : option (Success.Success (SizedList byte) byte A n)) :=
  option_map
    (fun s => (Success.value s, @Sized.value _ _ _ (Success.leftovers s)))
    result.

Lemma observe_leb_success {A n} result (v : A) rest :
  @observe_leb A n result = Some (v, rest) <->
  exists s, result = Some s /\
    Success.value s = v /\
    @Sized.value _ _ _ (Success.leftovers s) = rest.
Proof.
  destruct result as [s|]; simpl.
  - split.
    + intro E. inversion E. exists s. auto.
    + intros [t [E [V R]]]. inversion E; subst. reflexivity.
  - split; [discriminate | intros [s [E _]]; discriminate].
Qed.

Lemma observe_leb_app {A B m}
    (sa : Success.Success (SizedList byte) byte (A -> B) m)
    (result : option
      (Success.Success (SizedList byte) byte A (Success.size sa))) :
  observe_leb
    (option_map (Success.map snd)
      (option_map (Success.and sa)
        (option_map (Success.map (Success.value sa)) result))) =
  option_map (fun '(v, rest) => (Success.value sa v, rest))
    (observe_leb result).
Proof. destruct result; reflexivity. Qed.

Definition unsigned_terminal b : option N :=
  let '(_, (_, (_, (_, (_, (_, (_, more))))))) := Byte.to_bits b in
  if more then None else Some (Byte.to_N b).

Definition unsigned_continuation b : option N :=
  let '(_, (_, (_, (_, (_, (_, (_, more))))))) := Byte.to_bits b in
  if more then Some (Byte.to_N (make_msb_zero b)) else None.

Definition signed_terminal b : option Z :=
  let '(_, (_, (_, (_, (_, (_, (negative, more))))))) := Byte.to_bits b in
  if more then None
  else if negative then Some (sub_2_7 (Byte.to_N b))
       else Some (Z.of_N (Byte.to_N b)).

Definition signed_continuation b : option Z :=
  let '(_, (_, (_, (_, (_, (_, (_, more))))))) := Byte.to_bits b in
  if more then Some (sub_2_7 (Byte.to_N b)) else None.

Fixpoint read_unsigned (bs : list byte) : option (N * list byte) :=
  match bs with
  | nil => None
  | b :: bs =>
      match unsigned_terminal b with
      | Some v => Some (v, bs)
      | None =>
          match unsigned_continuation b with
          | Some lo =>
              option_map (fun '(hi, rest) => ((lo + 128 * hi)%N, rest))
                (read_unsigned bs)
          | None => None
          end
      end
  end.

Fixpoint read_signed (bs : list byte) : option (Z * list byte) :=
  match bs with
  | nil => None
  | b :: bs =>
      match signed_terminal b with
      | Some v => Some (v, bs)
      | None =>
          match signed_continuation b with
          | Some lo =>
              option_map (fun '(hi, rest) => ((lo + 128 * hi)%Z, rest))
                (read_signed bs)
          | None => None
          end
      end
  end.

Definition unsigned_fuel fuel n (below : n < fuel) :
    Parser (SizedList byte) byte option N n :=
  _unsigned n
    (call (@FixBox (@Unsigned (SizedList byte) option) unsigned_step fuel) below).

Lemma unsigned_fuel_correct fuel :
  forall n (below : n < fuel) bs (bound : List.length bs <= n),
    observe_leb
      (runParser (unsigned_fuel fuel n below) bound (mkSizedList bs)) =
    read_unsigned bs.
Proof.
  induction fuel as [|fuel IH]; intros n below bs bound; [lia |].
  destruct bs as [|b bs].
  - reflexivity.
  - cbn [unsigned_fuel FixBox call unsigned_step _unsigned
      parse_unsigned_end parse_unsigned_ctd].
    cbn [runParser observe_leb parse_unsigned_end parse_unsigned_ctd
      Combinators.alt Combinators.app Combinators.bind
      Combinators.map Combinators.andbind Combinators.guardM Combinators.anyTok
      Category.alt Category.bind Category.fmap Category.fromOption
      Success.getTok Success.fromView].
    simpl.
    unfold Success.guardM, unsigned_terminal, unsigned_continuation.
    simpl.
    destruct (Byte.to_bits b) as [b1 [b2 [b3 [b4 [b5 [b6 [b7 more]]]]]]].
    destruct more; simpl; [|reflexivity].
    assert (Eta : forall p : List.length bs = List.length bs,
      @Sized.MkSizedType (list byte) (@List.length byte) (List.length bs) bs p =
      mkSizedList bs).
    { intro p. unfold mkSizedList. f_equal. apply UIP_nat. }
    rewrite !Eta.
    match goal with
    | |- context [call (FixBox unsigned_step fuel) ?below'] =>
        pose proof (IH _ below' bs (Nat.le_refl _)) as R
    end.
    unfold unsigned_fuel in R.
    rewrite <- R.
    match goal with
    | |- context [runParser ?p ?bound' ?input] =>
        destruct (runParser p bound' input); reflexivity
    end.
Qed.

Theorem parse_unsigned_correct n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (@parse_unsigned (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) = read_unsigned bs.
Proof.
  change (observe_leb
    (runParser (unsigned_fuel (S n) n (le_n _))
      bound (mkSizedList bs)) = read_unsigned bs).
  apply unsigned_fuel_correct.
Qed.

Theorem extract_unsigned_correct n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (extract (@parse_unsigned (SizedList byte) _ option _ _ _ _ _ _) n)
      bound (mkSizedList bs)) = read_unsigned bs.
Proof.
  unfold extract, box, le_close, Combinators.le_lower.
  cbn [call runParser]. apply parse_unsigned_correct.
Qed.

Definition signed_fuel fuel n (below : n < fuel) :
    Parser (SizedList byte) byte option Z n :=
  _signed n
    (call (@FixBox (@Signed (SizedList byte) option) signed_step fuel) below).

Lemma signed_fuel_correct fuel :
  forall n (below : n < fuel) bs (bound : List.length bs <= n),
    observe_leb
      (runParser (signed_fuel fuel n below) bound (mkSizedList bs)) =
    read_signed bs.
Proof.
  induction fuel as [|fuel IH]; intros n below bs bound; [lia |].
  destruct bs as [|b bs].
  - reflexivity.
  - cbn [signed_fuel FixBox call signed_step _signed].
    cbn [runParser observe_leb parse_signed_end parse_signed_ctd
      Combinators.alt Combinators.app Combinators.bind
      Combinators.map Combinators.andbind Combinators.guardM Combinators.anyTok
      Category.alt Category.bind Category.fmap Category.fromOption
      Success.getTok Success.fromView].
    simpl.
    unfold Success.guardM, signed_terminal, signed_continuation.
    simpl.
    destruct (Byte.to_bits b) as [b1 [b2 [b3 [b4 [b5 [b6 [negative more]]]]]]].
    destruct more; simpl; [|destruct negative; reflexivity].
    assert (Eta : forall p : List.length bs = List.length bs,
      @Sized.MkSizedType (list byte) (@List.length byte) (List.length bs) bs p =
      mkSizedList bs).
    { intro p. unfold mkSizedList. f_equal. apply UIP_nat. }
    rewrite !Eta.
    match goal with
    | |- context [call (FixBox signed_step fuel) ?below'] =>
        pose proof (IH _ below' bs (Nat.le_refl _)) as R
    end.
    unfold signed_fuel in R.
    rewrite <- R.
    match goal with
    | |- context [runParser ?p ?bound' ?input] =>
        destruct (runParser p bound' input); reflexivity
    end.
Qed.

Theorem parse_signed_correct n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (@parse_signed (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) = read_signed bs.
Proof.
  change (observe_leb
    (runParser (signed_fuel (S n) n (le_n _))
      bound (mkSizedList bs)) = read_signed bs).
  apply signed_fuel_correct.
Qed.

Theorem extract_signed_correct n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (extract (@parse_signed (SizedList byte) _ option _ _ _ _ _ _) n)
      bound (mkSizedList bs)) = read_signed bs.
Proof.
  unfold extract, box, le_close, Combinators.le_lower.
  cbn [call runParser]. apply parse_signed_correct.
Qed.

(** The byte grammar deliberately permits padding: it describes all encodings
    accepted by the recursive parser, not just the printer's encodings. *)
Inductive unsigned_encoding : N -> list byte -> Prop :=
| unsigned_encoding_end b v :
    unsigned_terminal b = Some v ->
    unsigned_encoding v (b :: nil)
| unsigned_encoding_more b lo hi tail :
    unsigned_terminal b = None ->
    unsigned_continuation b = Some lo ->
    unsigned_encoding hi tail ->
    unsigned_encoding (lo + 128 * hi)%N (b :: tail).

Inductive signed_encoding : Z -> list byte -> Prop :=
| signed_encoding_end b v :
    signed_terminal b = Some v ->
    signed_encoding v (b :: nil)
| signed_encoding_more b lo hi tail :
    signed_terminal b = None ->
    signed_continuation b = Some lo ->
    signed_encoding hi tail ->
    signed_encoding (lo + 128 * hi)%Z (b :: tail).

Lemma read_unsigned_complete v prefix :
  unsigned_encoding v prefix ->
  forall rest, read_unsigned (prefix ++ rest) = Some (v, rest).
Proof.
  intro H. induction H; intro rest; simpl.
  - now rewrite H.
  - now rewrite H, H0, IHunsigned_encoding.
Qed.

Lemma read_unsigned_sound bs v rest :
  read_unsigned bs = Some (v, rest) ->
  exists prefix, bs = prefix ++ rest /\ unsigned_encoding v prefix.
Proof.
  revert v rest. induction bs as [|b bs IH]; intros v rest R;
    [discriminate |].
  simpl in R.
  destruct (unsigned_terminal b) as [lo|] eqn:T.
  - inversion R; subst. exists (b :: nil). split; [reflexivity |].
    now constructor.
  - destruct (unsigned_continuation b) as [lo|] eqn:C; [|discriminate].
    destruct (read_unsigned bs) as [[hi suffix]|] eqn:S; [|discriminate].
    inversion R; subst.
    destruct (IH _ _ eq_refl) as [prefix [B E]].
    exists (b :: prefix). split; [simpl; now rewrite B |].
    now apply unsigned_encoding_more.
Qed.

Theorem read_unsigned_grammar bs v rest :
  read_unsigned bs = Some (v, rest) <->
  exists prefix, bs = prefix ++ rest /\ unsigned_encoding v prefix.
Proof.
  split; [apply read_unsigned_sound |].
  intros [prefix [-> E]]. now apply read_unsigned_complete.
Qed.

Lemma read_signed_complete v prefix :
  signed_encoding v prefix ->
  forall rest, read_signed (prefix ++ rest) = Some (v, rest).
Proof.
  intro H. induction H; intro rest; simpl.
  - now rewrite H.
  - now rewrite H, H0, IHsigned_encoding.
Qed.

Lemma read_signed_sound bs v rest :
  read_signed bs = Some (v, rest) ->
  exists prefix, bs = prefix ++ rest /\ signed_encoding v prefix.
Proof.
  revert v rest. induction bs as [|b bs IH]; intros v rest R;
    [discriminate |].
  simpl in R.
  destruct (signed_terminal b) as [lo|] eqn:T.
  - inversion R; subst. exists (b :: nil). split; [reflexivity |].
    now constructor.
  - destruct (signed_continuation b) as [lo|] eqn:C; [|discriminate].
    destruct (read_signed bs) as [[hi suffix]|] eqn:S; [|discriminate].
    inversion R; subst.
    destruct (IH _ _ eq_refl) as [prefix [B E]].
    exists (b :: prefix). split; [simpl; now rewrite B |].
    now apply signed_encoding_more.
Qed.

Theorem read_signed_grammar bs v rest :
  read_signed bs = Some (v, rest) <->
  exists prefix, bs = prefix ++ rest /\ signed_encoding v prefix.
Proof.
  split; [apply read_signed_sound |].
  intros [prefix [-> E]]. now apply read_signed_complete.
Qed.

Theorem parse_unsigned_grammar n bs (bound : List.length bs <= n) v rest :
  observe_leb
    (runParser
      (@parse_unsigned (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) = Some (v, rest) <->
  exists prefix, bs = prefix ++ rest /\ unsigned_encoding v prefix.
Proof. rewrite parse_unsigned_correct. apply read_unsigned_grammar. Qed.

Theorem parse_signed_grammar n bs (bound : List.length bs <= n) v rest :
  observe_leb
    (runParser
      (@parse_signed (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) = Some (v, rest) <->
  exists prefix, bs = prefix ++ rest /\ signed_encoding v prefix.
Proof. rewrite parse_signed_correct. apply read_signed_grammar. Qed.

Lemma payload_byte_unsigned n :
  unsigned_terminal (payload_byte n) = Some (n mod 128)%N /\
  unsigned_terminal (make_msb_one (payload_byte n)) = None /\
  unsigned_continuation (make_msb_one (payload_byte n)) =
    Some (n mod 128)%N.
Proof.
  pose proof (N.mod_lt n 128 ltac:(discriminate)) as Range.
  unfold payload_byte.
  destruct (Byte.of_N (n mod 128)) as [b|] eqn:B.
  - apply Byte.to_of_N in B. rewrite <- B in Range |- *.
    destruct b; vm_compute in Range |- *; try discriminate;
      repeat split; reflexivity.
  - apply Byte.of_N_None_iff in B. lia.
Qed.

Lemma write_unsigned_encoding fuel n :
  (n < 128 ^ N.of_nat (S fuel))%N ->
  unsigned_encoding n (write_unsigned fuel n) /\
  List.length (write_unsigned fuel n) <= S fuel.
Proof.
  revert n. induction fuel as [|fuel IH]; intros n Bound.
  - change (n < 128)%N in Bound.
    split; [|reflexivity].
    apply unsigned_encoding_end.
    rewrite (proj1 (payload_byte_unsigned n)).
    now rewrite N.mod_small.
  - cbn [write_unsigned].
    destruct (N.ltb n 128) eqn:Small.
    + apply N.ltb_lt in Small.
      split; [|simpl; lia].
      apply unsigned_encoding_end.
      rewrite (proj1 (payload_byte_unsigned n)).
      now rewrite N.mod_small.
    + assert (Quotient : (n / 128 < 128 ^ N.of_nat (S fuel))%N).
      { apply N.Div0.div_lt_upper_bound.
        now rewrite Nat2N.inj_succ, N.pow_succ_r' in Bound. }
      destruct (IH _ Quotient) as [Encoding Length].
      split; [|simpl; lia].
      replace n with (n mod 128 + 128 * (n / 128))%N at 1
        by (pose proof (N.div_mod n 128 ltac:(discriminate)); lia).
      apply unsigned_encoding_more.
      * exact (proj1 (proj2 (payload_byte_unsigned n))).
      * exact (proj2 (proj2 (payload_byte_unsigned n))).
      * exact Encoding.
Qed.

Theorem encode_unsigned_encoding n :
  unsigned_encoding n (encode_unsigned n).
Proof.
  unfold encode_unsigned.
  apply write_unsigned_encoding.
  rewrite Nat2N.inj_succ, N2Nat.id.
  pose proof (N.size_gt n).
  pose proof (N.pow_le_mono_l 2 128 (N.size n) ltac:(lia)).
  pose proof (N.pow_le_mono_r 128 (N.size n) (N.succ (N.size n))
    ltac:(discriminate) ltac:(lia)).
  lia.
Qed.

Theorem read_encode_unsigned n rest :
  read_unsigned (encode_unsigned n ++ rest) = Some (n, rest).
Proof. apply read_unsigned_complete. apply encode_unsigned_encoding. Qed.

Theorem parse_encode_unsigned n rest bound_index
    (bound : List.length (encode_unsigned n ++ rest) <= bound_index) :
  observe_leb
    (runParser
      (@parse_unsigned (SizedList byte) _ option _ _ _ _ _ _ bound_index)
      bound (mkSizedList (encode_unsigned n ++ rest))) = Some (n, rest).
Proof. rewrite parse_unsigned_correct. apply read_encode_unsigned. Qed.

Lemma payload_byte_signed n :
  signed_terminal (payload_byte n) =
    Some (if N.ltb (n mod 128) 64 then Z.of_N (n mod 128)
          else Z.of_N (n mod 128) - 128)%Z /\
  signed_terminal (make_msb_one (payload_byte n)) = None /\
  signed_continuation (make_msb_one (payload_byte n)) =
    Some (Z.of_N (n mod 128)).
Proof.
  pose proof (N.mod_lt n 128 ltac:(discriminate)) as Range.
  unfold payload_byte.
  destruct (Byte.of_N (n mod 128)) as [b|] eqn:B.
  - apply Byte.to_of_N in B. rewrite <- B in Range |- *.
    destruct b; vm_compute in Range |- *; try discriminate;
      repeat split; reflexivity.
  - apply Byte.of_N_None_iff in B. lia.
Qed.

Lemma signed_payload_remainder z :
  (Z.to_N (z mod 128) mod 128)%N = Z.to_N (z mod 128) /\
  Z.of_N (Z.to_N (z mod 128)) = (z mod 128)%Z.
Proof.
  pose proof (Z.mod_pos_bound z 128 ltac:(lia)) as Range.
  split.
  - apply N.mod_small. apply N2Z.inj_lt.
    rewrite Z2N.id by lia. exact (proj2 Range).
  - apply Z2N.id. lia.
Qed.

Lemma signed_terminal_payload z :
  (-64 <= z < 64)%Z ->
  signed_terminal (payload_byte (Z.to_N (z mod 128))) = Some z.
Proof.
  intro Range. rewrite (proj1 (payload_byte_signed _)).
  rewrite (proj1 (signed_payload_remainder z)).
  destruct (Z.ltb z 0) eqn:Negative.
  - apply Z.ltb_lt in Negative.
    assert (M : (z mod 128 = z + 128)%Z).
    { symmetry. apply (Z.mod_unique z 128 (-1)); [left; lia | lia]. }
    rewrite M.
    assert (B : (Z.to_N (z + 128) <? 64)%N = false).
    { apply N.ltb_ge. apply N2Z.inj_le. rewrite Z2N.id by lia. lia. }
    rewrite B, Z2N.id by lia. f_equal. lia.
  - apply Z.ltb_ge in Negative.
    rewrite Z.mod_small by lia.
    assert (B : (Z.to_N z <? 64)%N = true).
    { apply N.ltb_lt. apply N2Z.inj_lt. rewrite Z2N.id by lia. lia. }
    now rewrite B, Z2N.id by lia.
Qed.

Lemma write_signed_encoding fuel z :
  (-64 * Z.of_N (128 ^ N.of_nat fuel) <= z <
    64 * Z.of_N (128 ^ N.of_nat fuel))%Z ->
  signed_encoding z (write_signed fuel z) /\
  List.length (write_signed fuel z) <= S fuel.
Proof.
  revert z. induction fuel as [|fuel IH]; intros z Bound.
  - change (-64 <= z < 64)%Z in Bound.
    split; [|reflexivity].
    apply signed_encoding_end. now apply signed_terminal_payload.
  - cbn [write_signed].
    destruct (andb (Z.leb (-64) z) (Z.ltb z 64)) eqn:Small.
    + apply Bool.andb_true_iff in Small.
      destruct Small as [Lower Upper].
      apply Z.leb_le in Lower. apply Z.ltb_lt in Upper.
      split; [|simpl; lia].
      apply signed_encoding_end. apply signed_terminal_payload. lia.
    + assert (Quotient :
        (-64 * Z.of_N (128 ^ N.of_nat fuel) <= z / 128 <
          64 * Z.of_N (128 ^ N.of_nat fuel))%Z).
      { rewrite Nat2N.inj_succ, N.pow_succ_r', N2Z.inj_mul in Bound.
        split.
        - apply Z.div_le_lower_bound; lia.
        - apply Z.div_lt_upper_bound; lia. }
      destruct (IH _ Quotient) as [Encoding Length].
      split; [|simpl; lia].
      replace z with (z mod 128 + 128 * (z / 128))%Z at 1
        by (pose proof (Z.div_mod z 128 ltac:(lia)); lia).
      apply signed_encoding_more.
      * exact (proj1 (proj2 (payload_byte_signed _))).
      * rewrite (proj2 (proj2 (payload_byte_signed _))).
        rewrite (proj1 (signed_payload_remainder z)).
        now rewrite (proj2 (signed_payload_remainder z)).
      * exact Encoding.
Qed.

Theorem encode_signed_encoding z :
  signed_encoding z (encode_signed z).
Proof.
  unfold encode_signed.
  apply write_signed_encoding.
  rewrite N2Nat.id.
  set (m := Z.to_N (Z.abs z)).
  assert (Magnitude :
    (Z.abs z < Z.of_N (128 ^ N.size m))%Z).
  { pose proof (N.size_gt m).
    pose proof (N.pow_le_mono_l 2 128 (N.size m) ltac:(lia)).
    assert (B : (m < 128 ^ N.size m)%N) by lia.
    apply N2Z.inj_lt in B.
    unfold m in B. now rewrite Z2N.id in B by apply Z.abs_nonneg. }
  destruct (Z.abs_spec z) as [[Sign Abs] | [Sign Abs]]; rewrite Abs in Magnitude;
    nia.
Qed.

Theorem read_encode_signed z rest :
  read_signed (encode_signed z ++ rest) = Some (z, rest).
Proof. apply read_signed_complete. apply encode_signed_encoding. Qed.

Theorem parse_encode_signed z rest bound_index
    (bound : List.length (encode_signed z ++ rest) <= bound_index) :
  observe_leb
    (runParser
      (@parse_signed (SizedList byte) _ option _ _ _ _ _ _ bound_index)
      bound (mkSizedList (encode_signed z ++ rest))) = Some (z, rest).
Proof. rewrite parse_signed_correct. apply read_encode_signed. Qed.

Lemma write_unsigned_length_bound groups fuel n :
  (n < 128 ^ N.of_nat (S groups))%N ->
  List.length (write_unsigned fuel n) <= S groups.
Proof.
  revert fuel n. induction groups as [|groups IH]; intros fuel n Bound.
  - change (n < 128)%N in Bound.
    destruct fuel; cbn [write_unsigned]; [reflexivity |].
    rewrite (proj2 (N.ltb_lt _ _) Bound). reflexivity.
  - destruct fuel as [|fuel]; cbn [write_unsigned]; [simpl; lia |].
    destruct (N.ltb n 128); [simpl; lia |].
    simpl. apply le_n_S. apply IH.
    apply N.Div0.div_lt_upper_bound.
    now rewrite Nat2N.inj_succ, N.pow_succ_r' in Bound.
Qed.

Lemma write_signed_length_bound groups fuel z :
  (-64 * Z.of_N (128 ^ N.of_nat groups) <= z <
    64 * Z.of_N (128 ^ N.of_nat groups))%Z ->
  List.length (write_signed fuel z) <= S groups.
Proof.
  revert fuel z. induction groups as [|groups IH]; intros fuel z Bound.
  - change (-64 <= z < 64)%Z in Bound.
    destruct fuel; cbn [write_signed]; [reflexivity |].
    assert (Small : andb (Z.leb (-64) z) (Z.ltb z 64) = true).
    { apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    now rewrite Small.
  - destruct fuel as [|fuel]; cbn [write_signed]; [simpl; lia |].
    destruct (andb (Z.leb (-64) z) (Z.ltb z 64)); [simpl; lia |].
    simpl. apply le_n_S. apply IH.
    rewrite Nat2N.inj_succ, N.pow_succ_r', N2Z.inj_mul in Bound.
    split.
    + apply Z.div_le_lower_bound; lia.
    + apply Z.div_lt_upper_bound; lia.
Qed.

Lemma encode_u32_length n :
  (n <= 4294967295)%N -> List.length (encode_unsigned n) <= 5.
Proof.
  intro Range. unfold encode_unsigned.
  apply (write_unsigned_length_bound 4).
  change (n < 34359738368)%N. lia.
Qed.

Lemma encode_s32_length z :
  (-2147483648 <= z <= 2147483647)%Z ->
  List.length (encode_signed z) <= 5.
Proof.
  intro Range. unfold encode_signed.
  apply (write_signed_length_bound 4).
  change (-17179869184 <= z < 17179869184)%Z. lia.
Qed.

Lemma encode_s33_length z :
  (-4294967296 <= z <= 4294967295)%Z ->
  List.length (encode_signed z) <= 5.
Proof.
  intro Range. unfold encode_signed.
  apply (write_signed_length_bound 4).
  change (-17179869184 <= z < 17179869184)%Z. lia.
Qed.

Lemma encode_s64_length z :
  (-9223372036854775808 <= z <= 9223372036854775807)%Z ->
  List.length (encode_signed z) <= 10.
Proof.
  intro Range. unfold encode_signed.
  apply (write_signed_length_bound 9).
  change (-590295810358705651712 <= z < 590295810358705651712)%Z. lia.
Qed.

Lemma unsigned_terminal_bound b v :
  unsigned_terminal b = Some v -> (v < 128)%N.
Proof.
  destruct b; intro E; vm_compute in E; try discriminate;
    inversion E; subst; vm_compute; reflexivity.
Qed.

Lemma unsigned_continuation_bound b v :
  unsigned_continuation b = Some v -> (v < 128)%N.
Proof.
  destruct b; intro E; vm_compute in E; try discriminate;
    inversion E; subst; vm_compute; reflexivity.
Qed.

Lemma signed_terminal_bound b v :
  signed_terminal b = Some v -> (-64 <= v < 64)%Z.
Proof.
  destruct b; intro E; vm_compute in E; try discriminate;
    inversion E; subst; vm_compute; split; congruence.
Qed.

Lemma signed_continuation_bound b v :
  signed_continuation b = Some v -> (0 <= v < 128)%Z.
Proof.
  destruct b; intro E; vm_compute in E; try discriminate;
    inversion E; subst; vm_compute; split; congruence.
Qed.

Lemma unsigned_encoding_bound v prefix :
  unsigned_encoding v prefix ->
  (v < 128 ^ N.of_nat (List.length prefix))%N.
Proof.
  intro E. induction E.
  - change (v < 128)%N. now apply unsigned_terminal_bound in H.
  - change (lo + 128 * hi < 128 ^ N.of_nat (S (List.length tail)))%N.
    rewrite Nat2N.inj_succ, N.pow_succ_r'.
    apply unsigned_continuation_bound in H0. nia.
Qed.

Lemma signed_encoding_bound v prefix :
  signed_encoding v prefix ->
  prefix <> nil /\
  (-64 * Z.of_N (128 ^ N.of_nat (Nat.pred (List.length prefix))) <= v <
    64 * Z.of_N (128 ^ N.of_nat (Nat.pred (List.length prefix))))%Z.
Proof.
  intro E. induction E as [b v End | b lo hi tail End Cont Enc IH].
  - split; [discriminate |].
    change (-64 <= v < 64)%Z. now apply signed_terminal_bound in End.
  - split; [discriminate |].
    destruct IH as [Nonempty Bound].
    destruct tail as [|head tail]; [contradiction |].
    change
      (-64 * Z.of_N (128 ^ N.of_nat (List.length tail)) <= hi <
        64 * Z.of_N (128 ^ N.of_nat (List.length tail)))%Z in Bound.
    change
      (-64 * Z.of_N (128 ^ N.of_nat (S (List.length tail))) <= lo + 128 * hi <
        64 * Z.of_N (128 ^ N.of_nat (S (List.length tail))))%Z.
    rewrite Nat2N.inj_succ, N.pow_succ_r', N2Z.inj_mul.
    apply signed_continuation_bound in Cont. nia.
Qed.

Theorem encode_unsigned_no_longer v prefix :
  unsigned_encoding v prefix ->
  List.length (encode_unsigned v) <= List.length prefix.
Proof.
  intro E. destruct prefix as [|b prefix]; [inversion E |].
  unfold encode_unsigned.
  apply (write_unsigned_length_bound (List.length prefix)).
  exact (unsigned_encoding_bound _ _ E).
Qed.

Theorem encode_signed_no_longer v prefix :
  signed_encoding v prefix ->
  List.length (encode_signed v) <= List.length prefix.
Proof.
  intro E. destruct prefix as [|b prefix]; [inversion E |].
  unfold encode_signed.
  apply (write_signed_length_bound (List.length prefix)).
  exact (proj2 (signed_encoding_bound _ _ E)).
Qed.

Corollary read_unsigned_print_size bs v rest :
  read_unsigned bs = Some (v, rest) ->
  List.length (encode_unsigned v) <= List.length bs - List.length rest.
Proof.
  intro R. apply read_unsigned_sound in R.
  destruct R as [prefix [-> E]].
  rewrite List.length_app, Nat.add_sub. now apply encode_unsigned_no_longer.
Qed.

Corollary read_signed_print_size bs v rest :
  read_signed bs = Some (v, rest) ->
  List.length (encode_signed v) <= List.length bs - List.length rest.
Proof.
  intro R. apply read_signed_sound in R.
  destruct R as [prefix [-> E]].
  rewrite List.length_app, Nat.add_sub. now apply encode_signed_no_longer.
Qed.
