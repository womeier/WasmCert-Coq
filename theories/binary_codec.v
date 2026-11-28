(** Unsigned LEB128 grammar, bounded decoder and encoder. *)
From Stdlib Require Import List ZArith NArith Lia Strings.Byte Eqdep_dec.
From parseque Require Import Parseque.
Open Scope N_scope.

Definition leb_byte (n: N) : byte :=
  match Byte.of_N n with Some b => b | None => x00 end.

Lemma leb_byte_value : forall n, n < 256 -> Byte.to_N (leb_byte n) = n.
Proof.
  intros n Hn. unfold leb_byte.
  destruct (Byte.of_N n) eqn:Hbyte.
  - now apply Byte.to_of_N in Hbyte.
  - apply Byte.of_N_None_iff in Hbyte. lia.
Qed.

Section Parser.
Context {Toks: nat -> Type} `{Sized Toks byte}
  {M: Type -> Type} `{RawMonad M} `{RawAlternative M}.

(* Consume at most [fuel] bytes. The successful result carries the actual
   remaining stream, so this primitive fits the existing Parseque interface. *)
Fixpoint parse_uleb (fuel: nat) (n: nat) : Parser Toks byte M N n :=
  MkParser (fun m _ input =>
    match fuel with
    | O => Category.fail
    | S fuel' =>
      Category.bind (Category.fromOption (Success.getTok input)) (fun first =>
        let b := Success.value first in
        if Byte.to_N b <? 128 then
          Category.pure (Success.map Byte.to_N first)
        else
          Category.fmap
            (fun rest => Success.lt_lift (Success.small first)
              (Success.map (fun v => Byte.to_N b mod 128 + 128 * v) rest))
            (runParser (parse_uleb fuel' (Success.size first))
              (Nat.le_refl _) (Success.leftovers first)))
    end).
End Parser.

Section UintParser.
Context {Toks: nat -> Type} `{Sized Toks byte}
  {M: Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition parse_uint (bits: N) (fuel n: nat) : Parser Toks byte M N n :=
  Combinators.guardM (fun v => if v <? 2 ^ bits then Some v else None)
    (parse_uleb fuel n).
End UintParser.

Definition observe_prefix {A n}
  (result: option (Success.Success (SizedList byte) byte A n)) : option (A * list byte) :=
  option_map
    (fun s => (Success.value s,
      Sized.value (@List.length byte) _ (Success.leftovers s))) result.

Inductive unsigned_leb : list byte -> N -> Prop :=
| unsigned_leb_end : forall b,
    Byte.to_N b < 128 ->
    unsigned_leb (b :: nil) (Byte.to_N b)
| unsigned_leb_more : forall b bs n,
    128 <= Byte.to_N b ->
    unsigned_leb bs n ->
    unsigned_leb (b :: bs) (Byte.to_N b mod 128 + 128 * n).

Fixpoint decode_uleb (fuel: nat) (input: list byte) : option (N * list byte) :=
  match fuel, input with
  | S fuel', b :: rest =>
      if Byte.to_N b <? 128 then Some (Byte.to_N b, rest)
      else match decode_uleb fuel' rest with
           | Some (n, suffix) => Some (Byte.to_N b mod 128 + 128 * n, suffix)
           | None => None
           end
  | _, _ => None
  end.

Lemma sized_list_refl : forall input (H: List.length input = List.length input),
  @MkSizedType (list byte) (@List.length byte) (List.length input) input H =
    mkSizedList input.
Proof.
  intros input H. unfold mkSizedList. f_equal.
  apply UIP_dec. apply Nat.eq_dec.
Qed.

Lemma parse_uleb_correct : forall fuel n input
  (Hbound: (List.length input <= n)%nat),
  observe_prefix
    (runParser (parse_uleb fuel n) Hbound (mkSizedList input)) =
  decode_uleb fuel input.
Proof.
  induction fuel as [|fuel IH]; intros n input Hbound.
  - reflexivity.
  - destruct input as [|b input]; [reflexivity|].
    cbn -[Byte.to_N N.ltb N.modulo N.add N.mul].
    rewrite sized_list_refl.
    destruct (Byte.to_N b <? 128) eqn:Hb; [reflexivity|].
    rewrite <- (IH (List.length input) input (Nat.le_refl _)).
    unfold observe_prefix.
    destruct (runParser (parse_uleb fuel (List.length input))
      (Nat.le_refl _) (mkSizedList input)) as [s|]; reflexivity.
Qed.

Fixpoint encode_uleb (fuel: nat) (n: N) : list byte :=
  match fuel with
  | O => nil
  | S fuel' =>
      if n <? 128 then leb_byte n :: nil
      else leb_byte (128 + n mod 128) :: encode_uleb fuel' (n / 128)
  end.

Lemma decode_uleb_sound : forall fuel input n suffix,
  decode_uleb fuel input = Some (n, suffix) ->
  exists prefix,
    input = prefix ++ suffix /\
    (List.length prefix <= fuel)%nat /\
    unsigned_leb prefix n.
Proof.
  induction fuel as [|fuel IH]; intros input n suffix Hdecode; try discriminate.
  destruct input as [|b rest]; try discriminate.
  simpl in Hdecode.
  destruct (Byte.to_N b <? 128) eqn:Hb.
  - inversion Hdecode; subst.
    exists (b :: nil). split; [reflexivity|].
    split; [simpl; lia|]. constructor. now apply N.ltb_lt.
  - destruct (decode_uleb fuel rest) as [[v tail]|] eqn:Hrest; try discriminate.
    inversion Hdecode; subst.
    destruct (IH _ _ _ Hrest) as [prefix [-> [Hlen Hleb]]].
    exists (b :: prefix). split; [reflexivity|].
    split; [simpl; lia|].
    constructor; [now apply N.ltb_ge|assumption].
Qed.

Lemma decode_uleb_complete : forall prefix n,
  unsigned_leb prefix n ->
  forall fuel suffix, (List.length prefix <= fuel)%nat ->
    decode_uleb fuel (prefix ++ suffix) = Some (n, suffix).
Proof.
  intros prefix n Hleb. induction Hleb; intros [|fuel] suffix Hlen;
    simpl in Hlen; try lia.
  - simpl. apply N.ltb_lt in H. now rewrite H.
  - simpl. apply N.ltb_ge in H. rewrite H.
    rewrite IHHleb by lia. reflexivity.
Qed.

Lemma decode_uleb_iff : forall fuel input n suffix,
  decode_uleb fuel input = Some (n, suffix) <->
  exists prefix,
    input = prefix ++ suffix /\
    (List.length prefix <= fuel)%nat /\
    unsigned_leb prefix n.
Proof.
  split; [apply decode_uleb_sound|].
  intros [prefix [-> [Hlen Hleb]]].
  now apply decode_uleb_complete.
Qed.

Lemma encode_uleb_round_trip : forall fuel n suffix,
  (0 < fuel)%nat ->
  n < 128 ^ N.of_nat fuel ->
  decode_uleb fuel (encode_uleb fuel n ++ suffix) = Some (n, suffix).
Proof.
  induction fuel as [|fuel IH]; intros n suffix Hfuel Hbound; [lia|].
  change (decode_uleb (S fuel)
    ((if n <? 128 then leb_byte n :: nil
      else leb_byte (128 + n mod 128) :: encode_uleb fuel (n / 128)) ++ suffix)
    = Some (n, suffix)).
  destruct (n <? 128) eqn:Hsmall.
  - apply N.ltb_lt in Hsmall.
    cbn -[leb_byte N.add N.mul N.modulo N.div].
    rewrite leb_byte_value by lia.
    apply N.ltb_lt in Hsmall. now rewrite Hsmall.
  - apply N.ltb_ge in Hsmall.
    assert (Hmod: n mod 128 < 128) by (apply N.mod_lt; lia).
    cbn -[leb_byte N.add N.mul N.modulo N.div].
    rewrite leb_byte_value by lia.
    assert (Hcont: (128 + n mod 128 <? 128) = false)
      by (apply N.ltb_ge; apply N.le_add_r).
    rewrite Hcont.
    assert (Hpositive: (0 < fuel)%nat).
    { destruct fuel; simpl in Hbound; lia. }
    assert (Hquot: n / 128 < 128 ^ N.of_nat fuel).
    { rewrite Nat2N.inj_succ, N.pow_succ_r in Hbound by lia.
      apply N.div_lt_upper_bound; lia. }
    rewrite IH by assumption.
    rewrite N.add_mod by lia.
    rewrite N.mod_same by lia. rewrite N.add_0_l.
    repeat rewrite N.mod_mod by lia.
    pose proof (N.div_mod n 128 ltac:(lia)).
    f_equal. f_equal. lia.
Qed.

Definition decode_uint (bits: N) (fuel: nat) (input: list byte) :=
  match decode_uleb fuel input with
  | Some (v, suffix) =>
      if v <? 2 ^ bits then Some (v, suffix) else None
  | None => None
  end.

Lemma observe_guardM : forall A B n m
  (p: Parser (SizedList byte) byte option A n)
  (f: A -> option B) (Hbound: (m <= n)%nat) (input: SizedList byte m),
  observe_prefix (runParser (Combinators.guardM f p) Hbound input) =
  match observe_prefix (runParser p Hbound input) with
  | Some (a, rest) => option_map (fun b => (b, rest)) (f a)
  | None => None
  end.
Proof.
  intros A B n m p f Hbound input.
  unfold Combinators.guardM.
  cbn [runParser].
  destruct (runParser p Hbound input) as [s|]; [|reflexivity].
  unfold Category.bind, Category.fromOption, observe_prefix, Success.guardM.
  cbn.
  destruct (f (Success.value s)); reflexivity.
Qed.

Lemma parse_uint_correct : forall bits fuel n input
  (Hbound: (List.length input <= n)%nat),
  observe_prefix
    (runParser (parse_uint bits fuel n) Hbound (mkSizedList input)) =
  decode_uint bits fuel input.
Proof.
  intros bits fuel n input Hbound. unfold parse_uint.
  rewrite observe_guardM, parse_uleb_correct.
  unfold decode_uint.
  destruct (decode_uleb fuel input) as [[v rest]|]; [|reflexivity].
  destruct (v <? 2 ^ bits); reflexivity.
Qed.

Theorem parse_uint_spec : forall bits fuel n input v suffix
  (Hbound: (List.length input <= n)%nat),
  observe_prefix
    (runParser (parse_uint bits fuel n) Hbound (mkSizedList input)) =
    Some (v, suffix) <->
  exists prefix,
    input = prefix ++ suffix /\
    (List.length prefix <= fuel)%nat /\
    unsigned_leb prefix v /\ v < 2 ^ bits.
Proof.
  intros bits fuel n input v suffix Hbound.
  rewrite parse_uint_correct. unfold decode_uint. split.
  - destruct (decode_uleb fuel input) as [[x rest]|] eqn:Hdecode; try discriminate.
    destruct (x <? 2 ^ bits) eqn:Hrange; try discriminate.
    intros Heq. inversion Heq; subst.
    apply decode_uleb_sound in Hdecode.
    destruct Hdecode as [prefix [Hin [Hlen Hleb]]].
    exists prefix. repeat split; try assumption.
    now apply N.ltb_lt.
  - intros [prefix [Hin [Hlen [Hleb Hrange]]]].
    subst input. rewrite (decode_uleb_complete _ _ Hleb fuel suffix Hlen).
    apply N.ltb_lt in Hrange. now rewrite Hrange.
Qed.

Theorem parse_uint_encode_round_trip : forall bits fuel v suffix n
  (Hbound: (List.length (encode_uleb fuel v ++ suffix) <= n)%nat),
  (0 < fuel)%nat ->
  v < 128 ^ N.of_nat fuel ->
  v < 2 ^ bits ->
  observe_prefix (runParser (parse_uint bits fuel n) Hbound
    (mkSizedList (encode_uleb fuel v ++ suffix))) = Some (v, suffix).
Proof.
  intros bits fuel v suffix n Hbound Hfuel Hfits Hrange.
  rewrite parse_uint_correct. unfold decode_uint.
  rewrite encode_uleb_round_trip by assumption.
  apply N.ltb_lt in Hrange. now rewrite Hrange.
Qed.
