(** Bounded unsigned LEB128 decoding.
    Unlike the legacy unbounded decoder, this reader stops after five bytes.
    Its declarative relation permits non-canonical padding and explicitly
    records the unconsumed suffix. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque Success.

Open Scope N_scope.

Inductive uleb_prefix : nat -> list byte -> N -> list byte -> Prop :=
| uleb_last : forall fuel b rest,
    (Byte.to_N b < 128)%N ->
    uleb_prefix (S fuel) (b :: rest) (Byte.to_N b) rest
| uleb_more : forall fuel b input value rest,
    (128 <= Byte.to_N b)%N ->
    uleb_prefix fuel input value rest ->
    uleb_prefix (S fuel) (b :: input)
      (Byte.to_N b - 128 + 128 * value) rest.

Fixpoint decode_uleb (fuel : nat) (input : list byte) :
    option (N * list byte) :=
  match fuel, input with
  | O, _ | _, nil => None
  | S fuel', b :: rest =>
      if N.ltb (Byte.to_N b) 128 then Some (Byte.to_N b, rest)
      else option_map
        (fun '(value, suffix) =>
          (Byte.to_N b - 128 + 128 * value, suffix))
        (decode_uleb fuel' rest)
  end.

Lemma decode_uleb_correct : forall fuel input value rest,
    decode_uleb fuel input = Some (value, rest) <->
    uleb_prefix fuel input value rest.
Proof.
  induction fuel as [|fuel IH]; intros input value rest.
  - split; [discriminate | intro H; inversion H].
  - destruct input as [|b input].
    + split; [discriminate | intro H; inversion H].
    + cbn [decode_uleb].
      destruct (N.ltb (Byte.to_N b) 128) eqn:Hb.
      * apply N.ltb_lt in Hb.
        split.
        -- intro H; inversion H; subst. constructor; assumption.
        -- intro H; inversion H; subst; [reflexivity | lia].
      * apply N.ltb_ge in Hb.
        split.
        -- destruct (decode_uleb fuel input) as [[v suffix]|] eqn:Hr;
             cbn; try discriminate.
           intro H; inversion H; subst.
           constructor; [assumption | apply IH; assumption].
        -- intro H; inversion H; subst; [lia |].
           match goal with
           | Hprefix : uleb_prefix fuel input _ _ |- _ =>
               apply IH in Hprefix; rewrite Hprefix; reflexivity
           end.
Qed.

Lemma uleb_prefix_consumed : forall fuel input value rest,
    uleb_prefix fuel input value rest ->
    exists bytes, input = List.app bytes rest /\
      (1 <= List.length bytes <= fuel)%nat.
Proof.
  intros fuel input value rest H.
  induction H as [fuel b rest Hb | fuel b input value rest Hb Hr IH].
  - exists (b :: nil). cbn. split; [reflexivity | lia].
  - destruct IH as [bytes [Hinput Hlength]].
    exists (b :: bytes). cbn. split; [now rewrite Hinput | lia].
Qed.

Definition u32_prefix input value rest :=
  uleb_prefix 5 input value rest /\ (value <= 4294967295)%N.

Definition decode_u32 input : option (N * list byte) :=
  match decode_uleb 5 input with
  | Some (value, rest) =>
      if N.leb value 4294967295 then Some (value, rest) else None
  | None => None
  end.

Definition decode_u32_pair input : option ((N * N) * list byte) :=
  match decode_u32 input with
  | Some (first, rest) =>
      option_map (fun '(second, suffix) => ((first, second), suffix))
        (decode_u32 rest)
  | None => None
  end.

Lemma decode_u32_correct : forall input value rest,
    decode_u32 input = Some (value, rest) <-> u32_prefix input value rest.
Proof.
  intros input value rest.
  unfold decode_u32, u32_prefix.
  split.
  - destruct (decode_uleb 5 input) as [[v suffix]|] eqn:Hr;
      try discriminate.
    destruct (N.leb v 4294967295) eqn:Hv; try discriminate.
    intro H; inversion H; subst.
    split; [apply decode_uleb_correct; assumption | now apply N.leb_le].
  - intros [Hr Hv].
    apply decode_uleb_correct in Hr.
    rewrite Hr, (proj2 (N.leb_le _ _) Hv). reflexivity.
Qed.

Lemma decode_u32_pair_correct : forall input first second rest,
    decode_u32_pair input = Some ((first, second), rest) <->
    exists middle, u32_prefix input first middle /\
      u32_prefix middle second rest.
Proof.
  intros input first second rest.
  unfold decode_u32_pair.
  split.
  - destruct (decode_u32 input) as [[v middle]|] eqn:Hfirst;
      try discriminate.
    destruct (decode_u32 middle) as [[w suffix]|] eqn:Hsecond;
      cbn; try discriminate.
    intro H; inversion H; subst.
    exists middle. split; now apply decode_u32_correct.
  - intros [middle [Hfirst Hsecond]].
    apply decode_u32_correct in Hfirst, Hsecond.
    rewrite Hfirst, Hsecond. reflexivity.
Qed.

Section Reader.
Context {Toks : nat -> Type} `{Sized Toks byte}.

Fixpoint read_uleb (fuel : nat) {n} (input : Toks n) :
    option (Success Toks byte N n) :=
  match fuel with
  | O => None
  | S fuel' =>
      match Success.getTok input with
      | None => None
      | Some first =>
          if N.ltb (Byte.to_N (Success.value first)) 128 then
            Some (Success.map Byte.to_N first)
          else
            option_map
              (fun next =>
                Success.map
                  (fun '(b, value) => Byte.to_N b - 128 + 128 * value)
                  (Success.and first next))
              (read_uleb fuel' (Success.leftovers first))
      end
  end.

Definition read_u32 {n} (input : Toks n) :=
  match read_uleb 5 input with
  | Some result =>
      if N.leb (Success.value result) 4294967295 then Some result else None
  | None => None
  end.

Lemma getTok_consumed_one : forall n (input : Toks n) first,
    Success.getTok input = Some first ->
    (n - Success.size first = 1)%nat.
Proof.
  intros n input first Htok.
  destruct n as [|n].
  - pose proof (Success.small first). lia.
  - unfold Success.getTok in Htok.
    destruct (uncons input) as [[b tail]|]; [|discriminate].
    cbn [option_map Success.fromView uncurry] in Htok.
    inversion Htok; subst first.
    cbn [Success.size]. lia.
Qed.

Lemma read_uleb_consumed_bound : forall fuel n (input : Toks n) result,
    read_uleb fuel input = Some result ->
    (n - Success.size result <= fuel)%nat.
Proof.
  induction fuel as [|fuel IH]; intros n input result Hread; [discriminate |].
  cbn [read_uleb] in Hread.
  destruct (Success.getTok input) as [first|] eqn:Hfirst; [|discriminate].
  pose proof (getTok_consumed_one n input first Hfirst) as Hcount.
  destruct (N.ltb (Byte.to_N (Success.value first)) 128).
  - inversion Hread; subst result. cbn [Success.map Success.size]. lia.
  - destruct (read_uleb fuel (Success.leftovers first)) as [next|] eqn:Hnext;
      [|discriminate].
    cbn [option_map] in Hread. inversion Hread; subst result.
    specialize (IH _ _ next Hnext).
    pose proof (Success.small first).
    pose proof (Success.small next).
    cbn [Success.map Success.and Success.lt_lift Success.le_lift Success.size].
    lia.
Qed.

Definition read_u32_pair {n} (input : Toks n) :=
  match read_u32 input with
  | Some first =>
      option_map (Success.and first) (read_u32 (Success.leftovers first))
  | None => None
  end.

Context {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Definition parse_bounded_u32 {n} : Parser Toks byte M N n :=
  MkParser (fun _ _ input => fromOption (read_u32 input)).

Definition parse_bounded_u32_pair {n} : Parser Toks byte M (N * N) n :=
  MkParser (fun _ _ input => fromOption (read_u32_pair input)).
End Reader.

Definition observe_reader {A n} (result : Success (SizedList byte) byte A n) :=
  (Success.value result, @Sized.value _ _ _ (Success.leftovers result)).

Lemma read_uleb_correct : forall fuel n (input : SizedList byte n),
    option_map observe_reader (read_uleb fuel input) =
    decode_uleb fuel (@Sized.value _ _ _ input).
Proof.
  induction fuel as [|fuel IH]; intros n [input Hlen].
  - reflexivity.
  - destruct input as [|b input]; cbn in Hlen; subst n.
    + reflexivity.
    + cbn [read_uleb Success.getTok sizedList uncons listUncons
        Success.fromView Success.map observe_reader Sized.value decode_uleb
        option_map uncurry Success.value Success.size Success.small
        Success.leftovers].
      destruct (N.ltb (Byte.to_N b) 128); [reflexivity |].
      match goal with
      | |- context [read_uleb fuel ?tail] =>
          specialize (IH _ tail);
          destruct (@read_uleb (SizedList byte) (sizedList byte) fuel _ tail)
            as [result|] eqn:Hread
      end;
        cbn in IH; rewrite <- IH;
        [destruct result |]; reflexivity.
Qed.

Lemma read_u32_correct : forall n (input : SizedList byte n),
    option_map observe_reader (read_u32 input) =
    decode_u32 (@Sized.value _ _ _ input).
Proof.
  intros n input.
  unfold read_u32, decode_u32.
  rewrite <- (read_uleb_correct 5 n input).
  destruct (read_uleb 5 input) as [result|]; cbn; [|reflexivity].
  destruct (N.leb (Success.value result) 4294967295); reflexivity.
Qed.

Lemma parse_bounded_u32_correct : forall n m (Hle : (m <= n)%nat)
    (input : SizedList byte m) value rest,
    option_map observe_reader
      (runParser (parse_bounded_u32 : Parser (SizedList byte) byte option N n)
        Hle input) = Some (value, rest) <->
    u32_prefix (@Sized.value _ _ _ input) value rest.
Proof.
  intros.
  unfold parse_bounded_u32; cbn [runParser].
  assert (Hfrom : (fromOption (read_u32 input) :
    option (Success (SizedList byte) byte N m)) = read_u32 input).
  { destruct (read_u32 input); reflexivity. }
  rewrite Hfrom.
  rewrite read_u32_correct.
  apply decode_u32_correct.
Qed.

Lemma read_u32_pair_correct : forall n (input : SizedList byte n),
    option_map observe_reader (read_u32_pair input) =
    decode_u32_pair (@Sized.value _ _ _ input).
Proof.
  intros n input.
  unfold read_u32_pair, decode_u32_pair.
  rewrite <- (read_u32_correct n input).
  destruct (read_u32 input) as [first|]; cbn; [|reflexivity].
  destruct first as [v size Hsize rest].
  cbn [observe_reader Success.value Success.leftovers Success.size].
  rewrite <- (read_u32_correct size rest).
  destruct (read_u32 rest) as [second|]; [destruct second |]; reflexivity.
Qed.
