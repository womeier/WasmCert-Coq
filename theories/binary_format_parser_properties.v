(** Properties of the parsers used by [run_parse_module_str].

    The option instances below are the instances selected by the extracted
    module parser.  RawMonad/RawApplicative do not require laws, so these
    results must not be generalized to arbitrary instances without additional
    hypotheses.

    This file verifies the byte-count and numeric-range guards on the actual
    Parseque execution path.  Recursive LEB128 grammar correspondence and
    encoder roundtrips are proved in [leb128_properties]. *)
From Wasm Require Import binary_format_parser binary_format_printer datatypes
                         leb128_properties.
From Stdlib Require Import ZArith Lia Strings.Byte NArith.Nnat Arith.Peano_dec.
From parseque Require Import Parseque.

Local Open Scope list_scope.

Section OptionParsers.
  Context {Toks : nat -> Type}.
  Context {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  Lemma run_map_option {A B : Type} (f : A -> B)
      (p : Parser Toks Byte.byte option A n) :
    runParser (Combinators.map f p) bound input =
    option_map (Success.map f) (runParser p bound input).
  Proof. reflexivity. Qed.

  Lemma run_bind_option_success {A B : Type}
      (p : Parser Toks Byte.byte option A n)
      (q : A -> Box (Parser Toks Byte.byte option B) n) s :
    runParser (Combinators.bind p q) bound input = Some s ->
    exists r t,
      runParser p bound input = Some r /\
      runParser
        (call (q (Success.value r))
          (Nat.le_trans _ _ _ (Success.small r) bound))
        (Nat.le_refl _) (Success.leftovers r) = Some t /\
      Success.value s = Success.value t /\
      Success.size s = Success.size t.
  Proof.
    unfold Combinators.bind, Combinators.map, Combinators.andbind.
    simpl.
    destruct (runParser p bound input) as [r|] eqn:R; [|discriminate].
    simpl.
    destruct (runParser
      (call (q (Success.value r))
        (Nat.le_trans _ _ _ (Success.small r) bound))
      (Nat.le_refl _) (Success.leftovers r)) as [t|] eqn:T;
      [|discriminate].
    simpl. intro E; inversion E; subst.
    exists r, t. repeat split; assumption.
  Qed.

  Lemma run_guardM_option {A B : Type} (f : A -> option B)
      (p : Parser Toks Byte.byte option A n) :
    runParser (Combinators.guardM f p) bound input =
    match runParser p bound input with
    | Some s => Success.guardM f s
    | None => None
    end.
  Proof.
    unfold Combinators.guardM.
    simpl. destruct (runParser p bound input) as [s|]; [|reflexivity].
    simpl. destruct (Success.guardM f s); reflexivity.
  Qed.

  Lemma run_alt_option {A : Type}
      (p q : Parser Toks Byte.byte option A n) :
    runParser (Combinators.alt p q) bound input =
    match runParser p bound input with
    | Some s => Some s
    | None => runParser q bound input
    end.
  Proof.
    unfold Combinators.alt. simpl.
    destruct (runParser p bound input); reflexivity.
  Qed.

  Lemma run_sized_parser_option {A : Type} (p : Parser Toks Byte.byte option A n) :
    runParser (sized_parser p) bound input =
    option_map
      (fun s => Success.MkSuccess
        (Success.value s, N.of_nat (m - Success.size s))
        (Success.small s) (Success.leftovers s))
      (runParser p bound input).
  Proof.
    unfold sized_parser. simpl.
    destruct (runParser p bound input) as [[a k Hk rest]|]; reflexivity.
  Qed.

  Lemma run_assert_sized_option {A : Type} (p : Parser Toks Byte.byte option A n)
      (constraint : N -> bool) :
    runParser (assert_sized p constraint) bound input =
    match runParser p bound input with
    | Some s =>
        if constraint (N.of_nat (m - Success.size s)) then Some s else None
    | None => None
    end.
  Proof.
    unfold assert_sized.
    rewrite run_guardM_option, run_sized_parser_option.
    destruct (runParser p bound input) as [[a k Hk rest]|]; simpl.
    unfold Success.guardM; simpl.
    - destruct (constraint (N.of_nat (m - k))); reflexivity.
    - reflexivity.
  Qed.

  Lemma assert_sized_option_correct {A : Type}
      (p : Parser Toks Byte.byte option A n) (constraint : N -> bool) s :
    runParser (assert_sized p constraint) bound input = Some s <->
    runParser p bound input = Some s /\
    constraint (N.of_nat (m - Success.size s)) = true.
  Proof.
    rewrite run_assert_sized_option.
    destruct (runParser p bound input) as [r|] eqn:H.
    - destruct (constraint (N.of_nat (m - Success.size r))) eqn:C.
      + split.
        * intro E; inversion E; subst. auto.
        * intros [E _]; inversion E; subst. reflexivity.
      + split; [discriminate |].
        intros [E D]; inversion E; subst. congruence.
    - split; [discriminate | intros [E _]; discriminate].
  Qed.

  Lemma guardM_option_success {A B : Type} (f : A -> option B)
      (p : Parser Toks Byte.byte option A n) s :
    runParser (Combinators.guardM f p) bound input = Some s ->
    exists r,
      runParser p bound input = Some r /\
      f (Success.value r) = Some (Success.value s) /\
      Success.size r = Success.size s.
  Proof.
    rewrite run_guardM_option.
    destruct (runParser p bound input) as [[a k Hk rest]|] eqn:H;
      [|discriminate].
    unfold Success.guardM; simpl.
    destruct (f a) as [b|] eqn:F; [|discriminate].
    intro E; inversion E; subst.
    eexists; repeat split; eauto.
  Qed.
End OptionParsers.

Section ObservedParsers.
  Context {A B : Type} {n : nat}.
  Variable bs : list Byte.byte.
  Variable bound : List.length bs <= n.

  Lemma observe_map_option (f : A -> B)
      (p : Parser (SizedList Byte.byte) Byte.byte option A n) :
    observe_leb (runParser (Combinators.map f p) bound (mkSizedList bs)) =
    option_map (fun '(a, rest) => (f a, rest))
      (observe_leb (runParser p bound (mkSizedList bs))).
  Proof.
    rewrite run_map_option.
    destruct (runParser p bound (mkSizedList bs)); reflexivity.
  Qed.

  Lemma observe_alt_option
      (p q : Parser (SizedList Byte.byte) Byte.byte option A n) :
    observe_leb (runParser (Combinators.alt p q) bound (mkSizedList bs)) =
    match observe_leb (runParser p bound (mkSizedList bs)) with
    | Some result => Some result
    | None => observe_leb (runParser q bound (mkSizedList bs))
    end.
  Proof.
    rewrite run_alt_option.
    destruct (runParser p bound (mkSizedList bs)); reflexivity.
  Qed.

  Lemma observe_andbind_success
      (p : Parser (SizedList Byte.byte) Byte.byte option A n)
      (q : A -> Parser (SizedList Byte.byte) Byte.byte option B n)
      a tail b rest :
    observe_leb (runParser p bound (mkSizedList bs)) = Some (a, tail) ->
    (forall tail_bound : List.length tail <= n,
      observe_leb (runParser (q a) tail_bound (mkSizedList tail)) =
        Some (b, rest)) ->
    observe_leb
      (runParser (Combinators.andbind p (fun a => q a))
        bound (mkSizedList bs)) = Some ((a, b), rest).
  Proof.
    intros P Q. apply observe_leb_success in P.
    destruct P as [s [P [V Left]]].
    unfold Combinators.andbind. cbn [runParser]. rewrite P. simpl.
    destruct s as [v k Hk [tail' Length]]. simpl in V, Left.
    subst v tail'. subst k. simpl.
    assert (Eta : forall p : List.length tail = List.length tail,
      @Sized.MkSizedType (list byte) (@List.length byte)
        (List.length tail) tail p = mkSizedList tail).
    { intro equality. unfold mkSizedList. f_equal. apply UIP_nat. }
    rewrite !Eta.
    match goal with
    | |- context [runParser (q a) ?tail_bound (mkSizedList tail)] =>
        pose proof (Q tail_bound) as R;
        destruct (runParser (q a) tail_bound (mkSizedList tail)) as [t|] eqn:T
    end.
    - unfold observe_leb in R |- *. simpl in R |- *.
      inversion R. reflexivity.
    - discriminate R.
  Qed.

  Lemma observe_guardM_option (f : A -> option B)
      (p : Parser (SizedList Byte.byte) Byte.byte option A n) :
    observe_leb (runParser (Combinators.guardM f p) bound (mkSizedList bs)) =
    match observe_leb (runParser p bound (mkSizedList bs)) with
    | Some (a, rest) => option_map (fun b => (b, rest)) (f a)
    | None => None
    end.
  Proof.
    rewrite run_guardM_option.
    destruct (runParser p bound (mkSizedList bs)) as [s|]; [|reflexivity].
    unfold observe_leb, Success.guardM. simpl.
    destruct (f (Success.value s)); reflexivity.
  Qed.

  Lemma observe_assert_sized_option
      (p : Parser (SizedList Byte.byte) Byte.byte option A n) constraint :
    observe_leb (runParser (assert_sized p constraint) bound (mkSizedList bs)) =
    match observe_leb (runParser p bound (mkSizedList bs)) with
    | Some (a, rest) =>
        if constraint (N.of_nat (List.length bs - List.length rest))
        then Some (a, rest) else None
    | None => None
    end.
  Proof.
    rewrite run_assert_sized_option.
    destruct (runParser p bound (mkSizedList bs))
      as [[a k Hk [rest Length]]|]; [|reflexivity].
    subst k. unfold observe_leb. simpl.
    destruct (constraint (N.of_nat (List.length bs - List.length rest)));
      reflexivity.
  Qed.
End ObservedParsers.

Lemma observe_map_andbind_success {A B C : Type} {n}
    bs (bound : List.length bs <= n) (f : A * B -> C)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : A -> Parser (SizedList Byte.byte) Byte.byte option B n)
    a tail b rest :
  observe_leb (runParser p bound (mkSizedList bs)) = Some (a, tail) ->
  (forall tail_bound : List.length tail <= n,
    observe_leb (runParser (q a) tail_bound (mkSizedList tail)) =
      Some (b, rest)) ->
  observe_leb
    (runParser (Combinators.map f (Combinators.andbind p (fun a => q a)))
      bound (mkSizedList bs)) = Some (f (a, b), rest).
Proof.
  intros P Q. rewrite observe_map_option.
  erewrite observe_andbind_success; [reflexivity | exact P | exact Q].
Qed.

Lemma parse_u32_observe n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) =
  match read_unsigned bs with
  | Some (v, rest) =>
      if N.leb (N.of_nat (List.length bs - List.length rest)) 5 then
        if N.leb v 4294967295 then Some (v, rest) else None
      else None
  | None => None
  end.
Proof.
  unfold parse_u32_as_N.
  rewrite observe_guardM_option, observe_assert_sized_option,
    extract_unsigned_correct.
  destruct (read_unsigned bs) as [[v rest]|]; [|reflexivity].
  destruct (N.leb (N.of_nat (List.length bs - List.length rest)) 5);
    [destruct (N.leb v 4294967295) |]; reflexivity.
Qed.

Lemma parse_s32_observe n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (@parse_s32 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) =
  match read_signed bs with
  | Some (z, rest) =>
      if N.leb (N.of_nat (List.length bs - List.length rest)) 5 then
        if andb (Z.leb z 2147483647) (Z.leb (-2147483648) z)
        then Some (Wasm_int.Int32.repr z, rest) else None
      else None
  | None => None
  end.
Proof.
  unfold parse_s32.
  rewrite observe_guardM_option, observe_assert_sized_option,
    extract_signed_correct.
  destruct (read_signed bs) as [[z rest]|]; [|reflexivity].
  destruct (N.leb (N.of_nat (List.length bs - List.length rest)) 5);
    [destruct (andb (Z.leb z 2147483647) (Z.leb (-2147483648) z)) |];
    reflexivity.
Qed.

Lemma parse_s64_observe n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (@parse_s64 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) =
  match read_signed bs with
  | Some (z, rest) =>
      if N.leb (N.of_nat (List.length bs - List.length rest)) 10 then
        if andb (Z.leb z 9223372036854775807)
                (Z.leb (-9223372036854775808) z)
        then Some (Wasm_int.Int64.repr z, rest) else None
      else None
  | None => None
  end.
Proof.
  unfold parse_s64.
  rewrite observe_guardM_option, observe_assert_sized_option,
    extract_signed_correct.
  destruct (read_signed bs) as [[z rest]|]; [|reflexivity].
  destruct (N.leb (N.of_nat (List.length bs - List.length rest)) 10);
    [destruct (andb (Z.leb z 9223372036854775807)
                   (Z.leb (-9223372036854775808) z)) |]; reflexivity.
Qed.

Lemma parse_s33_observe n bs (bound : List.length bs <= n) :
  observe_leb
    (runParser
      (@parse_s33 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList bs)) =
  match read_signed bs with
  | Some (z, rest) =>
      if N.leb (N.of_nat (List.length bs - List.length rest)) 5 then
        if andb (Z.leb (-4294967296) z) (Z.leb z 4294967295)
        then Some (z, rest) else None
      else None
  | None => None
  end.
Proof.
  unfold parse_s33.
  rewrite observe_guardM_option, observe_assert_sized_option,
    extract_signed_correct.
  destruct (read_signed bs) as [[z rest]|]; [|reflexivity].
  destruct (N.leb (N.of_nat (List.length bs - List.length rest)) 5);
    [destruct (andb (Z.leb (-4294967296) z) (Z.leb z 4294967295)) |];
    reflexivity.
Qed.

Lemma parse_u32_encode x rest n
    (bound : List.length (leb128.encode_unsigned x ++ rest) <= n) :
  (x <= 4294967295)%N ->
  observe_leb
    (runParser
      (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (leb128.encode_unsigned x ++ rest))) =
  Some (x, rest).
Proof.
  intro Range. rewrite parse_u32_observe, read_encode_unsigned.
  rewrite List.length_app, Nat.add_sub.
  assert (Width : N.leb (N.of_nat (List.length (leb128.encode_unsigned x))) 5 =
    true).
  { apply N.leb_le. pose proof (encode_u32_length x Range). lia. }
  rewrite Width. now rewrite (proj2 (N.leb_le _ _) Range).
Qed.

Lemma parse_s32_encode z rest n
    (bound : List.length (leb128.encode_signed z ++ rest) <= n) :
  (-2147483648 <= z <= 2147483647)%Z ->
  observe_leb
    (runParser
      (@parse_s32 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (leb128.encode_signed z ++ rest))) =
  Some (Wasm_int.Int32.repr z, rest).
Proof.
  intro Range. rewrite parse_s32_observe, read_encode_signed.
  rewrite List.length_app, Nat.add_sub.
  assert (Width : N.leb (N.of_nat (List.length (leb128.encode_signed z))) 5 =
    true).
  { apply N.leb_le. pose proof (encode_s32_length z Range). lia. }
  assert (Fits :
    andb (Z.leb z 2147483647) (Z.leb (-2147483648) z) = true).
  { apply Bool.andb_true_iff. split; apply Z.leb_le; lia. }
  now rewrite Width, Fits.
Qed.

Lemma parse_s64_encode z rest n
    (bound : List.length (leb128.encode_signed z ++ rest) <= n) :
  (-9223372036854775808 <= z <= 9223372036854775807)%Z ->
  observe_leb
    (runParser
      (@parse_s64 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (leb128.encode_signed z ++ rest))) =
  Some (Wasm_int.Int64.repr z, rest).
Proof.
  intro Range. rewrite parse_s64_observe, read_encode_signed.
  rewrite List.length_app, Nat.add_sub.
  assert (Width : N.leb (N.of_nat (List.length (leb128.encode_signed z))) 10 =
    true).
  { apply N.leb_le. pose proof (encode_s64_length z Range). lia. }
  assert (Fits :
    andb (Z.leb z 9223372036854775807) (Z.leb (-9223372036854775808) z) = true).
  { apply Bool.andb_true_iff. split; apply Z.leb_le; lia. }
  now rewrite Width, Fits.
Qed.

Lemma parse_s33_encode z rest n
    (bound : List.length (leb128.encode_signed z ++ rest) <= n) :
  (-4294967296 <= z <= 4294967295)%Z ->
  observe_leb
    (runParser
      (@parse_s33 (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (leb128.encode_signed z ++ rest))) =
  Some (z, rest).
Proof.
  intro Range. rewrite parse_s33_observe, read_encode_signed.
  rewrite List.length_app, Nat.add_sub.
  assert (Width : N.leb (N.of_nat (List.length (leb128.encode_signed z))) 5 =
    true).
  { apply N.leb_le. pose proof (encode_s33_length z Range). lia. }
  assert (Fits :
    andb (Z.leb (-4294967296) z) (Z.leb z 4294967295) = true).
  { apply Bool.andb_true_iff. split; apply Z.leb_le; lia. }
  now rewrite Width, Fits.
Qed.

Lemma parse_heap_typeidx_encode x rest n
    (bound : List.length (leb128.encode_signed (Z.of_N x) ++ rest) <= n) :
  (x <= 4294967295)%N ->
  observe_leb
    (runParser
      (@parse_heap_typeidx (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (leb128.encode_signed (Z.of_N x) ++ rest))) =
  Some (x, rest).
Proof.
  intro Range. unfold parse_heap_typeidx.
  rewrite observe_guardM_option, parse_s33_encode.
  - rewrite (proj2 (Z.leb_le _ _) (N2Z.is_nonneg x)).
    simpl. now rewrite N2Z.id.
  - pose proof (N2Z.is_nonneg x).
    apply N2Z.inj_le in Range. lia.
Qed.

Section IntegerGuards.
  Context {Toks : nat -> Type} `{Sized Toks Byte.byte}.
  Context {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  (** Both guards are necessary: the value guard rejects overflow, while the
      consumed-byte guard rejects overlong encodings of an in-range value. *)
  Lemma parse_u32_as_N_guards s :
    runParser (@parse_u32_as_N Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (Success.value s <= 4294967295)%N /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_u32_as_N. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (N.leb (Success.value r) 4294967295) eqn:B; [|discriminate].
    inversion V.
    apply assert_sized_option_correct in R.
    destruct R as [_ W].
    split.
    - now apply N.leb_le.
    - rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_u8_as_N_guards s :
    runParser (@parse_u8_as_N Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (Success.value s <= 255)%N /\
    (N.of_nat (m - Success.size s) <= 2)%N.
  Proof.
    unfold parse_u8_as_N. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (N.leb (Success.value r) 255) eqn:B; [|discriminate].
    inversion V.
    apply assert_sized_option_correct in R.
    destruct R as [_ W].
    split.
    - now apply N.leb_le.
    - rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_s32_guards s :
    runParser (@parse_s32 Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    exists z,
      Success.value s = Wasm_int.Int32.repr z /\
      Wasm_int.Int32.signed (Success.value s) = z /\
      (-2147483648 <= z <= 2147483647)%Z /\
      (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_s32. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (andb (Z.leb (Success.value r) 2147483647)
              (Z.leb (-2147483648) (Success.value r))) eqn:B; [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Upper Lower].
    apply Z.leb_le in Upper. apply Z.leb_le in Lower.
    inversion V.
    apply assert_sized_option_correct in R. destruct R as [_ W].
    exists (Success.value r).
    split; [reflexivity |].
    split.
    - apply Wasm_int.Int32.signed_repr.
      change (-2147483648 <= Success.value r <= 2147483647)%Z. lia.
    - split; [lia |]. rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_s64_guards s :
    runParser (@parse_s64 Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    exists z,
      Success.value s = Wasm_int.Int64.repr z /\
      Wasm_int.Int64.signed (Success.value s) = z /\
      (-9223372036854775808 <= z <= 9223372036854775807)%Z /\
      (N.of_nat (m - Success.size s) <= 10)%N.
  Proof.
    unfold parse_s64. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (andb (Z.leb (Success.value r) 9223372036854775807)
              (Z.leb (-9223372036854775808) (Success.value r))) eqn:B;
      [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Upper Lower].
    apply Z.leb_le in Upper. apply Z.leb_le in Lower.
    inversion V.
    apply assert_sized_option_correct in R. destruct R as [_ W].
    exists (Success.value r).
    split; [reflexivity |].
    split.
    - apply Wasm_int.Int64.signed_repr.
      change (-9223372036854775808 <= Success.value r <=
        9223372036854775807)%Z. lia.
    - split; [lia |]. rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_s33_guards s :
    runParser (@parse_s33 Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (-4294967296 <= Success.value s <= 4294967295)%Z /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_s33. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (andb (Z.leb (-4294967296) (Success.value r))
              (Z.leb (Success.value r) 4294967295)) eqn:B;
      [|discriminate].
    apply Bool.andb_true_iff in B. destruct B as [Lower Upper].
    apply Z.leb_le in Lower. apply Z.leb_le in Upper.
    inversion V.
    apply assert_sized_option_correct in R. destruct R as [_ W].
    split; [lia |]. rewrite <- S. now apply N.leb_le.
  Qed.

  Lemma parse_heap_typeidx_guards s :
    runParser (@parse_heap_typeidx Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    (Success.value s <= 4294967295)%N /\
    (N.of_nat (m - Success.size s) <= 5)%N.
  Proof.
    unfold parse_heap_typeidx. intro Hparse.
    apply guardM_option_success in Hparse.
    destruct Hparse as [r [R [V S]]].
    destruct (Z.leb 0 (Success.value r)) eqn:B; [|discriminate].
    apply Z.leb_le in B.
    inversion V.
    apply parse_s33_guards in R. destruct R as [Range Width].
    split.
    - apply N2Z.inj_le. rewrite Z2N.id; lia.
    - rewrite <- S. exact Width.
  Qed.
End IntegerGuards.

Definition encoded_list {A} (encode : A -> list byte) (values : list A) :=
  List.concat (List.map encode values).

Lemma encoded_list_cons {A} (encode : A -> list byte) a values :
  encoded_list encode (a :: values) = encode a ++ encoded_list encode values.
Proof. reflexivity. Qed.

Lemma encoded_list_app {A} (encode : A -> list byte) left right :
  encoded_list encode (left ++ right) =
  encoded_list encode left ++ encoded_list encode right.
Proof.
  unfold encoded_list. now rewrite List.map_app, List.concat_app.
Qed.

Lemma split_list_twice {A} (values : list A) count :
  List.length values = 2 * count ->
  exists left right, values = left ++ right /\
    List.length left = count /\ List.length right = count.
Proof.
  intro Length. exists (List.firstn count values), (List.skipn count values).
  split; [symmetry; apply List.firstn_skipn |].
  split.
  - rewrite List.length_firstn, Nat.min_l; lia.
  - rewrite List.length_skipn. lia.
Qed.

Section ConcreteVectors.
  Context {A : Type} {n : nat}.
  Variable p : Parser (SizedList byte) byte option A n.
  Variable encode : A -> list byte.
  Variable valid : A -> Prop.
  Hypothesis Element :
    forall a, valid a -> forall rest
      (bound : List.length (encode a ++ rest) <= n),
    observe_leb (runParser p bound (mkSizedList (encode a ++ rest))) =
      Some (a, rest).

  Lemma parse_vec_positive_encode count values rest
      (Elements : List.Forall valid values)
      (Count : List.length values = Pos.to_nat count)
      (bound : List.length (encoded_list encode values ++ rest) <= n) :
    observe_leb
      (runParser (parse_vec_aux_positive p count)
        bound (mkSizedList (encoded_list encode values ++ rest))) =
    Some (values, rest).
  Proof.
    revert values rest Elements Count bound.
    induction count as [count IH | count IH |];
      intros values rest Elements Count bound.
    - rewrite Pos2Nat.inj_xI in Count.
      destruct values as [|a values]; [simpl in Count; lia |].
      inversion Elements as [|? ? Head Tail]; subst.
      destruct (split_list_twice values (Pos.to_nat count) ltac:(simpl in Count; lia))
        as [left [right [Split [Left Right]]]].
      subst values. apply List.Forall_app in Tail. destruct Tail as [VL VR].
      revert bound.
      rewrite encoded_list_cons, encoded_list_app, <- !List.app_assoc.
      intro bound. cbn [parse_vec_aux_positive].
      eapply observe_map_andbind_success with
        (a := a) (b := (left, right))
        (tail := encoded_list encode left ++ encoded_list encode right ++ rest).
      + now apply Element.
      + intro tail_bound.
        eapply observe_andbind_success with (a := left) (b := right)
          (tail := encoded_list encode right ++ rest).
        * now apply IH.
        * intro right_bound. now apply IH.
    - rewrite Pos2Nat.inj_xO in Count.
      destruct (split_list_twice values (Pos.to_nat count) Count)
        as [left [right [Split [Left Right]]]].
      subst values. apply List.Forall_app in Elements.
      destruct Elements as [VL VR].
      revert bound. rewrite encoded_list_app, <- List.app_assoc.
      intro bound. cbn [parse_vec_aux_positive].
      eapply observe_map_andbind_success with (a := left) (b := right)
        (tail := encoded_list encode right ++ rest).
      + now apply IH.
      + intro right_bound. now apply IH.
    - change (List.length values = 1) in Count.
      destruct values as [|a values]; [discriminate |].
      destruct values as [|extra values]; [|simpl in Count; lia].
      inversion Elements as [|? ? Head Tail]; subst.
      revert bound. cbn [encoded_list List.map List.concat].
      rewrite List.app_nil_r. intro bound.
      cbn [parse_vec_aux_positive]. rewrite observe_map_option.
      now rewrite (Element a Head rest bound).
  Qed.

  Lemma parse_vec_encode values rest
      (Elements : List.Forall valid values)
      (Range : (N.of_nat (List.length values) <= 4294967295)%N)
      (bound : List.length
        (leb128.encode_unsigned (N.of_nat (List.length values)) ++
          encoded_list encode values ++ rest) <= n) :
    observe_leb
      (runParser (parse_vec p) bound
        (mkSizedList
          (leb128.encode_unsigned (N.of_nat (List.length values)) ++
            encoded_list encode values ++ rest))) =
    Some (values, rest).
  Proof.
    assert (CountParse :
      observe_leb
        (runParser parse_vec_length bound
          (mkSizedList
            (leb128.encode_unsigned (N.of_nat (List.length values)) ++
              encoded_list encode values ++ rest))) =
      Some (N.of_nat (List.length values), encoded_list encode values ++ rest)).
    { unfold parse_vec_length. now apply parse_u32_encode. }
    unfold parse_vec.
    rewrite observe_alt_option, observe_guardM_option, CountParse.
    destruct values as [|a values]; [reflexivity |].
    assert (Nonzero :
      N.eqb (N.of_nat (List.length (a :: values))) 0 = false)
      by (apply N.eqb_neq; simpl; discriminate).
    rewrite Nonzero. cbn [option_map].
    unfold Combinators.bind.
    eapply observe_map_andbind_success with
      (a := N.of_nat (List.length (a :: values))) (b := a :: values)
      (tail := encoded_list encode (a :: values) ++ rest).
    - exact CountParse.
    - intro tail_bound. cbn [parse_vec_aux List.length N.of_nat].
      apply parse_vec_positive_encode; [exact Elements |].
      simpl. now rewrite SuccNat2Pos.id_succ.
  Qed.
End ConcreteVectors.

Lemma parse_number_type_encode t rest n
    (bound : List.length (binary_of_number_type t :: rest) <= n) :
  observe_leb
    (runParser
      (@parse_number_type (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (binary_of_number_type t :: rest))) =
  Some (t, rest).
Proof. destruct t; reflexivity. Qed.

Lemma parse_vector_type_encode t rest n
    (bound : List.length (binary_of_vector_type t :: rest) <= n) :
  observe_leb
    (runParser
      (@parse_vector_type (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (binary_of_vector_type t :: rest))) =
  Some (t, rest).
Proof. destruct t; reflexivity. Qed.

Lemma parse_reference_type_encode t rest n
    (bound : List.length (binary_of_reference_type t :: rest) <= n) :
  observe_leb
    (runParser
      (@parse_reference_type (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (binary_of_reference_type t :: rest))) =
  Some (t, rest).
Proof. destruct t; reflexivity. Qed.

Lemma parse_value_type_encode t rest n
    (bound : List.length (binary_of_value_type t :: rest) <= n) :
  t <> T_bot ->
  observe_leb
    (runParser
      (@parse_value_type (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (binary_of_value_type t :: rest))) =
  Some (t, rest).
Proof.
  intro Valid. destruct t as [i|v|r|]; [destruct i | destruct v | destruct r |];
    try contradiction; reflexivity.
Qed.

Lemma parse_result_type_encode values rest n
    (bound : List.length (binary_of_result_type values ++ rest) <= n) :
  List.Forall (fun t => t <> T_bot) values ->
  (N.of_nat (List.length values) <= 4294967295)%N ->
  observe_leb
    (runParser
      (@parse_vec (SizedList byte) _ option _ _ _ _ _ _ value_type n parse_value_type)
      bound (mkSizedList (binary_of_result_type values ++ rest))) =
  Some (values, rest).
Proof.
  intros Elements Range.
  unfold binary_of_result_type, binary_of_vec, binary_of_u32_nat in bound |- *.
  revert bound. rewrite <- List.app_assoc. intro bound.
  eapply parse_vec_encode with (valid := fun t => t <> T_bot).
  - intros t Good suffix suffix_bound. now apply parse_value_type_encode.
  - exact Elements.
  - exact Range.
Qed.

Lemma parse_function_type_encode args results rest n
    (bound : List.length (binary_of_functype (Tf args results) ++ rest) <= n) :
  List.Forall (fun t => t <> T_bot) args ->
  List.Forall (fun t => t <> T_bot) results ->
  (N.of_nat (List.length args) <= 4294967295)%N ->
  (N.of_nat (List.length results) <= 4294967295)%N ->
  observe_leb
    (runParser
      (@parse_function_type (SizedList byte) _ option _ _ _ _ _ _ n)
      bound (mkSizedList (binary_of_functype (Tf args results) ++ rest))) =
  Some (Tf args results, rest).
Proof.
  intros Args Results ArgsLength ResultsLength.
  unfold binary_of_functype in bound |- *.
  revert bound. cbn [List.app]. rewrite <- List.app_assoc. intro bound.
  unfold parse_function_type, Combinators.rand.
  eapply observe_map_andbind_success with
    (a := x60) (b := Tf args results)
    (tail := binary_of_result_type args ++ binary_of_result_type results ++ rest).
  - reflexivity.
  - intro body_bound. unfold Combinators.and.
    eapply observe_map_andbind_success with
      (a := args) (b := results)
      (tail := binary_of_result_type results ++ rest).
    + now apply parse_result_type_encode.
    + intro result_bound. now apply parse_result_type_encode.
Qed.

Section SectionSizes.
  Context {Toks : nat -> Type} `{Sized Toks Byte.byte}.
  Context {A : Type} {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  Lemma length_prefixed_payload_guards
      (payload : Parser Toks Byte.byte option A n) s :
    runParser
      (Combinators.bind parse_u32_as_N
        (fun sz => assert_sized payload (fun consumed => N.eqb sz consumed)))
      bound input = Some s ->
    exists r,
      runParser parse_u32_as_N bound input = Some r /\
      (Success.value r <= 4294967295)%N /\
      N.of_nat (Success.size r - Success.size s) = Success.value r.
  Proof.
    intro R. apply run_bind_option_success in R.
    destruct R as [r [t [R [T [V S]]]]].
    change (runParser
      (assert_sized payload
        (fun consumed => N.eqb (Success.value r) consumed))
      (Nat.le_trans _ _ _ (Nat.le_refl _)
        (Nat.lt_le_incl _ _
          (Nat.le_trans _ _ _ (Success.small r) bound)))
      (Success.leftovers r) = Some t) in T.
    apply assert_sized_option_correct in T.
    destruct T as [_ W].
    apply N.eqb_eq in W.
    exists r. split; [exact R |].
    split.
    - now apply parse_u32_as_N_guards in R.
    - rewrite S. symmetry. exact W.
  Qed.
End SectionSizes.

Section VectorLengths.
  Context {Toks : nat -> Type} `{Sized Toks Byte.byte}.
  Context {A : Type} {m n : nat}.
  Variable bound : m <= n.
  Variable input : Toks m.

  (** This theorem covers every successful representation of a zero u32
      length, not just the canonical single zero byte. *)
  Lemma parse_vec_zero_length
      (p : Parser Toks Byte.byte option A n) s :
    runParser (@parse_vec_length Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    Success.value s = 0%N ->
    runParser (parse_vec p) bound input =
      Some (Success.map (fun _ => @nil A) s).
  Proof.
    intros R V.
    unfold parse_vec.
    rewrite run_alt_option, run_guardM_option, R.
    unfold Success.guardM. rewrite V. simpl.
    reflexivity.
  Qed.

  (** For positive counts, the previous length-and-elements parser is used
      unchanged: the zero-count case cannot swallow a nonempty vector. *)
  Lemma parse_vec_positive_length
      (p : Parser Toks Byte.byte option A n) s :
    runParser (@parse_vec_length Toks _ option _ _ _ _ _ _ n)
      bound input = Some s ->
    Success.value s <> 0%N ->
    runParser (parse_vec p) bound input =
    runParser
      (Combinators.bind parse_vec_length (fun k => parse_vec_aux p k))
      bound input.
  Proof.
    intros R V.
    unfold parse_vec.
    rewrite run_alt_option, run_guardM_option, R.
    unfold Success.guardM.
    destruct (N.eqb (Success.value s) 0) eqn:Z; simpl.
    - apply N.eqb_eq in Z. contradiction.
    - reflexivity.
  Qed.
End VectorLengths.

Section CompleteInputs.
  Context {A : Type}.

  (** [run] is the entry point used by [run_parse_module] and hence by the
      extracted interpreter.  In its option instance, a result is accepted
      exactly when the underlying parser succeeds and consumes all input. *)
  Lemma run_option_correct
      (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n)
      bs a :
    @run option _ _ _ _ Byte.byte tokBytes A bs p = Some a <->
    exists s,
      runParser (p (List.length bs)) (Nat.le_refl _) (mkSizedList bs) = Some s /\
      Success.value s = a /\ Success.size s = 0.
  Proof.
    unfold run, fromText, tokenize; simpl.
    destruct (runParser (p (List.length bs)) (Nat.le_refl _)
      (mkSizedList bs)) as [[v k Hk rest]|] eqn:R; simpl.
    - destruct k; simpl.
      + split.
        * intro E; inversion E; subst.
          eexists; repeat split; reflexivity.
        * intros [s [E [V S]]]; inversion E; subst.
          reflexivity.
      + split; [discriminate |].
        intros [s [E [V S]]]; inversion E; subst; discriminate.
    - split; [discriminate | intros [s [E _]]; discriminate].
  Qed.

  Lemma run_option_has_no_leftovers
      (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n)
      bs a :
    @run option _ _ _ _ Byte.byte tokBytes A bs p = Some a ->
    exists s,
      runParser (p (List.length bs)) (Nat.le_refl _) (mkSizedList bs) = Some s /\
      Success.value s = a /\
      @Sized.value _ _ _ (Success.leftovers s) = nil.
  Proof.
    rewrite run_option_correct.
    intros [s [R [V S]]]. exists s. split; [exact R |].
    split; [exact V |].
    pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as L.
    rewrite S in L.
    destruct (@Sized.value _ _ _ (Success.leftovers s));
      [reflexivity | discriminate].
  Qed.

  Lemma run_option_observe
      (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n)
      bs a :
    @run option _ _ _ _ Byte.byte tokBytes A bs p = Some a <->
    observe_leb
      (runParser (p (List.length bs)) (Nat.le_refl _) (mkSizedList bs)) =
    Some (a, nil).
  Proof.
    rewrite run_option_correct, observe_leb_success.
    split.
    - intros [s [R [V S]]]. exists s. split; [exact R |].
      split; [exact V |].
      pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as L.
      rewrite S in L.
      destruct (@Sized.value _ _ _ (Success.leftovers s));
        [reflexivity | discriminate].
    - intros [s [R [V S]]]. exists s. split; [exact R |].
      split; [exact V |].
      pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as L.
      rewrite S in L. simpl in L. symmetry. exact L.
  Qed.
End CompleteInputs.

Lemma run_typeidx_guards bs x :
  @run option _ _ _ _ Byte.byte tokBytes N bs (fun _ => parse_typeidx) = Some x ->
  (x <= 4294967295)%N /\ (N.of_nat (List.length bs) <= 5)%N.
Proof.
  rewrite run_option_correct.
  intros [s [R [V S]]].
  unfold parse_typeidx in R.
  apply parse_u32_as_N_guards in R.
  rewrite V, S, Nat.sub_0_r in R. exact R.
Qed.

Lemma run_heap_typeidx_guards bs x :
  run_parse_heap_typeidx bs = Some x ->
  (x <= 4294967295)%N /\ (N.of_nat (List.length bs) <= 5)%N.
Proof.
  unfold run_parse_heap_typeidx. rewrite run_option_correct.
  intros [s [R [V S]]].
  apply parse_heap_typeidx_guards in R.
  rewrite V, S, Nat.sub_0_r in R. exact R.
Qed.

Lemma run_encode_typeidx x :
  (x <= 4294967295)%N ->
  @run option _ _ _ _ Byte.byte tokBytes typeidx (binary_of_typeidx x)
    (fun _ => parse_typeidx) = Some x.
Proof.
  intro Range. apply run_option_observe.
  unfold binary_of_typeidx, binary_of_idx, binary_of_u32, binary_of_N,
    parse_typeidx.
  pose proof (parse_u32_encode x nil
    (List.length (leb128.encode_unsigned x ++ nil)) (Nat.le_refl _) Range) as R.
  now rewrite List.app_nil_r in R.
Qed.

Theorem run_typeidx_roundtrip bs x :
  @run option _ _ _ _ Byte.byte tokBytes typeidx bs
    (fun _ => parse_typeidx) = Some x ->
  @run option _ _ _ _ Byte.byte tokBytes typeidx (binary_of_typeidx x)
    (fun _ => parse_typeidx) = Some x.
Proof.
  intro R. apply run_typeidx_guards in R.
  apply run_encode_typeidx. exact (proj1 R).
Qed.

Lemma run_encode_heap_typeidx x :
  (x <= 4294967295)%N ->
  run_parse_heap_typeidx (leb128.encode_signed (Z.of_N x)) = Some x.
Proof.
  intro Range. unfold run_parse_heap_typeidx. apply run_option_observe.
  pose proof (parse_heap_typeidx_encode x nil
    (List.length (leb128.encode_signed (Z.of_N x) ++ nil))
    (Nat.le_refl _) Range) as R.
  now rewrite List.app_nil_r in R.
Qed.

Theorem run_heap_typeidx_roundtrip bs x :
  run_parse_heap_typeidx bs = Some x ->
  run_parse_heap_typeidx (leb128.encode_signed (Z.of_N x)) = Some x.
Proof.
  intro R. apply run_heap_typeidx_guards in R.
  apply run_encode_heap_typeidx. exact (proj1 R).
Qed.

Theorem run_i32_roundtrip x :
  @run option _ _ _ _ Byte.byte tokBytes _ (binary_of_i32 x)
    (fun _ => parse_s32) = Some x.
Proof.
  apply run_option_observe. unfold binary_of_i32.
  assert (Range :
    (-2147483648 <= Wasm_int.Int32.signed x <= 2147483647)%Z)
    by apply Wasm_int.Int32.signed_range.
  pose proof (parse_s32_encode (Wasm_int.Int32.signed x) nil
    (List.length (leb128.encode_signed (Wasm_int.Int32.signed x) ++ nil))
    (Nat.le_refl _) Range) as R.
  rewrite List.app_nil_r, Wasm_int.Int32.repr_signed in R. exact R.
Qed.

Theorem run_i64_roundtrip x :
  @run option _ _ _ _ Byte.byte tokBytes _ (binary_of_i64 x)
    (fun _ => parse_s64) = Some x.
Proof.
  apply run_option_observe. unfold binary_of_i64.
  assert (Range :
    (-9223372036854775808 <= Wasm_int.Int64.signed x <= 9223372036854775807)%Z)
    by apply Wasm_int.Int64.signed_range.
  pose proof (parse_s64_encode (Wasm_int.Int64.signed x) nil
    (List.length (leb128.encode_signed (Wasm_int.Int64.signed x) ++ nil))
    (Nat.le_refl _) Range) as R.
  rewrite List.app_nil_r, Wasm_int.Int64.repr_signed in R. exact R.
Qed.

Lemma run_vec_empty_count {A : Type}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) bs :
  @run option _ _ _ _ Byte.byte tokBytes N bs
    (fun _ => parse_vec_length) = Some 0%N ->
  @run option _ _ _ _ Byte.byte tokBytes (list A) bs
    (fun n => parse_vec (p n)) = Some nil.
Proof.
  rewrite run_option_correct.
  intros [s [R [V S]]].
  apply run_option_correct.
  exists (Success.map (fun _ => @nil A) s).
  split.
  - now apply parse_vec_zero_length.
  - split; [reflexivity | exact S].
Qed.

(** Printing a successfully parsed module and parsing it again preserves the
    module, not necessarily the original bytes (encodings need not be canonical).
    This is a target property, not an established guarantee: parser and printer
    bugs may need fixing before it can be proved. *)
Theorem run_parse_module_roundtrip bs m :
  run_parse_module bs = Some m ->
  run_parse_module (binary_of_module m) = Some m.
Admitted.

(** Every lane byte produced by parsing can be printed and parsed again,
    including bytes with the high bit set.  Lane bounds for a particular SIMD
    instruction are a separate validation concern. *)
Lemma run_laneidx_byte_roundtrip b :
  @run option _ _ _ _ Byte.byte tokBytes laneidx
    (binary_of_laneidx (Byte.to_N b)) (fun _ => parse_laneidx) =
  Some (Byte.to_N b).
Proof.
  unfold binary_of_laneidx. rewrite Byte.of_to_N. reflexivity.
Qed.

Lemma run_number_type_roundtrip t :
  @run option _ _ _ _ Byte.byte tokBytes number_type
    (binary_of_number_type t :: nil) (fun _ => parse_number_type) = Some t.
Proof. destruct t; vm_compute; reflexivity. Qed.

Lemma run_vector_type_roundtrip t :
  @run option _ _ _ _ Byte.byte tokBytes vector_type
    (binary_of_vector_type t :: nil) (fun _ => parse_vector_type) = Some t.
Proof. destruct t; vm_compute; reflexivity. Qed.

Lemma run_reference_type_roundtrip t :
  @run option _ _ _ _ Byte.byte tokBytes reference_type
    (binary_of_reference_type t :: nil) (fun _ => parse_reference_type) = Some t.
Proof. destruct t; vm_compute; reflexivity. Qed.

Lemma run_splat_roundtrip sh :
  run_parse_be (binary_of_be (BI_splat_vec sh)) = Some (BI_splat_vec sh).
Proof.
  destruct sh as [i | f]; [destruct i | destruct f]; vm_compute; reflexivity.
Qed.

(** This covers all successfully parsed single-byte instructions, not just a
    hand-selected list of arithmetic opcodes. *)
Lemma run_single_byte_instruction_roundtrip b be :
  run_parse_be (b :: nil) = Some be ->
  run_parse_be (binary_of_be be) = Some be.
Proof.
  destruct b; intro H; vm_compute in H; try discriminate;
    inversion H; subst; vm_compute; reflexivity.
Qed.

Local Open Scope list_scope.

Lemma binary_of_laneidx_byte b :
  binary_of_laneidx (Byte.to_N b) = b :: nil.
Proof. unfold binary_of_laneidx. now rewrite Byte.of_to_N. Qed.

Lemma binary_of_shuffle_bytes bs :
  binary_of_vbinop (13%N, List.map Byte.to_N bs) =
  xfd :: x0d :: bs.
Proof.
  change (xfd :: x0d ::
    List.concat (List.map binary_of_laneidx (List.map Byte.to_N bs)) =
    xfd :: x0d :: bs).
  f_equal. f_equal.
  induction bs as [|b bs IH]; [reflexivity |].
  cbn [List.map List.concat].
  rewrite binary_of_laneidx_byte. simpl. now rewrite IH.
Qed.
