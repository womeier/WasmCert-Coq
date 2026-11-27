(** Prefix soundness for the actual option/Parseque combinators.
    These lemmas retain the input/output byte strings, not merely result
    values.  They are intended for the recursive binary grammar proofs. *)
From Stdlib Require Import List Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties.

Definition input_bytes {n} (ts : SizedList Byte.byte n) : list Byte.byte :=
  @Sized.value _ _ _ ts.

Definition output_bytes {A n}
    (s : Success.Success (SizedList Byte.byte) Byte.byte A n) : list Byte.byte :=
  input_bytes (Success.leftovers s).

Definition parser_sound {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) : Prop :=
  forall m (bound : m <= n) input s,
    runParser p bound input = Some s ->
    exists prefix,
      input_bytes input = prefix ++ output_bytes s /\
      P prefix (Success.value s).

Lemma parser_sound_weaken {A n} p (P Q : list Byte.byte -> A -> Prop) :
  @parser_sound A n p P ->
  (forall bs a, P bs a -> Q bs a) ->
  parser_sound p Q.
Proof.
  intros H Imp m bound input s R.
  destruct (H m bound input s R) as [bs [E HP]].
  exists bs. split; [exact E | now apply Imp].
Qed.

Lemma parser_sound_map {A B n} (f : A -> B)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) (Q : list Byte.byte -> B -> Prop) :
  parser_sound p P ->
  (forall bs a, P bs a -> Q bs (f a)) ->
  parser_sound (Combinators.map f p) Q.
Proof.
  intros H Imp m bound input s R.
  unfold Combinators.map in R; simpl in R.
  destruct (runParser p bound input) as [r|] eqn:Raw; [|discriminate].
  inversion R; subst.
  destruct (H m bound input r Raw) as [bs [E HP]].
  exists bs. split; [exact E | now apply Imp].
Qed.

Lemma parser_sound_guardM {A B n} (f : A -> option B)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) (Q : list Byte.byte -> B -> Prop) :
  parser_sound p P ->
  (forall bs a b, P bs a -> f a = Some b -> Q bs b) ->
  parser_sound (Combinators.guardM f p) Q.
Proof.
  intros H Imp m bound input s R.
  rewrite run_guardM_option in R.
  destruct (runParser p bound input) as [r|] eqn:Raw; [|discriminate].
  unfold Success.guardM in R.
  destruct (f (Success.value r)) as [b|] eqn:F; simpl in R; [|discriminate].
  inversion R; subst.
  destruct (H m bound input r Raw) as [bs [E HP]].
  exists bs. split; [exact E | eapply Imp; eassumption].
Qed.

Lemma parser_sound_alt {A n}
    (p q : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_sound p P -> parser_sound q P ->
  parser_sound (Combinators.alt p q) P.
Proof.
  intros Hp Hq m bound input s R.
  rewrite run_alt_option in R.
  destruct (runParser p bound input) as [r|] eqn:Raw.
  - inversion R; subst. now apply (Hp m bound input).
  - now apply (Hq m bound input).
Qed.

Lemma parser_sound_anyTok n :
  parser_sound (@anyTok (SizedList Byte.byte) Byte.byte _ option _ _ _ n)
    (fun bs b => bs = b :: nil).
Proof.
  intros m bound [bs L] s R.
  destruct m as [|m]; simpl in R; [discriminate |].
  destruct bs as [|b bs]; [discriminate |].
  unfold anyTok in R; simpl in R.
  unfold Success.getTok in R; simpl in R.
  unfold listUncons in R; simpl in R.
  inversion R; subst. exists (b :: nil). split; reflexivity.
Qed.

Lemma parser_sound_assert_sized {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P constraint :
  parser_sound p P -> parser_sound (assert_sized p constraint) P.
Proof.
  intros H m bound input s R.
  apply assert_sized_option_correct in R.
  destruct R as [R _]. now apply (H m bound input s).
Qed.

Lemma parser_sound_le_lower {A m n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P (bound : m <= n) :
  parser_sound p P -> parser_sound (Combinators.le_lower bound p) P.
Proof.
  intros H k lower input s R.
  unfold Combinators.le_lower in R; simpl in R.
  now apply (H k (Nat.le_trans _ _ _ lower bound) input s).
Qed.

Lemma parser_sound_extract {A}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_sound (p n) P) ->
  forall n, parser_sound (extract (fun n => box (p n)) n) P.
Proof.
  intros H n. unfold extract, box, le_close; simpl.
  apply parser_sound_le_lower. apply H.
Qed.

Lemma parser_sound_andbind {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : A -> Box (Parser (SizedList Byte.byte) Byte.byte option B) n)
    (P : list Byte.byte -> A -> Prop)
    (Q : A -> list Byte.byte -> B -> Prop)
    (R : list Byte.byte -> A * B -> Prop) :
  parser_sound p P ->
  (forall a k (lt : k < n), parser_sound (call (q a) lt) (Q a)) ->
  (forall xs ys a b, P xs a -> Q a ys b -> R (xs ++ ys) (a, b)) ->
  parser_sound (Combinators.andbind p q) R.
Proof.
  intros Hp Hq Combine m bound input s Run.
  unfold Combinators.andbind in Run; simpl in Run.
  destruct (runParser p bound input) as [sa|] eqn:Ra; [|discriminate].
  simpl in Run.
  destruct (runParser
    (call (q (Success.value sa))
      (Nat.le_trans _ _ _ (Success.small sa) bound))
    (Nat.le_refl _) (Success.leftovers sa)) as [sb|] eqn:Rb;
    simpl in Run; [|discriminate].
  inversion Run; subst.
  destruct (Hp m bound input sa Ra) as [xs [Ex Px]].
  destruct (Hq (Success.value sa) _
    (Nat.le_trans _ _ _ (Success.small sa) bound)
    _ (Nat.le_refl _) (Success.leftovers sa) sb Rb) as [ys [Ey Py]].
  exists (xs ++ ys). split.
  - change (input_bytes input = (xs ++ ys) ++ output_bytes sb).
    rewrite Ex.
    change (xs ++ input_bytes (Success.leftovers sa) =
      (xs ++ ys) ++ output_bytes sb).
    rewrite Ey. apply app_assoc.
  - simpl. now apply Combine.
Qed.

Lemma parser_sound_bind {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : A -> Box (Parser (SizedList Byte.byte) Byte.byte option B) n)
    (P : list Byte.byte -> A -> Prop)
    (Q : A -> list Byte.byte -> B -> Prop)
    (R : list Byte.byte -> B -> Prop) :
  parser_sound p P ->
  (forall a k (lt : k < n), parser_sound (call (q a) lt) (Q a)) ->
  (forall xs ys a b, P xs a -> Q a ys b -> R (xs ++ ys) b) ->
  parser_sound (Combinators.bind p q) R.
Proof.
  intros Hp Hq Combine.
  unfold Combinators.bind.
  eapply parser_sound_map with
    (P := fun bs ab => R bs (snd ab)).
  - eapply parser_sound_andbind; eauto.
  - auto.
Qed.

Lemma parser_sound_app {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option (A -> B) n)
    (q : Box (Parser (SizedList Byte.byte) Byte.byte option A) n)
    (P : list Byte.byte -> (A -> B) -> Prop)
    (Q : list Byte.byte -> A -> Prop)
    (R : list Byte.byte -> B -> Prop) :
  parser_sound p P ->
  (forall k (lt : k < n), parser_sound (call q lt) Q) ->
  (forall xs ys f a, P xs f -> Q ys a -> R (xs ++ ys) (f a)) ->
  parser_sound (Combinators.app p q) R.
Proof.
  intros Hp Hq Combine.
  unfold Combinators.app.
  eapply parser_sound_bind with
    (P := P) (Q := fun f bs b => exists a, Q bs a /\ b = f a).
  - exact Hp.
  - intros f k lt. simpl.
    eapply parser_sound_map; [apply Hq |].
    intros bs a H. exists a. auto.
  - intros xs ys f b Hf [a [Ha E]]. subst b.
    now apply Combine.
Qed.

(** The recursion combinator uses structural recursion on an upper bound.
    Prove its invariant once, without assuming functional extensionality or
    equality of the different arithmetic proofs carried by parser results. *)
Lemma fix_box_invariant {A : nat -> Type}
    (step : forall n, Box A n -> A n) (I : forall n, A n -> Prop) :
  (forall n rec,
    (forall k (lt : k < n), I k (call rec lt)) -> I n (step n rec)) ->
  forall fuel k (lt : k < fuel), I k (call (FixBox step fuel) lt).
Proof.
  intro Step. induction fuel as [|fuel IH].
  - intros k lt. lia.
  - intros k lt. simpl. apply Step.
    intros j lower. apply IH.
Qed.

Lemma fix_invariant {A : nat -> Type}
    (step : forall n, Box A n -> A n) (I : forall n, A n -> Prop) :
  (forall n rec,
    (forall k (lt : k < n), I k (call rec lt)) -> I n (step n rec)) ->
  forall n, I n (Fix A step n).
Proof.
  intros Step n. unfold Fix, extract.
  now apply fix_box_invariant.
Qed.

Lemma run_parser_sound {A}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_sound (p n) P) ->
  forall bs a,
    @binary_format_parser.run option _ _ _ _ Byte.byte
      binary_format_parser.tokBytes A bs p = Some a ->
    P bs a.
Proof.
  intros H bs a R.
  apply run_option_has_no_leftovers in R.
  destruct R as [s [Raw [V Empty]]].
  destruct (H _ _ (Nat.le_refl _) (mkSizedList bs) s Raw)
    as [prefix [Bytes Parsed]].
  change (bs = prefix ++ output_bytes s) in Bytes.
  unfold output_bytes, input_bytes in Bytes. rewrite Empty, app_nil_r in Bytes.
  subst prefix. now rewrite V in Parsed.
Qed.
