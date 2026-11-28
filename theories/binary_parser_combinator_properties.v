(** Shared non-GC proof layer from 51ec3e8, 5e0002b and the common part of
    6fddcdf.  No GC reference codec or admitted module target is imported.

    Prefix soundness for the actual option/Parseque combinators.
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

Definition parser_complete {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) : Prop :=
  forall m (bound : m <= n) input prefix suffix a,
    input_bytes input = prefix ++ suffix ->
    P prefix a ->
    exists s,
      runParser p bound input = Some s /\
      Success.value s = a /\ output_bytes s = suffix.

Lemma parser_complete_weaken {A n} p (P Q : list Byte.byte -> A -> Prop) :
  @parser_complete A n p P ->
  (forall bs a, Q bs a -> P bs a) ->
  parser_complete p Q.
Proof.
  intros H Imp m bound input prefix suffix a E HP.
  eapply H; [exact E | now apply Imp].
Qed.

Lemma parser_complete_anyTok n :
  parser_complete (@anyTok (SizedList Byte.byte) Byte.byte _ option _ _ _ n)
    (fun bs b => bs = b :: nil).
Proof.
  intros m bound [bs L] prefix suffix a E P.
  subst prefix. simpl in E. subst bs.
  destruct m as [|m]; [discriminate |].
  unfold anyTok; simpl.
  eexists; repeat split; reflexivity.
Qed.

Lemma parser_complete_guardM {A B n} (f : A -> option B)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) (Q : list Byte.byte -> B -> Prop) :
  parser_complete p P ->
  (forall bs b, Q bs b -> exists a, P bs a /\ f a = Some b) ->
  parser_complete (Combinators.guardM f p) Q.
Proof.
  intros H Preimage m bound input prefix suffix b E Qb.
  destruct (Preimage prefix b Qb) as [a [Pa F]].
  destruct (H m bound input prefix suffix a E Pa) as [r [Raw [V Out]]].
  exists (Success.MkSuccess b (Success.small r) (Success.leftovers r)).
  split.
  - rewrite run_guardM_option, Raw.
    unfold Success.guardM. rewrite V, F. reflexivity.
  - split; [reflexivity | exact Out].
Qed.

Lemma parser_complete_map {A B n} (f : A -> B)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) (Q : list Byte.byte -> B -> Prop) :
  parser_complete p P ->
  (forall bs b, Q bs b -> exists a, P bs a /\ b = f a) ->
  parser_complete (Combinators.map f p) Q.
Proof.
  intros H Preimage m bound input prefix suffix b E Qb.
  destruct (Preimage prefix b Qb) as [a [Pa F]].
  destruct (H m bound input prefix suffix a E Pa) as [r [Raw [V Out]]].
  exists (Success.map f r).
  split.
  - unfold Combinators.map; simpl. now rewrite Raw.
  - split; [simpl; congruence | exact Out].
Qed.

Lemma parser_complete_alt_left {A n}
    (p q : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_complete p P -> parser_complete (Combinators.alt p q) P.
Proof.
  intros H m bound input prefix suffix a E Pa.
  destruct (H m bound input prefix suffix a E Pa) as [s [Raw Rest]].
  exists s. split; [rewrite run_alt_option, Raw; reflexivity | exact Rest].
Qed.

Lemma parser_complete_alt_right {A n}
    (p q : Parser (SizedList Byte.byte) Byte.byte option A n) P Q :
  parser_sound p P -> parser_complete q Q ->
  (forall xs ys tail1 tail2 a b,
    P xs a -> Q ys b -> xs ++ tail1 = ys ++ tail2 -> False) ->
  parser_complete (Combinators.alt p q) Q.
Proof.
  intros Hp Hq Disjoint m bound input prefix suffix a E Qa.
  destruct (Hq m bound input prefix suffix a E Qa) as [s [Raw Rest]].
  exists s. split; [|exact Rest].
  rewrite run_alt_option.
  destruct (runParser p bound input) as [r|] eqn:R; [|exact Raw].
  destruct (Hp m bound input r R) as [xs [Ex Px]].
  exfalso.
  apply (Disjoint xs prefix (output_bytes r) suffix (Success.value r) a Px Qa).
  now rewrite <- Ex.
Qed.

Lemma parser_complete_andbind {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : A -> Box (Parser (SizedList Byte.byte) Byte.byte option B) n)
    (P : list Byte.byte -> A -> Prop)
    (Q : A -> list Byte.byte -> B -> Prop)
    (R : list Byte.byte -> A * B -> Prop) :
  parser_complete p P ->
  (forall a k (lt : k < n), parser_complete (call (q a) lt) (Q a)) ->
  (forall bytes a b, R bytes (a, b) ->
    exists xs ys, bytes = xs ++ ys /\ P xs a /\ Q a ys b) ->
  parser_complete (Combinators.andbind p q) R.
Proof.
  intros Hp Hq Split m bound input prefix suffix [a b] E Rab.
  destruct (Split prefix a b Rab) as [xs [ys [Parts [Pa Qb]]]].
  rewrite Parts, <- app_assoc in E.
  destruct (Hp m bound input xs (ys ++ suffix) a E Pa)
    as [sa [Ra [Va Outa]]].
  rewrite <- Va in Qb.
  destruct (Hq (Success.value sa) _
    (Nat.le_trans _ _ _ (Success.small sa) bound)
    _ (Nat.le_refl _) (Success.leftovers sa) ys suffix b Outa Qb)
    as [sb [Rb [Vb Outb]]].
  exists (Success.and sa sb). split.
  - unfold Combinators.andbind; simpl.
    rewrite Ra. simpl. rewrite Rb. reflexivity.
  - split; [simpl; now rewrite Va, Vb | exact Outb].
Qed.

Lemma parser_complete_bind {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : A -> Box (Parser (SizedList Byte.byte) Byte.byte option B) n)
    (P : list Byte.byte -> A -> Prop)
    (Q : A -> list Byte.byte -> B -> Prop)
    (R : list Byte.byte -> B -> Prop) :
  parser_complete p P ->
  (forall a k (lt : k < n), parser_complete (call (q a) lt) (Q a)) ->
  (forall bytes b, R bytes b ->
    exists xs ys a, bytes = xs ++ ys /\ P xs a /\ Q a ys b) ->
  parser_complete (Combinators.bind p q) R.
Proof.
  intros Hp Hq Split m bound input prefix suffix b E Rb.
  destruct (Split prefix b Rb) as [xs [ys [a [Parts [Pa Qb]]]]].
  rewrite Parts, <- app_assoc in E.
  destruct (Hp m bound input xs (ys ++ suffix) a E Pa)
    as [sa [Ra [Va Outa]]].
  rewrite <- Va in Qb.
  destruct (Hq (Success.value sa) _
    (Nat.le_trans _ _ _ (Success.small sa) bound)
    _ (Nat.le_refl _) (Success.leftovers sa) ys suffix b Outa Qb)
    as [sb [Rb' [Vb Outb]]].
  exists (Success.map snd (Success.and sa sb)).
  split.
  - unfold Combinators.bind, Combinators.map, Combinators.andbind; simpl.
    rewrite Ra. simpl. rewrite Rb'. reflexivity.
  - split; [exact Vb | exact Outb].
Qed.

Lemma parser_complete_app {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option (A -> B) n)
    (q : Box (Parser (SizedList Byte.byte) Byte.byte option A) n)
    (P : list Byte.byte -> (A -> B) -> Prop)
    (Q : list Byte.byte -> A -> Prop)
    (R : list Byte.byte -> B -> Prop) :
  parser_complete p P ->
  (forall k (lt : k < n), parser_complete (call q lt) Q) ->
  (forall bytes b, R bytes b ->
    exists xs ys f a,
      bytes = xs ++ ys /\ P xs f /\ Q ys a /\ b = f a) ->
  parser_complete (Combinators.app p q) R.
Proof.
  intros Hp Hq Split.
  unfold Combinators.app.
  eapply parser_complete_bind with
    (P := P) (Q := fun f bs b => exists a, Q bs a /\ b = f a).
  - exact Hp.
  - intros f k lt. simpl.
    eapply parser_complete_map; [apply Hq |].
    auto.
  - intros bytes b Rb.
    destruct (Split bytes b Rb) as [xs [ys [f [a [E [Pf [Qa F]]]]]]].
    exists xs, ys, f. repeat split; auto. exists a. auto.
Qed.

Lemma parser_complete_le_lower {A m n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P (bound : m <= n) :
  parser_complete p P -> parser_complete (Combinators.le_lower bound p) P.
Proof.
  intros H k lower input prefix suffix a E Pa.
  unfold Combinators.le_lower; simpl.
  now apply (H k (Nat.le_trans _ _ _ lower bound) input prefix suffix a).
Qed.

Lemma parser_complete_extract {A}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_complete (p n) P) ->
  forall n, parser_complete (extract (fun n => box (p n)) n) P.
Proof.
  intros H n. unfold extract, box, le_close; simpl.
  apply parser_complete_le_lower. apply H.
Qed.

Lemma parser_complete_assert_sized {A n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n) P constraint :
  parser_complete p P ->
  (forall bs a, P bs a -> constraint (BinNat.N.of_nat (length bs)) = true) ->
  parser_complete (assert_sized p constraint) P.
Proof.
  intros H Width m bound input prefix suffix a E Pa.
  destruct (H m bound input prefix suffix a E Pa) as [s [Raw [V Out]]].
  exists s. split; [|auto].
  rewrite run_assert_sized_option, Raw.
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes s) = Success.size s) in Lout.
  rewrite E, length_app in Lin. rewrite Out in Lout.
  replace (m - Success.size s) with (length prefix) by lia.
  rewrite (Width prefix a Pa). reflexivity.
Qed.

Lemma run_parser_complete {A}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_complete (p n) P) ->
  forall bs a, P bs a ->
    @binary_format_parser.run option _ _ _ _ Byte.byte
      binary_format_parser.tokBytes A bs p = Some a.
Proof.
  intros H bs a Pa.
  destruct (H _ _ (Nat.le_refl _) (mkSizedList bs) bs nil a)
    as [s [Raw [V Out]]].
  - simpl. now rewrite app_nil_r.
  - exact Pa.
  - apply run_option_correct. exists s.
    split; [exact Raw |]. split; [exact V |].
    pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
    change (length (output_bytes s) = Success.size s) in Lout.
    rewrite Out in Lout. simpl in Lout. congruence.
Qed.

Lemma parser_sound_exact_byte b n :
  parser_sound (@exact_byte (SizedList Byte.byte) _ option _ _ _ _ _ _ b n)
    (fun bs x => bs = b :: nil /\ x = b).
Proof.
  unfold exact_byte.
  eapply parser_sound_guardM with (P := fun bs x => bs = x :: nil).
  - apply parser_sound_anyTok.
  - intros bs x y E F.
    unfold datatypes_properties.byte_eqb in F.
    destruct (Byte.byte_eq_dec x b) as [Eq|Neq]; simpl in F;
      [|discriminate].
    inversion F; subst. auto.
Qed.

Lemma parser_complete_exact_byte b n :
  parser_complete (@exact_byte (SizedList Byte.byte) _ option _ _ _ _ _ _ b n)
    (fun bs x => bs = b :: nil /\ x = b).
Proof.
  unfold exact_byte.
  eapply parser_complete_guardM with (P := fun bs x => bs = x :: nil).
  - apply parser_complete_anyTok.
  - intros bs x [E V]. subst x.
    exists b. split; [exact E |].
    unfold datatypes_properties.byte_eqb.
    destruct (Byte.byte_eq_dec b b); simpl; congruence.
Qed.

Lemma run_parse_prefix_sound {A}
    (p : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_sound (p n) P) ->
  forall bs a rest,
    run_parse_prefix p bs = Some (a, rest) ->
    exists prefix, bs = prefix ++ rest /\ P prefix a.
Proof.
  intros H bs a rest R.
  unfold run_parse_prefix in R.
  destruct (runParser (p (length bs)) (Nat.le_refl _) (mkSizedList bs))
    as [s|] eqn:Raw; [|discriminate].
  inversion R; subst.
  destruct (H _ _ (Nat.le_refl _) (mkSizedList bs) s Raw)
    as [prefix [E Pp]].
  exists prefix. auto.
Qed.
