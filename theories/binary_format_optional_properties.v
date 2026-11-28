(** Byte grammar of production optional section composition. *)
From Stdlib Require Import List Arith.
From parseque Require Import Parseque.
From Wasm Require Import binary_parser_combinator_properties.

Definition optional_encoding {A} (P : list Byte.byte -> A -> Prop)
    bs value :=
  match value with Some a => P bs a | None => bs = nil end.

Lemma parser_sound_andmbind {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : A -> Box (Parser (SizedList Byte.byte) Byte.byte option B) n)
    (P : list Byte.byte -> A -> Prop)
    (Q : A -> list Byte.byte -> B -> Prop)
    (R : list Byte.byte -> A * option B -> Prop) :
  parser_sound p P ->
  (forall a k (lt : k < n), parser_sound (call (q a) lt) (Q a)) ->
  (forall xs ys a b,
    P xs a -> optional_encoding (Q a) ys b ->
    R (xs ++ ys) (a, b)) ->
  parser_sound (Combinators.andmbind p q) R.
Proof.
  intros Hp Hq Combine m bound input s Run.
  unfold Combinators.andmbind in Run; simpl in Run.
  destruct (runParser p bound input) as [sa|] eqn:Ra; [|discriminate].
  simpl in Run.
  destruct (runParser
    (call (q (Success.value sa))
      (Nat.le_trans _ _ _ (Success.small sa) bound))
    (Nat.le_refl _) (Success.leftovers sa)) as [sb|] eqn:Rb;
    simpl in Run; inversion Run; subst.
  - destruct (Hp _ _ _ _ Ra) as [xs [Ex Px]].
    destruct (Hq (Success.value sa) _
      (Nat.le_trans _ _ _ (Success.small sa) bound)
      _ (Nat.le_refl _) (Success.leftovers sa) sb Rb) as [ys [Ey Py]].
    exists (xs ++ ys). split.
    + change (input_bytes input = (xs ++ ys) ++ output_bytes sb).
      rewrite Ex.
      change (xs ++ input_bytes (Success.leftovers sa) =
        (xs ++ ys) ++ output_bytes sb).
      rewrite Ey; apply app_assoc.
    + simpl. apply Combine; [exact Px |exact Py].
  - destruct (Hp _ _ _ _ Ra) as [xs [Ex Px]].
    exists xs; split; [exact Ex |].
    replace xs with (xs ++ nil) at 1 by apply app_nil_r.
    apply Combine; [exact Px |reflexivity].
Qed.

Lemma parser_sound_andm {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : Box (Parser (SizedList Byte.byte) Byte.byte option B) n) P Q R :
  parser_sound p P ->
  (forall k (lt : k < n), parser_sound (call q lt) Q) ->
  (forall xs ys a b, P xs a -> optional_encoding Q ys b ->
    R (xs ++ ys) (a, b)) ->
  parser_sound (Combinators.andm p q) R.
Proof.
  intros Hp Hq Combine. unfold Combinators.andm.
  eapply parser_sound_andmbind; [exact Hp | |exact Combine].
  intros a k lt; apply Hq.
Qed.
