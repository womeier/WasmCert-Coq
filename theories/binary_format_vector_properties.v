(** Byte-grammar properties of the production vector combinators.
    These are prerequisites for recursive expression/section proofs, not a
    claim of whole-module correctness. *)
From Stdlib Require Import List ZArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_parser_combinator_properties
  leb128_properties binary_format_parser_properties addressing addressing_binary
  addressing_parseque utf8.

Inductive encoded_items {A} (P : list Byte.byte -> A -> Prop) :
    list Byte.byte -> list A -> Prop :=
| encoded_items_nil : encoded_items P nil nil
| encoded_items_cons : forall xs ys a rest,
    P xs a -> encoded_items P ys rest ->
    encoded_items P (xs ++ ys) (a :: rest).

Lemma encoded_items_app {A} (P : list Byte.byte -> A -> Prop) xs ys a b :
  encoded_items P xs a -> encoded_items P ys b ->
  encoded_items P (xs ++ ys) (a ++ b).
Proof.
  intros H; revert ys b. induction H; intros zs b Tail; simpl.
  - exact Tail.
  - rewrite <- app_assoc. constructor; auto.
Qed.

Lemma parse_u32_bounded_prefix_sound n :
  parser_sound (parse_u32_as_N (Toks := SizedList Byte.byte) (M := option) (n := n))
    (fun bs x => unsigned_leb bs x /\
      (x <= 4294967295)%N /\ length bs <= 5).
Proof.
  intros m bound input s R.
  pose proof (parse_u32_as_N_prefix_correspondence bound input) as E.
  rewrite R in E.
  unfold AddressingParseque.flatten in E; simpl in E.
  symmetry in E.
  apply AddressingBinary.decode_address_spec in E.
  destruct E as [Range [prefix [Bytes [Width Encoding]]]].
  exists prefix; split; [exact Bytes |].
  split; [now apply unsigned_leb_addressing |].
  split; [|exact Width].
  change (Success.value s < 4294967296)%N in Range; lia.
Qed.

Lemma parse_vec_aux_positive_sound {A} p :
  forall n (f : Parser (SizedList Byte.byte) Byte.byte option A n) P,
  parser_sound f P ->
  parser_sound (parse_vec_aux_positive f p)
    (fun bs values => encoded_items P bs values /\
      length values = Pos.to_nat p).
Proof.
  induction p as [p IH|p IH|]; intros n f P Hf; simpl.
  - eapply parser_sound_map with
      (P := fun bs pair => exists xs ys zs a l1 l2,
        bs = xs ++ (ys ++ zs) /\ pair = (a, (l1, l2)) /\
        P xs a /\ encoded_items P ys l1 /\ encoded_items P zs l2 /\
        length l1 = Pos.to_nat p /\ length l2 = Pos.to_nat p).
    + eapply parser_sound_andbind with (P := P)
        (Q := fun _ bs pair => exists ys zs l1 l2,
          bs = ys ++ zs /\ pair = (l1, l2) /\
          encoded_items P ys l1 /\ encoded_items P zs l2 /\
          length l1 = Pos.to_nat p /\ length l2 = Pos.to_nat p).
      * exact Hf.
      * intros a k lt; simpl.
        apply parser_sound_le_lower.
        eapply parser_sound_andbind.
        -- apply IH; exact Hf.
        -- intros l j lower; simpl.
           apply parser_sound_le_lower. apply IH; exact Hf.
        -- intros ys zs l1 l2 [E1 L1] [E2 L2].
           exists ys, zs, l1, l2. repeat split; assumption || reflexivity.
      * intros xs rest a [l1 l2] Pa
          [ys [zs [v1 [v2 [Bytes [Values Facts]]]]]].
        inversion Values; subst.
        exists xs, ys, zs, a, v1, v2. auto.
    + intros bs [a [l1 l2]]
        [xs [ys [zs [v [v1 [v2 [Bytes [Values [Pa [E1 [E2 [L1 L2]]]]]]]]]]]].
      inversion Values; subst; simpl. split.
      * constructor; [exact Pa | now apply encoded_items_app].
      * rewrite length_app, L1, L2, Pos2Nat.inj_xI. lia.
  - eapply parser_sound_map with
      (P := fun bs pair => exists xs ys l1 l2,
        bs = xs ++ ys /\ pair = (l1, l2) /\
        encoded_items P xs l1 /\ encoded_items P ys l2 /\
        length l1 = Pos.to_nat p /\ length l2 = Pos.to_nat p).
    + eapply parser_sound_andbind.
      * apply IH; exact Hf.
      * intros l k lt; simpl.
        apply parser_sound_le_lower. apply IH; exact Hf.
      * intros xs ys l1 l2 [E1 L1] [E2 L2].
        exists xs, ys, l1, l2. repeat split; assumption || reflexivity.
    + intros bs [l1 l2]
        [xs [ys [v1 [v2 [Bytes [Values [E1 [E2 [L1 L2]]]]]]]]].
      inversion Values; subst; simpl. split.
      * now apply encoded_items_app.
      * rewrite length_app, L1, L2, Pos2Nat.inj_xO. lia.
  - eapply parser_sound_map; [exact Hf |].
    intros bs a Pa; split; [|reflexivity].
    rewrite <- (app_nil_r bs). constructor; [exact Pa | constructor].
Qed.

Lemma parse_vec_aux_sound {A} n
    (f : Parser (SizedList Byte.byte) Byte.byte option A n) P k :
  parser_sound f P ->
  parser_sound (parse_vec_aux f k)
    (fun bs values => encoded_items P bs values /\
      N.of_nat (length values) = k).
Proof.
  intro Hf. destruct k as [|p].
  - intros m bound input s R. discriminate.
  - eapply parser_sound_weaken.
    + apply parse_vec_aux_positive_sound; exact Hf.
    + intros bs values [E L]. split; [exact E |].
      rewrite L. apply positive_nat_N.
Qed.

Definition vector_encoding {A} (P : list Byte.byte -> A -> Prop)
    bs (values : list A) : Prop :=
  exists header body,
    bs = header ++ body /\
    unsigned_leb header (N.of_nat (length values)) /\
    (N.of_nat (length values) <= 4294967295)%N /\
    length header <= 5 /\ encoded_items P body values.

Theorem parse_vec_sound {A} n
    (f : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_sound f P ->
  parser_sound (parse_vec f) (vector_encoding P).
Proof.
  intro Hf. unfold parse_vec. apply parser_sound_alt.
  - eapply parser_sound_guardM.
    + apply parse_u32_bounded_prefix_sound.
    + intros bs k values [Encoding [Range Width]] E.
      destruct (N.eqb k 0) eqn:Zero; [|discriminate].
      apply N.eqb_eq in Zero; subst k.
      inversion E; subst. exists bs, nil.
      rewrite app_nil_r. repeat split; auto; constructor.
  - eapply parser_sound_bind with
      (P := fun bs k => unsigned_leb bs k /\
        (k <= 4294967295)%N /\ length bs <= 5)
      (Q := fun k bs values => encoded_items P bs values /\
        N.of_nat (length values) = k).
    + apply parse_u32_bounded_prefix_sound.
    + intros k j lt; simpl. apply parser_sound_le_lower.
      apply parse_vec_aux_sound; exact Hf.
    + intros header body k values [Encoding [Range Width]] [Items Count].
      exists header, body. rewrite Count. auto.
Qed.

Theorem run_vec_sound {A}
    (f : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_sound (f n) P) ->
  forall bs values, run bs (fun n => parse_vec (f n)) = Some values ->
    vector_encoding P bs values.
Proof.
  intro H. apply run_parser_sound.
  intro n. apply parse_vec_sound; apply H.
Qed.

Lemma encoded_raw_bytes bs values :
  encoded_items (fun xs b => xs = b :: nil) bs values ->
  bs = values.
Proof.
  intro E. induction E.
  - reflexivity.
  - subst xs. simpl. now rewrite IHE.
Qed.

Theorem parse_raw_bytes_sound n k :
  parser_sound
    (parse_vec_aux
      (@anyTok (SizedList Byte.byte) Byte.byte _ option _ _ _ n) k)
    (fun bs values => bs = values /\ N.of_nat (length bs) = k).
Proof.
  eapply parser_sound_weaken.
  - apply parse_vec_aux_sound. apply parser_sound_anyTok.
  - intros bs values [Items Count].
    apply encoded_raw_bytes in Items. subst; auto.
Qed.

(** Names in the actual module grammar consume one bounded u32 header and
    exactly that many raw bytes; successful names satisfy the production
    UTF-8 checker.  This includes legally padded length headers. *)
Theorem parse_name_sound n :
  parser_sound (parse_name (Toks := SizedList Byte.byte) (M := option) (n := n))
    (fun bs name => utf8_valid name = true /\
      exists header, bs = header ++ name /\
        unsigned_leb header (N.of_nat (length name)) /\
        (N.of_nat (length name) <= 4294967295)%N /\ length header <= 5).
Proof.
  unfold parse_name. eapply parser_sound_guardM.
  - apply parse_vec_sound. apply parser_sound_anyTok.
  - intros bs raw name
      [header [body [Bytes [Encoding [Range [Width Items]]]]]] R.
    destruct (utf8_valid raw) eqn:Valid; [|discriminate].
    inversion R; subst name.
    apply encoded_raw_bytes in Items; subst body.
    split; [exact Valid |]. exists header. auto.
Qed.
