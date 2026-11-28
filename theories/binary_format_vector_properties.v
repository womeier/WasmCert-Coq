(** Byte-grammar properties of the production vector combinators.
    These are prerequisites for recursive expression/section proofs, not a
    claim of whole-module correctness. *)
From Stdlib Require Import List ZArith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_parser_combinator_properties
  leb128_properties binary_format_parser_properties addressing addressing_binary
  addressing_parseque utf8 binary_format_printer leb128_unsigned_printer_properties.
From Wasm Require binary_format_properties.

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

Lemma encoded_items_split {A} (P : list Byte.byte -> A -> Prop) a b bs :
  encoded_items P bs (a ++ b) ->
  exists xs ys, bs = xs ++ ys /\
    encoded_items P xs a /\ encoded_items P ys b.
Proof.
  revert bs. induction a as [|a rest IH]; intros bs E.
  - exists nil, bs. simpl. repeat split; auto; constructor.
  - inversion E as [|head tail v vs Item Items]; subst.
    destruct (IH _ Items) as [xs [ys [Bytes [Left Right]]]].
    exists (head ++ xs), ys.
    rewrite Bytes, app_assoc. split; [reflexivity |].
    split; [constructor; assumption | exact Right].
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

Lemma encoded_items_halves {A} (P : list Byte.byte -> A -> Prop) bs values k :
  encoded_items P bs values -> length values = k + k ->
  exists xs ys l1 l2,
    bs = xs ++ ys /\ values = l1 ++ l2 /\
    encoded_items P xs l1 /\ encoded_items P ys l2 /\
    length l1 = k /\ length l2 = k.
Proof.
  intros Items Count.
  rewrite <- (firstn_skipn k values) in Items.
  destruct (encoded_items_split P _ _ _ Items)
    as [xs [ys [Bytes [Left Right]]]].
  exists xs, ys, (firstn k values), (skipn k values).
  repeat split; auto using firstn_skipn.
  - rewrite length_firstn, Count. lia.
  - rewrite length_skipn, Count. lia.
Qed.

Lemma parse_vec_aux_positive_complete {A} p :
  forall n (f : Parser (SizedList Byte.byte) Byte.byte option A n) P,
  parser_complete f P ->
  parser_complete (parse_vec_aux_positive f p)
    (fun bs values => encoded_items P bs values /\
      length values = Pos.to_nat p).
Proof.
  induction p as [p IH|p IH|]; intros n f P Hf; simpl.
  - eapply parser_complete_map with
      (P := fun bs pair => exists xs ys zs a l1 l2,
        bs = xs ++ (ys ++ zs) /\ pair = (a, (l1, l2)) /\
        P xs a /\ encoded_items P ys l1 /\ encoded_items P zs l2 /\
        length l1 = Pos.to_nat p /\ length l2 = Pos.to_nat p).
    + eapply parser_complete_andbind with (P := P)
        (Q := fun _ bs pair => exists ys zs l1 l2,
          bs = ys ++ zs /\ pair = (l1, l2) /\
          encoded_items P ys l1 /\ encoded_items P zs l2 /\
          length l1 = Pos.to_nat p /\ length l2 = Pos.to_nat p).
      * exact Hf.
      * intros a k lt; simpl. apply parser_complete_le_lower.
        eapply parser_complete_andbind.
        -- apply IH; exact Hf.
        -- intros l j lower; simpl.
           apply parser_complete_le_lower. apply IH; exact Hf.
        -- intros bs l1 l2
             [ys [zs [v1 [v2 [Bytes [Values Facts]]]]]].
           inversion Values; subst.
           exists ys, zs. tauto.
      * intros bs a [l1 l2]
          [xs [ys [zs [v [v1 [v2 [Bytes [Values Facts]]]]]]]].
        inversion Values; subst.
        exists xs, (ys ++ zs). split; [reflexivity |].
        split; [tauto |].
        exists ys, zs, v1, v2. tauto.
    + intros bs values [Items Count].
      destruct values as [|a rest]; [simpl in Count; lia |].
      inversion Items as [|xs tail v vs Item Tail]; subst.
      assert (length rest = Pos.to_nat p + Pos.to_nat p) as RestCount.
      { rewrite Pos2Nat.inj_xI in Count; simpl in Count; lia. }
      destruct (encoded_items_halves P _ _ _ Tail RestCount)
        as [ys [zs [l1 [l2 [Bytes [Values Facts]]]]]].
      exists (a, (l1, l2)). split.
      * exists xs, ys, zs, a, l1, l2.
        repeat split; subst; tauto.
      * simpl. now rewrite Values.
  - eapply parser_complete_map with
      (P := fun bs pair => exists xs ys l1 l2,
        bs = xs ++ ys /\ pair = (l1, l2) /\
        encoded_items P xs l1 /\ encoded_items P ys l2 /\
        length l1 = Pos.to_nat p /\ length l2 = Pos.to_nat p).
    + eapply parser_complete_andbind.
      * apply IH; exact Hf.
      * intros l k lt; simpl.
        apply parser_complete_le_lower. apply IH; exact Hf.
      * intros bs l1 l2
          [xs [ys [v1 [v2 [Bytes [Values Facts]]]]]].
        inversion Values; subst.
        exists xs, ys. tauto.
    + intros bs values [Items Count].
      rewrite Pos2Nat.inj_xO in Count.
      destruct (encoded_items_halves P _ _ (Pos.to_nat p) Items ltac:(lia))
        as [xs [ys [l1 [l2 [Bytes [Values Facts]]]]]].
      exists (l1, l2). split.
      * exists xs, ys, l1, l2. tauto.
      * exact Values.
  - eapply parser_complete_map; [exact Hf |].
    intros bs values [Items Count].
    destruct values as [|a [|b rest]]; simpl in Count; try discriminate.
    inversion Items as [|xs tail v vs Item Tail]; subst.
    inversion Tail; subst.
    exists a. rewrite app_nil_r. auto.
Qed.

Definition vector_encoding {A} (P : list Byte.byte -> A -> Prop)
    bs (values : list A) : Prop :=
  exists header body,
    bs = header ++ body /\
    unsigned_leb header (N.of_nat (length values)) /\
    (N.of_nat (length values) <= 4294967295)%N /\
    length header <= 5 /\ encoded_items P body values.

Lemma parse_vec_aux_complete {A} n
    (f : Parser (SizedList Byte.byte) Byte.byte option A n) P k :
  k <> 0%N -> parser_complete f P ->
  parser_complete (parse_vec_aux f k)
    (fun bs values => encoded_items P bs values /\
      N.of_nat (length values) = k).
Proof.
  intros Nonzero Hf. destruct k as [|p]; [contradiction |].
  eapply parser_complete_weaken.
  - apply parse_vec_aux_positive_complete; exact Hf.
  - intros bs values [Items Count]. split; [exact Items |].
    apply (f_equal N.to_nat) in Count. now rewrite Nat2N.id in Count.
Qed.

Theorem parse_vec_complete {A} n
    (f : Parser (SizedList Byte.byte) Byte.byte option A n) P :
  parser_complete f P ->
  parser_complete (parse_vec f) (vector_encoding P).
Proof.
  intros Hf m bound input prefix suffix values Bytes
    [header [body [Parts [Encoding [Range [Width Items]]]]]].
  rewrite Parts, <- app_assoc in Bytes.
  destruct (parse_u32_prefix_complete n m bound input header (body ++ suffix)
    (N.of_nat (length values)) Bytes ltac:(repeat split; assumption))
    as [sa [Ra [Va Outa]]].
  destruct values as [|a rest].
  - inversion Items; subst body.
    exists (Success.map (fun _ : N => @nil A) sa).
    split.
    + unfold parse_vec, parse_vec_length. rewrite run_alt_option, run_guardM_option, Ra.
      unfold Success.guardM. rewrite Va. reflexivity.
    + split; [reflexivity |exact Outa].
  - assert (N.of_nat (length (a :: rest)) <> 0%N) as Nonzero by (simpl; lia).
    destruct (parse_vec_aux_complete n f P _ Nonzero Hf
      (Success.size sa)
      (Nat.le_trans _ _ _ (Nat.lt_le_incl _ _ (Success.small sa)) bound)
      (Success.leftovers sa) body suffix (a :: rest) Outa ltac:(split; [exact Items |reflexivity]))
      as [sb [Rb [Vb Outb]]].
    exists (Success.map snd (Success.and sa sb)).
    split.
    + unfold parse_vec, parse_vec_length. rewrite run_alt_option, run_guardM_option, Ra.
      unfold Success.guardM. rewrite Va. simpl.
      unfold Combinators.bind, Combinators.map, Combinators.andbind; simpl.
       simpl in Ra.
      rewrite Ra. simpl. rewrite Va.
      match goal with
      | |- context [runParser _ ?lower _] =>
        rewrite (Peano_dec.le_unique _ _ lower
          (Nat.le_trans _ _ _
            (Nat.lt_le_incl _ _ (Success.small sa)) bound))
      end.
      rewrite Rb. reflexivity.
    + split; [exact Vb |exact Outb].
Qed.

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

Theorem run_vec_complete {A}
    (f : forall n, Parser (SizedList Byte.byte) Byte.byte option A n) P :
  (forall n, parser_complete (f n) P) ->
  forall bs values, vector_encoding P bs values ->
    run bs (fun n => parse_vec (f n)) = Some values.
Proof.
  intro H. apply run_parser_complete.
  intro n. apply parse_vec_complete; apply H.
Qed.

Theorem binary_of_vec_roundtrip {A}
    (f : forall n, Parser (SizedList Byte.byte) Byte.byte option A n)
    (print : A -> list Byte.byte) P values :
  (forall n, parser_complete (f n) P) ->
  (forall a, In a values -> P (print a) a) ->
  (N.of_nat (length values) <= 4294967295)%N ->
  run (binary_of_vec print values) (fun n => parse_vec (f n)) = Some values.
Proof.
  intros Complete Prints Range.
  apply (run_vec_complete f P Complete).
  exists (leb128.encode_unsigned (N.of_nat (length values))),
    (concat (List.map print values)).
  split.
  { unfold binary_of_vec, binary_of_u32_nat.
    now rewrite binary_format_properties.binary_of_u32_arithmetic. }
  split; [apply encode_unsigned_sound |].
  split; [exact Range |]. split.
  - apply (encode_unsigned_length_bound 4).
    change (Z.of_N (N.of_nat (length values)) < 34359738368)%Z.
    apply N2Z.inj_le in Range. lia.
  - induction values as [|a rest IH]; simpl; [constructor |].
    constructor.
    + apply Prints; now left.
    + apply IH.
      * intros a' Member. apply Prints; now right.
      * simpl in Range; lia.
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
