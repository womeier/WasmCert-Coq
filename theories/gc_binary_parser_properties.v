(** Correspondence of the exported GC reference decoder with the actual
    option/Parseque binary-parser path and the declarative binary grammar.
    The final module-level shared reference representation remains separate. *)
From Stdlib Require Import List.
From parseque Require Import Parseque.
From Wasm Require Import gc_types gc_binary binary_format_parser
  binary_format_printer binary_parser_combinator_properties.
From Wasm Require Import binary_parser_lookahead_properties.

Definition abstract_heap_prefix bs h :=
  exists b, bs = b :: nil /\ abstract_heap_encoding b h.

Definition abstract_reference_prefix bs t :=
  abstract_reference_encoding bs t nil.

Lemma parse_gc_abstract_heap_sound n :
  parser_sound
    (@parse_gc_abstract_heap_type (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    abstract_heap_prefix.
Proof.
  unfold parse_gc_abstract_heap_type.
  eapply parser_sound_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_sound_anyTok.
  - intros bs b h E D.
    exists b. split; [exact E | now apply decode_abstract_heap_correct].
Qed.

Lemma parse_gc_abstract_heap_complete n :
  parser_complete
    (@parse_gc_abstract_heap_type (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    abstract_heap_prefix.
Proof.
  unfold parse_gc_abstract_heap_type.
  eapply parser_complete_guardM with (P := fun bs b => bs = b :: nil).
  - apply parser_complete_anyTok.
  - intros bs h [b [E D]].
    exists b. split; [exact E | now apply decode_abstract_heap_correct].
Qed.

Lemma parse_gc_abstract_heap_fixed_complete n b h :
  abstract_heap_encoding b h ->
  parser_complete
    (@parse_gc_abstract_heap_type (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs value => bs = b :: nil /\ value = h).
Proof.
  intro Encoded.
  eapply parser_complete_weaken; [apply parse_gc_abstract_heap_complete|].
  intros bs value [Bytes Value]; subst bs value.
  exists b; auto.
Qed.

Lemma parse_gc_explicit_reference_fixed_complete n nullable b h :
  abstract_heap_encoding b h ->
  parser_complete
    ((fun heap => {| art_nullable := nullable; art_heap := heap |}) <$>
      ((@exact_byte (SizedList Byte.byte) _ option _ _ _ _ _ _
        (if nullable then Byte.x63 else Byte.x64) n) &>
        parse_gc_abstract_heap_type))
    (fun bs value =>
      bs = (if nullable then Byte.x63 else Byte.x64) :: b :: nil /\
      value = {| art_nullable := nullable; art_heap := h |}).
Proof.
  intro Encoded.
  eapply parser_complete_map with
    (P := fun bs heap =>
      bs = (if nullable then Byte.x63 else Byte.x64) :: b :: nil /\ heap = h).
  - apply parser_complete_prefix_byte with
      (Q := fun bs heap => bs = b :: nil /\ heap = h).
    + intros k lt; simpl. apply parser_complete_le_lower.
      now apply parse_gc_abstract_heap_fixed_complete.
    + intros bs heap [Bytes Value]. exists (b :: nil); auto.
  - intros bs value [Bytes Value]. exists h; auto.
Qed.

Theorem parse_gc_abstract_reference_prefix_complete n :
  parser_complete
    (@parse_gc_abstract_reference_type
      (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    (fun bs reference => abstract_reference_encoding bs reference nil).
Proof.
  intros m bound input prefix suffix reference Bytes Encoded.
  inversion Encoded as [b h rest Heap|b h rest Heap|b h rest Heap]; subst.
  - assert (Complete : parser_complete
      (@parse_gc_abstract_reference_type
        (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      (fun bs value => bs = b :: nil /\
        value = {| art_nullable := true; art_heap := h |})).
    { unfold parse_gc_abstract_reference_type.
      eapply parser_complete_alt_right_initial with
        (expected := Byte.x63) (actual := b).
      - apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
      - destruct Heap; discriminate.
      - intros bs value [Head _]; exists nil; exact Head.
      - eapply parser_complete_alt_right_initial with
          (expected := Byte.x64) (actual := b).
        + apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
        + destruct Heap; discriminate.
        + intros bs value [Head _]; exists nil; exact Head.
        + eapply parser_complete_map with
            (P := fun bs value => bs = b :: nil /\ value = h).
          * exact (parse_gc_abstract_heap_fixed_complete n b h Heap).
          * intros bs value [Head Value]; exists h; auto. }
    apply (Complete m bound input _ suffix _ Bytes); auto.
  - assert (Complete : parser_complete
      (@parse_gc_abstract_reference_type
        (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      (fun bs value => bs = Byte.x63 :: b :: nil /\
        value = {| art_nullable := true; art_heap := h |})).
    { unfold parse_gc_abstract_reference_type.
      apply parser_complete_alt_left.
      exact (parse_gc_explicit_reference_fixed_complete n true b h Heap). }
    apply (Complete m bound input _ suffix _ Bytes); auto.
  - assert (Complete : parser_complete
      (@parse_gc_abstract_reference_type
        (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
      (fun bs value => bs = Byte.x64 :: b :: nil /\
        value = {| art_nullable := false; art_heap := h |})).
    { unfold parse_gc_abstract_reference_type.
      eapply parser_complete_alt_right_initial with
        (expected := Byte.x63) (actual := Byte.x64).
      - apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
      - discriminate.
      - intros bs value [Head _]; exists (b :: nil); exact Head.
      - apply parser_complete_alt_left.
        exact (parse_gc_explicit_reference_fixed_complete n false b h Heap). }
    apply (Complete m bound input _ suffix _ Bytes); auto.
Qed.

Lemma parse_gc_explicit_reference_sound n nullable :
  parser_sound
    ((fun h => {| art_nullable := nullable; art_heap := h |}) <$>
      ((@exact_byte (SizedList Byte.byte) _ option _ _ _ _ _ _
          (if nullable then Byte.x63 else Byte.x64) n) &>
        parse_gc_abstract_heap_type))
    abstract_reference_prefix.
Proof.
  eapply parser_sound_map with
    (P := fun bytes h => exists b,
      bytes = (if nullable then Byte.x63 else Byte.x64) :: b :: nil /\
      abstract_heap_encoding b h).
  - change (parser_sound
      (Combinators.bind
        (@exact_byte (SizedList Byte.byte) _ option _ _ _ _ _ _
          (if nullable then Byte.x63 else Byte.x64) n)
        (fun _ => box parse_gc_abstract_heap_type))
      (fun bytes h => exists b,
        bytes = (if nullable then Byte.x63 else Byte.x64) :: b :: nil /\
        abstract_heap_encoding b h)).
    eapply parser_sound_bind with
      (P := fun bs x =>
        bs = (if nullable then Byte.x63 else Byte.x64) :: nil /\
        x = (if nullable then Byte.x63 else Byte.x64))
      (Q := fun _ => abstract_heap_prefix).
    + apply parser_sound_exact_byte.
    + intros x k lt. simpl.
      apply parser_sound_le_lower. apply parse_gc_abstract_heap_sound.
    + intros xs ys x h [E V] [b [F D]].
      subst xs ys. exists b. auto.
  - intros bs h [b [E D]]. subst bs.
    destruct nullable; unfold abstract_reference_prefix; now constructor.
Qed.

Theorem parse_gc_abstract_reference_sound n :
  parser_sound
    (@parse_gc_abstract_reference_type
      (SizedList Byte.byte) _ option _ _ _ _ _ _ n)
    abstract_reference_prefix.
Proof.
  unfold parse_gc_abstract_reference_type.
  apply parser_sound_alt; [apply parse_gc_explicit_reference_sound |].
  apply parser_sound_alt; [apply parse_gc_explicit_reference_sound |].
  eapply parser_sound_map; [apply parse_gc_abstract_heap_sound |].
  intros bs h [b [E D]]. subst bs.
  unfold abstract_reference_prefix. now constructor.
Qed.

Lemma abstract_reference_encoding_suffix prefix t rest :
  abstract_reference_prefix prefix t ->
  abstract_reference_encoding (prefix ++ rest) t rest.
Proof.
  unfold abstract_reference_prefix.
  intro E; inversion E; subst; simpl; now constructor.
Qed.

Theorem run_parse_gc_abstract_reference_sound bs t rest :
  run_parse_gc_abstract_reference_type bs = Some (t, rest) ->
  abstract_reference_encoding bs t rest.
Proof.
  unfold run_parse_gc_abstract_reference_type. intro R.
  apply (run_parse_prefix_sound _
    abstract_reference_prefix parse_gc_abstract_reference_sound) in R.
  destruct R as [prefix [E P]]. subst bs.
  now apply abstract_reference_encoding_suffix.
Qed.

Theorem run_parse_gc_abstract_reference_complete bs t rest :
  abstract_reference_encoding bs t rest ->
  run_parse_gc_abstract_reference_type bs = Some (t, rest).
Proof.
  intro E. destruct E; destruct H; reflexivity.
Qed.

Theorem run_parse_gc_abstract_reference_correct bs t rest :
  run_parse_gc_abstract_reference_type bs = Some (t, rest) <->
  abstract_reference_encoding bs t rest.
Proof.
  split; [apply run_parse_gc_abstract_reference_sound |
          apply run_parse_gc_abstract_reference_complete].
Qed.

(** This pointwise correspondence justifies replacing the standalone decoder
    export with the Parseque parser while preserving suffix/error behavior. *)
Theorem gc_reference_parseque_correspondence bs :
  run_parse_gc_abstract_reference_type bs = decode_abstract_reference bs.
Proof.
  destruct (run_parse_gc_abstract_reference_type bs) as [[t rest]|] eqn:R.
  - apply run_parse_gc_abstract_reference_sound in R.
    apply decode_abstract_reference_complete in R. symmetry. exact R.
  - destruct (decode_abstract_reference bs) as [[t rest]|] eqn:D;
      [|reflexivity].
    apply decode_abstract_reference_sound in D.
    apply run_parse_gc_abstract_reference_complete in D. congruence.
Qed.

Theorem gc_reference_parseque_roundtrip t rest :
  run_parse_gc_abstract_reference_type (encode_abstract_reference t ++ rest) =
  Some (t, rest).
Proof.
  rewrite gc_reference_parseque_correspondence.
  apply abstract_reference_codec_roundtrip.
Qed.

(** The actual main reference-type parser now reuses the proved fragment,
    mapping its results into the shared representation. *)
Theorem shared_reference_parser_correspondence bs :
  run_parse_prefix (fun _ => parse_reference_type) bs =
  option_map
    (fun '(t, rest) => (shared_reference_of_abstract t, rest))
    (decode_abstract_reference bs).
Proof.
  unfold parse_reference_type.
  rewrite run_parse_prefix_map.
  change
    (option_map
      (fun '(t, rest) => (shared_reference_of_abstract t, rest))
      (run_parse_gc_abstract_reference_type bs) =
     option_map
      (fun '(t, rest) => (shared_reference_of_abstract t, rest))
      (decode_abstract_reference bs)).
  now rewrite gc_reference_parseque_correspondence.
Qed.

Theorem shared_reference_parser_correct bs rt rest :
  run_parse_prefix (fun _ => parse_reference_type) bs = Some (rt, rest) <->
  exists t, rt = shared_reference_of_abstract t /\
    abstract_reference_encoding bs t rest.
Proof.
  rewrite shared_reference_parser_correspondence.
  split.
  - destruct (decode_abstract_reference bs) as [[t suffix]|] eqn:D;
      [|discriminate].
    intro E; inversion E; subst.
    exists t. split; [reflexivity | now apply decode_abstract_reference_sound].
  - intros [t [E Encoding]]. subst rt.
    apply decode_abstract_reference_complete in Encoding.
    rewrite Encoding. reflexivity.
Qed.

Lemma shared_reference_printer_correspondence t :
  binary_of_reference_type (shared_reference_of_abstract t) =
  encode_abstract_reference t.
Proof. destruct t as [nullable h]; destruct nullable, h; reflexivity. Qed.

Theorem shared_reference_codec_roundtrip t rest :
  run_parse_prefix (fun _ => parse_reference_type)
    (binary_of_reference_type (shared_reference_of_abstract t) ++ rest) =
  Some (shared_reference_of_abstract t, rest).
Proof.
  rewrite shared_reference_printer_correspondence,
    shared_reference_parser_correspondence, abstract_reference_codec_roundtrip.
  reflexivity.
Qed.
