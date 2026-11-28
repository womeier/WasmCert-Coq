(** Nonrecursive grammar combinators factored from the pinned module handoff.
    All execution proofs use the existing shared parser contracts. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties.
Local Notation byte := Byte.byte.

Definition mapped_encoding {A B} (f : A -> B) (P : list byte -> A -> Prop) bytes value :=
  exists a, P bytes a /\ value = f a.
Definition sequence_encoding {A B} (P : list byte -> A -> Prop)
    (Q : list byte -> B -> Prop) bytes (value : A * B) :=
  exists xs ys, bytes = xs ++ ys /\ P xs (fst value) /\ Q ys (snd value).
Definition application_encoding {A B} (P : list byte -> (A -> B) -> Prop)
    (Q : list byte -> A -> Prop) bytes value :=
  exists xs ys f a, bytes = xs ++ ys /\ P xs f /\ Q ys a /\ value = f a.
Definition tagged_encoding {A} tag (P : list byte -> A -> Prop) bytes value :=
  exists body, bytes = tag :: body /\ P body value.

Lemma grammar_sound_map {A B n} (f : A -> B)
    (p : Parser (SizedList byte) byte option A n) P :
  parser_sound p P -> parser_sound (Combinators.map f p) (mapped_encoding f P).
Proof.
  intro Sound; eapply parser_sound_map; [exact Sound |].
  intros bytes value E; exists value; auto.
Qed.

Lemma grammar_complete_map {A B n} (f : A -> B)
    (p : Parser (SizedList byte) byte option A n) P :
  parser_complete p P -> parser_complete (Combinators.map f p) (mapped_encoding f P).
Proof.
  intro Complete; eapply parser_complete_map; [exact Complete |].
  intros bytes value Encoding; exact Encoding.
Qed.

Lemma grammar_sound_app {A B n}
    (p : Parser (SizedList byte) byte option (A -> B) n)
    (q : Parser (SizedList byte) byte option A n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound (Combinators.app p (box q)) (application_encoding P Q).
Proof.
  intros Pp Qq; eapply parser_sound_app with (P := P) (Q := Q); [exact Pp | |].
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros xs ys f a Pf Qa; exists xs, ys, f, a; auto.
Qed.

Lemma grammar_complete_app {A B n}
    (p : Parser (SizedList byte) byte option (A -> B) n)
    (q : Parser (SizedList byte) byte option A n) P Q :
  parser_complete p P -> parser_complete q Q ->
  parser_complete (Combinators.app p (box q)) (application_encoding P Q).
Proof.
  intros Pp Qq; eapply parser_complete_app with (P := P) (Q := Q); [exact Pp | |].
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes value Encoding; exact Encoding.
Qed.

Lemma grammar_sound_sequence {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound (Combinators.and p (box q)) (sequence_encoding P Q).
Proof.
  intros Pp Qq; unfold Combinators.and.
  eapply parser_sound_andbind with (P := P) (Q := fun _ => Q); [exact Pp | |].
  - intros a k lt; simpl; now apply parser_sound_le_lower.
  - intros xs ys a b Pa Qb; exists xs, ys; auto.
Qed.

Lemma grammar_complete_sequence {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Parser (SizedList byte) byte option B n) P Q :
  parser_complete p P -> parser_complete q Q ->
  parser_complete (Combinators.and p (box q)) (sequence_encoding P Q).
Proof.
  intros Pp Qq; unfold Combinators.and.
  eapply parser_complete_andbind with (P := P) (Q := fun _ => Q); [exact Pp | |].
  - intros a k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes a b Encoding; exact Encoding.
Qed.

Lemma grammar_sound_tag {A n} tag
    (p : Parser (SizedList byte) byte option A n) P :
  parser_sound p P ->
  parser_sound (Combinators.rand (exact_byte tag) (box p)) (tagged_encoding tag P).
Proof.
  intro Sound; apply parser_sound_prefix_byte with (Q := P).
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros bytes value E; exists bytes; auto.
Qed.

Lemma grammar_complete_tag {A n} tag
    (p : Parser (SizedList byte) byte option A n) P :
  parser_complete p P ->
  parser_complete (Combinators.rand (exact_byte tag) (box p)) (tagged_encoding tag P).
Proof.
  intro Complete; apply parser_complete_prefix_byte with (Q := P).
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes value Encoding; exact Encoding.
Qed.

Lemma grammar_complete_choice {A n}
    (p q : Parser (SizedList byte) byte option A n) P Q :
  parser_sound p P ->
  parser_complete p P -> parser_complete q Q ->
  (forall xs ys tail1 tail2 a b,
    P xs a -> Q ys b -> xs ++ tail1 = ys ++ tail2 -> False) ->
  parser_complete (Combinators.alt p q) (fun bs value => P bs value \/ Q bs value).
Proof.
  intros Sound Left Right Disjoint m bound input prefix suffix value Bytes E.
  destruct E as [E|E].
  - eapply parser_complete_alt_left; [exact Left |exact Bytes |exact E].
  - eapply parser_complete_alt_right;
      [exact Sound |exact Right |exact Disjoint |exact Bytes |exact E].
Qed.
