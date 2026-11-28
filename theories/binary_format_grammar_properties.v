(** Parser-independent grammar algebra for actual source declaration/record
    composition. These relations contain no parser-success conditions. *)
From Stdlib Require Import List Strings.Byte Arith.
From parseque Require Import Parseque.
From Wasm Require Import binary_format_parser binary_format_parser_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_vector_properties.
Local Notation byte := Byte.byte.

Definition wire_map {A B} (f : A -> B) (P : list byte -> A -> Prop) bytes b :=
  exists a, P bytes a /\ b = f a.
Definition wire_app {A B} (P : list byte -> (A -> B) -> Prop)
    (Q : list byte -> A -> Prop) bytes b :=
  exists xs ys f a, bytes = xs ++ ys /\ P xs f /\ Q ys a /\ b = f a.
Definition wire_pair {A B} (P : list byte -> A -> Prop)
    (Q : list byte -> B -> Prop) bytes (pair : A * B) :=
  exists xs ys, bytes = xs ++ ys /\ P xs (fst pair) /\ Q ys (snd pair).
Definition wire_tag {A} tag (P : list byte -> A -> Prop) bytes a :=
  exists body, bytes = tag :: body /\ P body a.
Definition wire_fixed {A} (tag : byte) (a : A) bytes value :=
  bytes = tag :: nil /\ value = a.
Definition wire_choice {A} (P Q : list byte -> A -> Prop) bytes a :=
  P bytes a \/ Q bytes a.
Definition parser_codec {A n} (p : byte_parser (Toks := SizedList byte) (M := option) A n) P :=
  parser_sound p P /\ parser_complete p P.

Lemma grammar_initial_map {A B n}
    (p : byte_parser A n) (f : A -> B) Allowed :
  parser_initial_set p Allowed ->
  parser_initial_set (Combinators.map f p) Allowed.
Proof.
  intros Initial m bound input s Run.
  unfold Combinators.map in Run; simpl in Run.
  destruct (runParser p bound input) as [raw|] eqn:Raw; [|discriminate].
  exact (Initial _ _ _ _ Raw).
Qed.

Lemma wire_map_codec {A B n} (f : A -> B) (p : byte_parser A n) P :
  parser_codec p P -> parser_codec (Combinators.map f p) (wire_map f P).
Proof.
  intros [Sound Complete]; split.
  - eapply parser_sound_map; [exact Sound |].
    intros bytes a Enc; exists a; auto.
  - eapply parser_complete_map; [exact Complete |].
    intros bytes b Enc; exact Enc.
Qed.

Lemma wire_app_codec {A B n} (p : byte_parser (A -> B) n) (q : byte_parser A n) P Q :
  parser_codec p P -> parser_codec q Q ->
  parser_codec (Combinators.app p (box q)) (wire_app P Q).
Proof.
  intros [PS PC] [QS QC]; split.
  - eapply parser_sound_app with (P := P) (Q := Q); [exact PS | |].
    + intros k lt; simpl; now apply parser_sound_le_lower.
    + intros xs ys f a Pf Qa; exists xs, ys, f, a; auto.
  - eapply parser_complete_app with (P := P) (Q := Q); [exact PC | |].
    + intros k lt; simpl; now apply parser_complete_le_lower.
    + intros bytes b Enc; exact Enc.
Qed.

Lemma wire_pair_codec {A B n} (p : byte_parser A n) (q : byte_parser B n) P Q :
  parser_codec p P -> parser_codec q Q ->
  parser_codec (Combinators.and p (box q)) (wire_pair P Q).
Proof.
  intros [PS PC] [QS QC]; split; unfold Combinators.and.
  - eapply parser_sound_andbind with (P := P) (Q := fun _ => Q); [exact PS | |].
    + intros a k lt; simpl; now apply parser_sound_le_lower.
    + intros xs ys a b Pa Qb; exists xs, ys; auto.
  - eapply parser_complete_andbind with (P := P) (Q := fun _ => Q); [exact PC | |].
    + intros a k lt; simpl; now apply parser_complete_le_lower.
    + intros bytes a b Enc; exact Enc.
Qed.

Lemma wire_tag_codec {A n} tag (p : byte_parser A n) P :
  parser_codec p P ->
  parser_codec (Combinators.rand (exact_byte tag) (box p)) (wire_tag tag P).
Proof.
  intros [Sound Complete]; split.
  - apply parser_sound_prefix_byte with (Q := P).
    + intros k lt; simpl; now apply parser_sound_le_lower.
    + intros bytes a Enc; exists bytes; auto.
  - apply parser_complete_prefix_byte with (Q := P).
    + intros k lt; simpl; now apply parser_complete_le_lower.
    + intros bytes a Enc; exact Enc.
Qed.

Lemma wire_fixed_codec {A n} tag (a : A) :
  parser_codec
    (Combinators.cmap a (exact_byte (Toks := SizedList byte) (M := option) (n := n) tag))
    (wire_fixed tag a).
Proof.
  split.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bytes b [Bytes _]; split; auto.
  - unfold Combinators.cmap.
    eapply parser_complete_map; [apply parser_complete_exact_byte |].
    intros bytes b [Bytes ->]; exists tag; auto.
Qed.

Lemma wire_vec_codec {A n} (p : forall k, byte_parser A k) P :
  (forall k, parser_codec (p k) P) ->
  parser_codec (parse_vec (p n)) (vector_encoding P).
Proof.
  intro Codec; split.
  - apply parse_vec_sound; exact (proj1 (Codec n)).
  - apply parse_vec_complete; exact (proj2 (Codec n)).
Qed.

Lemma wire_choice_codec {A n}
    (p q : byte_parser A n) P Q Left Right :
  parser_codec p P -> parser_codec q Q ->
  parser_initial_set p Left -> parser_initial_set q Right ->
  (forall b, Left b -> Right b -> False) ->
  parser_codec (Combinators.alt p q) (wire_choice P Q).
Proof.
  intros [PS PC] [QS QC] InitialP InitialQ Different; split.
  - apply parser_sound_alt.
    + eapply parser_sound_weaken; [exact PS |]; intros bytes a Enc; now left.
    + eapply parser_sound_weaken; [exact QS |]; intros bytes a Enc; now right.
  - intros m bound input prefix suffix a Bytes Enc.
    destruct Enc as [Enc|Enc].
    + eapply parser_complete_alt_left; [exact PC |exact Bytes |exact Enc].
    + destruct (QC m bound input prefix suffix a Bytes Enc) as [s [Run Facts]].
      assert (Absent : runParser p bound input = None).
      { destruct (runParser p bound input) as [raw|] eqn:Raw; [|reflexivity].
        destruct (InitialP _ _ _ _ Raw) as [b [tail [Input Member]]].
        destruct (InitialQ _ _ _ _ Run) as [c [rest [Input' Member']]].
        rewrite Input in Input'; inversion Input'; subst c.
        exfalso; exact (Different b Member Member'). }
      exists s; split; [now rewrite run_alt_option, Absent |exact Facts].
Qed.
