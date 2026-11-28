(** Correspondence of the exported GC reference decoder with the actual
    option/Parseque binary-parser path and the declarative binary grammar.
    The final module-level shared reference representation remains separate. *)
From Stdlib Require Import List.
From parseque Require Import Parseque.
From Wasm Require Import datatypes gc_types gc_binary binary_format_parser
  binary_format_printer binary_parser_combinator_properties.

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

(** The main abstract-reference grammar includes the independent EH hierarchy
    as well as the GC fragment. Indexed heap types use the declaration parser. *)
Definition decode_supported_heap (b : Byte.byte) : option heap_type :=
  match b with
  | Byte.x69 => Some HT_exn
  | Byte.x74 => Some HT_noexn
  | _ => option_map shared_heap_of_abstract (decode_abstract_heap b)
  end.

Inductive shared_heap_encoding : Byte.byte -> heap_type -> Prop :=
| she_gc : forall b h, abstract_heap_encoding b h ->
    shared_heap_encoding b (shared_heap_of_abstract h)
| she_exn : shared_heap_encoding Byte.x69 HT_exn
| she_noexn : shared_heap_encoding Byte.x74 HT_noexn.

Lemma decode_supported_heap_correct b h :
  decode_supported_heap b = Some h <-> shared_heap_encoding b h.
Proof.
  split.
  - destruct b; simpl; intro E; try discriminate; inversion E; subst;
    first [apply she_exn | apply she_noexn |
      apply (she_gc _ AH_any) | apply (she_gc _ AH_eq) |
      apply (she_gc _ AH_i31) | apply (she_gc _ AH_struct) |
      apply (she_gc _ AH_array) | apply (she_gc _ AH_none) |
      apply (she_gc _ AH_func) | apply (she_gc _ AH_nofunc) |
      apply (she_gc _ AH_extern) | apply (she_gc _ AH_noextern)];
      try constructor.
  - intro E; destruct E; try reflexivity; destruct H; reflexivity.
Qed.

Definition read_supported_reference (nullable : bool) (bs : list Byte.byte) :
    option (reference_type * list Byte.byte) :=
  match bs with
  | nil => None
  | b :: rest => option_map (fun h => (Ref_type nullable h, rest))
      (decode_supported_heap b)
  end.

Definition decode_shared_reference (bs : list Byte.byte) :
    option (reference_type * list Byte.byte) :=
  match bs with
  | nil => None
  | Byte.x63 :: rest => read_supported_reference true rest
  | Byte.x64 :: rest => read_supported_reference false rest
  | _ => read_supported_reference true bs
  end.

Inductive shared_reference_encoding :
    list Byte.byte -> reference_type -> list Byte.byte -> Prop :=
| sre_short : forall b h rest, shared_heap_encoding b h ->
    shared_reference_encoding (b :: rest) (Ref_type true h) rest
| sre_nullable : forall b h rest, shared_heap_encoding b h ->
    shared_reference_encoding (Byte.x63 :: b :: rest) (Ref_type true h) rest
| sre_nonnull : forall b h rest, shared_heap_encoding b h ->
    shared_reference_encoding (Byte.x64 :: b :: rest) (Ref_type false h) rest.

Lemma read_supported_reference_correct nullable bs rt rest :
  read_supported_reference nullable bs = Some (rt, rest) <->
  exists b h, bs = b :: rest /\ shared_heap_encoding b h /\
    rt = Ref_type nullable h.
Proof.
  destruct bs as [|b tail]; simpl.
  - split; [discriminate | intros [b [h [E _]]]; discriminate].
  - destruct (decode_supported_heap b) as [h|] eqn:D; simpl.
    + split.
      * intro E; inversion E; subst. exists b, h.
        repeat split; auto. now apply decode_supported_heap_correct.
      * intros [b' [h' [E [Heap Ref]]]].
        inversion E; subst. apply decode_supported_heap_correct in Heap.
        rewrite D in Heap. inversion Heap; subst. reflexivity.
    + split; [discriminate |].
      intros [b' [h' [E [Heap Ref]]]].
      inversion E; subst. apply decode_supported_heap_correct in Heap. congruence.
Qed.

Lemma decode_shared_reference_correct bs rt rest :
  decode_shared_reference bs = Some (rt, rest) <->
  shared_reference_encoding bs rt rest.
Proof.
  split.
  - destruct bs as [|b tail]; [discriminate |].
    destruct b; simpl; try discriminate;
      try (intro E; inversion E; subst; apply sre_short;
        apply decode_supported_heap_correct; reflexivity);
      intro E; apply read_supported_reference_correct in E;
      destruct E as [b [h [Bytes [Heap Ref]]]]; subst;
      first [apply sre_nullable | apply sre_nonnull]; assumption.
  - intro E; destruct E; destruct H; try destruct H; reflexivity.
Qed.

Theorem shared_reference_parser_correspondence bs :
  run_parse_prefix (fun _ => parse_reference_type) bs =
  decode_shared_reference bs.
Proof.
  destruct bs as [|b tail]; [reflexivity |].
  destruct b; try reflexivity.
  all: destruct tail as [|b tail]; [reflexivity |]; destruct b; reflexivity.
Qed.

Theorem shared_reference_parser_correct bs rt rest :
  run_parse_prefix (fun _ => parse_reference_type) bs = Some (rt, rest) <->
  shared_reference_encoding bs rt rest.
Proof.
  rewrite shared_reference_parser_correspondence.
  apply decode_shared_reference_correct.
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
  rewrite shared_reference_parser_correspondence.
  destruct t as [nullable h]; destruct nullable, h; reflexivity.
Qed.

(** All four exception reference types use the actual main printer/parser,
    preserving an arbitrary following byte string. *)
Theorem exception_reference_codec_roundtrip nullable h rest :
  h = HT_exn \/ h = HT_noexn ->
  run_parse_prefix (fun _ => parse_reference_type)
    (binary_of_reference_type (Ref_type nullable h) ++ rest) =
  Some (Ref_type nullable h, rest).
Proof.
  intros [E|E]; subst h; rewrite shared_reference_parser_correspondence;
    destruct nullable; reflexivity.
Qed.

Theorem shared_reference_parser_consumes bs rt rest :
  run_parse_prefix (fun _ => parse_reference_type) bs = Some (rt, rest) ->
  exists prefix, bs = prefix ++ rest /\
    (length prefix = 1 \/ length prefix = 2).
Proof.
  rewrite shared_reference_parser_correct. intro E; destruct E.
  - exists (b :: nil). split; [reflexivity | now left].
  - exists (Byte.x63 :: b :: nil). split; [reflexivity | now right].
  - exists (Byte.x64 :: b :: nil). split; [reflexivity | now right].
Qed.
