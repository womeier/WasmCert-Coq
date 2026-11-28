(** Source declaration syntax, independent of validation and closed runtime
    descriptors. Indices here are signed-s33 source indices, never store IDs. *)
From Stdlib Require Import List Strings.Byte ZArith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes gc_types gc_binary
  binary_format_parser binary_format_printer
  binary_format_parser_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_language_properties
  binary_format_block_properties binary_format_type_properties
  binary_format_numeric_complete
  binary_format_section_properties
  binary_format_vector_properties gc_binary_parser_properties leb128 leb128_properties
  leb128_printer_properties.
Local Notation byte := Byte.byte.

Definition declaration_abstract_heap_encoding bs heap :=
  (exists abstract, abstract_heap_prefix bs abstract /\
    heap = shared_heap_of_abstract abstract) \/
  (bs = x69 :: nil /\ heap = HT_exn) \/
  (bs = x74 :: nil /\ heap = HT_noexn).

Definition declaration_heap_encoding bs heap :=
  declaration_abstract_heap_encoding bs heap \/
  exists index, block_index_encoding bs index /\ heap = HT_type index.

Inductive declaration_reference_encoding : list byte -> reference_type -> Prop :=
| declaration_reference_compact : forall bs heap,
    declaration_abstract_heap_encoding bs heap ->
    declaration_reference_encoding bs (Ref_type true heap)
| declaration_reference_explicit : forall bs (nullable : bool) heap,
    declaration_heap_encoding bs heap ->
    declaration_reference_encoding
      ((if nullable then x63 else x64) :: bs) (Ref_type nullable heap).

Definition declaration_value_encoding bs value :=
  match value with
  | T_num nt => bs = binary_of_number_type nt :: nil
  | T_vec vt => bs = binary_of_vector_type vt :: nil
  | T_ref reference => declaration_reference_encoding bs reference
  | T_bot => False
  end.

Lemma parse_declaration_abstract_heap_sound n :
  parser_sound
    (parse_declaration_abstract_heap_type
      (Toks := SizedList byte) (M := option) (n := n))
    declaration_abstract_heap_encoding.
Proof.
  unfold parse_declaration_abstract_heap_type.
  apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_map; [apply parse_gc_abstract_heap_sound|].
    intros bs abstract Encoding; left; exists abstract; auto.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; right; left; auto.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; right; right; auto.
Qed.

Lemma declaration_abstract_heap_head bs heap :
  declaration_abstract_heap_encoding bs heap ->
  exists first, bs = first :: nil /\ (101 <= Byte.to_N first < 123)%N.
Proof.
  intros [[abstract [[first [Bytes Heap]] Value]]|[[Bytes Value]|[Bytes Value]]].
  - exists first; split; [exact Bytes|].
    destruct Heap; vm_compute; split; congruence.
  - exists x69; split; [exact Bytes|].
    change (101 <= 105 < 123)%N; lia.
  - exists x74; split; [exact Bytes|].
    change (101 <= 116 < 123)%N; lia.
Qed.

Lemma parse_declaration_abstract_heap_complete n :
  parser_complete
    (parse_declaration_abstract_heap_type
      (Toks := SizedList byte) (M := option) (n := n))
    declaration_abstract_heap_encoding.
Proof.
  intros m bound input prefix suffix heap Bytes Encoding.
  destruct Encoding as [[abstract [Encoded Value]]|[Exn|NoExn]].
  - assert (Complete : parser_complete
      (parse_declaration_abstract_heap_type
        (Toks := SizedList byte) (M := option) (n := n))
      (fun bs heap => exists abstract, abstract_heap_prefix bs abstract /\
        heap = shared_heap_of_abstract abstract)).
    { unfold parse_declaration_abstract_heap_type.
      apply parser_complete_alt_left.
      eapply parser_complete_map; [apply parse_gc_abstract_heap_complete|].
      intros bs value [a [E V]]; exists a; auto. }
    apply (Complete m bound input prefix suffix heap Bytes).
    exists abstract; auto.
  - assert (Complete : parser_complete
      (parse_declaration_abstract_heap_type
        (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = x69 :: nil /\ value = HT_exn)).
    { unfold parse_declaration_abstract_heap_type.
      eapply parser_complete_alt_right with
        (P := fun bs heap => exists a, abstract_heap_prefix bs a /\
          heap = shared_heap_of_abstract a).
      - eapply parser_sound_map; [apply parse_gc_abstract_heap_sound|].
        intros bs a E; exists a; auto.
      - apply parser_complete_alt_left; apply fixed_instruction_complete.
      - intros xs ys tail1 tail2 a b
          [abstract [[first [X Heap]] _]] [Y _] Same.
        subst xs ys; destruct Heap; discriminate. }
    exact (Complete m bound input prefix suffix heap Bytes Exn).
  - assert (Complete : parser_complete
      (parse_declaration_abstract_heap_type
        (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = x74 :: nil /\ value = HT_noexn)).
    { unfold parse_declaration_abstract_heap_type.
      eapply parser_complete_alt_right with
        (P := fun bs heap => exists a, abstract_heap_prefix bs a /\
          heap = shared_heap_of_abstract a).
      - eapply parser_sound_map; [apply parse_gc_abstract_heap_sound|].
        intros bs a E; exists a; auto.
      - eapply parser_complete_alt_right_initial with
          (expected := x69) (actual := x74).
        + numeric_initial.
        + discriminate.
        + apply fixed_encoding_head.
        + apply fixed_instruction_complete.
      - intros xs ys tail1 tail2 a b
          [abstract [[first [X Heap]] _]] [Y _] Same.
        subst xs ys; destruct Heap; discriminate. }
    exact (Complete m bound input prefix suffix heap Bytes NoExn).
Qed.

Lemma parse_s33_sound n :
  parser_sound (parse_s33 (Toks := SizedList byte) (M := option) (n := n))
    (fun bs z => signed_leb bs z /\ length bs <= 5 /\
      (-4294967296 <= z <= 4294967295)%Z).
Proof.
  unfold parse_s33.
  eapply parser_sound_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 5).
  - intros m bound input s Run.
    apply assert_sized_option_correct in Run.
    destruct Run as [Run Width].
    destruct (parser_sound_extract parse_signed signed_leb parse_signed_sound
      n m bound input s Run) as [bs [Bytes Encoding]].
    exists bs; split; [exact Bytes|]. split; [exact Encoding|].
    pose proof (@Sized.sized _ _ _ input) as Lin.
    pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
    change (length (input_bytes input) = m) in Lin.
    change (length (output_bytes s) = Success.size s) in Lout.
    rewrite Bytes, length_app in Lin.
    apply N.leb_le in Width; lia.
  - intros bs z value [Encoded Width] Run.
    destruct (andb (Z.leb (-4294967296) z) (Z.leb z 4294967295))
      eqn:Range; [|discriminate].
    apply Bool.andb_true_iff in Range.
    destruct Range as [Lower Upper].
    apply Z.leb_le in Lower; apply Z.leb_le in Upper.
    inversion Run; subst; auto.
Qed.

Lemma parse_s33_complete n :
  parser_complete (parse_s33 (Toks := SizedList byte) (M := option) (n := n))
    (fun bs z => signed_leb bs z /\ length bs <= 5 /\
      (-4294967296 <= z <= 4294967295)%Z).
Proof.
  unfold parse_s33.
  eapply parser_complete_guardM with
    (P := fun bs z => signed_leb bs z /\ length bs <= 5).
  - apply parser_complete_assert_sized.
    + eapply parser_complete_weaken.
      * apply parser_complete_extract; exact parse_signed_complete.
      * intros bs z [Encoding _]; exact Encoding.
    + intros bs z [_ Width]; apply N.leb_le; lia.
  - intros bs z [Encoding [Width [Lower Upper]]].
    exists z; split; [auto|].
    assert (L : Z.leb (-4294967296) z = true) by (apply Z.leb_le; lia).
    assert (U : Z.leb z 4294967295 = true) by (apply Z.leb_le; lia).
    now rewrite L, U.
Qed.

Lemma parse_heap_typeidx_sound n :
  parser_sound (parse_heap_typeidx
    (Toks := SizedList byte) (M := option) (n := n)) block_index_encoding.
Proof.
  unfold parse_heap_typeidx.
  eapply parser_sound_guardM; [apply parse_s33_sound|].
  intros bs z index [Encoding [Width Range]] Run.
  destruct (Z.leb 0 z) eqn:Lower; [|discriminate].
  apply Z.leb_le in Lower; inversion Run; subst.
  unfold block_index_encoding; rewrite Z2N.id by assumption.
  repeat split; auto; lia.
Qed.

Lemma parse_heap_typeidx_complete n :
  parser_complete (parse_heap_typeidx
    (Toks := SizedList byte) (M := option) (n := n)) block_index_encoding.
Proof.
  unfold parse_heap_typeidx.
  eapply parser_complete_guardM; [apply parse_s33_complete|].
  intros bs index [Encoding [Range Width]].
  exists (Z.of_N index); split.
  - repeat split; auto; pose proof (N2Z.is_nonneg index); lia.
  - assert (Lower : Z.leb 0 (Z.of_N index) = true)
      by (apply Z.leb_le; apply N2Z.is_nonneg).
    now rewrite Lower, N2Z.id.
Qed.

Lemma parse_declaration_heap_sound n :
  parser_sound (parse_declaration_heap_type
    (Toks := SizedList byte) (M := option) (n := n))
    declaration_heap_encoding.
Proof.
  unfold parse_declaration_heap_type; apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply parse_declaration_abstract_heap_sound|].
    intros bs heap Encoding; now left.
  - eapply parser_sound_map; [apply parse_heap_typeidx_sound|].
    intros bs index Encoding; right; exists index; auto.
Qed.

Lemma parse_declaration_reference_sound n :
  parser_sound (parse_declaration_reference_type
    (Toks := SizedList byte) (M := option) (n := n))
    declaration_reference_encoding.
Proof.
  unfold parse_declaration_reference_type.
  apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_map with
      (P := fun bs heap => exists payload,
        bs = x63 :: payload /\ declaration_heap_encoding payload heap).
    + apply parser_sound_prefix_byte with (Q := declaration_heap_encoding).
      * intros k lt; simpl; apply parser_sound_le_lower;
          apply parse_declaration_heap_sound.
      * intros bs heap Encoding; exists bs; auto.
    + intros bs heap [payload [Bytes Encoding]]; subst bs.
      exact (declaration_reference_explicit payload true heap Encoding).
  - eapply parser_sound_map with
      (P := fun bs heap => exists payload,
        bs = x64 :: payload /\ declaration_heap_encoding payload heap).
    + apply parser_sound_prefix_byte with (Q := declaration_heap_encoding).
      * intros k lt; simpl; apply parser_sound_le_lower;
          apply parse_declaration_heap_sound.
      * intros bs heap Encoding; exists bs; auto.
    + intros bs heap [payload [Bytes Encoding]]; subst bs.
      exact (declaration_reference_explicit payload false heap Encoding).
  - eapply parser_sound_map; [apply parse_declaration_abstract_heap_sound|].
    intros bs heap Encoding; now apply declaration_reference_compact.
Qed.

Lemma parse_declaration_value_sound n :
  parser_sound (parse_declaration_value_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_value_encoding.
Proof.
  unfold parse_declaration_value_type.
  apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_map; [apply parse_number_type_sound|].
    intros bs nt Encoding; exact Encoding.
  - eapply parser_sound_map with
      (P := fun bs vt => bs = binary_of_vector_type vt :: nil).
    + unfold parse_vector_type.
      eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
      intros bs b [Bytes _]; exact Bytes.
    + intros bs vt Encoding; destruct vt; exact Encoding.
  - eapply parser_sound_map; [apply parse_declaration_reference_sound|].
    intros bs reference Encoding; exact Encoding.
Qed.

Lemma parse_declaration_heap_complete n :
  parser_complete (parse_declaration_heap_type
    (Toks := SizedList byte) (M := option) (n := n))
    declaration_heap_encoding.
Proof.
  intros m bound input prefix suffix heap Bytes Encoding.
  destruct Encoding as [Abstract|[index [Encoded Value]]].
  - assert (Complete : parser_complete
      (parse_declaration_heap_type (Toks := SizedList byte) (M := option) (n := n))
      declaration_abstract_heap_encoding).
    { unfold parse_declaration_heap_type.
      apply parser_complete_alt_left; apply parse_declaration_abstract_heap_complete. }
    exact (Complete m bound input prefix suffix heap Bytes Abstract).
  - assert (Complete : parser_complete
      (parse_declaration_heap_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bs heap => exists index,
        block_index_encoding bs index /\ heap = HT_type index)).
    { unfold parse_declaration_heap_type.
      eapply parser_complete_alt_right with
        (P := declaration_abstract_heap_encoding).
      - apply parse_declaration_abstract_heap_sound.
      - eapply parser_complete_map; [apply parse_heap_typeidx_complete|].
        intros bs value [i [E V]]; exists i; auto.
      - intros xs ys tail1 tail2 a b Abstract
          [i [[Signed [Range Width]] V]] Same.
        destruct (declaration_abstract_heap_head xs a Abstract)
          as [first [Head Bounds]]; subst xs.
        eapply (signed_nonnegative_disjoint_negative_byte _ _ first _ _).
        + exact Signed.
        + apply N2Z.is_nonneg.
        + lia.
        + symmetry; exact Same. }
    apply (Complete m bound input prefix suffix heap Bytes).
    exists index; auto.
Qed.

Lemma parse_declaration_explicit_reference_complete n nullable :
  parser_complete
    ((Ref_type nullable <$>
      ((@exact_byte (SizedList byte) _ option _ _ _ _ _ _
        (if nullable then x63 else x64) n) &> parse_declaration_heap_type)))
    (fun bs reference => exists payload heap,
      bs = (if nullable then x63 else x64) :: payload /\
      declaration_heap_encoding payload heap /\ reference = Ref_type nullable heap).
Proof.
  eapply parser_complete_map with
    (P := fun bs heap => exists payload,
      bs = (if nullable then x63 else x64) :: payload /\
      declaration_heap_encoding payload heap).
  - apply parser_complete_prefix_byte with (Q := declaration_heap_encoding).
    + intros k lt; simpl; apply parser_complete_le_lower;
        apply parse_declaration_heap_complete.
    + intros bs heap [payload Facts]; exists payload; exact Facts.
  - intros bs reference [payload [heap [Bytes [Encoding Value]]]].
    exists heap; split; [exists payload; auto|exact Value].
Qed.

Lemma parse_declaration_reference_complete n :
  parser_complete (parse_declaration_reference_type
    (Toks := SizedList byte) (M := option) (n := n))
    declaration_reference_encoding.
Proof.
  intros m bound input prefix suffix reference Bytes Encoding.
  destruct Encoding as [payload heap Abstract|payload nullable heap Encoded].
  - assert (Complete : parser_complete
      (parse_declaration_reference_type
        (Toks := SizedList byte) (M := option) (n := n))
      (fun bs reference => exists heap,
        declaration_abstract_heap_encoding bs heap /\ reference = Ref_type true heap)).
    { clear payload heap Abstract Bytes.
      unfold parse_declaration_reference_type.
      eapply parser_complete_alt_right with
        (P := fun bs reference => exists payload heap,
          bs = x63 :: payload /\ reference = Ref_type true heap).
      - eapply parser_sound_map with
          (P := fun bs heap => exists payload, bs = x63 :: payload).
        + apply parser_sound_prefix_byte with (Q := declaration_heap_encoding).
          * intros k lt; simpl; apply parser_sound_le_lower;
              apply parse_declaration_heap_sound.
          * intros bs heap E; exists bs; reflexivity.
        + intros bs heap [payload Head]; exists payload, heap; auto.
      - eapply parser_complete_alt_right with
          (P := fun bs reference => exists payload heap,
            bs = x64 :: payload /\ reference = Ref_type false heap).
        + eapply parser_sound_map with
            (P := fun bs heap => exists payload, bs = x64 :: payload).
          * apply parser_sound_prefix_byte with (Q := declaration_heap_encoding).
            -- intros k lt; simpl; apply parser_sound_le_lower;
                 apply parse_declaration_heap_sound.
            -- intros bs heap E; exists bs; reflexivity.
          * intros bs heap [payload Head]; exists payload, heap; auto.
        + eapply parser_complete_map; [apply parse_declaration_abstract_heap_complete|].
          intros bs value [heap [E V]]; exists heap; auto.
        + intros xs ys tail1 tail2 a b [payload [heap [X _]]]
            [h [Abstract _]] Same.
          destruct (declaration_abstract_heap_head ys h Abstract)
            as [first [Y Bounds]].
          subst xs ys; inversion Same; subst first.
          change (101 <= 100 < 123)%N in Bounds; lia.
      - intros xs ys tail1 tail2 a b [payload [heap [X _]]]
          [h [Abstract _]] Same.
        destruct (declaration_abstract_heap_head ys h Abstract)
          as [first [Y Bounds]].
        subst xs ys; inversion Same; subst first.
        change (101 <= 99 < 123)%N in Bounds; lia. }
    apply (Complete m bound input payload suffix _ Bytes); exists heap; auto.
  - destruct nullable.
    + assert (Complete : parser_complete
        (parse_declaration_reference_type
          (Toks := SizedList byte) (M := option) (n := n))
        (fun bs reference => exists payload heap,
          bs = x63 :: payload /\ declaration_heap_encoding payload heap /\
          reference = Ref_type true heap)).
      { clear payload heap Encoded Bytes.
        unfold parse_declaration_reference_type.
        apply parser_complete_alt_left.
        exact (parse_declaration_explicit_reference_complete n true). }
      apply (Complete m bound input _ suffix _ Bytes).
      exists payload, heap; auto.
    + assert (Complete : parser_complete
        (parse_declaration_reference_type
          (Toks := SizedList byte) (M := option) (n := n))
        (fun bs reference => exists payload heap,
          bs = x64 :: payload /\ declaration_heap_encoding payload heap /\
          reference = Ref_type false heap)).
      { clear payload heap Encoded Bytes.
        unfold parse_declaration_reference_type.
        eapply parser_complete_alt_right_initial with
          (expected := x63) (actual := x64).
        - numeric_initial.
        - discriminate.
        - intros bs value [payload [heap [Head _]]]; exists payload; exact Head.
        - apply parser_complete_alt_left.
          exact (parse_declaration_explicit_reference_complete n false). }
      apply (Complete m bound input _ suffix _ Bytes).
      exists payload, heap; auto.
Qed.

Lemma declaration_reference_head bs reference :
  declaration_reference_encoding bs reference ->
  exists first rest, bs = first :: rest /\ (99 <= Byte.to_N first < 123)%N.
Proof.
  intros Encoding; destruct Encoding as [bs heap Abstract|bs nullable heap Encoded].
  - destruct (declaration_abstract_heap_head bs heap Abstract) as [first [Head Bounds]].
    exists first, nil; split; [exact Head|lia].
  - exists (if nullable then x63 else x64), bs; split; [reflexivity|].
    destruct nullable; [change (99 <= 99 < 123)%N|change (99 <= 100 < 123)%N]; lia.
Qed.

Lemma parse_declaration_value_complete n :
  parser_complete (parse_declaration_value_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_value_encoding.
Proof.
  intros m bound input prefix suffix value Bytes Encoding.
  destruct value as [nt|vt|reference|]; [| | |contradiction].
  - assert (Complete : parser_complete
      (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = binary_of_number_type nt :: nil /\ value = T_num nt)).
    { unfold parse_declaration_value_type.
      apply parser_complete_alt_left.
      eapply parser_complete_map; [apply parse_number_type_complete|].
      intros bs value [E V]; exists nt; auto. }
    apply (Complete m bound input prefix suffix _ Bytes); auto.
  - destruct vt.
    assert (Complete : parser_complete
      (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = x7b :: nil /\ value = T_vec T_v128)).
    { unfold parse_declaration_value_type.
      eapply parser_complete_alt_right with
        (P := fun bs value => exists nt, bs = binary_of_number_type nt :: nil /\
          value = T_num nt).
      - eapply parser_sound_map; [apply parse_number_type_sound|].
        intros bs nt E; exists nt; auto.
      - apply parser_complete_alt_left.
        eapply parser_complete_map with
          (P := fun bs vt => bs = x7b :: nil /\ vt = T_v128).
        + unfold parse_vector_type; apply fixed_instruction_complete.
        + intros bs value [E V]; exists T_v128; auto.
      - intros xs ys tail1 tail2 a b [nt [X _]] [Y _] Same.
        subst xs ys; destruct nt; discriminate. }
    apply (Complete m bound input prefix suffix _ Bytes); auto.
  - assert (Complete : parser_complete
      (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => declaration_reference_encoding bs reference /\
        value = T_ref reference)).
    { unfold parse_declaration_value_type.
      eapply parser_complete_alt_right with
        (P := fun bs value => exists nt, bs = binary_of_number_type nt :: nil /\
          value = T_num nt).
      - eapply parser_sound_map; [apply parse_number_type_sound|].
        intros bs nt E; exists nt; auto.
      - eapply parser_complete_alt_right with
          (P := fun bs value => bs = x7b :: nil /\ value = T_vec T_v128).
        + eapply parser_sound_map with
            (P := fun bs vt => bs = binary_of_vector_type vt :: nil).
          * unfold parse_vector_type.
            eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
            intros bs b [E _]; exact E.
          * intros bs vt E; destruct vt; auto.
        + eapply parser_complete_map; [apply parse_declaration_reference_complete|].
          intros bs value [E V]; exists reference; auto.
        + intros xs ys tail1 tail2 a b [X _] [Y _] Same.
          destruct (declaration_reference_head ys reference Y) as [first [rest [Head Bounds]]].
          subst xs ys; inversion Same; subst first.
          change (99 <= 123 < 123)%N in Bounds; lia.
      - intros xs ys tail1 tail2 a b [nt [X _]] [Y _] Same.
        destruct (declaration_reference_head ys reference Y) as [first [rest [Head Bounds]]].
        subst xs ys; inversion Same; subst first.
        destruct nt;
          first [change (99 <= 127 < 123)%N in Bounds
                |change (99 <= 126 < 123)%N in Bounds
                |change (99 <= 125 < 123)%N in Bounds
                |change (99 <= 124 < 123)%N in Bounds]; lia. }
    apply (Complete m bound input prefix suffix _ Bytes); auto.
Qed.

(** Encoding constructors for finite declaration products. These reuse the
    shared combinator contracts; neither definition mentions a parser run. *)
Definition source_unary {A B} (make : A -> B) (P : list byte -> A -> Prop)
    bs value := exists a, P bs a /\ value = make a.

Definition source_binary {A B C} (make : A -> B -> C)
    (P : list byte -> A -> Prop) (Q : list byte -> B -> Prop) bs value :=
  exists xs ys a b, bs = xs ++ ys /\ P xs a /\ Q ys b /\ value = make a b.

Definition source_prefixed {A} opcode (P : list byte -> A -> Prop) bs value :=
  exists payload, bs = opcode :: payload /\ P payload value.

Lemma source_unary_sound {A B n} (make : A -> B)
    (p : byte_parser A n) P :
  parser_sound p P -> parser_sound (make <$> p) (source_unary make P).
Proof.
  intro Sound; eapply parser_sound_map; [exact Sound|].
  intros bs value Encoding; exists value; auto.
Qed.

Lemma source_unary_complete {A B n} (make : A -> B)
    (p : byte_parser A n) P :
  parser_complete p P -> parser_complete (make <$> p) (source_unary make P).
Proof.
  intro Complete; eapply parser_complete_map; [exact Complete|].
  intros bs value [a Facts]; exists a; exact Facts.
Qed.

Lemma source_binary_sound {A B C n} (make : A -> B -> C)
    (p : byte_parser A n) (q : byte_parser B n) P Q :
  parser_sound p P -> parser_sound q Q ->
  parser_sound ((make <$> p) <*> q) (source_binary make P Q).
Proof.
  intros Hp Hq.
  eapply parser_sound_app with (P := source_unary make P) (Q := Q).
  - now apply source_unary_sound.
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros xs ys f b [a [Pa Value]] Qb; subst f.
    exists xs, ys, a, b; auto.
Qed.

Lemma source_binary_complete {A B C n} (make : A -> B -> C)
    (p : byte_parser A n) (q : byte_parser B n) P Q :
  parser_complete p P -> parser_complete q Q ->
  parser_complete ((make <$> p) <*> q) (source_binary make P Q).
Proof.
  intros Hp Hq.
  eapply parser_complete_app with (P := source_unary make P) (Q := Q).
  - now apply source_unary_complete.
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bs value [xs [ys [a [b [Bytes [Pa [Qb Value]]]]]]].
    exists xs, ys, (make a), b; split; [exact Bytes|].
    split; [exists a; auto|auto].
Qed.

Lemma source_prefixed_sound {A n} opcode (p : byte_parser A n) P :
  parser_sound p P ->
  parser_sound (exact_byte opcode &> p) (source_prefixed opcode P).
Proof.
  intro Sound; apply parser_sound_prefix_byte with (Q := P).
  - intros k lt; simpl; now apply parser_sound_le_lower.
  - intros bs value Encoding; exists bs; auto.
Qed.

Lemma source_prefixed_complete {A n} opcode (p : byte_parser A n) P :
  parser_complete p P ->
  parser_complete (exact_byte opcode &> p) (source_prefixed opcode P).
Proof.
  intro Complete; apply parser_complete_prefix_byte with (Q := P).
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bs value Facts; exact Facts.
Qed.

Definition declaration_function_encoding :=
  source_prefixed x60
    (source_unary (uncurry Tf)
      (source_binary pair (vector_encoding declaration_value_encoding)
        (vector_encoding declaration_value_encoding))).

Definition declaration_mut_encoding bs mut :=
  (bs = x00 :: nil /\ mut = MUT_const) \/
  (bs = x01 :: nil /\ mut = MUT_var).

Definition declaration_storage_encoding bs storage :=
  (bs = x78 :: nil /\ storage = ST_packed PT_i8) \/
  (bs = x77 :: nil /\ storage = ST_packed PT_i16) \/
  source_unary ST_value declaration_value_encoding bs storage.

Definition declaration_field_encoding :=
  source_binary
    (fun storage mut => {| field_mutability := mut; field_storage := storage |})
    declaration_storage_encoding declaration_mut_encoding.

Definition declaration_composite_encoding bs composite :=
  source_unary Comp_func declaration_function_encoding bs composite \/
  source_prefixed x5f
    (source_unary Comp_struct (vector_encoding declaration_field_encoding)) bs composite \/
  source_prefixed x5e (source_unary Comp_array declaration_field_encoding) bs composite.

Definition declaration_subtype_encoding bs subtype :=
  source_binary (Sub_type false)
    (source_prefixed x50 (vector_encoding
      (fun bs x => unsigned_leb bs x /\ (x <= 4294967295)%N /\ length bs <= 5)))
    declaration_composite_encoding bs subtype \/
  source_binary (Sub_type true)
    (source_prefixed x4f (vector_encoding
      (fun bs x => unsigned_leb bs x /\ (x <= 4294967295)%N /\ length bs <= 5)))
    declaration_composite_encoding bs subtype \/
  source_unary (Sub_type true nil) declaration_composite_encoding bs subtype.

Definition declaration_recursive_encoding bs group :=
  source_prefixed x4e (vector_encoding declaration_subtype_encoding) bs group \/
  source_unary (fun subtype => subtype :: nil) declaration_subtype_encoding bs group.

Lemma parse_declaration_function_sound n :
  parser_sound (parse_function_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_function_encoding.
Proof.
  unfold parse_function_type, declaration_function_encoding.
  apply source_prefixed_sound; apply source_unary_sound.
  unfold Combinators.and.
  eapply parser_sound_andbind with
    (P := vector_encoding declaration_value_encoding)
    (Q := fun _ => vector_encoding declaration_value_encoding).
  - apply parse_vec_sound; apply parse_declaration_value_sound.
  - intros a k lt; simpl; apply parser_sound_le_lower.
    apply parse_vec_sound; apply parse_declaration_value_sound.
  - intros xs ys a b Pa Qb; exists xs, ys, a, b; auto.
Qed.

Lemma parse_declaration_function_complete n :
  parser_complete (parse_function_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_function_encoding.
Proof.
  unfold parse_function_type, declaration_function_encoding.
  apply source_prefixed_complete; apply source_unary_complete.
  unfold Combinators.and.
  eapply parser_complete_andbind with
    (P := vector_encoding declaration_value_encoding)
    (Q := fun _ => vector_encoding declaration_value_encoding).
  - apply parse_vec_complete; apply parse_declaration_value_complete.
  - intros a k lt; simpl; apply parser_complete_le_lower.
    apply parse_vec_complete; apply parse_declaration_value_complete.
  - intros bs a b [xs [ys [a' [b' [Bytes [Pa [Qb Value]]]]]]].
    inversion Value; subst a' b'; exists xs, ys; auto.
Qed.

Lemma parse_declaration_mut_sound n :
  parser_sound (parse_mut (Toks := SizedList byte) (M := option) (n := n))
    declaration_mut_encoding.
Proof.
  unfold parse_mut; apply parser_sound_alt.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; left; auto.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; right; auto.
Qed.

Lemma parse_declaration_storage_sound n :
  parser_sound (parse_storage_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_storage_encoding.
Proof.
  unfold parse_storage_type; apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; left; auto.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; right; left; auto.
  - eapply parser_sound_weaken; [apply source_unary_sound; apply parse_declaration_value_sound|].
    intros bs value Encoding; right; right; exact Encoding.
Qed.

Lemma parse_declaration_field_sound n :
  parser_sound (parse_field_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_field_encoding.
Proof.
  unfold parse_field_type, declaration_field_encoding; apply source_binary_sound.
  - apply parse_declaration_storage_sound.
  - apply parse_declaration_mut_sound.
Qed.

Lemma parse_declaration_composite_sound n :
  parser_sound (parse_composite_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_composite_encoding.
Proof.
  unfold parse_composite_type; apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_weaken;
      [apply source_unary_sound; apply parse_declaration_function_sound|].
    intros bs value Encoding; left; exact Encoding.
  - eapply parser_sound_weaken;
      [apply source_prefixed_sound; apply source_unary_sound;
       apply parse_vec_sound; apply parse_declaration_field_sound|].
    intros bs value Encoding; right; left; exact Encoding.
  - eapply parser_sound_weaken;
      [apply source_prefixed_sound; apply source_unary_sound;
       apply parse_declaration_field_sound|].
    intros bs value Encoding; right; right; exact Encoding.
Qed.

Lemma parse_declaration_subtype_sound n :
  parser_sound (parse_subtype (Toks := SizedList byte) (M := option) (n := n))
    declaration_subtype_encoding.
Proof.
  unfold parse_subtype; apply parser_sound_alt; [|apply parser_sound_alt].
  - eapply parser_sound_weaken.
    + apply source_binary_sound.
      * apply source_prefixed_sound; apply parse_vec_sound; apply parse_u32_bounded_prefix_sound.
      * apply parse_declaration_composite_sound.
    + intros bs value Encoding; left; exact Encoding.
  - eapply parser_sound_weaken.
    + apply source_binary_sound.
      * apply source_prefixed_sound; apply parse_vec_sound; apply parse_u32_bounded_prefix_sound.
      * apply parse_declaration_composite_sound.
    + intros bs value Encoding; right; left; exact Encoding.
  - eapply parser_sound_weaken;
      [apply source_unary_sound; apply parse_declaration_composite_sound|].
    intros bs value Encoding; right; right; exact Encoding.
Qed.

Theorem parse_recursive_type_source_sound n :
  parser_sound (parse_recursive_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_recursive_encoding.
Proof.
  unfold parse_recursive_type; apply parser_sound_alt.
  - eapply parser_sound_weaken;
      [apply source_prefixed_sound; apply parse_vec_sound; apply parse_declaration_subtype_sound|].
    intros bs value Encoding; left; exact Encoding.
  - eapply parser_sound_weaken;
      [apply source_unary_sound; apply parse_declaration_subtype_sound|].
    intros bs value Encoding; right; exact Encoding.
Qed.

Lemma source_alt_complete {A n} (p q : byte_parser A n) P Q :
  parser_sound p P -> parser_complete p P -> parser_complete q Q ->
  (forall xs ys tail1 tail2 a b,
    P xs a -> Q ys b -> xs ++ tail1 = ys ++ tail2 -> False) ->
  parser_complete (p <|> q) (fun bs value => P bs value \/ Q bs value).
Proof.
  intros Sound Left Right Disjoint m bound input prefix suffix value Bytes Encoding.
  destruct Encoding as [Encoding|Encoding].
  - apply (parser_complete_alt_left p q P Left m bound input prefix suffix value Bytes Encoding).
  - exact (parser_complete_alt_right p q P Q Sound Right Disjoint
      m bound input prefix suffix value Bytes Encoding).
Qed.

Lemma parse_declaration_mut_complete n :
  parser_complete (parse_mut (Toks := SizedList byte) (M := option) (n := n))
    declaration_mut_encoding.
Proof.
  unfold parse_mut; apply source_alt_complete.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; auto.
  - apply fixed_instruction_complete.
  - apply fixed_instruction_complete.
  - intros xs ys tail1 tail2 a b [X _] [Y _] Same.
    subst xs ys; discriminate.
Qed.

Lemma declaration_value_head bs value :
  declaration_value_encoding bs value ->
  exists first rest, bs = first :: rest /\
    ((99 <= Byte.to_N first < 117)%N \/ (123 <= Byte.to_N first <= 127)%N).
Proof.
  destruct value as [nt|vt|reference|]; simpl; intro Encoding; [| | |contradiction].
  - exists (binary_of_number_type nt), nil; split; [exact Encoding|].
    right; destruct nt; vm_compute; split; congruence.
  - destruct vt; exists x7b, nil; split; [exact Encoding|].
    right; change (123 <= 123 <= 127)%N; lia.
  - destruct Encoding as [bs heap Abstract|bs nullable heap Encoded].
    + destruct Abstract as [[abstract [[first [Head Heap]] Value]]|
        [[Head Value]|[Head Value]]].
      * exists first, nil; split; [exact Head|].
        left; destruct Heap; vm_compute; split; congruence.
      * exists x69, nil; split; [exact Head|].
        left; change (99 <= 105 < 117)%N; lia.
      * exists x74, nil; split; [exact Head|].
        left; change (99 <= 116 < 117)%N; lia.
    + exists (if nullable then x63 else x64), bs; split; [reflexivity|].
      left; destruct nullable;
        [change (99 <= 99 < 117)%N|change (99 <= 100 < 117)%N]; lia.
Qed.

Lemma parse_declaration_storage_complete n :
  parser_complete (parse_storage_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_storage_encoding.
Proof.
  unfold parse_storage_type.
  apply source_alt_complete.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
    intros bs b [Bytes _]; auto.
  - apply fixed_instruction_complete.
  - apply source_alt_complete.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte|].
      intros bs b [Bytes _]; auto.
    + apply fixed_instruction_complete.
    + apply source_unary_complete; apply parse_declaration_value_complete.
    + intros xs ys tail1 tail2 a b [X _] [value [E V]] Same.
      destruct (declaration_value_head ys value E) as [first [rest [Y Bounds]]].
      subst xs ys; inversion Same; subst first.
      change ((99 <= 119 < 117)%N \/ (123 <= 119 <= 127)%N) in Bounds; lia.
  - intros xs ys tail1 tail2 a b [X _] [[Y _]|[value [E V]]] Same.
    + subst xs ys; discriminate.
    + destruct (declaration_value_head ys value E) as [first [rest [Y Bounds]]].
      subst xs ys; inversion Same; subst first.
      change ((99 <= 120 < 117)%N \/ (123 <= 120 <= 127)%N) in Bounds; lia.
Qed.

Lemma parse_declaration_field_complete n :
  parser_complete (parse_field_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_field_encoding.
Proof.
  unfold parse_field_type, declaration_field_encoding; apply source_binary_complete.
  - apply parse_declaration_storage_complete.
  - apply parse_declaration_mut_complete.
Qed.

Lemma parse_declaration_composite_complete n :
  parser_complete (parse_composite_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_composite_encoding.
Proof.
  unfold parse_composite_type; apply source_alt_complete.
  - apply source_unary_sound; apply parse_declaration_function_sound.
  - apply source_unary_complete; apply parse_declaration_function_complete.
  - apply source_alt_complete.
    + apply source_prefixed_sound; apply source_unary_sound.
      apply parse_vec_sound; apply parse_declaration_field_sound.
    + apply source_prefixed_complete; apply source_unary_complete.
      apply parse_vec_complete; apply parse_declaration_field_complete.
    + apply source_prefixed_complete; apply source_unary_complete.
      apply parse_declaration_field_complete.
    + intros xs ys tail1 tail2 a b [payload [X _]] [payload' [Y _]] Same.
      subst xs ys; discriminate.
  - intros xs ys tail1 tail2 a b [ft [[payload [X _]] _]]
      [[payload' [Y _]]|[payload' [Y _]]] Same; subst xs ys; discriminate.
Qed.

Lemma declaration_composite_head bs composite :
  declaration_composite_encoding bs composite ->
  exists first rest, bs = first :: rest /\
    (first = x60 \/ first = x5f \/ first = x5e).
Proof.
  intros [[ft [[payload [Head _]] _]]|[[payload [Head _]]|[payload [Head _]]]].
  - exists x60, payload; auto.
  - exists x5f, payload; auto.
  - exists x5e, payload; auto.
Qed.

Lemma parse_declaration_subtype_complete n :
  parser_complete (parse_subtype (Toks := SizedList byte) (M := option) (n := n))
    declaration_subtype_encoding.
Proof.
  unfold parse_subtype; apply source_alt_complete.
  - apply source_binary_sound.
    + apply source_prefixed_sound; apply parse_vec_sound; apply parse_u32_bounded_prefix_sound.
    + apply parse_declaration_composite_sound.
  - apply source_binary_complete.
    + apply source_prefixed_complete; apply parse_vec_complete; apply parse_u32_prefix_complete.
    + apply parse_declaration_composite_complete.
  - apply source_alt_complete.
    + apply source_binary_sound.
      * apply source_prefixed_sound; apply parse_vec_sound; apply parse_u32_bounded_prefix_sound.
      * apply parse_declaration_composite_sound.
    + apply source_binary_complete.
      * apply source_prefixed_complete; apply parse_vec_complete; apply parse_u32_prefix_complete.
      * apply parse_declaration_composite_complete.
    + apply source_unary_complete; apply parse_declaration_composite_complete.
    + intros xs ys tail1 tail2 a b
        [prefix [suffix [supers [comp [X [[payload [Head _]] _]]]]]]
        [comp' [E V]] Same.
      destruct (declaration_composite_head ys comp' E) as [first [rest [Y Choices]]].
      subst xs prefix ys; simpl in Same; inversion Same; subst first.
      destruct Choices as [C|[C|C]]; discriminate.
  - intros xs ys tail1 tail2 a b
      [prefix [suffix [supers [comp [X [[payload [Head _]] _]]]]]]
      [[prefix' [suffix' [supers' [comp' [Y [[payload' [Head' _]] _]]]]]]|
       [comp' [E V]]] Same.
    + subst xs prefix ys prefix'; discriminate.
    + destruct (declaration_composite_head ys comp' E) as [first [rest [Y Choices]]].
      subst xs prefix ys; simpl in Same; inversion Same; subst first.
      destruct Choices as [C|[C|C]]; discriminate.
Qed.

Lemma declaration_subtype_head bs subtype :
  declaration_subtype_encoding bs subtype ->
  exists first rest, bs = first :: rest /\
    (first = x50 \/ first = x4f \/ first = x60 \/ first = x5f \/ first = x5e).
Proof.
  intros [[prefix [suffix [supers [comp [Bytes [[payload [Head _]] _]]]]]]|
    [[prefix [suffix [supers [comp [Bytes [[payload [Head _]] _]]]]]]|
     [comp [E V]]]].
  - exists x50, (payload ++ suffix); subst bs prefix; auto.
  - exists x4f, (payload ++ suffix); subst bs prefix; auto.
  - destruct (declaration_composite_head bs comp E) as [first [rest [Head Choices]]].
    exists first, rest; split; [exact Head|tauto].
Qed.

Theorem parse_recursive_type_source_complete n :
  parser_complete (parse_recursive_type (Toks := SizedList byte) (M := option) (n := n))
    declaration_recursive_encoding.
Proof.
  unfold parse_recursive_type; apply source_alt_complete.
  - apply source_prefixed_sound; apply parse_vec_sound; apply parse_declaration_subtype_sound.
  - apply source_prefixed_complete; apply parse_vec_complete; apply parse_declaration_subtype_complete.
  - apply source_unary_complete; apply parse_declaration_subtype_complete.
  - intros xs ys tail1 tail2 a b [payload [X _]] [subtype [E V]] Same.
    destruct (declaration_subtype_head ys subtype E) as [first [rest [Y Choices]]].
    subst xs ys; inversion Same; subst first.
    destruct Choices as [C|[C|[C|[C|C]]]]; discriminate.
Qed.

Definition declaration_type_section_encoding :=
  source_prefixed x01
    (section_payload_encoding (vector_encoding declaration_recursive_encoding)).

Theorem parse_typesec_source_sound n :
  parser_sound (parse_typesec (Toks := SizedList byte) (M := option) (n := n))
    declaration_type_section_encoding.
Proof.
  unfold parse_typesec, declaration_type_section_encoding.
  apply source_prefixed_sound; apply parse_section_payload_sound.
  apply parse_vec_sound; apply parse_recursive_type_source_sound.
Qed.

Theorem parse_typesec_source_complete n :
  parser_complete (parse_typesec (Toks := SizedList byte) (M := option) (n := n))
    declaration_type_section_encoding.
Proof.
  unfold parse_typesec, declaration_type_section_encoding.
  apply source_prefixed_complete; apply parse_section_payload_complete.
  apply parse_vec_complete; apply parse_recursive_type_source_complete.
Qed.

Definition declaration_heap_binary_wf heap :=
  match heap with HT_type index => (index <= 4294967295)%N | _ => True end.

Definition declaration_value_binary_wf value :=
  match value with
  | T_num _ | T_vec _ => True
  | T_ref reference => declaration_heap_binary_wf (ref_heap reference)
  | T_bot => False
  end.

Lemma binary_of_declaration_abstract_heap_encoding heap :
  (forall index, heap <> HT_type index) ->
  declaration_abstract_heap_encoding (binary_of_heap_type heap) heap.
Proof.
  intro Abstract.
  destruct heap; cbn [binary_of_heap_type];
    try (left; eexists; split;
      [eexists; split; [reflexivity|constructor]|reflexivity]).
  - right; left; auto.
  - right; right; auto.
  - exfalso; apply (Abstract t); reflexivity.
Qed.

Lemma binary_of_declaration_heap_encoding heap :
  declaration_heap_binary_wf heap ->
  declaration_heap_encoding (binary_of_heap_type heap) heap.
Proof.
  intro Wf.
  destruct heap;
    try (left; apply binary_of_declaration_abstract_heap_encoding; discriminate).
  right; exists t; split; [|reflexivity].
  split; [apply encode_signed_sound|]; split; [exact Wf|].
  apply (encode_signed_length_bound 4).
  change (-17179869184 <= Z.of_N t < 17179869184)%Z.
  change (t <= 4294967295)%N in Wf.
  pose proof (N2Z.is_nonneg t); lia.
Qed.

Lemma binary_of_declaration_reference_encoding reference :
  declaration_heap_binary_wf (ref_heap reference) ->
  declaration_reference_encoding (binary_of_reference_type reference) reference.
Proof.
  destruct reference as [nullable heap]; intro Wf; destruct nullable.
  - destruct heap;
      try (apply declaration_reference_compact;
        apply binary_of_declaration_abstract_heap_encoding; discriminate).
    apply (declaration_reference_explicit _ true).
    now apply binary_of_declaration_heap_encoding.
  - apply (declaration_reference_explicit _ false).
    now apply binary_of_declaration_heap_encoding.
Qed.

Lemma binary_of_declaration_value_encoding value :
  declaration_value_binary_wf value ->
  declaration_value_encoding (binary_of_value_type value) value.
Proof.
  destruct value; simpl; intro Wf; try reflexivity; try contradiction.
  now apply binary_of_declaration_reference_encoding.
Qed.
