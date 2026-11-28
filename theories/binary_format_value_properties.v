(** Byte grammars for the production abstract reference fragment.
    Source indexed descriptors remain at the separate canonical closing boundary. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_format_parser_properties binary_locals_properties
  binary_locals_printer_properties gc_types gc_binary gc_binary_parser_properties.
Close Scope N_scope.

Definition reference_type_encoding bs rt :=
  exists abstract, rt = shared_reference_of_abstract abstract /\
    abstract_reference_encoding bs abstract nil.

Definition value_type_encoding bs t := concrete_valtype_prefix bs t nil.

Definition heap_type_encoding bs ht :=
  exists b abstract, bs = b :: nil /\ abstract_heap_encoding b abstract /\
    ht = shared_heap_of_abstract abstract.

Lemma parse_heap_type_sound n :
  parser_sound (parse_gc_heap_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    heap_type_encoding.
Proof.
  unfold parse_gc_heap_type.
  eapply parser_sound_map; [apply parse_gc_abstract_heap_sound |].
  intros bs abstract [b [Bytes Encoding]].
  exists b, abstract. auto.
Qed.

Lemma parse_heap_type_complete n :
  parser_complete (parse_gc_heap_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    heap_type_encoding.
Proof.
  intros m bound [input L] prefix suffix ht Bytes [b [abstract [Prefix [Encoding Value]]]].
  change (input = prefix ++ suffix) in Bytes.
  subst prefix input ht. cbn in L. subst m.
  destruct Encoding.
  all: eexists; split; [reflexivity | split; reflexivity].
Qed.

Lemma concrete_valtype_suffix bs t rest :
  concrete_valtype_prefix bs t nil ->
  concrete_valtype_prefix (bs ++ rest) t rest.
Proof.
  intro E. inversion E; subst; try solve [constructor].
  apply valtype_abstract_reference.
  now apply abstract_reference_encoding_suffix.
Qed.

Lemma concrete_valtype_consumed input t rest :
  concrete_valtype_prefix input t rest ->
  exists bs, input = bs ++ rest /\ value_type_encoding bs t.
Proof.
  intro E. inversion E; subst;
    try solve [match goal with
      | |- exists bs, ?b :: rest = bs ++ rest /\ _ =>
        exists (b :: nil); split; [reflexivity | constructor]
      end].
  match goal with H : abstract_reference_encoding _ _ _ |- _ => destruct H end;
    match goal with
    | |- exists bs, ?b :: ?h :: rest = bs ++ rest /\ _ =>
      exists (b :: h :: nil)
    | |- exists bs, ?b :: rest = bs ++ rest /\ _ => exists (b :: nil)
    end.
  all: split; [reflexivity | apply valtype_abstract_reference;
    first [apply are_short | apply are_nullable | apply are_nonnull]; eassumption].
Qed.

Lemma parse_value_type_sound n :
  parser_sound (parse_value_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    value_type_encoding.
Proof.
  intros m bound input s Run.
  apply concrete_valtype_consumed.
  apply (parse_concrete_valtype_sound n m input
    (Success.value s) (output_bytes s) bound).
  rewrite Run. reflexivity.
Qed.

Lemma parse_value_type_complete n :
  parser_complete (parse_value_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    value_type_encoding.
Proof.
  intros m bound input prefix suffix t Bytes Encoding.
  assert (E : option_map binary_uleb128.observe_reader
    (runParser (parse_value_type :
      Parser (SizedList Byte.byte) Byte.byte option value_type n) bound input) =
    Some (t, suffix)).
  { apply parse_concrete_valtype_prefix.
    change (concrete_valtype_prefix (input_bytes input) t suffix).
    rewrite Bytes. now apply concrete_valtype_suffix. }
  destruct (runParser (parse_value_type :
    Parser (SizedList Byte.byte) Byte.byte option value_type n) bound input)
    as [s|] eqn:Run; [|discriminate].
  exists s. split; [reflexivity |].
  change (Some (Success.value s, output_bytes s) = Some (t, suffix)) in E.
  now inversion E.
Qed.

Lemma binary_of_value_type_encoding t :
  printable_local_type t -> value_type_encoding (binary_of_value_type t) t.
Proof.
  intro E.
  pose proof (printable_local_type_suffix t nil E) as H.
  now rewrite app_nil_r in H.
Qed.

Lemma value_type_encoding_head bs t :
  value_type_encoding bs t ->
  exists b tail, bs = b :: tail /\ (64 <= Byte.to_N b < 128)%N /\ b <> x40.
Proof.
  intro E. inversion E; subst;
    try (eexists; eexists; repeat split; try reflexivity; try discriminate;
      cbn; lia).
  match goal with H : abstract_reference_encoding _ _ _ |- _ => destruct H end;
    match goal with H : abstract_heap_encoding _ _ |- _ => destruct H end;
    eexists; eexists; repeat split; try reflexivity; try discriminate; cbn; lia.
Qed.

Lemma parse_reference_type_sound n :
  parser_sound (parse_reference_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    reference_type_encoding.
Proof.
  unfold parse_reference_type.
  eapply parser_sound_map; [apply parse_gc_abstract_reference_sound |].
  intros bs abstract E. exists abstract; auto.
Qed.

Lemma parse_reference_type_complete n :
  parser_complete (parse_reference_type (Toks := SizedList Byte.byte) (M := option) (n := n))
    reference_type_encoding.
Proof.
  intros m bound input prefix suffix rt Bytes [abstract [Value Encoding]].
  subst rt.
  assert (E : option_map binary_uleb128.observe_reader
    (runParser (parse_reference_type :
      Parser (SizedList Byte.byte) Byte.byte option reference_type n) bound input) =
    Some (shared_reference_of_abstract abstract, suffix)).
  { apply parser_map_prefix with (value := abstract).
    destruct input as [input L].
    change (input = prefix ++ suffix) in Bytes. subst input.
    apply abstract_reference_encoding_suffix with (rest := suffix) in Encoding.
    destruct Encoding; destruct H; cbn in L; subst m; reflexivity. }
  destruct (runParser (parse_reference_type :
    Parser (SizedList Byte.byte) Byte.byte option reference_type n) bound input)
    as [s|] eqn:Run; [|discriminate].
  exists s. split; [reflexivity |].
  change (Some (Success.value s, output_bytes s) =
    Some (shared_reference_of_abstract abstract, suffix)) in E.
  now inversion E.
Qed.
