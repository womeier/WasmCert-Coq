(** Full SOURCE value/global grammar and actual printer membership.
    Bounds describe wire encodability, not parser runs or runtime identities. *)
From Stdlib Require Import List Strings.Byte NArith ZArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes gc_types gc_storage_types
  gc_binary_parser_properties binary_format_parser binary_format_printer
  binary_format_reference_properties binary_format_eh_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  leb128_properties leb128_printer_properties.
Local Notation byte := Byte.byte.

Definition source_heap_binary_wf h :=
  match h with HT_type x => (x <= 4294967295)%N | _ => True end.
Definition source_value_binary_wf t :=
  match t with
  | T_num _ | T_vec _ => True
  | T_ref rt => source_heap_binary_wf rt.(ref_heap)
  | T_bot => False
  end.

Theorem source_heap_printer_membership h :
  source_heap_binary_wf h ->
  source_heap_encoding (binary_of_heap_type h) h.
Proof.
  intro Bound; destruct h; simpl in Bound.
  all: try (
    apply source_heap_abstract; eexists; split; [reflexivity |];
    first [apply she_exn |apply she_noexn |
      apply (she_gc _ AH_func); constructor |
      apply (she_gc _ AH_extern); constructor |
      apply (she_gc _ AH_any); constructor |
      apply (she_gc _ AH_eq); constructor |
      apply (she_gc _ AH_i31); constructor |
      apply (she_gc _ AH_struct); constructor |
      apply (she_gc _ AH_array); constructor |
      apply (she_gc _ AH_none); constructor |
      apply (she_gc _ AH_nofunc); constructor |
      apply (she_gc _ AH_noextern); constructor]).
  apply source_heap_index; split; [apply encode_signed_sound |].
  split; [exact Bound |].
  apply (encode_signed_length_bound 4).
  change (-17179869184 <= Z.of_N t < 17179869184)%Z.
  pose proof (N2Z.is_nonneg t); lia.
Qed.

Theorem source_reference_printer_membership rt :
  source_heap_binary_wf rt.(ref_heap) ->
  source_reference_encoding (binary_of_reference_type rt) rt.
Proof.
  destruct rt as [nullable h]; simpl; intro Bound.
  unfold binary_of_reference_type; simpl.
  destruct nullable.
  - destruct h.
    all: try (
      apply source_reference_short;
      match goal with
      | |- shared_heap_prefix _ ?heap =>
        pose proof (source_heap_printer_membership heap I) as Enc;
        inversion Enc; subst; assumption
      end).
    apply source_reference_nullable; now apply source_heap_printer_membership.
  - apply source_reference_nonnull; now apply source_heap_printer_membership.
Qed.

Theorem source_value_printer_membership t :
  source_value_binary_wf t ->
  source_value_encoding (binary_of_value_type t) t.
Proof.
  destruct t as [number|vector|rt|]; simpl; intro Bound.
  - apply source_value_number; reflexivity.
  - destruct vector; constructor.
  - apply source_value_reference; now apply source_reference_printer_membership.
  - contradiction.
Qed.

Theorem run_parse_source_value_correct bytes t rest :
  run_parse_prefix (fun n => parse_declaration_value_type (n := n)) bytes = Some (t, rest) <->
  exists prefix, bytes = prefix ++ rest /\ source_value_encoding prefix t.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_declaration_value_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_declaration_value_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest t Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (t, rest)).
    now rewrite Value, Rest.
Qed.

Theorem source_value_printer_prefix_roundtrip t rest :
  source_value_binary_wf t ->
  run_parse_prefix (fun n => parse_declaration_value_type (n := n))
    (binary_of_value_type t ++ rest) = Some (t, rest).
Proof.
  intro Bound; apply run_parse_source_value_correct.
  exists (binary_of_value_type t); split; [reflexivity |].
  now apply source_value_printer_membership.
Qed.

Definition mutability_encoding bytes mut := bytes = binary_of_mutability mut.

Lemma parse_mut_sound n :
  parser_sound (parse_mut (Toks := SizedList byte) (M := option) (n := n))
    mutability_encoding.
Proof.
  unfold parse_mut; apply parser_sound_alt.
  all: eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  all: intros bytes b [Bytes _]; exact Bytes.
Qed.

Lemma parse_mut_complete n :
  parser_complete (parse_mut (Toks := SizedList byte) (M := option) (n := n))
    mutability_encoding.
Proof.
  intros m bound input prefix suffix mut Bytes Encoding.
  destruct mut.
  - assert (Complete : parser_complete
      (parse_mut (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x00 :: nil /\ value = MUT_const)).
    { unfold parse_mut; apply parser_complete_alt_left; apply fixed_heap_complete. }
    eapply Complete; [exact Bytes |auto].
  - assert (Complete : parser_complete
      (parse_mut (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x01 :: nil /\ value = MUT_var)).
    { unfold parse_mut.
      eapply parser_complete_alt_right_initial with (expected := x00) (actual := x01).
      - apply parser_initial_cmap; apply exact_byte_initial.
      - discriminate.
      - intros bytes value [-> _]; exists nil; reflexivity.
      - apply fixed_heap_complete. }
    eapply Complete; [exact Bytes |auto].
Qed.

Definition global_type_encoding bytes gt :=
  exists types mut,
    bytes = types ++ mut /\
    source_value_encoding types gt.(tg_t) /\ mutability_encoding mut gt.(tg_mut).

Theorem parse_global_type_sound n :
  parser_sound (parse_global_type (Toks := SizedList byte) (M := option) (n := n))
    global_type_encoding.
Proof.
  unfold parse_global_type.
  eapply parser_sound_app with
    (P := fun bytes f => exists t, source_value_encoding bytes t /\
      f = (fun m => Build_global_type m t))
    (Q := mutability_encoding).
  - eapply parser_sound_map; [apply parse_declaration_value_sound |].
    intros bytes t Enc; exists t; auto.
  - intros k lt; simpl; apply parser_sound_le_lower; apply parse_mut_sound.
  - intros types mut f m [t [Enc ->]] Mut.
    exists types, mut; auto.
Qed.

Theorem parse_global_type_complete n :
  parser_complete (parse_global_type (Toks := SizedList byte) (M := option) (n := n))
    global_type_encoding.
Proof.
  unfold parse_global_type.
  eapply parser_complete_app with
    (P := fun bytes f => exists t, source_value_encoding bytes t /\
      f = (fun m => Build_global_type m t))
    (Q := mutability_encoding).
  - eapply parser_complete_map; [apply parse_declaration_value_complete |].
    intros bytes f Enc; exact Enc.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_mut_complete.
  - intros bytes gt [types [mut [Bytes [Enc Mut]]]].
    exists types, mut, (fun m => Build_global_type m gt.(tg_t)), gt.(tg_mut).
    split; [exact Bytes |]. split; [exists gt.(tg_t); auto |].
    split; [exact Mut |destruct gt; reflexivity].
Qed.

Theorem run_parse_global_type_correct bytes gt rest :
  run_parse_prefix (fun n => parse_global_type (n := n)) bytes = Some (gt, rest) <->
  exists prefix, bytes = prefix ++ rest /\ global_type_encoding prefix gt.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_global_type_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_global_type_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest gt Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (gt, rest)).
    now rewrite Value, Rest.
Qed.

Theorem global_type_printer_membership gt :
  source_value_binary_wf gt.(tg_t) ->
  global_type_encoding (binary_of_global_type gt) gt.
Proof.
  intro Bound; exists (binary_of_value_type gt.(tg_t)), (binary_of_mutability gt.(tg_mut)).
  split; [reflexivity |]. split; [now apply source_value_printer_membership |reflexivity].
Qed.

Theorem global_type_printer_prefix_roundtrip gt rest :
  source_value_binary_wf gt.(tg_t) ->
  run_parse_prefix (fun n => parse_global_type (n := n))
    (binary_of_global_type gt ++ rest) = Some (gt, rest).
Proof.
  intro Bound; apply run_parse_global_type_correct.
  exists (binary_of_global_type gt); split; [reflexivity |].
  now apply global_type_printer_membership.
Qed.

Definition source_ref_null_encoding bytes be :=
  exists payload h,
    bytes = xd0 :: payload /\ source_heap_encoding payload h /\ be = BI_ref_null h.

Theorem parse_source_ref_null_sound n :
  parser_sound (parse_ref_null (Toks := SizedList byte) (M := option) (n := n))
    source_ref_null_encoding.
Proof.
  unfold parse_ref_null.
  apply parser_sound_prefix_byte with
    (Q := fun bytes be => exists h, source_heap_encoding bytes h /\ be = BI_ref_null h).
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_declaration_heap_sound |].
    intros bytes h Enc; exists h; auto.
  - intros bytes be [h [Enc Value]]; exists bytes, h; auto.
Qed.

Theorem parse_source_ref_null_complete n :
  parser_complete (parse_ref_null (Toks := SizedList byte) (M := option) (n := n))
    source_ref_null_encoding.
Proof.
  unfold parse_ref_null.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists h, source_heap_encoding bytes h /\ be = BI_ref_null h).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_declaration_heap_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be [payload [h [Bytes [Enc Value]]]].
    exists payload; split; [exact Bytes |exists h; auto].
Qed.

Theorem source_ref_null_printer_membership h :
  source_heap_binary_wf h ->
  source_ref_null_encoding (binary_of_be (BI_ref_null h)) (BI_ref_null h).
Proof.
  intro Bound; exists (binary_of_heap_type h), h.
  split; [reflexivity |]. split; [now apply source_heap_printer_membership |reflexivity].
Qed.
