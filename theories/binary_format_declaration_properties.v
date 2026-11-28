(** Source declaration codecs. HT_type is a module-local index; these grammar
    results do not close it, validate it, or turn it into a runtime identity. *)
From Stdlib Require Import List Strings.Byte NArith ZArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_parser_properties binary_parser_combinator_properties
  binary_format_language_properties binary_format_grammar_common
  binary_format_value_properties binary_format_block_properties
  binary_format_vector_properties binary_format_type_properties
  binary_format_print_encoding binary_format_numeric_complete
  binary_format_atomic_properties leb128_properties gc_types gc_binary.
Local Notation byte := Byte.byte.
From Wasm Require Import binary_format_global_properties.

Definition declaration_abstract_heap_encoding bytes h :=
  heap_type_encoding bytes h \/
  (bytes = x69 :: nil /\ h = HT_exn) \/
  (bytes = x74 :: nil /\ h = HT_noexn).

Lemma parse_declaration_abstract_heap_sound n :
  parser_sound (parse_declaration_abstract_heap_type
    (Toks := SizedList byte) (M := option) (n := n))
    declaration_abstract_heap_encoding.
Proof.
  unfold parse_declaration_abstract_heap_type.
  apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply parse_heap_type_sound |].
    intros bs h E; now left.
  - apply parser_sound_alt.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; right; left; auto.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; right; right; auto.
Qed.

Lemma parse_declaration_abstract_heap_complete n :
  parser_complete (parse_declaration_abstract_heap_type
    (Toks := SizedList byte) (M := option) (n := n))
    declaration_abstract_heap_encoding.
Proof.
  unfold parse_declaration_abstract_heap_type, declaration_abstract_heap_encoding.
  apply grammar_complete_choice.
  - apply parse_heap_type_sound.
  - apply parse_heap_type_complete.
  - apply grammar_complete_choice.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; auto.
    + apply fixed_instruction_complete.
    + apply fixed_instruction_complete.
    + intros xs ys t1 t2 a b [-> _] [-> _] E. discriminate.
  - intros xs ys t1 t2 a b [code [abstract [-> [Heap _]]]]
      [[-> _]|[-> _]] E; destruct Heap; discriminate.
Qed.

Lemma declaration_abstract_heap_head bytes h :
  declaration_abstract_heap_encoding bytes h ->
  exists b, bytes = b :: nil /\ (64 <= Byte.to_N b < 128)%N /\
    b <> x63 /\ b <> x64 /\
    b <> x7f /\ b <> x7e /\ b <> x7d /\ b <> x7c /\ b <> x7b.
Proof.
  intros [[b [abstract [-> [Heap _]]]]|[[-> _]|[-> _]]].
  - destruct Heap; eexists; repeat split; try reflexivity; try discriminate; cbn; lia.
  - exists x69; repeat split; try reflexivity; try discriminate; cbn; lia.
  - exists x74; repeat split; try reflexivity; try discriminate; cbn; lia.
Qed.

Lemma parse_declaration_index_sound n :
  parser_sound (parse_heap_typeidx
    (Toks := SizedList byte) (M := option) (n := n)) block_index_encoding.
Proof.
  intros m bound input s Run.
  destruct (parse_heap_typeidx_prefix_sound n m bound input s Run)
    as [bs [Bytes Encoding]].
  destruct (parse_heap_typeidx_guards bound input s Run) as [Range Width].
  exists bs; split; [exact Bytes |].
  split; [exact Encoding |]. split; [exact Range |].
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes s) = Success.size s) in Lout.
  rewrite Bytes, length_app in Lin. lia.
Qed.

Definition declaration_heap_encoding bytes h :=
  declaration_abstract_heap_encoding bytes h \/
  mapped_encoding HT_type block_index_encoding bytes h.

Lemma parse_declaration_heap_sound n :
  parser_sound (parse_declaration_heap_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_heap_encoding.
Proof.
  unfold parse_declaration_heap_type. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply parse_declaration_abstract_heap_sound |].
    intros bs h E; now left.
  - eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_declaration_index_sound |].
    intros bs h E; now right.
Qed.

Lemma parse_declaration_heap_complete n :
  parser_complete (parse_declaration_heap_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_heap_encoding.
Proof.
  unfold parse_declaration_heap_type, declaration_heap_encoding.
  apply grammar_complete_choice.
  - apply parse_declaration_abstract_heap_sound.
  - apply parse_declaration_abstract_heap_complete.
  - apply grammar_complete_map. apply parse_heap_typeidx_prefix_complete.
  - intros xs ys t1 t2 a b A [index [[E _] Value]] Same.
    destruct (declaration_abstract_heap_head xs a A) as [head [Bytes [Negative _]]].
    subst xs.
    eapply signed_nonnegative_disjoint_negative_byte;
      [exact E |apply N2Z.is_nonneg |exact Negative |].
    cbn in Same. symmetry; exact Same.
Qed.

Definition declaration_reference_encoding bytes rt :=
  tagged_encoding x63 (mapped_encoding (Ref_type true) declaration_heap_encoding) bytes rt \/
  tagged_encoding x64 (mapped_encoding (Ref_type false) declaration_heap_encoding) bytes rt \/
  mapped_encoding (Ref_type true) declaration_abstract_heap_encoding bytes rt.

Lemma parse_declaration_reference_sound n :
  parser_sound (parse_declaration_reference_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_reference_encoding.
Proof.
  unfold parse_declaration_reference_type. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply grammar_sound_map; apply grammar_sound_tag;
      apply parse_declaration_heap_sound |].
    intros bs h [heap [[body [Bytes E]] Value]].
    left. exists body; split; [exact Bytes |exists heap; auto].
  - apply parser_sound_alt.
    + eapply parser_sound_weaken; [apply grammar_sound_map; apply grammar_sound_tag;
        apply parse_declaration_heap_sound |].
      intros bs h [heap [[body [Bytes E]] Value]].
      right; left. exists body; split; [exact Bytes |exists heap; auto].
    + eapply parser_sound_weaken; [apply grammar_sound_map;
        apply parse_declaration_abstract_heap_sound |].
      intros bs h E; right; now right.
Qed.

Lemma declaration_reference_tag_sound n nullable tag :
  parser_sound
    ((Ref_type nullable <$> (exact_byte tag &> parse_declaration_heap_type)) :
      Parser (SizedList byte) byte option reference_type n)
    (tagged_encoding tag (mapped_encoding (Ref_type nullable) declaration_heap_encoding)).
Proof.
  eapply parser_sound_weaken; [apply grammar_sound_map; apply grammar_sound_tag;
    apply parse_declaration_heap_sound |].
  intros bs rt [heap [[body [Bytes E]] Value]].
  exists body; split; [exact Bytes |exists heap; auto].
Qed.

Lemma declaration_reference_tag_complete n nullable tag :
  parser_complete
    ((Ref_type nullable <$> (exact_byte tag &> parse_declaration_heap_type)) :
      Parser (SizedList byte) byte option reference_type n)
    (tagged_encoding tag (mapped_encoding (Ref_type nullable) declaration_heap_encoding)).
Proof.
  eapply parser_complete_map; [apply grammar_complete_tag; apply parse_declaration_heap_complete |].
  intros bs rt [body [Bytes [heap [Encoding Value]]]].
  exists heap; split; [exists body; auto |exact Value].
Qed.

Lemma parse_declaration_reference_complete n :
  parser_complete (parse_declaration_reference_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_reference_encoding.
Proof.
  unfold parse_declaration_reference_type, declaration_reference_encoding.
  apply grammar_complete_choice.
  - apply declaration_reference_tag_sound.
  - apply declaration_reference_tag_complete.
  - apply grammar_complete_choice.
    + apply declaration_reference_tag_sound.
    + apply declaration_reference_tag_complete.
    + apply grammar_complete_map. apply parse_declaration_abstract_heap_complete.
    + intros xs ys t1 t2 a b [body [-> _]] [heap [Encoding Value]] Same.
      destruct (declaration_abstract_heap_head ys heap Encoding)
        as [head [Bytes [_ [_ [Different _]]]]].
      subst ys. cbn in Same; inversion Same; congruence.
  - intros xs ys t1 t2 a b [body [-> _]] [[body' [-> _]]|[heap [Encoding Value]]] Same.
    + discriminate.
    + destruct (declaration_abstract_heap_head ys heap Encoding)
        as [head [Bytes [_ [Different _]]]].
      subst ys. cbn in Same; inversion Same; congruence.
Qed.

Lemma declaration_reference_head bytes rt :
  declaration_reference_encoding bytes rt ->
  exists head tail, bytes = head :: tail /\
    head <> x7f /\ head <> x7e /\ head <> x7d /\ head <> x7c /\ head <> x7b.
Proof.
  intros [[body [-> E]]|[[body [-> E]]|[heap [E Value]]]].
  - exists x63, body; repeat split; discriminate.
  - exists x64, body; repeat split; discriminate.
  - destruct (declaration_abstract_heap_head bytes heap E)
      as [head [Bytes [_ [_ [_ Different]]]]].
    exists head, nil; auto.
Qed.

Definition declaration_value_encoding bytes t :=
  mapped_encoding T_num (fun bs nt => bs = binary_of_number_type nt :: nil) bytes t \/
  mapped_encoding T_vec (fun bs vt => bs = binary_of_vector_type vt :: nil) bytes t \/
  mapped_encoding T_ref declaration_reference_encoding bytes t.

Lemma declaration_vector_sound n :
  parser_sound (parse_vector_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bs vt => bs = binary_of_vector_type vt :: nil).
Proof.
  unfold parse_vector_type. eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  intros bs b [Bytes _]. exact Bytes.
Qed.

Lemma declaration_vector_complete n :
  parser_complete (parse_vector_type (Toks := SizedList byte) (M := option) (n := n))
    (fun bs vt => bs = binary_of_vector_type vt :: nil).
Proof.
  intros m bound input prefix suffix [ ] Bytes Encoding.
  eapply fixed_instruction_complete; [exact Bytes |auto].
Qed.

Lemma parse_declaration_value_sound n :
  parser_sound (parse_declaration_value_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_value_encoding.
Proof.
  unfold parse_declaration_value_type. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_number_type_sound |].
    intros bs t E; now left.
  - apply parser_sound_alt.
    + eapply parser_sound_weaken; [apply grammar_sound_map; apply declaration_vector_sound |].
      intros bs t E; right; now left.
    + eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_declaration_reference_sound |].
      intros bs t E; right; now right.
Qed.

Lemma parse_declaration_value_complete n :
  parser_complete (parse_declaration_value_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_value_encoding.
Proof.
  unfold parse_declaration_value_type, declaration_value_encoding.
  apply grammar_complete_choice.
  - apply grammar_sound_map; apply parse_number_type_sound.
  - apply grammar_complete_map; apply parse_number_type_complete.
  - apply grammar_complete_choice.
    + apply grammar_sound_map; apply declaration_vector_sound.
    + apply grammar_complete_map; apply declaration_vector_complete.
    + apply grammar_complete_map; apply parse_declaration_reference_complete.
    + intros xs ys t1 t2 a b [vt [-> Value]] [rt [E Value']] Same.
      destruct vt.
      destruct (declaration_reference_head ys rt E) as [head [tail [Bytes [_ [_ [_ [_ Different]]]]]]].
      subst ys. cbn in Same; inversion Same; congruence.
  - intros xs ys t1 t2 a b [nt [-> Value]] [[vt [-> Value']]|[rt [E Value']]] Same.
    + destruct nt, vt; discriminate.
    + destruct (declaration_reference_head ys rt E) as [head [tail [Bytes Different]]].
      subst ys. destruct nt; cbn in Same; inversion Same; intuition congruence.
Qed.

Definition declaration_heap_binary_wf h :=
  match h with HT_type x => binary_index_wf x | _ => True end.
Definition declaration_value_binary_wf t :=
  match t with
  | T_bot => False
  | T_ref rt => declaration_heap_binary_wf rt.(ref_heap)
  | _ => True
  end.

Lemma declaration_abstract_printer h :
  (match h with HT_type _ => False | _ => True end) ->
  declaration_abstract_heap_encoding (binary_of_heap_type h) h.
Proof.
  destruct h; intro Wf; try contradiction;
    try solve [left; eexists; eexists; split; [reflexivity |split; [constructor |reflexivity]]];
    [right; left; auto |right; right; auto].
Qed.

Lemma declaration_heap_printer h :
  declaration_heap_binary_wf h -> declaration_heap_encoding (binary_of_heap_type h) h.
Proof.
  intro Wf. destruct h; try (left; apply declaration_abstract_printer; exact I).
  right; exists t; split; [|reflexivity].
  exact (binary_of_block_type_encoding (BT_id t) Wf).
Qed.

Lemma declaration_reference_printer rt :
  declaration_heap_binary_wf rt.(ref_heap) ->
  declaration_reference_encoding (binary_of_reference_type rt) rt.
Proof.
  destruct rt as [nullable h]; intro Wf; destruct nullable.
  - destruct h; try solve [right; right; eexists; split;
      [apply declaration_abstract_printer; exact I |reflexivity]].
    left. exists (binary_of_heap_type (HT_type t)); split; [reflexivity |].
    exists (HT_type t); split; [now apply declaration_heap_printer |reflexivity].
  - right; left. exists (binary_of_heap_type h); split; [reflexivity |].
    exists h; split; [now apply declaration_heap_printer |reflexivity].
Qed.

Lemma declaration_value_printer t :
  declaration_value_binary_wf t ->
  declaration_value_encoding (binary_of_value_type t) t.
Proof.
  destruct t as [number|vector|reference|]; intro Wf; try contradiction.
  - left; exists number; auto.
  - right; left; exists vector; auto.
  - right; right; exists reference; split; [now apply declaration_reference_printer |reflexivity].
Qed.

Definition declaration_function_encoding :=
  tagged_encoding x60
    (mapped_encoding (fun '(ins, outs) => Tf ins outs)
      (sequence_encoding (vector_encoding declaration_value_encoding)
        (vector_encoding declaration_value_encoding))).
Definition declaration_function_binary_wf ft :=
  match ft with Tf ins outs =>
    Forall declaration_value_binary_wf ins /\ Forall declaration_value_binary_wf outs /\
    binary_vector_length_wf ins /\ binary_vector_length_wf outs
  end.

Lemma parse_declaration_function_sound n :
  parser_sound (parse_function_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_function_encoding.
Proof.
  unfold parse_function_type.
  apply grammar_sound_tag; apply grammar_sound_map; apply grammar_sound_sequence;
    apply parse_vec_sound; apply parse_declaration_value_sound.
Qed.

Lemma parse_declaration_function_complete n :
  parser_complete (parse_function_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_function_encoding.
Proof.
  unfold parse_function_type.
  apply grammar_complete_tag; apply grammar_complete_map; apply grammar_complete_sequence;
    apply parse_vec_complete; apply parse_declaration_value_complete.
Qed.

Lemma declaration_function_printer ft :
  declaration_function_binary_wf ft ->
  declaration_function_encoding (binary_of_functype ft) ft.
Proof.
  destruct ft as [ins outs]; intros [Ins [Outs [Ni No]]].
  exists (binary_of_result_type ins ++ binary_of_result_type outs).
  split; [reflexivity |].
  exists (ins, outs); split; [|reflexivity].
  exists (binary_of_result_type ins), (binary_of_result_type outs).
  split; [reflexivity |]. split.
  - apply binary_of_vec_encoding; [|exact Ni].
    eapply Forall_impl; [|exact Ins].
    intros t Wf; now apply declaration_value_printer.
  - apply binary_of_vec_encoding; [|exact No].
    eapply Forall_impl; [|exact Outs].
    intros t Wf; now apply declaration_value_printer.
Qed.

Lemma declaration_value_not_packed bytes t :
  declaration_value_encoding bytes t ->
  exists b tail, bytes = b :: tail /\ b <> x78 /\ b <> x77.
Proof.
  intros [[nt [-> _]]|[[vt [-> _]]|[rt [Reference _]]]].
  - destruct nt; eexists; eexists; repeat split; discriminate.
  - destruct vt; eexists; eexists; repeat split; discriminate.
  - destruct Reference as [[body [-> _]]|[[body [-> _]]|[h [Heap _]]]].
    + exists x63, body; repeat split; discriminate.
    + exists x64, body; repeat split; discriminate.
    + destruct Heap as [[b [abstract [-> [Heap _]]]]|[[-> _]|[-> _]]].
      * destruct Heap; eexists; eexists; repeat split; discriminate.
      * exists x69, nil; repeat split; discriminate.
      * exists x74, nil; repeat split; discriminate.
Qed.

Definition declaration_storage_encoding bytes t :=
  (bytes = x78 :: nil /\ t = ST_packed PT_i8) \/
  (bytes = x77 :: nil /\ t = ST_packed PT_i16) \/
  mapped_encoding ST_value declaration_value_encoding bytes t.

Lemma parse_declaration_storage_sound n :
  parser_sound (parse_storage_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_storage_encoding.
Proof.
  unfold parse_storage_type. apply parser_sound_alt.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bs b [Bytes _]; now left.
  - apply parser_sound_alt.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; right; now left.
    + eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_declaration_value_sound |].
      intros bs t E; right; now right.
Qed.

Lemma parse_declaration_storage_complete n :
  parser_complete (parse_storage_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_storage_encoding.
Proof.
  unfold parse_storage_type, declaration_storage_encoding.
  apply grammar_complete_choice.
  - eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bs b [Bytes _]; auto.
  - apply fixed_instruction_complete.
  - apply grammar_complete_choice.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bs b [Bytes _]; auto.
    + apply fixed_instruction_complete.
    + apply grammar_complete_map; apply parse_declaration_value_complete.
    + intros xs ys t1 t2 a b [-> _] [v [E _]] Same.
      destruct (declaration_value_not_packed ys v E) as [head [tail [Bytes [_ Different]]]].
      subst ys. cbn in Same; inversion Same; congruence.
  - intros xs ys t1 t2 a b [-> _] [[-> _]|[v [E _]]] Same.
    + discriminate.
    + destruct (declaration_value_not_packed ys v E) as [head [tail [Bytes [Different _]]]].
      subst ys. cbn in Same; inversion Same; congruence.
Qed.

Definition declaration_field_encoding :=
  application_encoding
    (mapped_encoding (fun storage mut => {| field_mutability := mut; field_storage := storage |})
      declaration_storage_encoding)
    (fun bytes mut => bytes = binary_of_mutability mut).

Lemma parse_declaration_field_sound n :
  parser_sound (parse_field_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_field_encoding.
Proof.
  unfold parse_field_type.
  apply grammar_sound_app; [apply grammar_sound_map; apply parse_declaration_storage_sound |
    apply parse_mut_sound].
Qed.

Lemma parse_declaration_field_complete n :
  parser_complete (parse_field_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_field_encoding.
Proof.
  unfold parse_field_type.
  apply grammar_complete_app;
    [apply grammar_complete_map; apply parse_declaration_storage_complete |apply parse_mut_complete].
Qed.

Definition declaration_composite_encoding bytes t :=
  mapped_encoding Comp_func declaration_function_encoding bytes t \/
  tagged_encoding x5f
    (mapped_encoding Comp_struct (vector_encoding declaration_field_encoding)) bytes t \/
  tagged_encoding x5e (mapped_encoding Comp_array declaration_field_encoding) bytes t.

Lemma parse_declaration_composite_sound n :
  parser_sound (parse_composite_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_composite_encoding.
Proof.
  unfold parse_composite_type. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_declaration_function_sound |].
    intros bs t E; now left.
  - apply parser_sound_alt.
    + eapply parser_sound_weaken; [apply grammar_sound_tag; apply grammar_sound_map;
        apply parse_vec_sound; apply parse_declaration_field_sound |].
      intros bs t E; right; now left.
    + eapply parser_sound_weaken; [apply grammar_sound_tag; apply grammar_sound_map;
        apply parse_declaration_field_sound |].
      intros bs t E; right; now right.
Qed.

Lemma parse_declaration_composite_complete n :
  parser_complete (parse_composite_type
    (Toks := SizedList byte) (M := option) (n := n)) declaration_composite_encoding.
Proof.
  unfold parse_composite_type, declaration_composite_encoding.
  apply grammar_complete_choice.
  - apply grammar_sound_map; apply parse_declaration_function_sound.
  - apply grammar_complete_map; apply parse_declaration_function_complete.
  - apply grammar_complete_choice.
    + apply grammar_sound_tag; apply grammar_sound_map; apply parse_vec_sound;
        apply parse_declaration_field_sound.
    + apply grammar_complete_tag; apply grammar_complete_map; apply parse_vec_complete;
        apply parse_declaration_field_complete.
    + apply grammar_complete_tag; apply grammar_complete_map; apply parse_declaration_field_complete.
    + intros xs ys t1 t2 a b [first [-> _]] [second [-> _]] Same. discriminate.
  - intros xs ys t1 t2 a b [ft [[body [-> _]] _]]
      [[fields [-> _]]|[field [-> _]]] Same; discriminate.
Qed.

Lemma declaration_composite_head bytes t :
  declaration_composite_encoding bytes t ->
  exists b tail, bytes = b :: tail /\ (b = x60 \/ b = x5f \/ b = x5e).
Proof.
  intros [[ft [[body [-> _]] _]]|[[fields [-> _]]|[field [-> _]]]].
  - exists x60, body; auto.
  - exists x5f, fields; auto.
  - exists x5e, field; auto.
Qed.

Definition declaration_subtype_encoding bytes t :=
  application_encoding
    (mapped_encoding (Sub_type false)
      (tagged_encoding x50 (vector_encoding index_encoding)))
    declaration_composite_encoding bytes t \/
  application_encoding
    (mapped_encoding (Sub_type true)
      (tagged_encoding x4f (vector_encoding index_encoding)))
    declaration_composite_encoding bytes t \/
  mapped_encoding (Sub_type true nil) declaration_composite_encoding bytes t.

Lemma parse_declaration_subtype_sound n :
  parser_sound (parse_subtype
    (Toks := SizedList byte) (M := option) (n := n)) declaration_subtype_encoding.
Proof.
  unfold parse_subtype. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply grammar_sound_app;
      [apply grammar_sound_map; apply grammar_sound_tag; apply parse_vec_sound; apply parse_index_sound |
       apply parse_declaration_composite_sound] |].
    intros bs t E; now left.
  - apply parser_sound_alt.
    + eapply parser_sound_weaken; [apply grammar_sound_app;
        [apply grammar_sound_map; apply grammar_sound_tag; apply parse_vec_sound; apply parse_index_sound |
         apply parse_declaration_composite_sound] |].
      intros bs t E; right; now left.
    + eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_declaration_composite_sound |].
      intros bs t E; right; now right.
Qed.

Lemma parse_declaration_subtype_complete n :
  parser_complete (parse_subtype
    (Toks := SizedList byte) (M := option) (n := n)) declaration_subtype_encoding.
Proof.
  unfold parse_subtype, declaration_subtype_encoding.
  apply grammar_complete_choice.
  - apply grammar_sound_app;
      [apply grammar_sound_map; apply grammar_sound_tag; apply parse_vec_sound; apply parse_index_sound |
       apply parse_declaration_composite_sound].
  - apply grammar_complete_app;
      [apply grammar_complete_map; apply grammar_complete_tag; apply parse_vec_complete;
       apply leb128_properties.parse_u32_prefix_complete |apply parse_declaration_composite_complete].
  - apply grammar_complete_choice.
    + apply grammar_sound_app;
        [apply grammar_sound_map; apply grammar_sound_tag; apply parse_vec_sound; apply parse_index_sound |
         apply parse_declaration_composite_sound].
    + apply grammar_complete_app;
        [apply grammar_complete_map; apply grammar_complete_tag; apply parse_vec_complete;
         apply leb128_properties.parse_u32_prefix_complete |apply parse_declaration_composite_complete].
    + apply grammar_complete_map; apply parse_declaration_composite_complete.
    + intros xs ys t1 t2 a b [first [second [f [comp [X [[supers [[header [First _]] _]] _]]]]]]
        [composite [E _]] Same.
      destruct (declaration_composite_head ys composite E) as [head [tail [Y Heads]]].
      rewrite X, First, Y in Same. cbn in Same; inversion Same; intuition congruence.
  - intros xs ys t1 t2 a b
      [first [second [f [comp [X [[supers [[header [First _]] _]] _]]]]]] Right Same.
    destruct Right as
      [[third [fourth [f' [comp' [Y [[supers' [[header' [Third _]] _]] _]]]]]]|
       [composite [E _]]].
    + rewrite X, First, Y, Third in Same. discriminate.
    + destruct (declaration_composite_head ys composite E) as [head [tail [Y Heads]]].
      rewrite X, First, Y in Same. cbn in Same; inversion Same; intuition congruence.
Qed.

Lemma declaration_subtype_head bytes t :
  declaration_subtype_encoding bytes t ->
  exists b tail, bytes = b :: tail /\
    (b = x50 \/ b = x4f \/ b = x60 \/ b = x5f \/ b = x5e).
Proof.
  intros [E|[E|E]].
  - destruct E as [first [second [f [comp [Bytes [[supers [[header [First _]] _]] _]]]]]].
    exists x50, (header ++ second). rewrite Bytes, First; auto.
  - destruct E as [first [second [f [comp [Bytes [[supers [[header [First _]] _]] _]]]]]].
    exists x4f, (header ++ second). rewrite Bytes, First; auto.
  - destruct E as [composite [E Value]].
    destruct (declaration_composite_head bytes composite E) as [head [tail [Bytes Heads]]].
    exists head, tail; intuition.
Qed.

Definition recursive_type_encoding bytes group :=
  tagged_encoding x4e (vector_encoding declaration_subtype_encoding) bytes group \/
  mapped_encoding (fun t => t :: nil) declaration_subtype_encoding bytes group.

Theorem parse_recursive_type_sound n :
  parser_sound (parse_recursive_type
    (Toks := SizedList byte) (M := option) (n := n)) recursive_type_encoding.
Proof.
  unfold parse_recursive_type. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply grammar_sound_tag; apply parse_vec_sound;
      apply parse_declaration_subtype_sound |].
    intros bs t E; now left.
  - eapply parser_sound_weaken; [apply grammar_sound_map; apply parse_declaration_subtype_sound |].
    intros bs t E; now right.
Qed.

Theorem parse_recursive_type_complete n :
  parser_complete (parse_recursive_type
    (Toks := SizedList byte) (M := option) (n := n)) recursive_type_encoding.
Proof.
  unfold parse_recursive_type, recursive_type_encoding.
  apply grammar_complete_choice.
  - apply grammar_sound_tag; apply parse_vec_sound; apply parse_declaration_subtype_sound.
  - apply grammar_complete_tag; apply parse_vec_complete; apply parse_declaration_subtype_complete.
  - apply grammar_complete_map; apply parse_declaration_subtype_complete.
  - intros xs ys t1 t2 a b [body [-> _]] [subtype [E _]] Same.
    destruct (declaration_subtype_head ys subtype E) as [head [tail [Bytes Heads]]].
    subst ys. cbn in Same; inversion Same; intuition congruence.
Qed.

Definition declaration_storage_binary_wf t :=
  match t with ST_value v => declaration_value_binary_wf v | ST_packed _ => True end.
Definition declaration_field_binary_wf f :=
  declaration_storage_binary_wf f.(field_storage).
Definition declaration_composite_binary_wf t :=
  match t with
  | Comp_func ft => declaration_function_binary_wf ft
  | Comp_struct fields =>
      Forall declaration_field_binary_wf fields /\ binary_vector_length_wf fields
  | Comp_array field => declaration_field_binary_wf field
  end.
Definition declaration_subtype_binary_wf t :=
  Forall binary_index_wf t.(subtype_supers) /\
  binary_vector_length_wf t.(subtype_supers) /\
  declaration_composite_binary_wf t.(subtype_composite).
Definition recursive_type_binary_wf group :=
  Forall declaration_subtype_binary_wf group /\ binary_vector_length_wf group.

Lemma declaration_storage_printer storage :
  declaration_storage_binary_wf storage ->
  declaration_storage_encoding (binary_of_storage_type storage) storage.
Proof.
  destruct storage as [v|packed]; intro Wf.
  - right; right; exists v; split; [now apply declaration_value_printer |reflexivity].
  - destruct packed; [left |right; left]; auto.
Qed.

Lemma declaration_field_printer field :
  declaration_field_binary_wf field ->
  declaration_field_encoding (binary_of_field_type field) field.
Proof.
  destruct field as [mut storage]; intro Wf.
  exists (binary_of_storage_type storage), (binary_of_mutability mut),
    (fun mut => {| field_mutability := mut; field_storage := storage |}), mut.
  split; [destruct mut; reflexivity |].
  split; [exists storage; split; [now apply declaration_storage_printer |reflexivity] |].
  split; reflexivity.
Qed.

Lemma declaration_composite_printer composite :
  declaration_composite_binary_wf composite ->
  declaration_composite_encoding (binary_of_composite_type composite) composite.
Proof.
  destruct composite as [ft|fields|field]; intro Wf.
  - left; exists ft; split; [now apply declaration_function_printer |reflexivity].
  - right; left; exists (binary_of_vec binary_of_field_type fields).
    split; [reflexivity |]. exists fields; split; [|reflexivity].
    destruct Wf as [Fields Count]. apply binary_of_vec_encoding; [|exact Count].
    eapply Forall_impl; [|exact Fields].
    intros f Valid; now apply declaration_field_printer.
  - right; right; exists (binary_of_field_type field).
    split; [reflexivity |]. exists field; split; [now apply declaration_field_printer |reflexivity].
Qed.

Lemma declaration_subtype_explicit_printer final supers composite :
  Forall binary_index_wf supers -> binary_vector_length_wf supers ->
  declaration_composite_binary_wf composite ->
  application_encoding
    (mapped_encoding (Sub_type final)
      (tagged_encoding (if final then x4f else x50) (vector_encoding index_encoding)))
    declaration_composite_encoding
    ((if final then x4f else x50) ::
      binary_of_vec binary_of_typeidx supers ++ binary_of_composite_type composite)
    (Sub_type final supers composite).
Proof.
  intros Supers Count Composite.
  exists ((if final then x4f else x50) :: binary_of_vec binary_of_typeidx supers),
    (binary_of_composite_type composite), (Sub_type final supers), composite.
  split; [reflexivity |]. split.
  - exists supers; split; [|reflexivity].
    exists (binary_of_vec binary_of_typeidx supers); split; [reflexivity |].
    apply binary_of_vec_encoding; [|exact Count].
    eapply Forall_impl; [|exact Supers].
    intros x Valid; now apply binary_of_index_encoding.
  - split; [now apply declaration_composite_printer |reflexivity].
Qed.

Lemma declaration_subtype_printer subtype :
  declaration_subtype_binary_wf subtype ->
  declaration_subtype_encoding (binary_of_subtype subtype) subtype.
Proof.
  destruct subtype as [final supers composite]; intros [Supers [Count Composite]].
  destruct final; destruct supers as [|super supers].
  - right; right; exists composite; split; [now apply declaration_composite_printer |reflexivity].
  - right; left; now apply declaration_subtype_explicit_printer.
  - left; now apply declaration_subtype_explicit_printer.
  - left; now apply declaration_subtype_explicit_printer.
Qed.

Theorem binary_of_recursive_type_encoding group :
  recursive_type_binary_wf group ->
  recursive_type_encoding (binary_of_recursive_type group) group.
Proof.
  intros [Subtypes Count].
  assert (Vector : vector_encoding declaration_subtype_encoding
    (binary_of_vec binary_of_subtype group) group).
  { apply binary_of_vec_encoding; [|exact Count].
    eapply Forall_impl; [|exact Subtypes].
    intros subtype Wf; now apply declaration_subtype_printer. }
  destruct group as [|subtype [|next rest]].
  - left; exists (binary_of_vec binary_of_subtype nil); auto.
  - right; exists subtype; split; [|reflexivity].
    inversion Subtypes; now apply declaration_subtype_printer.
  - left; exists (binary_of_vec binary_of_subtype (subtype :: next :: rest)); auto.
Qed.
