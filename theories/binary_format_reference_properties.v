(** EH-aware source heap grammar and the production declaration decoder.
    Reference identities remain source syntax here; scope/closing belongs to
    source_local_properties and the shared canonical validation boundary. *)
From Stdlib Require Import List Strings.Byte NArith ZArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes gc_types gc_binary gc_binary_parser_properties
  binary_format_parser binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_eh_properties
  binary_format_parser_properties binary_format_printer leb128_properties.
Local Notation byte := Byte.byte.

Definition gc_heap_prefix bytes h :=
  exists b abstract, bytes = b :: nil /\ abstract_heap_encoding b abstract /\
    h = shared_heap_of_abstract abstract.

Definition shared_heap_prefix bytes h :=
  exists b, bytes = b :: nil /\ shared_heap_encoding b h.

Theorem parse_gc_heap_sound n :
  parser_sound (parse_gc_heap_type (Toks := SizedList byte) (M := option) (n := n))
    gc_heap_prefix.
Proof.
  unfold parse_gc_heap_type.
  eapply parser_sound_map; [apply parse_gc_abstract_heap_sound |].
  intros bytes h [b [Bytes Enc]]; exists b, h; auto.
Qed.

Theorem parse_gc_heap_complete n :
  parser_complete (parse_gc_heap_type (Toks := SizedList byte) (M := option) (n := n))
    gc_heap_prefix.
Proof.
  unfold parse_gc_heap_type.
  eapply parser_complete_map; [apply parse_gc_abstract_heap_complete |].
  intros bytes h [b [abstract [Bytes [Enc Value]]]].
  exists abstract; split; [exists b; auto |exact Value].
Qed.

Lemma parse_gc_heap_initial n :
  parser_initial_set
    (parse_gc_heap_type (Toks := SizedList byte) (M := option) (n := n))
    (fun b => exists h, abstract_heap_encoding b h).
Proof.
  eapply parser_initial_set_from_sound; [apply parse_gc_heap_sound |].
  intros bytes h [b [a [Bytes [Enc Value]]]].
  exists b, nil; split; [exact Bytes |exists a; exact Enc].
Qed.

Lemma fixed_heap_complete {A} n opcode (h : A) :
  parser_complete
    (Combinators.cmap h (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode))
    (fun bytes value => bytes = opcode :: nil /\ value = h).
Proof.
  unfold Combinators.cmap.
  eapply parser_complete_map; [apply parser_complete_exact_byte |].
  intros bytes value [Bytes Value]; exists opcode; auto.
Qed.

Theorem parse_supported_heap_sound n :
  parser_sound (parse_supported_heap_type (Toks := SizedList byte) (M := option) (n := n))
    shared_heap_prefix.
Proof.
  unfold parse_supported_heap_type; apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply parse_gc_heap_sound |].
    intros bytes h [b [a [Bytes [Enc ->]]]].
    exists b; split; [exact Bytes |now constructor].
  - apply parser_sound_alt.
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bytes b [Bytes _]; exists x69; split; [exact Bytes |constructor].
    + eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
      intros bytes b [Bytes _]; exists x74; split; [exact Bytes |constructor].
Qed.

Theorem parse_supported_heap_complete n :
  parser_complete (parse_supported_heap_type (Toks := SizedList byte) (M := option) (n := n))
    shared_heap_prefix.
Proof.
  intros m bound input prefix suffix h Bytes [b [Prefix Enc]].
  destruct Enc as [b a Enc| |].
  - assert (Complete : parser_complete
      (parse_supported_heap_type (Toks := SizedList byte) (M := option) (n := n))
      gc_heap_prefix).
    { unfold parse_supported_heap_type; apply parser_complete_alt_left.
      apply parse_gc_heap_complete. }
    eapply Complete; [exact Bytes |].
    exists b, a; auto.
  - assert (Complete : parser_complete
      (parse_supported_heap_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x69 :: nil /\ value = HT_exn)).
    { unfold parse_supported_heap_type.
      eapply parser_complete_alt_right_initial_set with
        (Allowed := fun b => exists h, abstract_heap_encoding b h) (opcode := x69).
      - apply parse_gc_heap_initial.
      - intros [a Impossible]; inversion Impossible.
      - intros bytes value [-> _]; exists nil; reflexivity.
      - apply parser_complete_alt_left; apply fixed_heap_complete. }
    eapply Complete; [exact Bytes |auto].
  - assert (Complete : parser_complete
      (parse_supported_heap_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x74 :: nil /\ value = HT_noexn)).
    { unfold parse_supported_heap_type.
      eapply parser_complete_alt_right_initial_set with
        (Allowed := fun b => exists h, abstract_heap_encoding b h) (opcode := x74).
      - apply parse_gc_heap_initial.
      - intros [a Impossible]; inversion Impossible.
      - intros bytes value [-> _]; exists nil; reflexivity.
      - eapply parser_complete_alt_right_initial with (expected := x69) (actual := x74).
        + apply parser_initial_cmap; apply exact_byte_initial.
        + discriminate.
        + intros bytes value [-> _]; exists nil; reflexivity.
        + apply fixed_heap_complete. }
    eapply Complete; [exact Bytes |auto].
Qed.

Definition source_heap_index_encoding bytes x :=
  signed_leb bytes (Z.of_N x) /\ (x <= 4294967295)%N /\ length bytes <= 5.

Lemma parse_source_heap_index_sound n :
  parser_sound (parse_heap_typeidx (Toks := SizedList byte) (M := option) (n := n))
    source_heap_index_encoding.
Proof.
  intros m bound input s Run.
  destruct (parse_heap_typeidx_prefix_sound n _ _ _ _ Run) as [prefix [Bytes Enc]].
  destruct (parse_heap_typeidx_guards bound input s Run) as [Range Width].
  exists prefix; split; [exact Bytes |].
  split; [exact Enc |]. split; [exact Range |].
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes s) = Success.size s) in Lout.
  rewrite Bytes, length_app in Lin.
  assert (Count : m - Success.size s = length prefix) by lia.
  rewrite Count in Width; lia.
Qed.

Inductive source_heap_encoding : list byte -> heap_type -> Prop :=
| source_heap_abstract : forall bytes h,
    shared_heap_prefix bytes h -> source_heap_encoding bytes h
| source_heap_index : forall bytes x,
    source_heap_index_encoding bytes x -> source_heap_encoding bytes (HT_type x).

Lemma nonnegative_index_not_abstract bytes x b rest h :
  source_heap_index_encoding bytes x ->
  bytes = b :: rest -> shared_heap_encoding b h -> False.
Proof.
  intros [Encoding [Range Width]] Bytes Heap; subst bytes.
  destruct Heap; try destruct H; inversion Encoding; subst; simpl in *; lia.
Qed.

Theorem parse_declaration_heap_sound n :
  parser_sound (parse_declaration_heap_type (Toks := SizedList byte) (M := option) (n := n))
    source_heap_encoding.
Proof.
  unfold parse_declaration_heap_type; apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply parse_supported_heap_sound |].
    intros bytes h Enc; now constructor.
  - eapply parser_sound_map; [apply parse_source_heap_index_sound |].
    intros bytes x Enc; now constructor.
Qed.

Theorem parse_declaration_heap_complete n :
  parser_complete (parse_declaration_heap_type (Toks := SizedList byte) (M := option) (n := n))
    source_heap_encoding.
Proof.
  intros m bound input prefix suffix h Bytes Encoding.
  destruct Encoding as [prefix h Enc|prefix x Enc].
  - eapply (parser_complete_alt_left _ _ _ (parse_supported_heap_complete n));
      [exact Bytes |exact Enc].
  - assert (Complete : parser_complete
      (parse_declaration_heap_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes h => exists x, source_heap_index_encoding bytes x /\ h = HT_type x)).
    { unfold parse_declaration_heap_type.
      apply parser_complete_alt_right_failure.
      - intros k lower tokens bytes tail value Input [i [Index Value]].
        destruct (runParser parse_declaration_abstract_heap_type lower tokens)
          as [s|] eqn:Run; [|reflexivity].
        destruct (parse_supported_heap_sound n _ _ _ _ Run)
          as [consumed [Consumed [b [Head Heap]]]].
        destruct bytes as [|first rest].
        + destruct Index as [Signed _]; inversion Signed.
        + rewrite Input, Head in Consumed.
          inversion Consumed; subst first.
          exfalso; eapply nonnegative_index_not_abstract;
            [exact Index |reflexivity |exact Heap].
      - eapply parser_complete_map; [apply parse_heap_typeidx_prefix_complete |].
        intros bytes value [i [Index Value]]; exists i; auto. }
    eapply Complete; [exact Bytes |exists x; auto].
Qed.

Inductive source_reference_encoding : list byte -> reference_type -> Prop :=
| source_reference_short : forall bytes h,
    shared_heap_prefix bytes h ->
    source_reference_encoding bytes (Ref_type true h)
| source_reference_nullable : forall bytes h,
    source_heap_encoding bytes h ->
    source_reference_encoding (x63 :: bytes) (Ref_type true h)
| source_reference_nonnull : forall bytes h,
    source_heap_encoding bytes h ->
    source_reference_encoding (x64 :: bytes) (Ref_type false h).

Definition mapped_reference_encoding nullable (P : list byte -> heap_type -> Prop) bytes rt :=
  exists h, P bytes h /\ rt = Ref_type nullable h.

Lemma mapped_reference_complete n nullable p P :
  parser_complete p P ->
  parser_complete
    (Combinators.map (Ref_type nullable)
      (p : Parser (SizedList byte) byte option heap_type n))
    (mapped_reference_encoding nullable P).
Proof.
  intro Complete; eapply parser_complete_map; [exact Complete |].
  intros bytes rt Enc; exact Enc.
Qed.

Theorem parse_declaration_reference_sound n :
  parser_sound (parse_declaration_reference_type (Toks := SizedList byte) (M := option) (n := n))
    source_reference_encoding.
Proof.
  unfold parse_declaration_reference_type; apply parser_sound_alt.
  - eapply parser_sound_map.
    + apply eh_prefixed_sound; apply parse_declaration_heap_sound.
    + intros bytes h [body [-> Enc]]; now constructor.
  - apply parser_sound_alt.
    + eapply parser_sound_map.
      * apply eh_prefixed_sound; apply parse_declaration_heap_sound.
      * intros bytes h [body [-> Enc]]; now constructor.
    + eapply parser_sound_map; [apply parse_supported_heap_sound |].
      intros bytes h Enc; now constructor.
Qed.

Lemma shared_heap_not_explicit b h :
  shared_heap_encoding b h -> b <> x63 /\ b <> x64.
Proof.
  intro Heap; destruct Heap; try destruct H; split; discriminate.
Qed.

Lemma skip_reference_prefix {A n}
    (p q : Parser (SizedList byte) byte option A n) opcode Q :
  parser_initial_byte p opcode ->
  (forall bytes value, Q bytes value ->
    exists first rest, bytes = first :: rest /\ first <> opcode) ->
  parser_complete q Q ->
  parser_complete (Combinators.alt p q) Q.
Proof.
  intros Initial Head Complete.
  apply parser_complete_alt_right_failure; [|exact Complete].
  intros m bound input prefix suffix value Bytes Enc.
  destruct (Head _ _ Enc) as [first [rest [Prefix Different]]].
  apply (parser_initial_mismatch p opcode first Initial) with (tail := rest ++ suffix).
  - congruence.
  - now rewrite Bytes, Prefix.
Qed.

Theorem parse_declaration_reference_complete n :
  parser_complete (parse_declaration_reference_type (Toks := SizedList byte) (M := option) (n := n))
    source_reference_encoding.
Proof.
  intros m bound input prefix suffix rt Bytes Encoding.
  destruct Encoding as [prefix h Enc|body h Enc|body h Enc].
  - assert (Complete : parser_complete
      (parse_declaration_reference_type (Toks := SizedList byte) (M := option) (n := n))
      (mapped_reference_encoding true shared_heap_prefix)).
    { unfold parse_declaration_reference_type.
      eapply skip_reference_prefix with (opcode := x63).
      - apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
      - intros bytes value [h' [[b [Prefix Heap]] Value]].
        exists b, nil; split; [exact Prefix |].
        exact (proj1 (shared_heap_not_explicit b h' Heap)).
      - eapply skip_reference_prefix with (opcode := x64).
        + apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
        + intros bytes value [h' [[b [Prefix Heap]] Value]].
          exists b, nil; split; [exact Prefix |].
          exact (proj2 (shared_heap_not_explicit b h' Heap)).
        + apply mapped_reference_complete; apply parse_supported_heap_complete. }
    eapply Complete; [exact Bytes |exists h; auto].
  - assert (Complete : parser_complete
      (parse_declaration_reference_type (Toks := SizedList byte) (M := option) (n := n))
      (mapped_reference_encoding true (eh_prefixed x63 source_heap_encoding))).
    { unfold parse_declaration_reference_type; apply parser_complete_alt_left.
      apply mapped_reference_complete; apply eh_prefixed_complete.
      apply parse_declaration_heap_complete. }
    eapply Complete; [exact Bytes |].
    exists h; split; [exists body; auto |reflexivity].
  - assert (Complete : parser_complete
      (parse_declaration_reference_type (Toks := SizedList byte) (M := option) (n := n))
      (mapped_reference_encoding false (eh_prefixed x64 source_heap_encoding))).
    { unfold parse_declaration_reference_type.
      eapply parser_complete_alt_right_initial with (expected := x63) (actual := x64).
      - apply parser_initial_map; apply parser_initial_rand; apply exact_byte_initial.
      - discriminate.
      - intros bytes value [h' [[tail [Prefix _]] _]]; exists tail; exact Prefix.
      - apply parser_complete_alt_left.
        apply mapped_reference_complete; apply eh_prefixed_complete.
        apply parse_declaration_heap_complete. }
    eapply Complete; [exact Bytes |].
    exists h; split; [exists body; auto |reflexivity].
Qed.

Theorem run_parse_declaration_reference_correct bytes rt rest :
  run_parse_prefix (fun n => parse_declaration_reference_type (n := n)) bytes =
    Some (rt, rest) <->
  exists prefix, bytes = prefix ++ rest /\ source_reference_encoding prefix rt.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_declaration_reference_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_declaration_reference_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest rt Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (rt, rest)).
    now rewrite Value, Rest.
Qed.

Definition number_type_encoding bytes t := bytes = binary_of_number_type t :: nil.

Lemma parse_number_type_sound n :
  parser_sound (parse_number_type (Toks := SizedList byte) (M := option) (n := n))
    number_type_encoding.
Proof.
  unfold parse_number_type.
  do 3 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  all: intros bytes b [Bytes _]; exact Bytes.
Qed.

Ltac type_byte_dispatch opcode :=
  first
    [solve [apply parser_complete_alt_left; apply fixed_heap_complete]
    |eapply parser_complete_alt_right_initial with (actual := opcode);
      [apply parser_initial_cmap; apply exact_byte_initial |discriminate |
       let bs := fresh "bs" in let v := fresh "v" in
       intros bs v [-> _]; exists nil; reflexivity |
       type_byte_dispatch opcode]
    |apply fixed_heap_complete].

Lemma parse_number_type_complete n :
  parser_complete (parse_number_type (Toks := SizedList byte) (M := option) (n := n))
    number_type_encoding.
Proof.
  intros m bound input prefix suffix t Bytes Encoding.
  destruct t;
    match goal with
    | Encoding : number_type_encoding _ ?t |- _ =>
      assert (Complete : parser_complete
        (parse_number_type (Toks := SizedList byte) (M := option) (n := n))
        (fun bytes value => bytes = binary_of_number_type t :: nil /\ value = t))
        by (cbn [binary_of_number_type]; unfold parse_number_type;
          type_byte_dispatch ltac:(eval cbv in (binary_of_number_type t)));
      exact (Complete m bound input prefix suffix t Bytes (conj Encoding Logic.eq_refl))
    end.
Qed.

Lemma source_reference_head bytes rt :
  source_reference_encoding bytes rt ->
  exists first rest, bytes = first :: rest /\
    ~ In first (x7f :: x7e :: x7d :: x7c :: x7b :: nil).
Proof.
  intro Encoding; destruct Encoding.
  - destruct H as [b [Bytes Heap]].
    exists b, nil; split; [exact Bytes |].
    destruct Heap; try destruct H; simpl; intuition discriminate.
  - exists x63, bytes; split; [reflexivity |].
    simpl; intuition discriminate.
  - exists x64, bytes; split; [reflexivity |].
    simpl; intuition discriminate.
Qed.

Inductive source_value_encoding : list byte -> value_type -> Prop :=
| source_value_number : forall bytes t,
    number_type_encoding bytes t -> source_value_encoding bytes (T_num t)
| source_value_vector : source_value_encoding (x7b :: nil) (T_vec T_v128)
| source_value_reference : forall bytes rt,
    source_reference_encoding bytes rt -> source_value_encoding bytes (T_ref rt).

Theorem parse_declaration_value_sound n :
  parser_sound (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
    source_value_encoding.
Proof.
  unfold parse_declaration_value_type; apply parser_sound_alt.
  - eapply parser_sound_map; [apply parse_number_type_sound |].
    intros bytes t Enc; now constructor.
  - apply parser_sound_alt.
    + eapply parser_sound_map with (P := fun bytes (_ : vector_type) => bytes = x7b :: nil).
      * unfold parse_vector_type; eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
        intros bytes b [Bytes _]; exact Bytes.
      * intros bytes t Enc; subst bytes; destruct t; constructor.
    + eapply parser_sound_map; [apply parse_declaration_reference_sound |].
      intros bytes rt Enc; now constructor.
Qed.

Lemma skip_reference_initial_set {n}
    (p q : Parser (SizedList byte) byte option value_type n) Allowed :
  parser_initial_set p Allowed ->
  (forall b, Allowed b -> In b (x7f :: x7e :: x7d :: x7c :: x7b :: nil)) ->
  parser_complete q
    (fun bytes v => exists rt, source_reference_encoding bytes rt /\ v = T_ref rt) ->
  parser_complete (Combinators.alt p q)
    (fun bytes v => exists rt, source_reference_encoding bytes rt /\ v = T_ref rt).
Proof.
  intros Initial Members Complete.
  apply parser_complete_alt_right_failure; [|exact Complete].
  intros m bound input prefix suffix value Bytes [rt [Enc Value]].
  destruct (source_reference_head _ _ Enc) as [first [rest [Prefix Rejected]]].
  destruct (runParser p bound input) as [s|] eqn:Run; [|reflexivity].
  destruct (Initial _ _ _ _ Run) as [other [tail [Head AllowedByte]]].
  rewrite Bytes, Prefix in Head; inversion Head; subst other.
  exfalso; apply Rejected; now apply Members.
Qed.

Theorem parse_declaration_value_complete n :
  parser_complete (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
    source_value_encoding.
Proof.
  intros m bound input prefix suffix value Bytes Encoding.
  destruct Encoding as [prefix t Enc| |prefix rt Enc].
  - assert (Complete : parser_complete
      (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => exists t, number_type_encoding bytes t /\ value = T_num t)).
    { unfold parse_declaration_value_type; apply parser_complete_alt_left.
      eapply parser_complete_map; [apply parse_number_type_complete |].
      intros bytes value E; exact E. }
    eapply Complete; [exact Bytes |exists t; auto].
  - assert (Complete : parser_complete
      (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x7b :: nil /\ value = T_vec T_v128)).
    { unfold parse_declaration_value_type.
      eapply parser_complete_alt_right_initial_set with
        (Allowed := fun b => In b (x7f :: x7e :: x7d :: x7c :: nil)) (opcode := x7b).
      - eapply parser_initial_set_from_sound with
          (Grammar := fun bytes value => exists t,
            number_type_encoding bytes t /\ value = T_num t).
        + eapply parser_sound_map; [apply parse_number_type_sound |].
          intros bytes t NumberEncoding; exists t; auto.
        + intros bytes value [t [NumberEncoding Value]].
          exists (binary_of_number_type t), nil; split; [exact NumberEncoding |].
          destruct t; simpl; auto.
      - simpl; intuition discriminate.
      - intros bytes value [-> _]; exists nil; reflexivity.
      - apply parser_complete_alt_left.
        eapply parser_complete_map.
        + unfold parse_vector_type; apply fixed_heap_complete.
        + intros bytes value [VectorBytes VectorValue].
          exists T_v128; auto. }
    eapply Complete; [exact Bytes |auto].
  - assert (Complete : parser_complete
      (parse_declaration_value_type (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => exists rt, source_reference_encoding bytes rt /\ value = T_ref rt)).
    { unfold parse_declaration_value_type.
      eapply skip_reference_initial_set with
        (Allowed := fun b => In b (x7f :: x7e :: x7d :: x7c :: nil)).
      - eapply parser_initial_set_from_sound with
          (Grammar := fun bytes value => exists t,
            number_type_encoding bytes t /\ value = T_num t).
        + eapply parser_sound_map; [apply parse_number_type_sound |].
          intros bytes t NumberEncoding; exists t; auto.
        + intros bytes value [t [NumberEncoding Value]].
          exists (binary_of_number_type t), nil; split; [exact NumberEncoding |].
          destruct t; simpl; auto.
      - simpl; tauto.
      - eapply skip_reference_initial_set with (Allowed := fun b => b = x7b).
        + apply parser_initial_exact_set.
          apply parser_initial_map; unfold parse_vector_type.
          apply parser_initial_cmap; apply exact_byte_initial.
        + intros b ->; simpl; tauto.
        + eapply parser_complete_map; [apply parse_declaration_reference_complete |].
          intros bytes value E; exact E. }
    eapply Complete; [exact Bytes |exists rt; auto].
Qed.

Definition source_local_encoding bytes (local : N * value_type) :=
  exists count_bytes type_bytes,
    bytes = count_bytes ++ type_bytes /\
    eh_index_encoding count_bytes (fst local) /\
    source_value_encoding type_bytes (snd local).

Theorem parse_locals_sound n :
  parser_sound (parse_locals (Toks := SizedList byte) (M := option) (n := n))
    source_local_encoding.
Proof.
  unfold parse_locals, Combinators.and.
  eapply parser_sound_andbind with (P := eh_index_encoding)
    (Q := fun _ => source_value_encoding).
  - apply eh_index_sound.
  - intros count k lt; simpl; apply parser_sound_le_lower.
    apply parse_declaration_value_sound.
  - intros xs ys count t Count TypeEncoding.
    exists xs, ys; auto.
Qed.

Theorem parse_locals_complete n :
  parser_complete (parse_locals (Toks := SizedList byte) (M := option) (n := n))
    source_local_encoding.
Proof.
  unfold parse_locals, Combinators.and.
  eapply parser_complete_andbind with (P := eh_index_encoding)
    (Q := fun _ => source_value_encoding).
  - apply parse_u32_prefix_complete.
  - intros count k lt; simpl; apply parser_complete_le_lower.
    apply parse_declaration_value_complete.
  - intros bytes count t Encoding; exact Encoding.
Qed.

Theorem run_parse_source_locals_correct bytes local rest :
  run_parse_prefix (fun n => parse_locals (n := n)) bytes = Some (local, rest) <->
  exists prefix, bytes = prefix ++ rest /\ source_local_encoding prefix local.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_locals_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_locals_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest local Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (local, rest)).
    now rewrite Value, Rest.
Qed.
