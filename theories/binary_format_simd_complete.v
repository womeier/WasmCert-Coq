(** Ordered SIMD opcode-class disjointness and production completeness. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia Bool.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_atomic_properties binary_format_numeric_properties
  binary_format_numeric_complete binary_parser_lookahead_properties
  binary_format_vector_properties leb128_properties.
Local Notation byte := Byte.byte.
Open Scope nat_scope.

Inductive simd_kind :=
| SK_unop | SK_binop | SK_ternop | SK_testop | SK_shiftop | SK_splat | SK_lane.

Definition simd_kind_code kind code : Prop :=
  match kind with
  | SK_unop => opcode_is_unop code = true
  | SK_binop => code = 13%N \/ opcode_is_binop code = true
  | SK_ternop => opcode_is_ternop code = true
  | SK_testop => opcode_is_testop code = true
  | SK_shiftop => opcode_is_shiftop code = true
  | SK_splat => (15 <= code <= 20)%N
  | SK_lane => (21 <= code <= 34)%N
  end.

Ltac split_opcode_tests :=
  repeat rewrite Bool.orb_true_iff in *;
  repeat rewrite Bool.andb_true_iff in *;
  repeat rewrite N.eqb_eq in *;
  repeat rewrite N.leb_le in *.

Lemma simd_kind_disjoint kind1 kind2 code :
  simd_kind_code kind1 code -> simd_kind_code kind2 code -> kind1 = kind2.
Proof.
  destruct kind1, kind2; try reflexivity;
    unfold simd_kind_code, opcode_is_unop, opcode_is_binop, opcode_is_ternop,
      opcode_is_testop, opcode_is_shiftop;
    intros H1 H2; split_opcode_tests; intuition lia.
Qed.

Definition simd_prefix_encoding kind bytes (_ : basic_instruction) :=
  exists header tail code,
    bytes = header ++ tail /\ index_encoding header code /\
    simd_kind_code kind code.

Lemma guarded_simd_complete n classify (make : N -> basic_instruction)
    (R : list byte -> basic_instruction -> Prop) :
  (forall bytes be, R bytes be -> exists code,
    index_encoding bytes code /\ classify code = true /\ be = make code) ->
  parser_complete
    (Combinators.guardM
      (fun code => if classify code then Some (make code) else None)
      (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))) R.
Proof.
  intro Split.
  eapply parser_complete_guardM; [apply parse_u32_prefix_complete |].
  intros bytes be E. destruct (Split _ _ E) as [code [Encoding [Valid Value]]].
  exists code; split; [exact Encoding |]. now rewrite Valid, Value.
Qed.

Lemma guarded_simd_prefix_sound n classify (make : N -> basic_instruction) kind :
  (forall code, classify code = true -> simd_kind_code kind code) ->
  parser_sound
    (Combinators.guardM
      (fun code => if classify code then Some (make code) else None)
      (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)))
    (simd_prefix_encoding kind).
Proof.
  intro Kind. apply guarded_simd_index_sound.
  intros bytes code Encoding Valid.
  exists bytes, nil, code. rewrite app_nil_r. auto.
Qed.

Lemma simd_prefix_choice_right n p q previous current R :
  previous <> current ->
  @parser_sound basic_instruction n p (simd_prefix_encoding previous) ->
  (forall bytes be, R bytes be -> simd_prefix_encoding current bytes be) ->
  parser_complete q R -> parser_complete (Combinators.alt p q) R.
Proof.
  intros Different Sound Prefix Complete.
  eapply parser_complete_alt_right; [exact Sound |exact Complete |].
  intros xs ys tail1 tail2 a b
    [header1 [body1 [code1 [Bytes1 [Encoding1 Kind1]]]]] Rb Same.
  destruct (Prefix _ _ Rb) as [header2 [body2 [code2
    [Bytes2 [Encoding2 Kind2]]]]].
  subst xs ys.
  assert (code1 = code2) as Codes.
  { apply (index_encoding_prefix_injective header1 header2
      (body1 ++ tail1) (body2 ++ tail2) _ _ Encoding1 Encoding2).
    now repeat rewrite app_assoc. }
  subst code2. apply Different. now apply (simd_kind_disjoint _ _ code1).
Qed.

Definition simd_code_prefix code bytes (_ : basic_instruction) :=
  exists header tail, bytes = header ++ tail /\ index_encoding header code.

Lemma simd_code_choice_right n p q previous current R :
  previous <> current ->
  @parser_sound basic_instruction n p (simd_code_prefix previous) ->
  (forall bytes be, R bytes be -> simd_code_prefix current bytes be) ->
  parser_complete q R -> parser_complete (Combinators.alt p q) R.
Proof.
  intros Different Sound Prefix Complete.
  eapply parser_complete_alt_right; [exact Sound |exact Complete |].
  intros xs ys tail1 tail2 a b [h1 [b1 [Bytes1 Encoding1]]] Rb Same.
  destruct (Prefix _ _ Rb) as [h2 [b2 [Bytes2 Encoding2]]].
  subst xs ys. apply Different.
  apply (index_encoding_prefix_injective h1 h2 (b1 ++ tail1)
    (b2 ++ tail2) _ _ Encoding1 Encoding2).
  now repeat rewrite app_assoc.
Qed.

Lemma simd_splat_code_bound code shape :
  In (code, shape) simd_splat_codes -> (15 <= code <= 20)%N.
Proof.
  assert (Bounds : Forall (fun pair => (15 <= fst pair <= 20)%N) simd_splat_codes).
  { unfold simd_splat_codes; repeat constructor; cbn; lia. }
  exact ((proj1 (List.Forall_forall _ _)) Bounds (code, shape)).
Qed.

Lemma simd_lane_code_bound code make :
  In (code, make) simd_lane_codes -> (21 <= code <= 34)%N.
Proof.
  assert (Bounds : Forall (fun pair => (21 <= fst pair <= 34)%N) simd_lane_codes).
  { unfold simd_lane_codes; repeat constructor; cbn; lia. }
  exact ((proj1 (List.Forall_forall _ _)) Bounds (code, make)).
Qed.

Lemma simd_shuffle_prefix_sound n :
  parser_sound
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) 13%N)
      (box (Combinators.map
        (fun bs => BI_vbinop (13%N, List.map Byte.to_N bs))
        (parse_vec_aux anyTok 16%N))))
    (simd_code_prefix 13%N).
Proof.
  eapply parser_sound_rand_grammar with
    (P := fun bytes code => index_encoding bytes 13%N /\ code = 13%N)
    (Q := fun bytes be => length bytes = 16 /\
      be = BI_vbinop (13%N, List.map Byte.to_N bytes)).
  - apply assert_u32_sound.
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply (parse_raw_bytes_sound n 16%N) |].
    intros bytes lanes [Bytes Count]; subst lanes; split; [lia |reflexivity].
  - intros header lanes code be [Encoding _] _.
    exists header, lanes; auto.
Qed.

Lemma parse_simd_unop_prefix_sound n :
  parser_sound
    (parse_simd_unop (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_unop).
Proof.
  unfold parse_simd_unop. apply guarded_simd_prefix_sound; auto.
Qed.

Lemma parse_simd_binop_prefix_sound n :
  parser_sound
    (parse_simd_binop (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_binop).
Proof.
  unfold parse_simd_binop. apply parser_sound_alt.
  - eapply parser_sound_weaken; [apply simd_shuffle_prefix_sound |].
    intros bytes be [header [tail [Bytes Encoding]]].
    exists header, tail, 13%N. split; [exact Bytes |].
    split; [exact Encoding |left; reflexivity].
  - apply guarded_simd_prefix_sound.
    intros code Valid; now right.
Qed.

Lemma parse_simd_ternop_prefix_sound n :
  parser_sound
    (parse_simd_ternop (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_ternop).
Proof. unfold parse_simd_ternop; apply guarded_simd_prefix_sound; auto. Qed.
Lemma parse_simd_testop_prefix_sound n :
  parser_sound
    (parse_simd_testop (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_testop).
Proof. unfold parse_simd_testop; apply guarded_simd_prefix_sound; auto. Qed.
Lemma parse_simd_shiftop_prefix_sound n :
  parser_sound
    (parse_simd_shiftop (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_shiftop).
Proof. unfold parse_simd_shiftop; apply guarded_simd_prefix_sound; auto. Qed.

Lemma splat_prefix_sound n code shape :
  In (code, shape) simd_splat_codes ->
  parser_sound
    (Combinators.cmap (BI_splat_vec shape)
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code))
    (simd_prefix_encoding SK_splat).
Proof.
  intro Member.
  eapply parser_sound_cmap; [apply assert_u32_sound |].
  intros bytes c [Encoding _]. exists bytes, nil, code.
  rewrite app_nil_r. split; [reflexivity |].
  split; [exact Encoding |now apply (simd_splat_code_bound _ shape)].
Qed.

Lemma parse_simd_splat_prefix_sound n :
  parser_sound
    (parse_simd_splat (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_splat).
Proof.
  unfold parse_simd_splat.
  do 5 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply splat_prefix_sound; unfold simd_splat_codes; simpl; tauto.
Qed.

Lemma lane_prefix_sound n code make :
  In (code, make) simd_lane_codes ->
  parser_sound
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.map make parse_laneidx)))
    (simd_prefix_encoding SK_lane).
Proof.
  intro Member.
  eapply parser_sound_rand_grammar with
    (P := fun bytes c => index_encoding bytes code /\ c = code)
    (Q := fun bytes be => exists lane, bytes = lane :: nil /\
      be = make (Byte.to_N lane)).
  - apply assert_u32_sound.
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_laneidx_sound |].
    intros bytes x [lane [Bytes Value]]; subst. exists lane; auto.
  - intros header bytes c be [Encoding _] _.
    exists header, bytes, code. split; [reflexivity |].
    split; [exact Encoding |now apply (simd_lane_code_bound _ make)].
Qed.

Lemma parse_extract_replace_lane_prefix_sound n :
  parser_sound
    (parse_extract_replace_lane (Toks := SizedList byte) (M := option) (n := n))
    (simd_prefix_encoding SK_lane).
Proof.
  unfold parse_extract_replace_lane.
  do 13 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply lane_prefix_sound; unfold simd_lane_codes; simpl; tauto.
Qed.

Lemma asserted_fixed_complete n code (be : basic_instruction) :
  parser_complete
    (Combinators.cmap be
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code))
    (fun bytes value => index_encoding bytes code /\ value = be).
Proof.
  unfold Combinators.cmap.
  eapply parser_complete_map; [apply assert_u32_complete |].
  intros bytes value [Encoding Value]; subst value. exists code; auto.
Qed.

Lemma parse_laneidx_complete n :
  parser_complete
    (parse_laneidx (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => exists b, bytes = b :: nil /\ value = Byte.to_N b).
Proof.
  unfold parse_laneidx.
  eapply parser_complete_map; [apply parser_complete_anyTok |].
  intros bytes value [b [Bytes Value]]. exists b; auto.
Qed.

Definition lane_instruction_encoding code (make : N -> basic_instruction) bytes be :=
  exists header lane, bytes = header ++ (lane :: nil) /\
    index_encoding header code /\ be = make (Byte.to_N lane).

Lemma asserted_lane_complete n code make :
  parser_complete
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.map make parse_laneidx)))
    (lane_instruction_encoding code make).
Proof.
  eapply parser_complete_rand_grammar with
    (P := fun bytes value => index_encoding bytes code /\ value = code)
    (Q := fun bytes be => exists b, bytes = b :: nil /\
      be = make (Byte.to_N b)).
  - apply assert_u32_complete.
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_laneidx_complete |].
    intros bytes be [b [Bytes Value]].
    exists (Byte.to_N b); split; [exists b; auto |exact Value].
  - intros bytes be [header [lane [Bytes [Encoding Value]]]].
    exists header, (lane :: nil), code.
    split; [exact Bytes |]. split; [auto |exists lane; auto].
Qed.

Lemma asserted_fixed_prefix_sound n code (be : basic_instruction) :
  parser_sound
    (Combinators.cmap be
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code))
    (simd_code_prefix code).
Proof.
  eapply parser_sound_cmap; [apply assert_u32_sound |].
  intros bytes c [Encoding _]; exists bytes, nil.
  rewrite app_nil_r; auto.
Qed.

Lemma asserted_lane_prefix_sound n code make :
  parser_sound
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.map make parse_laneidx)))
    (simd_code_prefix code).
Proof.
  eapply parser_sound_rand_grammar with
    (P := fun bytes value => index_encoding bytes code /\ value = code)
    (Q := fun bytes be => exists b, bytes = b :: nil /\
      be = make (Byte.to_N b)).
  - apply assert_u32_sound.
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_laneidx_sound |].
    intros bytes value [b [Bytes Value]]; subst. exists b; auto.
  - intros header bytes c be [Encoding _] _; exists header, bytes; auto.
Qed.

Ltac asserted_simd_dispatch code Complete Prefix :=
  first
    [exact Complete
    |apply parser_complete_alt_left; exact Complete
    |lazymatch goal with
     | |- parser_complete (Combinators.alt ?p ?q) _ =>
       lazymatch p with
       | Combinators.cmap _ (assert_u32 ?old) =>
         eapply simd_code_choice_right with (previous := old) (current := code);
         [discriminate
         |apply asserted_fixed_prefix_sound
         |exact Prefix
         |asserted_simd_dispatch code Complete Prefix]
       | Combinators.rand (assert_u32 ?old) _ =>
         eapply simd_code_choice_right with (previous := old) (current := code);
         [discriminate
         |apply asserted_lane_prefix_sound
         |exact Prefix
         |asserted_simd_dispatch code Complete Prefix]
       end
     end].

Lemma parse_simd_splat_complete n code shape :
  In (code, shape) simd_splat_codes ->
  parser_complete
    (parse_simd_splat (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => index_encoding bytes code /\ value = BI_splat_vec shape).
Proof.
  intro Member.
  assert (Prefix : forall bytes value,
    index_encoding bytes code /\ value = BI_splat_vec shape ->
    simd_code_prefix code bytes value).
  { intros bytes value [E _]; exists bytes, nil; rewrite app_nil_r; auto. }
  unfold simd_splat_codes in Member; cbn [In] in Member.
  destruct Member as [E|[E|[E|[E|[E|[E|E]]]]]]; try contradiction;
    inversion E; subst code shape;
    unfold parse_simd_splat;
    lazymatch goal with
    | |- parser_complete _ (fun bytes value =>
        index_encoding bytes ?c /\ value = ?instruction) =>
      asserted_simd_dispatch c (asserted_fixed_complete n c instruction) Prefix
    end.
Qed.

Lemma parse_extract_replace_lane_complete n code make :
  In (code, make) simd_lane_codes ->
  parser_complete
    (parse_extract_replace_lane (Toks := SizedList byte) (M := option) (n := n))
    (lane_instruction_encoding code make).
Proof.
  intro Member.
  assert (Prefix : forall bytes value,
    lane_instruction_encoding code make bytes value ->
    simd_code_prefix code bytes value).
  { intros bytes value [header [lane [Bytes [E _]]]].
    exists header, (lane :: nil); auto. }
  unfold simd_lane_codes in Member; cbn [In] in Member.
  destruct Member as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]];
    try contradiction; inversion E; subst code make;
    unfold parse_extract_replace_lane;
    lazymatch goal with
    | |- parser_complete _ (lane_instruction_encoding ?c ?build) =>
      asserted_simd_dispatch c (asserted_lane_complete n c build) Prefix
    end.
Qed.

Definition shuffle_instruction_encoding bytes be :=
  exists header lanes, bytes = header ++ lanes /\
    index_encoding header 13%N /\ length lanes = 16 /\
    be = BI_vbinop (13%N, List.map Byte.to_N lanes).

Lemma parse_simd_shuffle_complete n :
  parser_complete
    (parse_simd_binop (Toks := SizedList byte) (M := option) (n := n))
    shuffle_instruction_encoding.
Proof.
  unfold parse_simd_binop. apply parser_complete_alt_left.
  eapply parser_complete_rand_grammar with
    (P := fun bytes value => index_encoding bytes 13%N /\ value = 13%N)
    (Q := fun bytes be => length bytes = 16 /\
      be = BI_vbinop (13%N, List.map Byte.to_N bytes)).
  - apply assert_u32_complete.
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map.
    + apply (parse_raw_bytes_complete n 16%N); discriminate.
    + intros bytes be [Count Value]. exists bytes.
      split; [split; [reflexivity |lia] |exact Value].
  - intros bytes be [header [lanes [Bytes [Encoding [Count Value]]]]].
    exists header, lanes, 13%N. split; [exact Bytes |].
    split; auto.
Qed.

Lemma parse_simd_binop_complete n code :
  opcode_is_binop code = true ->
  parser_complete
    (parse_simd_binop (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => index_encoding bytes code /\
      value = BI_vbinop (code, nil)).
Proof.
  intro Valid. unfold parse_simd_binop.
  eapply simd_code_choice_right with (previous := 13%N) (current := code).
  - intro E; subst code; discriminate.
  - apply simd_shuffle_prefix_sound.
  - intros bytes value [Encoding _]. exists bytes, nil; rewrite app_nil_r; auto.
  - apply guarded_simd_complete.
    intros bytes value [Encoding Value]. exists code; auto.
Qed.

Definition simd_kind_parser kind n :
    Parser (SizedList byte) byte option basic_instruction n :=
  match kind with
  | SK_unop => parse_simd_unop
  | SK_binop => parse_simd_binop
  | SK_ternop => parse_simd_ternop
  | SK_testop => parse_simd_testop
  | SK_shiftop => parse_simd_shiftop
  | SK_splat => parse_simd_splat
  | SK_lane => parse_extract_replace_lane
  end.

Ltac simd_previous_prefix :=
  first [apply parse_simd_unop_prefix_sound
        |apply parse_simd_binop_prefix_sound
        |apply parse_simd_ternop_prefix_sound
        |apply parse_simd_testop_prefix_sound
        |apply parse_simd_shiftop_prefix_sound
        |apply parse_simd_splat_prefix_sound
        |apply parse_extract_replace_lane_prefix_sound].

Ltac skip_simd old_kind new_kind Prefix :=
  eapply simd_prefix_choice_right with (previous := old_kind) (current := new_kind);
  [discriminate |simd_previous_prefix |exact Prefix |].

Lemma simd_dispatch_complete n kind R :
  parser_complete (simd_kind_parser kind n) R ->
  (forall bytes be, R bytes be -> simd_prefix_encoding kind bytes be) ->
  parser_complete
    (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n)) R.
Proof.
  intros Complete Prefix.
  destruct kind; cbn [simd_kind_parser] in Complete; unfold parse_simd_instruction.
  - apply parser_complete_alt_left; exact Complete.
  - skip_simd SK_unop SK_binop Prefix.
    apply parser_complete_alt_left; exact Complete.
  - skip_simd SK_unop SK_ternop Prefix.
    skip_simd SK_binop SK_ternop Prefix.
    apply parser_complete_alt_left; exact Complete.
  - skip_simd SK_unop SK_testop Prefix.
    skip_simd SK_binop SK_testop Prefix.
    skip_simd SK_ternop SK_testop Prefix.
    apply parser_complete_alt_left; exact Complete.
  - skip_simd SK_unop SK_shiftop Prefix.
    skip_simd SK_binop SK_shiftop Prefix.
    skip_simd SK_ternop SK_shiftop Prefix.
    skip_simd SK_testop SK_shiftop Prefix.
    apply parser_complete_alt_left; exact Complete.
  - skip_simd SK_unop SK_splat Prefix.
    skip_simd SK_binop SK_splat Prefix.
    skip_simd SK_ternop SK_splat Prefix.
    skip_simd SK_testop SK_splat Prefix.
    skip_simd SK_shiftop SK_splat Prefix.
    apply parser_complete_alt_left; exact Complete.
  - skip_simd SK_unop SK_lane Prefix.
    skip_simd SK_binop SK_lane Prefix.
    skip_simd SK_ternop SK_lane Prefix.
    skip_simd SK_testop SK_lane Prefix.
    skip_simd SK_shiftop SK_lane Prefix.
    skip_simd SK_splat SK_lane Prefix.
    exact Complete.
Qed.

Lemma simd_fixed_code_dispatch_complete n kind code be :
  simd_kind_code kind code ->
  parser_complete (simd_kind_parser kind n)
    (fun bytes value => index_encoding bytes code /\ value = be) ->
  parser_complete
    (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => index_encoding bytes code /\ value = be).
Proof.
  intros Kind Complete. apply (simd_dispatch_complete n kind); [exact Complete |].
  intros bytes value [Encoding _]. exists bytes, nil, code.
  rewrite app_nil_r. split; [reflexivity |]. auto.
Qed.

Theorem parse_simd_instruction_complete n :
  parser_complete
    (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
    simd_numeric_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding as
    [header code E Valid
    |header code E Valid
    |header code E Valid
    |header code E Valid
    |header code E Valid
    |header lanes E Count
    |header code shape E Member
    |header code make lane E Member].
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => index_encoding bytes code /\ value = BI_vunop code)).
    { apply (simd_fixed_code_dispatch_complete n SK_unop); [exact Valid |].
      cbn [simd_kind_parser]. unfold parse_simd_unop.
      apply guarded_simd_complete.
      intros bytes value [Enc Value]; exists code; auto. }
    apply (Complete m bound input header suffix (BI_vunop code) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => index_encoding bytes code /\
        value = BI_vbinop (code, nil))).
    { apply (simd_fixed_code_dispatch_complete n SK_binop).
      - now right.
      - apply parse_simd_binop_complete; exact Valid. }
    apply (Complete m bound input header suffix (BI_vbinop (code, nil)) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => index_encoding bytes code /\ value = BI_vternop code)).
    { apply (simd_fixed_code_dispatch_complete n SK_ternop); [exact Valid |].
      cbn [simd_kind_parser]. unfold parse_simd_ternop.
      apply guarded_simd_complete.
      intros bytes value [Enc Value]; exists code; auto. }
    apply (Complete m bound input header suffix (BI_vternop code) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => index_encoding bytes code /\ value = BI_vtestop code)).
    { apply (simd_fixed_code_dispatch_complete n SK_testop); [exact Valid |].
      cbn [simd_kind_parser]. unfold parse_simd_testop.
      apply guarded_simd_complete.
      intros bytes value [Enc Value]; exists code; auto. }
    apply (Complete m bound input header suffix (BI_vtestop code) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => index_encoding bytes code /\ value = BI_vshiftop code)).
    { apply (simd_fixed_code_dispatch_complete n SK_shiftop); [exact Valid |].
      cbn [simd_kind_parser]. unfold parse_simd_shiftop.
      apply guarded_simd_complete.
      intros bytes value [Enc Value]; exists code; auto. }
    apply (Complete m bound input header suffix (BI_vshiftop code) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      shuffle_instruction_encoding).
    { apply (simd_dispatch_complete n SK_binop); [apply parse_simd_shuffle_complete |].
      intros bytes value [h [ls [Parts [Enc _]]]].
      exists h, ls, 13%N. split; [exact Parts |].
      split; [exact Enc |left; reflexivity]. }
    apply (Complete m bound input (header ++ lanes) suffix
      (BI_vbinop (13%N, List.map Byte.to_N lanes)) Bytes).
    exists header, lanes; auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => index_encoding bytes code /\ value = BI_splat_vec shape)).
    { apply (simd_fixed_code_dispatch_complete n SK_splat).
      - now apply (simd_splat_code_bound _ shape).
      - now apply parse_simd_splat_complete. }
    apply (Complete m bound input header suffix (BI_splat_vec shape) Bytes); auto.
  - assert (Complete : parser_complete
      (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
      (lane_instruction_encoding code make)).
    { apply (simd_dispatch_complete n SK_lane).
      - now apply parse_extract_replace_lane_complete.
      - intros bytes value [h [b [Parts [Enc _]]]].
        exists h, (b :: nil), code. split; [exact Parts |].
        split; [exact Enc |now apply (simd_lane_code_bound _ make)]. }
    apply (Complete m bound input (header ++ (lane :: nil)) suffix
      (make (Byte.to_N lane)) Bytes).
    exists header, lane; auto.
Qed.

Lemma simd_encoding_has_kind bytes be :
  simd_numeric_encoding bytes be ->
  exists kind, simd_prefix_encoding kind bytes be.
Proof.
  intro E. destruct E.
  - exists SK_unop, bs, nil, code. rewrite app_nil_r; auto.
  - exists SK_binop, bs, nil, code. rewrite app_nil_r.
    split; [reflexivity |]. split; [assumption |now right].
  - exists SK_ternop, bs, nil, code. rewrite app_nil_r; auto.
  - exists SK_testop, bs, nil, code. rewrite app_nil_r; auto.
  - exists SK_shiftop, bs, nil, code. rewrite app_nil_r; auto.
  - exists SK_binop, header, lanes, 13%N.
    split; [reflexivity |]. split; [assumption |left; reflexivity].
  - exists SK_splat, header, nil, code. rewrite app_nil_r.
    split; [reflexivity |]. split; [assumption |].
    now apply (simd_splat_code_bound _ shape).
  - exists SK_lane, header, (lane :: nil), code.
    split; [reflexivity |]. split; [assumption |].
    now apply (simd_lane_code_bound _ make).
Qed.

Lemma simd_kind_not_const kind code :
  simd_kind_code kind code -> code <> 12%N.
Proof.
  intros Kind Equal; subst code; destruct kind;
    vm_compute in Kind; intuition discriminate.
Qed.

Definition fd_code_prefix code bytes (_ : basic_instruction) :=
  exists header payload,
    bytes = xfd :: header ++ payload /\ index_encoding header code.

Lemma v128_const_prefix_sound n :
  parser_sound
    (parse_v128_const (Toks := SizedList byte) (M := option) (n := n))
    (fd_code_prefix 12%N).
Proof.
  unfold parse_v128_const.
  eapply parser_sound_rand_grammar with
    (P := fun bytes _ => exists header,
      bytes = xfd :: header /\ index_encoding header 12%N)
    (Q := fun bytes be => length bytes = 16 /\
      be = BI_const_vec (VAL_vec128 (List.map compcert_byte_of_byte bytes))).
  - apply parser_sound_prefix_byte with
      (Q := fun bytes value => index_encoding bytes 12%N /\ value = 12%N).
    + intros k lt; simpl. apply parser_sound_le_lower; apply assert_u32_sound.
    + intros bytes value [E _]; exists bytes; auto.
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map with
      (P := fun bytes value => length bytes = 16 /\
        value = List.map compcert_byte_of_byte bytes).
    + unfold parse_16bytes.
      eapply parser_sound_map; [apply parse_raw_bytes_sound |].
      intros bytes lanes [Bytes Count]; subst lanes; split; [lia |reflexivity].
    + intros bytes value [Count Value]; subst value; auto.
  - intros first payload value be [header [Bytes E]] _; subst first.
    exists header, payload; auto.
Qed.

Definition simd_instruction_encoding bytes be :=
  exists body, bytes = xfd :: body /\ simd_numeric_encoding body be.

Lemma numeric_after_v128_complete n q R :
  (forall bytes be, R bytes be -> simd_instruction_encoding bytes be) ->
  @parser_complete basic_instruction n q R ->
  parser_complete
    (Combinators.alt
      (parse_v128_const (Toks := SizedList byte) (M := option) (n := n)) q) R.
Proof.
  intros Prefix Complete.
  eapply parser_complete_alt_right; [apply v128_const_prefix_sound |exact Complete |].
  intros xs ys tail1 tail2 a b [header [payload [Bytes E]]] Rb Same.
  destruct (Prefix _ _ Rb) as [body [Y G]].
  destruct (simd_encoding_has_kind _ _ G)
    as [kind [other [rest [code [Body [E' Kind]]]]]].
  subst xs ys body. simpl in Same; inversion Same as [Equal].
  assert (12%N = code) as Codes.
  { apply (index_encoding_prefix_injective header other
      (payload ++ tail1) (rest ++ tail2) _ _ E E').
    now repeat rewrite app_assoc. }
  exact (simd_kind_not_const kind code Kind (eq_sym Codes)).
Qed.

Ltac parser_term_head term :=
  lazymatch term with
  | ?f ?argument => parser_term_head f
  | _ => term
  end.

Ltac numeric_simd_dispatch Complete :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p ?q) _ =>
    let head := parser_term_head p in
    tryif constr_eq head (@parse_v128_const) then
      (eapply numeric_after_v128_complete;
       [intros bytes be E; exact E |numeric_simd_dispatch Complete])
    else
      (eapply parser_complete_alt_right_initial with (actual := xfd);
       [numeric_initial
       |discriminate
       |intros bytes be [body [Bytes _]]; now exists body
       |numeric_simd_dispatch Complete])
  | _ => exact Complete
  end.

Theorem parse_numeric_simd_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    simd_instruction_encoding.
Proof.
  assert (Leaf : parser_complete
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfd)
      (box parse_simd_instruction)) simd_instruction_encoding).
  { apply parser_complete_prefix_byte with (Q := simd_numeric_encoding).
    - intros k lt; simpl. apply parser_complete_le_lower.
      apply parse_simd_instruction_complete.
    - intros bytes be E; exact E. }
  unfold parse_numeric_instruction.
  numeric_simd_dispatch Leaf.
Qed.

Theorem parse_numeric_instruction_complete n :
  parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding as
    [opcode be Lower Opcode
    |payload v E Count
    |payload v E Count
    |payload Count
    |payload Count
    |header payload E Count
    |prefix code be E Opcode
    |body be E].
  - apply (parse_numeric_fixed_complete n opcode be Lower Opcode
      m bound input (opcode :: nil) suffix be Bytes); auto.
  - apply (parse_numeric_i32_complete n m bound input (x41 :: payload)
      suffix (BI_const_num (VAL_int32 v)) Bytes).
    exists payload, v; auto.
  - apply (parse_numeric_i64_complete n m bound input (x42 :: payload)
      suffix (BI_const_num (VAL_int64 v)) Bytes).
    exists payload, v; auto.
  - apply (parse_numeric_f32_complete n m bound input (x43 :: payload)
      suffix (BI_const_num (VAL_float32 (f32_from_bytes payload))) Bytes).
    exists payload; auto.
  - apply (parse_numeric_f64_complete n m bound input (x44 :: payload)
      suffix (BI_const_num (VAL_float64 (f64_from_bytes payload))) Bytes).
    exists payload; auto.
  - apply (parse_numeric_v128_complete n m bound input (xfd :: header ++ payload)
      suffix (BI_const_vec (VAL_vec128 (List.map compcert_byte_of_byte payload))) Bytes).
    exists header, payload; auto.
  - apply (parse_numeric_saturating_complete n code be Opcode
      m bound input prefix suffix be Bytes); auto.
  - apply (parse_numeric_simd_complete n m bound input (xfd :: body)
      suffix be Bytes). exists body; auto.
Qed.
