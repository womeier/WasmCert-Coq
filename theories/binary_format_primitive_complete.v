(** Cross-family dispatch, using only production parsers and byte grammars. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_index_lookahead_properties binary_format_atomic_properties
  binary_format_control_complete binary_format_memory_properties
  binary_format_memory_complete binary_format_numeric_properties
  binary_format_numeric_complete binary_format_simd_complete
  binary_format_dispatch_properties.
Local Notation byte := Byte.byte.

Ltac reject_extended_input prefixTag currentCode Header Bytes :=
  lazymatch goal with
  | |- runParser (Combinators.alt _ _) _ _ = None =>
      apply parser_alt_failure;
      [reject_extended_input prefixTag currentCode Header Bytes
      |reject_extended_input prefixTag currentCode Header Bytes]
  | _ =>
      first
        [eapply parser_initial_mismatch with (actual := prefixTag);
         [control_initial |discriminate |exact Bytes]
        |eapply parser_extended_mismatch with (tag := prefixTag) (actual := currentCode);
         [apply parser_initial_extended_rand; apply extended_assert_initial
         |lia |exact Bytes |exact Header]]
  end.

Lemma parse_table_reject_fc n m (bound : m <= n) input header code payload :
  input_bytes input = xfc :: header ++ payload ->
  index_encoding header code -> (code < 12)%N ->
  runParser (parse_table_instruction (Toks := SizedList byte) (M := option) (n := n))
    bound input = None.
Proof.
  intros Bytes Header Outside.
  unfold parse_table_instruction, parse_table_init, parse_elem_drop,
    parse_table_copy, parse_table_grow, parse_table_size, parse_table_fill.
  reject_extended_input xfc code Header Bytes.
Qed.

Lemma parse_memory_reject_fc n m (bound : m <= n) input header code payload :
  input_bytes input = xfc :: header ++ payload ->
  index_encoding header code -> (code < 8)%N ->
  runParser (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    bound input = None.
Proof.
  intros Bytes Header Outside.
  unfold parse_memory_instruction, parse_memory_init, parse_data_drop,
    parse_memory_copy, parse_memory_fill.
  reject_extended_input xfc code Header Bytes.
Qed.

Lemma parse_vector_payload_sound n :
  parser_sound
    (Combinators.alt (parse_v128_load (Toks := SizedList byte) (M := option) (n := n))
      (Combinators.alt parse_v128_load_packed
        (Combinators.alt parse_v128_load_splat
          (Combinators.alt parse_v128_load_zero
            (Combinators.alt parse_v128_store
              (Combinators.alt parse_v128_load_lane parse_v128_store_lane))))))
    vector_memory_encoding.
Proof.
  apply parser_sound_alt; [apply parse_vector_plain_load_sound |].
  apply parser_sound_alt; [apply parse_vector_packed_load_sound |].
  apply parser_sound_alt; [apply parse_vector_splat_load_sound |].
  apply parser_sound_alt; [apply parse_vector_zero_load_sound |].
  apply parser_sound_alt; [apply parse_vector_store_sound |].
  apply parser_sound_alt; [apply parse_vector_load_lane_sound |].
  apply parse_vector_store_lane_sound.
Qed.

Definition not_vector_memory_code code :=
  (forall make, ~ In (code, make) vector_memarg_opcodes) /\
  (forall make, ~ In (code, make) vector_memory_lane_opcodes).

Lemma parse_vector_memory_reject_fd n m (bound : m <= n) input header code payload :
  input_bytes input = xfd :: header ++ payload ->
  index_encoding header code -> not_vector_memory_code code ->
  runParser (parse_vector_memory_instruction
    (Toks := SizedList byte) (M := option) (n := n)) bound input = None.
Proof.
  intros Bytes Header [NotArg NotLane].
  assert (Sound : parser_sound (parse_vector_memory_instruction (n := n))
    (fun bytes be => exists body, bytes = xfd :: body /\ vector_memory_encoding body be)).
  { unfold parse_vector_memory_instruction.
    apply parser_sound_prefix_byte with (Q := vector_memory_encoding).
    - intros k lt; simpl; apply parser_sound_le_lower; apply parse_vector_payload_sound.
    - intros bytes be Enc; exists bytes; auto. }
  destruct (runParser (parse_vector_memory_instruction (n := n)) bound input) as [s|] eqn:Run;
    [|reflexivity].
  destruct (Sound _ _ _ _ Run) as [prefix [Input [body [Prefix Enc]]]].
  subst prefix; rewrite Bytes in Input; inversion Input as [Equal].
  destruct Enc as [actual make codebytes args marg Member Code Args
    |actual make codebytes args marg lane Member Code Args].
  - exfalso; apply (NotArg make).
    assert (Same : actual = code).
    { eapply index_encoding_prefix_injective; [exact Code |exact Header |].
      rewrite <- app_assoc in Equal; symmetry; exact Equal. }
    now subst actual.
  - exfalso; apply (NotLane make).
    assert (Same : actual = code).
    { eapply index_encoding_prefix_injective; [exact Code |exact Header |].
      rewrite <- app_assoc in Equal; symmetry; exact Equal. }
    now subst actual.
Qed.

Lemma parse_memory_reject_fd n m (bound : m <= n) input header code payload :
  input_bytes input = xfd :: header ++ payload ->
  index_encoding header code -> not_vector_memory_code code ->
  runParser (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    bound input = None.
Proof.
  intros Bytes Header Outside.
  unfold parse_memory_instruction.
  do 23 (apply parser_alt_failure;
    [eapply parser_initial_mismatch with (actual := xfd);
      [control_initial |discriminate |exact Bytes] |]).
  apply parser_alt_failure.
  - eapply parse_vector_memory_reject_fd; eassumption.
  - do 5 (apply parser_alt_failure; [shelve |]). Unshelve.
    all: eapply parser_initial_mismatch with (actual := xfd);
      [control_initial |discriminate |exact Bytes].
Qed.

Lemma numeric_simd_not_vector_memory kind code :
  simd_kind_code kind code -> not_vector_memory_code code.
Proof.
  intro Kind; split; intros make Member.
  - unfold vector_memarg_opcodes in Member; cbn [In] in Member.
    repeat destruct Member as [Member|Member]; try contradiction;
      inversion Member; subst code; destruct kind; vm_compute in Kind; intuition discriminate.
  - unfold vector_memory_lane_opcodes in Member; cbn [In] in Member.
    repeat destruct Member as [Member|Member]; try contradiction;
      inversion Member; subst code; destruct kind; vm_compute in Kind; intuition discriminate.
Qed.

Ltac layer_initial_set :=
  first
    [control_initial_set
    |unfold parse_reference_instruction; control_initial_set
    |unfold parse_parametric_instruction; control_initial_set
    |unfold parse_variable_instruction; control_initial_set
    |unfold parse_table_instruction; control_initial_set
    |unfold parse_memory_instruction; control_initial_set].

Ltac reject_layer_allowed :=
  cbn; intuition (try congruence; subst; cbn [Byte.to_N] in *; lia).

Ltac layer_dispatch tag Complete Head Other :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p _) _ =>
      let selected := lazymatch type of Complete with parser_complete ?q _ => q end in
      tryif constr_eq p selected then
        (apply parser_complete_alt_left; exact Complete)
      else
        first
          [let AllowedSet := open_constr:(_ : byte -> Prop) in
           let Initial := fresh "Initial" in
           assert (Initial : parser_initial_set p AllowedSet) by layer_initial_set;
           let Rejected := fresh "Rejected" in
           assert (Rejected : ~ AllowedSet tag) by reject_layer_allowed;
           eapply parser_complete_alt_right_initial_set with
             (Allowed := AllowedSet) (opcode := tag);
           [exact Initial |exact Rejected |exact Head
           |layer_dispatch tag Complete Head Other]
          |Other p; layer_dispatch tag Complete Head Other]
  | _ => exact Complete
  end.

Ltac reject_table_layer Failed p :=
  let head := parser_term_head p in
  constr_eq head (@parse_table_instruction);
  eapply parser_complete_alt_right_failure; [exact Failed |].

Ltac reject_memory_layer Failed p :=
  let head := parser_term_head p in
  constr_eq head (@parse_memory_instruction);
  eapply parser_complete_alt_right_failure; [exact Failed |].

Definition numeric_fc_encoding bytes be :=
  numeric_atomic_encoding bytes be /\
  exists header payload code, bytes = xfc :: header ++ payload /\
    index_encoding header code /\ (code < 8)%N.

Definition numeric_fd_encoding bytes be :=
  numeric_atomic_encoding bytes be /\
  exists header payload code, bytes = xfd :: header ++ payload /\
    index_encoding header code /\ not_vector_memory_code code.

Theorem parse_be_layer_numeric_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n) :
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    numeric_atomic_encoding.
Proof.
  assert (Normal : forall tag, (65 <= Byte.to_N tag <= 196)%N ->
    parser_complete (parse_be_layer (k := n) body branches)
      (fun bytes be => numeric_atomic_encoding bytes be /\ exists rest, bytes = tag :: rest)).
  { intros tag Valid.
    assert (Complete : parser_complete (parse_numeric_instruction (n := n))
      (fun bytes be => numeric_atomic_encoding bytes be /\ exists rest, bytes = tag :: rest)).
    { eapply parser_complete_weaken; [apply parse_numeric_instruction_complete |].
      intros bytes be [Enc _]; exact Enc. }
    assert (Head : forall bytes be,
      numeric_atomic_encoding bytes be /\ (exists rest, bytes = tag :: rest) ->
      exists rest, bytes = tag :: rest) by tauto.
    unfold parse_be_layer; cbv zeta.
    let Other := fun _ => fail in layer_dispatch tag Complete Head Other. }
  assert (CompleteFC : parser_complete (parse_numeric_instruction (n := n)) numeric_fc_encoding).
  { eapply parser_complete_weaken; [apply parse_numeric_instruction_complete |].
    intros bytes be [Enc _]; exact Enc. }
  assert (HeadFC : forall bytes be, numeric_fc_encoding bytes be ->
    exists rest, bytes = xfc :: rest).
  { intros bytes be [_ [header [payload [code [Bytes _]]]]].
    exists (header ++ payload); auto. }
  assert (FailedTableFC : forall m (bound : m <= n) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> numeric_fc_encoding prefix be ->
    runParser (parse_table_instruction (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Prefix [Header Range]]]]]].
    eapply parse_table_reject_fc with (code := code) (header := header) (payload := payload ++ suffix).
    - rewrite Bytes, Prefix; simpl; now rewrite app_assoc.
    - exact Header.
    - lia. }
  assert (FailedMemoryFC : forall m (bound : m <= n) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> numeric_fc_encoding prefix be ->
    runParser (parse_memory_instruction (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Prefix [Header Range]]]]]].
    eapply parse_memory_reject_fc with (code := code) (header := header) (payload := payload ++ suffix).
    - rewrite Bytes, Prefix; simpl; now rewrite app_assoc.
    - exact Header.
    - exact Range. }
  assert (LayerFC : parser_complete (parse_be_layer (k := n) body branches) numeric_fc_encoding).
  { unfold parse_be_layer; cbv zeta.
    let Other := fun p => first [reject_table_layer FailedTableFC p |reject_memory_layer FailedMemoryFC p] in
    layer_dispatch xfc CompleteFC HeadFC Other. }
  assert (CompleteFD : parser_complete (parse_numeric_instruction (n := n)) numeric_fd_encoding).
  { eapply parser_complete_weaken; [apply parse_numeric_instruction_complete |].
    intros bytes be [Enc _]; exact Enc. }
  assert (HeadFD : forall bytes be, numeric_fd_encoding bytes be ->
    exists rest, bytes = xfd :: rest).
  { intros bytes be [_ [header [payload [code [Bytes _]]]]].
    exists (header ++ payload); auto. }
  assert (FailedMemoryFD : forall m (bound : m <= n) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> numeric_fd_encoding prefix be ->
    runParser (parse_memory_instruction (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Prefix [Header Outside]]]]]].
    eapply parse_memory_reject_fd with (code := code) (header := header) (payload := payload ++ suffix).
    - rewrite Bytes, Prefix; simpl; now rewrite app_assoc.
    - exact Header.
    - exact Outside. }
  assert (LayerFD : parser_complete (parse_be_layer (k := n) body branches) numeric_fd_encoding).
  { unfold parse_be_layer; cbv zeta.
    let Other := fun p => reject_memory_layer FailedMemoryFD p in
    layer_dispatch xfd CompleteFD HeadFD Other. }
  intros m bound input prefix suffix be Bytes Enc.
  pose proof Enc as Saved.
  destruct Enc as
    [opcode be Lower Opcode
    |payload v Encoding Count
    |payload v Encoding Count
    |payload Count
    |payload Count
    |header payload Encoding Count
    |prefix code be Encoding Opcode
    |payload be Encoding].
  - assert (Bound : (N.to_nat (Byte.to_N opcode) - 69 < 128)%nat).
    { change (N.to_nat (Byte.to_N opcode) - 69 < length fixed_numeric_instructions)%nat.
      apply nth_error_Some; rewrite Opcode; discriminate. }
    apply (Normal opcode ltac:(lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists nil; reflexivity].
  - apply (Normal x41 ltac:(cbn; lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists payload; reflexivity].
  - apply (Normal x42 ltac:(cbn; lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists payload; reflexivity].
  - apply (Normal x43 ltac:(cbn; lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists payload; reflexivity].
  - apply (Normal x44 ltac:(cbn; lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists payload; reflexivity].
  - apply (LayerFD m bound input _ suffix _ Bytes).
    split; [exact Saved |exists header, payload, 12%N].
    split; [reflexivity |]. split; [exact Encoding |].
    split; intros make; cbn; intuition discriminate.
  - assert (Bound : (N.to_nat code < 8)%nat).
    { change (N.to_nat code < length saturating_instructions)%nat.
      apply nth_error_Some; rewrite Opcode; discriminate. }
    apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |].
    destruct Encoding as [header [Parts Header]]; exists header, nil, code.
    rewrite app_nil_r; split; [exact Parts |split; [exact Header |lia]].
  - apply (LayerFD m bound input _ suffix _ Bytes).
    split; [exact Saved |].
    destruct (simd_encoding_has_kind _ _ Encoding)
      as [kind [header [bodybytes [code [Parts [Header Kind]]]]]].
    exists header, bodybytes, code.
    split; [now rewrite Parts |split; [exact Header |now apply (numeric_simd_not_vector_memory kind)]].
Qed.

Definition memory_fc_encoding bytes be :=
  memory_instruction_encoding bytes be /\
  exists header payload code, bytes = xfc :: header ++ payload /\
    index_encoding header code /\ (8 <= code <= 11)%N.

Lemma scalar_memory_opcode_bound opcode make :
  In (opcode, make) scalar_memory_opcodes -> (40 <= Byte.to_N opcode <= 62)%N.
Proof.
  unfold scalar_memory_opcodes; cbn [In].
  intro Member; repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst opcode; cbn; lia.
Qed.

Theorem parse_be_layer_memory_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n) :
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    memory_instruction_encoding.
Proof.
  assert (Normal : forall tag, (tag = xfd \/ (40 <= Byte.to_N tag <= 64)%N) ->
    parser_complete (parse_be_layer (k := n) body branches)
      (fun bytes be => memory_instruction_encoding bytes be /\ exists rest, bytes = tag :: rest)).
  { intros tag Valid.
    assert (Complete : parser_complete (parse_memory_instruction (n := n))
      (fun bytes be => memory_instruction_encoding bytes be /\ exists rest, bytes = tag :: rest)).
    { eapply parser_complete_weaken; [apply parse_memory_instruction_complete |].
      intros bytes be [Enc _]; exact Enc. }
    assert (Head : forall bytes be,
      memory_instruction_encoding bytes be /\ (exists rest, bytes = tag :: rest) ->
      exists rest, bytes = tag :: rest) by tauto.
    unfold parse_be_layer; cbv zeta.
    let Other := fun _ => fail in layer_dispatch tag Complete Head Other. }
  assert (CompleteFC : parser_complete (parse_memory_instruction (n := n)) memory_fc_encoding).
  { eapply parser_complete_weaken; [apply parse_memory_instruction_complete |].
    intros bytes be [Enc _]; exact Enc. }
  assert (HeadFC : forall bytes be, memory_fc_encoding bytes be ->
    exists rest, bytes = xfc :: rest).
  { intros bytes be [_ [header [payload [code [Bytes _]]]]].
    exists (header ++ payload); auto. }
  assert (FailedTable : forall m (bound : m <= n) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> memory_fc_encoding prefix be ->
    runParser (parse_table_instruction (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Prefix [Header Range]]]]]].
    eapply parse_table_reject_fc with (code := code) (header := header) (payload := payload ++ suffix).
    - rewrite Bytes, Prefix; simpl; now rewrite app_assoc.
    - exact Header.
    - lia. }
  assert (LayerFC : parser_complete (parse_be_layer (k := n) body branches) memory_fc_encoding).
  { unfold parse_be_layer; cbv zeta.
    let Other := fun p => reject_table_layer FailedTable p in
    layer_dispatch xfc CompleteFC HeadFC Other. }
  intros m bound input prefix suffix be Bytes Enc.
  pose proof Enc as Saved.
  destruct Enc as
    [opcode make payload marg Member Payload
    |payload be Vector
    |
    |
    |header data x Header Data
    |header data x Header Data
    |header Header
    |header Header].
  - apply (Normal opcode ltac:(right; pose proof (scalar_memory_opcode_bound _ _ Member); lia)
      m bound input _ suffix _ Bytes).
    split; [exact Saved |exists payload; reflexivity].
  - apply (Normal xfd ltac:(now left) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists payload; reflexivity].
  - apply (Normal x3f ltac:(right; cbn; lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists (x00 :: nil); reflexivity].
  - apply (Normal x40 ltac:(right; cbn; lia) m bound input _ suffix _ Bytes).
    split; [exact Saved |exists (x00 :: nil); reflexivity].
  - apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |exists header, (data ++ x00 :: nil), 8%N].
    split; [reflexivity |split; [exact Header |lia]].
  - apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |exists header, data, 9%N].
    split; [reflexivity |split; [exact Header |lia]].
  - apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |exists header, (x00 :: x00 :: nil), 10%N].
    split; [reflexivity |split; [exact Header |lia]].
  - apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |exists header, (x00 :: nil), 11%N].
    split; [reflexivity |split; [exact Header |lia]].
Qed.

Theorem wasm_parse_be_layer_atomic_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n) :
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    wasm_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Enc.
  destruct Enc as [Control|[Bulk|[Numeric|Memory]]].
  - eapply parse_be_layer_control_complete; eassumption.
  - eapply parse_be_layer_bulk_complete; eassumption.
  - eapply parse_be_layer_numeric_complete; eassumption.
  - eapply parse_be_layer_memory_complete; eassumption.
Qed.
