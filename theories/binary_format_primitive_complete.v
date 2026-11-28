(** First-byte and extended-opcode disjointness for production atomic
    alternatives in [parse_be_layer]. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_control_complete
  binary_memory_grammar_properties binary_memory_properties
  binary_parser_combinators binary_codec binary_format_simd_complete
  binary_format_numeric_properties binary_format_dispatch_properties
  binary_format_type_properties.
Local Notation byte := Byte.byte.

Definition tail_initial b := b = x12 \/ b = x13.
Definition reference_initial b :=
  b = xd0 \/ b = xd1 \/ b = xd2 \/ b = xd4 \/ b = xfb \/ b = xd5 \/ b = xd6.
Definition parametric_initial b := b = x1a \/ b = x1b \/ b = x1c.
Definition variable_initial b :=
  b = x20 \/ b = x21 \/ b = x22 \/ b = x23 \/ b = x24.
Definition table_initial b := b = x25 \/ b = x26 \/ b = xfc.
Definition memory_initial b :=
  b = xfc \/ b = xfd \/ (40 <= Byte.to_N b <= 64)%N.

Lemma parse_tail_call_initial n :
  parser_initial_set
    (parse_tail_call (Toks := SizedList byte) (M := option) (n := n)) tail_initial.
Proof.
  unfold parse_tail_call. apply parser_initial_set_alt.
  all: eapply parser_initial_set_single; [numeric_initial |].
  all: unfold tail_initial; auto.
Qed.

Lemma parse_reference_initial n :
  parser_initial_set
    (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
    reference_initial.
Proof.
  unfold parse_reference_instruction.
  repeat apply parser_initial_set_alt.
  all: eapply parser_initial_set_single; [numeric_initial |].
  all: unfold reference_initial; tauto.
Qed.

Lemma parse_parametric_initial n :
  parser_initial_set
    (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
    parametric_initial.
Proof.
  unfold parse_parametric_instruction.
  do 2 (apply parser_initial_set_alt; [shelve |]). Unshelve.
  all: eapply parser_initial_set_single; [numeric_initial |].
  all: unfold parametric_initial; auto.
Qed.

Lemma parse_variable_initial n :
  parser_initial_set
    (parse_variable_instruction (Toks := SizedList byte) (M := option) (n := n))
    variable_initial.
Proof.
  unfold parse_variable_instruction.
  do 4 (apply parser_initial_set_alt; [shelve |]). Unshelve.
  all: eapply parser_initial_set_single; [numeric_initial |].
  all: unfold variable_initial; auto.
Qed.

Lemma parse_table_initial n :
  parser_initial_set
    (parse_table_instruction (Toks := SizedList byte) (M := option) (n := n))
    table_initial.
Proof.
  unfold parse_table_instruction.
  do 7 (apply parser_initial_set_alt; [shelve |]). Unshelve.
  all: eapply parser_initial_set_single; [numeric_initial |].
  all: unfold table_initial; auto.
Qed.

Lemma memory_grammar_initial bytes be :
  binary_memory_instruction bytes be ->
  exists first rest, bytes = first :: rest /\ memory_initial first.
Proof.
  intro E. destruct E as [op bytes be E|op bytes be E|bytes be E].
  - destruct E as [args [marg [Bytes [E Value]]]]; subst bytes.
    exists (scalar_memop_tag op), args; split; [reflexivity |].
    right; right; destruct op; cbn; lia.
  - destruct E.
    + exists x3f, args; split; [reflexivity |right; right; cbn; lia].
    + exists x40, args; split; [reflexivity |right; right; cbn; lia].
    + exists xfc, (code ++ args); split; [reflexivity |now left].
    + exists xfc, (code ++ dest ++ src); split; [reflexivity |now left].
    + exists xfc, (code ++ data ++ mem); split; [reflexivity |now left].
    + exists xfc, (code ++ args); split; [reflexivity |now left].
  - destruct E.
    + exists xfd, (opbytes ++ args); split; [reflexivity |right; now left].
    + exists xfd, (opbytes ++ args ++ (lane :: nil));
        split; [reflexivity |right; now left].
Qed.

Lemma parse_memory_initial n :
  parser_initial_set
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    memory_initial.
Proof.
  eapply parser_initial_set_from_sound.
  - exact (parse_memory_instruction_binary_sound n).
  - exact memory_grammar_initial.
Qed.

Lemma prefix_semantics_failure {A} (p : byte_parser_family A) decode :
  prefix_semantics p decode ->
  forall n m (bound : (m <= n)%nat) (input : SizedList byte m),
    decode (input_bytes input) = None ->
    runParser (p n) bound input = None.
Proof.
  intros Prefix n m bound [bytes Size] Failed.
  cbn in Size; subst m.
  rewrite binary_codec.sized_list_refl.
  pose proof (Prefix n bytes bound) as Observed.
  change (decode bytes = None) in Failed; rewrite Failed in Observed.
  destruct (runParser (p n) bound (mkSizedList bytes)) as [s|]; [|reflexivity].
  discriminate.
Qed.

Lemma decode_table_reject_fc header code payload :
  index_encoding header code ->
  ((code < 12)%N \/ (17 < code)%N) ->
  decode_table_instruction (xfc :: header ++ payload) = None.
Proof.
  intros Encoding Outside.
  unfold decode_table_instruction, decode_or, decode_sequence,
    decode_exact_byte, decode_fc_prefix, decode_assert_u32.
  cbn -[decode_uint].
  repeat rewrite (index_encoding_decode_suffix header code Encoding).
  assert (Different : forall k, (12 <= k <= 17)%N -> N.eqb code k = false).
  { intros k Bound. apply N.eqb_neq; lia. }
  rewrite (Different 12%N ltac:(lia)), (Different 13%N ltac:(lia)),
    (Different 14%N ltac:(lia)), (Different 15%N ltac:(lia)),
    (Different 16%N ltac:(lia)), (Different 17%N ltac:(lia)).
  reflexivity.
Qed.

Lemma parse_table_reject_fc n m (bound : (m <= n)%nat)
    (input : SizedList byte m) header code payload :
  input_bytes input = xfc :: header ++ payload ->
  index_encoding header code -> ((code < 12)%N \/ (17 < code)%N) ->
  runParser (parse_table_instruction (M := option) (n := n)) bound input = None.
Proof.
  intros Bytes Encoding Outside.
  apply (prefix_semantics_failure (fun n => parse_table_instruction)
    decode_table_instruction table_instruction_prefix_correct).
  rewrite Bytes; exact (decode_table_reject_fc header code payload Encoding Outside).
Qed.

Lemma decode_memory_reject_fc header code payload :
  index_encoding header code ->
  ((code < 8)%N \/ (11 < code)%N) ->
  decode_memory_instruction (xfc :: header ++ payload) = None.
Proof.
  intros Encoding Outside.
  unfold decode_memory_instruction, scalar_memops, decode_or,
    decode_tagged_memarg, decode_exact_byte.
  cbn -[decode_uint].
  unfold decode_indexed_memop, decode_vector_memory, decode_fc_prefix,
    decode_sequence, decode_assert_u32.
  cbn -[decode_uint].
  repeat rewrite (index_encoding_decode_suffix header code Encoding).
  assert (Different : forall k, (8 <= k <= 11)%N -> N.eqb code k = false).
  { intros k Bound. apply N.eqb_neq; lia. }
  rewrite (Different 8%N ltac:(lia)), (Different 9%N ltac:(lia)),
    (Different 10%N ltac:(lia)), (Different 11%N ltac:(lia)).
  reflexivity.
Qed.

Lemma parse_memory_reject_fc n m (bound : (m <= n)%nat)
    (input : SizedList byte m) header code payload :
  input_bytes input = xfc :: header ++ payload ->
  index_encoding header code -> ((code < 8)%N \/ (11 < code)%N) ->
  runParser (parse_memory_instruction (M := option) (n := n)) bound input = None.
Proof.
  intros Bytes Encoding Outside.
  apply (prefix_semantics_failure (fun n => parse_memory_instruction)
    decode_memory_instruction memory_instruction_prefix_correct).
  rewrite Bytes; exact (decode_memory_reject_fc header code payload Encoding Outside).
Qed.

Lemma decode_memory_reject_fd header code payload :
  index_encoding header code -> vector_memory_opcode code = None ->
  decode_memory_instruction (xfd :: header ++ payload) = None.
Proof.
  intros Encoding NotMemory.
  unfold decode_memory_instruction, scalar_memops, decode_or,
    decode_tagged_memarg, decode_exact_byte.
  cbn -[decode_uint decode_vector_memory].
  unfold decode_vector_memory, decode_sequence.
  cbn -[decode_uint decode_vector_memory_tail].
  rewrite (index_encoding_decode_suffix header code Encoding payload).
  unfold decode_vector_memory_tail; rewrite NotMemory.
  reflexivity.
Qed.

Lemma parse_memory_reject_fd n m (bound : (m <= n)%nat)
    (input : SizedList byte m) header code payload :
  input_bytes input = xfd :: header ++ payload ->
  index_encoding header code -> vector_memory_opcode code = None ->
  runParser (parse_memory_instruction (M := option) (n := n)) bound input = None.
Proof.
  intros Bytes Encoding NotMemory.
  apply (prefix_semantics_failure (fun n => parse_memory_instruction)
    decode_memory_instruction memory_instruction_prefix_correct).
  rewrite Bytes; exact (decode_memory_reject_fd header code payload Encoding NotMemory).
Qed.

Lemma numeric_simd_not_vector_memory kind code :
  simd_kind_code kind code -> vector_memory_opcode code = None.
Proof.
  intro Kind.
  destruct (vector_memory_opcode code) as [args|] eqn:Memory; [|reflexivity].
  exfalso.
  pose proof (vector_memory_opcode_bound code args Memory) as Bound.
  set (k := N.to_nat code).
  assert (Code : code = N.of_nat k) by (unfold k; now rewrite N2Nat.id).
  rewrite Code in Kind, Memory, Bound.
  clearbody k; clear Code code.
  do 128 (destruct k as [|k];
    [cbn in Memory; try discriminate;
      destruct kind; vm_compute in Kind; intuition discriminate |]).
  change (N.of_nat (128 + k) < 128)%N in Bound.
  rewrite Nat2N.inj_add in Bound. cbn [N.of_nat] in Bound. lia.
Qed.

Ltac layer_initial_set :=
  lazymatch goal with
  | |- parser_initial_set ?p _ =>
    let head := parser_term_head p in
    first
      [constr_eq head (@parse_tail_call); apply parse_tail_call_initial
      |constr_eq head (@parse_reference_instruction); apply parse_reference_initial
      |constr_eq head (@parse_parametric_instruction); apply parse_parametric_initial
      |constr_eq head (@parse_variable_instruction); apply parse_variable_initial
      |constr_eq head (@parse_table_instruction); apply parse_table_initial
      |constr_eq head (@parse_memory_instruction); apply parse_memory_initial
      |constr_eq head (@Combinators.map);
         apply parser_initial_exact_set; apply parser_initial_map; numeric_initial
      |apply parser_initial_exact_set; numeric_initial]
  end.

Ltac reject_layer_initial :=
  unfold tail_initial, reference_initial, parametric_initial, variable_initial,
    table_initial, memory_initial in *;
  intuition (try congruence;
    try (repeat match goal with
      | H : ?b = ?c |- _ => is_var b; subst b
      | H : ?b = ?c |- _ => is_var c; subst c
      end; cbn [Byte.to_N] in *; lia)).

Ltac normal_layer_dispatch tag Complete Head :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p ?q) _ =>
    let selected :=
      lazymatch type of Complete with parser_complete ?parser _ => parser end in
    let actual_head := parser_term_head p in
    let selected_head := parser_term_head selected in
    tryif constr_eq actual_head selected_head then
      (apply parser_complete_alt_left; exact Complete)
    else
      (let AllowedSet := open_constr:(_ : byte -> Prop) in
       let Initial := fresh "Initial" in
       assert (Initial : parser_initial_set p AllowedSet) by layer_initial_set;
       eapply parser_complete_alt_right_initial_set with
         (Allowed := AllowedSet) (opcode := tag);
       [exact Initial
       |reject_layer_initial
       |exact Head
       |normal_layer_dispatch tag Complete Head])
  | _ => exact Complete
  end.

Theorem parse_be_layer_variable_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) opcode make :
  In (opcode, make) variable_opcodes ->
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    (indexed_instruction_encoding opcode make).
Proof.
  intro Member.
  pose proof (parse_variable_instruction_complete n opcode make Member) as Complete.
  pose proof (indexed_instruction_head opcode make) as Head.
  unfold variable_opcodes in Member; cbn [In] in Member.
  destruct Member as [E|[E|[E|[E|[E|E]]]]]; try contradiction;
    inversion E; subst opcode make;
    unfold parse_be_layer;
    lazymatch type of Head with
    | forall bytes be, indexed_instruction_encoding ?op _ bytes be -> _ =>
      normal_layer_dispatch op Complete Head
    end.
Qed.

Theorem parse_be_layer_tail_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    binary_format_tail_properties.tail_instruction_encoding.
Proof.
  unfold parse_be_layer. apply parser_complete_alt_left.
  apply parse_tail_call_complete.
Qed.

Theorem parse_be_layer_reference_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    reference_instruction_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding as [Null|[IsNull|Func]].
  - assert (Complete : parser_complete
      (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
      ref_null_instruction_encoding).
    { eapply parser_complete_weaken; [apply parse_reference_instruction_complete |].
      intros bs value E; now left. }
    assert (Head : forall bs value, ref_null_instruction_encoding bs value ->
      exists rest, bs = xd0 :: rest).
    { intros bs value [payload [t [Parts _]]]; now exists payload. }
    assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      ref_null_instruction_encoding).
    { unfold parse_be_layer; normal_layer_dispatch xd0 Complete Head. }
    now apply (Layer m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = xd1 :: nil /\ value = BI_ref_is_null)).
    { eapply parser_complete_weaken; [apply parse_reference_instruction_complete |].
      intros bs value E; right; now left. }
    assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (fun bs value => bs = xd1 :: nil /\ value = BI_ref_is_null)).
    { unfold parse_be_layer.
      normal_layer_dispatch xd1 Complete
        (binary_format_type_properties.fixed_encoding_head xd1 BI_ref_is_null). }
    now apply (Layer m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
      (indexed_instruction_encoding xd2 BI_ref_func)).
    { eapply parser_complete_weaken; [apply parse_reference_instruction_complete |].
      intros bs value E; right; now right. }
    assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (indexed_instruction_encoding xd2 BI_ref_func)).
    { unfold parse_be_layer.
      normal_layer_dispatch xd2 Complete (indexed_instruction_head xd2 BI_ref_func). }
    now apply (Layer m bound input prefix suffix be Bytes).
Qed.

Theorem parse_be_layer_parametric_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    parametric_instruction_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding as [Drop|[Select|Typed]].
  - assert (Complete : parser_complete
      (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = x1a :: nil /\ value = BI_drop)).
    { eapply parser_complete_weaken; [apply parse_parametric_instruction_complete |].
      intros bs value E; now left. }
    assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (fun bs value => bs = x1a :: nil /\ value = BI_drop)).
    { unfold parse_be_layer.
      normal_layer_dispatch x1a Complete
        (binary_format_type_properties.fixed_encoding_head x1a BI_drop). }
    now apply (Layer m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bs value => bs = x1b :: nil /\ value = BI_select None)).
    { eapply parser_complete_weaken; [apply parse_parametric_instruction_complete |].
      intros bs value E; right; now left. }
    assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (fun bs value => bs = x1b :: nil /\ value = BI_select None)).
    { unfold parse_be_layer.
      normal_layer_dispatch x1b Complete
        (binary_format_type_properties.fixed_encoding_head x1b (BI_select None)). }
    now apply (Layer m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
      typed_select_instruction_encoding).
    { eapply parser_complete_weaken; [apply parse_parametric_instruction_complete |].
      intros bs value E; right; now right. }
    assert (Head : forall bs value, typed_select_instruction_encoding bs value ->
      exists rest, bs = x1c :: rest).
    { intros bs value [payload [types [Parts _]]]; now exists payload. }
    assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      typed_select_instruction_encoding).
    { unfold parse_be_layer; normal_layer_dispatch x1c Complete Head. }
    now apply (Layer m bound input prefix suffix be Bytes).
Qed.

Theorem parse_be_layer_table_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    table_instruction_encoding.
Proof.
  assert (CompleteFC : parser_complete
    (parse_table_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bs value => table_instruction_encoding bs value /\
      exists rest, bs = xfc :: rest)).
  { eapply parser_complete_weaken; [apply parse_table_instruction_complete |].
    intros bs value [E _]; exact E. }
  assert (HeadFC : forall bs value,
    table_instruction_encoding bs value /\ (exists rest, bs = xfc :: rest) ->
    exists rest, bs = xfc :: rest) by tauto.
  assert (LayerFC : parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    (fun bs value => table_instruction_encoding bs value /\
      exists rest, bs = xfc :: rest)).
  { unfold parse_be_layer; normal_layer_dispatch xfc CompleteFC HeadFC. }
  intros m bound input prefix suffix be Bytes Encoding.
  pose proof Encoding as Saved.
  destruct Encoding.
  - { assert (Complete : parser_complete
      (parse_table_instruction (Toks := SizedList byte) (M := option) (n := n))
      (indexed_instruction_encoding opcode make)).
    { eapply parser_complete_weaken; [apply parse_table_instruction_complete |].
      intros bs value [body [x [Parts [E Value]]]]; subst bs value.
      now apply table_single_encoding. }
    pose proof (indexed_instruction_head opcode make) as Head.
    unfold table_single_opcodes in H; cbn [In] in H.
    destruct H as [Eq|[Eq|Eq]]; try contradiction; inversion Eq; subst opcode make.
    all: assert (Layer : parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (indexed_instruction_encoding _ _)) by
      (unfold parse_be_layer;
       lazymatch type of Head with
       | forall bs value, indexed_instruction_encoding ?op _ bs value -> _ =>
         normal_layer_dispatch op Complete Head
       end).
    all: apply (Layer m bound input _ suffix _ Bytes).
    all: exists payload, index; split; [reflexivity |].
    all: split; [assumption |reflexivity]. }
  - apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |eexists; reflexivity].
  - apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |eexists; reflexivity].
Qed.

Lemma binary_u32_index_encoding bytes index :
  binary_format_properties.binary_u32 bytes index -> index_encoding bytes index.
Proof.
  intro Encoding.
  destruct (parse_u32_binary_complete (length bytes) _ (Nat.le_refl _)
    (mkSizedList bytes) bytes nil index
    ltac:(unfold input_bytes; simpl; now rewrite app_nil_r) Encoding)
    as [s [Run [Value Rest]]].
  destruct (binary_format_vector_properties.parse_u32_bounded_prefix_sound
    (length bytes) _ (Nat.le_refl _) (mkSizedList bytes) s Run)
    as [prefix [Bytes E]].
  change (input_bytes (mkSizedList bytes) = prefix ++ output_bytes s) in Bytes.
  change (output_bytes s = nil) in Rest.
  rewrite Rest, app_nil_r in Bytes.
  change (bytes = prefix) in Bytes; subst prefix.
  rewrite Value in E; exact E.
Qed.

Ltac extended_layer_dispatch tag Complete Head Other :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p ?q) _ =>
    let selected :=
      lazymatch type of Complete with parser_complete ?parser _ => parser end in
    let actual_head := parser_term_head p in
    let selected_head := parser_term_head selected in
    tryif constr_eq actual_head selected_head then
      (apply parser_complete_alt_left; exact Complete)
    else
      first
        [(let AllowedSet := open_constr:(_ : byte -> Prop) in
          let Initial := fresh "Initial" in
          assert (Initial : parser_initial_set p AllowedSet) by layer_initial_set;
          eapply parser_complete_alt_right_initial_set with
            (Allowed := AllowedSet) (opcode := tag);
          [exact Initial
          |solve [reject_layer_initial]
          |exact Head
          |extended_layer_dispatch tag Complete Head Other])
        |Other constr:(tt); extended_layer_dispatch tag Complete Head Other]
  | _ => exact Complete
  end.

Ltac reject_table_layer Failed :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p _) _ =>
    let head := parser_term_head p in
    constr_eq head (@parse_table_instruction);
    eapply parser_complete_alt_right_failure; [exact Failed |]
  end.

Definition memory_fc_encoding bytes be :=
  binary_memory_instruction bytes be /\
  exists header payload code, bytes = xfc :: header ++ payload /\
    binary_format_properties.binary_u32 header code /\ (8 <= code <= 11)%N.

Theorem parse_be_layer_memory_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    binary_memory_instruction.
Proof.
  assert (CompleteFC : parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    memory_fc_encoding).
  { eapply parser_complete_weaken; [exact (parse_memory_instruction_binary_complete n) |].
    intros bytes value [E _]; exact E. }
  assert (HeadFC : forall bytes value, memory_fc_encoding bytes value ->
    exists rest, bytes = xfc :: rest).
  { intros bytes value [_ [header [payload [code [Parts _]]]]].
    now exists (header ++ payload). }
  assert (FailedTable : forall m (bound : (m <= n)%nat) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> memory_fc_encoding prefix be ->
    runParser (parse_table_instruction (M := option) (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Parts [Encoding Range]]]]]].
    apply (parse_table_reject_fc n m bound input header code (payload ++ suffix)).
    - rewrite Bytes, Parts. simpl. now rewrite app_assoc.
    - now apply binary_u32_index_encoding.
    - left; lia. }
  assert (LayerFC : parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    memory_fc_encoding).
  { unfold parse_be_layer.
    let Other := fun _ => reject_table_layer FailedTable in
    extended_layer_dispatch xfc CompleteFC HeadFC Other. }
  assert (Normal : forall tag,
    (tag = xfd \/ (40 <= Byte.to_N tag <= 64)%N) ->
    parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (fun bytes value => binary_memory_instruction bytes value /\
        exists rest, bytes = tag :: rest)).
  { intros tag Valid.
    assert (Complete : parser_complete
      (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => binary_memory_instruction bytes value /\
        exists rest, bytes = tag :: rest)).
    { eapply parser_complete_weaken; [exact (parse_memory_instruction_binary_complete n) |].
      intros bytes value [E _]; exact E. }
    assert (Head : forall bytes value,
      binary_memory_instruction bytes value /\ (exists rest, bytes = tag :: rest) ->
      exists rest, bytes = tag :: rest) by tauto.
    unfold parse_be_layer.
    normal_layer_dispatch tag Complete Head. }
  intros m bound input prefix suffix be Bytes Encoding.
  pose proof Encoding as Saved.
  destruct Encoding as [op bytes be E|op bytes be E|bytes be E].
  - destruct E as [args [marg [Parts [E Value]]]]; subst bytes.
    apply (Normal (scalar_memop_tag op) ltac:(right; destruct op; cbn; lia)
      m bound input _ suffix be Bytes).
    split; [exact Saved |exists args; reflexivity].
  - destruct E.
    + apply (Normal x3f ltac:(right; cbn; lia)
        m bound input _ suffix _ Bytes).
      split; [exact Saved |exists args; reflexivity].
    + apply (Normal x40 ltac:(right; cbn; lia)
        m bound input _ suffix _ Bytes).
      split; [exact Saved |exists args; reflexivity].
    + apply (LayerFC m bound input _ suffix _ Bytes).
      split; [exact Saved |]. exists code, args, 11%N.
      split; [reflexivity |]. split; [assumption |lia].
    + apply (LayerFC m bound input _ suffix _ Bytes).
      split; [exact Saved |]. exists code, (dest ++ src), 10%N.
      split; [reflexivity |]. split; [assumption |lia].
    + apply (LayerFC m bound input _ suffix _ Bytes).
      split; [exact Saved |]. exists code, (data ++ mem), 8%N.
      split; [reflexivity |]. split; [assumption |lia].
    + apply (LayerFC m bound input _ suffix _ Bytes).
      split; [exact Saved |]. exists code, args, 9%N.
      split; [reflexivity |]. split; [assumption |lia].
  - destruct E.
    + apply (Normal xfd ltac:(now left) m bound input _ suffix _ Bytes).
      split; [exact Saved |eexists; reflexivity].
    + apply (Normal xfd ltac:(now left) m bound input _ suffix _ Bytes).
      split; [exact Saved |eexists; reflexivity].
Qed.

Ltac reject_memory_layer Failed :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt ?p _) _ =>
    let head := parser_term_head p in
    constr_eq head (@parse_memory_instruction);
    eapply parser_complete_alt_right_failure; [exact Failed |]
  end.

Definition numeric_fc_encoding bytes be :=
  numeric_atomic_encoding bytes be /\
  exists header payload code, bytes = xfc :: header ++ payload /\
    index_encoding header code /\ (code < 8)%N.

Definition numeric_fd_encoding bytes be :=
  numeric_atomic_encoding bytes be /\
  exists header payload code, bytes = xfd :: header ++ payload /\
    index_encoding header code /\ vector_memory_opcode code = None.

Theorem parse_be_layer_numeric_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    numeric_atomic_encoding.
Proof.
  assert (Normal : forall tag, (65 <= Byte.to_N tag <= 196)%N ->
    parser_complete
      (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
      (fun bytes value => numeric_atomic_encoding bytes value /\
        exists rest, bytes = tag :: rest)).
  { intros tag Valid.
    assert (Complete : parser_complete
      (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => numeric_atomic_encoding bytes value /\
        exists rest, bytes = tag :: rest)).
    { eapply parser_complete_weaken; [apply parse_numeric_instruction_complete |].
      intros bytes value [E _]; exact E. }
    assert (Head : forall bytes value,
      numeric_atomic_encoding bytes value /\ (exists rest, bytes = tag :: rest) ->
      exists rest, bytes = tag :: rest) by tauto.
    unfold parse_be_layer; normal_layer_dispatch tag Complete Head. }
  assert (CompleteFC : parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    numeric_fc_encoding).
  { eapply parser_complete_weaken; [apply parse_numeric_instruction_complete |].
    intros bytes value [E _]; exact E. }
  assert (HeadFC : forall bytes value, numeric_fc_encoding bytes value ->
    exists rest, bytes = xfc :: rest).
  { intros bytes value [_ [header [payload [code [Parts _]]]]].
    now exists (header ++ payload). }
  assert (FailedTableFC : forall m (bound : (m <= n)%nat) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> numeric_fc_encoding prefix be ->
    runParser (parse_table_instruction (M := option) (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Parts [E Range]]]]]].
    apply (parse_table_reject_fc n m bound input header code (payload ++ suffix)).
    - rewrite Bytes, Parts; simpl; now rewrite app_assoc.
    - exact E.
    - left; lia. }
  assert (FailedMemoryFC : forall m (bound : (m <= n)%nat) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> numeric_fc_encoding prefix be ->
    runParser (parse_memory_instruction (M := option) (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Parts [E Range]]]]]].
    apply (parse_memory_reject_fc n m bound input header code (payload ++ suffix)).
    - rewrite Bytes, Parts; simpl; now rewrite app_assoc.
    - exact E.
    - now left. }
  assert (LayerFC : parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    numeric_fc_encoding).
  { unfold parse_be_layer.
    let Other := fun _ =>
      first [reject_table_layer FailedTableFC |reject_memory_layer FailedMemoryFC] in
    extended_layer_dispatch xfc CompleteFC HeadFC Other. }
  assert (CompleteFD : parser_complete
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    numeric_fd_encoding).
  { eapply parser_complete_weaken; [apply parse_numeric_instruction_complete |].
    intros bytes value [E _]; exact E. }
  assert (HeadFD : forall bytes value, numeric_fd_encoding bytes value ->
    exists rest, bytes = xfd :: rest).
  { intros bytes value [_ [header [payload [code [Parts _]]]]].
    now exists (header ++ payload). }
  assert (FailedMemoryFD : forall m (bound : (m <= n)%nat) input prefix suffix be,
    input_bytes input = prefix ++ suffix -> numeric_fd_encoding prefix be ->
    runParser (parse_memory_instruction (M := option) (n := n)) bound input = None).
  { intros m bound input prefix suffix be Bytes
      [_ [header [payload [code [Parts [E NotMemory]]]]]].
    apply (parse_memory_reject_fd n m bound input header code (payload ++ suffix)).
    - rewrite Bytes, Parts; simpl; now rewrite app_assoc.
    - exact E.
    - exact NotMemory. }
  assert (LayerFD : parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    numeric_fd_encoding).
  { unfold parse_be_layer.
    let Other := fun _ => reject_memory_layer FailedMemoryFD in
    extended_layer_dispatch xfd CompleteFD HeadFD Other. }
  intros m bound input prefix suffix be Bytes Encoding.
  pose proof Encoding as Saved.
  destruct Encoding as
    [opcode be Lower Opcode
    |payload v E Count
    |payload v E Count
    |payload Count
    |payload Count
    |header payload E Count
    |prefix code be E Opcode
    |body be E].
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
    split; [exact Saved |]. exists header, payload, 12%N.
    split; [reflexivity |]. split; [exact E |reflexivity].
  - assert (Bound : (N.to_nat code < 8)%nat).
    { change (N.to_nat code < length saturating_instructions)%nat.
      apply nth_error_Some; rewrite Opcode; discriminate. }
    apply (LayerFC m bound input _ suffix _ Bytes).
    split; [exact Saved |]. destruct E as [header [Parts E]].
    exists header, nil, code.
    rewrite app_nil_r. split; [exact Parts |]. split; [exact E |lia].
  - apply (LayerFD m bound input _ suffix _ Bytes).
    split; [exact Saved |].
    destruct (simd_encoding_has_kind _ _ E)
      as [kind [header [payload [code [Parts [Enc Kind]]]]]].
    exists header, payload, code. split; [now rewrite Parts |].
    split; [exact Enc |now apply (numeric_simd_not_vector_memory kind)].
Qed.

Definition basic_fixed_opcodes : list (byte * basic_instruction) :=
  (x00, BI_unreachable) :: (x01, BI_nop) :: (x0f, BI_return) :: nil.

Theorem parse_be_layer_fixed_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) opcode be :
  In (opcode, be) basic_fixed_opcodes ->
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    (fun bytes value => bytes = opcode :: nil /\ value = be).
Proof.
  intro Member. unfold basic_fixed_opcodes in Member; cbn [In] in Member.
  destruct Member as [E|[E|[E|E]]]; try contradiction;
    inversion E; subst opcode be.
  - pose proof (fixed_instruction_complete n x00 BI_unreachable) as Complete.
    change (parser_complete (parse_unreachable (n := n))
      (fun bytes value => bytes = x00 :: nil /\ value = BI_unreachable)) in Complete.
    unfold parse_be_layer.
    normal_layer_dispatch x00 Complete
      (binary_format_type_properties.fixed_encoding_head x00 BI_unreachable).
  - pose proof (fixed_instruction_complete n x01 BI_nop) as Complete.
    change (parser_complete (parse_nop (n := n))
      (fun bytes value => bytes = x01 :: nil /\ value = BI_nop)) in Complete.
    unfold parse_be_layer.
    normal_layer_dispatch x01 Complete
      (binary_format_type_properties.fixed_encoding_head x01 BI_nop).
  - pose proof (fixed_instruction_complete n x0f BI_return) as Complete.
    change (parser_complete (parse_return (n := n))
      (fun bytes value => bytes = x0f :: nil /\ value = BI_return)) in Complete.
    unfold parse_be_layer.
    normal_layer_dispatch x0f Complete
      (binary_format_type_properties.fixed_encoding_head x0f BI_return).
Qed.

Definition basic_indexed_opcodes : list (byte * (N -> basic_instruction)) :=
  (x0c, BI_br) :: (x0d, BI_br_if) :: (x10, BI_call) :: nil.

Theorem parse_be_layer_indexed_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) opcode make :
  In (opcode, make) basic_indexed_opcodes ->
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    (indexed_instruction_encoding opcode make).
Proof.
  intro Member. unfold basic_indexed_opcodes in Member; cbn [In] in Member.
  destruct Member as [E|[E|[E|E]]]; try contradiction;
    inversion E; subst opcode make.
  - pose proof (indexed_instruction_complete n x0c BI_br) as Complete.
    change (parser_complete (parse_br (n := n))
      (indexed_instruction_encoding x0c BI_br)) in Complete.
    unfold parse_be_layer.
    normal_layer_dispatch x0c Complete (indexed_instruction_head x0c BI_br).
  - pose proof (indexed_instruction_complete n x0d BI_br_if) as Complete.
    change (parser_complete (parse_br_if (n := n))
      (indexed_instruction_encoding x0d BI_br_if)) in Complete.
    unfold parse_be_layer.
    normal_layer_dispatch x0d Complete (indexed_instruction_head x0d BI_br_if).
  - pose proof (indexed_instruction_complete n x10 BI_call) as Complete.
    change (parser_complete (parse_call (n := n))
      (indexed_instruction_encoding x10 BI_call)) in Complete.
    unfold parse_be_layer.
    normal_layer_dispatch x10 Complete (indexed_instruction_head x10 BI_call).
Qed.

Theorem parse_be_layer_br_table_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    br_table_instruction_encoding.
Proof.
  pose proof (parse_br_table_complete n) as Complete.
  assert (Head : forall bytes be, br_table_instruction_encoding bytes be ->
    exists rest, bytes = x0e :: rest).
  { intros bytes be [targets [fallback [labels [label [Bytes _]]]]].
    now exists (targets ++ fallback). }
  unfold parse_be_layer; normal_layer_dispatch x0e Complete Head.
Qed.

Theorem parse_be_layer_call_indirect_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    (indirect_instruction_encoding x11
      (fun typ tab => BI_call_indirect tab typ)).
Proof.
  pose proof (indirect_instruction_complete n x11
    (fun typ tab => BI_call_indirect tab typ)) as Complete.
  change (parser_complete (parse_call_indirect (n := n))
    (indirect_instruction_encoding x11
      (fun typ tab => BI_call_indirect tab typ))) in Complete.
  assert (Head : forall bytes be,
    indirect_instruction_encoding x11
      (fun typ tab => BI_call_indirect tab typ) bytes be ->
    exists rest, bytes = x11 :: rest).
  { intros bytes be [first [second [x [y [Bytes _]]]]].
    now exists (first ++ second). }
  unfold parse_be_layer; normal_layer_dispatch x11 Complete Head.
Qed.

Lemma index_encoding_binary_u32 bytes index :
  index_encoding bytes index ->
  binary_format_properties.binary_u32 bytes index.
Proof.
  intro Encoding.
  destruct (leb128_properties.parse_u32_prefix_complete
    (length bytes) _ (Nat.le_refl _) (mkSizedList bytes) bytes nil index
    ltac:(unfold input_bytes; simpl; now rewrite app_nil_r) Encoding)
    as [s [Run [Value Rest]]].
  destruct (parse_u32_binary_sound
    (length bytes) _ (Nat.le_refl _) (mkSizedList bytes) s Run)
    as [prefix [Bytes E]].
  change (input_bytes (mkSizedList bytes) = prefix ++ output_bytes s) in Bytes.
  change (output_bytes s = nil) in Rest.
  rewrite Rest, app_nil_r in Bytes.
  change (bytes = prefix) in Bytes; subst prefix.
  rewrite Value in E; exact E.
Qed.

Definition gc_reference_encoding code (expected : basic_instruction) bytes be :=
  exists header, bytes = xfb :: header /\ index_encoding header code /\ be = expected.

Lemma gc_reference_head code expected bytes be :
  gc_reference_encoding code expected bytes be ->
  exists tail, bytes = xfb :: tail.
Proof. intros [header [Bytes _]]. now exists header. Qed.

Lemma parse_ref_i31_complete n :
  parser_complete (parse_ref_i31 (Toks := SizedList byte) (M := option) (n := n))
    (gc_reference_encoding 28%N BI_ref_i31).
Proof.
  unfold parse_ref_i31, Combinators.cmap.
  eapply parser_complete_map with
    (P := fun bs value => exists header,
      bs = xfb :: header /\ index_encoding header 28%N /\ value = 28%N).
  - apply parser_complete_prefix_byte with
      (Q := fun bs value => index_encoding bs 28%N /\ value = 28%N).
    + intros k lt; simpl. apply parser_complete_le_lower. apply assert_u32_complete.
    + intros bytes value [header [Bytes Facts]]. exists header; auto.
  - intros bytes be [header [Bytes [Encoding Value]]].
    exists 28%N. split; [exists header; auto |exact Value].
Qed.

Lemma parse_i31_get_complete n code sign :
  (code = 29%N /\ sign = SX_S) \/ (code = 30%N /\ sign = SX_U) ->
  parser_complete (parse_i31_get (Toks := SizedList byte) (M := option) (n := n))
    (gc_reference_encoding code (BI_i31_get sign)).
Proof.
  intro Kind. unfold parse_i31_get.
  apply parser_complete_prefix_byte with
    (Q := fun bytes value => index_encoding bytes code /\ value = BI_i31_get sign).
  - intros k lt; simpl. apply parser_complete_le_lower.
    destruct Kind as [[-> ->]|[-> ->]].
    + apply parser_complete_alt_left. apply asserted_fixed_complete.
    + eapply parser_complete_alt_right with
        (P := fun bs _ => index_encoding bs 29%N).
      * eapply parser_sound_cmap; [apply assert_u32_sound |].
        intros bytes value [Encoding _]. exact Encoding.
      * apply asserted_fixed_complete.
      * intros xs ys tail1 tail2 a b E [F _] Same.
        pose proof (index_encoding_prefix_injective xs ys tail1 tail2 _ _ E F Same).
        discriminate.
  - intros bytes value [header [Bytes Facts]]. exists header; auto.
Qed.

Lemma parse_ref_i31_gc_sound n :
  parser_sound (parse_ref_i31 (Toks := SizedList byte) (M := option) (n := n))
    (gc_reference_encoding 28%N BI_ref_i31).
Proof.
  unfold parse_ref_i31.
  eapply parser_sound_cmap with
    (P := fun bs _ => exists header, bs = xfb :: header /\ index_encoding header 28%N).
  - apply parser_sound_prefix_byte with
      (Q := fun bytes _ => index_encoding bytes 28%N).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_weaken; [apply assert_u32_sound |].
      intros bytes value [Encoding _]. exact Encoding.
    + intros bytes value Encoding. exists bytes; auto.
  - intros bytes value [header [Bytes Encoding]]. exists header; auto.
Qed.

Lemma parse_reference_gc_complete n code expected :
  In (code, expected)
    ((28%N, BI_ref_i31) :: (29%N, BI_i31_get SX_S) ::
      (30%N, BI_i31_get SX_U) :: nil) ->
  parser_complete
    (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
    (gc_reference_encoding code expected).
Proof.
  intro Member. simpl in Member.
  destruct Member as [E|[E|[E|E]]]; try contradiction;
    inversion E; subst code expected.
  - unfold parse_reference_instruction.
    byte_type_dispatch xfb (parse_ref_i31_complete n)
      (gc_reference_head 28%N BI_ref_i31).
  - assert (Complete : parser_complete
      (parse_i31_get (Toks := SizedList byte) (M := option) (n := n))
      (gc_reference_encoding 29%N (BI_i31_get SX_S))).
    { apply parse_i31_get_complete; auto. }
    unfold parse_reference_instruction.
    do 4 (eapply parser_complete_alt_right_initial with (actual := xfb);
      [numeric_initial |discriminate |
       apply gc_reference_head |]).
    eapply parser_complete_alt_right with
      (P := gc_reference_encoding 28%N BI_ref_i31).
    + apply parse_ref_i31_gc_sound.
    + apply parser_complete_alt_left. exact Complete.
    + intros xs ys tail1 tail2 a b [h1 [X [E1 _]]] [h2 [Y [E2 _]]] Same.
      subst xs ys. inversion Same.
      pose proof (index_encoding_prefix_injective h1 h2 tail1 tail2 _ _ E1 E2 H0).
      discriminate.
  - assert (Complete : parser_complete
      (parse_i31_get (Toks := SizedList byte) (M := option) (n := n))
      (gc_reference_encoding 30%N (BI_i31_get SX_U))).
    { apply parse_i31_get_complete; auto. }
    unfold parse_reference_instruction.
    do 4 (eapply parser_complete_alt_right_initial with (actual := xfb);
      [numeric_initial |discriminate |
       apply gc_reference_head |]).
    eapply parser_complete_alt_right with
      (P := gc_reference_encoding 28%N BI_ref_i31).
    + apply parse_ref_i31_gc_sound.
    + apply parser_complete_alt_left. exact Complete.
    + intros xs ys tail1 tail2 a b [h1 [X [E1 _]]] [h2 [Y [E2 _]]] Same.
      subst xs ys. inversion Same.
      pose proof (index_encoding_prefix_injective h1 h2 tail1 tail2 _ _ E1 E2 H0).
      discriminate.
Qed.

Theorem parse_be_layer_control_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    control_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding.
  - { unfold fixed_control_opcodes in H; cbn [In] in H.
    destruct H as [E|[E|[E|[E|[E|[E|E]]]]]]; try contradiction;
      inversion E; subst opcode be.
    all: first
      [lazymatch type of E with (?tag, ?value) = _ =>
       eapply (parse_be_layer_fixed_complete n ends branches tag value
         ltac:(unfold basic_fixed_opcodes; simpl; tauto)
         m bound input _ suffix _ Bytes); split; reflexivity end
      |apply (parse_be_layer_parametric_complete n ends branches
         m bound input _ suffix _ Bytes);
       unfold parametric_instruction_encoding;
       intuition reflexivity
      |apply (parse_be_layer_reference_complete n ends branches
         m bound input _ suffix _ Bytes);
       unfold reference_instruction_encoding; intuition reflexivity]. }
  - { unfold single_index_opcodes in H; cbn [In] in H.
      destruct H as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]];
        try contradiction; inversion E; subst opcode make.
      all: first
        [lazymatch type of E with (?tag, ?build) = _ =>
         eapply (parse_be_layer_indexed_complete n ends branches tag build
           ltac:(unfold basic_indexed_opcodes; simpl; tauto)
           m bound input _ suffix _ Bytes);
         exists bytes, x; split; [reflexivity |]; split; [exact H0 |reflexivity] end
        |lazymatch type of E with (?tag, ?build) = _ =>
         eapply (parse_be_layer_variable_complete n ends branches tag build
           ltac:(unfold variable_opcodes; simpl; tauto)
           m bound input _ suffix _ Bytes);
         exists bytes, x; split; [reflexivity |]; split; [exact H0 |reflexivity] end
        |apply (parse_be_layer_tail_complete n ends branches
           m bound input _ suffix _ Bytes);
         left; exists bytes, x; split; [reflexivity |];
         split; [exact H0 |reflexivity]
        |apply (parse_be_layer_table_complete n ends branches
           m bound input _ suffix _ Bytes);
         eapply table_single_encoding;
         [unfold table_single_opcodes; simpl; tauto |exact H0]
        |apply (parse_be_layer_memory_complete n ends branches
           m bound input _ suffix _ Bytes);
         apply BMI_indexed with (op := IM_size);
         apply BIM_size; now apply index_encoding_binary_u32
        |apply (parse_be_layer_memory_complete n ends branches
           m bound input _ suffix _ Bytes);
         apply BMI_indexed with (op := IM_grow);
         apply BIM_grow; now apply index_encoding_binary_u32
        |apply (parse_be_layer_reference_complete n ends branches
           m bound input _ suffix _ Bytes);
         right; right; exists bytes, x; split; [reflexivity |];
         split; [exact H0 |reflexivity]]. }
  - apply (parse_be_layer_call_indirect_complete n ends branches
      m bound input _ suffix _ Bytes).
    exists types, tables, y, x.
    split; [reflexivity |]. split; [exact H |].
    split; [exact H0 |reflexivity].
  - apply (parse_be_layer_tail_complete n ends branches
      m bound input _ suffix _ Bytes).
    right; exists types, tables, y, x.
    split; [reflexivity |]. split; [exact H |].
    split; [exact H0 |reflexivity].
  - apply (parse_be_layer_br_table_complete n ends branches
      m bound input _ suffix _ Bytes).
    exists targets, fallback, xs, x.
    split; [reflexivity |]. split; [exact H |].
    split; [exact H0 |reflexivity].
  - apply (parse_be_layer_reference_complete n ends branches
       m bound input _ suffix _ Bytes).
    left; exists bytes, t; auto.
  - apply (parse_be_layer_parametric_complete n ends branches
      m bound input _ suffix _ Bytes).
    right; right; exists bytes, ts.
    split; [reflexivity |]. split; [exact H |reflexivity].
  - destruct H.
    + assert (Complete : parser_complete
        (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
        (fun bytes be => bytes = xd4 :: nil /\ be = BI_ref_as_non_null)).
      { unfold parse_reference_instruction.
        byte_type_dispatch xd4 (fixed_instruction_complete n xd4 BI_ref_as_non_null)
          (fixed_encoding_head xd4 BI_ref_as_non_null). }
      assert (Layer : parser_complete
        (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
        (fun bytes be => bytes = xd4 :: nil /\ be = BI_ref_as_non_null)).
      { unfold parse_be_layer.
        normal_layer_dispatch xd4 Complete (fixed_encoding_head xd4 BI_ref_as_non_null). }
      apply (Layer m bound input _ suffix _ Bytes). auto.
    + simpl in H. destruct H as [E|[E|[E|[E|E]]]]; try contradiction;
        inversion E; subst opcode make.
      * assert (Complete : parser_complete
          (parse_call_ref (Toks := SizedList byte) (M := option) (n := n))
          (indexed_instruction_encoding x14 BI_call_ref))
          by apply indexed_instruction_complete.
        assert (Layer : parser_complete
          (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
          (indexed_instruction_encoding x14 BI_call_ref)).
        { unfold parse_be_layer.
          normal_layer_dispatch x14 Complete (indexed_instruction_head x14 BI_call_ref). }
        apply (Layer m bound input _ suffix _ Bytes). exists bytes, x; auto.
      * assert (Complete : parser_complete
          (parse_return_call_ref (Toks := SizedList byte) (M := option) (n := n))
          (indexed_instruction_encoding x15 BI_return_call_ref))
          by apply indexed_instruction_complete.
        assert (Layer : parser_complete
          (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
          (indexed_instruction_encoding x15 BI_return_call_ref)).
        { unfold parse_be_layer.
          normal_layer_dispatch x15 Complete (indexed_instruction_head x15 BI_return_call_ref). }
        apply (Layer m bound input _ suffix _ Bytes). exists bytes, x; auto.
      * assert (Complete : parser_complete
          (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
          (indexed_instruction_encoding xd5 BI_br_on_null)).
        { unfold parse_reference_instruction.
          byte_type_dispatch xd5 (indexed_instruction_complete n xd5 BI_br_on_null)
            (indexed_instruction_head xd5 BI_br_on_null). }
        assert (Layer : parser_complete
          (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
          (indexed_instruction_encoding xd5 BI_br_on_null)).
        { unfold parse_be_layer.
          normal_layer_dispatch xd5 Complete (indexed_instruction_head xd5 BI_br_on_null). }
        apply (Layer m bound input _ suffix _ Bytes). exists bytes, x; auto.
      * assert (Complete : parser_complete
          (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
          (indexed_instruction_encoding xd6 BI_br_on_non_null)).
        { unfold parse_reference_instruction.
          byte_type_dispatch xd6 (indexed_instruction_complete n xd6 BI_br_on_non_null)
            (indexed_instruction_head xd6 BI_br_on_non_null). }
        assert (Layer : parser_complete
          (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
          (indexed_instruction_encoding xd6 BI_br_on_non_null)).
        { unfold parse_be_layer.
          normal_layer_dispatch xd6 Complete (indexed_instruction_head xd6 BI_br_on_non_null). }
        apply (Layer m bound input _ suffix _ Bytes). exists bytes, x; auto.
    + pose proof (parse_reference_gc_complete n code be H) as Complete.
      assert (Layer : parser_complete
        (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
        (gc_reference_encoding code be)).
      { unfold parse_be_layer.
        normal_layer_dispatch xfb Complete (gc_reference_head code be). }
      apply (Layer m bound input _ suffix _ Bytes). exists bytes; auto.
Qed.

Theorem parse_be_layer_bulk_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    bulk_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding.
  - { destruct H0 as [header [Parts Header]]; subst prefix.
      unfold bulk_single_index_opcodes in H; cbn [In] in H.
      destruct H as [E|[E|[E|[E|[E|[E|E]]]]]]; try contradiction;
        inversion E; subst code make.
      all: first
        [apply (parse_be_layer_table_complete n ends branches
           m bound input _ suffix _ Bytes);
         eapply table_bulk_single_encoding;
         [unfold table_bulk_single_opcodes; simpl; tauto |exact Header |exact H1]
        |apply (parse_be_layer_memory_complete n ends branches
           m bound input _ suffix _ Bytes);
         apply BMI_indexed with (op := IM_drop); apply BIM_drop;
         now apply index_encoding_binary_u32
        |apply (parse_be_layer_memory_complete n ends branches
           m bound input _ suffix _ Bytes);
         apply BMI_indexed with (op := IM_fill); apply BIM_fill;
         now apply index_encoding_binary_u32]. }
  - { destruct H0 as [header [Parts Header]]; subst prefix.
      unfold bulk_two_index_opcodes in H; cbn [In] in H.
      destruct H as [E|[E|[E|[E|E]]]]; try contradiction;
        inversion E; subst code make.
      - apply (parse_be_layer_memory_complete n ends branches
          m bound input _ suffix _ Bytes).
        apply BMI_indexed with (op := IM_init).
        apply (BIM_init header first second y x);
          now apply index_encoding_binary_u32.
      - apply (parse_be_layer_memory_complete n ends branches
          m bound input _ suffix _ Bytes).
        apply BMI_indexed with (op := IM_copy).
        apply (BIM_copy header first second x y);
          now apply index_encoding_binary_u32.
      - apply (parse_be_layer_table_complete n ends branches
          m bound input _ suffix _ Bytes).
        apply (table_bulk_two_encoding 12%N
          (fun elem table => BI_table_init table elem) header first second x y).
        + unfold table_bulk_two_opcodes; simpl; tauto.
        + exact Header.
        + exact H1.
        + exact H2.
      - apply (parse_be_layer_table_complete n ends branches
          m bound input _ suffix _ Bytes).
        apply (table_bulk_two_encoding 14%N BI_table_copy header first second x y).
        + unfold table_bulk_two_opcodes; simpl; tauto.
        + exact Header.
        + exact H1.
        + exact H2. }
Qed.

Theorem wasm_parse_be_layer_atomic_complete n
    (ends : Box (Parser (SizedList byte) byte option (list basic_instruction)) n)
    (branches : Box (Parser (SizedList byte) byte option
      (list basic_instruction * list basic_instruction)) n) :
  parser_complete
    (parse_be_layer (Toks := SizedList byte) (M := option) ends branches)
    wasm_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Encoding.
  destruct Encoding as [Control|[Bulk|[Numeric|Memory]]].
  - now apply (parse_be_layer_control_complete n ends branches
      m bound input prefix suffix be Bytes).
  - now apply (parse_be_layer_bulk_complete n ends branches
      m bound input prefix suffix be Bytes).
  - now apply (parse_be_layer_numeric_complete n ends branches
      m bound input prefix suffix be Bytes).
  - now apply (parse_be_layer_memory_complete n ends branches
      m bound input prefix suffix be Bytes).
Qed.
