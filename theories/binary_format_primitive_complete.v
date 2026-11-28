(** First-byte and extended-opcode disjointness for production atomic
    alternatives in [parse_be_layer]. *)
From Stdlib Require Import List Strings.Byte Arith NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_control_complete
  binary_memory_grammar_properties binary_memory_properties
  binary_parser_combinators binary_codec binary_format_simd_complete.
Local Notation byte := Byte.byte.

Definition tail_initial b := b = x12 \/ b = x13.
Definition reference_initial b := b = xd0 \/ b = xd1 \/ b = xd2.
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
  do 2 (apply parser_initial_set_alt; [shelve |]). Unshelve.
  all: eapply parser_initial_set_single; [numeric_initial |].
  all: unfold reference_initial; auto.
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
      |apply parser_initial_exact_set; numeric_initial]
  end.

Ltac reject_layer_initial :=
  unfold tail_initial, reference_initial, parametric_initial, variable_initial,
    table_initial, memory_initial in *;
  intuition (try congruence; try lia).

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
    { intros bs value [t [Parts _]]; now exists (binary_format_printer.binary_of_reference_type t :: nil). }
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
