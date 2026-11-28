(** Concrete control/reference/parametric/indexed primitive completeness,
    retaining arbitrary suffixes and production parser bounds. *)
From Stdlib Require Import List Strings.Byte Arith NArith.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_atomic_properties binary_format_numeric_complete
  binary_format_type_properties binary_format_vector_properties
  binary_format_tail_properties leb128_properties binary_codec
  binary_format_properties binary_memory_properties binary_memory_grammar_properties.
Local Notation byte := Byte.byte.

Definition indexed_instruction_encoding (opcode : byte)
    (make : N -> basic_instruction) bytes be :=
  exists payload x, bytes = opcode :: payload /\
    index_encoding payload x /\ be = make x.

Lemma indexed_instruction_complete n opcode (make : N -> basic_instruction) :
  parser_complete
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.map make parse_u32_as_N)))
    (indexed_instruction_encoding opcode make).
Proof.
  eapply parser_complete_prefix_byte with
    (Q := fun bytes value => exists x, index_encoding bytes x /\ value = make x).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_u32_prefix_complete |].
    intros bytes be [x [E Value]]; exists x; auto.
  - intros bytes be [payload [x [Bytes Facts]]].
    exists payload; split; [exact Bytes |]. exists x; exact Facts.
Qed.

Lemma indexed_instruction_head opcode make bytes be :
  indexed_instruction_encoding opcode make bytes be ->
  exists payload, bytes = opcode :: payload.
Proof. intros [payload [x [Bytes _]]]; now exists payload. Qed.

Definition variable_opcodes : list (byte * (N -> basic_instruction)) :=
  (x20, BI_local_get) :: (x21, BI_local_set) :: (x22, BI_local_tee) ::
  (x23, BI_global_get) :: (x24, BI_global_set) :: nil.

Theorem parse_variable_instruction_complete n opcode make :
  In (opcode, make) variable_opcodes ->
  parser_complete
    (parse_variable_instruction (Toks := SizedList byte) (M := option) (n := n))
    (indexed_instruction_encoding opcode make).
Proof.
  intro Member. unfold variable_opcodes in Member; cbn [In] in Member.
  destruct Member as [E|[E|[E|[E|[E|E]]]]]; try contradiction;
    inversion E; subst opcode make; unfold parse_variable_instruction;
    lazymatch goal with
    | |- parser_complete _ (indexed_instruction_encoding ?op ?build) =>
      byte_type_dispatch op (indexed_instruction_complete n op build)
        (indexed_instruction_head op build)
    end.
Qed.

Definition indirect_instruction_encoding (opcode : byte)
    (make : N -> N -> basic_instruction) bytes be :=
  exists first second x y, bytes = opcode :: first ++ second /\
    index_encoding first x /\ index_encoding second y /\ be = make x y.

Lemma indirect_instruction_complete n opcode (make : N -> N -> basic_instruction) :
  parser_complete
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.app (Combinators.map make parse_u32_as_N)
        (box parse_u32_as_N))))
    (indirect_instruction_encoding opcode make).
Proof.
  eapply parser_complete_prefix_byte with
    (Q := fun bytes value => exists first second x y,
      bytes = first ++ second /\ index_encoding first x /\
      index_encoding second y /\ value = make x y).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_app with
      (P := fun bytes f => exists x, index_encoding bytes x /\ f = make x)
      (Q := index_encoding).
    + eapply parser_complete_map; [apply parse_u32_prefix_complete |].
      intros bytes f [x [E Value]]; exists x; auto.
    + intros j lower; simpl. apply parser_complete_le_lower.
      apply parse_u32_prefix_complete.
    + intros bytes be [first [second [x [y [Bytes [E [E' Value]]]]]]].
      exists first, second, (make x), y. split; [exact Bytes |].
      split; [exists x; auto |]. split; assumption.
  - intros bytes be [first [second [x [y [Bytes Facts]]]]].
    exists (first ++ second); split; [exact Bytes |].
    exists first, second, x, y; auto.
Qed.

Definition ref_null_instruction_encoding bytes be :=
  exists t, bytes = xd0 :: binary_of_reference_type t :: nil /\ be = BI_ref_null t.

Lemma parse_ref_null_complete n :
  parser_complete
    (parse_ref_null (Toks := SizedList byte) (M := option) (n := n))
    ref_null_instruction_encoding.
Proof.
  unfold parse_ref_null.
  eapply parser_complete_prefix_byte with
    (Q := fun bytes be => exists t,
      bytes = binary_of_reference_type t :: nil /\ be = BI_ref_null t).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_reference_type_complete |].
    intros bytes be [t [E Value]]; exists t; auto.
  - intros bytes be [t [Bytes Value]].
    exists (binary_of_reference_type t :: nil); split; [exact Bytes |].
    exists t; auto.
Qed.

Definition typed_select_instruction_encoding bytes be :=
  exists payload types, bytes = x1c :: payload /\
    vector_encoding value_type_encoding payload types /\ be = BI_select (Some types).

Lemma parse_select_typed_complete n :
  parser_complete
    (parse_select_Some (Toks := SizedList byte) (M := option) (n := n))
    typed_select_instruction_encoding.
Proof.
  unfold parse_select_Some.
  eapply parser_complete_prefix_byte with
    (Q := fun bytes be => exists types,
      vector_encoding value_type_encoding bytes types /\
      be = BI_select (Some types)).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_map.
    + apply parse_vec_complete; apply parse_value_type_complete.
    + intros bytes be [types [E Value]]; exists types; auto.
  - intros bytes be [payload [types [Bytes Facts]]].
    exists payload; split; [exact Bytes |]. exists types; exact Facts.
Qed.

Definition reference_instruction_encoding bytes be :=
  ref_null_instruction_encoding bytes be \/
  (bytes = xd1 :: nil /\ be = BI_ref_is_null) \/
  indexed_instruction_encoding xd2 BI_ref_func bytes be.

Theorem parse_reference_instruction_complete n :
  parser_complete
    (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
    reference_instruction_encoding.
Proof.
  intros m bound input prefix suffix be Bytes E.
  destruct E as [Null|[IsNull|Func]].
  - assert (Complete : parser_complete
      (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
      ref_null_instruction_encoding).
    { unfold parse_reference_instruction.
      apply parser_complete_alt_left; apply parse_ref_null_complete. }
    now apply (Complete m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = xd1 :: nil /\ value = BI_ref_is_null)).
    { unfold parse_reference_instruction.
      byte_type_dispatch xd1 (fixed_instruction_complete n xd1 BI_ref_is_null)
        (fixed_encoding_head xd1 BI_ref_is_null). }
    now apply (Complete m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
      (indexed_instruction_encoding xd2 BI_ref_func)).
    { unfold parse_reference_instruction.
      byte_type_dispatch xd2 (indexed_instruction_complete n xd2 BI_ref_func)
        (indexed_instruction_head xd2 BI_ref_func). }
    now apply (Complete m bound input prefix suffix be Bytes).
Qed.

Definition parametric_instruction_encoding bytes be :=
  (bytes = x1a :: nil /\ be = BI_drop) \/
  (bytes = x1b :: nil /\ be = BI_select None) \/
  typed_select_instruction_encoding bytes be.

Theorem parse_parametric_instruction_complete n :
  parser_complete
    (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
    parametric_instruction_encoding.
Proof.
  intros m bound input prefix suffix be Bytes E.
  destruct E as [Drop|[Select|Typed]].
  - assert (Complete : parser_complete
      (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x1a :: nil /\ value = BI_drop)).
    { unfold parse_parametric_instruction.
      apply parser_complete_alt_left; apply fixed_instruction_complete. }
    now apply (Complete m bound input prefix suffix be Bytes).
  - assert (Complete : parser_complete
      (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => bytes = x1b :: nil /\ value = BI_select None)).
    { unfold parse_parametric_instruction.
      byte_type_dispatch x1b (fixed_instruction_complete n x1b (BI_select None))
        (fixed_encoding_head x1b (BI_select None)). }
    now apply (Complete m bound input prefix suffix be Bytes).
  - assert (Head : forall bytes value, typed_select_instruction_encoding bytes value ->
      exists payload, bytes = x1c :: payload).
    { intros bytes value [payload [types [Parts _]]]; now exists payload. }
    assert (Complete : parser_complete
      (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
      typed_select_instruction_encoding).
    { unfold parse_parametric_instruction.
      byte_type_dispatch x1c (parse_select_typed_complete n) Head. }
    now apply (Complete m bound input prefix suffix be Bytes).
Qed.

Theorem parse_tail_call_complete n :
  parser_complete
    (parse_tail_call (Toks := SizedList byte) (M := option) (n := n))
    tail_instruction_encoding.
Proof.
  intros m bound input prefix suffix be Bytes E.
  destruct E as [Direct|Indirect].
  - assert (Complete : parser_complete
      (parse_tail_call (Toks := SizedList byte) (M := option) (n := n))
      (indexed_instruction_encoding x12 BI_return_call)).
    { unfold parse_tail_call. apply parser_complete_alt_left.
      unfold parse_return_call, extract_funcidx.
      apply indexed_instruction_complete. }
    apply (Complete m bound input prefix suffix be Bytes); exact Direct.
  - assert (Head : forall bytes value,
      indirect_instruction_encoding x13
        (fun typ tab => BI_return_call_indirect tab typ) bytes value ->
      exists payload, bytes = x13 :: payload).
    { intros bytes value [types [tables [typ [tab [Parts _]]]]].
      now exists (types ++ tables). }
    assert (Complete : parser_complete
      (parse_tail_call (Toks := SizedList byte) (M := option) (n := n))
      (indirect_instruction_encoding x13
        (fun typ tab => BI_return_call_indirect tab typ))).
    { unfold parse_tail_call.
      byte_type_dispatch x13
        (indirect_instruction_complete n x13
          (fun typ tab => BI_return_call_indirect tab typ)) Head. }
    apply (Complete m bound input prefix suffix be Bytes); exact Indirect.
Qed.

Definition br_table_instruction_encoding bytes be :=
  exists targets fallback labels label,
    bytes = x0e :: targets ++ fallback /\
    vector_encoding index_encoding targets labels /\
    index_encoding fallback label /\ be = BI_br_table labels label.

Theorem parse_br_table_complete n :
  parser_complete
    (parse_br_table (Toks := SizedList byte) (M := option) (n := n))
    br_table_instruction_encoding.
Proof.
  unfold parse_br_table.
  eapply parser_complete_prefix_byte with
    (Q := fun bytes be => exists targets fallback labels label,
      bytes = targets ++ fallback /\
      vector_encoding index_encoding targets labels /\
      index_encoding fallback label /\ be = BI_br_table labels label).
  - intros k lt; simpl. apply parser_complete_le_lower.
    eapply parser_complete_app with
      (P := fun bytes f => exists labels,
        vector_encoding index_encoding bytes labels /\
        f = (fun label => BI_br_table labels label))
      (Q := index_encoding).
    + eapply parser_complete_map.
      * apply parse_vec_complete; apply leb128_properties.parse_u32_prefix_complete.
      * intros bytes f [labels [E Value]]. exists labels; split; [exact E |].
        unfold parse_br_table_aux, extract_labelidx.
        now rewrite List.map_id.
    + intros j lower; simpl. apply parser_complete_le_lower.
      apply leb128_properties.parse_u32_prefix_complete.
    + intros bytes be [targets [fallback [labels [label [Bytes [E [E' Value]]]]]]].
      exists targets, fallback, (fun label => BI_br_table labels label), label.
      split; [exact Bytes |]. split; [exists labels; auto |].
      split; assumption.
  - intros bytes be [targets [fallback [labels [label [Bytes Facts]]]]].
    exists (targets ++ fallback); split; [exact Bytes |].
    exists targets, fallback, labels, label; auto.
Qed.

Lemma index_encoding_decode_suffix bytes index :
  index_encoding bytes index ->
  forall suffix, decode_uint 32 5 (bytes ++ suffix) = Some (index, suffix).
Proof.
  intros Encoding suffix.
  destruct (leb128_properties.parse_u32_prefix_complete
    (length (bytes ++ suffix)) _ (Nat.le_refl _)
    (mkSizedList (bytes ++ suffix)) bytes suffix index eq_refl Encoding)
    as [s [Run [Value Rest]]].
  pose proof (production_u32_reference_decoder (length (bytes ++ suffix))
    (bytes ++ suffix) (Nat.le_refl _)) as H.
  unfold observe_prefix in H. rewrite Run in H; simpl in H.
  unfold output_bytes, input_bytes in Rest.
  rewrite Value, Rest in H. symmetry; exact H.
Qed.

Definition table_single_opcodes : list (byte * (N -> basic_instruction)) :=
  (x25, BI_table_get) :: (x26, BI_table_set) :: nil.
Definition table_bulk_single_opcodes : list (N * (N -> basic_instruction)) :=
  (13%N, BI_elem_drop) :: (15%N, BI_table_grow) ::
  (16%N, BI_table_size) :: (17%N, BI_table_fill) :: nil.
Definition table_bulk_two_opcodes :
    list (N * (N -> N -> basic_instruction)) :=
  (12%N, fun elem table => BI_table_init table elem) ::
  (14%N, BI_table_copy) :: nil.

Inductive table_instruction_encoding : list byte -> basic_instruction -> Prop :=
| table_single_encoding : forall opcode make payload index,
    In (opcode, make) table_single_opcodes -> index_encoding payload index ->
    table_instruction_encoding (opcode :: payload) (make index)
| table_bulk_single_encoding : forall code make header payload index,
    In (code, make) table_bulk_single_opcodes ->
    index_encoding header code -> index_encoding payload index ->
    table_instruction_encoding (xfc :: header ++ payload) (make index)
| table_bulk_two_encoding : forall code make header first second x y,
    In (code, make) table_bulk_two_opcodes ->
    index_encoding header code ->
    index_encoding first x -> index_encoding second y ->
    table_instruction_encoding (xfc :: header ++ first ++ second) (make x y).

Lemma decode_table_instruction_complete bytes be :
  table_instruction_encoding bytes be ->
  forall suffix, decode_table_instruction (bytes ++ suffix) = Some (be, suffix).
Proof.
  intros Encoding suffix. destruct Encoding.
  - unfold table_single_opcodes in H; cbn [In] in H.
    destruct H as [E|[E|E]]; try contradiction; inversion E; subst opcode make;
      unfold decode_table_instruction, decode_or, decode_sequence,
        decode_exact_byte, decode_map; cbn -[decode_uint];
      rewrite (index_encoding_decode_suffix _ _ H0 suffix); reflexivity.
  - { unfold table_bulk_single_opcodes in H; cbn [In] in H.
    destruct H as [E|[E|[E|[E|E]]]]; try contradiction; inversion E; subst code make;
      unfold decode_table_instruction, decode_or, decode_sequence,
        decode_exact_byte, decode_map, decode_fc_prefix, decode_assert_u32,
        decode_two_indices; cbn -[decode_uint].
    all: unfold decode_map.
    all: repeat rewrite <- List.app_assoc.
    all: repeat match goal with
    | E : index_encoding ?prefix ?v |- context [decode_uint 32 5 (?prefix ++ ?rest)] =>
      rewrite (index_encoding_decode_suffix prefix v E rest); cbn -[decode_uint]
    end.
    all: reflexivity. }
  - { unfold table_bulk_two_opcodes in H; cbn [In] in H.
    destruct H as [E|[E|E]]; try contradiction; inversion E; subst code make;
      unfold decode_table_instruction, decode_or, decode_sequence,
        decode_exact_byte, decode_map, decode_fc_prefix, decode_assert_u32,
        decode_two_indices; cbn -[decode_uint].
    all: unfold decode_map.
    all: repeat rewrite <- List.app_assoc.
    all: repeat match goal with
    | E : index_encoding ?prefix ?v |- context [decode_uint 32 5 (?prefix ++ ?rest)] =>
      rewrite (index_encoding_decode_suffix prefix v E rest); cbn -[decode_uint]
    end.
    all: reflexivity. }
Qed.

Theorem parse_table_instruction_complete n :
  parser_complete
    (parse_table_instruction (Toks := SizedList byte) (M := option) (n := n))
    table_instruction_encoding.
Proof.
  exact (prefix_semantics_grammar_complete basic_instruction
    (fun n => parse_table_instruction) decode_table_instruction
    table_instruction_encoding table_instruction_prefix_correct
    decode_table_instruction_complete n).
Qed.
