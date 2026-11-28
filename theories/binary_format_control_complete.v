(** Actual source-aware control and EH atomic completeness. *)
From Stdlib Require Import List Strings.Byte Arith NArith.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_atomic_properties binary_format_numeric_complete
  binary_format_index_lookahead_properties binary_format_memory_complete
  binary_format_reference_properties binary_format_vector_properties
  binary_format_global_properties binary_format_simd_complete leb128_properties.
Local Notation byte := Byte.byte.

Definition indexed_instruction_encoding opcode
    (make : N -> basic_instruction) bytes be :=
  exists body x, bytes = opcode :: body /\ index_encoding body x /\ be = make x.

Lemma indexed_instruction_complete n opcode make :
  parser_complete
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.map make parse_u32_as_N)))
    (indexed_instruction_encoding opcode make).
Proof.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists x, index_encoding bytes x /\ be = make x).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_u32_prefix_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be [body [x [Bytes Facts]]]; exists body; split; [exact Bytes |].
    exists x; exact Facts.
Qed.

Definition indirect_instruction_encoding opcode
    (make : N -> N -> basic_instruction) bytes be :=
  exists first second x y, bytes = opcode :: first ++ second /\
    index_encoding first x /\ index_encoding second y /\ be = make x y.

Lemma indirect_instruction_complete n opcode make :
  parser_complete
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.app (Combinators.map make parse_u32_as_N)
        (box parse_u32_as_N))))
    (indirect_instruction_encoding opcode make).
Proof.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists first second x y, bytes = first ++ second /\
      index_encoding first x /\ index_encoding second y /\ be = make x y).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_app with
      (P := fun bytes f => exists x, index_encoding bytes x /\ f = make x)
      (Q := index_encoding).
    + eapply parser_complete_map; [apply parse_u32_prefix_complete |].
      intros bytes f Enc; exact Enc.
    + intros j lower; simpl; apply parser_complete_le_lower; apply parse_u32_prefix_complete.
    + intros bytes be [first [second [x [y [Bytes [First [Second Value]]]]]]].
      exists first, second, (make x), y.
      split; [exact Bytes |]. split; [exists x; auto |auto].
  - intros bytes be [first [second [x [y [Bytes Facts]]]]].
    exists (first ++ second); split; [exact Bytes |exists first, second, x, y; auto].
Qed.

Definition source_null_instruction_encoding bytes be :=
  exists body h, bytes = xd0 :: body /\ source_heap_encoding body h /\ be = BI_ref_null h.

Lemma source_null_instruction_complete n :
  parser_complete
    (parse_ref_null (Toks := SizedList byte) (M := option) (n := n))
    source_null_instruction_encoding.
Proof.
  unfold parse_ref_null.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists h, source_heap_encoding bytes h /\ be = BI_ref_null h).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_declaration_heap_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be [body [h [Bytes Facts]]]; exists body; split; [exact Bytes |].
    exists h; exact Facts.
Qed.

Definition source_select_instruction_encoding bytes be :=
  exists body ts, bytes = x1c :: body /\
    vector_encoding source_value_encoding body ts /\ be = BI_select (Some ts).

Lemma source_select_instruction_complete n :
  parser_complete
    (parse_select_Some (Toks := SizedList byte) (M := option) (n := n))
    source_select_instruction_encoding.
Proof.
  unfold parse_select_Some.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists ts,
      vector_encoding source_value_encoding bytes ts /\ be = BI_select (Some ts)).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map.
    + apply parse_vec_complete; apply parse_declaration_value_complete.
    + intros bytes be Enc; exact Enc.
  - intros bytes be [body [ts [Bytes Facts]]]; exists body; split; [exact Bytes |].
    exists ts; exact Facts.
Qed.

Ltac control_initial :=
  first [apply exact_byte_initial
    |apply parser_initial_cmap; control_initial
    |apply parser_initial_rand; control_initial
    |apply parser_initial_map; control_initial
    |apply parser_initial_app; control_initial].

Ltac control_initial_set :=
  lazymatch goal with
  | |- parser_initial_set (Combinators.alt _ _) _ =>
      eapply parser_initial_set_union; [control_initial_set |control_initial_set]
  | |- parser_initial_set ?p _ =>
      eapply parser_initial_exact_set; control_initial
  end.

Ltac control_byte_dispatch tag Complete Head :=
  lazymatch goal with
     | |- parser_complete (Combinators.alt ?p _) _ =>
       let AllowedSet := open_constr:(_ : byte -> Prop) in
       let Initial := fresh "Initial" in
       assert (Initial : parser_initial_set p AllowedSet) by control_initial_set;
       let Rejected := fresh "Rejected" in
       tryif (assert (Rejected : ~ AllowedSet tag) by (cbn; intuition congruence))
       then
         (eapply parser_complete_alt_right_initial_set with
            (Allowed := AllowedSet) (opcode := tag);
           [exact Initial |exact Rejected |exact Head
           |control_byte_dispatch tag Complete Head])
       else
         (apply parser_complete_alt_left; control_byte_dispatch tag Complete Head)
     | _ => exact Complete
  end.

Ltac unfold_control_layer :=
  unfold parse_be_layer, parse_reference_instruction, parse_parametric_instruction,
    parse_variable_instruction, parse_table_instruction; cbv zeta.

Theorem control_indexed_layer_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n)
    opcode make :
  In (opcode, make) single_index_opcodes ->
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    (indexed_instruction_encoding opcode make).
Proof.
  intro Member.
  assert (Head : forall bytes be, indexed_instruction_encoding opcode make bytes be ->
    exists rest, bytes = opcode :: rest).
  { intros bytes be [rest [x [Bytes _]]]; exists rest; auto. }
  unfold single_index_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst opcode make; unfold_control_layer;
    lazymatch goal with
    | |- parser_complete _ (indexed_instruction_encoding ?opcode ?make) =>
        control_byte_dispatch opcode (indexed_instruction_complete n opcode make) Head
    end.
Qed.

Definition br_table_instruction_encoding bytes be :=
  exists targets fallback labels label,
    bytes = x0e :: targets ++ fallback /\
    vector_encoding index_encoding targets labels /\
    index_encoding fallback label /\ be = BI_br_table labels label.

Lemma parse_br_table_complete n :
  parser_complete
    (parse_br_table (Toks := SizedList byte) (M := option) (n := n))
    br_table_instruction_encoding.
Proof.
  unfold parse_br_table.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists targets fallback labels label,
      bytes = targets ++ fallback /\ vector_encoding index_encoding targets labels /\
      index_encoding fallback label /\ be = BI_br_table labels label).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_app with
      (P := fun bytes f => exists labels, vector_encoding index_encoding bytes labels /\
        f = (fun label => BI_br_table labels label))
      (Q := index_encoding).
    + eapply parser_complete_map.
      * apply parse_vec_complete; apply parse_u32_prefix_complete.
      * intros bytes f [labels [Enc Value]]; exists labels; split; [exact Enc |].
        unfold parse_br_table_aux, extract_labelidx; now rewrite List.map_id.
    + intros j lower; simpl; apply parser_complete_le_lower; apply parse_u32_prefix_complete.
    + intros bytes be [targets [fallback [labels [label [Bytes [Targets [Fallback Value]]]]]]].
      exists targets, fallback, (fun label => BI_br_table labels label), label.
      split; [exact Bytes |]. split; [exists labels; auto |auto].
  - intros bytes be [targets [fallback [labels [label [Bytes Facts]]]]].
    exists (targets ++ fallback); split; [exact Bytes |exists targets, fallback, labels, label; auto].
Qed.

Definition i31_instruction_encoding code (be : basic_instruction) bytes value :=
  exists header, bytes = xfb :: header /\ index_encoding header code /\ value = be.

Lemma i31_reference_complete n code be :
  In (code, be) ((28%N, BI_ref_i31) ::
    (29%N, BI_i31_get SX_S) :: (30%N, BI_i31_get SX_U) :: nil) ->
  parser_complete
    (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
    (i31_instruction_encoding code be).
Proof.
  intro Member.
  assert (Head : forall bytes value, i31_instruction_encoding code be bytes value ->
    exists rest, bytes = xfb :: rest).
  { intros bytes value [header [Bytes _]]; exists header; auto. }
  assert (ExtendedHead : forall bytes value, i31_instruction_encoding code be bytes value ->
    exists header rest, bytes = xfb :: header ++ rest /\ index_encoding header code).
  { intros bytes value [header [Bytes [Header _]]].
    exists header, nil; rewrite app_nil_r; auto. }
  cbn [In] in Member.
  destruct Member as [Equal|[Equal|[Equal|Equal]]]; try contradiction;
    inversion Equal; subst code be.
  - assert (Complete : parser_complete (parse_ref_i31 (n := n))
      (i31_instruction_encoding 28%N BI_ref_i31)).
    { unfold parse_ref_i31.
      eapply parser_complete_map with
        (P := fun bytes x => exists header,
          bytes = xfb :: header /\ index_encoding header 28%N /\ x = 28%N).
      - apply parser_complete_prefix_byte with
          (Q := fun bytes x => index_encoding bytes 28%N /\ x = 28%N).
        + intros k lt; simpl; apply parser_complete_le_lower; apply assert_u32_complete.
        + intros bytes x [header [Bytes Facts]]; exists header; auto.
      - intros bytes value [header [Bytes [Header ->]]].
        exists 28%N; split; [exists header; auto |reflexivity]. }
    unfold parse_reference_instruction.
    do 4 (eapply parser_complete_alt_right_initial with (actual := xfb);
      [control_initial |discriminate |exact Head |]).
    apply parser_complete_alt_left; exact Complete.
  - assert (Complete : parser_complete (parse_i31_get (n := n))
      (i31_instruction_encoding 29%N (BI_i31_get SX_S))).
    { unfold parse_i31_get.
      apply parser_complete_prefix_byte with
        (Q := fun bytes value => index_encoding bytes 29%N /\ value = BI_i31_get SX_S).
      - intros k lt; simpl; apply parser_complete_le_lower.
        apply parser_complete_alt_left; apply asserted_fixed_complete.
      - intros bytes value [header [Bytes Facts]]; exists header; auto. }
    unfold parse_reference_instruction.
    do 4 (eapply parser_complete_alt_right_initial with (actual := xfb);
      [control_initial |discriminate |exact Head |]).
    eapply parser_complete_alt_right_extended with (tag := xfb) (actual := 29%N).
    + unfold parse_ref_i31; apply parser_initial_extended_cmap; apply extended_assert_initial.
    + discriminate.
    + exact ExtendedHead.
    + apply parser_complete_alt_left; exact Complete.
  - assert (Complete : parser_complete (parse_i31_get (n := n))
      (i31_instruction_encoding 30%N (BI_i31_get SX_U))).
    { unfold parse_i31_get.
      apply parser_complete_prefix_byte with
        (Q := fun bytes value => index_encoding bytes 30%N /\ value = BI_i31_get SX_U).
      - intros k lt; simpl; apply parser_complete_le_lower.
        eapply parser_complete_alt_right_index with (actual := 30%N).
        + apply parser_initial_index_cmap; apply assert_u32_initial_index.
        + discriminate.
        + intros bytes value [Enc _]; exists bytes, nil; rewrite app_nil_r; auto.
        + apply asserted_fixed_complete.
      - intros bytes value [header [Bytes Facts]]; exists header; auto. }
    unfold parse_reference_instruction.
    do 4 (eapply parser_complete_alt_right_initial with (actual := xfb);
      [control_initial |discriminate |exact Head |]).
    eapply parser_complete_alt_right_extended with (tag := xfb) (actual := 30%N).
    + unfold parse_ref_i31; apply parser_initial_extended_cmap; apply extended_assert_initial.
    + discriminate.
    + exact ExtendedHead.
    + apply parser_complete_alt_left; exact Complete.
Qed.

Theorem control_fixed_layer_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n)
    opcode be :
  In (opcode, be) fixed_control_opcodes ->
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    (fun bytes value => bytes = opcode :: nil /\ value = be).
Proof.
  intro Member.
  assert (Head : forall bytes value, bytes = opcode :: nil /\ value = be ->
    exists rest, bytes = opcode :: rest).
  { intros bytes value [Bytes _]; exists nil; auto. }
  unfold fixed_control_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst opcode be; unfold_control_layer;
    lazymatch goal with
    | |- parser_complete _ (fun bytes value => bytes = ?opcode :: nil /\ value = ?be) =>
        control_byte_dispatch opcode (fixed_instruction_complete n opcode be) Head
    end.
Qed.

Theorem parse_be_layer_control_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n) :
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    control_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Enc.
  destruct Enc as
    [opcode be Member
    |opcode make payload x Member Payload
    |types tables x y Types Tables
    |types tables x y Types Tables
    |targets fallback labels label Targets Fallback
    |payload h Heap
    |payload ts Types
    |payload code be Index Member].
  - eapply control_fixed_layer_complete; [exact Member |exact Bytes |auto].
  - eapply control_indexed_layer_complete; [exact Member |exact Bytes |].
    exists payload, x; auto.
  - assert (Complete : parser_complete (parse_be_layer (k := n) body branches)
      (indirect_instruction_encoding x11 (fun typ tab => BI_call_indirect tab typ))).
    { assert (Head : forall bytes value,
        indirect_instruction_encoding x11 (fun typ tab => BI_call_indirect tab typ) bytes value ->
        exists rest, bytes = x11 :: rest).
      { intros bytes value [first [second [a [b [E _]]]]]; exists (first ++ second); auto. }
      unfold_control_layer.
      control_byte_dispatch x11
        (indirect_instruction_complete n x11 (fun typ tab => BI_call_indirect tab typ)) Head. }
    eapply Complete; [exact Bytes |exists types, tables, y, x; auto].
  - assert (Complete : parser_complete (parse_be_layer (k := n) body branches)
      (indirect_instruction_encoding x13 (fun typ tab => BI_return_call_indirect tab typ))).
    { assert (Head : forall bytes value,
        indirect_instruction_encoding x13 (fun typ tab => BI_return_call_indirect tab typ) bytes value ->
        exists rest, bytes = x13 :: rest).
      { intros bytes value [first [second [a [b [E _]]]]]; exists (first ++ second); auto. }
      unfold_control_layer.
      control_byte_dispatch x13
        (indirect_instruction_complete n x13 (fun typ tab => BI_return_call_indirect tab typ)) Head. }
    eapply Complete; [exact Bytes |exists types, tables, y, x; auto].
  - assert (Complete : parser_complete (parse_be_layer (k := n) body branches)
      br_table_instruction_encoding).
    { assert (Head : forall bytes value, br_table_instruction_encoding bytes value ->
        exists rest, bytes = x0e :: rest).
      { intros bytes value [a [b [xs [x [E _]]]]]; exists (a ++ b); auto. }
      unfold_control_layer; control_byte_dispatch x0e (parse_br_table_complete n) Head. }
    eapply Complete; [exact Bytes |exists targets, fallback, labels, label; auto].
  - assert (Complete : parser_complete (parse_be_layer (k := n) body branches)
      source_null_instruction_encoding).
    { assert (Head : forall bytes value, source_null_instruction_encoding bytes value ->
        exists rest, bytes = xd0 :: rest).
      { intros bytes value [rest [a [E _]]]; exists rest; auto. }
      unfold_control_layer; control_byte_dispatch xd0 (source_null_instruction_complete n) Head. }
    eapply Complete; [exact Bytes |exists payload, h; auto].
  - assert (Complete : parser_complete (parse_be_layer (k := n) body branches)
      source_select_instruction_encoding).
    { assert (Head : forall bytes value, source_select_instruction_encoding bytes value ->
        exists rest, bytes = x1c :: rest).
      { intros bytes value [rest [a [E _]]]; exists rest; auto. }
      unfold_control_layer; control_byte_dispatch x1c (source_select_instruction_complete n) Head. }
    eapply Complete; [exact Bytes |exists payload, ts; auto].
  - assert (Complete : parser_complete (parse_be_layer (k := n) body branches)
      (i31_instruction_encoding code be)).
    { assert (Head : forall bytes value, i31_instruction_encoding code be bytes value ->
        exists rest, bytes = xfb :: rest).
      { intros bytes value [rest [E _]]; exists rest; auto. }
      unfold parse_be_layer; cbv zeta.
      do 18 (eapply parser_complete_alt_right_initial with (actual := xfb);
        [control_initial |discriminate |exact Head |]).
      apply parser_complete_alt_left; now apply i31_reference_complete. }
    eapply Complete; [exact Bytes |exists payload; auto].
Qed.

Definition two_index_payload (make : N -> N -> basic_instruction) bytes be :=
  exists first second x y, bytes = first ++ second /\
    index_encoding first x /\ index_encoding second y /\ be = make x y.

Lemma two_index_payload_complete n make :
  parser_complete
    (Combinators.app
      (Combinators.map make (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)))
      (box parse_u32_as_N))
    (two_index_payload make).
Proof.
  eapply parser_complete_app with
    (P := fun bytes f => exists x, index_encoding bytes x /\ f = make x)
    (Q := index_encoding).
  - eapply parser_complete_map; [apply parse_u32_prefix_complete |].
    intros bytes f Enc; exact Enc.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_u32_prefix_complete.
  - intros bytes be [first [second [x [y [Bytes [First [Second Value]]]]]]].
    exists first, second, (make x), y.
    split; [exact Bytes |]. split; [exists x; auto |auto].
Qed.

Lemma bulk_index_leaf_complete n code make :
  parser_complete
    (Combinators.rand
      (Combinators.rand (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code)))
      (box (Combinators.map make parse_u32_as_N)))
    (memory_bulk_payload code
      (fun bytes be => exists x, index_encoding bytes x /\ be = make x)).
Proof.
  eapply memory_extended_complete.
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_u32_prefix_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be Enc; exact Enc.
Qed.

Lemma bulk_two_leaf_complete n code make :
  parser_complete
    (Combinators.rand
      (Combinators.rand (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code)))
      (box (Combinators.app (Combinators.map make parse_u32_as_N) (box parse_u32_as_N))))
    (memory_bulk_payload code (two_index_payload make)).
Proof.
  eapply memory_extended_complete.
  - intros k lt; simpl; apply parser_complete_le_lower; apply two_index_payload_complete.
  - intros bytes be Enc; exact Enc.
Qed.

Ltac control_bulk_dispatch code Complete Head ExtendedHead :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt (Combinators.alt _ _) _) _ =>
      apply parser_complete_alt_associate;
      control_bulk_dispatch code Complete Head ExtendedHead
  | |- parser_complete (Combinators.alt ?p _) _ =>
      first
        [eapply parser_complete_alt_right_initial with (actual := xfc);
         [control_initial |discriminate |exact Head
         |control_bulk_dispatch code Complete Head ExtendedHead]
        |let previous := open_constr:(_ : N) in
         let Initial := fresh "Initial" in
         assert (Initial : parser_initial_extended p xfc previous) by
           (apply parser_initial_extended_rand; apply extended_assert_initial);
         tryif constr_eq previous code then
           (apply parser_complete_alt_left; exact Complete)
         else
           (eapply parser_complete_alt_right_extended with (tag := xfc) (actual := code);
            [exact Initial |discriminate |exact ExtendedHead
            |control_bulk_dispatch code Complete Head ExtendedHead])]
  | _ => exact Complete
  end.

Ltac unfold_control_bulk :=
  unfold_control_layer;
  unfold parse_table_init, parse_elem_drop, parse_table_copy, parse_table_grow,
    parse_table_size, parse_table_fill.

Theorem control_bulk_single_layer_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n)
    code make :
  In (code, make) bulk_single_index_opcodes ->
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    (memory_bulk_payload code
      (fun bytes be => exists x, index_encoding bytes x /\ be = make x)).
Proof.
  intro Member.
  assert (Head : forall bytes be, memory_bulk_payload code
    (fun bytes be => exists x, index_encoding bytes x /\ be = make x) bytes be ->
    exists rest, bytes = xfc :: rest).
  { intros bytes be [header [payload [Bytes _]]]; exists (header ++ payload); auto. }
  assert (ExtendedHead : forall bytes be, memory_bulk_payload code
    (fun bytes be => exists x, index_encoding bytes x /\ be = make x) bytes be ->
    exists header payload, bytes = xfc :: header ++ payload /\ index_encoding header code).
  { intros bytes be [header [payload [Bytes [Header _]]]]; exists header, payload; auto. }
  unfold bulk_single_index_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst code make; unfold_control_bulk.
  - unfold parse_memory_instruction, parse_data_drop.
    control_bulk_dispatch 9%N (bulk_index_leaf_complete n 9%N BI_data_drop) Head ExtendedHead.
  - control_bulk_dispatch 13%N (bulk_index_leaf_complete n 13%N BI_elem_drop) Head ExtendedHead.
  - control_bulk_dispatch 15%N (bulk_index_leaf_complete n 15%N BI_table_grow) Head ExtendedHead.
  - control_bulk_dispatch 16%N (bulk_index_leaf_complete n 16%N BI_table_size) Head ExtendedHead.
  - control_bulk_dispatch 17%N (bulk_index_leaf_complete n 17%N BI_table_fill) Head ExtendedHead.
Qed.

Theorem control_bulk_two_layer_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n)
    code make :
  In (code, make) bulk_two_index_opcodes ->
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    (memory_bulk_payload code (two_index_payload make)).
Proof.
  intro Member.
  assert (Head : forall bytes be, memory_bulk_payload code (two_index_payload make) bytes be ->
    exists rest, bytes = xfc :: rest).
  { intros bytes be [header [payload [Bytes _]]]; exists (header ++ payload); auto. }
  assert (ExtendedHead : forall bytes be, memory_bulk_payload code (two_index_payload make) bytes be ->
    exists header payload, bytes = xfc :: header ++ payload /\ index_encoding header code).
  { intros bytes be [header [payload [Bytes [Header _]]]]; exists header, payload; auto. }
  unfold bulk_two_index_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst code make; unfold_control_bulk.
  - control_bulk_dispatch 12%N
      (bulk_two_leaf_complete n 12%N (fun elem table => BI_table_init table elem)) Head ExtendedHead.
  - control_bulk_dispatch 14%N
      (bulk_two_leaf_complete n 14%N BI_table_copy) Head ExtendedHead.
Qed.

Theorem parse_be_layer_bulk_complete n
    (body : Box (byte_parser (list basic_instruction)) n)
    (branches : Box (byte_parser (list basic_instruction * list basic_instruction)) n) :
  parser_complete (parse_be_layer (Toks := SizedList byte) (M := option) body branches)
    bulk_atomic_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Enc.
  destruct Enc as [prefix code make payload x Member Prefix Payload
    |prefix code make first second x y Member Prefix First Second];
    destruct Prefix as [header [-> Header]].
  - eapply control_bulk_single_layer_complete; [exact Member |exact Bytes |].
    exists header, payload; split; [reflexivity |].
    split; [exact Header |exists x; auto].
  - eapply control_bulk_two_layer_complete; [exact Member |exact Bytes |].
    exists header, (first ++ second); split; [reflexivity |].
    split; [exact Header |exists first, second, x, y; auto].
Qed.
