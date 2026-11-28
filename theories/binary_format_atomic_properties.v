(** Atomic instruction byte grammar.  The opcode tables below are encoding
    rules, not parser runs; u32 immediates admit legal padded encodings. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_block_properties binary_format_vector_properties
  leb128_properties binary_format_value_properties.
Local Notation byte := Byte.byte.

Definition index_encoding bs x :=
  unsigned_leb bs x /\ (x <= 4294967295)%N /\ length bs <= 5.

Definition single_index_opcodes : list (byte * (N -> basic_instruction)) :=
  (x0c, BI_br) :: (x0d, BI_br_if) ::
  (x10, BI_call) :: (x12, BI_return_call) ::
  (x20, BI_local_get) :: (x21, BI_local_set) ::
  (x22, BI_local_tee) :: (x23, BI_global_get) :: (x24, BI_global_set) ::
  (x25, BI_table_get) :: (x26, BI_table_set) ::
  (x3f, BI_memory_size) :: (x40, BI_memory_grow) ::
  (xd2, BI_ref_func) :: nil.

Definition fixed_control_opcodes : list (byte * basic_instruction) :=
  (x00, BI_unreachable) :: (x01, BI_nop) :: (x0f, BI_return) ::
  (x1a, BI_drop) :: (x1b, BI_select None) :: (xd1, BI_ref_is_null) :: nil.

Inductive extended_reference_encoding : list byte -> basic_instruction -> Prop :=
| extended_fixed :
    extended_reference_encoding (xd4 :: nil) BI_ref_as_non_null
| extended_index : forall opcode make bytes x,
    In (opcode, make)
      ((x14, BI_call_ref) :: (x15, BI_return_call_ref) ::
       (xd5, BI_br_on_null) :: (xd6, BI_br_on_non_null) :: nil) ->
    index_encoding bytes x ->
    extended_reference_encoding (opcode :: bytes) (make x)
| extended_gc : forall code be bytes,
    In (code, be)
      ((28%N, BI_ref_i31) :: (29%N, BI_i31_get SX_S) ::
       (30%N, BI_i31_get SX_U) :: nil) ->
    index_encoding bytes code ->
    extended_reference_encoding (xfb :: bytes) be.

Inductive control_atomic_encoding : list byte -> basic_instruction -> Prop :=
| control_fixed : forall opcode be,
    In (opcode, be) fixed_control_opcodes ->
    control_atomic_encoding (opcode :: nil) be
| control_index : forall opcode make bytes x,
    In (opcode, make) single_index_opcodes ->
    index_encoding bytes x ->
    control_atomic_encoding (opcode :: bytes) (make x)
| control_call_indirect : forall types tables x y,
    index_encoding types y -> index_encoding tables x ->
    control_atomic_encoding (x11 :: types ++ tables) (BI_call_indirect x y)
| control_return_call_indirect : forall types tables x y,
    index_encoding types y -> index_encoding tables x ->
    control_atomic_encoding (x13 :: types ++ tables) (BI_return_call_indirect x y)
| control_br_table : forall targets fallback xs x,
    vector_encoding index_encoding targets xs -> index_encoding fallback x ->
    control_atomic_encoding (x0e :: targets ++ fallback) (BI_br_table xs x)
| control_ref_null : forall bytes t,
    heap_type_encoding bytes t ->
    control_atomic_encoding
      (xd0 :: bytes)
      (BI_ref_null t)
| control_select_typed : forall bytes ts,
    vector_encoding
      value_type_encoding bytes ts ->
    control_atomic_encoding (x1c :: bytes) (BI_select (Some ts))
| control_extended : forall bytes be,
    extended_reference_encoding bytes be -> control_atomic_encoding bytes be.

Lemma parse_index_sound n :
  parser_sound
    (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))
    index_encoding.
Proof. apply parse_u32_bounded_prefix_sound. Qed.

Lemma single_index_instruction_sound n opcode make :
  In (opcode, make) single_index_opcodes ->
  parser_sound
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) opcode)
      (box (Combinators.map make (parse_u32_as_N (n := n)))))
    control_atomic_encoding.
Proof.
  intro Opcode.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => exists x, index_encoding bs x /\ be = make x).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_index_sound |].
    intros bs x E; exists x; auto.
  - intros bs be [x [Encoding Value]]; subst.
    now apply control_index.
Qed.

Lemma fixed_control_instruction_sound n opcode be :
  In (opcode, be) fixed_control_opcodes ->
  parser_sound
    (Combinators.cmap be
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode))
    control_atomic_encoding.
Proof.
  intro Opcode. eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  intros bs b [Bytes _]; subst. now apply control_fixed.
Qed.

Lemma parse_variable_instruction_sound n :
  parser_sound
    (parse_variable_instruction (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_variable_instruction.
  do 4 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: unfold parse_local_get, parse_local_set, parse_local_tee,
    parse_global_get, parse_global_set, extract_localidx, extract_globalidx,
    parse_localidx, parse_globalidx.
  all: apply single_index_instruction_sound;
    unfold single_index_opcodes; simpl; tauto.
Qed.

Lemma assert_u32_sound n k :
  parser_sound
    (assert_u32 (Toks := SizedList byte) (M := option) (n := n) k)
    (fun bs x => index_encoding bs k /\ x = k).
Proof.
  unfold assert_u32.
  eapply parser_sound_guardM; [apply parse_index_sound |].
  intros bs x y Encoding E.
  destruct (N.eqb x k) eqn:Equal; [|discriminate].
  apply N.eqb_eq in Equal; subst.
  inversion E; subst. auto.
Qed.

Lemma extended_index_instruction_sound n opcode make :
  In (opcode, make)
    ((x14, BI_call_ref) :: (x15, BI_return_call_ref) ::
     (xd5, BI_br_on_null) :: (xd6, BI_br_on_non_null) :: nil) ->
  parser_sound
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) opcode)
      (box (Combinators.map make (parse_u32_as_N (n := n)))))
    control_atomic_encoding.
Proof.
  intro Opcode.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => exists x, index_encoding bs x /\ be = make x).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_index_sound |].
    intros bs x E; exists x; auto.
  - intros bs be [x [Encoding Value]]; subst.
    apply control_extended. now apply extended_index.
Qed.

Lemma extended_gc_instruction_sound n code be :
  In (code, be)
    ((28%N, BI_ref_i31) :: (29%N, BI_i31_get SX_S) ::
     (30%N, BI_i31_get SX_U) :: nil) ->
  parser_sound
    (Combinators.cmap be
      (Combinators.rand
        (exact_byte (Toks := SizedList byte) (M := option) xfb)
        (box (assert_u32 (n := n) code))))
    control_atomic_encoding.
Proof.
  intro Opcode.
  eapply parser_sound_cmap with
    (P := fun bs _ => exists bytes, bs = xfb :: bytes /\ index_encoding bytes code).
  - apply parser_sound_prefix_byte with (Q := fun bs _ => index_encoding bs code).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_weaken; [apply assert_u32_sound |].
      intros bs x [Encoding _]. exact Encoding.
    + intros bs x Encoding. exists bs; auto.
  - intros bs x [bytes [Bytes Encoding]]; subst.
    apply control_extended. eapply extended_gc; eassumption.
Qed.

Lemma parse_reference_instruction_sound n :
  parser_sound
    (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_reference_instruction.
  repeat apply parser_sound_alt.
  - unfold parse_ref_null.
    apply parser_sound_prefix_byte with
      (Q := fun bs be => exists t,
        heap_type_encoding bs t /\
        be = BI_ref_null t).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_map; [apply parse_heap_type_sound |].
      intros bs t Bytes; exists t; auto.
    + intros bs be [t [Bytes Value]]; subst. now apply control_ref_null.
  - unfold parse_ref_is_null. apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - unfold parse_ref_func, parse_funcidx.
    apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - unfold parse_ref_as_non_null.
    eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bs b [Bytes _]; subst.
    apply control_extended. constructor.
  - unfold parse_ref_i31.
    apply extended_gc_instruction_sound. simpl; auto.
  - unfold parse_i31_get.
    apply parser_sound_prefix_byte with
      (Q := fun bs be => exists code,
        index_encoding bs code /\
        In (code, be) ((29%N, BI_i31_get SX_S) :: (30%N, BI_i31_get SX_U) :: nil)).
    + intros k lt; simpl. apply parser_sound_le_lower. apply parser_sound_alt.
      * eapply parser_sound_cmap; [apply assert_u32_sound |].
        intros bs x [Encoding _]. exists 29%N; auto.
      * eapply parser_sound_cmap; [apply assert_u32_sound |].
        intros bs x [Encoding _]. exists 30%N; simpl; auto.
    + intros bs be [code [Encoding Member]].
      apply control_extended. eapply extended_gc with (code := code);
        [simpl in Member |- *; tauto |exact Encoding].
  - unfold parse_br_on_non_null, parse_labelidx.
    apply extended_index_instruction_sound. simpl; auto.
  - unfold parse_br_on_null, parse_labelidx.
    apply extended_index_instruction_sound. simpl; auto.
Qed.

Lemma parse_parametric_instruction_sound n :
  parser_sound
    (parse_parametric_instruction (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_parametric_instruction.
  apply parser_sound_alt; [|apply parser_sound_alt].
  - unfold parse_drop. apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - unfold parse_select_None. apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - unfold parse_select_Some.
    apply parser_sound_prefix_byte with
      (Q := fun bs be => exists ts,
        vector_encoding
          value_type_encoding bs ts /\ be = BI_select (Some ts)).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_map.
      * apply parse_vec_sound; apply parse_value_type_sound.
      * intros bs ts E; exists ts; auto.
    + intros bs be [ts [Encoding Value]]; subst.
      now apply control_select_typed.
Qed.

Lemma parse_indirect_calls_sound n opcode make :
  (opcode = x11 /\ make = BI_call_indirect) \/
  (opcode = x13 /\ make = BI_return_call_indirect) ->
  parser_sound
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) opcode)
      (box
        (Combinators.app
          (Combinators.map (fun typ tab => make tab typ)
            (parse_typeidx (n := n))) (box parse_tableidx))))
    control_atomic_encoding.
Proof.
  intro Opcode.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => exists xs ys x y,
      bs = xs ++ ys /\ index_encoding xs y /\ index_encoding ys x /\
      be = make x y).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_app with
      (P := fun bs f => exists y, index_encoding bs y /\
        f = (fun x => make x y))
      (Q := index_encoding).
    + eapply parser_sound_map; [apply parse_index_sound |].
      intros bs y E; exists y; auto.
    + intros j lower; simpl. apply parser_sound_le_lower; apply parse_index_sound.
    + intros xs ys f x [y [E F]] E'; subst f.
      exists xs, ys, x, y. split; [reflexivity |].
      split; [exact E |]. split; [exact E' |reflexivity].
  - intros bs be [xs [ys [x [y [Bytes [E [E' Value]]]]]]].
    subst bs be. destruct Opcode as [[Op Make]|[Op Make]]; subst;
      constructor; assumption.
Qed.

Lemma parse_br_table_sound n :
  parser_sound
    (parse_br_table (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_br_table.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => exists xs ys targets fallback,
      bs = xs ++ ys /\ vector_encoding index_encoding xs targets /\
      index_encoding ys fallback /\ be = BI_br_table targets fallback).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_app with
      (P := fun bs f => exists targets,
        vector_encoding index_encoding bs targets /\
        f = (fun fallback => BI_br_table targets fallback))
      (Q := index_encoding).
    + eapply parser_sound_map.
      * apply parse_vec_sound; apply parse_index_sound.
      * intros bs targets E. exists targets. split; [exact E |].
        unfold parse_br_table_aux, extract_labelidx.
        now rewrite List.map_id.
    + intros j lower; simpl. apply parser_sound_le_lower; apply parse_index_sound.
    + intros xs ys f fallback [targets [E F]] E'; subst f.
      exists xs, ys, targets, fallback.
      split; [reflexivity |]. split; [exact E |].
      split; [exact E' |reflexivity].
  - intros bs be [xs [ys [targets [fallback [Bytes [E [E' Value]]]]]]].
    subst bs be. now apply control_br_table.
Qed.

Lemma parser_sound_rand_grammar {A B n}
    (p : Parser (SizedList byte) byte option A n)
    (q : Box (Parser (SizedList byte) byte option B) n) P Q R :
  parser_sound p P ->
  (forall k (lt : k < n), parser_sound (call q lt) Q) ->
  (forall xs ys a b, P xs a -> Q ys b -> R (xs ++ ys) b) ->
  parser_sound (Combinators.rand p q) R.
Proof.
  intros Hp Hq Combine. unfold Combinators.rand, Combinators.and.
  eapply parser_sound_map with (P := fun bs pair => R bs (snd pair)).
  - eapply parser_sound_andbind; [exact Hp | |].
    + intros a k lt; apply Hq.
    + intros xs ys a b E E'; now apply (Combine xs ys a b).
  - auto.
Qed.

Definition bulk_prefix bs k :=
  exists header, bs = xfc :: header /\ index_encoding header k.

Lemma bulk_prefix_sound n k :
  parser_sound
    (Combinators.rand
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
      (box (assert_u32 k)))
    (fun bs _ => bulk_prefix bs k).
Proof.
  apply parser_sound_prefix_byte with
    (Q := fun bs x => index_encoding bs k /\ x = k).
  - intros j lt; simpl. apply parser_sound_le_lower; apply assert_u32_sound.
  - intros bs x [E _]; exists bs; auto.
Qed.

Definition bulk_single_index_opcodes : list (N * (N -> basic_instruction)) :=
  (9%N, BI_data_drop) :: (11%N, BI_memory_fill) ::
  (13%N, BI_elem_drop) :: (15%N, BI_table_grow) ::
  (16%N, BI_table_size) :: (17%N, BI_table_fill) :: nil.

Definition bulk_two_index_opcodes :
    list (N * (N -> N -> basic_instruction)) :=
  (8%N, fun data memory => BI_memory_init memory data) ::
  (10%N, BI_memory_copy) ::
  (12%N, fun elem table => BI_table_init table elem) ::
  (14%N, BI_table_copy) :: nil.

Inductive bulk_atomic_encoding : list byte -> basic_instruction -> Prop :=
| bulk_single : forall prefix code make body x,
    In (code, make) bulk_single_index_opcodes ->
    bulk_prefix prefix code -> index_encoding body x ->
    bulk_atomic_encoding (prefix ++ body) (make x)
| bulk_two : forall prefix code make first second x y,
    In (code, make) bulk_two_index_opcodes ->
    bulk_prefix prefix code ->
    index_encoding first x -> index_encoding second y ->
    bulk_atomic_encoding (prefix ++ (first ++ second)) (make x y).

Lemma bulk_single_instruction_sound n code make :
  In (code, make) bulk_single_index_opcodes ->
  parser_sound
    (Combinators.rand
      (Combinators.rand
        (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code)))
      (box (Combinators.map make parse_u32_as_N)))
    bulk_atomic_encoding.
Proof.
  intro Opcode.
  eapply parser_sound_rand_grammar with
    (P := fun bs _ => bulk_prefix bs code)
    (Q := fun bs be => exists x, index_encoding bs x /\ be = make x).
  - apply bulk_prefix_sound.
  - intros j lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_index_sound |].
    intros bs x E; exists x; auto.
  - intros prefix body k be Prefix [x [E Value]]; subst be.
    eapply bulk_single; eassumption.
Qed.

Lemma bulk_two_instruction_sound n code make :
  In (code, make) bulk_two_index_opcodes ->
  parser_sound
    (Combinators.rand
      (Combinators.rand
        (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code)))
      (box (Combinators.app (Combinators.map make parse_u32_as_N)
        (box parse_u32_as_N))))
    bulk_atomic_encoding.
Proof.
  intro Opcode.
  eapply parser_sound_rand_grammar with
    (P := fun bs _ => bulk_prefix bs code)
    (Q := fun bs be => exists first second x y,
      bs = first ++ second /\ index_encoding first x /\
      index_encoding second y /\ be = make x y).
  - apply bulk_prefix_sound.
  - intros j lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_app with
      (P := fun bs f => exists x, index_encoding bs x /\ f = make x)
      (Q := index_encoding).
    + eapply parser_sound_map; [apply parse_index_sound |].
      intros bs x E; exists x; auto.
    + intros k lower; simpl. apply parser_sound_le_lower; apply parse_index_sound.
    + intros first second f y [x [E F]] E'; subst f.
      exists first, second, x, y. split; [reflexivity |].
      split; [exact E |]. split; [exact E' |reflexivity].
  - intros prefix body k be Prefix
      [first [second [x [y [Bytes [E [E' Value]]]]]]].
    subst body be. eapply bulk_two; eassumption.
Qed.

Definition table_atomic_encoding bs be :=
  control_atomic_encoding bs be \/ bulk_atomic_encoding bs be.

Lemma parse_table_instruction_sound n :
  parser_sound
    (parse_table_instruction (Toks := SizedList byte) (M := option) (n := n))
    table_atomic_encoding.
Proof.
  assert (Single : forall code make,
    In (code, make) bulk_single_index_opcodes ->
    parser_sound
      (Combinators.rand
        (Combinators.rand
          (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
          (box (assert_u32 code)))
        (box (Combinators.map make parse_u32_as_N)))
      table_atomic_encoding).
  { intros code make Member. eapply parser_sound_weaken.
    - apply bulk_single_instruction_sound; exact Member.
    - intros bs be E; now right. }
  assert (Two : forall code make,
    In (code, make) bulk_two_index_opcodes ->
    parser_sound
      (Combinators.rand
        (Combinators.rand
          (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
          (box (assert_u32 code)))
        (box (Combinators.app (Combinators.map make parse_u32_as_N)
          (box parse_u32_as_N))))
      table_atomic_encoding).
  { intros code make Member. eapply parser_sound_weaken.
    - apply bulk_two_instruction_sound; exact Member.
    - intros bs be E; now right. }
  unfold parse_table_instruction.
  do 7 (apply parser_sound_alt; [shelve |]). Unshelve.
  - unfold parse_table_fill, parse_tableidx. apply Single.
    unfold bulk_single_index_opcodes; simpl; tauto.
  - unfold parse_table_get, parse_tableidx.
    eapply parser_sound_weaken.
    + apply single_index_instruction_sound.
      unfold single_index_opcodes; simpl; tauto.
    + intros bs be E; now left.
  - unfold parse_table_set, parse_tableidx.
    eapply parser_sound_weaken.
    + apply single_index_instruction_sound.
      unfold single_index_opcodes; simpl; tauto.
    + intros bs be E; now left.
  - unfold parse_table_init, parse_tableidx, parse_elemidx. apply Two.
    unfold bulk_two_index_opcodes; simpl; tauto.
  - unfold parse_elem_drop, parse_elemidx. apply Single.
    unfold bulk_single_index_opcodes; simpl; tauto.
  - unfold parse_table_copy, parse_tableidx. apply Two.
    unfold bulk_two_index_opcodes; simpl; tauto.
  - unfold parse_table_grow, parse_tableidx. apply Single.
    unfold bulk_single_index_opcodes; simpl; tauto.
  - unfold parse_table_size, parse_tableidx. apply Single.
    unfold bulk_single_index_opcodes; simpl; tauto.
Qed.
