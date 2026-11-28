(** Atomic instruction byte grammar.  The opcode tables below are encoding
    rules, not parser runs; u32 immediates admit legal padded encodings. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties binary_format_language_properties
  binary_format_block_properties binary_format_vector_properties
  binary_format_reference_properties binary_format_global_properties
  leb128_properties.
Local Notation byte := Byte.byte.

Definition index_encoding bs x :=
  unsigned_leb bs x /\ (x <= 4294967295)%N /\ length bs <= 5.

Definition single_index_opcodes : list (byte * (N -> basic_instruction)) :=
  (x0c, BI_br) :: (x0d, BI_br_if) ::
  (x10, BI_call) :: (x12, BI_return_call) ::
  (x20, BI_local_get) :: (x21, BI_local_set) ::
  (x22, BI_local_tee) :: (x23, BI_global_get) :: (x24, BI_global_set) ::
  (x25, BI_table_get) :: (x26, BI_table_set) ::
  (xd2, BI_ref_func) :: (x08, BI_throw) ::
  (x14, BI_call_ref) :: (x15, BI_return_call_ref) ::
  (xd6, BI_br_on_non_null) :: nil.

Definition fixed_control_opcodes : list (byte * basic_instruction) :=
  (x00, BI_unreachable) :: (x01, BI_nop) :: (x0f, BI_return) ::
  (x1a, BI_drop) :: (x1b, BI_select None) :: (xd1, BI_ref_is_null) ::
  (xd4, BI_ref_as_non_null) :: (x0a, BI_throw_ref) :: nil.

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
| control_ref_null : forall bytes h,
    source_heap_encoding bytes h ->
    control_atomic_encoding (xd0 :: bytes) (BI_ref_null h)
| control_select_typed : forall bytes ts,
    vector_encoding source_value_encoding bytes ts ->
    control_atomic_encoding (x1c :: bytes) (BI_select (Some ts))
| control_i31 : forall bytes code be,
    index_encoding bytes code ->
    In (code, be) ((28%N, BI_ref_i31) ::
      (29%N, BI_i31_get SX_S) :: (30%N, BI_i31_get SX_U) :: nil) ->
    control_atomic_encoding (xfb :: bytes) be.

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
        vector_encoding source_value_encoding bs ts /\ be = BI_select (Some ts)).
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_map.
       * apply parse_vec_sound; apply parse_declaration_value_sound.
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
  (9%N, BI_data_drop) ::
  (13%N, BI_elem_drop) :: (15%N, BI_table_grow) ::
  (16%N, BI_table_size) :: (17%N, BI_table_fill) :: nil.

Definition bulk_two_index_opcodes :
    list (N * (N -> N -> basic_instruction)) :=
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

Lemma parse_ref_i31_control_sound n :
  parser_sound (parse_ref_i31 (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_ref_i31.
  eapply parser_sound_cmap with
    (P := fun bytes _ => exists payload,
      bytes = xfb :: payload /\ index_encoding payload 28%N).
  - apply parser_sound_prefix_byte with
      (Q := fun bytes x => index_encoding bytes 28%N /\ x = 28%N).
    + intros k lt; simpl; apply parser_sound_le_lower; apply assert_u32_sound.
    + intros bytes x [Enc _]; exists bytes; auto.
  - intros bytes ignored [payload [-> Enc]].
    eapply control_i31; [exact Enc |simpl; auto].
Qed.

Lemma parse_i31_get_control_sound n :
  parser_sound (parse_i31_get (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_i31_get.
  apply parser_sound_prefix_byte with
    (Q := fun bytes be => exists code, index_encoding bytes code /\
      In (code, be) ((28%N, BI_ref_i31) ::
        (29%N, BI_i31_get SX_S) :: (30%N, BI_i31_get SX_U) :: nil)).
  - intros k lt; simpl; apply parser_sound_le_lower.
    apply parser_sound_alt.
    + eapply parser_sound_cmap; [apply assert_u32_sound |].
      intros bytes x [Enc _]; eexists; split; [exact Enc |simpl; auto].
    + eapply parser_sound_cmap; [apply assert_u32_sound |].
      intros bytes x [Enc _]; eexists; split; [exact Enc |simpl; auto].
  - intros bytes be [code [Enc Member]]; eapply control_i31; eassumption.
Qed.

Lemma parse_reference_instruction_sound n :
  parser_sound (parse_reference_instruction (Toks := SizedList byte) (M := option) (n := n))
    control_atomic_encoding.
Proof.
  unfold parse_reference_instruction.
  do 6 (apply parser_sound_alt; [shelve |]). Unshelve.
  - unfold parse_br_on_non_null, parse_labelidx; apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - eapply parser_sound_weaken; [apply parse_source_ref_null_sound |].
    intros bytes be [payload [h [Bytes [Enc Value]]]]; subst bytes be.
    now apply control_ref_null.
  - unfold parse_ref_is_null; apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - unfold parse_ref_func, parse_funcidx; apply single_index_instruction_sound.
    unfold single_index_opcodes; simpl; tauto.
  - unfold parse_ref_as_non_null; apply fixed_control_instruction_sound.
    unfold fixed_control_opcodes; simpl; tauto.
  - apply parse_ref_i31_control_sound.
  - apply parse_i31_get_control_sound.
Qed.
