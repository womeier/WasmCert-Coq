(** Concrete memory grammar for this production AST/profile: memory zero,
    u32 offsets, final alignment flags (including explicit padded zero).
    No addressing/multi-memory model or replacement parser is imported. *)
From Stdlib Require Import List Strings.Byte NArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_atomic_properties binary_format_vector_properties.
Local Notation byte := Byte.byte.

Definition mapped_offset_encoding flags bytes marg :=
  exists offset, index_encoding bytes offset /\
    marg = {| memarg_offset := offset; memarg_align := flags |}.

Definition memarg_tail_encoding flags bytes marg :=
  if N.ltb flags 64 then mapped_offset_encoding flags bytes marg
  else if N.ltb flags 128 then
    exists memory offset,
      bytes = memory ++ offset /\ index_encoding memory 0%N /\
      mapped_offset_encoding (flags - 64)%N offset marg
  else False.

Definition memarg_encoding bytes marg :=
  exists header payload flags,
    bytes = header ++ payload /\ index_encoding header flags /\
    memarg_tail_encoding flags payload marg.

Lemma parse_offset_sound n flags :
  parser_sound
    (Combinators.map (fun offset => {| memarg_offset := offset; memarg_align := flags |})
      (parse_static_offset (Toks := SizedList byte) (M := option) (n := n)))
    (mapped_offset_encoding flags).
Proof.
  eapply parser_sound_map; [apply parse_index_sound |].
  intros bytes offset Enc; exists offset; auto.
Qed.

Theorem parse_memarg_sound n :
  parser_sound (parse_memarg (Toks := SizedList byte) (M := option) (n := n))
    memarg_encoding.
Proof.
  unfold parse_memarg.
  eapply parser_sound_bind with (P := index_encoding) (Q := memarg_tail_encoding).
  - apply parse_index_sound.
  - intros flags k lt.
    unfold memarg_tail_encoding.
    destruct (N.ltb flags 64); simpl.
    + apply parser_sound_le_lower; apply parse_offset_sound.
    + destruct (N.ltb flags 128); simpl.
      * apply parser_sound_le_lower; eapply parser_sound_rand_grammar with
          (P := fun bytes x => index_encoding bytes 0%N /\ x = 0%N)
          (Q := mapped_offset_encoding (flags - 64)%N).
        -- apply assert_u32_sound.
        -- intros j lower; simpl; apply parser_sound_le_lower; apply parse_offset_sound.
        -- intros memory offset x marg [Memory _] Offset.
           exists memory, offset; auto.
      * intros m bound input s Run; discriminate.
  - intros header payload flags marg Header Payload.
    exists header, payload, flags; auto.
Qed.

Definition scalar_memory_opcodes : list (byte * (memarg -> basic_instruction)) :=
  (x28, BI_load T_i32 None) :: (x29, BI_load T_i64 None) ::
  (x2a, BI_load T_f32 None) :: (x2b, BI_load T_f64 None) ::
  (x2c, BI_load T_i32 (Some (Tp_i8, SX_S))) ::
  (x2d, BI_load T_i32 (Some (Tp_i8, SX_U))) ::
  (x2e, BI_load T_i32 (Some (Tp_i16, SX_S))) ::
  (x2f, BI_load T_i32 (Some (Tp_i16, SX_U))) ::
  (x30, BI_load T_i64 (Some (Tp_i8, SX_S))) ::
  (x31, BI_load T_i64 (Some (Tp_i8, SX_U))) ::
  (x32, BI_load T_i64 (Some (Tp_i16, SX_S))) ::
  (x33, BI_load T_i64 (Some (Tp_i16, SX_U))) ::
  (x34, BI_load T_i64 (Some (Tp_i32, SX_S))) ::
  (x35, BI_load T_i64 (Some (Tp_i32, SX_U))) ::
  (x36, BI_store T_i32 None) :: (x37, BI_store T_i64 None) ::
  (x38, BI_store T_f32 None) :: (x39, BI_store T_f64 None) ::
  (x3a, BI_store T_i32 (Some Tp_i8)) ::
  (x3b, BI_store T_i32 (Some Tp_i16)) ::
  (x3c, BI_store T_i64 (Some Tp_i8)) ::
  (x3d, BI_store T_i64 (Some Tp_i16)) ::
  (x3e, BI_store T_i64 (Some Tp_i32)) :: nil.

Definition vector_memarg_opcodes : list (N * (memarg -> basic_instruction)) :=
  (0%N, BI_load_vec LVA_none) ::
  (1%N, BI_load_vec (LVA_extend (8%N, 8%N) SX_S)) ::
  (2%N, BI_load_vec (LVA_extend (8%N, 8%N) SX_U)) ::
  (3%N, BI_load_vec (LVA_extend (16%N, 4%N) SX_S)) ::
  (4%N, BI_load_vec (LVA_extend (16%N, 4%N) SX_U)) ::
  (5%N, BI_load_vec (LVA_extend (32%N, 2%N) SX_S)) ::
  (6%N, BI_load_vec (LVA_extend (32%N, 2%N) SX_U)) ::
  (7%N, BI_load_vec (LVA_splat 8%N)) ::
  (8%N, BI_load_vec (LVA_splat 16%N)) ::
  (9%N, BI_load_vec (LVA_splat 32%N)) ::
  (10%N, BI_load_vec (LVA_splat 64%N)) ::
  (11%N, BI_store_vec) ::
  (92%N, BI_load_vec (LVA_zero 32%N)) ::
  (93%N, BI_load_vec (LVA_zero 64%N)) :: nil.

Definition vector_memory_lane_opcodes :
    list (N * (memarg -> laneidx -> basic_instruction)) :=
  (84%N, BI_load_vec_lane 8%N) :: (85%N, BI_load_vec_lane 16%N) ::
  (86%N, BI_load_vec_lane 32%N) :: (87%N, BI_load_vec_lane 64%N) ::
  (88%N, BI_store_vec_lane 8%N) :: (89%N, BI_store_vec_lane 16%N) ::
  (90%N, BI_store_vec_lane 32%N) :: (91%N, BI_store_vec_lane 64%N) :: nil.

Inductive vector_memory_encoding : list byte -> basic_instruction -> Prop :=
| vector_memory_memarg : forall code make header body marg,
    In (code, make) vector_memarg_opcodes ->
    index_encoding header code -> memarg_encoding body marg ->
    vector_memory_encoding (header ++ body) (make marg)
| vector_memory_lane : forall code make header body marg lane,
    In (code, make) vector_memory_lane_opcodes ->
    index_encoding header code -> memarg_encoding body marg ->
    vector_memory_encoding (header ++ body ++ (lane :: nil)) (make marg (Byte.to_N lane)).

Inductive memory_instruction_encoding : list byte -> basic_instruction -> Prop :=
| memory_scalar : forall opcode make bytes marg,
    In (opcode, make) scalar_memory_opcodes ->
    memarg_encoding bytes marg ->
    memory_instruction_encoding (opcode :: bytes) (make marg)
| memory_vector : forall bytes be, vector_memory_encoding bytes be ->
    memory_instruction_encoding (xfd :: bytes) be
| memory_size : memory_instruction_encoding (x3f :: x00 :: nil) BI_memory_size
| memory_grow : memory_instruction_encoding (x40 :: x00 :: nil) BI_memory_grow
| memory_init : forall header data x,
    index_encoding header 8%N -> index_encoding data x ->
    memory_instruction_encoding (xfc :: header ++ data ++ (x00 :: nil)) (BI_memory_init x)
| memory_drop : forall header data x,
    index_encoding header 9%N -> index_encoding data x ->
    memory_instruction_encoding (xfc :: header ++ data) (BI_data_drop x)
| memory_copy : forall header,
    index_encoding header 10%N ->
    memory_instruction_encoding (xfc :: header ++ (x00 :: x00 :: nil)) BI_memory_copy
| memory_fill : forall header,
    index_encoding header 11%N ->
    memory_instruction_encoding (xfc :: header ++ (x00 :: nil)) BI_memory_fill.

Lemma scalar_memory_instruction_sound n opcode make :
  In (opcode, make) scalar_memory_opcodes ->
  parser_sound
    (Combinators.rand (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.map make parse_memarg)))
    memory_instruction_encoding.
Proof.
  intro Member.
  apply parser_sound_prefix_byte with
    (Q := fun bytes be => exists marg, memarg_encoding bytes marg /\ be = make marg).
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_memarg_sound |].
    intros bytes marg Enc; exists marg; auto.
  - intros bytes be [marg [Enc ->]]; now apply memory_scalar.
Qed.

Lemma vector_memarg_instruction_sound n code make :
  In (code, make) vector_memarg_opcodes ->
  parser_sound
    (Combinators.rand (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.map make parse_memarg)))
    vector_memory_encoding.
Proof.
  intro Member.
  eapply parser_sound_rand_grammar with
    (P := fun bytes x => index_encoding bytes code /\ x = code)
    (Q := fun bytes be => exists marg, memarg_encoding bytes marg /\ be = make marg).
  - apply assert_u32_sound.
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_memarg_sound |].
    intros bytes marg Enc; exists marg; auto.
  - intros header body x be [Header _] [marg [Body ->]].
    eapply vector_memory_memarg; eassumption.
Qed.

Lemma vector_lane_instruction_sound n code make :
  In (code, make) vector_memory_lane_opcodes ->
  parser_sound
    (Combinators.rand (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.app (Combinators.map make parse_memarg) (box parse_laneidx))))
    vector_memory_encoding.
Proof.
  intro Member.
  eapply parser_sound_rand_grammar with
    (P := fun bytes x => index_encoding bytes code /\ x = code)
    (Q := fun bytes be => exists body marg lane,
      bytes = body ++ (lane :: nil) /\ memarg_encoding body marg /\
      be = make marg (Byte.to_N lane)).
  - apply assert_u32_sound.
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_app with
      (P := fun bytes f => exists marg, memarg_encoding bytes marg /\ f = make marg)
      (Q := fun bytes lane => exists b, bytes = b :: nil /\ lane = Byte.to_N b).
    + eapply parser_sound_map; [apply parse_memarg_sound |].
      intros bytes marg Enc; exists marg; auto.
    + intros j lower; simpl; apply parser_sound_le_lower.
      unfold parse_laneidx; eapply parser_sound_map; [apply parser_sound_anyTok |].
      intros bytes lane Enc; exists lane; auto.
    + intros body tail f lane [marg [Body ->]] [b [-> ->]].
      exists body, marg, b; auto.
  - intros header body x be [Header _] [payload [marg [lane [Bytes [Body ->]]]]].
    subst body; eapply vector_memory_lane; eassumption.
Qed.

Ltac memory_opcode_member :=
  repeat first [left; reflexivity |right].

Lemma parse_vector_plain_load_sound n :
  parser_sound (parse_v128_load (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_load; apply vector_memarg_instruction_sound.
  left; reflexivity.
Qed.

Lemma parse_vector_packed_load_sound n :
  parser_sound (parse_v128_load_packed (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_load_packed.
  do 5 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply vector_memarg_instruction_sound; unfold vector_memarg_opcodes; memory_opcode_member.
Qed.

Lemma parse_vector_splat_load_sound n :
  parser_sound (parse_v128_load_splat (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_load_splat.
  do 3 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply vector_memarg_instruction_sound; unfold vector_memarg_opcodes; memory_opcode_member.
Qed.

Lemma parse_vector_zero_load_sound n :
  parser_sound (parse_v128_load_zero (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_load_zero; apply parser_sound_alt.
  all: apply vector_memarg_instruction_sound; unfold vector_memarg_opcodes; memory_opcode_member.
Qed.

Lemma parse_vector_store_sound n :
  parser_sound (parse_v128_store (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_store; apply vector_memarg_instruction_sound.
  unfold vector_memarg_opcodes; memory_opcode_member.
Qed.

Lemma parse_vector_load_lane_sound n :
  parser_sound (parse_v128_load_lane (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_load_lane.
  do 3 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply vector_lane_instruction_sound; unfold vector_memory_lane_opcodes; memory_opcode_member.
Qed.

Lemma parse_vector_store_lane_sound n :
  parser_sound (parse_v128_store_lane (Toks := SizedList byte) (M := option) (n := n))
    vector_memory_encoding.
Proof.
  unfold parse_v128_store_lane.
  do 3 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply vector_lane_instruction_sound; unfold vector_memory_lane_opcodes; memory_opcode_member.
Qed.

Theorem parse_vector_memory_sound n :
  parser_sound (parse_vector_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  unfold parse_vector_memory_instruction.
  apply parser_sound_prefix_byte with (Q := vector_memory_encoding).
  - intros k lt; simpl; apply parser_sound_le_lower.
    apply parser_sound_alt; [apply parse_vector_plain_load_sound |].
    apply parser_sound_alt; [apply parse_vector_packed_load_sound |].
    apply parser_sound_alt; [apply parse_vector_splat_load_sound |].
    apply parser_sound_alt; [apply parse_vector_zero_load_sound |].
    apply parser_sound_alt; [apply parse_vector_store_sound |].
    apply parser_sound_alt; [apply parse_vector_load_lane_sound |].
    apply parse_vector_store_lane_sound.
  - intros bytes be Enc; now apply memory_vector.
Qed.

Lemma reserved_memory_instruction_sound n opcode be :
  (opcode = x3f /\ be = BI_memory_size) \/ (opcode = x40 /\ be = BI_memory_grow) ->
  parser_sound
    (Combinators.rand (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.cmap be (exact_byte x00))))
    memory_instruction_encoding.
Proof.
  intro Opcode.
  apply parser_sound_prefix_byte with (Q := fun bytes value => bytes = x00 :: nil /\ value = be).
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
    intros bytes b [Bytes _]; auto.
  - intros bytes value [-> ->]; destruct Opcode as [[-> ->]|[-> ->]]; constructor.
Qed.

Lemma parse_memory_init_sound n :
  parser_sound (parse_memory_init (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  unfold parse_memory_init.
  eapply parser_sound_rand_grammar with
    (P := fun bytes _ => bulk_prefix bytes 8%N)
    (Q := fun bytes be => exists data x, bytes = data ++ (x00 :: nil) /\
      index_encoding data x /\ be = BI_memory_init x).
  - apply bulk_prefix_sound.
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_app with
      (P := fun bytes f => exists x, index_encoding bytes x /\
        f = (fun _ : byte => BI_memory_init x))
      (Q := fun bytes b => bytes = x00 :: nil /\ b = x00).
    + eapply parser_sound_map; [apply parse_index_sound |].
      intros bytes x Enc; exists x; auto.
    + intros j lower; simpl; apply parser_sound_le_lower; apply parser_sound_exact_byte.
    + intros data reserved f b [x [Enc ->]] [-> _]; exists data, x; auto.
  - intros prefix body k be [header [-> Header]] [data [x [-> [Data ->]]]].
    apply memory_init; assumption.
Qed.

Lemma parse_data_drop_sound n :
  parser_sound (parse_data_drop (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  unfold parse_data_drop.
  eapply parser_sound_rand_grammar with
    (P := fun bytes _ => bulk_prefix bytes 9%N)
    (Q := fun bytes be => exists x, index_encoding bytes x /\ be = BI_data_drop x).
  - apply bulk_prefix_sound.
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_index_sound |].
    intros bytes x Enc; exists x; auto.
  - intros prefix body k be [header [-> Header]] [x [Body ->]].
    now apply memory_drop.
Qed.

Lemma parse_memory_copy_sound n :
  parser_sound (parse_memory_copy (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  unfold parse_memory_copy.
  eapply parser_sound_rand_grammar with
    (P := fun bytes _ => bulk_prefix bytes 10%N)
    (Q := fun bytes be => bytes = x00 :: x00 :: nil /\ be = BI_memory_copy).
  - apply bulk_prefix_sound.
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_app with
      (P := fun bytes f => bytes = x00 :: nil /\ f = (fun _ : byte => BI_memory_copy))
      (Q := fun bytes b => bytes = x00 :: nil /\ b = x00).
    + eapply parser_sound_map; [apply parser_sound_exact_byte |].
      intros bytes b [Bytes _]; auto.
    + intros j lower; simpl; apply parser_sound_le_lower; apply parser_sound_exact_byte.
    + intros first second f b [-> ->] [-> _]; auto.
  - intros prefix body k be [header [-> Header]] [-> ->]; now apply memory_copy.
Qed.

Lemma parse_memory_fill_sound n :
  parser_sound (parse_memory_fill (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  unfold parse_memory_fill.
  eapply parser_sound_rand_grammar with
    (P := fun bytes _ => bulk_prefix bytes 11%N)
    (Q := fun bytes be => bytes = x00 :: nil /\ be = BI_memory_fill).
  - apply bulk_prefix_sound.
  - intros k lt; simpl; apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parser_sound_exact_byte |].
    intros bytes b [Bytes _]; auto.
  - intros prefix body k be [header [-> Header]] [-> ->]; now apply memory_fill.
Qed.

Ltac scalar_memory_leaf_sound :=
  unfold parse_i32_load, parse_i64_load, parse_f32_load, parse_f64_load,
    parse_i32_load8_s, parse_i32_load8_u, parse_i32_load16_s, parse_i32_load16_u,
    parse_i64_load8_s, parse_i64_load8_u, parse_i64_load16_s, parse_i64_load16_u,
    parse_i64_load32_s, parse_i64_load32_u,
    parse_i32_store, parse_i64_store, parse_f32_store, parse_f64_store,
    parse_i32_store8, parse_i32_store16, parse_i64_store8, parse_i64_store16, parse_i64_store32;
  apply scalar_memory_instruction_sound; unfold scalar_memory_opcodes; memory_opcode_member.

Theorem parse_memory_instruction_sound n :
  parser_sound (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  unfold parse_memory_instruction.
  do 23 (apply parser_sound_alt; [scalar_memory_leaf_sound |]).
  apply parser_sound_alt; [apply parse_vector_memory_sound |].
  apply parser_sound_alt.
  - unfold parse_memory_size; apply reserved_memory_instruction_sound; auto.
  - apply parser_sound_alt.
    + unfold parse_memory_grow; apply reserved_memory_instruction_sound; auto.
    + apply parser_sound_alt; [apply parse_memory_init_sound |].
      apply parser_sound_alt; [apply parse_data_drop_sound |].
      apply parser_sound_alt; [apply parse_memory_copy_sound |].
      apply parse_memory_fill_sound.
Qed.
