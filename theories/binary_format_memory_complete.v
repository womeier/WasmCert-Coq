(** Concrete arbitrary-suffix completeness of production memory immediates.
    No atomic parser contracts are assumed. *)
From Stdlib Require Import List Strings.Byte NArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_printer_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_memory_properties
  binary_format_simd_complete binary_format_index_lookahead_properties
  leb128_unsigned_printer_properties leb128_properties.
Local Notation byte := Byte.byte.

Lemma parse_offset_complete n flags :
  parser_complete
    (Combinators.map (fun offset => {| memarg_offset := offset; memarg_align := flags |})
      (parse_static_offset (Toks := SizedList byte) (M := option) (n := n)))
    (mapped_offset_encoding flags).
Proof.
  eapply parser_complete_map; [apply parse_u32_prefix_complete |].
  intros bytes marg Enc; exact Enc.
Qed.

Theorem parse_memarg_complete n :
  parser_complete (parse_memarg (Toks := SizedList byte) (M := option) (n := n))
    memarg_encoding.
Proof.
  unfold parse_memarg.
  eapply parser_complete_bind with (P := index_encoding) (Q := memarg_tail_encoding).
  - apply parse_u32_prefix_complete.
  - intros flags k lt; unfold memarg_tail_encoding.
    destruct (N.ltb flags 64); simpl.
    + apply parser_complete_le_lower; apply parse_offset_complete.
    + destruct (N.ltb flags 128); simpl.
      * apply parser_complete_le_lower.
        eapply parser_complete_rand_grammar with
          (P := fun bytes x => index_encoding bytes 0%N /\ x = 0%N)
          (Q := mapped_offset_encoding (flags - 64)%N).
        -- apply assert_u32_complete.
        -- intros j lower; simpl; apply parser_complete_le_lower; apply parse_offset_complete.
        -- intros bytes marg [memory [offset [Bytes [Memory Offset]]]].
           exists memory, offset, 0%N; split; [exact Bytes |].
           split; [auto |exact Offset].
      * intros m bound input prefix suffix marg Bytes Impossible; contradiction.
  - intros bytes marg Enc; exact Enc.
Qed.

Theorem run_parse_memarg_correct bytes marg rest :
  run_parse_prefix (fun n => parse_memarg (n := n)) bytes = Some (marg, rest) <->
  exists prefix, bytes = prefix ++ rest /\ memarg_encoding prefix marg.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_memarg_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_memarg_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest marg Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (marg, rest)).
    now rewrite Value, Rest.
Qed.

Theorem scalar_memory_instruction_complete n opcode (make : memarg -> basic_instruction) :
  parser_complete
    (Combinators.rand (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode)
      (box (Combinators.map make parse_memarg)))
    (fun bytes be => exists body marg,
      bytes = opcode :: body /\ memarg_encoding body marg /\ be = make marg).
Proof.
  apply parser_complete_prefix_byte with
    (Q := fun bytes be => exists marg, memarg_encoding bytes marg /\ be = make marg).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_memarg_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be [body [marg [Bytes [Enc Value]]]].
    exists body; split; [exact Bytes |exists marg; auto].
Qed.

Definition vector_memarg_payload code (make : memarg -> basic_instruction) bytes be :=
  exists header body marg, bytes = header ++ body /\
    index_encoding header code /\ memarg_encoding body marg /\ be = make marg.

Lemma vector_memarg_complete n code make :
  parser_complete
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.map make parse_memarg)))
    (vector_memarg_payload code make).
Proof.
  eapply parser_complete_rand_grammar with
    (P := fun bytes x => index_encoding bytes code /\ x = code)
    (Q := fun bytes be => exists marg, memarg_encoding bytes marg /\ be = make marg).
  - apply assert_u32_complete.
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [apply parse_memarg_complete |].
    intros bytes be Enc; exact Enc.
  - intros bytes be [header [body [marg [Bytes [Header [Body Value]]]]]].
    exists header, body, code; split; [exact Bytes |].
    split; [auto |exists marg; auto].
Qed.

Definition vector_lane_payload code
    (make : memarg -> laneidx -> basic_instruction) bytes be :=
  exists header body marg lane, bytes = header ++ body ++ (lane :: nil) /\
    index_encoding header code /\ memarg_encoding body marg /\
    be = make marg (Byte.to_N lane).

Lemma vector_lane_complete n code make :
  parser_complete
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.app (Combinators.map make parse_memarg) (box parse_laneidx))))
    (vector_lane_payload code make).
Proof.
  eapply parser_complete_rand_grammar with
    (P := fun bytes x => index_encoding bytes code /\ x = code)
    (Q := fun bytes be => exists body marg lane,
      bytes = body ++ (lane :: nil) /\ memarg_encoding body marg /\
      be = make marg (Byte.to_N lane)).
  - apply assert_u32_complete.
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_app with
      (P := fun bytes f => exists marg, memarg_encoding bytes marg /\ f = make marg)
      (Q := fun bytes lane => exists b, bytes = b :: nil /\ lane = Byte.to_N b).
    + eapply parser_complete_map; [apply parse_memarg_complete |].
      intros bytes f Enc; exact Enc.
    + intros j lower; simpl; apply parser_complete_le_lower; apply parse_laneidx_complete.
    + intros bytes be [body [marg [lane [Bytes [Body Value]]]]].
      exists body, (lane :: nil), (make marg), (Byte.to_N lane).
      split; [exact Bytes |].
      split; [exists marg; auto |].
      split; [exists lane; auto |exact Value].
  - intros bytes be [header [body [marg [lane [Bytes [Header [Body Value]]]]]]].
    exists header, (body ++ (lane :: nil)), code.
    split; [exact Bytes |]. split; [auto |exists body, marg, lane; auto].
Qed.

Ltac memory_initial_index :=
  lazymatch goal with
  | |- parser_initial_index (Combinators.alt _ _) _ =>
      apply parser_initial_index_alt; [memory_initial_index |memory_initial_index]
  | |- parser_initial_index (Combinators.rand (assert_u32 _) _) _ =>
      apply parser_initial_index_rand; apply assert_u32_initial_index
  end.

Ltac memory_index_dispatch code Complete Head :=
  lazymatch goal with
  | |- parser_complete (Combinators.alt _ _) _ =>
      first
        [solve [apply parser_complete_alt_left; memory_index_dispatch code Complete Head]
        |eapply parser_complete_alt_right_index with (actual := code);
          [memory_initial_index
          |cbn; intuition congruence
          |exact Head
          |memory_index_dispatch code Complete Head]]
  | _ => exact Complete
  end.

Lemma vector_memory_memarg_choice_complete n code make :
  In (code, make) vector_memarg_opcodes ->
  parser_complete
    (Combinators.alt (parse_v128_load (Toks := SizedList byte) (M := option) (n := n))
      (Combinators.alt parse_v128_load_packed
        (Combinators.alt parse_v128_load_splat
          (Combinators.alt parse_v128_load_zero
            (Combinators.alt parse_v128_store
              (Combinators.alt parse_v128_load_lane parse_v128_store_lane))))))
    (vector_memarg_payload code make).
Proof.
  intro Member.
  assert (Head : forall bytes be, vector_memarg_payload code make bytes be ->
    exists header body, bytes = header ++ body /\ index_encoding header code).
  { intros bytes be [header [body [marg [Bytes [Header _]]]]].
    exists header, body; auto. }
  unfold vector_memarg_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst code make;
    unfold parse_v128_load, parse_v128_load_packed, parse_v128_load_splat,
      parse_v128_load_zero, parse_v128_store, parse_v128_load_lane, parse_v128_store_lane;
    lazymatch goal with
    | |- parser_complete _ (vector_memarg_payload ?code ?make) =>
        memory_index_dispatch code (vector_memarg_complete n code make) Head
    end.
Qed.

Lemma vector_memory_lane_choice_complete n code make :
  In (code, make) vector_memory_lane_opcodes ->
  parser_complete
    (Combinators.alt (parse_v128_load (Toks := SizedList byte) (M := option) (n := n))
      (Combinators.alt parse_v128_load_packed
        (Combinators.alt parse_v128_load_splat
          (Combinators.alt parse_v128_load_zero
            (Combinators.alt parse_v128_store
              (Combinators.alt parse_v128_load_lane parse_v128_store_lane))))))
    (vector_lane_payload code make).
Proof.
  intro Member.
  assert (Head : forall bytes be, vector_lane_payload code make bytes be ->
    exists header body, bytes = header ++ body /\ index_encoding header code).
  { intros bytes be [header [body [marg [lane [Bytes [Header _]]]]]].
    exists header, (body ++ lane :: nil); auto. }
  unfold vector_memory_lane_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst code make;
    unfold parse_v128_load, parse_v128_load_packed, parse_v128_load_splat,
      parse_v128_load_zero, parse_v128_store, parse_v128_load_lane, parse_v128_store_lane;
    lazymatch goal with
    | |- parser_complete _ (vector_lane_payload ?code ?make) =>
        memory_index_dispatch code (vector_lane_complete n code make) Head
    end.
Qed.

Theorem parse_vector_memory_complete n :
  parser_complete
    (parse_vector_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes be => exists body, bytes = xfd :: body /\ vector_memory_encoding body be).
Proof.
  unfold parse_vector_memory_instruction.
  apply parser_complete_prefix_byte with (Q := vector_memory_encoding).
  - intros k lt; simpl; apply parser_complete_le_lower.
    intros m bound input prefix suffix be Bytes Enc.
    destruct Enc as [code make header body marg Member Header Body
      |code make header body marg lane Member Header Body].
    + eapply vector_memory_memarg_choice_complete; [exact Member |exact Bytes |].
      exists header, body, marg; auto.
    + eapply vector_memory_lane_choice_complete; [exact Member |exact Bytes |].
      exists header, body, marg, lane; auto.
  - intros bytes be Enc; exact Enc.
Qed.

Lemma memory_extended_complete n code
    (payload : Box (byte_parser basic_instruction) n) Q R :
  (forall k (lt : k < n), parser_complete (call payload lt) Q) ->
  (forall bytes be, R bytes be -> exists header body,
    bytes = xfc :: header ++ body /\ index_encoding header code /\ Q body be) ->
  parser_complete
    (Combinators.rand
      (Combinators.rand
        (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code))) payload) R.
Proof.
  intros Payload Split.
  eapply parser_complete_rand_grammar with
    (P := fun bytes x => bulk_prefix bytes code /\ x = code) (Q := Q).
  - apply parser_complete_prefix_byte with
      (Q := fun bytes x => index_encoding bytes code /\ x = code).
    + intros k lt; simpl; apply parser_complete_le_lower; apply assert_u32_complete.
    + intros bytes x [[header [Bytes Header]] Value]; exists header; auto.
  - exact Payload.
  - intros bytes be Enc.
    destruct (Split _ _ Enc) as [header [body [Bytes [Header Body]]]].
    exists (xfc :: header), body, code.
    split; [exact Bytes |]. split; [split; [exists header; auto |reflexivity] |exact Body].
Qed.

Definition memory_init_payload bytes be :=
  exists data x, bytes = data ++ (x00 :: nil) /\
    index_encoding data x /\ be = BI_memory_init x.

Lemma memory_init_payload_complete n :
  parser_complete
    (Combinators.app
      (Combinators.map (fun x _ => BI_memory_init x)
        (parse_dataidx (Toks := SizedList byte) (M := option) (n := n)))
      (box (exact_byte x00))) memory_init_payload.
Proof.
  eapply parser_complete_app with
    (P := fun bytes f => exists x, index_encoding bytes x /\
      f = (fun _ : byte => BI_memory_init x))
    (Q := fun bytes b => bytes = x00 :: nil /\ b = x00).
  - eapply parser_complete_map; [apply parse_u32_prefix_complete |].
    intros bytes f Enc; exact Enc.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parser_complete_exact_byte.
  - intros bytes be [data [x [Bytes [Data Value]]]].
    exists data, (x00 :: nil), (fun _ : byte => BI_memory_init x), x00.
    split; [exact Bytes |]. split; [exists x; auto |auto].
Qed.

Lemma memory_copy_payload_complete n :
  parser_complete
    (Combinators.app
      (Combinators.map (fun _ _ => BI_memory_copy)
        (exact_byte (Toks := SizedList byte) (M := option) (n := n) x00))
      (box (exact_byte x00)))
    (fun bytes be => bytes = x00 :: x00 :: nil /\ be = BI_memory_copy).
Proof.
  eapply parser_complete_app with
    (P := fun bytes f => bytes = x00 :: nil /\ f = (fun _ : byte => BI_memory_copy))
    (Q := fun bytes b => bytes = x00 :: nil /\ b = x00).
  - eapply parser_complete_map; [apply parser_complete_exact_byte |].
    intros bytes f [Bytes ->]; exists x00; auto.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parser_complete_exact_byte.
  - intros bytes be [-> ->].
    exists (x00 :: nil), (x00 :: nil), (fun _ : byte => BI_memory_copy), x00; auto.
Qed.

Ltac unfold_memory_parsers :=
  unfold parse_memory_instruction,
    parse_i32_load, parse_i64_load, parse_f32_load, parse_f64_load,
    parse_i32_load8_s, parse_i32_load8_u, parse_i32_load16_s, parse_i32_load16_u,
    parse_i64_load8_s, parse_i64_load8_u, parse_i64_load16_s, parse_i64_load16_u,
    parse_i64_load32_s, parse_i64_load32_u,
    parse_i32_store, parse_i64_store, parse_f32_store, parse_f64_store,
    parse_i32_store8, parse_i32_store16, parse_i64_store8, parse_i64_store16,
    parse_i64_store32, parse_vector_memory_instruction, parse_memory_size,
    parse_memory_grow, parse_memory_init, parse_data_drop, parse_memory_copy,
    parse_memory_fill.

Ltac memory_byte_dispatch opcode Complete Head :=
  first
    [exact Complete
    |lazymatch goal with
     | |- parser_complete (Combinators.alt _ _) _ =>
       first
         [solve [apply parser_complete_alt_left; exact Complete]
         |eapply parser_complete_alt_right_initial with (actual := opcode);
           [numeric_initial |discriminate |exact Head
           |memory_byte_dispatch opcode Complete Head]]
     end].

Lemma memory_scalar_choice_complete n opcode make :
  In (opcode, make) scalar_memory_opcodes ->
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes be => exists body marg,
      bytes = opcode :: body /\ memarg_encoding body marg /\ be = make marg).
Proof.
  intro Member.
  assert (Head : forall bytes be, (exists body marg,
    bytes = opcode :: body /\ memarg_encoding body marg /\ be = make marg) ->
    exists body, bytes = opcode :: body).
  { intros bytes be [body [marg [Bytes _]]]; exists body; auto. }
  unfold scalar_memory_opcodes in Member; cbn [In] in Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst opcode make; unfold_memory_parsers;
    lazymatch goal with
    | |- parser_complete _ (fun bytes be => exists body marg,
      bytes = ?opcode :: body /\ memarg_encoding body marg /\ be = ?make marg) =>
        memory_byte_dispatch opcode
          (scalar_memory_instruction_complete n opcode make) Head
    end.
Qed.

Ltac memory_bulk_dispatch code Complete Head ExtendedHead :=
  first
    [exact Complete
    |lazymatch goal with
     | |- parser_complete (Combinators.alt _ _) _ =>
       first
         [solve [apply parser_complete_alt_left; exact Complete]
         |eapply parser_complete_alt_right_initial with (actual := xfc);
           [numeric_initial |discriminate |exact Head
           |memory_bulk_dispatch code Complete Head ExtendedHead]
         |eapply parser_complete_alt_right_extended with (tag := xfc) (actual := code);
           [apply parser_initial_extended_rand; apply extended_assert_initial
           |discriminate |exact ExtendedHead
           |memory_bulk_dispatch code Complete Head ExtendedHead]]
     end].

Definition memory_bulk_payload code (Q : list byte -> basic_instruction -> Prop) bytes be :=
  exists header body, bytes = xfc :: header ++ body /\
    index_encoding header code /\ Q body be.

Lemma memory_init_complete n :
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (memory_bulk_payload 8%N memory_init_payload).
Proof.
  assert (Complete : parser_complete (parse_memory_init (n := n))
    (memory_bulk_payload 8%N memory_init_payload)).
  { unfold parse_memory_init; eapply memory_extended_complete.
    - intros k lt; simpl; apply parser_complete_le_lower; apply memory_init_payload_complete.
    - intros bytes be Enc; exact Enc. }
  assert (Head : forall bytes be, memory_bulk_payload 8%N memory_init_payload bytes be ->
    exists body, bytes = xfc :: body).
  { intros bytes be [header [body [Bytes _]]]; exists (header ++ body); auto. }
  assert (ExtendedHead : forall bytes be,
    memory_bulk_payload 8%N memory_init_payload bytes be ->
    exists header body, bytes = xfc :: header ++ body /\ index_encoding header 8%N).
  { intros bytes be [header [body [Bytes [Header _]]]]; exists header, body; auto. }
  unfold parse_memory_init in Complete.
  unfold_memory_parsers; memory_bulk_dispatch 8%N Complete Head ExtendedHead.
Qed.

Lemma memory_drop_complete n :
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (memory_bulk_payload 9%N
      (fun bytes be => exists x, index_encoding bytes x /\ be = BI_data_drop x)).
Proof.
  set (Q := fun bytes be => exists x, index_encoding bytes x /\ be = BI_data_drop x).
  assert (Complete : parser_complete (parse_data_drop (n := n)) (memory_bulk_payload 9%N Q)).
  { unfold parse_data_drop; eapply memory_extended_complete.
    - intros k lt; simpl; apply parser_complete_le_lower.
      eapply parser_complete_map; [apply parse_u32_prefix_complete |].
      intros bytes be Enc; exact Enc.
    - intros bytes be Enc; exact Enc. }
  assert (Head : forall bytes be, memory_bulk_payload 9%N Q bytes be ->
    exists body, bytes = xfc :: body).
  { intros bytes be [header [body [Bytes _]]]; exists (header ++ body); auto. }
  assert (ExtendedHead : forall bytes be, memory_bulk_payload 9%N Q bytes be ->
    exists header body, bytes = xfc :: header ++ body /\ index_encoding header 9%N).
  { intros bytes be [header [body [Bytes [Header _]]]]; exists header, body; auto. }
  unfold parse_data_drop in Complete.
  unfold_memory_parsers; memory_bulk_dispatch 9%N Complete Head ExtendedHead.
Qed.

Lemma memory_copy_complete n :
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (memory_bulk_payload 10%N
      (fun bytes be => bytes = x00 :: x00 :: nil /\ be = BI_memory_copy)).
Proof.
  set (Q := fun bytes be => bytes = x00 :: x00 :: nil /\ be = BI_memory_copy).
  assert (Complete : parser_complete (parse_memory_copy (n := n)) (memory_bulk_payload 10%N Q)).
  { unfold parse_memory_copy; eapply memory_extended_complete.
    - intros k lt; simpl; apply parser_complete_le_lower; apply memory_copy_payload_complete.
    - intros bytes be Enc; exact Enc. }
  assert (Head : forall bytes be, memory_bulk_payload 10%N Q bytes be ->
    exists body, bytes = xfc :: body).
  { intros bytes be [header [body [Bytes _]]]; exists (header ++ body); auto. }
  assert (ExtendedHead : forall bytes be, memory_bulk_payload 10%N Q bytes be ->
    exists header body, bytes = xfc :: header ++ body /\ index_encoding header 10%N).
  { intros bytes be [header [body [Bytes [Header _]]]]; exists header, body; auto. }
  unfold parse_memory_copy in Complete.
  unfold_memory_parsers; memory_bulk_dispatch 10%N Complete Head ExtendedHead.
Qed.

Lemma memory_fill_complete n :
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (memory_bulk_payload 11%N
      (fun bytes be => bytes = x00 :: nil /\ be = BI_memory_fill)).
Proof.
  set (Q := fun bytes be => bytes = x00 :: nil /\ be = BI_memory_fill).
  assert (Complete : parser_complete (parse_memory_fill (n := n)) (memory_bulk_payload 11%N Q)).
  { unfold parse_memory_fill; eapply memory_extended_complete with (Q := Q).
    - intros k lt; simpl; apply parser_complete_le_lower.
      eapply parser_complete_map; [apply parser_complete_exact_byte |].
      intros bytes be Enc; unfold Q in Enc; destruct Enc as [Bytes ->].
      exists x00; auto.
    - intros bytes be Enc; exact Enc. }
  assert (Head : forall bytes be, memory_bulk_payload 11%N Q bytes be ->
    exists body, bytes = xfc :: body).
  { intros bytes be [header [body [Bytes _]]]; exists (header ++ body); auto. }
  assert (ExtendedHead : forall bytes be, memory_bulk_payload 11%N Q bytes be ->
    exists header body, bytes = xfc :: header ++ body /\ index_encoding header 11%N).
  { intros bytes be [header [body [Bytes [Header _]]]]; exists header, body; auto. }
  unfold parse_memory_fill in Complete.
  unfold_memory_parsers; memory_bulk_dispatch 11%N Complete Head ExtendedHead.
Qed.

Lemma memory_reserved_complete n opcode be :
  (opcode = x3f /\ be = BI_memory_size) \/
  (opcode = x40 /\ be = BI_memory_grow) ->
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => bytes = opcode :: x00 :: nil /\ value = be).
Proof.
  intro Cases.
  assert (Complete : parser_complete
    (Combinators.rand (exact_byte (n := n) opcode)
      (box (Combinators.cmap be (exact_byte x00))))
    (fun bytes value => bytes = opcode :: x00 :: nil /\ value = be)).
  { apply parser_complete_prefix_byte with
      (Q := fun bytes value => bytes = x00 :: nil /\ value = be).
    - intros k lt; simpl; apply parser_complete_le_lower; apply fixed_instruction_complete.
    - intros bytes value [Bytes Value]; exists (x00 :: nil); auto. }
  assert (Head : forall bytes value,
    bytes = opcode :: x00 :: nil /\ value = be -> exists body, bytes = opcode :: body).
  { intros bytes value [Bytes _]; exists (x00 :: nil); auto. }
  destruct Cases as [[-> ->]|[-> ->]]; unfold_memory_parsers.
  - memory_byte_dispatch x3f Complete Head.
  - memory_byte_dispatch x40 Complete Head.
Qed.

Theorem parse_memory_instruction_complete n :
  parser_complete
    (parse_memory_instruction (Toks := SizedList byte) (M := option) (n := n))
    memory_instruction_encoding.
Proof.
  intros m bound input prefix suffix be Bytes Enc.
  destruct Enc as
    [opcode make body marg Member Body
    |body be Vector
    |
    |
    |header data x Header Data
    |header data x Header Data
    |header Header
    |header Header].
  - eapply memory_scalar_choice_complete; [exact Member |exact Bytes |].
    exists body, marg; auto.
  - assert (Complete : parser_complete (parse_memory_instruction (n := n))
      (fun bytes be => exists body, bytes = xfd :: body /\ vector_memory_encoding body be)).
    { assert (Head : forall bytes be, (exists body,
        bytes = xfd :: body /\ vector_memory_encoding body be) ->
        exists body, bytes = xfd :: body).
      { intros bytes value [tail [E _]]; exists tail; auto. }
      pose proof (parse_vector_memory_complete n) as Complete.
      unfold parse_vector_memory_instruction in Complete.
      unfold_memory_parsers; memory_byte_dispatch xfd Complete Head. }
    eapply Complete; [exact Bytes |exists body; auto].
  - eapply memory_reserved_complete; [left; auto |exact Bytes |auto].
  - eapply memory_reserved_complete; [right; auto |exact Bytes |auto].
  - eapply memory_init_complete; [exact Bytes |].
    exists header, (data ++ x00 :: nil); split; [reflexivity |].
    split; [exact Header |exists data, x; auto].
  - eapply memory_drop_complete; [exact Bytes |].
    exists header, data; split; [reflexivity |].
    split; [exact Header |exists x; auto].
  - eapply memory_copy_complete; [exact Bytes |].
    exists header, (x00 :: x00 :: nil); auto.
  - eapply memory_fill_complete; [exact Bytes |].
    exists header, (x00 :: nil); auto.
Qed.

Theorem run_parse_memory_instruction_correct bytes be rest :
  run_parse_prefix (fun n => parse_memory_instruction (n := n)) bytes = Some (be, rest) <->
  exists prefix, bytes = prefix ++ rest /\ memory_instruction_encoding prefix be.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_memory_instruction_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_memory_instruction_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest be Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (be, rest)).
    now rewrite Value, Rest.
Qed.
