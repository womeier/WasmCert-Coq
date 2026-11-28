(** Numeric opcode byte grammar, including padded unsigned prefix opcodes.
    Core binary/instructions: the contiguous 0x45--0xc4 scalar table, 0xfc
    saturating conversions, and ordinary (not relaxed) 0xfd SIMD. *)
From Stdlib Require Import List Strings.Byte NArith ZArith Lia.
From compcert Require Import Integers Floats.
From parseque Require Import Parseque.
From Wasm Require Import datatypes numerics binary_format_parser
  binary_format_parser_properties binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_vector_properties leb128_properties.
Local Notation byte := Byte.byte.
Open Scope nat_scope.

Definition integer_relops :=
  ROI_eq :: ROI_ne :: ROI_lt SX_S :: ROI_lt SX_U ::
  ROI_gt SX_S :: ROI_gt SX_U :: ROI_le SX_S :: ROI_le SX_U ::
  ROI_ge SX_S :: ROI_ge SX_U :: nil.
Definition float_relops := ROF_eq :: ROF_ne :: ROF_lt :: ROF_gt :: ROF_le :: ROF_ge :: nil.
Definition integer_unops := UOI_clz :: UOI_ctz :: UOI_popcnt :: nil.
Definition integer_binops :=
  BOI_add :: BOI_sub :: BOI_mul :: BOI_div SX_S :: BOI_div SX_U ::
  BOI_rem SX_S :: BOI_rem SX_U :: BOI_and :: BOI_or :: BOI_xor ::
  BOI_shl :: BOI_shr SX_S :: BOI_shr SX_U :: BOI_rotl :: BOI_rotr :: nil.
Definition float_unops :=
  UOF_abs :: UOF_neg :: UOF_ceil :: UOF_floor :: UOF_trunc ::
  UOF_nearest :: UOF_sqrt :: nil.
Definition float_binops :=
  BOF_add :: BOF_sub :: BOF_mul :: BOF_div :: BOF_min :: BOF_max :: BOF_copysign :: nil.

Definition fixed_numeric_instructions : list basic_instruction :=
  (BI_testop T_i32 TO_eqz :: List.map (fun op => BI_relop T_i32 (Relop_i op)) integer_relops) ++
  (BI_testop T_i64 TO_eqz :: List.map (fun op => BI_relop T_i64 (Relop_i op)) integer_relops) ++
  List.map (fun op => BI_relop T_f32 (Relop_f op)) float_relops ++
  List.map (fun op => BI_relop T_f64 (Relop_f op)) float_relops ++
  List.map (fun op => BI_unop T_i32 (Unop_i op)) integer_unops ++
  List.map (fun op => BI_binop T_i32 (Binop_i op)) integer_binops ++
  List.map (fun op => BI_unop T_i64 (Unop_i op)) integer_unops ++
  List.map (fun op => BI_binop T_i64 (Binop_i op)) integer_binops ++
  List.map (fun op => BI_unop T_f32 (Unop_f op)) float_unops ++
  List.map (fun op => BI_binop T_f32 (Binop_f op)) float_binops ++
  List.map (fun op => BI_unop T_f64 (Unop_f op)) float_unops ++
  List.map (fun op => BI_binop T_f64 (Binop_f op)) float_binops ++
  (BI_cvtop T_i32 CVO_wrap T_i64 None ::
   BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_S) ::
   BI_cvtop T_i32 CVO_trunc T_f32 (Some SX_U) ::
   BI_cvtop T_i32 CVO_trunc T_f64 (Some SX_S) ::
   BI_cvtop T_i32 CVO_trunc T_f64 (Some SX_U) ::
   BI_cvtop T_i64 CVO_extend T_i32 (Some SX_S) ::
   BI_cvtop T_i64 CVO_extend T_i32 (Some SX_U) ::
   BI_cvtop T_i64 CVO_trunc T_f32 (Some SX_S) ::
   BI_cvtop T_i64 CVO_trunc T_f32 (Some SX_U) ::
   BI_cvtop T_i64 CVO_trunc T_f64 (Some SX_S) ::
   BI_cvtop T_i64 CVO_trunc T_f64 (Some SX_U) ::
   BI_cvtop T_f32 CVO_convert T_i32 (Some SX_S) ::
   BI_cvtop T_f32 CVO_convert T_i32 (Some SX_U) ::
   BI_cvtop T_f32 CVO_convert T_i64 (Some SX_S) ::
   BI_cvtop T_f32 CVO_convert T_i64 (Some SX_U) ::
   BI_cvtop T_f32 CVO_demote T_f64 None ::
   BI_cvtop T_f64 CVO_convert T_i32 (Some SX_S) ::
   BI_cvtop T_f64 CVO_convert T_i32 (Some SX_U) ::
   BI_cvtop T_f64 CVO_convert T_i64 (Some SX_S) ::
   BI_cvtop T_f64 CVO_convert T_i64 (Some SX_U) ::
   BI_cvtop T_f64 CVO_promote T_f32 None ::
   BI_cvtop T_i32 CVO_reinterpret T_f32 None ::
   BI_cvtop T_i64 CVO_reinterpret T_f64 None ::
   BI_cvtop T_f32 CVO_reinterpret T_i32 None ::
   BI_cvtop T_f64 CVO_reinterpret T_i64 None ::
   BI_unop T_i32 (Unop_extend 8%N) ::
   BI_unop T_i32 (Unop_extend 16%N) ::
   BI_unop T_i64 (Unop_extend 8%N) ::
   BI_unop T_i64 (Unop_extend 16%N) ::
   BI_unop T_i64 (Unop_extend 32%N) :: nil).

Definition saturating_instructions : list basic_instruction :=
  BI_cvtop T_i32 CVO_trunc_sat T_f32 (Some SX_S) ::
  BI_cvtop T_i32 CVO_trunc_sat T_f32 (Some SX_U) ::
  BI_cvtop T_i32 CVO_trunc_sat T_f64 (Some SX_S) ::
  BI_cvtop T_i32 CVO_trunc_sat T_f64 (Some SX_U) ::
  BI_cvtop T_i64 CVO_trunc_sat T_f32 (Some SX_S) ::
  BI_cvtop T_i64 CVO_trunc_sat T_f32 (Some SX_U) ::
  BI_cvtop T_i64 CVO_trunc_sat T_f64 (Some SX_S) ::
  BI_cvtop T_i64 CVO_trunc_sat T_f64 (Some SX_U) :: nil.

Definition f32_from_bytes bs :=
  Floats.Float32.of_bits (Integers.Int.repr
    (common.Memdata.decode_int (List.map compcert_byte_of_byte bs))).
Definition f64_from_bytes bs :=
  Floats.Float.of_bits (Integers.Int64.repr
    (common.Memdata.decode_int (List.map compcert_byte_of_byte bs))).

Definition simd_splat_codes : list (N * vshape) :=
  (15%N, VS_i VSI_8_16) :: (16%N, VS_i VSI_16_8) ::
  (17%N, VS_i VSI_32_4) :: (18%N, VS_i VSI_64_2) ::
  (19%N, VS_f VSF_32_4) :: (20%N, VS_f VSF_64_2) :: nil.

Definition simd_lane_codes : list (N * (laneidx -> basic_instruction)) :=
  (21%N, BI_extract_vec (VS_i VSI_8_16) (Some SX_S)) ::
  (22%N, BI_extract_vec (VS_i VSI_8_16) (Some SX_U)) ::
  (23%N, BI_replace_vec (VS_i VSI_8_16)) ::
  (24%N, BI_extract_vec (VS_i VSI_16_8) (Some SX_S)) ::
  (25%N, BI_extract_vec (VS_i VSI_16_8) (Some SX_U)) ::
  (26%N, BI_replace_vec (VS_i VSI_16_8)) ::
  (27%N, BI_extract_vec (VS_i VSI_32_4) None) ::
  (28%N, BI_replace_vec (VS_i VSI_32_4)) ::
  (29%N, BI_extract_vec (VS_i VSI_64_2) None) ::
  (30%N, BI_replace_vec (VS_i VSI_64_2)) ::
  (31%N, BI_extract_vec (VS_f VSF_32_4) None) ::
  (32%N, BI_replace_vec (VS_f VSF_32_4)) ::
  (33%N, BI_extract_vec (VS_f VSF_64_2) None) ::
  (34%N, BI_replace_vec (VS_f VSF_64_2)) :: nil.

Inductive simd_numeric_encoding : list byte -> basic_instruction -> Prop :=
| simd_unop_encoding : forall bs code,
    index_encoding bs code -> opcode_is_unop code = true ->
    simd_numeric_encoding bs (BI_vunop code)
| simd_binop_encoding : forall bs code,
    index_encoding bs code -> opcode_is_binop code = true ->
    simd_numeric_encoding bs (BI_vbinop (code, nil))
| simd_ternop_encoding : forall bs code,
    index_encoding bs code -> opcode_is_ternop code = true ->
    simd_numeric_encoding bs (BI_vternop code)
| simd_testop_encoding : forall bs code,
    index_encoding bs code -> opcode_is_testop code = true ->
    simd_numeric_encoding bs (BI_vtestop code)
| simd_shiftop_encoding : forall bs code,
    index_encoding bs code -> opcode_is_shiftop code = true ->
    simd_numeric_encoding bs (BI_vshiftop code)
| simd_shuffle_encoding : forall header lanes,
    index_encoding header 13%N -> length lanes = 16 ->
    simd_numeric_encoding (header ++ lanes)
      (BI_vbinop (13%N, List.map Byte.to_N lanes))
| simd_splat_encoding : forall header code shape,
    index_encoding header code -> In (code, shape) simd_splat_codes ->
    simd_numeric_encoding header (BI_splat_vec shape)
| simd_lane_encoding : forall header code make lane,
    index_encoding header code -> In (code, make) simd_lane_codes ->
    simd_numeric_encoding (header ++ (lane :: nil)) (make (Byte.to_N lane)).

Inductive numeric_atomic_encoding : list byte -> basic_instruction -> Prop :=
| numeric_fixed : forall opcode be,
    (69 <= Byte.to_N opcode)%N ->
    nth_error fixed_numeric_instructions (N.to_nat (Byte.to_N opcode) - 69) = Some be ->
    numeric_atomic_encoding (opcode :: nil) be
| numeric_i32 : forall bs v,
    signed_leb bs (Wasm_int.Int32.signed v) -> length bs <= 5 ->
    numeric_atomic_encoding (x41 :: bs) (BI_const_num (VAL_int32 v))
| numeric_i64 : forall bs v,
    signed_leb bs (Wasm_int.Int64.signed v) -> length bs <= 10 ->
    numeric_atomic_encoding (x42 :: bs) (BI_const_num (VAL_int64 v))
| numeric_f32 : forall bs, length bs = 4 ->
    numeric_atomic_encoding (x43 :: bs)
      (BI_const_num (VAL_float32 (f32_from_bytes bs)))
| numeric_f64 : forall bs, length bs = 8 ->
    numeric_atomic_encoding (x44 :: bs)
      (BI_const_num (VAL_float64 (f64_from_bytes bs)))
| numeric_v128 : forall header bs,
    index_encoding header 12%N -> length bs = 16 ->
    numeric_atomic_encoding (xfd :: header ++ bs)
      (BI_const_vec (VAL_vec128 (List.map compcert_byte_of_byte bs)))
| numeric_sat : forall prefix code be,
    bulk_prefix prefix code ->
    nth_error saturating_instructions (N.to_nat code) = Some be ->
    numeric_atomic_encoding prefix be
| numeric_simd : forall bs be,
    simd_numeric_encoding bs be ->
    numeric_atomic_encoding (xfd :: bs) be.

Lemma parser_sound_add_size_bound {A n} p P bound :
  @parser_sound A n p P ->
  (forall m (le : m <= n) input s, runParser p le input = Some s ->
    (N.of_nat (m - Success.size s) <= N.of_nat bound)%N) ->
  parser_sound p (fun bs a => P bs a /\ length bs <= bound).
Proof.
  intros Sound Width m le input s Run.
  destruct (Sound _ _ _ _ Run) as [bs [Bytes Parsed]].
  exists bs; split; [exact Bytes |]. split; [exact Parsed |].
  specialize (Width _ _ _ _ Run).
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes s) = Success.size s) in Lout.
  rewrite Bytes, length_app in Lin. lia.
Qed.

Lemma parse_i32_const_sound n :
  parser_sound (parse_i32_const (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  unfold parse_i32_const.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => exists v,
      signed_leb bs (Wasm_int.Int32.signed v) /\ length bs <= 5 /\
      be = BI_const_num (VAL_int32 v)).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map.
    + apply (parser_sound_add_size_bound _
        (fun bs v => signed_leb bs (Wasm_int.Int32.signed v)) 5).
      * apply parse_s32_prefix_sound.
      * intros m le input s Run.
        destruct (parse_s32_guards le input s Run) as [z [_ [_ [_ Width]]]].
        exact Width.
    + intros bs v [E Width]; exists v; auto.
  - intros bs be [v [E [Width Value]]]; subst.
    now apply numeric_i32.
Qed.

Lemma parse_i64_const_sound n :
  parser_sound (parse_i64_const (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  unfold parse_i64_const.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => exists v,
      signed_leb bs (Wasm_int.Int64.signed v) /\ length bs <= 10 /\
      be = BI_const_num (VAL_int64 v)).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map.
    + apply (parser_sound_add_size_bound _
        (fun bs v => signed_leb bs (Wasm_int.Int64.signed v)) 10).
      * apply parse_s64_prefix_sound.
      * intros m le input s Run.
        destruct (parse_s64_guards le input s Run) as [z [_ [_ [_ Width]]]].
        exact Width.
    + intros bs v [E Width]; exists v; auto.
  - intros bs be [v [E [Width Value]]]; subst.
    now apply numeric_i64.
Qed.

Lemma parse_f32_const_sound n :
  parser_sound (parse_f32_const (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  unfold parse_f32_const.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => length bs = 4 /\
      be = BI_const_num (VAL_float32 (f32_from_bytes bs))).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map with
      (P := fun bs v => length bs = 4 /\ v = f32_from_bytes bs).
    + unfold parse_f32. eapply parser_sound_map; [apply parse_raw_bytes_sound |].
      intros bs values [Bytes Count]. subst values.
      split; [lia |reflexivity].
    + intros bs v [Count Value]; subst v. auto.
  - intros bs be [Count Value]; subst be. now apply numeric_f32.
Qed.

Lemma parse_f64_const_sound n :
  parser_sound (parse_f64_const (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  unfold parse_f64_const.
  apply parser_sound_prefix_byte with
    (Q := fun bs be => length bs = 8 /\
      be = BI_const_num (VAL_float64 (f64_from_bytes bs))).
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map with
      (P := fun bs v => length bs = 8 /\ v = f64_from_bytes bs).
    + unfold parse_f64. eapply parser_sound_map; [apply parse_raw_bytes_sound |].
      intros bs values [Bytes Count]. subst values.
      split; [lia |reflexivity].
    + intros bs v [Count Value]; subst v. auto.
  - intros bs be [Count Value]; subst be. now apply numeric_f64.
Qed.

Lemma parse_laneidx_sound n :
  parser_sound (parse_laneidx (Toks := SizedList byte) (M := option) (n := n))
    (fun bs x => exists b, bs = b :: nil /\ x = Byte.to_N b).
Proof.
  unfold parse_laneidx.
  eapply parser_sound_map; [apply parser_sound_anyTok |].
  intros bs b Bytes. exists b; auto.
Qed.

Lemma guarded_simd_index_sound n classify (make : N -> basic_instruction)
    (R : list byte -> basic_instruction -> Prop) :
  (forall bs code, index_encoding bs code -> classify code = true ->
    R bs (make code)) ->
  parser_sound
    (Combinators.guardM
      (fun code => if classify code then Some (make code) else None)
      (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))) R.
Proof.
  intro Combine. eapply parser_sound_guardM; [apply parse_index_sound |].
  intros bs code be Encoding E.
  destruct (classify code) eqn:Valid; [|discriminate].
  inversion E; subst. now apply Combine.
Qed.

Lemma parse_simd_binop_sound n :
  parser_sound (parse_simd_binop (Toks := SizedList byte) (M := option) (n := n))
    simd_numeric_encoding.
Proof.
  unfold parse_simd_binop. apply parser_sound_alt.
  - eapply parser_sound_rand_grammar with
      (P := fun bs x => index_encoding bs 13%N /\ x = 13%N)
      (Q := fun bs be => length bs = 16 /\
        be = BI_vbinop (13%N, List.map Byte.to_N bs)).
    + apply assert_u32_sound.
    + intros k lt; simpl. apply parser_sound_le_lower.
      eapply parser_sound_map; [apply (parse_raw_bytes_sound n 16%N) |].
      intros bs lanes [Bytes Count]; subst lanes.
      split; [lia |reflexivity].
    + intros header lanes code be [Encoding _] [Count Value]; subst be.
      now apply simd_shuffle_encoding.
  - apply guarded_simd_index_sound.
    intros bs code E Valid. now apply simd_binop_encoding.
Qed.

Lemma simd_splat_instruction_sound n code shape :
  In (code, shape) simd_splat_codes ->
  parser_sound
    (Combinators.cmap (BI_splat_vec shape)
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code))
    simd_numeric_encoding.
Proof.
  intro Opcode.
  eapply parser_sound_cmap; [apply assert_u32_sound |].
  intros bs code' [Encoding _]. eapply simd_splat_encoding; eassumption.
Qed.

Lemma parse_simd_splat_sound n :
  parser_sound (parse_simd_splat (Toks := SizedList byte) (M := option) (n := n))
    simd_numeric_encoding.
Proof.
  unfold parse_simd_splat.
  do 5 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply simd_splat_instruction_sound;
    unfold simd_splat_codes; simpl; tauto.
Qed.

Lemma simd_lane_instruction_sound n code make :
  In (code, make) simd_lane_codes ->
  parser_sound
    (Combinators.rand
      (assert_u32 (Toks := SizedList byte) (M := option) (n := n) code)
      (box (Combinators.map make parse_laneidx)))
    simd_numeric_encoding.
Proof.
  intro Opcode.
  eapply parser_sound_rand_grammar with
    (P := fun bs x => index_encoding bs code /\ x = code)
    (Q := fun bs be => exists lane,
      bs = lane :: nil /\ be = make (Byte.to_N lane)).
  - apply assert_u32_sound.
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map; [apply parse_laneidx_sound |].
    intros bs x [lane [Bytes Value]]; subst. exists lane; auto.
  - intros header lanes x be [Encoding _] [lane [Bytes Value]].
    subst lanes be. eapply simd_lane_encoding; eassumption.
Qed.

Lemma parse_extract_replace_lane_sound n :
  parser_sound
    (parse_extract_replace_lane (Toks := SizedList byte) (M := option) (n := n))
    simd_numeric_encoding.
Proof.
  unfold parse_extract_replace_lane.
  do 13 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: apply simd_lane_instruction_sound;
    unfold simd_lane_codes; simpl; tauto.
Qed.

Lemma parse_simd_instruction_sound n :
  parser_sound
    (parse_simd_instruction (Toks := SizedList byte) (M := option) (n := n))
    simd_numeric_encoding.
Proof.
  unfold parse_simd_instruction.
  apply parser_sound_alt.
  - unfold parse_simd_unop. apply guarded_simd_index_sound.
    intros bs code E Valid; now apply simd_unop_encoding.
  - apply parser_sound_alt; [apply parse_simd_binop_sound |].
    apply parser_sound_alt.
    + unfold parse_simd_ternop. apply guarded_simd_index_sound.
      intros bs code E Valid; now apply simd_ternop_encoding.
    + apply parser_sound_alt.
      * unfold parse_simd_testop. apply guarded_simd_index_sound.
        intros bs code E Valid; now apply simd_testop_encoding.
      * apply parser_sound_alt.
        -- unfold parse_simd_shiftop. apply guarded_simd_index_sound.
           intros bs code E Valid; now apply simd_shiftop_encoding.
        -- apply parser_sound_alt;
             [apply parse_simd_splat_sound |apply parse_extract_replace_lane_sound].
Qed.

Lemma parse_v128_const_sound n :
  parser_sound (parse_v128_const (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  unfold parse_v128_const.
  eapply parser_sound_rand_grammar with
    (P := fun bs _ => exists header,
      bs = xfd :: header /\ index_encoding header 12%N)
    (Q := fun bs be => length bs = 16 /\
      be = BI_const_vec (VAL_vec128 (List.map compcert_byte_of_byte bs))).
  - apply parser_sound_prefix_byte with
      (Q := fun bs x => index_encoding bs 12%N /\ x = 12%N).
    + intros k lt; simpl. apply parser_sound_le_lower; apply assert_u32_sound.
    + intros bs x [E _]; exists bs; auto.
  - intros k lt; simpl. apply parser_sound_le_lower.
    eapply parser_sound_map with
      (P := fun bs v => length bs = 16 /\
        v = List.map compcert_byte_of_byte bs).
    + unfold parse_16bytes.
      eapply parser_sound_map; [apply parse_raw_bytes_sound |].
      intros bs lanes [Bytes Count]; subst lanes.
      split; [lia |reflexivity].
    + intros bs v [Count Value]; subst v; auto.
  - intros prefix bytes code be [header [Prefix Encoding]] [Count Value].
    subst prefix be. simpl. now apply numeric_v128.
Qed.

Lemma fixed_numeric_instruction_sound n opcode be :
  (69 <= Byte.to_N opcode)%N ->
  nth_error fixed_numeric_instructions (N.to_nat (Byte.to_N opcode) - 69) = Some be ->
  parser_sound
    (Combinators.cmap be
      (exact_byte (Toks := SizedList byte) (M := option) (n := n) opcode))
    numeric_atomic_encoding.
Proof.
  intros Lower Opcode.
  eapply parser_sound_cmap; [apply parser_sound_exact_byte |].
  intros bs b [Bytes _]; subst. now apply numeric_fixed.
Qed.

Lemma saturating_instruction_sound n code be :
  nth_error saturating_instructions (N.to_nat code) = Some be ->
  parser_sound
    (Combinators.cmap be
      (Combinators.rand
        (exact_byte (Toks := SizedList byte) (M := option) (n := n) xfc)
        (box (assert_u32 code))))
    numeric_atomic_encoding.
Proof.
  intro Opcode.
  eapply parser_sound_cmap; [apply bulk_prefix_sound |].
  intros bs k Prefix. apply (numeric_sat bs code be Prefix Opcode).
Qed.

Theorem parse_numeric_instruction_sound n :
  parser_sound
    (parse_numeric_instruction (Toks := SizedList byte) (M := option) (n := n))
    numeric_atomic_encoding.
Proof.
  unfold parse_numeric_instruction.
  apply parser_sound_alt; [apply parse_i32_const_sound |].
  apply parser_sound_alt; [apply parse_i64_const_sound |].
  apply parser_sound_alt; [apply parse_f32_const_sound |].
  apply parser_sound_alt; [apply parse_f64_const_sound |].
  apply parser_sound_alt; [apply parse_v128_const_sound |].
  do 128 (apply parser_sound_alt;
    [apply fixed_numeric_instruction_sound;
      [vm_compute; intuition discriminate |vm_compute; reflexivity] |]).
  do 8 (apply parser_sound_alt;
    [apply saturating_instruction_sound; vm_compute; reflexivity |]).
  apply parser_sound_prefix_byte with (Q := simd_numeric_encoding).
  - intros k lt; simpl. apply parser_sound_le_lower.
    apply parse_simd_instruction_sound.
  - intros bs be E; now apply numeric_simd.
Qed.
