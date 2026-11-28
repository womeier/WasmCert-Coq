(** Encoding membership of the actual production printer.  Domains below
    constrain AST fields, not parser executions or printed-byte membership. *)
From Stdlib Require Import List Strings.Byte Arith NArith ZArith Lia.
From compcert Require Import Integers Floats.
From parseque Require Import Parseque.
From Wasm Require Import datatypes numerics bytes common binary_format_parser
  binary_format_printer binary_parser_combinator_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_properties binary_format_dispatch_properties
  binary_format_type_properties binary_format_block_properties
  binary_format_vector_properties binary_format_properties
  binary_memory_properties binary_memory_grammar_properties
  binary_format_primitive_complete leb128_properties
  leb128_printer_properties leb128_unsigned_printer_properties
  binary_format_simd_complete binary_format_value_properties
  binary_locals_printer_properties binary_uleb128_printer gc_types gc_binary.
Close Scope N_scope.
Local Notation byte := Byte.byte.

Definition binary_index_wf x := (x <= 4294967295)%N.
Definition binary_vector_length_wf {A} (xs : list A) :=
  (N.of_nat (length xs) <= 4294967295)%N.

Lemma binary_of_index_encoding x :
  binary_index_wf x -> index_encoding (binary_of_idx x) x.
Proof.
  intro Bound. unfold binary_of_idx, binary_of_u32, binary_of_N.
  split; [apply encode_unsigned_sound |]. split; [exact Bound |].
  apply (encode_unsigned_length_bound 4).
  change (Z.of_N x < 34359738368)%Z.
  unfold binary_index_wf in Bound. lia.
Qed.

Lemma binary_of_verified_index_encoding x :
  binary_index_wf x -> index_encoding (binary_of_u32_verified x) x.
Proof.
  intro Range. destruct (binary_of_u32_verified_encoding x Range) as [E Width].
  repeat split; assumption.
Qed.

Lemma binary_of_vec_encoding {A} (print : A -> list byte) Grammar values :
  Forall (fun value => Grammar (print value) value) values ->
  binary_vector_length_wf values ->
  vector_encoding Grammar (binary_of_vec print values) values.
Proof.
  intros Items Count.
  exists (binary_of_u32_verified (N.of_nat (length values))),
    (concat (List.map print values)).
  split; [reflexivity |].
  destruct (binary_of_verified_index_encoding _ Count) as [E [Range Width]].
  split; [exact E |]. split; [exact Range |]. split; [exact Width |].
  clear Count E Range Width.
  induction Items; simpl; constructor; assumption.
Qed.

Lemma binary_of_value_types_encoding ts :
  Forall printable_local_type ts -> binary_vector_length_wf ts ->
  vector_encoding value_type_encoding (binary_of_value_types ts) ts.
Proof.
  intros Types Count; apply binary_of_vec_encoding; [|exact Count].
  clear Count.
  induction Types; constructor; [now apply binary_of_value_type_encoding |assumption].
Qed.

Lemma binary_of_memory_encoding be :
  encodable_memory_instruction be ->
  binary_memory_instruction (binary_of_be be) be.
Proof.
  intro Wf.
  apply (run_parser_sound (fun n => parse_memory_instruction)
    binary_memory_instruction).
  - exact parse_memory_instruction_binary_sound.
  - now apply memory_instruction_run_round_trip.
Qed.

Lemma binary_of_fixed_numeric_encoding be :
  In be fixed_numeric_instructions ->
  numeric_atomic_encoding (binary_of_be be) be.
Proof.
  assert (All : Forall (fun be =>
    numeric_atomic_encoding (binary_of_be be) be) fixed_numeric_instructions).
  { unfold fixed_numeric_instructions, integer_relops, float_relops,
      integer_unops, integer_binops, float_unops, float_binops; cbn [List.map List.app].
    repeat (apply Forall_cons;
      [cbn [binary_of_be]; apply numeric_fixed; [cbn; lia |reflexivity] |]).
    constructor. }
  exact ((proj1 (List.Forall_forall _ _)) All be).
Qed.

Lemma binary_of_saturating_encoding be :
  In be saturating_instructions ->
  numeric_atomic_encoding (binary_of_be be) be.
Proof.
  assert (All : Forall (fun be =>
    numeric_atomic_encoding (binary_of_be be) be) saturating_instructions).
  { unfold saturating_instructions.
    repeat (apply Forall_cons;
      [cbn [binary_of_be];
       lazymatch goal with
       | |- numeric_atomic_encoding (xfc :: ?tag :: nil) ?be =>
       apply (numeric_sat (xfc :: tag :: nil) (Byte.to_N tag) be)
       end;
       [unfold bulk_prefix; eexists; split; [reflexivity |];
        split; [apply uleb_end; cbn; lia |split; cbn; lia]
       |reflexivity] |]).
    constructor. }
  exact ((proj1 (List.Forall_forall _ _)) All be).
Qed.

Lemma binary_of_i32_encoding v :
  signed_leb (binary_of_i32 v) (Wasm_int.Int32.signed v) /\
  length (binary_of_i32 v) <= 5.
Proof.
  unfold binary_of_i32; split; [apply encode_signed_sound |].
  apply (encode_signed_length_bound 4).
  change (-17179869184 <= Wasm_int.Int32.signed v < 17179869184)%Z.
  pose proof (Wasm_int.Int32.signed_range v) as Range.
  change (-2147483648 <= Wasm_int.Int32.signed v <= 2147483647)%Z in Range.
  lia.
Qed.

Lemma binary_of_i64_encoding v :
  signed_leb (binary_of_i64 v) (Wasm_int.Int64.signed v) /\
  length (binary_of_i64 v) <= 10.
Proof.
  unfold binary_of_i64; split; [apply encode_signed_sound |].
  apply (encode_signed_length_bound 9).
  change (-590295810358705651712 <= Wasm_int.Int64.signed v <
    590295810358705651712)%Z.
  pose proof (Wasm_int.Int64.signed_range v) as Range.
  change (-9223372036854775808 <= Wasm_int.Int64.signed v <=
    9223372036854775807)%Z in Range. lia.
Qed.

Lemma compcert_bytes_roundtrip bs :
  List.map compcert_byte_of_byte (List.map byte_of_compcert_byte bs) = bs.
Proof.
  rewrite List.map_map.
  induction bs; simpl; [reflexivity |].
  now rewrite compcert_byte_roundtrip, IHbs.
Qed.

Lemma binary_of_f32_encoding v :
  f32_from_bytes (binary_of_f32 v) = v /\ length (binary_of_f32 v) = 4.
Proof.
  unfold binary_of_f32.
  split; [|rewrite length_map; apply Memdata.encode_int_length].
  unfold f32_from_bytes; rewrite compcert_bytes_roundtrip.
  unfold serialise_f32; rewrite Memdata.decode_encode_int.
  change (Float32.of_bits
    (Int.repr (Int.unsigned (Float32.to_bits v) mod Int.modulus)) = v).
  rewrite Z.mod_small by apply Int.unsigned_range.
  rewrite Int.repr_unsigned. apply Float32.of_to_bits.
Qed.

Lemma binary_of_f64_encoding v :
  f64_from_bytes (binary_of_f64 v) = v /\ length (binary_of_f64 v) = 8.
Proof.
  unfold binary_of_f64.
  split; [|rewrite length_map; apply Memdata.encode_int_length].
  unfold f64_from_bytes; rewrite compcert_bytes_roundtrip.
  unfold serialise_f64; rewrite Memdata.decode_encode_int.
  change (Float.of_bits
    (Int64.repr (Int64.unsigned (Float.to_bits v) mod Int64.modulus)) = v).
  rewrite Z.mod_small by apply Int64.unsigned_range.
  rewrite Int64.repr_unsigned. apply Float.of_to_bits.
Qed.

Lemma binary_of_const_num_encoding v :
  numeric_atomic_encoding (binary_of_be (BI_const_num v)) (BI_const_num v).
Proof.
  destruct v; cbn [binary_of_be].
  - apply numeric_i32; apply binary_of_i32_encoding.
  - apply numeric_i64; apply binary_of_i64_encoding.
  - destruct (binary_of_f32_encoding f) as [Value Width].
    rewrite <- Value at 2. now apply numeric_f32.
  - destruct (binary_of_f64_encoding f) as [Value Width].
    rewrite <- Value at 2. now apply numeric_f64.
Qed.

Lemma fixed_control_print opcode be :
  In (opcode, be) fixed_control_opcodes ->
  binary_of_be be = opcode :: nil.
Proof.
  intro Member; unfold fixed_control_opcodes in Member; cbn [In] in Member.
  repeat match type of Member with _ \/ _ => destruct Member as [Member|Member] end;
    try contradiction; inversion Member; reflexivity.
Qed.

Lemma single_index_print opcode make x :
  In (opcode, make) single_index_opcodes ->
  binary_index_wf x ->
  exists bytes, binary_of_be (make x) = opcode :: bytes /\ index_encoding bytes x.
Proof.
  intros Member Range; unfold single_index_opcodes in Member; cbn [In] in Member.
  repeat match type of Member with _ \/ _ => destruct Member as [Member|Member] end;
    try contradiction; inversion Member; subst;
    first [exists (binary_of_u32_verified x); split;
      [reflexivity |now apply binary_of_verified_index_encoding]
    |exists (binary_of_idx x); split; [reflexivity |now apply binary_of_index_encoding]].
Qed.

Lemma bulk_single_print code make x :
  In (code, make) bulk_single_index_opcodes ->
  binary_of_be (make x) = xfc :: binary_of_idx code ++ binary_of_idx x.
Proof.
  intro Member; unfold bulk_single_index_opcodes in Member; cbn [In] in Member.
  repeat match type of Member with _ \/ _ => destruct Member as [Member|Member] end;
    try contradiction; inversion Member; reflexivity.
Qed.

Lemma bulk_two_print code make x y :
  In (code, make) bulk_two_index_opcodes ->
  binary_of_be (make x y) =
    xfc :: binary_of_idx code ++ binary_of_idx x ++ binary_of_idx y.
Proof.
  intro Member; unfold bulk_two_index_opcodes in Member; cbn [In] in Member.
  repeat match type of Member with _ \/ _ => destruct Member as [Member|Member] end;
    try contradiction; inversion Member; reflexivity.
Qed.

(** Wire-encodability domain, deliberately distinct from validation:
    oversized but representable alignments may still be invalid Wasm.
     The shared final memory domain requires offset < 2^64, memory
    index < 2^32, alignment < 64, and raw lane index < 256. *)
Inductive atomic_binary_wf : basic_instruction -> Prop :=
| ABW_fixed : forall opcode be,
    In (opcode, be) fixed_control_opcodes -> atomic_binary_wf be
| ABW_index : forall opcode make x,
    In (opcode, make) single_index_opcodes -> binary_index_wf x ->
    atomic_binary_wf (make x)
| ABW_call_indirect : forall tab typ,
    binary_index_wf tab -> binary_index_wf typ ->
    atomic_binary_wf (BI_call_indirect tab typ)
| ABW_return_call_indirect : forall tab typ,
    binary_index_wf tab -> binary_index_wf typ ->
    atomic_binary_wf (BI_return_call_indirect tab typ)
| ABW_br_table : forall labels fallback,
    Forall binary_index_wf labels -> binary_vector_length_wf labels ->
    binary_index_wf fallback -> atomic_binary_wf (BI_br_table labels fallback)
| ABW_ref_null : forall abstract,
    atomic_binary_wf (BI_ref_null (shared_heap_of_abstract abstract))
| ABW_select : forall ts,
    Forall printable_local_type ts -> binary_vector_length_wf ts ->
    atomic_binary_wf (BI_select (Some ts))
| ABW_bulk_single : forall code make x,
    In (code, make) bulk_single_index_opcodes ->
    binary_index_wf code -> binary_index_wf x -> atomic_binary_wf (make x)
| ABW_bulk_two : forall code make x y,
    In (code, make) bulk_two_index_opcodes ->
    binary_index_wf code -> binary_index_wf x -> binary_index_wf y ->
    atomic_binary_wf (make x y)
| ABW_numeric : forall be,
    In be fixed_numeric_instructions -> atomic_binary_wf be
| ABW_saturating : forall be,
    In be saturating_instructions -> atomic_binary_wf be
| ABW_const_num : forall v, atomic_binary_wf (BI_const_num v)
| ABW_const_vec : forall bs,
    length bs = 16 -> atomic_binary_wf (BI_const_vec (VAL_vec128 bs))
| ABW_vunop : forall code,
    opcode_is_unop code = true -> binary_index_wf code ->
    atomic_binary_wf (BI_vunop code)
| ABW_vbinop : forall code,
    opcode_is_binop code = true -> binary_index_wf code ->
    atomic_binary_wf (BI_vbinop (code, nil))
| ABW_vternop : forall code,
    opcode_is_ternop code = true -> binary_index_wf code ->
    atomic_binary_wf (BI_vternop code)
| ABW_vtestop : forall code,
    opcode_is_testop code = true -> binary_index_wf code ->
    atomic_binary_wf (BI_vtestop code)
| ABW_vshiftop : forall code,
    opcode_is_shiftop code = true -> binary_index_wf code ->
    atomic_binary_wf (BI_vshiftop code)
| ABW_shuffle : forall lanes,
    length lanes = 16 -> Forall (fun lane => (lane < 32)%N) lanes ->
    atomic_binary_wf (BI_vbinop (13%N, lanes))
| ABW_splat : forall shape, atomic_binary_wf (BI_splat_vec shape)
| ABW_lane : forall code make lane,
    In (code, make) simd_lane_codes -> (lane < 256)%N ->
    atomic_binary_wf (make lane)
| ABW_memory : forall be,
    encodable_memory_instruction be -> atomic_binary_wf be
| ABW_call_ref : forall x, binary_index_wf x -> atomic_binary_wf (BI_call_ref x)
| ABW_return_call_ref : forall x, binary_index_wf x -> atomic_binary_wf (BI_return_call_ref x)
| ABW_br_on_null : forall x, binary_index_wf x -> atomic_binary_wf (BI_br_on_null x)
| ABW_br_on_non_null : forall x, binary_index_wf x -> atomic_binary_wf (BI_br_on_non_null x)
| ABW_ref_as_non_null : atomic_binary_wf BI_ref_as_non_null
| ABW_ref_i31 : atomic_binary_wf BI_ref_i31
| ABW_i31_get : forall sign, atomic_binary_wf (BI_i31_get sign).

Lemma binary_of_laneidx_encoding lane :
  (lane < 256)%N ->
  exists b, binary_of_laneidx lane = b :: nil /\ Byte.to_N b = lane.
Proof.
  intro Range; unfold binary_of_laneidx.
  destruct (Byte.of_N lane) as [b|] eqn:E.
  - exists b; split; [reflexivity |now apply Byte.to_of_N in E].
  - apply Byte.of_N_None_iff in E; lia.
Qed.

Lemma binary_of_shuffle_lanes lanes :
  Forall (fun lane => (lane < 32)%N) lanes ->
  exists raw, concat (List.map binary_of_laneidx lanes) = raw /\
    List.map Byte.to_N raw = lanes /\ length raw = length lanes.
Proof.
  intro Wf; induction Wf as [|lane lanes Range Wf [raw [Bytes [Values Count]]]].
  - exists nil; auto.
  - destruct (binary_of_laneidx_encoding lane ltac:(lia)) as [b [Byte Value]].
    exists (b :: raw); simpl.
    rewrite Byte, Bytes, Value, Values; auto.
Qed.

Lemma binary_of_lane_instruction code make lane :
  In (code, make) simd_lane_codes ->
  binary_of_be (make lane) =
    xfd :: binary_of_idx code ++ binary_of_laneidx lane.
Proof.
  intro Member; unfold simd_lane_codes in Member; cbn [In] in Member.
  repeat match type of Member with _ \/ _ => destruct Member as [Member|Member] end;
    try contradiction; inversion Member; reflexivity.
Qed.

Theorem binary_of_atomic_encoding be :
  atomic_binary_wf be -> wasm_atomic_encoding (binary_of_be be) be.
Proof.
  intro Wf; destruct Wf.
  - left. rewrite (fixed_control_print _ _ H). now apply control_fixed.
  - left. destruct (single_index_print _ _ x H H0) as [bytes [Bytes Encoding]].
    rewrite Bytes. now apply control_index.
  - left; cbn [binary_of_be].
    apply control_call_indirect; now apply binary_of_index_encoding.
  - left; cbn [binary_of_be].
    apply control_return_call_indirect; now apply binary_of_verified_index_encoding.
  - left; cbn [binary_of_be].
    apply control_br_table.
    + apply binary_of_vec_encoding; [|exact H0].
      clear H0.
      induction H; constructor; [now apply binary_of_index_encoding |assumption].
    + now apply binary_of_index_encoding.
  - left; apply control_ref_null.
    exists (encode_abstract_heap abstract), abstract.
    destruct abstract; repeat split; try reflexivity; constructor.
  - left; cbn [binary_of_be].
    apply control_select_typed; now apply binary_of_value_types_encoding.
  - right; left. rewrite (bulk_single_print _ _ x H).
    change (bulk_atomic_encoding
      ((xfc :: binary_of_idx code) ++ binary_of_idx x) (make x)).
    eapply bulk_single; [exact H | |now apply binary_of_index_encoding].
    exists (binary_of_idx code); split; [reflexivity |].
    now apply binary_of_index_encoding.
  - right; left. rewrite (bulk_two_print _ _ x y H).
    change (bulk_atomic_encoding
      ((xfc :: binary_of_idx code) ++ (binary_of_idx x ++ binary_of_idx y)) (make x y)).
    eapply bulk_two; [exact H | |now apply binary_of_index_encoding |
      now apply binary_of_index_encoding].
    exists (binary_of_idx code); split; [reflexivity |].
    now apply binary_of_index_encoding.
  - right; right; left; now apply binary_of_fixed_numeric_encoding.
  - right; right; left; now apply binary_of_saturating_encoding.
  - right; right; left; apply binary_of_const_num_encoding.
  - right; right; left; cbn [binary_of_be binary_of_valvec].
    rewrite <- (compcert_bytes_roundtrip bs) at 2.
    change (numeric_atomic_encoding
      (xfd :: binary_of_idx 12%N ++ List.map byte_of_compcert_byte bs)
      (BI_const_vec (VAL_vec128
        (List.map compcert_byte_of_byte (List.map byte_of_compcert_byte bs))))).
    apply numeric_v128.
    + apply binary_of_index_encoding; unfold binary_index_wf; lia.
    + now rewrite length_map.
  - right; right; left; cbn [binary_of_be binary_of_vunop].
    apply numeric_simd; apply simd_unop_encoding;
      [now apply binary_of_index_encoding |exact H].
  - right; right; left; cbn [binary_of_be binary_of_vbinop].
    assert (NotShuffle : N.eqb code 13 = false).
    { apply N.eqb_neq; intro E; subst code; discriminate. }
    rewrite NotShuffle. apply numeric_simd; apply simd_binop_encoding;
      [now apply binary_of_index_encoding |exact H].
  - right; right; left; cbn [binary_of_be binary_of_vternop].
    apply numeric_simd; apply simd_ternop_encoding;
      [now apply binary_of_index_encoding |exact H].
  - right; right; left; cbn [binary_of_be binary_of_vtestop].
    apply numeric_simd; apply simd_testop_encoding;
      [now apply binary_of_index_encoding |exact H].
  - right; right; left; cbn [binary_of_be binary_of_vshiftop].
    apply numeric_simd; apply simd_shiftop_encoding;
      [now apply binary_of_index_encoding |exact H].
  - right; right; left; cbn [binary_of_be binary_of_vbinop].
    destruct (binary_of_shuffle_lanes lanes H0) as [raw [Bytes [Values Count]]].
    rewrite Bytes, <- Values.
    change (numeric_atomic_encoding
      (xfd :: binary_of_idx 13%N ++ raw)
      (BI_vbinop (13%N, List.map Byte.to_N raw))).
    apply numeric_simd; apply simd_shuffle_encoding.
    + apply binary_of_index_encoding; unfold binary_index_wf; lia.
    + lia.
  - { right; right; left; destruct shape as [i|f]; [destruct i|destruct f];
      cbn [binary_of_be binary_of_splat_vec];
      apply numeric_simd;
      lazymatch goal with
      | |- simd_numeric_encoding (?tag :: nil) (BI_splat_vec ?sh) =>
        apply (simd_splat_encoding (tag :: nil) (Byte.to_N tag) sh)
      end.
      all: first
        [split; [apply uleb_end; cbn; lia |split; cbn; lia]
        |unfold simd_splat_codes; simpl; tauto]. }
  - right; right; left.
    rewrite (binary_of_lane_instruction code make lane H).
    destruct (binary_of_laneidx_encoding lane H0) as [b [Bytes Value]].
    rewrite Bytes, <- Value.
    apply numeric_simd; apply (simd_lane_encoding (binary_of_idx code) code make b);
      [|exact H].
    apply binary_of_index_encoding.
    pose proof (simd_lane_code_bound code make H).
    unfold binary_index_wf; lia.
  - right; right; right; now apply binary_of_memory_encoding.
  - left; apply control_extended. cbn [binary_of_be].
    apply extended_index; [simpl; auto |now apply binary_of_index_encoding].
  - left; apply control_extended. cbn [binary_of_be].
    apply extended_index; [simpl; auto |now apply binary_of_index_encoding].
  - left; apply control_extended. cbn [binary_of_be].
    apply extended_index; [simpl; auto |now apply binary_of_index_encoding].
  - left; apply control_extended. cbn [binary_of_be].
    apply extended_index; [simpl; auto |now apply binary_of_index_encoding].
  - left; apply control_extended. constructor.
  - left; apply control_extended.
    change (extended_reference_encoding
      (xfb :: binary_of_idx 28%N) BI_ref_i31).
    eapply extended_gc with (code := 28%N); [simpl; auto |].
    apply binary_of_index_encoding. unfold binary_index_wf; lia.
  - left; apply control_extended. destruct sign.
    + change (extended_reference_encoding
        (xfb :: binary_of_idx 29%N) (BI_i31_get SX_S)).
      eapply extended_gc with (code := 29%N); [simpl; auto |].
      apply binary_of_index_encoding. unfold binary_index_wf; lia.
    + change (extended_reference_encoding
        (xfb :: binary_of_idx 30%N) (BI_i31_get SX_U)).
      eapply extended_gc with (code := 30%N); [simpl; auto |].
      apply binary_of_index_encoding. unfold binary_index_wf; lia.
Qed.
