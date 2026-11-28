(** Exact-suffix correspondence for the production SIMD MEMORY dispatcher.
    No relaxed SIMD, recursive language, or new decoder is defined here.
    Format-valid lane bytes and semantically valid lane numbers are separate:
    an out-of-range lane byte must still reach validation, not be truncated. *)
From Stdlib Require Import List NArith Lia Strings.Byte Arith.PeanoNat.
From parseque Require Import Parseque.
From Wasm Require Import datatypes operations
  binary_format_parser binary_format_printer binary_format_parser_properties
  binary_parser_combinator_properties binary_format_addressing_instructions.
Open Scope list_scope.

Definition simd_body_encoding code
    (P : list Byte.byte -> basic_instruction -> Prop) bs be : Prop :=
  exists payload, bs = binary_of_u32 code ++ payload /\ P payload be.

Lemma production_simd_dispatch_complete code n P :
  (code < 4294967296)%N ->
  parser_complete
    (parse_vector_memory_tail (Toks := SizedList Byte.byte) (M := option) (n := n) code) P ->
  parser_complete
    ((parse_u32_as_N >>= (fun actual => parse_vector_memory_tail actual)) :
      Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
    (simd_body_encoding code P).
Proof.
  intros Range Complete.
  eapply parser_complete_bind with
    (P := fun bs actual => bs = binary_of_u32 code /\ actual = code)
    (Q := fun actual bs be => actual = code /\ P bs be).
  - eapply parser_complete_weaken; [apply production_u32_printed_complete |].
    intros bs actual [Bytes ->]. split; [exact Range |exact Bytes].
  - intros actual k lt; simpl.
    intros m bound input prefix suffix be Bytes [Value Encoding]. subst actual.
    eapply parser_complete_le_lower; [exact Complete |exact Bytes |exact Encoding].
  - intros bs be [payload [Bytes Encoding]].
    exists (binary_of_u32 code), payload, code. auto.
Qed.

Definition rejects_simd_subopcode n
    (p : Parser (SizedList Byte.byte) Byte.byte option basic_instruction n) code : Prop :=
  forall m (bound : m <= n) input suffix,
    input_bytes input = binary_of_u32 code ++ suffix ->
    runParser p bound input = None.

Lemma production_wrong_subopcode_fails expected actual m n
    (bound : m <= n) (input : SizedList Byte.byte m) suffix :
  (actual < 4294967296)%N ->
  actual <> expected ->
  input_bytes input = binary_of_u32 actual ++ suffix ->
  runParser (assert_u32 expected) bound input = None.
Proof.
  intros Range Different Input.
  destruct (production_u32_printed_complete n m bound input
    (binary_of_u32 actual) suffix actual Input (conj Range eq_refl))
    as [result [Parsed [Value Rest]]].
  unfold assert_u32.
  rewrite run_guardM_option, Parsed.
  unfold Success.guardM. rewrite Value.
  assert (Mismatch : N.eqb actual expected = false) by (now apply N.eqb_neq).
  now rewrite Mismatch.
Qed.

Lemma production_prefix_fails {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : Parser (SizedList Byte.byte) Byte.byte option B n)
    m (bound : m <= n) input :
  runParser p bound input = None ->
  runParser (p &> q) bound input = None.
Proof.
  intro Failed.
  change (runParser (Combinators.bind p (fun _ => box q)) bound input = None).
  unfold Combinators.bind, Combinators.map, Combinators.andbind; simpl.
  now rewrite Failed.
Qed.

Lemma production_rejects_subopcode expected actual n
    (p : Parser (SizedList Byte.byte) Byte.byte option basic_instruction n) :
  (actual < 4294967296)%N ->
  actual <> expected ->
  rejects_simd_subopcode n (assert_u32 expected &> p) actual.
Proof.
  intros Range Different m bound input suffix Input.
  apply production_prefix_fails.
  now apply (production_wrong_subopcode_fails expected actual m n bound input suffix).
Qed.

Lemma production_rejects_subopcode_alt n p q actual :
  rejects_simd_subopcode n p actual ->
  rejects_simd_subopcode n q actual ->
  rejects_simd_subopcode n (p <|> q) actual.
Proof.
  intros Left Right m bound input suffix Input.
  rewrite run_alt_option.
  rewrite (Left m bound input suffix Input), (Right m bound input suffix Input).
  reflexivity.
Qed.

Lemma production_simd_alt_right n p q actual P :
  rejects_simd_subopcode n p actual ->
  parser_complete q (simd_body_encoding actual P) ->
  parser_complete (p <|> q) (simd_body_encoding actual P).
Proof.
  intros Reject Complete m bound input prefix suffix be Input Encoding.
  destruct (Complete m bound input prefix suffix be Input Encoding)
    as [result [Parsed Rest]].
  exists result; split; [|exact Rest].
  rewrite run_alt_option.
  destruct Encoding as [payload [Bytes Body]].
  rewrite Bytes, <- app_assoc in Input.
  rewrite (Reject m bound input (payload ++ suffix) Input).
  exact Parsed.
Qed.

Lemma production_simd_assert_complete code n
    (p : Parser (SizedList Byte.byte) Byte.byte option basic_instruction n) P :
  (code < 4294967296)%N ->
  parser_complete p P ->
  parser_complete (assert_u32 code &> p) (simd_body_encoding code P).
Proof.
  intros Range Complete.
  apply production_prefix_complete with (first := code).
  - now apply production_assert_u32_complete.
  - exact Complete.
Qed.

Definition simd_memarg_payload
    (constructor : memarg -> basic_instruction) bs be : Prop :=
  exists marg, address_memarg_bounds marg /\
    bs = binary_of_memarg marg /\ be = constructor marg.

Lemma production_simd_memarg_payload_complete constructor n :
  parser_complete
    (constructor <$> (parse_memarg :
      Parser (SizedList Byte.byte) Byte.byte option memarg n))
    (simd_memarg_payload constructor).
Proof.
  apply production_mapped_immediate_complete.
  apply production_memarg_printed_complete.
Qed.

Lemma production_simd_memarg_framing code constructor n
    (p : Parser (SizedList Byte.byte) Byte.byte option basic_instruction n) :
  (forall marg, binary_of_be (constructor marg) =
    Byte.xfd :: (binary_of_u32 code ++ binary_of_memarg marg)) ->
  parser_complete p (simd_body_encoding code (simd_memarg_payload constructor)) ->
  parser_complete (exact_byte Byte.xfd &> p)
    (fun bs be => exists marg, address_memarg_bounds marg /\
      bs = binary_of_be (constructor marg) /\ be = constructor marg).
Proof.
  intros Printer Complete.
  eapply parser_complete_weaken; [apply production_opcode_complete; exact Complete|].
  intros bs be [marg [Valid [Bytes Value]]].
  rewrite Printer in Bytes.
  exists (binary_of_u32 code ++ binary_of_memarg marg); split; [exact Bytes|].
  exists (binary_of_memarg marg); split; [reflexivity|].
  exists marg; auto.
Qed.

Ltac reject_simd_subopcode :=
  first
    [ apply production_rejects_subopcode_alt;
        [reject_simd_subopcode | reject_simd_subopcode]
    | apply production_rejects_subopcode;
        [vm_compute; reflexivity | discriminate] ].

Ltac complete_simd_memarg_choice :=
  first
    [ solve [apply production_simd_assert_complete;
        [vm_compute; reflexivity | apply production_simd_memarg_payload_complete]]
    | solve [apply parser_complete_alt_left; complete_simd_memarg_choice]
    | eapply production_simd_alt_right;
        [reject_simd_subopcode | complete_simd_memarg_choice] ].

Ltac prove_simd_memarg_codec constructor :=
  let op := eval vm_compute in
    (Byte.to_N (List.hd Byte.x00 (List.tl
      (binary_of_be (constructor (Build_memarg 0%N 0%N 0%N)))))) in
  intro n;
  unfold parse_vector_memory_instruction;
  eapply production_simd_memarg_framing with (code := op);
    [intro marg; reflexivity |
      apply production_simd_dispatch_complete;
        [vm_compute; reflexivity |
         cbn [parse_vector_memory_tail vector_memory_opcode];
         apply production_simd_memarg_payload_complete]].

(** All 13 encodable vector-load shapes and the full vector store, through
    the actual production parse_vector_memory_instruction alternative tree.
    Wrong subopcode branches are proved to fail, not assumed disjoint. *)
Theorem production_simd_memory_memarg_codecs :
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec LVA_none) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_extend (8%N, 8%N) SX_S)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_extend (8%N, 8%N) SX_U)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_extend (16%N, 4%N) SX_S)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_extend (16%N, 4%N) SX_U)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_extend (32%N, 2%N) SX_S)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_extend (32%N, 2%N) SX_U)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_splat 8%N)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_splat 16%N)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_splat 32%N)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_splat 64%N)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_zero 32%N)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec (LVA_zero 64%N)) /\
  memarg_instruction_codec (fun n => parse_vector_memory_instruction) BI_store_vec.
Proof.
  repeat split;
    match goal with
    | |- memarg_instruction_codec _ ?constructor =>
        prove_simd_memarg_codec constructor
    end.
Qed.

Lemma production_laneidx_printed_complete n :
  parser_complete
    (@parse_laneidx (SizedList Byte.byte) _ option _ _ _ n)
    (printed binary_of_laneidx (fun lane => (lane < 256)%N)).
Proof.
  unfold parse_laneidx.
  eapply parser_complete_map; [apply parser_complete_anyTok|].
  intros bs lane [Range Bytes].
  destruct (Byte.of_N lane) as [b|] eqn:Byte.
  - exists b; split.
    + unfold binary_of_laneidx in Bytes. now rewrite Byte in Bytes.
    + symmetry. now apply Byte.to_of_N.
  - apply Byte.of_N_None_iff in Byte. lia.
Qed.

Definition simd_lane_payload
    (constructor : memarg -> laneidx -> basic_instruction) bs be : Prop :=
  exists marg lane, address_memarg_bounds marg /\ (lane < 256)%N /\
    bs = binary_of_memarg marg ++ binary_of_laneidx lane /\
    be = constructor marg lane.

Lemma production_simd_lane_payload_complete constructor n :
  parser_complete
    ((constructor <$> (parse_memarg :
        Parser (SizedList Byte.byte) Byte.byte option memarg n))
      <*> parse_laneidx)
    (simd_lane_payload constructor).
Proof.
  eapply parser_complete_app with
    (P := fun bs f => exists marg,
      address_memarg_bounds marg /\ bs = binary_of_memarg marg /\
      f = constructor marg)
    (Q := printed binary_of_laneidx (fun lane => (lane < 256)%N)).
  - apply production_mapped_immediate_complete.
    apply production_memarg_printed_complete.
  - intros k lt. simpl. apply parser_complete_le_lower.
    apply production_laneidx_printed_complete.
  - intros bs be [marg [lane [Bounds [Lane [Bytes Value]]]]].
    exists (binary_of_memarg marg), (binary_of_laneidx lane), (constructor marg), lane.
    split; [exact Bytes|].
    split; [exists marg; auto|].
    split; [split; auto|exact Value].
Qed.

Definition simd_lane_instruction_codec (p : production_be_parser)
    (constructor : memarg -> laneidx -> basic_instruction) : Prop :=
  forall n, parser_complete (p n)
    (fun bs be => exists marg lane,
      address_memarg_bounds marg /\ (lane < 256)%N /\
      bs = binary_of_be (constructor marg lane) /\ be = constructor marg lane).

Lemma production_simd_lane_framing code constructor n
    (p : Parser (SizedList Byte.byte) Byte.byte option basic_instruction n) :
  (forall marg lane, binary_of_be (constructor marg lane) =
    Byte.xfd :: (binary_of_u32 code ++
      (binary_of_memarg marg ++ binary_of_laneidx lane))) ->
  parser_complete p (simd_body_encoding code (simd_lane_payload constructor)) ->
  parser_complete (exact_byte Byte.xfd &> p)
    (fun bs be => exists marg lane,
      address_memarg_bounds marg /\ (lane < 256)%N /\
      bs = binary_of_be (constructor marg lane) /\ be = constructor marg lane).
Proof.
  intros Printer Complete.
  eapply parser_complete_weaken; [apply production_opcode_complete; exact Complete|].
  intros bs be [marg [lane [Bounds [Lane [Bytes Value]]]]].
  rewrite Printer in Bytes.
  exists (binary_of_u32 code ++ (binary_of_memarg marg ++ binary_of_laneidx lane)).
  split; [exact Bytes|].
  exists (binary_of_memarg marg ++ binary_of_laneidx lane); split; [reflexivity|].
  exists marg, lane; auto.
Qed.

Ltac complete_simd_lane_choice :=
  first
    [ solve [apply production_simd_assert_complete;
        [vm_compute; reflexivity | apply production_simd_lane_payload_complete]]
    | solve [apply parser_complete_alt_left; complete_simd_lane_choice]
    | eapply production_simd_alt_right;
        [reject_simd_subopcode | complete_simd_lane_choice] ].

Ltac prove_simd_lane_codec constructor :=
  let op := eval vm_compute in
    (Byte.to_N (List.hd Byte.x00 (List.tl
      (binary_of_be (constructor (Build_memarg 0%N 0%N 0%N) 0%N))))) in
  intro n;
  unfold parse_vector_memory_instruction;
  eapply production_simd_lane_framing with (code := op);
    [intros marg lane; reflexivity |
      apply production_simd_dispatch_complete;
        [vm_compute; reflexivity |
         cbn [parse_vector_memory_tail vector_memory_opcode];
         apply production_simd_lane_payload_complete]].

(** A laneidx is one binary byte. This theorem intentionally includes
    format-valid but semantically out-of-range lanes, which must parse and
    subsequently fail validation rather than be silently changed. *)
Theorem production_simd_memory_lane_codecs :
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec_lane 8%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec_lane 16%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec_lane 32%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_load_vec_lane 64%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_store_vec_lane 8%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_store_vec_lane 16%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_store_vec_lane 32%N) /\
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
    (BI_store_vec_lane 64%N).
Proof.
  repeat split;
    match goal with
    | |- simd_lane_instruction_codec _ ?constructor =>
        prove_simd_lane_codec constructor
    end.
Qed.

Definition simd_lane_width (width : N) : Prop :=
  width = 8%N \/ width = 16%N \/ width = 32%N \/ width = 64%N.

Lemma semantically_valid_simd_lane_is_a_byte width lane :
  simd_lane_width width -> (lane < 128 / width)%N -> (lane < 256)%N.
Proof.
  intros [Width|[Width|[Width|Width]]] Lane; subst width; cbn in Lane; lia.
Qed.

Definition semantically_valid_lane_codec (p : production_be_parser)
    (constructor : N -> memarg -> laneidx -> basic_instruction) width : Prop :=
  forall n, parser_complete (p n)
    (fun bs be => exists marg lane,
      address_memarg_bounds marg /\ (lane < 128 / width)%N /\
      bs = binary_of_be (constructor width marg lane) /\
      be = constructor width marg lane).

Theorem production_simd_memory_valid_lane_codecs width :
  simd_lane_width width ->
  semantically_valid_lane_codec (fun n => parse_vector_memory_instruction)
    BI_load_vec_lane width /\
  semantically_valid_lane_codec (fun n => parse_vector_memory_instruction)
    BI_store_vec_lane width.
Proof.
  intro Width.
  destruct production_simd_memory_lane_codecs
    as [L8 [L16 [L32 [L64 [S8 [S16 [S32 S64]]]]]]].
  assert (Weaken : forall constructor,
    simd_lane_instruction_codec (fun n => parse_vector_memory_instruction)
      (constructor width) ->
    semantically_valid_lane_codec (fun n => parse_vector_memory_instruction)
      constructor width).
  { intros constructor Complete n.
    eapply parser_complete_weaken; [apply Complete|].
    intros bs be [marg [lane [Bounds [Lane [Bytes Value]]]]].
    exists marg, lane; split; [exact Bounds|].
    split.
    - now apply (semantically_valid_simd_lane_is_a_byte width lane Width).
    - split; assumption. }
  destruct Width as [Width|[Width|[Width|Width]]]; subst width;
    split; apply Weaken; assumption.
Qed.

Definition run_simd_memory_prefix input : option (basic_instruction * list Byte.byte) :=
  option_map (fun result => (Success.value result, output_bytes result))
    (runParser
      (@parse_vector_memory_instruction (SizedList Byte.byte) _ option _ _ _ _ _ _
        (List.length input))
      (Nat.le_refl _) (mkSizedList input)).

Lemma production_memarg_codec_prefix_roundtrip constructor :
  memarg_instruction_codec (fun n => parse_vector_memory_instruction) constructor ->
  forall marg suffix,
    address_memarg_bounds marg ->
    run_simd_memory_prefix (binary_of_be (constructor marg) ++ suffix) =
      Some (constructor marg, suffix).
Proof.
  intros Complete marg suffix Bounds.
  specialize (Complete _ _ (Nat.le_refl _)
    (mkSizedList (binary_of_be (constructor marg) ++ suffix))
    (binary_of_be (constructor marg)) suffix (constructor marg) eq_refl).
  destruct Complete as [result [Parsed [Value Rest]]].
  - exists marg; auto.
  - unfold run_simd_memory_prefix. rewrite Parsed; cbn.
    now rewrite Value, Rest.
Qed.

Lemma production_lane_codec_prefix_roundtrip constructor :
  simd_lane_instruction_codec (fun n => parse_vector_memory_instruction) constructor ->
  forall marg lane suffix,
    address_memarg_bounds marg -> (lane < 256)%N ->
    run_simd_memory_prefix (binary_of_be (constructor marg lane) ++ suffix) =
      Some (constructor marg lane, suffix).
Proof.
  intros Complete marg lane suffix Bounds Lane.
  specialize (Complete _ _ (Nat.le_refl _)
    (mkSizedList (binary_of_be (constructor marg lane) ++ suffix))
    (binary_of_be (constructor marg lane)) suffix (constructor marg lane) eq_refl).
  destruct Complete as [result [Parsed [Value Rest]]].
  - exists marg, lane; auto.
  - unfold run_simd_memory_prefix. rewrite Parsed; cbn.
    now rewrite Value, Rest.
Qed.

(** These are precisely the load shapes with standard SIMD memory opcodes.
    The other infinitely many inhabitants of the raw LVA AST do not acquire
    a codec merely because the printer has a fallback/dummy branch. *)
Inductive simd_load_shape : load_vec_arg -> Prop :=
| simd_load_full : simd_load_shape LVA_none
| simd_load_extend8 s : simd_load_shape (LVA_extend (8%N, 8%N) s)
| simd_load_extend16 s : simd_load_shape (LVA_extend (16%N, 4%N) s)
| simd_load_extend32 s : simd_load_shape (LVA_extend (32%N, 2%N) s)
| simd_load_splat8 : simd_load_shape (LVA_splat 8%N)
| simd_load_splat16 : simd_load_shape (LVA_splat 16%N)
| simd_load_splat32 : simd_load_shape (LVA_splat 32%N)
| simd_load_splat64 : simd_load_shape (LVA_splat 64%N)
| simd_load_zero32 : simd_load_shape (LVA_zero 32%N)
| simd_load_zero64 : simd_load_shape (LVA_zero 64%N).

Theorem binary_simd_load_printer_parser_roundtrip shape marg suffix :
  simd_load_shape shape ->
  address_memarg_bounds marg ->
  run_simd_memory_prefix (binary_of_be (BI_load_vec shape marg) ++ suffix) =
    Some (BI_load_vec shape marg, suffix).
Proof.
  intros Shape Bounds.
  destruct production_simd_memory_memarg_codecs
    as [Full [E8S [E8U [E16S [E16U [E32S [E32U
      [Sp8 [Sp16 [Sp32 [Sp64 [Z32 [Z64 Store]]]]]]]]]]]]].
  apply production_memarg_codec_prefix_roundtrip; [|exact Bounds].
  destruct Shape; try assumption; destruct s; assumption.
Qed.

Theorem binary_simd_store_printer_parser_roundtrip marg suffix :
  address_memarg_bounds marg ->
  run_simd_memory_prefix (binary_of_be (BI_store_vec marg) ++ suffix) =
    Some (BI_store_vec marg, suffix).
Proof.
  intro Bounds.
  destruct production_simd_memory_memarg_codecs
    as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Store]]]]]]]]]]]]].
  now apply production_memarg_codec_prefix_roundtrip.
Qed.

Theorem binary_simd_lane_printer_parser_roundtrip width marg lane suffix :
  simd_lane_width width ->
  address_memarg_bounds marg -> (lane < 256)%N ->
  run_simd_memory_prefix (binary_of_be (BI_load_vec_lane width marg lane) ++ suffix) =
    Some (BI_load_vec_lane width marg lane, suffix) /\
  run_simd_memory_prefix (binary_of_be (BI_store_vec_lane width marg lane) ++ suffix) =
    Some (BI_store_vec_lane width marg lane, suffix).
Proof.
  intros Width Bounds Lane.
  destruct production_simd_memory_lane_codecs
    as [L8 [L16 [L32 [L64 [S8 [S16 [S32 S64]]]]]]].
  destruct Width as [Width|[Width|[Width|Width]]]; subst width; split;
    apply production_lane_codec_prefix_roundtrip; assumption.
Qed.
