(** General codec properties of the actual memory-instruction parsers. *)
From Wasm Require Import binary_codec binary_parser_combinators
  binary_format_parser binary_format_printer binary_format_properties
  datatypes_properties operations.
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.

Definition decode_exact_byte (tag: byte) (input: list byte) :=
  match input with
  | nil => None
  | b :: rest => if Byte.eqb b tag then Some (b, rest) else None
  end.

Lemma byte_eqb_Byte : forall b tag,
  byte_eqb b tag = Byte.eqb b tag.
Proof.
  intros b tag. unfold byte_eqb.
  destruct (Byte.byte_eq_dec b tag) as [Heq|Hneq].
  - subst. symmetry. now apply Byte.byte_dec_lb.
  - destruct (Byte.eqb b tag) eqn:Hb; [|reflexivity].
    apply Byte.byte_dec_bl in Hb. contradiction.
Qed.

Lemma prefix_exact_byte : forall tag,
  prefix_semantics (fun n =>
    (exact_byte tag: Parser (SizedList byte) byte option byte n))
    (decode_exact_byte tag).
Proof.
  intros tag n input Hbound. unfold exact_byte.
  rewrite observe_guardM, (prefix_anyTok n input Hbound).
  destruct input as [|b rest]; [reflexivity|].
  cbn [decode_exact_byte]. rewrite byte_eqb_Byte.
  destruct (Byte.eqb b tag); reflexivity.
Qed.

Definition decode_tagged_memarg (tag: byte) (build: memarg -> basic_instruction)
  (input: list byte) :=
  match decode_exact_byte tag input with
  | Some (_, rest) =>
      option_map (fun '(marg, tail) => (build marg, tail)) (decode_memarg rest)
  | None => None
  end.

Lemma prefix_tagged_memarg : forall tag build,
  prefix_semantics
    (fun n => (exact_byte tag &> (build <$> parse_memarg):
      Parser (SizedList byte) byte option basic_instruction n))
    (decode_tagged_memarg tag build).
Proof.
  intros tag build. unfold decode_tagged_memarg.
  apply prefix_rand; [apply prefix_exact_byte|].
  apply prefix_map. apply parse_memarg_prefix_correct.
Qed.

Lemma decode_tagged_memarg_round_trip : forall tag build marg suffix,
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  decode_tagged_memarg tag build (tag :: binary_of_memarg marg ++ suffix) =
    Some (build marg, suffix).
Proof.
  intros tag build marg suffix Ha Hm Ho.
  unfold decode_tagged_memarg, decode_exact_byte.
  rewrite (Byte.byte_dec_lb (eq_refl tag)).
  rewrite decode_binary_memarg_suffix by assumption. reflexivity.
Qed.

Inductive scalar_memop :=
| SM_i32_load | SM_i64_load | SM_f32_load | SM_f64_load
| SM_i32_load8_s | SM_i32_load8_u | SM_i32_load16_s | SM_i32_load16_u
| SM_i64_load8_s | SM_i64_load8_u | SM_i64_load16_s | SM_i64_load16_u
| SM_i64_load32_s | SM_i64_load32_u
| SM_i32_store | SM_i64_store | SM_f32_store | SM_f64_store
| SM_i32_store8 | SM_i32_store16 | SM_i64_store8 | SM_i64_store16 | SM_i64_store32.

Definition scalar_memop_tag (op: scalar_memop) :=
  match op with
  | SM_i32_load => x28 | SM_i64_load => x29 | SM_f32_load => x2a | SM_f64_load => x2b
  | SM_i32_load8_s => x2c | SM_i32_load8_u => x2d
  | SM_i32_load16_s => x2e | SM_i32_load16_u => x2f
  | SM_i64_load8_s => x30 | SM_i64_load8_u => x31
  | SM_i64_load16_s => x32 | SM_i64_load16_u => x33
  | SM_i64_load32_s => x34 | SM_i64_load32_u => x35
  | SM_i32_store => x36 | SM_i64_store => x37 | SM_f32_store => x38 | SM_f64_store => x39
  | SM_i32_store8 => x3a | SM_i32_store16 => x3b
  | SM_i64_store8 => x3c | SM_i64_store16 => x3d | SM_i64_store32 => x3e
  end.

Definition scalar_memop_build (op: scalar_memop) : memarg -> basic_instruction :=
  match op with
  | SM_i32_load => BI_load T_i32 None | SM_i64_load => BI_load T_i64 None
  | SM_f32_load => BI_load T_f32 None | SM_f64_load => BI_load T_f64 None
  | SM_i32_load8_s => BI_load T_i32 (Some (Tp_i8, SX_S))
  | SM_i32_load8_u => BI_load T_i32 (Some (Tp_i8, SX_U))
  | SM_i32_load16_s => BI_load T_i32 (Some (Tp_i16, SX_S))
  | SM_i32_load16_u => BI_load T_i32 (Some (Tp_i16, SX_U))
  | SM_i64_load8_s => BI_load T_i64 (Some (Tp_i8, SX_S))
  | SM_i64_load8_u => BI_load T_i64 (Some (Tp_i8, SX_U))
  | SM_i64_load16_s => BI_load T_i64 (Some (Tp_i16, SX_S))
  | SM_i64_load16_u => BI_load T_i64 (Some (Tp_i16, SX_U))
  | SM_i64_load32_s => BI_load T_i64 (Some (Tp_i32, SX_S))
  | SM_i64_load32_u => BI_load T_i64 (Some (Tp_i32, SX_U))
  | SM_i32_store => BI_store T_i32 None | SM_i64_store => BI_store T_i64 None
  | SM_f32_store => BI_store T_f32 None | SM_f64_store => BI_store T_f64 None
  | SM_i32_store8 => BI_store T_i32 (Some Tp_i8)
  | SM_i32_store16 => BI_store T_i32 (Some Tp_i16)
  | SM_i64_store8 => BI_store T_i64 (Some Tp_i8)
  | SM_i64_store16 => BI_store T_i64 (Some Tp_i16)
  | SM_i64_store32 => BI_store T_i64 (Some Tp_i32)
  end.

Definition scalar_memop_parser (op: scalar_memop) : byte_parser_family basic_instruction :=
  match op with
  | SM_i32_load => fun n => parse_i32_load | SM_i64_load => fun n => parse_i64_load
  | SM_f32_load => fun n => parse_f32_load | SM_f64_load => fun n => parse_f64_load
  | SM_i32_load8_s => fun n => parse_i32_load8_s | SM_i32_load8_u => fun n => parse_i32_load8_u
  | SM_i32_load16_s => fun n => parse_i32_load16_s | SM_i32_load16_u => fun n => parse_i32_load16_u
  | SM_i64_load8_s => fun n => parse_i64_load8_s | SM_i64_load8_u => fun n => parse_i64_load8_u
  | SM_i64_load16_s => fun n => parse_i64_load16_s | SM_i64_load16_u => fun n => parse_i64_load16_u
  | SM_i64_load32_s => fun n => parse_i64_load32_s | SM_i64_load32_u => fun n => parse_i64_load32_u
  | SM_i32_store => fun n => parse_i32_store | SM_i64_store => fun n => parse_i64_store
  | SM_f32_store => fun n => parse_f32_store | SM_f64_store => fun n => parse_f64_store
  | SM_i32_store8 => fun n => parse_i32_store8 | SM_i32_store16 => fun n => parse_i32_store16
  | SM_i64_store8 => fun n => parse_i64_store8 | SM_i64_store16 => fun n => parse_i64_store16
  | SM_i64_store32 => fun n => parse_i64_store32
  end.

Theorem scalar_memop_prefix_correct : forall op,
  prefix_semantics (scalar_memop_parser op)
    (decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op)).
Proof. intros op. destruct op; apply prefix_tagged_memarg. Qed.

Theorem scalar_memop_prefix_round_trip : forall op marg suffix bound
  (Hbound: (List.length
    (binary_of_be (scalar_memop_build op marg) ++ suffix) <= bound)%nat),
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  observe_prefix (runParser (scalar_memop_parser op bound) Hbound
    (mkSizedList (binary_of_be (scalar_memop_build op marg) ++ suffix))) =
    Some (scalar_memop_build op marg, suffix).
Proof.
  intros op marg suffix bound Hbound Ha Hm Ho.
  rewrite scalar_memop_prefix_correct.
  assert (Hbytes: binary_of_be (scalar_memop_build op marg) =
    scalar_memop_tag op :: binary_of_memarg marg) by (destruct op; reflexivity).
  rewrite Hbytes. now apply decode_tagged_memarg_round_trip.
Qed.

Theorem scalar_memop_run_round_trip : forall op marg,
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  binary_format_parser.run (binary_of_be (scalar_memop_build op marg))
    (scalar_memop_parser op) = Some (scalar_memop_build op marg).
Proof.
  intros op marg Ha Hm Ho.
  rewrite <- (List.app_nil_r (binary_of_be (scalar_memop_build op marg))).
  apply run_of_prefix. now apply scalar_memop_prefix_round_trip.
Qed.

Definition decode_assert_u32 (k: N) (input: list byte) :=
  match decode_uint 32 5 input with
  | Some (v, rest) => if N.eqb v k then Some (k, rest) else None
  | None => None
  end.

Lemma prefix_assert_u32 : forall k,
  prefix_semantics (fun n =>
    (assert_u32 k: Parser (SizedList byte) byte option N n))
    (decode_assert_u32 k).
Proof.
  intros k n input Hbound. unfold assert_u32.
  rewrite observe_guardM, (prefix_u32 n input Hbound).
  unfold decode_assert_u32.
  destruct (decode_uint 32 5 input) as [[v rest]|]; [|reflexivity].
  destruct (N.eqb v k); reflexivity.
Qed.

Definition decode_sequence {A B} (p: list byte -> option (A * list byte))
  (q: list byte -> option (B * list byte)) (input: list byte) :=
  match p input with Some (_, rest) => q rest | None => None end.

Definition decode_map {A B} (f: A -> B)
  (p: list byte -> option (A * list byte)) input :=
  option_map (fun '(v, rest) => (f v, rest)) (p input).

Definition decode_two_indices (build: N -> N -> basic_instruction) input :=
  match decode_map build (decode_uint 32 5) input with
  | Some (f, rest) => option_map (fun '(y, tail) => (f y, tail)) (decode_uint 32 5 rest)
  | None => None
  end.

Lemma prefix_two_indices : forall build,
  prefix_semantics (fun n =>
    ((build <$> parse_u32_as_N) <*> parse_u32_as_N:
      Parser (SizedList byte) byte option basic_instruction n))
    (decode_two_indices build).
Proof.
  intros build. unfold decode_two_indices, decode_map.
  apply prefix_app; [apply prefix_map; apply prefix_u32|apply prefix_u32].
Qed.

Definition decode_fc_prefix k :=
  decode_sequence (decode_exact_byte xfc) (decode_assert_u32 k).

Lemma prefix_fc_prefix : forall k,
  prefix_semantics (fun n =>
    (exact_byte xfc &> assert_u32 k: Parser (SizedList byte) byte option N n))
    (decode_fc_prefix k).
Proof.
  intros k. unfold decode_fc_prefix, decode_sequence.
  apply prefix_rand; [apply prefix_exact_byte|apply prefix_assert_u32].
Qed.

Inductive indexed_memop := IM_size | IM_grow | IM_fill | IM_copy | IM_init | IM_drop.

Definition indexed_memop_build op x y :=
  match op with
  | IM_size => BI_memory_size x | IM_grow => BI_memory_grow x
  | IM_fill => BI_memory_fill x | IM_copy => BI_memory_copy x y
  | IM_init => BI_memory_init x y | IM_drop => BI_data_drop x
  end.

Definition indexed_memop_parser op : byte_parser_family basic_instruction :=
  match op with
  | IM_size => fun n => parse_memory_size | IM_grow => fun n => parse_memory_grow
  | IM_fill => fun n => parse_memory_fill | IM_copy => fun n => parse_memory_copy
  | IM_init => fun n => parse_memory_init | IM_drop => fun n => parse_data_drop
  end.

Definition decode_indexed_memop op :=
  match op with
  | IM_size => decode_sequence (decode_exact_byte x3f)
      (decode_map BI_memory_size (decode_uint 32 5))
  | IM_grow => decode_sequence (decode_exact_byte x40)
      (decode_map BI_memory_grow (decode_uint 32 5))
  | IM_fill => decode_sequence (decode_fc_prefix 11)
      (decode_map BI_memory_fill (decode_uint 32 5))
  | IM_copy => decode_sequence (decode_fc_prefix 10) (decode_two_indices BI_memory_copy)
  | IM_init => decode_sequence (decode_fc_prefix 8)
      (decode_two_indices (fun data mem => BI_memory_init mem data))
  | IM_drop => decode_sequence (decode_fc_prefix 9)
      (decode_map BI_data_drop (decode_uint 32 5))
  end.

Theorem indexed_memop_prefix_correct : forall op,
  prefix_semantics (indexed_memop_parser op) (decode_indexed_memop op).
Proof.
  intros op. destruct op; unfold decode_indexed_memop, decode_sequence, decode_map.
  - apply prefix_rand; [apply prefix_exact_byte|apply prefix_map; apply prefix_u32].
  - apply prefix_rand; [apply prefix_exact_byte|apply prefix_map; apply prefix_u32].
  - apply prefix_rand; [apply prefix_fc_prefix|apply prefix_map; apply prefix_u32].
  - apply prefix_rand; [apply prefix_fc_prefix|apply prefix_two_indices].
  - apply prefix_rand; [apply prefix_fc_prefix|apply prefix_two_indices].
  - apply prefix_rand; [apply prefix_fc_prefix|apply prefix_map; apply prefix_u32].
Qed.

Lemma decode_small_u32_byte : forall b rest,
  N.lt (Byte.to_N b) 128 ->
  decode_uint 32 5 (b :: rest) = Some (Byte.to_N b, rest).
Proof.
  intros b rest Hsmall.
  unfold decode_uint. cbn [decode_uleb].
  assert (Hlo: N.ltb (Byte.to_N b) 128 = true) by now apply N.ltb_lt.
  rewrite Hlo.
  assert (Hhi: N.ltb (Byte.to_N b) (2 ^ 32) = true).
  { apply N.ltb_lt. eapply N.lt_trans; [exact Hsmall|reflexivity]. }
  now rewrite Hhi.
Qed.

Theorem indexed_memop_decode_round_trip : forall op x y suffix,
  N.lt x u32_bound -> N.lt y u32_bound ->
  decode_indexed_memop op (binary_of_be (indexed_memop_build op x y) ++ suffix) =
    Some (indexed_memop_build op x y, suffix).
Proof.
  intros op x y suffix Hx Hy.
  destruct op; cbn -[binary_of_u32 decode_uint].
  all: unfold binary_of_memidx, binary_of_dataidx, binary_of_idx,
    decode_fc_prefix, decode_sequence, decode_assert_u32, decode_two_indices,
    decode_map.
  all: cbn -[binary_of_u32 decode_uint].
  all: repeat rewrite <- List.app_assoc.
  all: repeat rewrite decode_small_u32_byte by reflexivity.
  all: cbn -[binary_of_u32 decode_uint].
  all: repeat (rewrite decode_binary_u32_suffix by assumption;
    cbn -[binary_of_u32 decode_uint]).
  all: reflexivity.
Qed.

Theorem indexed_memop_prefix_round_trip : forall op x y suffix bound
  (Hbound: (List.length
    (binary_of_be (indexed_memop_build op x y) ++ suffix) <= bound)%nat),
  N.lt x u32_bound -> N.lt y u32_bound ->
  observe_prefix (runParser (indexed_memop_parser op bound) Hbound
    (mkSizedList (binary_of_be (indexed_memop_build op x y) ++ suffix))) =
    Some (indexed_memop_build op x y, suffix).
Proof.
  intros. rewrite indexed_memop_prefix_correct.
  now apply indexed_memop_decode_round_trip.
Qed.

Theorem indexed_memop_run_round_trip : forall op x y,
  N.lt x u32_bound -> N.lt y u32_bound ->
  binary_format_parser.run (binary_of_be (indexed_memop_build op x y))
    (indexed_memop_parser op) = Some (indexed_memop_build op x y).
Proof.
  intros op x y Hx Hy.
  rewrite <- (List.app_nil_r (binary_of_be (indexed_memop_build op x y))).
  apply run_of_prefix. now apply indexed_memop_prefix_round_trip.
Qed.

Definition decode_laneidx (input: list byte) :=
  match input with nil => None | b :: rest => Some (Byte.to_N b, rest) end.

Lemma prefix_laneidx :
  prefix_semantics (fun n =>
    (parse_laneidx: Parser (SizedList byte) byte option laneidx n))
    decode_laneidx.
Proof.
  intros n [|b rest] Hbound; reflexivity.
Qed.

Definition decode_vector_memory_tail code input :=
  match vector_memory_opcode code with
  | Some (VMI_memarg build) => decode_map build decode_memarg input
  | Some (VMI_lane build) =>
      match decode_map build decode_memarg input with
      | Some (f, rest) => decode_map f decode_laneidx rest
      | None => None
      end
  | None => None
  end.

Lemma prefix_vector_memory_tail : forall code,
  prefix_semantics (fun n =>
    (parse_vector_memory_tail code:
      Parser (SizedList byte) byte option basic_instruction n))
    (decode_vector_memory_tail code).
Proof.
  intros code. unfold parse_vector_memory_tail, decode_vector_memory_tail.
  destruct (vector_memory_opcode code) as [[build|build]|].
  - apply prefix_map. apply parse_memarg_prefix_correct.
  - unfold decode_map.
    apply prefix_app; [apply prefix_map; apply parse_memarg_prefix_correct|].
    apply prefix_laneidx.
  - apply prefix_fail.
Qed.

Definition decode_vector_memory input :=
  decode_sequence (decode_exact_byte xfd)
    (fun input =>
      match decode_uint 32 5 input with
      | Some (code, rest) => decode_vector_memory_tail code rest
      | None => None
      end) input.

Theorem vector_memory_prefix_correct :
  prefix_semantics (fun n =>
    (parse_vector_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction n))
    decode_vector_memory.
Proof.
  unfold parse_vector_memory_instruction, decode_vector_memory, decode_sequence.
  apply prefix_rand; [apply prefix_exact_byte|].
  apply prefix_bind; [apply prefix_u32|apply prefix_vector_memory_tail].
Qed.

Ltac split_vector_opcode H :=
  do 7 (try match goal with p: positive |- _ => destruct p end;
    cbn [vector_memory_opcode] in H; try discriminate).

Lemma vector_memory_opcode_bound : forall code args,
  vector_memory_opcode code = Some args ->
  N.lt code 128.
Proof.
  intros [|p] args H; split_vector_opcode H; reflexivity.
Qed.

Lemma vector_memarg_print : forall code build marg,
  vector_memory_opcode code = Some (VMI_memarg build) ->
  binary_of_be (build marg) =
    xfd :: binary_of_u32 code ++ binary_of_memarg marg.
Proof.
  intros [|p] build marg H; split_vector_opcode H;
    inversion H; subst; reflexivity.
Qed.

Lemma vector_lane_print : forall code build marg lane,
  vector_memory_opcode code = Some (VMI_lane build) ->
  binary_of_be (build marg lane) =
    xfd :: binary_of_u32 code ++ binary_of_memarg marg ++ binary_of_laneidx lane.
Proof.
  intros [|p] build marg lane H; split_vector_opcode H;
    inversion H; subst; reflexivity.
Qed.

Lemma decode_binary_lane_suffix : forall lane suffix,
  N.lt lane 256 ->
  decode_laneidx (binary_of_laneidx lane ++ suffix) = Some (lane, suffix).
Proof.
  intros lane suffix Hlane. unfold binary_of_laneidx.
  destruct (Byte.of_N lane) eqn:Hbyte.
  - simpl. apply Byte.to_of_N in Hbyte. now rewrite Hbyte.
  - apply Byte.of_N_None_iff in Hbyte. lia.
Qed.

Theorem vector_memarg_prefix_round_trip : forall code build marg suffix bound
  (Hbound: (List.length (binary_of_be (build marg) ++ suffix) <= bound)%nat),
  vector_memory_opcode code = Some (VMI_memarg build) ->
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  observe_prefix (runParser
    (parse_vector_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be (build marg) ++ suffix))) =
    Some (build marg, suffix).
Proof.
  intros code build marg suffix bound Hbound Hcode Ha Hm Ho.
  rewrite vector_memory_prefix_correct.
  rewrite (vector_memarg_print _ _ _ Hcode).
  unfold decode_vector_memory, decode_sequence.
  cbn [List.app decode_exact_byte].
  rewrite (Byte.byte_dec_lb (eq_refl xfd)).
  rewrite <- List.app_assoc.
  rewrite decode_binary_u32_suffix.
  2: { pose proof (vector_memory_opcode_bound _ _ Hcode).
       unfold u32_bound. lia. }
  unfold decode_vector_memory_tail. rewrite Hcode.
  unfold decode_map.
  rewrite decode_binary_memarg_suffix by assumption. reflexivity.
Qed.

Theorem vector_lane_prefix_round_trip : forall code build marg lane suffix bound
  (Hbound: (List.length (binary_of_be (build marg lane) ++ suffix) <= bound)%nat),
  vector_memory_opcode code = Some (VMI_lane build) ->
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  N.lt lane 256 ->
  observe_prefix (runParser
    (parse_vector_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be (build marg lane) ++ suffix))) =
    Some (build marg lane, suffix).
Proof.
  intros code build marg lane suffix bound Hbound Hcode Ha Hm Ho Hlane.
  rewrite vector_memory_prefix_correct.
  rewrite (vector_lane_print _ _ _ _ Hcode).
  unfold decode_vector_memory, decode_sequence.
  cbn [List.app decode_exact_byte].
  rewrite (Byte.byte_dec_lb (eq_refl xfd)).
  repeat rewrite <- List.app_assoc.
  rewrite decode_binary_u32_suffix.
  2: { pose proof (vector_memory_opcode_bound _ _ Hcode).
       unfold u32_bound. lia. }
  unfold decode_vector_memory_tail. rewrite Hcode.
  unfold decode_map.
  rewrite decode_binary_memarg_suffix by assumption. simpl.
  rewrite decode_binary_lane_suffix by assumption. reflexivity.
Qed.

Theorem vector_memarg_run_round_trip : forall code build marg,
  vector_memory_opcode code = Some (VMI_memarg build) ->
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  binary_format_parser.run (binary_of_be (build marg))
    (fun n => (parse_vector_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction n)) = Some (build marg).
Proof.
  intros code build marg Hcode Ha Hm Ho.
  rewrite <- (List.app_nil_r (binary_of_be (build marg))).
  apply run_of_prefix.
  now eapply vector_memarg_prefix_round_trip with (code := code).
Qed.

Theorem vector_lane_run_round_trip : forall code build marg lane,
  vector_memory_opcode code = Some (VMI_lane build) ->
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  N.lt lane 256 ->
  binary_format_parser.run (binary_of_be (build marg lane))
    (fun n => (parse_vector_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction n)) =
    Some (build marg lane).
Proof.
  intros code build marg lane Hcode Ha Hm Ho Hl.
  rewrite <- (List.app_nil_r (binary_of_be (build marg lane))).
  apply run_of_prefix.
  now eapply vector_lane_prefix_round_trip with (code := code).
Qed.

Definition decode_or {A}
  (p q: list byte -> option (A * list byte)) input :=
  match p input with Some result => Some result | None => q input end.

Definition scalar_memops :=
  SM_i32_load :: SM_i64_load :: SM_f32_load :: SM_f64_load ::
  SM_i32_load8_s :: SM_i32_load8_u :: SM_i32_load16_s :: SM_i32_load16_u ::
  SM_i64_load8_s :: SM_i64_load8_u :: SM_i64_load16_s :: SM_i64_load16_u ::
  SM_i64_load32_s :: SM_i64_load32_u ::
  SM_i32_store :: SM_i64_store :: SM_f32_store :: SM_f64_store ::
  SM_i32_store8 :: SM_i32_store16 :: SM_i64_store8 :: SM_i64_store16 ::
  SM_i64_store32 :: nil.

Definition decode_memory_instruction :=
  List.fold_right decode_or (decode_indexed_memop IM_fill)
    (List.map (fun op =>
      decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op))
      scalar_memops ++
     decode_vector_memory ::
     decode_indexed_memop IM_size :: decode_indexed_memop IM_grow ::
     decode_indexed_memop IM_init :: decode_indexed_memop IM_drop ::
     decode_indexed_memop IM_copy :: nil).

Theorem memory_instruction_prefix_correct :
  prefix_semantics (fun n =>
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction n))
    decode_memory_instruction.
Proof.
  unfold parse_memory_instruction, decode_memory_instruction, scalar_memops.
  cbn [List.map List.app List.fold_right].
  unfold decode_or.
  do 23 (apply prefix_alt; [apply prefix_tagged_memarg|]).
  apply prefix_alt; [apply vector_memory_prefix_correct|].
  apply prefix_alt; [apply (indexed_memop_prefix_correct IM_size)|].
  apply prefix_alt; [apply (indexed_memop_prefix_correct IM_grow)|].
  apply prefix_alt; [apply (indexed_memop_prefix_correct IM_init)|].
  apply prefix_alt; [apply (indexed_memop_prefix_correct IM_drop)|].
  apply prefix_alt; [apply (indexed_memop_prefix_correct IM_copy)|].
  apply (indexed_memop_prefix_correct IM_fill).
Qed.

Theorem scalar_memory_class_round_trip : forall op marg suffix bound
  (Hbound: (List.length
    (binary_of_be (scalar_memop_build op marg) ++ suffix) <= bound)%nat),
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be (scalar_memop_build op marg) ++ suffix))) =
    Some (scalar_memop_build op marg, suffix).
Proof.
  intros op marg suffix bound Hbound Ha Hm Ho.
  rewrite memory_instruction_prefix_correct.
  assert (Hbytes: binary_of_be (scalar_memop_build op marg) =
    scalar_memop_tag op :: binary_of_memarg marg) by (destruct op; reflexivity).
  rewrite Hbytes.
  destruct op; unfold decode_memory_instruction, scalar_memops, decode_or,
    decode_tagged_memarg, decode_exact_byte;
    cbn -[binary_of_memarg decode_memarg decode_uint].
  all: rewrite decode_binary_memarg_suffix by assumption.
  all: reflexivity.
Qed.

Theorem indexed_memory_class_round_trip : forall op x y suffix bound
  (Hbound: (List.length
    (binary_of_be (indexed_memop_build op x y) ++ suffix) <= bound)%nat),
  N.lt x u32_bound -> N.lt y u32_bound ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be (indexed_memop_build op x y) ++ suffix))) =
    Some (indexed_memop_build op x y, suffix).
Proof.
  intros op x y suffix bound Hbound Hx Hy.
  rewrite memory_instruction_prefix_correct.
  destruct op; unfold decode_memory_instruction, scalar_memops, decode_or,
    decode_tagged_memarg, decode_exact_byte;
    cbn -[binary_of_u32 decode_uint].
  all: unfold binary_of_memidx, binary_of_dataidx, binary_of_idx,
    decode_indexed_memop, decode_fc_prefix, decode_sequence,
    decode_assert_u32, decode_two_indices, decode_map, decode_vector_memory.
  all: cbn -[binary_of_u32 decode_uint].
  all: repeat rewrite <- List.app_assoc.
  all: repeat (rewrite decode_small_u32_byte by reflexivity;
    cbn -[binary_of_u32 decode_uint]).
  all: repeat (rewrite decode_binary_u32_suffix by assumption;
    cbn -[binary_of_u32 decode_uint]).
  all: reflexivity.
Qed.

Theorem vector_memarg_class_round_trip : forall code build marg suffix bound
  (Hbound: (List.length (binary_of_be (build marg) ++ suffix) <= bound)%nat),
  vector_memory_opcode code = Some (VMI_memarg build) ->
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be (build marg) ++ suffix))) =
    Some (build marg, suffix).
Proof.
  intros code build marg suffix bound Hbound Hcode Ha Hm Ho.
  pose proof (vector_memarg_prefix_round_trip code build marg suffix bound
    Hbound Hcode Ha Hm Ho) as Hvec.
  rewrite vector_memory_prefix_correct in Hvec.
  rewrite memory_instruction_prefix_correct.
  rewrite (vector_memarg_print _ _ _ Hcode) in Hvec |- *.
  cbn [List.app] in Hvec.
  unfold decode_memory_instruction, scalar_memops, decode_or,
    decode_tagged_memarg, decode_exact_byte.
  cbn -[binary_of_u32 binary_of_memarg decode_memarg decode_uint decode_vector_memory].
  rewrite Hvec. reflexivity.
Qed.

Theorem vector_lane_class_round_trip : forall code build marg lane suffix bound
  (Hbound: (List.length (binary_of_be (build marg lane) ++ suffix) <= bound)%nat),
  vector_memory_opcode code = Some (VMI_lane build) ->
  N.lt marg.(memarg_align) 64 ->
  N.lt marg.(memarg_memory) u32_bound ->
  (marg.(memarg_offset) < 2 ^ 64)%N ->
  N.lt lane 256 ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be (build marg lane) ++ suffix))) =
    Some (build marg lane, suffix).
Proof.
  intros code build marg lane suffix bound Hbound Hcode Ha Hm Ho Hl.
  pose proof (vector_lane_prefix_round_trip code build marg lane suffix bound
    Hbound Hcode Ha Hm Ho Hl) as Hvec.
  rewrite vector_memory_prefix_correct in Hvec.
  rewrite memory_instruction_prefix_correct.
  rewrite (vector_lane_print _ _ _ _ Hcode) in Hvec |- *.
  cbn [List.app] in Hvec.
  unfold decode_memory_instruction, scalar_memops, decode_or,
    decode_tagged_memarg, decode_exact_byte.
  cbn -[binary_of_u32 binary_of_memarg binary_of_laneidx
    decode_memarg decode_uint decode_vector_memory].
  rewrite Hvec. reflexivity.
Qed.

(** Encodability is separate from validation: e.g. an excessive alignment can
    be syntactically encodable but correctly rejected by the type checker. *)
Inductive encodable_memory_instruction : basic_instruction -> Prop :=
| EMI_scalar : forall op marg,
    N.lt marg.(memarg_align) 64 ->
    N.lt marg.(memarg_memory) u32_bound ->
     (marg.(memarg_offset) < 2 ^ 64)%N ->
    encodable_memory_instruction (scalar_memop_build op marg)
| EMI_indexed : forall op x y,
    N.lt x u32_bound -> N.lt y u32_bound ->
    encodable_memory_instruction (indexed_memop_build op x y)
| EMI_vector : forall code build marg,
    vector_memory_opcode code = Some (VMI_memarg build) ->
    N.lt marg.(memarg_align) 64 ->
    N.lt marg.(memarg_memory) u32_bound ->
     (marg.(memarg_offset) < 2 ^ 64)%N ->
    encodable_memory_instruction (build marg)
| EMI_lane : forall code build marg lane,
    vector_memory_opcode code = Some (VMI_lane build) ->
    N.lt marg.(memarg_align) 64 ->
    N.lt marg.(memarg_memory) u32_bound ->
     (marg.(memarg_offset) < 2 ^ 64)%N ->
    N.lt lane 256 ->
    encodable_memory_instruction (build marg lane).

Theorem memory_instruction_run_round_trip : forall be,
  encodable_memory_instruction be ->
  binary_format_parser.run (binary_of_be be)
    (fun n => (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction n)) = Some be.
Proof.
  intros be Henc. rewrite <- (List.app_nil_r (binary_of_be be)).
  apply run_of_prefix.
  destruct Henc.
  - now apply scalar_memory_class_round_trip.
  - now apply indexed_memory_class_round_trip.
  - now eapply vector_memarg_class_round_trip with (code := code).
  - now eapply vector_lane_class_round_trip with (code := code).
Qed.

Inductive memory_head : byte -> Prop :=
| MH_scalar : forall op, memory_head (scalar_memop_tag op)
| MH_size : memory_head x3f
| MH_grow : memory_head x40
| MH_vector : memory_head xfd.

Local Opaque parse_memory_instruction parse_numeric_instruction.

Lemma run_exact_byte_mismatch : forall tag b rest bound
  (Hbound: (S (List.length rest) <= bound)%nat),
  Byte.eqb b tag = false ->
  @runParser (SizedList byte) byte option byte bound (exact_byte tag)
    (S (List.length rest)) Hbound (mkSizedList (b :: rest)) = None.
Proof.
  intros tag b rest bound Hbound Hneq.
  pose proof (prefix_exact_byte tag bound (b :: rest) Hbound) as H.
  unfold decode_exact_byte in H. rewrite Hneq in H.
  change (observe_prefix
    (@runParser (SizedList byte) byte option byte bound (exact_byte tag)
      (S (List.length rest)) Hbound (mkSizedList (b :: rest))) = None) in H.
  destruct (@runParser (SizedList byte) byte option byte bound (exact_byte tag)
    (S (List.length rest)) Hbound (mkSizedList (b :: rest)));
    [discriminate|reflexivity].
Qed.

Lemma parse_be_layer_plain_memory_success : forall tag rest bound value suffix
  (ends: Box (byte_parser (list basic_instruction)) bound)
  (branches: Box (byte_parser (list basic_instruction * list basic_instruction)) bound)
  (Hbound: (List.length (tag :: rest) <= bound)%nat),
  memory_head tag ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (tag :: rest))) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be_layer ends branches:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (tag :: rest))) = Some (value, suffix).
Proof.
  intros tag rest bound value suffix ends branches Hbound Hhead Hmem.
  unfold parse_be_layer.
  remember (parse_memory_instruction:
    byte_parser basic_instruction bound) as pm eqn:Hpm in *.
  clear Hpm.
  remember (parse_numeric_instruction:
    byte_parser basic_instruction bound) as pn eqn:Hpn.
  clear Hpn.
  destruct Hhead; [destruct op| | |].
  all: repeat (cbn -[exact_byte parse_block_type parse_labelidx parse_vec
      parse_funcidx parse_typeidx parse_tableidx parse_reference_type parse_u32_as_N];
    rewrite run_exact_byte_mismatch by reflexivity).
  all: cbn -[exact_byte parse_block_type parse_labelidx parse_vec
    parse_funcidx parse_typeidx parse_tableidx parse_reference_type parse_u32_as_N].
  all: lazymatch goal with
  | |- observe_prefix (option_rect _ _ _ ?result _) = _ =>
      change (observe_prefix result = Some (value, suffix)) in Hmem;
      destruct result; [exact Hmem|discriminate Hmem]
  end.
Qed.

Lemma parse_be_plain_memory_success : forall tag rest bound value suffix
  (Hbound: (List.length (tag :: rest) <= bound)%nat),
  memory_head tag ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (tag :: rest))) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be bound:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (tag :: rest))) = Some (value, suffix).
Proof.
  intros tag rest bound value suffix Hbound Hhead Hmem.
  destruct bound as [|bound]; [simpl in Hbound; lia|].
  unfold parse_be, language, Induction.Fix, Induction.extract.
  cbn [Induction.FixBox Induction.call _be].
  now apply parse_be_layer_plain_memory_success.
Qed.

Inductive memory_fc_head : byte -> Prop :=
| MFH_init : memory_fc_head x08
| MFH_drop : memory_fc_head x09
| MFH_copy : memory_fc_head x0a
| MFH_fill : memory_fc_head x0b.

Lemma run_exact_byte_mismatch2 : forall tag b c rest bound
  (Hbound: (S (S (List.length rest)) <= bound)%nat),
  Byte.eqb b tag = false ->
  @runParser (SizedList byte) byte option byte bound (exact_byte tag)
    (S (S (List.length rest))) Hbound (mkSizedList (b :: c :: rest)) = None.
Proof.
  intros tag b c rest bound Hbound H.
  exact (run_exact_byte_mismatch tag b (c :: rest) bound Hbound H).
Qed.

Definition decode_table_instruction :=
  decode_or (decode_sequence (decode_exact_byte x25)
    (decode_map BI_table_get (decode_uint 32 5)))
  (decode_or (decode_sequence (decode_exact_byte x26)
    (decode_map BI_table_set (decode_uint 32 5)))
  (decode_or (decode_sequence (decode_fc_prefix 12)
    (decode_two_indices (fun elem table => BI_table_init table elem)))
  (decode_or (decode_sequence (decode_fc_prefix 13)
    (decode_map BI_elem_drop (decode_uint 32 5)))
  (decode_or (decode_sequence (decode_fc_prefix 14)
    (decode_two_indices BI_table_copy))
  (decode_or (decode_sequence (decode_fc_prefix 15)
    (decode_map BI_table_grow (decode_uint 32 5)))
  (decode_or (decode_sequence (decode_fc_prefix 16)
    (decode_map BI_table_size (decode_uint 32 5)))
    (decode_sequence (decode_fc_prefix 17)
      (decode_map BI_table_fill (decode_uint 32 5))))))))).

Lemma table_instruction_prefix_correct :
  prefix_semantics (fun n =>
    (parse_table_instruction:
      Parser (SizedList byte) byte option basic_instruction n))
    decode_table_instruction.
Proof.
  unfold parse_table_instruction, decode_table_instruction, decode_or,
    decode_sequence, decode_map.
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_exact_byte|apply prefix_map; apply prefix_u32]. }
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_exact_byte|apply prefix_map; apply prefix_u32]. }
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_fc_prefix|apply prefix_two_indices]. }
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_fc_prefix|apply prefix_map; apply prefix_u32]. }
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_fc_prefix|apply prefix_two_indices]. }
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_fc_prefix|apply prefix_map; apply prefix_u32]. }
  apply prefix_alt.
  { apply prefix_rand; [apply prefix_fc_prefix|apply prefix_map; apply prefix_u32]. }
  apply prefix_rand; [apply prefix_fc_prefix|apply prefix_map; apply prefix_u32].
Qed.

Lemma run_table_memory_fc_reject : forall code rest bound
  (Hbound: (S (S (List.length rest)) <= bound)%nat),
  memory_fc_head code ->
  @runParser (SizedList byte) byte option basic_instruction bound
    parse_table_instruction (S (S (List.length rest))) Hbound
    (mkSizedList (xfc :: code :: rest)) = None.
Proof.
  intros code rest bound Hbound Hcode.
  pose proof (table_instruction_prefix_correct bound
    (xfc :: code :: rest) Hbound) as H.
  assert (Hdecode: decode_table_instruction (xfc :: code :: rest) = None).
  { unfold decode_table_instruction, decode_or, decode_sequence, decode_fc_prefix,
      decode_assert_u32, decode_exact_byte.
    cbn -[decode_uint].
    destruct Hcode;
      rewrite decode_small_u32_byte by reflexivity; reflexivity. }
  rewrite Hdecode in H.
  change (observe_prefix
    (@runParser (SizedList byte) byte option basic_instruction bound
      parse_table_instruction (S (S (List.length rest))) Hbound
      (mkSizedList (xfc :: code :: rest))) = None) in H.
  destruct (@runParser (SizedList byte) byte option basic_instruction bound
    parse_table_instruction (S (S (List.length rest))) Hbound
    (mkSizedList (xfc :: code :: rest))); [discriminate|reflexivity].
Qed.

Lemma parse_be_layer_fc_memory_success : forall code rest bound value suffix
  (ends: Box (byte_parser (list basic_instruction)) bound)
  (branches: Box (byte_parser (list basic_instruction * list basic_instruction)) bound)
  (Hbound: (List.length (xfc :: code :: rest) <= bound)%nat),
  memory_fc_head code ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: code :: rest))) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be_layer ends branches:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: code :: rest))) = Some (value, suffix).
Proof.
  intros code rest bound value suffix ends branches Hbound Hhead Hmem.
  unfold parse_be_layer.
  remember (parse_memory_instruction:
    byte_parser basic_instruction bound) as pm eqn:Hpm in *.
  clear Hpm.
  remember (parse_numeric_instruction:
    byte_parser basic_instruction bound) as pn eqn:Hpn.
  clear Hpn.
  cbn -[exact_byte parse_table_instruction parse_block_type parse_labelidx parse_vec
    parse_funcidx parse_typeidx parse_tableidx parse_reference_type parse_u32_as_N].
  repeat (rewrite run_exact_byte_mismatch2 by reflexivity;
    cbn -[exact_byte parse_table_instruction parse_block_type parse_labelidx parse_vec
      parse_funcidx parse_typeidx parse_tableidx parse_reference_type parse_u32_as_N]).
  rewrite run_table_memory_fc_reject by exact Hhead.
  cbn -[exact_byte].
  all: lazymatch goal with
  | |- observe_prefix (option_rect _ _ _ ?result _) = _ =>
      change (observe_prefix result = Some (value, suffix)) in Hmem;
      destruct result; [exact Hmem|discriminate Hmem]
  end.
Qed.

Lemma parse_be_fc_memory_success : forall code rest bound value suffix
  (Hbound: (List.length (xfc :: code :: rest) <= bound)%nat),
  memory_fc_head code ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: code :: rest))) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be bound:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: code :: rest))) = Some (value, suffix).
Proof.
  intros code rest bound value suffix Hbound Hhead Hmem.
  destruct bound as [|bound]; [simpl in Hbound; lia|].
  unfold parse_be, language, Induction.Fix, Induction.extract.
  cbn [Induction.FixBox Induction.call _be].
  now apply parse_be_layer_fc_memory_success.
Qed.

Inductive memory_binary_head : list byte -> Prop :=
| MBH_plain : forall tag rest,
    memory_head tag -> memory_binary_head (tag :: rest)
| MBH_fc : forall code rest,
    memory_fc_head code -> memory_binary_head (xfc :: code :: rest).

Lemma encodable_memory_binary_head : forall be,
  encodable_memory_instruction be ->
  forall suffix, memory_binary_head (binary_of_be be ++ suffix).
Proof.
  intros be Henc suffix. destruct Henc.
  - assert (Hbytes: binary_of_be (scalar_memop_build op marg) =
      scalar_memop_tag op :: binary_of_memarg marg)
      by (destruct op; reflexivity).
    rewrite Hbytes. apply MBH_plain. constructor.
  - destruct op; cbn -[binary_of_u32].
    + apply MBH_plain. exact MH_size.
    + apply MBH_plain. exact MH_grow.
    + apply MBH_fc. exact MFH_fill.
    + apply MBH_fc. exact MFH_copy.
    + apply MBH_fc. exact MFH_init.
    + apply MBH_fc. exact MFH_drop.
  - rewrite (vector_memarg_print _ _ _ H).
    apply MBH_plain. constructor.
  - rewrite (vector_lane_print _ _ _ _ H).
    apply MBH_plain. constructor.
Qed.

Lemma parse_be_memory_success : forall input bound value suffix
  (Hbound: (List.length input <= bound)%nat),
  memory_binary_head input ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList input)) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be bound:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList input)) = Some (value, suffix).
Proof.
  intros input bound value suffix Hbound Hhead Hmem.
  destruct Hhead.
  - now apply parse_be_plain_memory_success.
  - now apply parse_be_fc_memory_success.
Qed.

Theorem memory_instruction_prefix_round_trip : forall be,
  encodable_memory_instruction be ->
  forall suffix bound
    (Hbound: (List.length (binary_of_be be ++ suffix) <= bound)%nat),
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be be ++ suffix))) = Some (be, suffix).
Proof.
  intros be Henc suffix bound Hbound. destruct Henc.
  - now apply scalar_memory_class_round_trip.
  - now apply indexed_memory_class_round_trip.
  - now eapply vector_memarg_class_round_trip with (code := code).
  - now eapply vector_lane_class_round_trip with (code := code).
Qed.

Theorem parse_be_memory_prefix_round_trip : forall be,
  encodable_memory_instruction be ->
  forall suffix bound
    (Hbound: (List.length (binary_of_be be ++ suffix) <= bound)%nat),
  observe_prefix (runParser
    (parse_be bound:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (binary_of_be be ++ suffix))) = Some (be, suffix).
Proof.
  intros be Henc suffix bound Hbound.
  apply parse_be_memory_success.
  - now apply encodable_memory_binary_head.
  - now apply memory_instruction_prefix_round_trip.
Qed.

Theorem parse_be_memory_run_round_trip : forall be,
  encodable_memory_instruction be ->
  binary_format_parser.run (binary_of_be be) parse_be = Some be.
Proof.
  intros be Henc. rewrite <- (List.app_nil_r (binary_of_be be)).
  apply run_of_prefix. now apply parse_be_memory_prefix_round_trip.
Qed.

(** The top-level success connection is not restricted to canonical printer
    bytes: padded LEB subopcodes of bulk memory instructions are admitted too. *)
Inductive memory_bulk_code : N -> Prop :=
| MBC_init : memory_bulk_code 8
| MBC_drop : memory_bulk_code 9
| MBC_copy : memory_bulk_code 10
| MBC_fill : memory_bulk_code 11.

Lemma run_table_bulk_reject : forall rest code tail bound
  (Hbound: (S (List.length rest) <= bound)%nat),
  decode_uint 32 5 rest = Some (code, tail) ->
  memory_bulk_code code ->
  @runParser (SizedList byte) byte option basic_instruction bound
    parse_table_instruction (S (List.length rest)) Hbound
    (mkSizedList (xfc :: rest)) = None.
Proof.
  intros rest code tail bound Hbound Hdecode Hcode.
  pose proof (table_instruction_prefix_correct bound
    (xfc :: rest) Hbound) as H.
  assert (Hreject: decode_table_instruction (xfc :: rest) = None).
  { unfold decode_table_instruction, decode_or, decode_sequence, decode_fc_prefix,
      decode_assert_u32, decode_exact_byte.
    cbn -[decode_uint]. rewrite Hdecode.
    destruct Hcode; reflexivity. }
  rewrite Hreject in H.
  change (observe_prefix
    (@runParser (SizedList byte) byte option basic_instruction bound
      parse_table_instruction (S (List.length rest)) Hbound
      (mkSizedList (xfc :: rest))) = None) in H.
  destruct (@runParser (SizedList byte) byte option basic_instruction bound
    parse_table_instruction (S (List.length rest)) Hbound
    (mkSizedList (xfc :: rest))); [discriminate|reflexivity].
Qed.

Lemma parse_be_layer_bulk_memory_success : forall rest code tail bound value suffix
  (ends: Box (byte_parser (list basic_instruction)) bound)
  (branches: Box (byte_parser (list basic_instruction * list basic_instruction)) bound)
  (Hbound: (List.length (xfc :: rest) <= bound)%nat),
  decode_uint 32 5 rest = Some (code, tail) ->
  memory_bulk_code code ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: rest))) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be_layer ends branches:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: rest))) = Some (value, suffix).
Proof.
  intros rest code tail bound value suffix ends branches Hbound Hdecode Hcode Hmem.
  unfold parse_be_layer.
  remember (parse_memory_instruction:
    byte_parser basic_instruction bound) as pm eqn:Hpm in *.
  clear Hpm.
  remember (parse_numeric_instruction:
    byte_parser basic_instruction bound) as pn eqn:Hpn.
  clear Hpn.
  cbn -[exact_byte parse_table_instruction parse_block_type parse_labelidx parse_vec
    parse_funcidx parse_typeidx parse_tableidx parse_reference_type parse_u32_as_N].
  repeat (rewrite run_exact_byte_mismatch by reflexivity;
    cbn -[exact_byte parse_table_instruction parse_block_type parse_labelidx parse_vec
      parse_funcidx parse_typeidx parse_tableidx parse_reference_type parse_u32_as_N]).
  rewrite (run_table_bulk_reject rest code tail bound Hbound Hdecode Hcode).
  cbn -[exact_byte].
  lazymatch goal with
  | |- observe_prefix (option_rect _ _ _ ?result _) = _ =>
      change (observe_prefix result = Some (value, suffix)) in Hmem;
      destruct result; [exact Hmem|discriminate Hmem]
  end.
Qed.

Theorem parse_be_bulk_memory_success : forall rest code tail bound value suffix
  (Hbound: (List.length (xfc :: rest) <= bound)%nat),
  decode_uint 32 5 rest = Some (code, tail) ->
  memory_bulk_code code ->
  observe_prefix (runParser
    (parse_memory_instruction:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: rest))) = Some (value, suffix) ->
  observe_prefix (runParser
    (parse_be bound:
      Parser (SizedList byte) byte option basic_instruction bound)
    Hbound (mkSizedList (xfc :: rest))) = Some (value, suffix).
Proof.
  intros rest code tail bound value suffix Hbound Hdecode Hcode Hmem.
  destruct bound as [|bound]; [simpl in Hbound; lia|].
  unfold parse_be, language, Induction.Fix, Induction.extract.
  cbn [Induction.FixBox Induction.call _be].
  now eapply parse_be_layer_bulk_memory_success; eauto.
Qed.
