(** Compositional correspondence for the instruction parsers actually selected
    by the production language.  These lemmas concern instruction bodies;
    recursive language-dispatch/section/module correctness is a separate
    shared obligation, not inferred from immediate-codec correctness. *)
From Stdlib Require Import List NArith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes operations addressing addressing_binary
  addressing_parseque binary_format_parser binary_format_printer
  binary_format_addressing_properties binary_parser_combinator_properties
  leb128_properties leb128_unsigned_printer_properties.
Open Scope list_scope.

Definition address_memarg_bounds (m : memarg) : Prop :=
  (m.(memarg_align) < 64)%N /\
  (m.(memarg_memory) < Addressing.address_bound Addressing.AT_i32)%N /\
  (m.(memarg_offset) < Addressing.address_bound Addressing.AT_i64)%N.

Definition printed {A} (encode : A -> list Byte.byte) (valid : A -> Prop)
    (bs : list Byte.byte) (a : A) : Prop :=
  valid a /\ bs = encode a.

Lemma production_memarg_printed_complete n :
  parser_complete
    (@parse_memarg (SizedList Byte.byte) _ option _ _ _ n)
    (printed binary_of_memarg address_memarg_bounds).
Proof.
  intros m bound input prefix suffix arg Input [[Align [Memory Offset]] Prefix].
  subst prefix.
  pose proof (binary_memarg_printer_parser_roundtrip arg suffix Align Memory Offset)
    as Decoded.
  rewrite binary_memarg_parser_correct in Decoded.
  pose proof (AddressingParseque.decode_memarg_tokens_correct_sized m input)
    as Correspondence.
  assert (RawDecoded : AddressingParseque.decode_memarg (input_bytes input) =
    Some (arg, suffix)) by (rewrite Input; exact Decoded).
  unfold input_bytes in RawDecoded.
  rewrite RawDecoded in Correspondence.
  unfold AddressingParseque.flatten_memarg in Correspondence.
  destruct (AddressingParseque.decode_memarg_tokens input)
    as [result|] eqn:Tokens; cbn in Correspondence; [|discriminate].
  exists result; split.
  - cbn [parse_memarg AddressingParseque.parse_memarg runParser Category.fromOption].
    now rewrite Tokens.
  - inversion Correspondence; auto.
Qed.

Lemma production_u32_printed_complete n :
  parser_complete
    (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n)
    (printed binary_of_u32 (fun x => (x < 4294967296)%N)).
Proof.
  eapply parser_complete_weaken; [apply parse_u32_prefix_complete|].
  intros bs x [Range ->].
  split; [apply encode_unsigned_sound|].
  split; [lia|].
  apply (proj2 (binary_address_unsigned_encoding Addressing.AT_i32 x Range)).
Qed.

(** [rand] is the actual [&>] combinator, definitionally [bind] with an
    unused first result. No monad law or extraction rewrite is assumed. *)
Lemma production_prefix_complete {A B n}
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (q : Parser (SizedList Byte.byte) Byte.byte option B n)
    (prefix : list Byte.byte) (first : A) (Q : list Byte.byte -> B -> Prop) :
  parser_complete p (fun bs a => bs = prefix /\ a = first) ->
  parser_complete q Q ->
  parser_complete (p &> q)
    (fun bs b => exists tail, bs = prefix ++ tail /\ Q tail b).
Proof.
  intros Head Tail.
  change (parser_complete (Combinators.bind p (fun _ => box q))
    (fun bs b => exists tail, bs = prefix ++ tail /\ Q tail b)).
  eapply parser_complete_bind with
    (P := fun bs a => bs = prefix /\ a = first)
    (Q := fun _ bs b => Q bs b).
  - exact Head.
  - intros a k lt. simpl. apply parser_complete_le_lower. exact Tail.
  - intros bs b [tail [Bytes Parsed]].
    exists prefix, tail, first. auto.
Qed.

Lemma production_opcode_complete {A n}
    (opcode : Byte.byte)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (P : list Byte.byte -> A -> Prop) :
  parser_complete p P ->
  parser_complete (exact_byte opcode &> p)
    (fun bs a => exists tail, bs = opcode :: tail /\ P tail a).
Proof.
  intro Complete.
  change (parser_complete (exact_byte opcode &> p)
    (fun bs a => exists tail, bs = (opcode :: nil) ++ tail /\ P tail a)).
  apply production_prefix_complete with (first := opcode).
  - apply parser_complete_exact_byte.
  - exact Complete.
Qed.

Lemma production_mapped_immediate_complete {A B n}
    (constructor : A -> B)
    (p : Parser (SizedList Byte.byte) Byte.byte option A n)
    (encode : A -> list Byte.byte) (valid : A -> Prop) :
  parser_complete p (printed encode valid) ->
  parser_complete (constructor <$> p)
    (fun bs b => exists a, valid a /\ bs = encode a /\ b = constructor a).
Proof.
  intro Complete. eapply parser_complete_map; [exact Complete|].
  intros bs b [a [Valid [Bytes Value]]].
  exists a; split; [split; assumption|exact Value].
Qed.

Theorem production_scalar_memarg_body_complete opcode
    (constructor : memarg -> basic_instruction) n :
  parser_complete
    (exact_byte opcode &>
      (constructor <$> (@parse_memarg (SizedList Byte.byte) _ option _ _ _ n)))
    (fun bs be => exists marg,
      address_memarg_bounds marg /\
      bs = opcode :: binary_of_memarg marg /\ be = constructor marg).
Proof.
  eapply parser_complete_weaken.
  - apply production_opcode_complete.
    apply production_mapped_immediate_complete.
    apply production_memarg_printed_complete.
  - intros bs be [marg [Valid [Bytes Value]]].
    exists (binary_of_memarg marg); split; [exact Bytes|].
    exists marg; auto.
Qed.

Theorem production_indexed_body_complete opcode
    (constructor : N -> basic_instruction) n :
  parser_complete
    (exact_byte opcode &>
      (constructor <$> (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n)))
    (fun bs be => exists index,
      (index < 4294967296)%N /\
      bs = opcode :: binary_of_u32 index /\ be = constructor index).
Proof.
  eapply parser_complete_weaken.
  - apply production_opcode_complete.
    apply production_mapped_immediate_complete.
    apply production_u32_printed_complete.
  - intros bs be [index [Valid [Bytes Value]]].
    exists (binary_of_u32 index); split; [exact Bytes|].
    exists index; auto.
Qed.

Definition production_be_parser :=
  forall n, Parser (SizedList Byte.byte) Byte.byte option basic_instruction n.

Definition memarg_instruction_codec (p : production_be_parser)
    (constructor : memarg -> basic_instruction) : Prop :=
  forall n, parser_complete (p n)
    (fun bs be => exists marg,
      address_memarg_bounds marg /\
      bs = binary_of_be (constructor marg) /\ be = constructor marg).

(** All 14 scalar load forms and all 9 scalar store forms, with arbitrary
    bounded offsets, explicit memory indices, alignments and suffixes.
    Ill-shaped core AST constructors with no Wasm binary production are not
    included (e.g. packed floating-point loads). *)
Theorem production_scalar_load_store_codecs :
  memarg_instruction_codec (fun n => parse_i32_load) (BI_load T_i32 None) /\
  memarg_instruction_codec (fun n => parse_i64_load) (BI_load T_i64 None) /\
  memarg_instruction_codec (fun n => parse_f32_load) (BI_load T_f32 None) /\
  memarg_instruction_codec (fun n => parse_f64_load) (BI_load T_f64 None) /\
  memarg_instruction_codec (fun n => parse_i32_load8_s) (BI_load T_i32 (Some (Tp_i8, SX_S))) /\
  memarg_instruction_codec (fun n => parse_i32_load8_u) (BI_load T_i32 (Some (Tp_i8, SX_U))) /\
  memarg_instruction_codec (fun n => parse_i32_load16_s) (BI_load T_i32 (Some (Tp_i16, SX_S))) /\
  memarg_instruction_codec (fun n => parse_i32_load16_u) (BI_load T_i32 (Some (Tp_i16, SX_U))) /\
  memarg_instruction_codec (fun n => parse_i64_load8_s) (BI_load T_i64 (Some (Tp_i8, SX_S))) /\
  memarg_instruction_codec (fun n => parse_i64_load8_u) (BI_load T_i64 (Some (Tp_i8, SX_U))) /\
  memarg_instruction_codec (fun n => parse_i64_load16_s) (BI_load T_i64 (Some (Tp_i16, SX_S))) /\
  memarg_instruction_codec (fun n => parse_i64_load16_u) (BI_load T_i64 (Some (Tp_i16, SX_U))) /\
  memarg_instruction_codec (fun n => parse_i64_load32_s) (BI_load T_i64 (Some (Tp_i32, SX_S))) /\
  memarg_instruction_codec (fun n => parse_i64_load32_u) (BI_load T_i64 (Some (Tp_i32, SX_U))) /\
  memarg_instruction_codec (fun n => parse_i32_store) (BI_store T_i32 None) /\
  memarg_instruction_codec (fun n => parse_i64_store) (BI_store T_i64 None) /\
  memarg_instruction_codec (fun n => parse_f32_store) (BI_store T_f32 None) /\
  memarg_instruction_codec (fun n => parse_f64_store) (BI_store T_f64 None) /\
  memarg_instruction_codec (fun n => parse_i32_store8) (BI_store T_i32 (Some Tp_i8)) /\
  memarg_instruction_codec (fun n => parse_i32_store16) (BI_store T_i32 (Some Tp_i16)) /\
  memarg_instruction_codec (fun n => parse_i64_store8) (BI_store T_i64 (Some Tp_i8)) /\
  memarg_instruction_codec (fun n => parse_i64_store16) (BI_store T_i64 (Some Tp_i16)) /\
  memarg_instruction_codec (fun n => parse_i64_store32) (BI_store T_i64 (Some Tp_i32)).
Proof.
  repeat split; intro n; apply production_scalar_memarg_body_complete.
Qed.

Definition index_instruction_codec (p : production_be_parser)
    (constructor : N -> basic_instruction) : Prop :=
  forall n, parser_complete (p n)
    (fun bs be => exists index,
      (index < 4294967296)%N /\
      bs = binary_of_be (constructor index) /\ be = constructor index).

Theorem production_memory_table_unary_codecs :
  index_instruction_codec (fun n => parse_memory_size) BI_memory_size /\
  index_instruction_codec (fun n => parse_memory_grow) BI_memory_grow /\
  index_instruction_codec (fun n => parse_table_get) BI_table_get /\
  index_instruction_codec (fun n => parse_table_set) BI_table_set.
Proof.
  repeat split; intro n; apply production_indexed_body_complete.
Qed.

Lemma production_assert_u32_complete opcode n :
  (opcode < 4294967296)%N ->
  parser_complete
    (@assert_u32 (SizedList Byte.byte) _ option _ _ _ _ _ _ n opcode)
    (fun bs value => bs = binary_of_u32 opcode /\ value = opcode).
Proof.
  intro Range. unfold assert_u32.
  eapply parser_complete_guardM; [apply production_u32_printed_complete|].
  intros bs value [Bytes ->].
  exists opcode; split.
  - split; [exact Range|exact Bytes].
  - now rewrite N.eqb_refl.
Qed.

Lemma production_two_indices_complete (constructor : N -> N -> basic_instruction) n :
  parser_complete
    ((constructor <$> (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n))
      <*> parse_u32_as_N)
    (fun bs be => exists first second,
      (first < 4294967296)%N /\ (second < 4294967296)%N /\
      bs = binary_of_u32 first ++ binary_of_u32 second /\
      be = constructor first second).
Proof.
  eapply parser_complete_app with
    (P := fun bs f => exists first,
      (first < 4294967296)%N /\ bs = binary_of_u32 first /\ f = constructor first)
    (Q := printed binary_of_u32 (fun second => (second < 4294967296)%N)).
  - apply production_mapped_immediate_complete.
    apply production_u32_printed_complete.
  - intros k lt. simpl. apply parser_complete_le_lower.
    apply production_u32_printed_complete.
  - intros bs be [first [second [First [Second [Bytes Value]]]]].
    exists (binary_of_u32 first), (binary_of_u32 second), (constructor first), second.
    split; [exact Bytes|].
    split; [exists first; auto|].
    split; [split; auto|exact Value].
Qed.

Theorem production_two_index_opcode_complete opcode
    (constructor : N -> N -> basic_instruction) n :
  parser_complete
    (exact_byte opcode &>
      ((constructor <$> (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n))
        <*> parse_u32_as_N))
    (fun bs be => exists first second,
      (first < 4294967296)%N /\ (second < 4294967296)%N /\
      bs = opcode :: (binary_of_u32 first ++ binary_of_u32 second) /\
      be = constructor first second).
Proof.
  eapply parser_complete_weaken.
  - apply production_opcode_complete. apply production_two_indices_complete.
  - intros bs be [first [second [First [Second [Bytes Value]]]]].
    exists (binary_of_u32 first ++ binary_of_u32 second); split; [exact Bytes|].
    exists first, second; auto.
Qed.

Lemma production_prefixed_body_complete subopcode n
    (p : Parser (SizedList Byte.byte) Byte.byte option basic_instruction n)
    (P : list Byte.byte -> basic_instruction -> Prop) :
  (subopcode < 4294967296)%N ->
  parser_complete p P ->
  parser_complete (exact_byte Byte.xfc &> assert_u32 subopcode &> p)
    (fun bs be => exists tail,
      bs = Byte.xfc :: (binary_of_u32 subopcode ++ tail) /\ P tail be).
Proof.
  intros Range Complete.
  change (parser_complete ((exact_byte Byte.xfc &> assert_u32 subopcode) &> p)
    (fun bs be => exists tail,
      bs = (Byte.xfc :: binary_of_u32 subopcode) ++ tail /\ P tail be)).
  apply production_prefix_complete with (first := subopcode).
  - eapply parser_complete_weaken.
    + apply production_opcode_complete. now apply production_assert_u32_complete.
    + intros bs value [Bytes Value].
      exists (binary_of_u32 subopcode); auto.
  - exact Complete.
Qed.

Theorem production_prefixed_index_complete subopcode
    (constructor : N -> basic_instruction) n :
  (subopcode < 4294967296)%N ->
  parser_complete
    (exact_byte Byte.xfc &> assert_u32 subopcode &>
      (constructor <$> (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n)))
    (fun bs be => exists index,
      (index < 4294967296)%N /\
      bs = Byte.xfc :: (binary_of_u32 subopcode ++ binary_of_u32 index) /\
      be = constructor index).
Proof.
  intro Range.
  eapply parser_complete_weaken.
  - apply production_prefixed_body_complete; [exact Range|].
    apply production_mapped_immediate_complete.
    apply production_u32_printed_complete.
  - intros bs be [index [Valid [Bytes Value]]].
    exists (binary_of_u32 index); split; [exact Bytes|].
    exists index; auto.
Qed.

Theorem production_prefixed_two_indices_complete subopcode
    (constructor : N -> N -> basic_instruction) n :
  (subopcode < 4294967296)%N ->
  parser_complete
    (exact_byte Byte.xfc &> assert_u32 subopcode &>
      ((constructor <$> (@parse_u32_as_N (SizedList Byte.byte) _ option _ _ _ n))
        <*> parse_u32_as_N))
    (fun bs be => exists first second,
      (first < 4294967296)%N /\ (second < 4294967296)%N /\
      bs = Byte.xfc :: (binary_of_u32 subopcode ++
        (binary_of_u32 first ++ binary_of_u32 second)) /\
      be = constructor first second).
Proof.
  intro Range.
  eapply parser_complete_weaken.
  - apply production_prefixed_body_complete; [exact Range|].
    apply production_two_indices_complete.
  - intros bs be [first [second [First [Second [Bytes Value]]]]].
    exists (binary_of_u32 first ++ binary_of_u32 second); split; [exact Bytes|].
    exists first, second; auto.
Qed.

Theorem production_memory_table_bulk_unary_codecs :
  index_instruction_codec (fun n => parse_memory_fill) BI_memory_fill /\
  index_instruction_codec (fun n => parse_table_grow) BI_table_grow /\
  index_instruction_codec (fun n => parse_table_size) BI_table_size /\
  index_instruction_codec (fun n => parse_table_fill) BI_table_fill.
Proof.
  repeat split; intro n.
  all: apply production_prefixed_index_complete; vm_compute; reflexivity.
Qed.

Definition two_index_instruction_codec (p : production_be_parser)
    (constructor : N -> N -> basic_instruction) : Prop :=
  forall n, parser_complete (p n)
    (fun bs be => exists first second,
      (first < 4294967296)%N /\ (second < 4294967296)%N /\
      bs = binary_of_be (constructor first second) /\ be = constructor first second).

Theorem production_indirect_call_codecs :
  two_index_instruction_codec (fun n => parse_call_indirect)
    (fun typeidx tableidx => BI_call_indirect tableidx typeidx) /\
  two_index_instruction_codec (fun n => parse_return_call_indirect)
    (fun typeidx tableidx => BI_return_call_indirect tableidx typeidx).
Proof.
  repeat split; intro n; apply production_two_index_opcode_complete.
Qed.

Theorem production_memory_table_bulk_binary_codecs :
  two_index_instruction_codec (fun n => parse_memory_copy) BI_memory_copy /\
  two_index_instruction_codec (fun n => parse_table_copy) BI_table_copy /\
  two_index_instruction_codec (fun n => parse_memory_init)
    (fun dataidx memidx => BI_memory_init memidx dataidx) /\
  two_index_instruction_codec (fun n => parse_table_init)
    (fun elemidx tableidx => BI_table_init tableidx elemidx).
Proof.
  repeat split; intro n.
  all: apply production_prefixed_two_indices_complete; vm_compute; reflexivity.
Qed.
