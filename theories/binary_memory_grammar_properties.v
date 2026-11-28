(** Memory-owned adapters to the public parser_sound/parser_complete contracts
    audited at extended-const commits 1d15428 and ddb7f82.

    The contracts below are written out, rather than importing that branch's
    Addressing-dependent combinator layer. They are definitionally the same
    contracts (including arbitrary SizedList proofs and actual leftovers).
    No recursive language/section framework is defined here. *)
From Wasm Require Import datatypes binary_memory_properties binary_format_properties
  binary_parser_combinators binary_codec binary_format_parser.
From Stdlib Require Import List Strings.Byte NArith.
From parseque Require Import Parseque.

Lemma prefix_semantics_grammar_sound : forall A
  (p: byte_parser_family A) decode (Grammar: list byte -> A -> Prop),
  prefix_semantics p decode ->
  (forall input a suffix, decode input = Some (a, suffix) ->
    exists prefix, input = prefix ++ suffix /\ Grammar prefix a) ->
  forall n m (bound: (m <= n)%nat) (input: SizedList byte m) s,
    runParser (p n) bound input = Some s ->
    exists prefix,
      @Sized.value _ _ _ input =
        prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
      Grammar prefix (Success.value s).
Proof.
  intros A p decode Grammar Hp Hgrammar n m bound [input Hsize] s Run.
  cbn in Hsize. subst m.
  rewrite sized_list_refl in Run.
  pose proof (Hp n input bound) as H.
  rewrite Run in H. cbn [observe_prefix] in H.
  symmetry in H. exact (Hgrammar _ _ _ H).
Qed.

Lemma prefix_semantics_grammar_complete : forall A
  (p: byte_parser_family A) decode (Grammar: list byte -> A -> Prop),
  prefix_semantics p decode ->
  (forall prefix a, Grammar prefix a ->
    forall suffix, decode (prefix ++ suffix) = Some (a, suffix)) ->
  forall n m (bound: (m <= n)%nat) (input: SizedList byte m)
    prefix suffix a,
    @Sized.value _ _ _ input = prefix ++ suffix ->
    Grammar prefix a ->
    exists s, runParser (p n) bound input = Some s /\
      Success.value s = a /\
      @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  intros A p decode Grammar Hp Hgrammar n m bound [input Hsize]
    prefix suffix a Bytes Encoding.
  cbn in Hsize, Bytes. subst input.
  subst m. rewrite sized_list_refl.
  pose proof (Hp n (prefix ++ suffix) bound) as H.
  rewrite (Hgrammar prefix a Encoding suffix) in H.
  destruct (runParser (p n) bound (mkSizedList (prefix ++ suffix)))
    as [s|] eqn:Run; [|discriminate].
  cbn [observe_prefix] in H. inversion H.
  exists s. auto.
Qed.

Theorem parse_u32_binary_sound : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) s,
  runParser (parse_u32_as_N:
    Parser (SizedList byte) byte option N n) bound input = Some s ->
  exists prefix, @Sized.value _ _ _ input =
    prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
    binary_u32 prefix (Success.value s).
Proof.
  apply (prefix_semantics_grammar_sound N (fun n => parse_u32_as_N)
    (decode_uint 32 5) binary_u32).
  - apply prefix_u32.
  - intros input a suffix H. now apply decode_u32_spec in H.
Qed.

Theorem parse_u32_binary_complete : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) prefix suffix a,
  @Sized.value _ _ _ input = prefix ++ suffix ->
  binary_u32 prefix a ->
  exists s, runParser (parse_u32_as_N:
    Parser (SizedList byte) byte option N n) bound input = Some s /\
    Success.value s = a /\
    @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  apply (prefix_semantics_grammar_complete N (fun n => parse_u32_as_N)
    (decode_uint 32 5) binary_u32).
  - apply prefix_u32.
  - intros prefix a H suffix. apply decode_u32_spec. exists prefix. auto.
Qed.

Theorem parse_memarg_binary_sound : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) s,
  runParser (parse_memarg:
    Parser (SizedList byte) byte option memarg n) bound input = Some s ->
  exists prefix, @Sized.value _ _ _ input =
    prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
    binary_memarg prefix (Success.value s).
Proof.
  apply (prefix_semantics_grammar_sound memarg (fun n => parse_memarg)
    decode_memarg binary_memarg).
  - apply parse_memarg_prefix_correct.
  - apply decode_memarg_sound.
Qed.

Theorem parse_memarg_binary_complete : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) prefix suffix a,
  @Sized.value _ _ _ input = prefix ++ suffix ->
  binary_memarg prefix a ->
  exists s, runParser (parse_memarg:
    Parser (SizedList byte) byte option memarg n) bound input = Some s /\
    Success.value s = a /\
    @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  apply (prefix_semantics_grammar_complete memarg (fun n => parse_memarg)
    decode_memarg binary_memarg).
  - apply parse_memarg_prefix_correct.
  - apply decode_memarg_complete.
Qed.

Lemma decode_exact_byte_success : forall tag input b suffix,
  decode_exact_byte tag input = Some (b, suffix) ->
  input = tag :: suffix /\ b = tag.
Proof.
  intros tag [|head rest] b suffix H; [discriminate|].
  unfold decode_exact_byte in H.
  destruct (Byte.eqb head tag) eqn:Heq; [|discriminate].
  apply Byte.byte_dec_bl in Heq. inversion H; subst. auto.
Qed.

Definition binary_scalar_memory op bytes be :=
  exists args marg, bytes = scalar_memop_tag op :: args /\
    binary_memarg args marg /\ be = scalar_memop_build op marg.

Lemma decode_scalar_memory_sound : forall op input be suffix,
  decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op) input =
    Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_scalar_memory op prefix be.
Proof.
  intros op input be suffix H. unfold decode_tagged_memarg in H.
  destruct (decode_exact_byte (scalar_memop_tag op) input)
    as [[b rest]|] eqn:Htag; [|discriminate].
  apply decode_exact_byte_success in Htag. destruct Htag as [-> _].
  destruct (decode_memarg rest) as [[marg tail]|] eqn:Hargs; [|discriminate].
  inversion H; subst be tail.
  apply decode_memarg_sound in Hargs. destruct Hargs as [args [-> Encoding]].
  exists (scalar_memop_tag op :: args). split; [reflexivity|].
  exists args, marg. auto.
Qed.

Lemma decode_scalar_memory_complete : forall op prefix be,
  binary_scalar_memory op prefix be ->
  forall suffix,
  decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op)
    (prefix ++ suffix) = Some (be, suffix).
Proof.
  intros op prefix be [args [marg [-> [Encoding ->]]]] suffix.
  unfold decode_tagged_memarg, decode_exact_byte.
  cbn [List.app].
  rewrite (Byte.byte_dec_lb (eq_refl (scalar_memop_tag op))).
  rewrite (decode_memarg_complete args marg Encoding suffix). reflexivity.
Qed.

Theorem scalar_memop_binary_sound : forall op n m (bound: (m <= n)%nat)
  (input: SizedList byte m) s,
  runParser (scalar_memop_parser op n) bound input = Some s ->
  exists prefix, @Sized.value _ _ _ input =
    prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
    binary_scalar_memory op prefix (Success.value s).
Proof.
  intros op.
  apply (prefix_semantics_grammar_sound basic_instruction (scalar_memop_parser op)
    (decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op))
    (binary_scalar_memory op)).
  - apply scalar_memop_prefix_correct.
  - apply decode_scalar_memory_sound.
Qed.

Theorem scalar_memop_binary_complete : forall op n m (bound: (m <= n)%nat)
  (input: SizedList byte m) prefix suffix a,
  @Sized.value _ _ _ input = prefix ++ suffix ->
  binary_scalar_memory op prefix a ->
  exists s, runParser (scalar_memop_parser op n) bound input = Some s /\
    Success.value s = a /\
    @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  intros op.
  apply (prefix_semantics_grammar_complete basic_instruction (scalar_memop_parser op)
    (decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op))
    (binary_scalar_memory op)).
  - apply scalar_memop_prefix_correct.
  - apply decode_scalar_memory_complete.
Qed.

Inductive binary_indexed_memory : indexed_memop -> list byte -> basic_instruction -> Prop :=
| BIM_size : forall args x, binary_u32 args x ->
    binary_indexed_memory IM_size (x3f :: args) (BI_memory_size x)
| BIM_grow : forall args x, binary_u32 args x ->
    binary_indexed_memory IM_grow (x40 :: args) (BI_memory_grow x)
| BIM_fill : forall code args x, binary_u32 code 11 -> binary_u32 args x ->
    binary_indexed_memory IM_fill (xfc :: code ++ args) (BI_memory_fill x)
| BIM_copy : forall code dest src x y,
    binary_u32 code 10 -> binary_u32 dest x -> binary_u32 src y ->
    binary_indexed_memory IM_copy (xfc :: code ++ dest ++ src) (BI_memory_copy x y)
| BIM_init : forall code data mem x y,
    binary_u32 code 8 -> binary_u32 data y -> binary_u32 mem x ->
    binary_indexed_memory IM_init (xfc :: code ++ data ++ mem) (BI_memory_init x y)
| BIM_drop : forall code args x, binary_u32 code 9 -> binary_u32 args x ->
    binary_indexed_memory IM_drop (xfc :: code ++ args) (BI_data_drop x).

Lemma decode_assert_u32_sound : forall k input v suffix,
  decode_assert_u32 k input = Some (v, suffix) ->
  v = k /\ exists prefix, input = prefix ++ suffix /\ binary_u32 prefix k.
Proof.
  intros k input v suffix H. unfold decode_assert_u32 in H.
  destruct (decode_uint 32 5 input) as [[x tail]|] eqn:Hu; [|discriminate].
  destruct (N.eqb x k) eqn:Heq; [|discriminate].
  apply N.eqb_eq in Heq. subst x. inversion H; subst.
  split; [reflexivity|]. now apply decode_u32_spec.
Qed.

Lemma decode_fc_prefix_sound : forall k input v suffix,
  decode_fc_prefix k input = Some (v, suffix) ->
  exists code, input = (xfc :: code) ++ suffix /\ binary_u32 code k.
Proof.
  intros k input v suffix H. unfold decode_fc_prefix, decode_sequence in H.
  destruct (decode_exact_byte xfc input) as [[b rest]|] eqn:Htag;
    [|discriminate].
  apply decode_exact_byte_success in Htag. destruct Htag as [-> _].
  apply decode_assert_u32_sound in H. destruct H as [_ [code [-> Encoding]]].
  exists code. auto.
Qed.

Lemma decode_one_index_sound : forall (build: N -> basic_instruction) input be suffix,
  decode_map build (decode_uint 32 5) input = Some (be, suffix) ->
  exists args x, input = args ++ suffix /\ binary_u32 args x /\ be = build x.
Proof.
  intros build input be suffix H. unfold decode_map in H.
  destruct (decode_uint 32 5 input) as [[x tail]|] eqn:Hu; [|discriminate].
  inversion H; subst be tail. apply decode_u32_spec in Hu.
  destruct Hu as [args [-> Encoding]]. exists args, x. auto.
Qed.

Lemma decode_two_indices_sound : forall (build: N -> N -> basic_instruction) input be suffix,
  decode_two_indices build input = Some (be, suffix) ->
  exists first second x y, input = (first ++ second) ++ suffix /\
    binary_u32 first x /\ binary_u32 second y /\ be = build x y.
Proof.
  intros build input be suffix H. unfold decode_two_indices, decode_map in H.
  destruct (decode_uint 32 5 input) as [[x rest]|] eqn:Hx; [|discriminate].
  cbn -[decode_uint] in H.
  destruct (decode_uint 32 5 rest) as [[y tail]|] eqn:Hy; [|discriminate].
  inversion H; subst be tail. apply decode_u32_spec in Hx, Hy.
  destruct Hx as [first [-> Ex]]. destruct Hy as [second [-> Ey]].
  exists first, second, x, y. split; [apply List.app_assoc|auto].
Qed.

Lemma decode_indexed_memory_sound : forall op input be suffix,
  decode_indexed_memop op input = Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_indexed_memory op prefix be.
Proof.
  intros op input be suffix H.
  destruct op; cbn [decode_indexed_memop decode_sequence] in H.
  all: unfold decode_sequence in H.
  all: lazymatch type of H with
  | context [decode_exact_byte ?tag ?stream] =>
      destruct (decode_exact_byte tag stream) as [[b rest]|] eqn:Hhead;
      [apply decode_exact_byte_success in Hhead; destruct Hhead as [-> _]|discriminate]
  | context [decode_fc_prefix ?k ?stream] =>
      destruct (decode_fc_prefix k stream) as [[b rest]|] eqn:Hhead;
      [apply decode_fc_prefix_sound in Hhead;
        destruct Hhead as [code [-> Ecode]]|discriminate]
  end.
  all: first
    [apply decode_one_index_sound in H; destruct H as [args [x [-> [Ex ->]]]]
    |apply decode_two_indices_sound in H;
      destruct H as [first [second [x [y [-> [Ex [Ey ->]]]]]]]].
  - exists (x3f :: args). split; [reflexivity|now constructor].
  - exists (x40 :: args). split; [reflexivity|now constructor].
  - exists (xfc :: code ++ args). split.
    + cbn. now rewrite List.app_assoc.
    + now constructor.
  - exists (xfc :: code ++ first ++ second). split.
    + cbn. now repeat rewrite List.app_assoc.
    + now constructor.
  - exists (xfc :: code ++ first ++ second). split.
    + cbn. now repeat rewrite List.app_assoc.
    + now constructor.
  - exists (xfc :: code ++ args). split.
    + cbn. now rewrite List.app_assoc.
    + now constructor.
Qed.

Lemma binary_u32_decode_suffix : forall bytes x,
  binary_u32 bytes x ->
  forall suffix, decode_uint 32 5 (bytes ++ suffix) = Some (x, suffix).
Proof. intros bytes x H suffix. apply decode_u32_spec. exists bytes. auto. Qed.

Lemma decode_indexed_memory_complete : forall op prefix be,
  binary_indexed_memory op prefix be ->
  forall suffix, decode_indexed_memop op (prefix ++ suffix) = Some (be, suffix).
Proof.
  intros op prefix be Encoding suffix. destruct Encoding;
    unfold decode_indexed_memop, decode_sequence, decode_fc_prefix,
      decode_assert_u32, decode_two_indices, decode_map, decode_exact_byte;
    cbn -[decode_uint].
  all: repeat rewrite <- List.app_assoc.
  all: repeat match goal with
  | E: binary_u32 ?bs ?v |- context [decode_uint 32 5 (?bs ++ ?rest)] =>
      rewrite (binary_u32_decode_suffix bs v E rest); cbn -[decode_uint]
  end.
  all: reflexivity.
Qed.

Theorem indexed_memop_binary_sound : forall op n m (bound: (m <= n)%nat)
  (input: SizedList byte m) s,
  runParser (indexed_memop_parser op n) bound input = Some s ->
  exists prefix, @Sized.value _ _ _ input =
    prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
    binary_indexed_memory op prefix (Success.value s).
Proof.
  intros op.
  apply (prefix_semantics_grammar_sound basic_instruction (indexed_memop_parser op)
    (decode_indexed_memop op) (binary_indexed_memory op)).
  - apply indexed_memop_prefix_correct.
  - apply decode_indexed_memory_sound.
Qed.

Theorem indexed_memop_binary_complete : forall op n m (bound: (m <= n)%nat)
  (input: SizedList byte m) prefix suffix a,
  @Sized.value _ _ _ input = prefix ++ suffix ->
  binary_indexed_memory op prefix a ->
  exists s, runParser (indexed_memop_parser op n) bound input = Some s /\
    Success.value s = a /\
    @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  intros op.
  apply (prefix_semantics_grammar_complete basic_instruction (indexed_memop_parser op)
    (decode_indexed_memop op) (binary_indexed_memory op)).
  - apply indexed_memop_prefix_correct.
  - apply decode_indexed_memory_complete.
Qed.

Inductive binary_vector_memory : list byte -> basic_instruction -> Prop :=
| BVM_memarg : forall opbytes code args build marg,
    binary_u32 opbytes code ->
    vector_memory_opcode code = Some (VMI_memarg build) ->
    binary_memarg args marg ->
    binary_vector_memory (xfd :: opbytes ++ args) (build marg)
| BVM_lane : forall opbytes code args build marg lane,
    binary_u32 opbytes code ->
    vector_memory_opcode code = Some (VMI_lane build) ->
    binary_memarg args marg ->
    binary_vector_memory (xfd :: opbytes ++ args ++ lane :: nil)
      (build marg (Byte.to_N lane)).

Lemma decode_vector_memory_sound : forall input be suffix,
  decode_vector_memory input = Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_vector_memory prefix be.
Proof.
  intros input be suffix H. unfold decode_vector_memory, decode_sequence in H.
  destruct (decode_exact_byte xfd input) as [[b rest]|] eqn:Htag;
    [|discriminate].
  apply decode_exact_byte_success in Htag. destruct Htag as [-> _].
  destruct (decode_uint 32 5 rest) as [[code tail]|] eqn:Hcode; [|discriminate].
  unfold decode_vector_memory_tail in H.
  destruct (vector_memory_opcode code) as [[build|build]|] eqn:Hop;
    [| |discriminate].
  - unfold decode_map in H.
    destruct (decode_memarg tail) as [[marg after]|] eqn:Hargs; [|discriminate].
    inversion H; subst be after.
    apply decode_u32_spec in Hcode. destruct Hcode as [opbytes [-> Ecode]].
    apply decode_memarg_sound in Hargs. destruct Hargs as [args [-> Eargs]].
    exists (xfd :: opbytes ++ args). split.
    + cbn. now rewrite List.app_assoc.
    + eapply BVM_memarg; eassumption.
  - unfold decode_map in H.
    destruct (decode_memarg tail) as [[marg after]|] eqn:Hargs; [|discriminate].
    cbn -[decode_laneidx] in H.
    destruct after as [|lane after]; [discriminate|].
    cbn [decode_laneidx] in H. inversion H; subst be after.
    apply decode_u32_spec in Hcode. destruct Hcode as [opbytes [-> Ecode]].
    apply decode_memarg_sound in Hargs. destruct Hargs as [args [-> Eargs]].
    exists (xfd :: opbytes ++ args ++ lane :: nil). split.
    + cbn. repeat rewrite <- List.app_assoc. reflexivity.
    + eapply BVM_lane; eassumption.
Qed.

Lemma decode_vector_memory_complete : forall prefix be,
  binary_vector_memory prefix be ->
  forall suffix, decode_vector_memory (prefix ++ suffix) = Some (be, suffix).
Proof.
  intros prefix be Encoding suffix. destruct Encoding;
    unfold decode_vector_memory, decode_sequence, decode_exact_byte;
    cbn [List.app].
  all: rewrite (Byte.byte_dec_lb (eq_refl xfd)).
  all: repeat rewrite <- List.app_assoc.
  all: rewrite (binary_u32_decode_suffix opbytes code H).
  all: unfold decode_vector_memory_tail; rewrite H0; unfold decode_map.
  - rewrite (decode_memarg_complete args marg H1 suffix). reflexivity.
  - cbn [List.app].
    rewrite (decode_memarg_complete args marg H1 (lane :: suffix)).
    reflexivity.
Qed.

Theorem vector_memory_binary_sound : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) s,
  runParser (parse_vector_memory_instruction:
    Parser (SizedList byte) byte option basic_instruction n) bound input = Some s ->
  exists prefix, @Sized.value _ _ _ input =
    prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
    binary_vector_memory prefix (Success.value s).
Proof.
  apply (prefix_semantics_grammar_sound basic_instruction
    (fun n => parse_vector_memory_instruction)
    decode_vector_memory binary_vector_memory).
  - apply vector_memory_prefix_correct.
  - apply decode_vector_memory_sound.
Qed.

Theorem vector_memory_binary_complete : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) prefix suffix a,
  @Sized.value _ _ _ input = prefix ++ suffix ->
  binary_vector_memory prefix a ->
  exists s, runParser (parse_vector_memory_instruction:
    Parser (SizedList byte) byte option basic_instruction n) bound input = Some s /\
    Success.value s = a /\
    @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  apply (prefix_semantics_grammar_complete basic_instruction
    (fun n => parse_vector_memory_instruction)
    decode_vector_memory binary_vector_memory).
  - apply vector_memory_prefix_correct.
  - apply decode_vector_memory_complete.
Qed.

(** Independent byte grammar for the entire production memory alternative.
    Opcode ULEBs and memargs admit noncanonical encodings. Alignment/lane
    validation is deliberately not imposed by this binary syntax judgment. *)
Inductive binary_memory_instruction : list byte -> basic_instruction -> Prop :=
| BMI_scalar : forall op bytes be,
    binary_scalar_memory op bytes be -> binary_memory_instruction bytes be
| BMI_indexed : forall op bytes be,
    binary_indexed_memory op bytes be -> binary_memory_instruction bytes be
| BMI_vector : forall bytes be,
    binary_vector_memory bytes be -> binary_memory_instruction bytes be.

Lemma decode_or_grammar_sound : forall A
  (p q: list byte -> option (A * list byte)) Grammar,
  (forall input a suffix, p input = Some (a, suffix) ->
    exists prefix, input = prefix ++ suffix /\ Grammar prefix a) ->
  (forall input a suffix, q input = Some (a, suffix) ->
    exists prefix, input = prefix ++ suffix /\ Grammar prefix a) ->
  forall input a suffix, decode_or p q input = Some (a, suffix) ->
    exists prefix, input = prefix ++ suffix /\ Grammar prefix a.
Proof.
  intros A p q Grammar Hp Hq input a suffix H. unfold decode_or in H.
  destruct (p input) as [[x tail]|] eqn:Hpinput.
  - inversion H; subst. now apply Hp.
  - now apply Hq.
Qed.

Lemma memory_scalar_decoder_sound : forall op input be suffix,
  decode_tagged_memarg (scalar_memop_tag op) (scalar_memop_build op) input =
    Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_memory_instruction prefix be.
Proof.
  intros op input be suffix H.
  apply decode_scalar_memory_sound in H. destruct H as [prefix [Bytes E]].
  exists prefix. split; [exact Bytes|now apply BMI_scalar with (op := op)].
Qed.

Lemma memory_indexed_decoder_sound : forall op input be suffix,
  decode_indexed_memop op input = Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_memory_instruction prefix be.
Proof.
  intros op input be suffix H.
  apply decode_indexed_memory_sound in H. destruct H as [prefix [Bytes E]].
  exists prefix. split; [exact Bytes|now apply BMI_indexed with (op := op)].
Qed.

Lemma memory_vector_decoder_sound : forall input be suffix,
  decode_vector_memory input = Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_memory_instruction prefix be.
Proof.
  intros input be suffix H.
  apply decode_vector_memory_sound in H. destruct H as [prefix [Bytes E]].
  exists prefix. split; [exact Bytes|now apply BMI_vector].
Qed.

Theorem decode_memory_instruction_sound : forall input be suffix,
  decode_memory_instruction input = Some (be, suffix) ->
  exists prefix, input = prefix ++ suffix /\ binary_memory_instruction prefix be.
Proof.
  unfold decode_memory_instruction, scalar_memops.
  cbn [List.map List.app List.fold_right].
  do 23 (apply decode_or_grammar_sound; [apply memory_scalar_decoder_sound|]).
  apply decode_or_grammar_sound; [apply memory_vector_decoder_sound|].
  apply decode_or_grammar_sound; [apply (memory_indexed_decoder_sound IM_size)|].
  apply decode_or_grammar_sound; [apply (memory_indexed_decoder_sound IM_grow)|].
  apply decode_or_grammar_sound; [apply (memory_indexed_decoder_sound IM_init)|].
  apply decode_or_grammar_sound; [apply (memory_indexed_decoder_sound IM_drop)|].
  apply decode_or_grammar_sound; [apply (memory_indexed_decoder_sound IM_copy)|].
  apply (memory_indexed_decoder_sound IM_fill).
Qed.

Theorem decode_memory_instruction_complete : forall prefix be,
  binary_memory_instruction prefix be ->
  forall suffix, decode_memory_instruction (prefix ++ suffix) = Some (be, suffix).
Proof.
  intros prefix be Encoding suffix. destruct Encoding as [op bytes be E|op bytes be E|bytes be E].
  { destruct E as [args [marg [-> [Eargs ->]]]].
    destruct op; unfold decode_memory_instruction, scalar_memops, decode_or,
      decode_tagged_memarg, decode_exact_byte;
      cbn -[decode_memarg decode_uint];
      rewrite (decode_memarg_complete args marg Eargs suffix); reflexivity. }
  { destruct E; unfold decode_memory_instruction, scalar_memops, decode_or,
      decode_tagged_memarg, decode_exact_byte;
      cbn -[decode_uint].
    all: unfold decode_indexed_memop, decode_vector_memory, decode_fc_prefix,
      decode_sequence, decode_assert_u32, decode_two_indices, decode_map.
    all: cbn -[decode_uint].
    all: repeat rewrite <- List.app_assoc.
    all: repeat match goal with
    | E: binary_u32 ?bs ?v |- context [decode_uint 32 5 (?bs ++ ?rest)] =>
        rewrite (binary_u32_decode_suffix bs v E rest); cbn -[decode_uint]
    end.
    all: reflexivity. }
  { pose proof (decode_vector_memory_complete bytes be E suffix) as Hvec.
    destruct E; cbn [List.app] in Hvec;
      unfold decode_memory_instruction, scalar_memops, decode_or,
        decode_tagged_memarg, decode_exact_byte;
      cbn -[decode_vector_memory decode_memarg decode_uint].
    all: rewrite Hvec; reflexivity. }
Qed.

(** These two statements are exactly the extended-const public
    [parser_sound]/[parser_complete] contracts after unfolding their byte
    projection abbreviations. Use [parser_sound_weaken] to inject this grammar
    into the shared Atom judgment; no recursive grammar premises are assumed. *)
Theorem parse_memory_instruction_binary_sound : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) s,
  runParser (parse_memory_instruction:
    Parser (SizedList byte) byte option basic_instruction n) bound input = Some s ->
  exists prefix, @Sized.value _ _ _ input =
    prefix ++ @Sized.value _ _ _ (Success.leftovers s) /\
    binary_memory_instruction prefix (Success.value s).
Proof.
  apply (prefix_semantics_grammar_sound basic_instruction
    (fun n => parse_memory_instruction)
    decode_memory_instruction binary_memory_instruction).
  - apply memory_instruction_prefix_correct.
  - apply decode_memory_instruction_sound.
Qed.

Theorem parse_memory_instruction_binary_complete : forall n m (bound: (m <= n)%nat)
  (input: SizedList byte m) prefix suffix a,
  @Sized.value _ _ _ input = prefix ++ suffix ->
  binary_memory_instruction prefix a ->
  exists s, runParser (parse_memory_instruction:
    Parser (SizedList byte) byte option basic_instruction n) bound input = Some s /\
    Success.value s = a /\
    @Sized.value _ _ _ (Success.leftovers s) = suffix.
Proof.
  apply (prefix_semantics_grammar_complete basic_instruction
    (fun n => parse_memory_instruction)
    decode_memory_instruction binary_memory_instruction).
  - apply memory_instruction_prefix_correct.
  - apply decode_memory_instruction_complete.
Qed.
