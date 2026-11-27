(** Tail-call expression decoding inside function bodies with an empty local
    declaration vector. Suffix bytes and the ambient parser bound are arbitrary;
    this is a prefix theorem for the actual code-body parser. *)
From Stdlib Require Import List Strings.Byte NArith PeanoNat Lia.
From parseque Require Import Parseque Success.
From Wasm Require Import datatypes_properties binary_format_parser
  binary_format_printer binary_uleb128 binary_uleb128_printer
  binary_format_parser_properties tail_call_parser_properties
  tail_call_sequence_properties tail_call_codec_properties.

Lemma parse_code_func_tail_prefix : forall n opcode b input instruction suffix
    (Hle : (List.length (x00 :: opcode :: b :: input) <= n)%nat),
    opcode = x12 \/ opcode = x13 ->
    return_call_prefix (opcode :: b :: input) instruction (x0b :: suffix) \/
      return_call_indirect_prefix
        (opcode :: b :: input) instruction (x0b :: suffix) ->
    option_map observe_reader
      (runParser (parse_code_func :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
        Hle (mkSizedList (x00 :: opcode :: b :: input))) =
      Some ((nil, instruction :: nil), suffix).
Proof.
  intros n opcode b input instruction suffix Hle Hopcode Hgrammar.
  unfold parse_code_func, parse_vec.
  unfold Combinators.alt, Combinators.and, Combinators.andbind,
    Combinators.map, Combinators.cmap, exact_byte, Combinators.guardM.
  cbn [runParser anyTok Success.getTok sizedList uncons listUncons
    Success.fromView Success.guardM option_map uncurry Success.value
    Success.size Success.small Success.leftovers].
  unfold Combinators.map, Category.bind, Category.alt, Category.fmap,
    fromOption, Success.guardM.
  cbn [runParser anyTok Success.getTok sizedList uncons listUncons
    Success.fromView Success.guardM option_map uncurry Success.value
    Success.size Success.small Success.leftovers
    _bind _alt _fmap _pure _fail optionRawMonad optionRawAlternative
    optionRawFunctor optionRawApplicative pure fail].
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn -[parse_expr].
  match goal with
  | |- context [runParser ?parser ?bound ?tokens] =>
      pose proof (parse_expr_tail_prefix_sized n _ tokens
        opcode b input instruction suffix bound eq_refl Hopcode Hgrammar)
        as Hexpr;
      destruct (runParser parser bound tokens) as [result|] eqn:Hresult
  end; [|discriminate].
  destruct result as [body remaining Hsmall [rest Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hexpr.
  inversion Hexpr; subst body rest.
  reflexivity.
Qed.

Theorem parse_code_tail_prefix :
    forall n m (input : SizedList Byte.byte m)
      declared opcode b rest instruction suffix (Hle : (m <= n)%nat),
    u32_prefix (@Sized.value _ _ _ input) declared
      (x00 :: opcode :: b :: rest) ->
    declared =
      N.of_nat (List.length (x00 :: opcode :: b :: rest) - List.length suffix) ->
    opcode = x12 \/ opcode = x13 ->
    return_call_prefix (opcode :: b :: rest) instruction (x0b :: suffix) \/
      return_call_indirect_prefix
        (opcode :: b :: rest) instruction (x0b :: suffix) ->
    option_map observe_reader
      (runParser (parse_code :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
        Hle input) = Some ((nil, instruction :: nil), suffix).
Proof.
  intros n m input declared opcode b rest instruction suffix
    Hle Hheader Hdeclared Hopcode Hgrammar.
  pose proof (proj2 (parse_u32_as_N_correct n m Hle input declared
    (x00 :: opcode :: b :: rest)) Hheader) as Hhead.
  unfold parse_code, Combinators.bind, Combinators.andbind, Combinators.map.
  cbn [runParser].
  destruct (runParser (parse_u32_as_N :
    Parser (SizedList Byte.byte) Byte.byte option N n) Hle input)
    as [result|] eqn:Hraw; [|discriminate].
  destruct result as [value remaining Hsmall [tail Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hhead.
  inversion Hhead; subst value tail.
  cbn in Hlength. subst remaining.
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn -[assert_sized parse_code_func].
  assert (Hconstraint :
    N.eqb declared
      (N.of_nat (S (S (S (List.length rest))) - List.length suffix)) = true).
  { cbn [List.length] in Hdeclared.
    rewrite <- Hdeclared. apply N.eqb_refl. }
  match goal with
  | |- context [runParser (assert_sized ?parser ?constraint) ?bound ?tokens] =>
      pose proof (parse_code_func_tail_prefix n opcode b rest
        instruction suffix bound Hopcode Hgrammar) as Hbody;
      pose proof (assert_sized_correct _ n _ bound parser tokens
        (nil, instruction :: nil) suffix constraint Hbody Hconstraint) as Hassert;
      destruct (runParser (assert_sized parser constraint) bound tokens)
        as [body|] eqn:Hbody_parse
  end; [|discriminate].
  destruct body as [value remaining Hbody_small [tail Hbody_length]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hassert.
  inversion Hassert; subst value tail.
  reflexivity.
Qed.

Lemma parse_code_func_tail_prefix_sized :
    forall n m (input : SizedList Byte.byte m)
      opcode b rest instruction suffix (Hle : (m <= n)%nat),
    @Sized.value _ _ _ input = x00 :: opcode :: b :: rest ->
    opcode = x12 \/ opcode = x13 ->
    return_call_prefix (opcode :: b :: rest) instruction (x0b :: suffix) \/
      return_call_indirect_prefix
        (opcode :: b :: rest) instruction (x0b :: suffix) ->
    option_map observe_reader
      (runParser (parse_code_func :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
        Hle input) = Some ((nil, instruction :: nil), suffix).
Proof.
  intros n m [input Hlength] opcode b rest instruction suffix
    Hle Hinput Hopcode Hgrammar.
  cbn [Sized.value] in Hinput. subst input.
  subst m. now apply parse_code_func_tail_prefix.
Qed.

(** The zero local-vector length itself may have any permitted u32 padding. *)
Definition tail_body_prefix input instruction suffix :=
  exists payload,
    u32_prefix input 0 payload /\
    (return_call_prefix payload instruction (x0b :: suffix) \/
      return_call_indirect_prefix payload instruction (x0b :: suffix)).

Theorem parse_code_func_tail_prefix_general :
    forall n m (input : SizedList Byte.byte m) instruction suffix
      (Hle : (m <= n)%nat),
    tail_body_prefix (@Sized.value _ _ _ input) instruction suffix ->
    option_map observe_reader
      (runParser (parse_code_func :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
        Hle input) = Some ((nil, instruction :: nil), suffix).
Proof.
  intros n m input instruction suffix Hle [payload [Hlocals Hgrammar]].
  assert (Hvec :=
    parse_vec_zero_prefix _ n m Hle
      (parse_locals : Parser (SizedList Byte.byte) Byte.byte option
        (N * value_type) n) input payload Hlocals).
  destruct payload as [|opcode payload].
  { destruct Hgrammar as [H | H]; inversion H. }
  assert (Hopcode : opcode = x12 \/ opcode = x13).
  { destruct Hgrammar as [H | H]; inversion H; auto. }
  destruct payload as [|b rest].
  { destruct Hgrammar as [H | H]; inversion H; subst;
      match goal with
      | Hindex : u32_prefix nil _ _ |- _ =>
          destruct Hindex as [Hindex _]; inversion Hindex
      end. }
  unfold parse_code_func, Combinators.and, Combinators.andbind,
    Combinators.guardM; cbn [runParser].
  destruct (runParser (parse_vec parse_locals :
    Parser (SizedList Byte.byte) Byte.byte option (list (N * value_type)) n)
    Hle input) as [result|]; [|discriminate].
  destruct result as [locals remaining Hsmall [tail Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hvec.
  inversion Hvec; subst locals tail.
  cbn in Hlength. subst remaining.
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn -[parse_expr].
  match goal with
  | |- context [runParser ?parser ?bound ?tokens] =>
      pose proof (parse_expr_tail_prefix_sized n _ tokens
        opcode b rest instruction suffix bound eq_refl Hopcode Hgrammar)
        as Hexpr;
      change (option_map observe_reader (runParser parser bound tokens) =
        Some (instruction :: nil, suffix)) in Hexpr;
      destruct (runParser parser bound tokens) as [result|]
  end; [|discriminate].
  destruct result as [body remaining Hbody_small [tail Hbody_length]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hexpr.
  inversion Hexpr; subst body tail.
  reflexivity.
Qed.

Theorem parse_code_tail_prefix_general :
    forall n m (input : SizedList Byte.byte m)
      declared body instruction suffix (Hle : (m <= n)%nat),
    u32_prefix (@Sized.value _ _ _ input) declared body ->
    declared = N.of_nat (List.length body - List.length suffix) ->
    tail_body_prefix body instruction suffix ->
    option_map observe_reader
      (runParser (parse_code :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
        Hle input) = Some ((nil, instruction :: nil), suffix).
Proof.
  intros n m input declared body instruction suffix
    Hle Hheader Hdeclared Hgrammar.
  pose proof (proj2 (parse_u32_as_N_correct n m Hle input declared body)
    Hheader) as Hhead.
  unfold parse_code, Combinators.bind, Combinators.andbind, Combinators.map.
  cbn [runParser].
  destruct (runParser (parse_u32_as_N :
    Parser (SizedList Byte.byte) Byte.byte option N n) Hle input)
    as [result|]; [|discriminate].
  destruct result as [value remaining Hsmall [tail Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hhead.
  inversion Hhead; subst value tail.
  subst remaining.
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn -[assert_sized parse_code_func].
  assert (Hconstraint :
    N.eqb declared (N.of_nat (List.length body - List.length suffix)) = true).
  { rewrite <- Hdeclared. apply N.eqb_refl. }
  match goal with
  | |- context [runParser (assert_sized ?parser ?constraint) ?bound ?tokens] =>
      pose proof (parse_code_func_tail_prefix_general n _ tokens
        instruction suffix bound Hgrammar) as Hbody;
      pose proof (assert_sized_correct _ n _ bound parser tokens
        (nil, instruction :: nil) suffix constraint Hbody Hconstraint) as Hassert;
      destruct (runParser (assert_sized parser constraint) bound tokens)
        as [result|]
  end; [|discriminate].
  destruct result as [value remaining Hbody_small [tail Hbody_length]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hassert.
  inversion Hassert; subst value tail.
  reflexivity.
Qed.

Theorem parse_code_tail_wrong_size :
    forall n m (input : SizedList Byte.byte m)
      declared body instruction suffix (Hle : (m <= n)%nat),
    u32_prefix (@Sized.value _ _ _ input) declared body ->
    declared <> N.of_nat (List.length body - List.length suffix) ->
    tail_body_prefix body instruction suffix ->
    runParser (parse_code :
      Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
      Hle input = None.
Proof.
  intros n m input declared body instruction suffix
    Hle Hheader Hdeclared Hgrammar.
  pose proof (proj2 (parse_u32_as_N_correct n m Hle input declared body)
    Hheader) as Hhead.
  unfold parse_code, Combinators.bind, Combinators.andbind, Combinators.map.
  cbn [runParser].
  destruct (runParser (parse_u32_as_N :
    Parser (SizedList Byte.byte) Byte.byte option N n) Hle input)
    as [result|]; [|discriminate].
  destruct result as [value remaining Hsmall [tail Hlength]].
  cbn [observe_reader Success.value Success.leftovers Sized.value] in Hhead.
  inversion Hhead; subst value tail.
  subst remaining.
  cbn [Combinators.box le_close Combinators.le_lower call runParser].
  cbn -[assert_sized parse_code_func].
  assert (Hconstraint :
    N.eqb declared (N.of_nat (List.length body - List.length suffix)) = false).
  { now apply N.eqb_neq. }
  match goal with
  | |- context [runParser (assert_sized ?parser ?constraint) ?bound ?tokens] =>
      pose proof (parse_code_func_tail_prefix_general n _ tokens
        instruction suffix bound Hgrammar) as Hbody;
      rewrite (assert_sized_reject _ n _ bound parser tokens
        (nil, instruction :: nil) suffix constraint Hbody Hconstraint)
  end.
  reflexivity.
Qed.

Definition printable_tail_instruction instruction :=
  (exists index, instruction = BI_return_call index /\
    (index <= 4294967295)%N) \/
  (exists table type, instruction = BI_return_call_indirect table type /\
    (table <= 4294967295)%N /\ (type <= 4294967295)%N).

Lemma tail_instruction_print_prefix : forall instruction suffix,
    printable_tail_instruction instruction ->
    return_call_prefix (List.app (binary_of_be instruction) suffix)
      instruction suffix \/
    return_call_indirect_prefix (List.app (binary_of_be instruction) suffix)
      instruction suffix.
Proof.
  intros instruction suffix [[index [-> Hindex]] |
    [table [type [-> [Htable Htype]]]]].
  - left. now apply return_call_print_prefix.
  - right. now apply return_call_indirect_print_prefix.
Qed.

Lemma tail_instruction_print_length : forall instruction,
    printable_tail_instruction instruction ->
    (2 <= List.length (binary_of_be instruction) <= 11)%nat.
Proof.
  intros instruction [[index [-> Hindex]] |
    [table [type [-> [Htable Htype]]]]].
  - pose proof (binary_of_tailidx_length index Hindex).
    cbn [binary_of_be List.length]. lia.
  - pose proof (binary_of_tailidx_length table Htable).
    pose proof (binary_of_tailidx_length type Htype).
    cbn [binary_of_be List.length].
    rewrite List.app_length. lia.
Qed.

Lemma empty_locals_single_body_bytes : forall instruction,
    binary_of_code_func nil (instruction :: nil) =
      x00 :: List.app (binary_of_be instruction) (x0b :: nil).
Proof.
  intro instruction.
  unfold binary_of_code_func, binary_of_expr.
  cbn [List.map List.concat].
  rewrite List.app_nil_r.
  reflexivity.
Qed.

Lemma tail_body_print_prefix : forall instruction suffix,
    printable_tail_instruction instruction ->
    tail_body_prefix
      (List.app (binary_of_code_func nil (instruction :: nil)) suffix)
      instruction suffix.
Proof.
  intros instruction suffix Htail.
  rewrite empty_locals_single_body_bytes.
  cbn [List.app]. rewrite <- List.app_assoc.
  exists (List.app (binary_of_be instruction) (x0b :: suffix)).
  split.
  - split; [apply uleb_last; cbn; lia | lia].
  - now apply tail_instruction_print_prefix.
Qed.

Lemma tail_body_print_length : forall instruction,
    printable_tail_instruction instruction ->
    (4 <= List.length (binary_of_code_func nil (instruction :: nil)) <= 13)%nat.
Proof.
  intros instruction Htail.
  pose proof (tail_instruction_print_length instruction Htail).
  rewrite empty_locals_single_body_bytes.
  cbn [List.length]. rewrite List.app_length. cbn. lia.
Qed.

Theorem tail_code_print_prefix : forall n type instruction suffix
    (Hle : (List.length (List.app
      (binary_of_code (Build_module_func type nil (instruction :: nil))) suffix)
        <= n)%nat),
    printable_tail_instruction instruction ->
    option_map observe_reader
      (runParser (parse_code :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n)
        Hle (mkSizedList (List.app
          (binary_of_code (Build_module_func type nil (instruction :: nil)))
          suffix))) =
      Some ((nil, instruction :: nil), suffix).
Proof.
  intros n type instruction suffix Hle Htail.
  pose proof (tail_body_print_length instruction Htail) as Hlength.
  assert (Hbound :
    (N.of_nat (List.length (binary_of_code_func nil (instruction :: nil))) <=
      4294967295)%N) by lia.
  eapply parse_code_tail_prefix_general with
    (declared := N.of_nat
      (List.length (binary_of_code_func nil (instruction :: nil))))
    (body := List.app (binary_of_code_func nil (instruction :: nil)) suffix).
  - cbn [Sized.value mkSizedList binary_of_code modfunc_locals modfunc_body].
    unfold binary_of_code.
    cbn [modfunc_locals modfunc_body].
    rewrite <- List.app_assoc.
    now apply binary_of_tailidx_correct.
  - rewrite List.app_length, Nat.add_sub. reflexivity.
  - now apply tail_body_print_prefix.
Qed.

Theorem tail_code_roundtrip : forall type instruction,
    printable_tail_instruction instruction ->
    binary_format_parser.run
      (binary_of_code (Build_module_func type nil (instruction :: nil)))
      (fun n => (parse_code :
        Parser (SizedList Byte.byte) Byte.byte option module_func_without_type n))
      = Some (nil, instruction :: nil).
Proof.
  intros type instruction Htail.
  rewrite run_option_parser_characterization.
  pose proof (tail_code_print_prefix _ type instruction nil
    (Nat.le_refl _) Htail) as Hprefix.
  now rewrite List.app_nil_r in Hprefix.
Qed.
