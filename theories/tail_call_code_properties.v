(** Tail-call expression decoding inside function bodies with an empty local
    declaration vector. Suffix bytes and the ambient parser bound are arbitrary;
    this is a prefix theorem for the actual code-body parser. *)
From Stdlib Require Import List Strings.Byte NArith PeanoNat.
From parseque Require Import Parseque Success.
From Wasm Require Import datatypes_properties binary_format_parser
  binary_uleb128 tail_call_parser_properties tail_call_sequence_properties.

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
