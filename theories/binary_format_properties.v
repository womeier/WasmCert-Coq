(** Connections to the binary parser and printer extracted by the CLI. *)
From Wasm Require Import binary_codec binary_format_parser binary_format_printer datatypes_properties.
From Stdlib Require Import ZArith NArith Lia List Strings.Byte.
From parseque Require Import Parseque.

Theorem parse_u32_prefix_spec : forall bound input v suffix
  (Hbound: (List.length input <= bound)%nat),
  observe_prefix
    (runParser (@parse_u32_as_N (SizedList byte) (sizedList byte)
      option optionRawFunctor optionRawApplicative optionRawMonad
      optionRawFunctor optionRawApplicative optionRawAlternative bound) Hbound (mkSizedList input)) =
    Some (v, suffix) <->
  exists prefix,
    input = prefix ++ suffix /\
    (List.length prefix <= 5)%nat /\
    unsigned_leb prefix v /\ (v < u32_bound)%N.
Proof. intros. apply parse_uint_spec. Qed.

Theorem binary_u32_prefix_round_trip : forall v suffix bound
  (Hbound: (List.length (binary_of_u32 v ++ suffix) <= bound)%nat),
  (v < u32_bound)%N ->
  observe_prefix
    (runParser (@parse_u32_as_N (SizedList byte) (sizedList byte)
      option optionRawFunctor optionRawApplicative optionRawMonad
      optionRawFunctor optionRawApplicative optionRawAlternative bound) Hbound
      (mkSizedList (binary_of_u32 v ++ suffix))) = Some (v, suffix).
Proof.
  intros v suffix bound Hbound Hrange.
  unfold binary_of_u32 in *.
  destruct (N.ltb v u32_bound) eqn:Hlt.
  - apply parse_uint_encode_round_trip; try assumption; [lia|].
    unfold u32_bound in Hrange. cbn. lia.
  - apply N.ltb_ge in Hlt. lia.
Qed.

Lemma run_of_prefix : forall A
  (p: forall n, Parser (SizedList byte) byte option A n) input v,
  observe_prefix
    (runParser (p (List.length input)) (Nat.le_refl _) (mkSizedList input)) =
    Some (v, nil) ->
  binary_format_parser.run input p = Some v.
Proof.
  intros A p input v Hprefix.
  unfold binary_format_parser.run, fromText, tokenize.
  cbn.
  destruct (runParser (p (List.length input)) (Nat.le_refl _) (mkSizedList input))
    as [[value size Hsmall [rest Hsize]]|]; [|discriminate].
  unfold observe_prefix in Hprefix. simpl in Hprefix.
  inversion Hprefix; subst. reflexivity.
Qed.

Theorem binary_u32_run_round_trip : forall v,
  N.lt v u32_bound ->
  binary_format_parser.run (binary_of_u32 v) (fun n => @parse_u32_as_N
    (SizedList byte) (sizedList byte) option
    optionRawFunctor optionRawApplicative optionRawMonad
    optionRawFunctor optionRawApplicative optionRawAlternative n) = Some v.
Proof.
  intros v Hrange.
  rewrite <- (List.app_nil_r (binary_of_u32 v)).
  apply run_of_prefix.
  apply binary_u32_prefix_round_trip. exact Hrange.
Qed.
