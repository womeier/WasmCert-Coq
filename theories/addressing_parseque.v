(** Connection between the bounded binary decoder and Parseque's actual
    token interface.  No parser-success proof is erased by hand: Parseque's
    [Success] record carries the strictly smaller remainder.

    [decode_address_tokens_correct] connects executable token decoding to
    [AddressingBinary.decode_address], whose byte grammar is proved separately.
    It covers both the decoded value and every unconsumed byte. *)
From Wasm Require Import addressing addressing_binary.
From parseque Require Import Parseque.
From Stdlib Require Import Strings.Byte NArith List PeanoNat Eqdep_dec.
Import Addressing AddressingBinary.

Module AddressingParseque.

Section Tokens.
Context {Toks: nat -> Type} `{Sized Toks byte}.

Fixpoint decode_uleb_tokens (fuel: nat) {n} (input: Toks n)
    : option (Success.Success Toks byte N n) :=
  match fuel with
  | O => None
  | S fuel' =>
      match Success.getTok input with
      | None => None
      | Some first =>
          let digit := Byte.to_N (Success.value first) in
          if N.ltb digit 128 then
            Some (Success.map Byte.to_N first)
          else
            match decode_uleb_tokens fuel' (Success.leftovers first) with
            | None => None
            | Some tail =>
                Some (Success.lt_lift (Success.small first)
                  (Success.map (fun k => (digit - 128 + 128 * k)%N) tail))
            end
      end
  end.

Definition decode_address_tokens (a: address_type) {n} (input: Toks n)
    : option (Success.Success Toks byte N n) :=
  match decode_uleb_tokens (address_bytes a) input with
  | None => None
  | Some result =>
      if N.ltb (Success.value result) (address_bound a)
      then Some result else None
  end.

End Tokens.

Definition flatten {n}
    (result: option (Success.Success (SizedList byte) byte N n))
    : option (N * list byte) :=
  option_map
    (fun s => (Success.value s,
      @Sized.value _ (@List.length byte) _ (Success.leftovers s))) result.

Lemma sized_list_refl input (p: List.length input = List.length input) :
  @Sized.MkSizedType (list byte) (@List.length byte) (List.length input)
    input p = mkSizedList input.
Proof.
  unfold mkSizedList. f_equal. apply UIP_dec. exact Nat.eq_dec.
Qed.

Lemma decode_uleb_tokens_correct fuel input :
  flatten (decode_uleb_tokens fuel (mkSizedList input)) =
    decode_uleb fuel input.
Proof.
  revert input.
  induction fuel as [|fuel IH]; intros input; [reflexivity |].
  destruct input as [|b input]; [reflexivity |].
  cbn [decode_uleb_tokens Success.getTok uncons sizedList listUncons mkSizedList List.length
    Success.fromView Success.map Success.value Success.size Success.leftovers
    Success.small uncurry flatten option_map decode_uleb].
  destruct (N.ltb (Byte.to_N b) 128) eqn:Hlast; [reflexivity |].
  rewrite sized_list_refl.
  specialize (IH input).
  unfold flatten in IH.
  destruct (decode_uleb_tokens fuel (mkSizedList input)) as [tail|] eqn:Htail.
  - cbn [option_map] in IH. rewrite <- IH.
    destruct tail. reflexivity.
  - cbn [option_map] in IH. rewrite <- IH. reflexivity.
Qed.

Lemma decode_address_tokens_correct a input :
  flatten (decode_address_tokens a (mkSizedList input)) =
    decode_address a input.
Proof.
  unfold decode_address_tokens, decode_address.
  pose proof (decode_uleb_tokens_correct (address_bytes a) input) as Hcorrect.
  unfold flatten in *.
  destruct (decode_uleb_tokens (address_bytes a) (mkSizedList input))
    as [result|] eqn:Hresult.
  - cbn [option_map] in Hcorrect.
    rewrite <- Hcorrect. destruct (N.ltb _ _); reflexivity.
  - cbn [option_map] in Hcorrect. now rewrite <- Hcorrect.
Qed.

Section Parser.
Context {Toks: nat -> Type} `{Sized Toks byte}
  {M: Type -> Type} `{RawAlternative M}.

Definition parse_address (a: address_type) {n} : Parser Toks byte M N n :=
  MkParser (fun _ _ input => fromOption (decode_address_tokens a input)).

End Parser.

Definition run_prefix (a: address_type) (input: list byte)
    : option (N * list byte) :=
  flatten (runParser
    (@parse_address (SizedList byte) (sizedList byte) option
      optionRawFunctor optionRawApplicative optionRawAlternative a
      (List.length input))
    (Nat.le_refl _) (mkSizedList input)).

Lemma run_prefix_correct a input :
  run_prefix a input = decode_address a input.
Proof.
  rewrite <- decode_address_tokens_correct.
  unfold run_prefix, parse_address, flatten.
  cbn [runParser].
  destruct (decode_address_tokens a (mkSizedList input)); reflexivity.
Qed.

Lemma run_prefix_spec a input n rest :
  run_prefix a input = Some (n, rest) <->
  (n < address_bound a)%N /\
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= address_bytes a)%nat /\
    unsigned_leb prefix n.
Proof. rewrite run_prefix_correct. apply decode_address_spec. Qed.

End AddressingParseque.
