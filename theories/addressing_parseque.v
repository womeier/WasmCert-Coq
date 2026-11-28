(** Connection between the bounded binary decoder and Parseque's actual
    token interface.  No parser-success proof is erased by hand: Parseque's
    [Success] record carries the strictly smaller remainder.

    [decode_address_tokens_correct] connects executable token decoding to
    [AddressingBinary.decode_address], whose byte grammar is proved separately.
    It covers both the decoded value and every unconsumed byte. *)
From Wasm Require Import datatypes operations addressing addressing_binary.
From parseque Require Import Parseque.
From Stdlib Require Import Strings.Byte NArith List PeanoNat Eqdep_dec.
Import Addressing AddressingBinary.

Module AddressingParseque.

Definition decode_reference_byte (b: byte) : option reference_type :=
  match b with x70 => Some T_funcref | x6f => Some T_externref | _ => None end.

Inductive reference_head : Type :=
| RH_compact : reference_type -> reference_head
| RH_explicit : bool -> reference_head.

Definition decode_reference_head (b: byte) : option reference_head :=
  match b with
  | x70 => Some (RH_compact T_funcref)
  | x6f => Some (RH_compact T_externref)
  | x63 => Some (RH_explicit true)
  | x64 => Some (RH_explicit false)
  | _ => None
  end.

Definition decode_reference_type (input: list byte) : option (reference_type * list byte) :=
  match input with
  | nil => None
  | b :: input =>
      match decode_reference_head b with
      | Some (RH_compact rt) => Some (rt, input)
      | Some (RH_explicit nullable) =>
          match input with
          | nil => None
          | h :: rest => option_map (fun rt => (Ref_type nullable (ref_heap rt), rest))
              (decode_reference_byte h)
          end
      | None => None
      end
  end.

Inductive reference_encoding : list byte -> reference_type -> list byte -> Prop :=
| reference_compact b rt rest :
    decode_reference_head b = Some (RH_compact rt) ->
    reference_encoding (b :: rest) rt rest
| reference_explicit b h nullable rt rest :
    decode_reference_head b = Some (RH_explicit nullable) ->
    decode_reference_byte h = Some rt ->
    reference_encoding (b :: h :: rest) (Ref_type nullable (ref_heap rt)) rest.

Lemma decode_reference_type_spec input rt rest :
  decode_reference_type input = Some (rt, rest) <-> reference_encoding input rt rest.
Proof.
  split.
  - destruct input as [|b input]; [discriminate|].
    cbn [decode_reference_type].
    destruct (decode_reference_head b) as [[elem|nullable]|] eqn:Hhead; try discriminate.
    + intros H; inversion H; subst. now constructor.
    + destruct input as [|h input]; [discriminate|].
      destruct (decode_reference_byte h) as [elem|] eqn:Hheap; [|discriminate].
      intros H; inversion H; subst. econstructor; eassumption.
  - intros H; destruct H; cbn [decode_reference_type]; rewrite H; try reflexivity.
    now rewrite H0.
Qed.

Definition decode_table_type (input: list byte)
    : option (datatypes.table_type * list byte) :=
  match decode_reference_type input with
  | None => None
  | Some (elem, input) =>
      option_map (fun '(a, lim, rest) =>
        ({| tt_limits := lim; tt_elem_type := elem; tt_address_type := a |}, rest))
        (decode_limits input)
  end.

Definition decode_memarg (input: list byte) : option (memarg * list byte) :=
  match decode_address AT_i32 input with
  | None => None
  | Some (flags, input) =>
      match decode_memarg_flags flags with
      | None => None
      | Some (align, explicit) =>
          let selected := if explicit then decode_address AT_i32 input
                          else Some (0%N, input) in
          match selected with
          | None => None
          | Some (memory, input) =>
              option_map (fun '(offset, rest) => (Build_memarg offset align memory, rest))
                (decode_address AT_i64 input)
          end
      end
  end.

Definition unsigned_prefix (a: address_type) input value rest : Prop :=
  (value < address_bound a)%N /\
  exists prefix, input = prefix ++ rest /\
    (List.length prefix <= address_bytes a)%nat /\ unsigned_leb prefix value.

Inductive memarg_encoding : list byte -> memarg -> list byte -> Prop :=
| memarg_default input flags middle align offset rest :
    unsigned_prefix AT_i32 input flags middle ->
    decode_memarg_flags flags = Some (align, false) ->
    unsigned_prefix AT_i64 middle offset rest ->
    memarg_encoding input (Build_memarg offset align 0%N) rest
| memarg_indexed input flags middle align memory after_memory offset rest :
    unsigned_prefix AT_i32 input flags middle ->
    decode_memarg_flags flags = Some (align, true) ->
    unsigned_prefix AT_i32 middle memory after_memory ->
    unsigned_prefix AT_i64 after_memory offset rest ->
    memarg_encoding input (Build_memarg offset align memory) rest.

Lemma decode_memarg_sound input marg rest :
  decode_memarg input = Some (marg, rest) -> memarg_encoding input marg rest.
Proof.
  unfold decode_memarg.
  destruct (decode_address AT_i32 input) as [[flags middle]|] eqn:Hflags; [|discriminate].
  destruct (decode_memarg_flags flags) as [[align explicit]|] eqn:Hflag; [|discriminate].
  apply decode_address_spec in Hflags.
  destruct explicit.
  - destruct (decode_address AT_i32 middle) as [[memory after_memory]|] eqn:Hmemory; [|discriminate].
    destruct (decode_address AT_i64 after_memory) as [[offset remaining]|] eqn:Hoffset; [|discriminate].
    intros H; inversion H; subst.
    eapply memarg_indexed with (flags := flags) (middle := middle)
      (after_memory := after_memory).
    + exact Hflags.
    + exact Hflag.
    + now apply decode_address_spec.
    + now apply decode_address_spec.
  - destruct (decode_address AT_i64 middle) as [[offset remaining]|] eqn:Hoffset; [|discriminate].
    intros H; inversion H; subst.
    eapply memarg_default with (flags := flags) (middle := middle).
    + exact Hflags.
    + exact Hflag.
    + now apply decode_address_spec.
Qed.

Lemma decode_memarg_complete input marg rest :
  memarg_encoding input marg rest -> decode_memarg input = Some (marg, rest).
Proof.
  intros Henc; destruct Henc as
    [input flags middle align offset rest Hflags Hflag Hoffset |
     input flags middle align memory after_memory offset rest Hflags Hflag Hmemory Hoffset];
    apply decode_address_spec in Hflags; apply decode_address_spec in Hoffset;
    unfold decode_memarg; rewrite Hflags, Hflag.
  - now rewrite Hoffset.
  - apply decode_address_spec in Hmemory. now rewrite Hmemory, Hoffset.
Qed.

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

Definition decode_limits_tokens {n} (input: Toks n)
    : option (Success.Success Toks byte (address_type * limits) n) :=
  match Success.getTok input with
  | None => None
  | Some flag =>
      match decode_limits_flag (Success.value flag) with
      | None => None
      | Some (a, has_max) =>
          match decode_address_tokens a (Success.leftovers flag) with
          | None => None
          | Some minimum =>
              if has_max then
                match decode_address_tokens a (Success.leftovers minimum) with
                | None => None
                | Some maximum =>
                    Some (Success.lt_lift (Success.small flag)
                      (Success.lt_lift (Success.small minimum)
                        (Success.map (fun upper =>
                          (a, {| lim_min := Success.value minimum;
                                 lim_max := Some upper |})) maximum)))
                end
              else Some (Success.lt_lift (Success.small flag)
                (Success.map (fun lower =>
                  (a, {| lim_min := lower; lim_max := None |})) minimum))
          end
      end
  end.

Definition decode_reference_type_tokens {n} (input: Toks n)
    : option (Success.Success Toks byte reference_type n) :=
  match Success.getTok input with
  | None => None
  | Some first =>
      match decode_reference_head (Success.value first) with
      | None => None
      | Some (RH_compact rt) => Some (Success.map (fun _ => rt) first)
      | Some (RH_explicit nullable) =>
          match Success.getTok (Success.leftovers first) with
          | None => None
          | Some heap =>
              match decode_reference_byte (Success.value heap) with
              | None => None
              | Some rt => Some (Success.lt_lift (Success.small first)
                  (Success.map (fun _ => Ref_type nullable (ref_heap rt)) heap))
              end
          end
      end
  end.

Definition decode_table_type_tokens {n} (input: Toks n)
    : option (Success.Success Toks byte datatypes.table_type n) :=
  match decode_reference_type_tokens input with
  | None => None
  | Some reference =>
          match decode_limits_tokens (Success.leftovers reference) with
          | None => None
          | Some lims =>
              Some (Success.lt_lift (Success.small reference)
                (Success.map (fun '(a, lim) =>
                  {| tt_limits := lim; tt_elem_type := Success.value reference; tt_address_type := a |}) lims))
          end
  end.

Definition decode_memarg_offset_tokens align memory {n} (input: Toks n)
    : option (Success.Success Toks byte memarg n) :=
  option_map (Success.map (fun offset => Build_memarg offset align memory))
    (decode_address_tokens AT_i64 input).

Definition decode_memarg_tokens {n} (input: Toks n)
    : option (Success.Success Toks byte memarg n) :=
  match decode_address_tokens AT_i32 input with
  | None => None
  | Some flags =>
      match decode_memarg_flags (Success.value flags) with
      | None => None
      | Some (align, explicit) =>
          if explicit then
            match decode_address_tokens AT_i32 (Success.leftovers flags) with
            | None => None
            | Some memory =>
                option_map (fun offset => Success.lt_lift (Success.small flags)
                  (Success.lt_lift (Success.small memory) offset))
                  (decode_memarg_offset_tokens align (Success.value memory) (Success.leftovers memory))
            end
          else option_map (Success.lt_lift (Success.small flags))
            (decode_memarg_offset_tokens align 0%N (Success.leftovers flags))
      end
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

Lemma decode_address_tokens_correct_sized a n (input: SizedList byte n) :
  flatten (decode_address_tokens a input) =
    decode_address a (@Sized.value _ (@List.length byte) _ input).
Proof.
  destruct input as [input Hsize]. simpl in Hsize. subst n.
  rewrite sized_list_refl. apply decode_address_tokens_correct.
Qed.

Definition flatten_limits {n}
    (result: option (Success.Success (SizedList byte) byte (address_type * limits) n))
    : option (address_type * limits * list byte) :=
  option_map
    (fun s => (fst (Success.value s), snd (Success.value s),
      @Sized.value _ (@List.length byte) _ (Success.leftovers s))) result.

Lemma decode_limits_tokens_correct input :
  flatten_limits (decode_limits_tokens (mkSizedList input)) =
    decode_limits input.
Proof.
  destruct input as [|flag input]; [reflexivity |].
  unfold decode_limits_tokens.
  cbn [decode_limits_tokens Success.getTok uncons sizedList listUncons mkSizedList List.length
    Success.fromView Success.value Success.size Success.leftovers
    Success.small uncurry decode_limits flatten_limits option_map].
  destruct (decode_limits_flag flag) as [[a has_max]|] eqn:Hflag; [|reflexivity].
  rewrite sized_list_refl.
  pose proof (decode_address_tokens_correct a input) as Hmin.
  unfold flatten in Hmin.
  destruct (decode_address_tokens a (mkSizedList input)) as [minimum|] eqn:Hminimum;
    cbn [option_map] in Hmin; rewrite <- Hmin; [|reflexivity].
  destruct has_max; [|reflexivity].
  pose proof (decode_address_tokens_correct_sized a (Success.size minimum)
    (Success.leftovers minimum)) as Hmax.
  unfold flatten in Hmax.
  destruct (decode_address_tokens a (Success.leftovers minimum)) as [maximum|] eqn:Hmaximum;
    cbn [option_map] in Hmax; rewrite <- Hmax; reflexivity.
Qed.

Definition flatten_table_type {n}
    (result: option (Success.Success (SizedList byte) byte datatypes.table_type n))
    : option (datatypes.table_type * list byte) :=
  option_map (fun s => (Success.value s,
    @Sized.value _ (@List.length byte) _ (Success.leftovers s))) result.

Definition flatten_reference_type {n}
    (result: option (Success.Success (SizedList byte) byte reference_type n))
    : option (reference_type * list byte) :=
  option_map (fun s => (Success.value s,
    @Sized.value _ (@List.length byte) _ (Success.leftovers s))) result.

Lemma decode_reference_type_tokens_correct input :
  flatten_reference_type (decode_reference_type_tokens (mkSizedList input)) =
    decode_reference_type input.
Proof.
  destruct input as [|b input]; [reflexivity|].
  unfold decode_reference_type_tokens.
  cbn [flatten_reference_type option_map decode_reference_type Success.getTok uncons
    sizedList listUncons mkSizedList List.length Success.fromView
    Success.value Success.size Success.leftovers Success.small uncurry].
  destruct (decode_reference_head b) as [[rt|nullable]|]; try reflexivity.
  destruct input as [|h rest]; [reflexivity|].
  unfold flatten_reference_type.
  rewrite sized_list_refl.
  cbn [option_map Success.getTok uncons sizedList listUncons mkSizedList List.length
    Success.fromView Success.value Success.size Success.leftovers Success.small uncurry].
  destruct (decode_reference_byte h); reflexivity.
Qed.

Lemma decode_limits_tokens_correct_sized n (input: SizedList byte n) :
  flatten_limits (decode_limits_tokens input) =
    decode_limits (@Sized.value _ (@List.length byte) _ input).
Proof.
  destruct input as [input Hsize]. simpl in Hsize. subst n.
  rewrite sized_list_refl. apply decode_limits_tokens_correct.
Qed.

Lemma decode_table_type_tokens_correct input :
  flatten_table_type (decode_table_type_tokens (mkSizedList input)) =
    decode_table_type input.
Proof.
  unfold decode_table_type_tokens, decode_table_type.
  pose proof (decode_reference_type_tokens_correct input) as Href.
  unfold flatten_reference_type in Href.
  destruct (decode_reference_type_tokens (mkSizedList input)) as [reference|];
    cbn [option_map] in Href; rewrite <- Href; [|reflexivity].
  pose proof (decode_limits_tokens_correct_sized (Success.size reference)
    (Success.leftovers reference)) as Hlimits.
  unfold flatten_limits in Hlimits.
  destruct (decode_limits_tokens (Success.leftovers reference)) as [lims|];
    cbn [option_map] in Hlimits; rewrite <- Hlimits; [|reflexivity].
  destruct lims as [[a lim] size small rest]. reflexivity.
Qed.

Definition flatten_memarg {n}
    (result: option (Success.Success (SizedList byte) byte memarg n))
    : option (memarg * list byte) :=
  option_map (fun s => (Success.value s,
    @Sized.value _ (@List.length byte) _ (Success.leftovers s))) result.

Lemma decode_memarg_offset_tokens_correct align memory n (input: SizedList byte n) :
  flatten_memarg (decode_memarg_offset_tokens align memory input) =
    option_map (fun '(offset, rest) => (Build_memarg offset align memory, rest))
      (decode_address AT_i64 (@Sized.value _ (@List.length byte) _ input)).
Proof.
  pose proof (decode_address_tokens_correct_sized AT_i64 n input) as Hcorrect.
  unfold flatten in Hcorrect.
  unfold flatten_memarg, decode_memarg_offset_tokens.
  destruct (decode_address_tokens AT_i64 input); cbn [option_map] in Hcorrect;
    rewrite <- Hcorrect; reflexivity.
Qed.

Lemma decode_memarg_tokens_correct input :
  flatten_memarg (decode_memarg_tokens (mkSizedList input)) = decode_memarg input.
Proof.
  unfold decode_memarg_tokens, decode_memarg.
  pose proof (decode_address_tokens_correct AT_i32 input) as Hflags.
  unfold flatten in Hflags.
  destruct (decode_address_tokens AT_i32 (mkSizedList input)) as [flags|];
    cbn [option_map] in Hflags; rewrite <- Hflags; [|reflexivity].
  destruct (decode_memarg_flags (Success.value flags)) as [[align explicit]|]; [|reflexivity].
  destruct explicit.
  - pose proof (decode_address_tokens_correct_sized AT_i32 (Success.size flags)
      (Success.leftovers flags)) as Hmemory.
    unfold flatten in Hmemory.
    destruct (decode_address_tokens AT_i32 (Success.leftovers flags)) as [memory|];
      cbn [option_map] in Hmemory; rewrite <- Hmemory; [|reflexivity].
    rewrite <- (decode_memarg_offset_tokens_correct align (Success.value memory)
      (Success.size memory) (Success.leftovers memory)).
    unfold flatten_memarg.
    destruct (decode_memarg_offset_tokens align (Success.value memory)
      (Success.leftovers memory)); reflexivity.
  - rewrite <- (decode_memarg_offset_tokens_correct align 0%N
      (Success.size flags) (Success.leftovers flags)).
    unfold flatten_memarg.
    destruct (decode_memarg_offset_tokens align 0%N (Success.leftovers flags)); reflexivity.
Qed.

Section Parser.
Context {Toks: nat -> Type} `{Sized Toks byte}
  {M: Type -> Type} `{RawAlternative M}.

Definition parse_address (a: address_type) {n} : Parser Toks byte M N n :=
  MkParser (fun _ _ input => fromOption (decode_address_tokens a input)).

Definition parse_address_limits {n} : Parser Toks byte M (address_type * limits) n :=
  MkParser (fun _ _ input => fromOption (decode_limits_tokens input)).

Definition parse_table_type {n} : Parser Toks byte M datatypes.table_type n :=
  MkParser (fun _ _ input => fromOption (decode_table_type_tokens input)).

Definition parse_memarg {n} : Parser Toks byte M memarg n :=
  MkParser (fun _ _ input => fromOption (decode_memarg_tokens input)).

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

Definition run_limits_prefix (input: list byte)
    : option (address_type * limits * list byte) :=
  flatten_limits (runParser
    (@parse_address_limits (SizedList byte) (sizedList byte) option
      optionRawFunctor optionRawApplicative optionRawAlternative
      (List.length input))
    (Nat.le_refl _) (mkSizedList input)).

Lemma run_limits_prefix_correct input :
  run_limits_prefix input = decode_limits input.
Proof.
  rewrite <- decode_limits_tokens_correct.
  unfold run_limits_prefix, parse_address_limits, flatten_limits.
  cbn [runParser].
  destruct (decode_limits_tokens (mkSizedList input)); reflexivity.
Qed.

End AddressingParseque.
