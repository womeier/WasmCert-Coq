(** Final Wasm 3.0 Bmemarg: flags:u32, optional memory:u32, offset:u64.
    This grammar theorem connects the production parser, not a substitute
    decoder, to arbitrary suffix bytes and ambient Parseque bounds. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque Success.
From Wasm Require Import datatypes_properties operations binary_format_parser
  binary_uleb128 binary_format_parser_properties binary_format_addressing_properties.

Inductive memarg_prefix : list Byte.byte -> memarg -> list Byte.byte -> Prop :=
| memarg_implicit : forall input flags middle offset suffix,
    u32_prefix input flags middle ->
    (flags < 64)%N ->
    u64_prefix middle offset suffix ->
    memarg_prefix input (Build_memarg offset flags 0%N) suffix
| memarg_explicit : forall input flags middle memory after offset suffix,
    u32_prefix input flags middle ->
    (64 <= flags < 128)%N ->
    u32_prefix middle memory after ->
    u64_prefix after offset suffix ->
    memarg_prefix input (Build_memarg offset (flags - 64)%N memory) suffix.

Theorem parse_memarg_prefix_complete : forall n m (Hle : (m <= n)%nat)
    (input : SizedList Byte.byte m) marg suffix,
    memarg_prefix (@Sized.value _ _ _ input) marg suffix ->
    option_map observe_reader
      (runParser (parse_memarg :
        Parser (SizedList Byte.byte) Byte.byte option memarg n) Hle input) =
      Some (marg, suffix).
Proof.
  intros n m Hle input marg suffix Hgrammar.
  inversion Hgrammar as
    [bytes flags middle offset rest Hflags Hbound Hoffset |
     bytes flags middle memory after offset rest Hflags Hbound Hmemory Hoffset];
    subst marg rest.
  - unfold parse_memarg.
    eapply parser_bind_prefix with
      (first := (parse_alignment_exponent :
        Parser (SizedList Byte.byte) Byte.byte option N n))
      (next := fun flags => parse_memarg_payload (n := n) flags)
      (a := flags) (middle := middle).
    + now apply parse_u32_as_N_correct.
    + intros k Hkn tokens Htokens.
      unfold parse_memarg_payload.
      assert (Hdecode : decode_memarg_flags flags = Some (flags, false)).
      { unfold decode_memarg_flags.
        rewrite (proj2 (N.ltb_lt _ _) Hbound). reflexivity. }
      rewrite Hdecode.
      apply parser_map_prefix with (value := offset).
      apply parse_static_offset_correct. now rewrite Htokens.
  - unfold parse_memarg.
    eapply parser_bind_prefix with
      (first := (parse_alignment_exponent :
        Parser (SizedList Byte.byte) Byte.byte option N n))
      (next := fun flags => parse_memarg_payload (n := n) flags)
      (a := flags) (middle := middle).
    + now apply parse_u32_as_N_correct.
    + intros k Hkn tokens Htokens.
      unfold parse_memarg_payload.
      assert (Hdecode :
        decode_memarg_flags flags = Some ((flags - 64)%N, true)).
      { unfold decode_memarg_flags.
        rewrite (proj2 (N.ltb_ge flags 64) ltac:(lia)).
        rewrite (proj2 (N.ltb_lt flags 128) ltac:(lia)). reflexivity. }
      rewrite Hdecode.
      apply parser_map_prefix with (value := (memory, offset)).
      eapply parser_and_prefix with (a := memory) (middle := after).
      * apply parse_u32_as_N_correct. now rewrite Htokens.
      * intros j Hjn tokens' Htokens'.
        apply parse_static_offset_correct. now rewrite Htokens'.
Qed.

Theorem parse_memarg_prefix_sound : forall n m (Hle : (m <= n)%nat)
    (input : SizedList Byte.byte m) marg suffix,
    option_map observe_reader
      (runParser (parse_memarg :
        Parser (SizedList Byte.byte) Byte.byte option memarg n) Hle input) =
      Some (marg, suffix) ->
    memarg_prefix (@Sized.value _ _ _ input) marg suffix.
Proof.
  intros n m Hle input marg suffix Hobs.
  unfold parse_memarg in Hobs.
  assert (Hnext : forall flags k (Hkn : (k <= n)%nat)
      (tokens : SizedList Byte.byte k) value rest,
      option_map observe_reader
        (runParser
          (match decode_memarg_flags flags with
           | Some (align, false) =>
               Combinators.map (fun offset => Build_memarg offset align 0%N)
                 parse_static_offset
           | Some (align, true) =>
               Combinators.map (fun '(memory, offset) =>
                 Build_memarg offset align memory)
                 (Combinators.and parse_memidx parse_static_offset)
           | None => fail
           end : Parser (SizedList Byte.byte) Byte.byte option memarg n) Hkn tokens) =
        Some (value, rest) ->
      forall header,
        u32_prefix header flags (@Sized.value _ _ _ tokens) ->
        memarg_prefix header value rest).
  { intros flags k Hkn tokens value rest Hafter header Hheader.
    unfold decode_memarg_flags in Hafter.
    destruct (N.ltb flags 64) eqn:Hsmall.
    - apply N.ltb_lt in Hsmall.
      apply parser_map_prefix_inv in Hafter as [offset [Hvalue Hoffset]].
      subst value.
      econstructor; [exact Hheader | exact Hsmall |].
      now apply parse_static_offset_correct in Hoffset.
    - apply N.ltb_ge in Hsmall.
      destruct (N.ltb flags 128) eqn:Hlarge; [|discriminate].
      apply N.ltb_lt in Hlarge.
      apply parser_map_prefix_inv in Hafter as
        [[memory offset] [Hvalue Hpair]].
      subst value.
      destruct (parser_and_prefix_sound _ _ n parse_memidx parse_static_offset
        u32_prefix u64_prefix
        (fun j Hjn ts v tail => proj1 (parse_u32_as_N_correct n j Hjn ts v tail))
        (fun j Hjn ts v tail => proj1 (parse_static_offset_correct n j Hjn ts v tail))
        k Hkn tokens memory offset rest Hpair) as [middle [Hmemory Hoffset]].
      eapply memarg_explicit; [exact Hheader | lia | exact Hmemory | exact Hoffset]. }
  destruct (parser_bind_prefix_sound _ _ n parse_alignment_exponent _
    u32_prefix
    (fun flags bytes value rest => forall header,
      u32_prefix header flags bytes -> memarg_prefix header value rest)
    (fun k Hkn tokens value rest =>
      proj1 (parse_u32_as_N_correct n k Hkn tokens value rest))
    Hnext m Hle input marg suffix Hobs)
    as [flags [middle [Hflags Htail]]].
  now apply Htail.
Qed.

Corollary parse_memarg_prefix_correct : forall n m (Hle : (m <= n)%nat)
    (input : SizedList Byte.byte m) marg suffix,
    option_map observe_reader
      (runParser (parse_memarg :
        Parser (SizedList Byte.byte) Byte.byte option memarg n) Hle input) =
      Some (marg, suffix) <->
    memarg_prefix (@Sized.value _ _ _ input) marg suffix.
Proof.
  intros. split.
  - apply parse_memarg_prefix_sound.
  - apply parse_memarg_prefix_complete.
Qed.

Lemma memory32_offset_validation_correct : forall marg,
    memarg_offset32_valid marg = true <->
      (memarg_offset marg < 4294967296)%N.
Proof. intro marg. apply N.ltb_lt. Qed.
