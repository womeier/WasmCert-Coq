(** Compositional completeness of the parser's positive-count vector tree.
    The element-parser premise must be discharged for each concrete grammar;
    no replacement parser or correspondence assumption is introduced. *)
From Stdlib Require Import List Strings.Byte NArith PArith PeanoNat Lia.
From parseque Require Import Parseque Success.
From Wasm Require Import binary_format_parser binary_format_parser_properties
  binary_uleb128.

Inductive elements_prefix {A}
    (element : list byte -> A -> list byte -> Prop) :
    list byte -> list A -> list byte -> Prop :=
| elements_nil : forall suffix, elements_prefix element suffix nil suffix
| elements_cons : forall input value middle values suffix,
    element input value middle ->
    elements_prefix element middle values suffix ->
    elements_prefix element input (value :: values) suffix.

Lemma elements_prefix_split : forall A
    (element : list byte -> A -> list byte -> Prop) first second input suffix,
    elements_prefix element input (List.app first second) suffix ->
    exists middle, elements_prefix element input first middle /\
      elements_prefix element middle second suffix.
Proof.
  intros A element first.
  induction first as [|value first IH]; intros second input suffix Hprefix.
  - exists input. split; [constructor | exact Hprefix].
  - cbn [List.app] in Hprefix.
    inversion Hprefix as [|start head middle values rest Hhead Htail]; subst.
    destruct (IH second middle suffix Htail) as [after [Hfirst Hsecond]].
    exists after. split; [econstructor; eassumption | assumption].
Qed.

Lemma elements_prefix_halves : forall A
    (element : list byte -> A -> list byte -> Prop) k values input suffix,
    List.length values = (2 * k)%nat ->
    elements_prefix element input values suffix ->
    exists first second middle,
      values = List.app first second /\
      List.length first = k /\ List.length second = k /\
      elements_prefix element input first middle /\
      elements_prefix element middle second suffix.
Proof.
  intros A element k values input suffix Hlength Hprefix.
  pose proof (List.firstn_skipn k values) as Hsplit.
  rewrite <- Hsplit in Hprefix.
  destruct (elements_prefix_split A element _ _ _ _ Hprefix)
    as [middle [Hfirst Hsecond]].
  exists (List.firstn k values), (List.skipn k values), middle.
  split; [symmetry; exact Hsplit |].
  repeat split.
  - rewrite List.length_firstn, Hlength, Nat.min_l; lia.
  - rewrite List.length_skipn, Hlength. lia.
  - exact Hfirst.
  - exact Hsecond.
Qed.

Theorem parse_vec_aux_positive_complete : forall A
    (element : list byte -> A -> list byte -> Prop) p n
    (parser : Parser (SizedList byte) byte option A n),
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      element (@Sized.value _ _ _ input) value suffix ->
      option_map observe_reader (runParser parser Hle input) =
        Some (value, suffix)) ->
    forall m (Hle : (m <= n)%nat) (input : SizedList byte m) values suffix,
    List.length values = Pos.to_nat p ->
    elements_prefix element (@Sized.value _ _ _ input) values suffix ->
    option_map observe_reader
      (runParser (parse_vec_aux_positive parser p) Hle input) =
      Some (values, suffix).
Proof.
  intros A element p.
  induction p as [p IH | p IH |]; intros n parser Hparser m Hle input
    values suffix Hlength Hprefix.
  - rewrite Pos2Nat.inj_xI in Hlength.
    destruct values as [|value values]; [cbn in Hlength; lia |].
    cbn [List.length] in Hlength.
    inversion Hprefix as [|start head middle tail rest Hhead Htail]; subst.
    destruct (elements_prefix_halves A element (Pos.to_nat p) values middle
      suffix ltac:(lia) Htail)
      as [first [second [after [Hvalues [Hfirst_len [Hsecond_len [Hfirst Hsecond]]]]]]].
    subst values.
    change (option_map observe_reader
      (runParser (Combinators.map
        (fun '(head, (part1, part2)) => head :: List.app part1 part2)
        (Combinators.and parser
          (Combinators.and (parse_vec_aux_positive parser p)
            (parse_vec_aux_positive parser p)))) Hle input) =
      Some (value :: List.app first second, suffix)).
    apply parser_map_prefix with (value := (value, (first, second))).
    eapply parser_and_prefix with (a := value) (middle := middle).
    + now apply Hparser.
    + intros k Hkn tokens Htokens.
      eapply parser_and_prefix with (a := first) (middle := after).
      * eapply IH; [exact Hparser | exact Hfirst_len |].
        rewrite Htokens. exact Hfirst.
      * intros j Hjn tokens' Htokens'.
        eapply IH; [exact Hparser | exact Hsecond_len |].
        rewrite Htokens'. exact Hsecond.
  - rewrite Pos2Nat.inj_xO in Hlength.
    destruct (elements_prefix_halves A element (Pos.to_nat p) values
      (@Sized.value _ _ _ input) suffix Hlength Hprefix)
      as [first [second [middle [Hvalues [Hfirst_len [Hsecond_len [Hfirst Hsecond]]]]]]].
    subst values.
    change (option_map observe_reader
      (runParser (Combinators.map
        (fun '(part1, part2) => List.app part1 part2)
        (Combinators.and (parse_vec_aux_positive parser p)
          (parse_vec_aux_positive parser p))) Hle input) =
      Some (List.app first second, suffix)).
    apply parser_map_prefix with (value := (first, second)).
    eapply parser_and_prefix with (a := first) (middle := middle).
    + eapply IH; eassumption.
    + intros k Hkn tokens Htokens.
      eapply IH; [exact Hparser | exact Hsecond_len |].
      rewrite Htokens. exact Hsecond.
  - cbn in Hlength.
    destruct values as [|value values]; [cbn in Hlength; lia |].
    destruct values as [|extra values]; [|cbn in Hlength; lia].
    inversion Hprefix as [|start head middle tail rest Hhead Htail]; subst.
    inversion Htail; subst.
    cbn [parse_vec_aux_positive].
    apply parser_map_prefix with (value := value).
    now apply Hparser.
Qed.

Definition vector_prefix {A}
    (element : list byte -> A -> list byte -> Prop) input values suffix :=
  exists body,
    u32_prefix input (N.of_nat (List.length values)) body /\
    elements_prefix element body values suffix.

Theorem parse_vec_complete : forall A
    (element : list byte -> A -> list byte -> Prop) n
    (parser : Parser (SizedList byte) byte option A n),
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      element (@Sized.value _ _ _ input) value suffix ->
      option_map observe_reader (runParser parser Hle input) =
        Some (value, suffix)) ->
    forall m (Hle : (m <= n)%nat) (input : SizedList byte m) values suffix,
    vector_prefix element (@Sized.value _ _ _ input) values suffix ->
    option_map observe_reader (runParser (parse_vec parser) Hle input) =
      Some (values, suffix).
Proof.
  intros A element n parser Hparser m Hle input values suffix
    [body [Hheader Helements]].
  destruct (N.of_nat (List.length values)) as [|p] eqn:Hcount.
  - assert (Hlength : List.length values = 0%nat).
    { apply (f_equal N.to_nat) in Hcount.
      now rewrite Nat2N.id in Hcount. }
    apply List.length_zero_iff_nil in Hlength. subst values.
    inversion Helements; subst.
    now apply parse_vec_zero_prefix.
  - assert (Hlength : List.length values = Pos.to_nat p).
    { apply (f_equal N.to_nat) in Hcount.
      now rewrite Nat2N.id in Hcount. }
    destruct input as [input Hinput].
    cbn [Sized.value] in Hheader.
    destruct input as [|b input]; cbn in Hinput; subst m.
    { apply decode_u32_correct in Hheader. discriminate. }
    destruct (Byte.byte_eq_dec b x00) as [-> | Hbyte].
    { apply decode_u32_correct in Hheader.
      change (Some (0%N, input) = Some (N.pos p, body)) in Hheader.
      discriminate. }
    assert (Hneq : datatypes_properties.byte_eqb b x00 = false).
    { unfold datatypes_properties.byte_eqb.
      destruct (Byte.byte_eq_dec b x00); cbn; congruence. }
    pose proof (proj2 (parse_u32_as_N_correct n _ Hle
      (mkSizedList (b :: input)) (N.pos p) body) Hheader) as Hhead.
    unfold parse_vec, parse_vec_length, Combinators.alt,
      Combinators.cmap, Combinators.map, exact_byte, Combinators.guardM.
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
    cbn -[parse_u32_as_N].
    cbn -[parse_u32_as_N].
    match goal with
    | |- context [runParser ?reader ?bound ?tokens] =>
        change (option_map observe_reader (runParser reader bound tokens) =
          Some (N.pos p, body)) in Hhead;
        destruct (runParser reader bound tokens) as [result|]
    end; [|discriminate].
    destruct result as [count remaining Hsmall [tail Htail_length]].
    cbn [observe_reader Success.value Success.leftovers Sized.value] in Hhead.
    inversion Hhead; subst count tail.
    subst remaining.
    cbn [Combinators.bind Combinators.andbind Combinators.map
      Combinators.box le_close Combinators.le_lower call runParser].
    cbn -[parse_vec_aux_positive].
    match goal with
    | |- context [runParser ?reader ?bound ?tokens] =>
        pose proof (parse_vec_aux_positive_complete A element p n parser Hparser
          _ bound tokens values suffix Hlength Helements) as Hbody;
        change (option_map observe_reader (runParser reader bound tokens) =
          Some (values, suffix)) in Hbody;
        destruct (runParser reader bound tokens) as [result|]
    end; [|discriminate].
    destruct result as [parsed remaining Hparsed_small [tail Hparsed_length]].
    cbn [observe_reader Success.value Success.leftovers Sized.value] in Hbody.
    inversion Hbody; subst parsed tail.
    reflexivity.
Qed.

Lemma elements_prefix_app : forall A
    (element : list byte -> A -> list byte -> Prop) input first middle,
    elements_prefix element input first middle ->
    forall second suffix, elements_prefix element middle second suffix ->
    elements_prefix element input (List.app first second) suffix.
Proof.
  intros A element input first middle Hfirst.
  induction Hfirst as [middle |
    input value after values middle Hhead Htail IH]; intros second suffix Hsecond.
  - exact Hsecond.
  - cbn [List.app]. econstructor; [exact Hhead | now apply IH].
Qed.

Definition vector_chunk_prefix {A}
    (element : list byte -> A -> list byte -> Prop) p input values suffix :=
  List.length values = Pos.to_nat p /\
    elements_prefix element input values suffix.

Theorem parse_vec_aux_positive_sound : forall A
    (element : list byte -> A -> list byte -> Prop) p n
    (parser : Parser (SizedList byte) byte option A n),
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      option_map observe_reader (runParser parser Hle input) =
        Some (value, suffix) ->
      element (@Sized.value _ _ _ input) value suffix) ->
    forall m (Hle : (m <= n)%nat) (input : SizedList byte m) values suffix,
    option_map observe_reader
      (runParser (parse_vec_aux_positive parser p) Hle input) =
      Some (values, suffix) ->
    vector_chunk_prefix element p (@Sized.value _ _ _ input) values suffix.
Proof.
  intros A element p.
  induction p as [p IH | p IH |]; intros n parser Hparser m Hle input
    values suffix Hobs.
  - change (option_map observe_reader
      (runParser (Combinators.map
        (fun '(head, (part1, part2)) => head :: List.app part1 part2)
        (Combinators.and parser
          (Combinators.and (parse_vec_aux_positive parser p)
            (parse_vec_aux_positive parser p)))) Hle input) =
      Some (values, suffix)) in Hobs.
    apply parser_map_prefix_inv in Hobs as
      [[value [first second]] [Hvalues Hpair]].
    subst values.
    assert (Hpair_sound :
      forall k (Hkn : (k <= n)%nat) (tokens : SizedList byte k) parts rest,
      option_map observe_reader
        (runParser (Combinators.and (parse_vec_aux_positive parser p)
          (parse_vec_aux_positive parser p)) Hkn tokens) = Some (parts, rest) ->
      exists middle,
        vector_chunk_prefix element p (@Sized.value _ _ _ tokens)
          (fst parts) middle /\
        vector_chunk_prefix element p middle (snd parts) rest).
    { intros k Hkn tokens [part1 part2] rest Hparts.
      exact (parser_and_prefix_sound _ _ n _ _
        (vector_chunk_prefix element p) (vector_chunk_prefix element p)
        (IH n parser Hparser) (IH n parser Hparser)
        k Hkn tokens part1 part2 rest Hparts). }
    destruct (parser_and_prefix_sound _ _ n parser
      (Combinators.and (parse_vec_aux_positive parser p)
        (parse_vec_aux_positive parser p)) element
      (fun bytes parts rest => exists middle,
        vector_chunk_prefix element p bytes (fst parts) middle /\
        vector_chunk_prefix element p middle (snd parts) rest)
      Hparser Hpair_sound m Hle input value (first, second) suffix Hpair)
      as [middle [Hhead [after [[Hfirst_len Hfirst] [Hsecond_len Hsecond]]]]].
    split.
    + cbn in Hfirst_len, Hsecond_len.
      cbn [List.length]. rewrite List.length_app, Pos2Nat.inj_xI. lia.
    + eapply elements_cons; [exact Hhead |].
      eapply elements_prefix_app; eassumption.
  - change (option_map observe_reader
      (runParser (Combinators.map
        (fun '(part1, part2) => List.app part1 part2)
        (Combinators.and (parse_vec_aux_positive parser p)
          (parse_vec_aux_positive parser p))) Hle input) =
      Some (values, suffix)) in Hobs.
    apply parser_map_prefix_inv in Hobs as [[first second] [Hvalues Hpair]].
    subst values.
    destruct (parser_and_prefix_sound _ _ n _ _
      (vector_chunk_prefix element p) (vector_chunk_prefix element p)
      (IH n parser Hparser) (IH n parser Hparser)
      m Hle input first second suffix Hpair)
      as [middle [[Hfirst_len Hfirst] [Hsecond_len Hsecond]]].
    split.
    + rewrite List.length_app, Pos2Nat.inj_xO. lia.
    + eapply elements_prefix_app; eassumption.
  - cbn [parse_vec_aux_positive] in Hobs.
    apply parser_map_prefix_inv in Hobs as [value [Hvalues Hvalue]].
    subst values.
    split; [reflexivity |].
    econstructor; [exact (Hparser m Hle input value suffix Hvalue) | constructor].
Qed.

Theorem parse_vec_sound : forall A
    (element : list byte -> A -> list byte -> Prop) n
    (parser : Parser (SizedList byte) byte option A n),
    (forall m (Hle : (m <= n)%nat) (input : SizedList byte m) value suffix,
      option_map observe_reader (runParser parser Hle input) =
        Some (value, suffix) ->
      element (@Sized.value _ _ _ input) value suffix) ->
    forall m (Hle : (m <= n)%nat) (input : SizedList byte m) values suffix,
    option_map observe_reader (runParser (parse_vec parser) Hle input) =
      Some (values, suffix) ->
    vector_prefix element (@Sized.value _ _ _ input) values suffix.
Proof.
  intros A element n parser Hparser m Hle [input Hlength] values suffix Hobs.
  destruct input as [|b input]; cbn in Hlength; subst m.
  - discriminate.
  - destruct (Byte.byte_eq_dec b x00) as [-> | Hbyte].
    + change (Some (nil, input) = Some (values, suffix)) in Hobs.
      inversion Hobs; subst values suffix.
      exists input. split.
      * apply decode_u32_correct. reflexivity.
      * constructor.
    + assert (Hneq : datatypes_properties.byte_eqb b x00 = false).
      { unfold datatypes_properties.byte_eqb.
        destruct (Byte.byte_eq_dec b x00); cbn; congruence. }
      unfold parse_vec, parse_vec_length, Combinators.alt,
        Combinators.cmap, Combinators.map, exact_byte, Combinators.guardM in Hobs.
      cbn [runParser anyTok Success.getTok sizedList uncons listUncons
        Success.fromView Success.guardM option_map uncurry Success.value
        Success.size Success.small Success.leftovers] in Hobs.
      unfold Combinators.map, Category.bind, Category.alt, Category.fmap,
        fromOption, Success.guardM in Hobs.
      cbn [runParser anyTok Success.getTok sizedList uncons listUncons
        Success.fromView Success.guardM option_map uncurry Success.value
        Success.size Success.small Success.leftovers
        _bind _alt _fmap _pure _fail optionRawMonad optionRawAlternative
        optionRawFunctor optionRawApplicative pure fail] in Hobs.
      cbn -[parse_u32_as_N] in Hobs.
      cbn -[parse_u32_as_N] in Hobs.
      match goal with
      | Hobs : context [runParser ?reader ?bound ?tokens] |- _ =>
          pose proof (parse_u32_as_N_correct n _ bound tokens) as Hheader;
          destruct (runParser reader bound tokens) as [result|] eqn:Hraw
      end; [|discriminate].
      destruct result as [count remaining Hsmall [body Hbody_length]].
      assert (Hgrammar : u32_prefix (b :: input) count body).
      { apply Hheader. reflexivity. }
      destruct count as [|p].
      * change (Some (nil, body) = Some (values, suffix)) in Hobs.
        inversion Hobs; subst values suffix.
        exists body. split; [exact Hgrammar | constructor].
      * cbn [Combinators.bind Combinators.andbind Combinators.map
          Combinators.box le_close Combinators.le_lower call runParser] in Hobs.
        cbn -[parse_vec_aux_positive] in Hobs.
        match goal with
        | Hobs : context [runParser ?reader ?bound ?tokens] |- _ =>
            pose proof (parse_vec_aux_positive_sound A element p n parser Hparser
              _ bound tokens) as Hchunk;
            destruct (runParser reader bound tokens) as [result|]
        end; [|discriminate].
        destruct result as [parsed after Hafter_small [rest Hrest_length]].
        change (Some (parsed, rest) = Some (values, suffix)) in Hobs.
        inversion Hobs; subst values suffix.
        destruct (Hchunk parsed rest eq_refl) as [Hlen Helements].
        exists body. split; [|exact Helements].
        rewrite Hlen. change (u32_prefix (b :: input) (N.of_nat (N.to_nat (N.pos p))) body).
        now rewrite N2Nat.id.
Qed.
