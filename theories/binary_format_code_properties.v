(** Actual code-body/local composition and size framing. *)
From Stdlib Require Import List Strings.Byte NArith ZArith Arith Lia.
From mathcomp Require Import ssrbool eqtype.
From parseque Require Import Parseque.
From Wasm Require Import datatypes datatypes_properties binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_format_language_properties
  binary_format_atomic_properties binary_format_dispatch_properties
  binary_format_block_properties binary_format_type_properties
  binary_format_vector_properties binary_format_section_properties
  binary_format_print_encoding binary_format_expression_print
  binary_format_recursive_complete binary_parser_lookahead_properties
  binary_format_parser_properties.
Local Notation byte := Byte.byte.
Local Notation Expression := (expression_encoding wasm_atomic_encoding block_type_encoding).

Definition local_declaration_encoding bytes (decl : N * value_type) :=
  exists header, bytes = header ++ (binary_of_value_type (snd decl) :: nil) /\
    index_encoding header (fst decl) /\ snd decl <> T_bot.

Definition local_declarations_total (decls : list (N * value_type)) :=
  fold_left N.add (List.map fst decls) 0%N.

Definition local_declarations_expansion (decls : list (N * value_type)) :=
  concat (List.map (fun '(n, t) => List.repeat t (N.to_nat n)) decls).

Definition code_func_encoding bytes (func : module_func_without_type) :=
  exists locals body declarations,
    bytes = locals ++ body /\
    vector_encoding local_declaration_encoding locals declarations /\
    (local_declarations_total declarations < 4294967296)%N /\
    fst func = local_declarations_expansion declarations /\
    Expression body (snd func).

Lemma verify_locals_exact declarations :
  (local_declarations_total declarations < 4294967296)%N ->
  verify_locals declarations = Some (local_declarations_expansion declarations).
Proof.
  intro Range; unfold verify_locals.
  change ((if N.ltb (local_declarations_total declarations) 4294967296
    then Some (local_declarations_expansion declarations) else None) =
    Some (local_declarations_expansion declarations)).
  now rewrite (proj2 (N.ltb_lt _ _) Range).
Qed.

Lemma parse_locals_complete n :
  parser_complete
    (parse_locals (Toks := SizedList byte) (M := option) (n := n))
    local_declaration_encoding.
Proof.
  unfold parse_locals, Combinators.and.
  eapply parser_complete_andbind with
    (P := index_encoding) (Q := fun _ => value_type_encoding).
  - apply leb128_properties.parse_u32_prefix_complete.
  - intros count k lt; simpl; apply parser_complete_le_lower; apply parse_value_type_complete.
  - intros bytes count t [header [Bytes [E Valid]]].
    exists header, (binary_of_value_type t :: nil).
    split; [exact Bytes |]. split; [exact E |].
    split; [reflexivity |exact Valid].
Qed.

Lemma parse_locals_sound n :
  parser_sound
    (parse_locals (Toks := SizedList byte) (M := option) (n := n))
    local_declaration_encoding.
Proof.
  unfold parse_locals, Combinators.and.
  eapply parser_sound_andbind with
    (P := index_encoding) (Q := fun _ => value_type_encoding).
  - apply parse_index_sound.
  - intros count k lt; simpl; apply parser_sound_le_lower; apply parse_value_type_sound.
  - intros header bytes count t E [Bytes Valid]; subst bytes.
    exists header; simpl; auto.
Qed.

Theorem parse_code_func_complete n :
  parser_complete
    (parse_code_func (Toks := SizedList byte) (M := option) (n := n))
    code_func_encoding.
Proof.
  unfold parse_code_func.
  eapply parser_complete_guardM with
    (P := fun bytes pair => exists locals body,
      bytes = locals ++ body /\
      vector_encoding local_declaration_encoding locals (fst pair) /\
      Expression body (snd pair)).
  - unfold Combinators.and.
    eapply parser_complete_andbind with
      (P := vector_encoding local_declaration_encoding) (Q := fun _ => Expression).
    + apply parse_vec_complete; apply parse_locals_complete.
    + intros declarations k lt; simpl; apply parser_complete_le_lower.
      exact (wasm_production_parse_expr_complete n).
    + intros bytes declarations es [locals [body [Bytes [L E]]]].
      exists locals, body.
      split; [exact Bytes |]. split; [exact L |].
      exact E.
  - intros bytes [types es] [locals [body [declarations [Bytes [L [Range [Types E]]]]]]].
    exists (declarations, es); split.
    + exists locals, body; auto.
    + simpl. rewrite (verify_locals_exact declarations Range).
      simpl in Types; subst types; reflexivity.
Qed.

Theorem parse_code_func_sound n :
  parser_sound
    (parse_code_func (Toks := SizedList byte) (M := option) (n := n))
    code_func_encoding.
Proof.
  unfold parse_code_func.
  eapply parser_sound_guardM with
    (P := fun bytes pair => exists locals body,
      bytes = locals ++ body /\
      vector_encoding local_declaration_encoding locals (fst pair) /\
      Expression body (snd pair)).
  - unfold Combinators.and.
    eapply parser_sound_andbind with
      (P := vector_encoding local_declaration_encoding) (Q := fun _ => Expression).
    + apply parse_vec_sound; apply parse_locals_sound.
    + intros declarations k lt; simpl; apply parser_sound_le_lower.
      exact (wasm_production_parse_expr_sound n).
    + intros locals body declarations es L E.
      exists locals, body; auto.
  - intros bytes [declarations es] [types body]
      [locals [encoded [Bytes [L E]]]] Parsed.
    unfold verify_locals in Parsed; simpl in Parsed.
    change (match (if N.ltb (local_declarations_total declarations) 4294967296
      then Some (local_declarations_expansion declarations) else None) with
      | Some ts => Some (ts, es) | None => None end = Some (types, body)) in Parsed.
    destruct (N.ltb (local_declarations_total declarations) 4294967296) eqn:Range;
      [|discriminate].
    inversion Parsed; subst types body.
    exists locals, encoded, declarations.
    split; [exact Bytes |]. split; [exact L |].
    split; [now apply N.ltb_lt |]. split; [reflexivity |exact E].
Qed.

Theorem parse_code_complete n :
  parser_complete (parse_code (Toks := SizedList byte) (M := option) (n := n))
    (section_payload_encoding code_func_encoding).
Proof. apply parse_section_payload_complete; apply parse_code_func_complete. Qed.

Theorem parse_code_sound n :
  parser_sound (parse_code (Toks := SizedList byte) (M := option) (n := n))
    (section_payload_encoding code_func_encoding).
Proof. apply parse_section_payload_sound; apply parse_code_func_sound. Qed.

(** Selective pure packing invariant from the authorized 8d465bf tail
    handoff, adapted to the common grammar without its second codec stack. *)
Definition packed_locals_expansion (decls : list (nat * value_type)) :=
  concat (List.map (fun '(n, t) => List.repeat t n) decls).

Lemma packed_locals_expansion_app first second :
  packed_locals_expansion (first ++ second) =
    packed_locals_expansion first ++ packed_locals_expansion second.
Proof. unfold packed_locals_expansion; now rewrite map_app, concat_app. Qed.

Lemma bunch_locals_aux_expansion types current count acc :
  packed_locals_expansion (bunch_locals_aux current count acc types) =
    packed_locals_expansion (List.rev acc) ++ List.repeat current count ++ types.
Proof.
  revert current count acc; induction types as [|t types IH]; intros current count acc.
  - cbn [bunch_locals_aux List.rev].
    rewrite packed_locals_expansion_app; cbn [packed_locals_expansion List.map List.concat].
    now rewrite !app_nil_r.
  - cbn [bunch_locals_aux].
    destruct (current == t) eqn:Same.
    + assert (Equal : current = t) by exact (elimT eqP Same).
      subst t; rewrite IH, List.repeat_app; simpl.
      now rewrite <- app_assoc.
    + rewrite IH; cbn [List.rev].
      rewrite packed_locals_expansion_app.
      cbn [packed_locals_expansion List.map List.concat List.repeat].
      rewrite !app_nil_r; now rewrite <- app_assoc.
Qed.

Lemma bunch_locals_expansion types :
  packed_locals_expansion (bunch_locals types) = types.
Proof.
  destruct types as [|t types]; [reflexivity |].
  unfold bunch_locals; rewrite bunch_locals_aux_expansion; reflexivity.
Qed.

Lemma bunch_locals_aux_positive types current count acc :
  0 < count -> Forall (fun decl => 0 < fst decl) acc ->
  Forall (fun decl => 0 < fst decl) (bunch_locals_aux current count acc types).
Proof.
  revert current count acc; induction types; intros current count acc Positive Acc.
  - cbn [bunch_locals_aux]; apply Forall_rev; now constructor.
  - cbn [bunch_locals_aux]; destruct (current == a).
    + apply IHtypes; [exact (Nat.lt_lt_add_r _ _ _ Positive) |exact Acc].
    + apply IHtypes; [lia |constructor; assumption].
Qed.

Lemma bunch_locals_positive types :
  Forall (fun decl => 0 < fst decl) (bunch_locals types).
Proof.
  destruct types; [constructor |].
  apply bunch_locals_aux_positive; [lia |constructor].
Qed.

Lemma packed_locals_count declarations :
  Forall (fun decl => 0 < fst decl) declarations ->
  length declarations <= length (packed_locals_expansion declarations).
Proof.
  intro Positive; induction Positive as [|[count t] rest H Rest IH].
  - reflexivity.
  - change (S (length rest) <=
      length (List.repeat t count ++ packed_locals_expansion rest)).
    rewrite length_app, repeat_length; simpl in H; lia.
Qed.

Lemma packed_local_bounds declarations :
  Forall (fun decl => fst decl <= length (packed_locals_expansion declarations)) declarations.
Proof.
  induction declarations as [|[count t] rest IH]; [constructor |].
  change (Forall (fun decl => fst decl <=
    length (List.repeat t count ++ packed_locals_expansion rest))
    ((count, t) :: rest)).
  rewrite length_app, repeat_length.
  constructor; [simpl; lia |].
  eapply Forall_impl; [|exact IH].
  intros [n ty] Bound; simpl in *; lia.
Qed.

Lemma bunch_locals_aux_types types current count acc :
  Forall (fun t => t <> T_bot) types -> current <> T_bot ->
  Forall (fun decl => snd decl <> T_bot) acc ->
  Forall (fun decl => snd decl <> T_bot)
    (bunch_locals_aux current count acc types).
Proof.
  intros Types; revert current count acc; induction Types;
    intros current count acc Current Acc.
  - cbn [bunch_locals_aux]; apply Forall_rev; now constructor.
  - cbn [bunch_locals_aux]; destruct (current == x); apply IHTypes;
      try assumption; constructor; assumption.
Qed.

Lemma bunch_locals_types types :
  Forall (fun t => t <> T_bot) types ->
  Forall (fun decl => snd decl <> T_bot) (bunch_locals types).
Proof.
  intro Types; destruct Types; [constructor |].
  apply bunch_locals_aux_types; try assumption; constructor.
Qed.

Definition counted_local_declarations (declarations : list (nat * value_type)) :=
  List.map (fun '(count, t) => (N.of_nat count, t)) declarations.

Lemma counted_local_expansion declarations :
  local_declarations_expansion (counted_local_declarations declarations) =
    packed_locals_expansion declarations.
Proof.
  induction declarations as [|[count t] rest IH]; [reflexivity |].
  change (List.repeat t (N.to_nat (N.of_nat count)) ++
    local_declarations_expansion (counted_local_declarations rest) =
    List.repeat t count ++ packed_locals_expansion rest).
  now rewrite Nat2N.id, IH.
Qed.

Lemma counted_local_total declarations acc :
  fold_left N.add (List.map fst (counted_local_declarations declarations)) acc =
    (acc + N.of_nat (length (packed_locals_expansion declarations)))%N.
Proof.
  revert acc; induction declarations as [|[count t] rest IH]; intro acc.
  - simpl; now rewrite N.add_0_r.
  - change (fold_left N.add (List.map fst (counted_local_declarations rest))
      (acc + N.of_nat count)%N =
      (acc + N.of_nat (length (List.repeat t count ++ packed_locals_expansion rest)))%N).
    rewrite IH, length_app, repeat_length, Nat2N.inj_add, N.add_assoc.
    reflexivity.
Qed.

Lemma binary_nat_conversion n : ssrnat.bin_of_nat n = N.of_nat n.
Proof.
  assert (PosNat : forall p, ssrnat.nat_of_pos p = Pos.to_nat p).
  { apply Pos.peano_ind; [reflexivity |].
    intros p IH; now rewrite ssrnat.nat_of_succ_pos, Pos2Nat.inj_succ, IH. }
  assert (Nats : forall x, N.to_nat x = ssrnat.nat_of_bin x).
  { intros [|p]; [reflexivity |simpl; symmetry; apply PosNat]. }
  apply N2Nat.inj; rewrite Nat2N.id, Nats; apply ssrnat.bin_of_natK.
Qed.

Theorem binary_of_code_func_encoding types es :
  Forall (fun t => t <> T_bot) types ->
  (N.of_nat (length types) < 4294967296)%N ->
  expression_binary_wf es ->
  code_func_encoding (binary_of_code_func types es) (types, es).
Proof.
  intros Types Count Expr.
  exists (binary_of_vec binary_of_local (bunch_locals types)),
    (binary_of_expr es), (counted_local_declarations (bunch_locals types)).
  split; [reflexivity |]. split.
  - assert (Items : encoded_items local_declaration_encoding
      (concat (List.map binary_of_local (bunch_locals types)))
      (counted_local_declarations (bunch_locals types))).
    { pose proof (packed_local_bounds (bunch_locals types)) as Bounds.
      rewrite bunch_locals_expansion in Bounds.
      pose proof (bunch_locals_types types Types) as Valid.
      induction Valid as [|[n t] rest TypeValid Valid IH].
      - constructor.
      - inversion Bounds as [|decl decls Bound Tail]; subst.
        simpl; constructor.
        + exists (binary_of_idx (N.of_nat n)); split.
           * cbn [binary_of_local]; rewrite binary_nat_conversion.
             unfold binary_of_idx.
             now rewrite binary_format_properties.binary_of_u32_arithmetic.
          * split.
            -- apply binary_of_index_encoding; unfold binary_index_wf; simpl in Bound.
               change (N.of_nat n <= 4294967295)%N; lia.
            -- exact TypeValid.
        + apply IH; exact Tail. }
    exists (binary_of_idx (N.of_nat (length (bunch_locals types)))),
      (concat (List.map binary_of_local (bunch_locals types))).
    split; [reflexivity |].
    assert (PackedCount : binary_index_wf (N.of_nat (length (bunch_locals types)))).
    { pose proof (packed_locals_count _ (bunch_locals_positive types)) as Length.
      rewrite bunch_locals_expansion in Length; unfold binary_index_wf; lia. }
    destruct (binary_of_index_encoding _ PackedCount) as [E [Range Width]].
    unfold counted_local_declarations; rewrite length_map.
    split; [exact E |]. split; [exact Range |]. split; [exact Width |exact Items].
  - split.
    + unfold local_declarations_total.
      rewrite counted_local_total, N.add_0_l, bunch_locals_expansion; exact Count.
    + split.
      * simpl; rewrite counted_local_expansion, bunch_locals_expansion; reflexivity.
      * now apply binary_of_expr_encoding.
Qed.

Lemma with_length_encoding {A} Grammar bytes (value : A) :
  Grammar bytes value -> binary_vector_length_wf bytes ->
  section_payload_encoding Grammar (with_length bytes) value.
Proof.
  intros Encoding Count.
  exists (binary_of_idx (N.of_nat (length bytes))), bytes.
  split.
   - unfold with_length; rewrite binary_nat_conversion.
     unfold binary_of_idx.
     now rewrite binary_format_properties.binary_of_u32_arithmetic.
  - destruct (binary_of_index_encoding _ Count) as [E [Range Width]].
    split; [exact E |]. split; [exact Range |]. split; assumption.
Qed.

Definition code_binary_wf (func : module_func) :=
  Forall (fun t => t <> T_bot) func.(modfunc_locals) /\
  (N.of_nat (length func.(modfunc_locals)) < 4294967296)%N /\
  expression_binary_wf func.(modfunc_body) /\
  binary_vector_length_wf
    (binary_of_code_func func.(modfunc_locals) func.(modfunc_body)).

Theorem binary_of_code_encoding func :
  code_binary_wf func ->
  section_payload_encoding code_func_encoding (binary_of_code func)
    (func.(modfunc_locals), func.(modfunc_body)).
Proof.
  intros [Types [Locals [Expr Size]]].
  change (section_payload_encoding code_func_encoding
    (with_length (binary_of_code_func func.(modfunc_locals) func.(modfunc_body)))
    (func.(modfunc_locals), func.(modfunc_body))).
  apply with_length_encoding; [now apply binary_of_code_func_encoding |exact Size].
Qed.

Theorem code_print_prefix func :
  code_binary_wf func ->
  forall n m (bound : m <= n) (input : SizedList byte m) suffix,
    input_bytes input = binary_of_code func ++ suffix ->
    option_map (fun s => (Success.value s, output_bytes s))
      (runParser (parse_code (M := option) (n := n)) bound input) =
    Some ((func.(modfunc_locals), func.(modfunc_body)), suffix).
Proof.
  intros Wf n m bound input suffix Bytes.
  destruct (parse_code_complete n m bound input (binary_of_code func) suffix
    (func.(modfunc_locals), func.(modfunc_body)) Bytes
    (binary_of_code_encoding func Wf)) as [s [Run [Value Rest]]].
  rewrite Run; simpl; now rewrite Value, Rest.
Qed.

Corollary binary_of_code_roundtrip func :
  code_binary_wf func ->
  run (binary_of_code func) (fun _ => parse_code) =
    Some (func.(modfunc_locals), func.(modfunc_body)).
Proof.
  intro Wf; apply (run_parser_complete _ (section_payload_encoding code_func_encoding)).
  - exact parse_code_complete.
  - now apply binary_of_code_encoding.
Qed.

Definition code_section_encoding bytes functions :=
  exists payload, bytes = x0a :: payload /\
    section_payload_encoding (vector_encoding (section_payload_encoding code_func_encoding))
      payload functions.

Theorem parse_codesec_complete n :
  parser_complete (parse_codesec (Toks := SizedList byte) (M := option) (n := n))
    code_section_encoding.
Proof.
  unfold parse_codesec.
  apply parser_complete_prefix_byte with
    (Q := section_payload_encoding (vector_encoding (section_payload_encoding code_func_encoding))).
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_section_payload_complete; apply parse_vec_complete; apply parse_code_complete.
  - intros bytes functions Encoding; exact Encoding.
Qed.

Theorem parse_codesec_sound n :
  parser_sound (parse_codesec (Toks := SizedList byte) (M := option) (n := n))
    code_section_encoding.
Proof.
  unfold parse_codesec.
  apply parser_sound_prefix_byte with
    (Q := section_payload_encoding (vector_encoding (section_payload_encoding code_func_encoding))).
  - intros k lt; simpl; apply parser_sound_le_lower.
    apply parse_section_payload_sound; apply parse_vec_sound; apply parse_code_sound.
  - intros bytes functions Encoding.
    exists bytes; auto.
Qed.

Theorem binary_of_codesec_encoding functions :
  Forall code_binary_wf functions ->
  binary_vector_length_wf functions ->
  binary_vector_length_wf (binary_of_vec binary_of_code functions) ->
  code_section_encoding (binary_of_codesec functions)
    (List.map (fun f => (f.(modfunc_locals), f.(modfunc_body))) functions).
Proof.
  intros Wf Count Size.
  exists (with_length (binary_of_vec binary_of_code functions)).
  split; [reflexivity |]. apply with_length_encoding; [|exact Size].
  exists (binary_of_idx (N.of_nat (length functions))),
    (concat (List.map binary_of_code functions)).
  split; [reflexivity |].
  destruct (binary_of_index_encoding _ Count) as [E [Range Width]].
  rewrite length_map.
  split; [exact E |]. split; [exact Range |]. split; [exact Width |].
  clear Count Size E Range Width.
  induction Wf; simpl; constructor; [now apply binary_of_code_encoding |assumption].
Qed.

Corollary binary_of_codesec_roundtrip functions :
  Forall code_binary_wf functions ->
  binary_vector_length_wf functions ->
  binary_vector_length_wf (binary_of_vec binary_of_code functions) ->
  run (binary_of_codesec functions) (fun _ => parse_codesec) =
    Some (List.map (fun f => (f.(modfunc_locals), f.(modfunc_body))) functions).
Proof.
  intros Wf Count Size; apply (run_parser_complete _ code_section_encoding).
  - exact parse_codesec_complete.
  - now apply binary_of_codesec_encoding.
Qed.

Theorem verify_locals_overflow_rejected declarations :
  (4294967296 <= local_declarations_total declarations)%N ->
  verify_locals declarations = None.
Proof.
  intro Overflow; unfold verify_locals.
  change ((if N.ltb (local_declarations_total declarations) 4294967296
    then Some (local_declarations_expansion declarations) else None) = None).
  rewrite (proj2 (N.ltb_ge _ _) Overflow); reflexivity.
Qed.

Theorem parse_code_func_local_overflow_rejected n m (bound : m <= n)
    (input : SizedList byte m) locals body suffix declarations es :
  input_bytes input = (locals ++ body) ++ suffix ->
  vector_encoding local_declaration_encoding locals declarations ->
  Expression body es ->
  (4294967296 <= local_declarations_total declarations)%N ->
  runParser (parse_code_func (M := option) (n := n)) bound input = None.
Proof.
  intros Bytes Locals Expr Overflow.
  assert (Raw : parser_complete
    (Combinators.and (parse_vec (parse_locals (M := option) (n := n))) (box parse_expr))
    (fun bytes pair => exists locals body,
      bytes = locals ++ body /\
      vector_encoding local_declaration_encoding locals (fst pair) /\
      Expression body (snd pair))).
  { unfold Combinators.and.
    eapply parser_complete_andbind with
      (P := vector_encoding local_declaration_encoding) (Q := fun _ => Expression).
    - apply parse_vec_complete; apply parse_locals_complete.
    - intros decls k lt; simpl; apply parser_complete_le_lower.
      exact (wasm_production_parse_expr_complete n).
    - intros bytes decls expr [ls [bs [Parts [L E]]]].
      exists ls, bs; auto. }
  destruct (Raw m bound input (locals ++ body) suffix (declarations, es) Bytes
    ltac:(exists locals, body; auto)) as [s [Run [Value Rest]]].
  unfold parse_code_func; rewrite run_guardM_option, Run.
  unfold Success.guardM; rewrite Value; simpl.
  now rewrite (verify_locals_overflow_rejected declarations Overflow).
Qed.
