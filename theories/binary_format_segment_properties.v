(** Actual element/data segment codecs; source forms remain separate from
    validation and runtime reference closing. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From parseque Require Import Parseque.
From mathcomp Require Import ssrbool eqtype.
From Wasm Require Import datatypes datatypes_properties bytes common list_extra
  binary_format_parser binary_format_printer binary_format_parser_properties
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_type_properties
  binary_format_print_encoding binary_format_expression_print
  binary_format_recursive_complete binary_format_dispatch_properties
  binary_format_block_properties binary_format_vector_properties
  binary_format_record_properties.
Local Notation byte := Byte.byte.
Local Notation Expression := (expression_encoding wasm_atomic_encoding block_type_encoding).

Definition subopcode_encoding {A} code (Body : list byte -> A -> Prop) bytes value :=
  exists header payload, bytes = header ++ payload /\
    index_encoding header code /\ Body payload value.

Lemma asserted_body_complete {A n} code
    (p : Parser (SizedList byte) byte option A n) Body :
  parser_complete p Body ->
  parser_complete (Combinators.rand (assert_u32 code) (box p))
    (subopcode_encoding code Body).
Proof.
  intro Complete.
  apply parser_complete_rand_grammar with
    (P := fun bytes value => index_encoding bytes code /\ value = code) (Q := Body).
  - apply assert_u32_complete.
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros bytes value [header [payload [Bytes [E B]]]].
    exists header, payload, code; auto.
Qed.

Lemma asserted_wrong_subopcode n m (bound : m <= n) input header payload expected actual :
  input_bytes input = header ++ payload -> index_encoding header actual ->
  actual <> expected ->
  runParser (assert_u32 (M := option) (n := n) expected) bound input = None.
Proof.
  intros Bytes Encoding Different.
  destruct (leb128_properties.parse_u32_prefix_complete n m bound input
    header payload actual Bytes Encoding) as [s [Run [Value Rest]]].
  unfold assert_u32; rewrite run_guardM_option, Run.
  unfold Success.guardM; rewrite Value, (proj2 (N.eqb_neq _ _) Different).
  reflexivity.
Qed.

Lemma asserted_body_wrong_subopcode {A n} expected actual
    (p : Box (Parser (SizedList byte) byte option A) n) m bound input header payload :
  input_bytes input = header ++ payload -> index_encoding header actual ->
  actual <> expected ->
  runParser (Combinators.rand (assert_u32 expected) p) (m := m) bound input = None.
Proof.
  intros Bytes Encoding Different.
  pose proof (asserted_wrong_subopcode n m bound input header payload
    expected actual Bytes Encoding Different) as Failed.
  unfold Combinators.rand, Combinators.and, Combinators.map, Combinators.andbind.
  cbn -[assert_u32].
  now rewrite Failed.
Qed.

Lemma subopcode_choice_complete {A n} expected actual
    (p : Box (Parser (SizedList byte) byte option A) n)
    (q : Parser (SizedList byte) byte option A n) Body :
  actual <> expected ->
  parser_complete q (subopcode_encoding actual Body) ->
  parser_complete (Combinators.alt (Combinators.rand (assert_u32 expected) p) q)
    (subopcode_encoding actual Body).
Proof.
  intros Different Complete.
  apply parser_complete_alt_right_failure; [|exact Complete].
  intros m bound input prefix suffix value Bytes [header [payload [Parts [E B]]]].
  apply (asserted_body_wrong_subopcode expected actual p m bound input header (payload ++ suffix)).
  - rewrite Bytes, Parts; now rewrite app_assoc.
  - exact E.
  - exact Different.
Qed.

Ltac subopcode_dispatch code Leaf :=
  first [exact Leaf |apply parser_complete_alt_left; exact Leaf |
    eapply subopcode_choice_complete with (actual := code);
      [discriminate |subopcode_dispatch code Leaf]].

Definition raw_vector_encoding := vector_encoding (fun bytes b => bytes = b :: nil).

Definition data_passive_encoding bytes data :=
  exists raw, raw_vector_encoding bytes raw /\
    data = Build_module_data (List.map compcert_byte_of_byte raw) MD_passive.

Definition data_active_encoding bytes data :=
  exists indices body rawbytes index es raw,
    bytes = indices ++ body ++ rawbytes /\ index_encoding indices index /\
    Expression body es /\ raw_vector_encoding rawbytes raw /\
    data = Build_module_data (List.map compcert_byte_of_byte raw) (MD_active index es).

Lemma parse_data_passive_complete n :
  parser_complete (parse_module_data_1 (Toks := SizedList byte) (M := option) (n := n))
    data_passive_encoding.
Proof.
  unfold parse_module_data_1.
  eapply parser_complete_map; [apply parse_vec_complete; apply parser_complete_anyTok |].
  intros bytes data [raw [E Value]]; exists raw; auto.
Qed.

Lemma parse_data_active_complete n :
  parser_complete (parse_module_data_2 (Toks := SizedList byte) (M := option) (n := n))
    data_active_encoding.
Proof.
  unfold parse_module_data_2.
  eapply parser_complete_app with
    (P := fun bytes f => exists indices body index es,
      bytes = indices ++ body /\ index_encoding indices index /\ Expression body es /\
      f = (fun raw => Build_module_data (List.map compcert_byte_of_byte raw) (MD_active index es)))
    (Q := raw_vector_encoding).
  - eapply parser_complete_app with
      (P := fun bytes f => exists index, index_encoding bytes index /\
        f = (fun es raw => Build_module_data (List.map compcert_byte_of_byte raw) (MD_active index es)))
      (Q := Expression).
    + eapply parser_complete_map; [apply leb128_properties.parse_u32_prefix_complete |].
      intros bytes f [index [E Value]]; exists index; auto.
    + intros k lt; simpl; apply parser_complete_le_lower; apply wasm_production_parse_expr_complete.
    + intros bytes f [indices [body [index [es [Bytes [I [E Value]]]]]]].
      exists indices, body, (fun es raw =>
        Build_module_data (List.map compcert_byte_of_byte raw) (MD_active index es)), es.
      split; [exact Bytes |]. split; [exists index; auto |]. split; assumption.
  - intros k lt; simpl; apply parser_complete_le_lower.
    apply parse_vec_complete; apply parser_complete_anyTok.
  - intros bytes data [indices [body [rawbytes [index [es [raw [Bytes [I [E [Raw Value]]]]]]]]]].
    exists (indices ++ body), rawbytes,
      (fun raw => Build_module_data (List.map compcert_byte_of_byte raw) (MD_active index es)), raw.
    split; [now rewrite <- app_assoc |].
    split; [exists indices, body, index, es; auto |]. split; assumption.
Qed.

Definition data_binary_wf data :=
  binary_vector_length_wf data.(moddata_init) /\
  match data.(moddata_mode) with
  | MD_passive => True
  | MD_active index es => binary_index_wf index /\ expression_binary_wf es
  end.

Theorem parse_module_data_printed_complete n :
  parser_complete (parse_module_data (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding data_binary_wf binary_of_data).
Proof.
  intros m bound input prefix suffix [init mode] Bytes [[Count Wf] Printed].
  destruct mode as [|index es].
  2: { pose proof (asserted_body_complete 2%N (parse_module_data_2 (n := n))
      data_active_encoding (parse_data_active_complete n)) as Leaf.
    assert (Complete : parser_complete
      (parse_module_data (Toks := SizedList byte) (M := option) (n := n))
      (subopcode_encoding 2%N data_active_encoding)).
    { unfold parse_module_data; subopcode_dispatch 2%N Leaf. }
    apply (Complete m bound input prefix suffix
      (Build_module_data init (MD_active index es)) Bytes).
    destruct Wf as [Index Expr].
    exists (binary_of_idx 2%N),
      (binary_of_idx index ++ binary_of_expr es ++
        binary_of_vec (fun b => byte_of_compcert_byte b :: nil) init).
    split; [exact Printed |].
    split; [apply binary_of_index_encoding; unfold binary_index_wf; lia |].
    exists (binary_of_idx index), (binary_of_expr es),
      (binary_of_vec (fun b => byte_of_compcert_byte b :: nil) init),
      index, es, (List.map byte_of_compcert_byte init).
    split; [reflexivity |]. split; [now apply binary_of_index_encoding |].
    split; [now apply binary_of_expr_encoding |]. split.
    + (* The bytes vector is raw, not per-byte LEB128. *)
      unfold binary_of_vec.
      rewrite <- (List.map_map byte_of_compcert_byte (fun b => b :: nil) init).
      rewrite <- (length_map byte_of_compcert_byte init) at 1.
      apply binary_of_vec_encoding.
      * apply Forall_forall; intros b Member; reflexivity.
      * unfold binary_vector_length_wf; now rewrite length_map.
    + now rewrite compcert_bytes_roundtrip. }
  - pose proof (asserted_body_complete 1%N (parse_module_data_1 (n := n))
      data_passive_encoding (parse_data_passive_complete n)) as Leaf.
    assert (Complete : parser_complete
      (parse_module_data (Toks := SizedList byte) (M := option) (n := n))
      (subopcode_encoding 1%N data_passive_encoding)).
    { unfold parse_module_data; subopcode_dispatch 1%N Leaf. }
    apply (Complete m bound input prefix suffix (Build_module_data init MD_passive) Bytes).
    exists (binary_of_idx 1%N),
      (binary_of_vec (fun b => byte_of_compcert_byte b :: nil) init).
    split; [exact Printed |]. split.
    + apply binary_of_index_encoding; unfold binary_index_wf; lia.
    + exists (List.map byte_of_compcert_byte init); split.
      * unfold binary_of_vec.
        rewrite <- (List.map_map byte_of_compcert_byte (fun b => b :: nil) init).
        rewrite <- (length_map byte_of_compcert_byte init) at 1.
        apply binary_of_vec_encoding.
        -- apply Forall_forall; intros b Member; reflexivity.
        -- unfold binary_vector_length_wf; now rewrite length_map.
      * now rewrite compcert_bytes_roundtrip.
Qed.

Lemma complete_concrete {A n}
    (p : Parser (SizedList byte) byte option A n) P bytes value :
  parser_complete p P -> P bytes value ->
  parser_complete p (fun parsed result => parsed = bytes /\ result = value).
Proof.
  intros Complete Encoding; eapply parser_complete_weaken; [exact Complete |].
  intros parsed result [Bytes Value]; now subst parsed result.
Qed.

Lemma concrete_map {A B n} (f : A -> B)
    (p : Parser (SizedList byte) byte option A n) bytes value :
  parser_complete p (fun parsed result => parsed = bytes /\ result = value) ->
  parser_complete (Combinators.map f p)
    (fun parsed result => parsed = bytes /\ result = f value).
Proof.
  intro Complete; eapply parser_complete_map; [exact Complete |].
  intros parsed result [Bytes Value]; exists value; auto.
Qed.

Lemma concrete_app {A B n}
    (p : Parser (SizedList byte) byte option (A -> B) n)
    (q : Parser (SizedList byte) byte option A n) xs ys f value :
  parser_complete p (fun parsed result => parsed = xs /\ result = f) ->
  parser_complete q (fun parsed result => parsed = ys /\ result = value) ->
  parser_complete (Combinators.app p (box q))
    (fun parsed result => parsed = xs ++ ys /\ result = f value).
Proof.
  intros P Q; eapply parser_complete_app with
    (P := fun parsed result => parsed = xs /\ result = f)
    (Q := fun parsed result => parsed = ys /\ result = value).
  - exact P.
  - intros k lt; simpl; now apply parser_complete_le_lower.
  - intros parsed result [Bytes Value].
    exists xs, ys, f, value; auto.
Qed.

Lemma expr_concrete n es :
  expression_binary_wf es ->
  parser_complete (parse_expr (Toks := SizedList byte) (M := option) (n := n))
    (fun parsed result => parsed = binary_of_expr es /\ result = es).
Proof.
  intro Wf; apply (complete_concrete _ Expression).
  - apply wasm_production_parse_expr_complete.
  - now apply binary_of_expr_encoding.
Qed.

Lemma expression_vector_concrete n inits :
  Forall expression_binary_wf inits -> binary_vector_length_wf inits ->
  parser_complete (parse_vec (parse_expr (Toks := SizedList byte) (M := option) (n := n)))
    (fun parsed result => parsed = binary_of_vec binary_of_expr inits /\ result = inits).
Proof.
  intros Wf Count.
  apply (complete_concrete _ (printed_encoding
    (fun values => Forall expression_binary_wf values /\ binary_vector_length_wf values)
    (binary_of_vec binary_of_expr))).
  - apply vector_printed_complete.
    apply (complete_printed_encoding _ Expression).
    + apply wasm_production_parse_expr_complete.
    + exact binary_of_expr_encoding.
  - split; [split; assumption |reflexivity].
Qed.

Lemma reference_concrete n rt :
  parser_complete (parse_reference_type (Toks := SizedList byte) (M := option) (n := n))
    (fun parsed result => parsed = binary_of_reference_type rt :: nil /\ result = rt).
Proof.
  apply (complete_concrete _ (fun bytes t => bytes = binary_of_reference_type t :: nil)).
  - apply parse_reference_type_complete.
  - reflexivity.
Qed.

Lemma index_concrete n index :
  binary_index_wf index ->
  parser_complete (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))
    (fun parsed result => parsed = binary_of_idx index /\ result = index).
Proof.
  intro Wf; apply (complete_concrete _ index_encoding).
  - apply leb128_properties.parse_u32_prefix_complete.
  - now apply binary_of_index_encoding.
Qed.

Definition element_binary_wf element :=
  Forall expression_binary_wf element.(modelem_init) /\
  binary_vector_length_wf element.(modelem_init) /\
  Forall (fun es => match to_ref_func es with
    | Some index => binary_index_wf index | None => True end) element.(modelem_init) /\
  match element.(modelem_mode) with
  | ME_active index es => binary_index_wf index /\ expression_binary_wf es
  | _ => True
  end.

Lemma to_ref_func_inverse es index :
  to_ref_func es = Some index -> es = BI_ref_func index :: nil.
Proof.
  destruct es as [|be [|be' rest]]; cbn [to_ref_func]; try discriminate.
  all: destruct be; try discriminate; intro Equal; inversion Equal; reflexivity.
Qed.

Lemma short_element_initializers inits indices :
  Forall (fun es => match to_ref_func es with
    | Some index => binary_index_wf index | None => True end) inits ->
  those (List.map to_ref_func inits) = Some indices ->
  inits = List.map (fun index => BI_ref_func index :: nil) indices /\
  Forall binary_index_wf indices /\ length indices = length inits.
Proof.
  intros Wf; rewrite <- those_those0; revert indices.
  induction Wf as [|es rest Head Rest IH]; intros indices Parsed.
  - inversion Parsed; subst; repeat split; constructor.
  - cbn [List.map those0] in Parsed.
    destruct (to_ref_func es) as [index|] eqn:Index; [|discriminate].
    destruct (those0 (List.map to_ref_func rest)) as [tail|] eqn:Tail; [|discriminate].
    inversion Parsed; subst indices.
    destruct (IH tail Logic.eq_refl) as [Inits [Bounds Count]].
    apply to_ref_func_inverse in Index; subst es.
    split; [simpl; now rewrite Inits |].
    split; [now constructor |simpl; now rewrite Count].
Qed.

Theorem parse_module_element_printed_complete n :
  parser_complete (parse_module_element (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding element_binary_wf binary_of_module_elem).
Proof.
  intros m bound input prefix suffix [rt inits mode] Bytes [[Exprs [Count [Short Wf]]] Printed].
  destruct mode as [|index es|].
  - assert (Body : parser_complete (parse_module_element_5 (M := option) (n := n))
      (fun parsed result => parsed =
        (binary_of_reference_type rt :: nil) ++ binary_of_vec binary_of_expr inits /\
        result = Build_module_element rt inits ME_passive)).
    { unfold parse_module_element_5.
      apply concrete_app with (f := fun els => Build_module_element rt els ME_passive) (value := inits);
        [apply concrete_map with (value := rt); apply reference_concrete |].
      now apply expression_vector_concrete. }
    pose proof (asserted_body_complete 5%N _ _ Body) as Leaf.
    assert (Complete : parser_complete (parse_module_element (M := option) (n := n))
      (subopcode_encoding 5%N (fun parsed result => parsed =
        (binary_of_reference_type rt :: nil) ++ binary_of_vec binary_of_expr inits /\
        result = Build_module_element rt inits ME_passive))).
    { unfold parse_module_element; subopcode_dispatch 5%N Leaf. }
    apply (Complete m bound input prefix suffix _ Bytes).
    exists (binary_of_idx 5%N),
      ((binary_of_reference_type rt :: nil) ++ binary_of_vec binary_of_expr inits).
    split; [exact Printed |]. split; [apply binary_of_index_encoding; unfold binary_index_wf; lia |].
    split; reflexivity.
  - destruct Wf as [Index Offset].
    destruct (elem_of_wasm_1_0 (Build_module_element rt inits (ME_active index es)))
      as [shortbytes|] eqn:Legacy.
    + assert (LegacyShape : index = 0%N /\ rt = T_funcref /\
        exists indices, those (List.map to_ref_func inits) = Some indices /\
          shortbytes = x00 :: binary_of_expr es ++ binary_of_vec binary_of_funcidx indices).
      { unfold elem_of_wasm_1_0 in Legacy; cbn [modelem_mode modelem_type modelem_init] in Legacy.
        destruct index; [|discriminate].
        destruct (rt == T_funcref) eqn:TypeRef; [|discriminate].
         assert (Equal : rt = T_funcref) by exact (elimT eqP TypeRef).
         subst rt.
         change (match those (List.map to_ref_func inits) with
           | Some ys => Some (x00 :: binary_of_expr es ++ binary_of_vec binary_of_funcidx ys)
           | None => None end = Some shortbytes) in Legacy.
        destruct (those (List.map to_ref_func inits)) as [indices|] eqn:E; [|discriminate].
        inversion Legacy; subst shortbytes; split; [reflexivity |].
        split; [reflexivity |exists indices; auto]. }
      destruct LegacyShape as [Zero [TypeRef [indices [Decode ShortBytes]]]].
      subst index rt shortbytes.
      destruct (short_element_initializers inits indices Short Decode) as [Inits [Bounds Length]].
      assert (Indices : parser_complete
        (parse_vec (parse_funcidx (M := option) (Toks := SizedList byte) (n := n)))
        (fun parsed result => parsed = binary_of_vec binary_of_funcidx indices /\ result = indices)).
      { apply (complete_concrete _ (printed_encoding
          (fun values => Forall binary_index_wf values /\ binary_vector_length_wf values)
          (binary_of_vec binary_of_funcidx))).
        - apply vector_printed_complete; apply parse_index_printed_complete.
        - split; [|reflexivity]. split; [exact Bounds |].
          change (N.of_nat (List.length indices) <= 4294967295)%N.
          change (List.length indices = List.length inits) in Length.
          rewrite Length; exact Count. }
      assert (Body : parser_complete (parse_module_element_0 (M := option) (n := n))
        (fun parsed result => parsed = binary_of_expr es ++ binary_of_vec binary_of_funcidx indices /\
          result = Build_module_element T_funcref inits (ME_active 0%N es))).
      { rewrite Inits; unfold parse_module_element_0.
        apply concrete_app with (f := fun fids => Build_module_element T_funcref
          (List.map (fun index => BI_ref_func index :: nil) fids) (ME_active 0%N es))
          (value := indices);
          [apply concrete_map with (value := es); now apply expr_concrete |exact Indices]. }
      pose proof (asserted_body_complete 0%N _ _ Body) as Leaf.
      assert (Complete : parser_complete (parse_module_element (M := option) (n := n))
        (subopcode_encoding 0%N (fun parsed result =>
          parsed = binary_of_expr es ++ binary_of_vec binary_of_funcidx indices /\
          result = Build_module_element T_funcref inits (ME_active 0%N es)))).
      { unfold parse_module_element; subopcode_dispatch 0%N Leaf. }
      apply (Complete m bound input prefix suffix _ Bytes).
      exists (binary_of_idx 0%N), (binary_of_expr es ++ binary_of_vec binary_of_funcidx indices).
      split.
      * unfold binary_of_module_elem in Printed; simpl in Printed; rewrite Legacy in Printed; exact Printed.
      * split; [apply binary_of_index_encoding; unfold binary_index_wf; lia |split; reflexivity].
    + assert (Body : parser_complete (parse_module_element_6 (M := option) (n := n))
        (fun parsed result => parsed = ((binary_of_idx index ++ binary_of_expr es) ++
          (binary_of_reference_type rt :: nil)) ++ binary_of_vec binary_of_expr inits /\
          result = Build_module_element rt inits (ME_active index es))).
      { unfold parse_module_element_6.
        apply concrete_app with
          (f := fun els => Build_module_element rt els (ME_active index es)) (value := inits).
        - apply concrete_app with
            (f := fun t els => Build_module_element t els (ME_active index es)) (value := rt).
          + apply concrete_app with
              (f := fun es t els => Build_module_element t els (ME_active index es)) (value := es).
            * apply concrete_map with (value := index); now apply index_concrete.
            * now apply expr_concrete.
          + apply reference_concrete.
        - now apply expression_vector_concrete. }
      pose proof (asserted_body_complete 6%N _ _ Body) as Leaf.
      assert (Complete : parser_complete (parse_module_element (M := option) (n := n))
        (subopcode_encoding 6%N (fun parsed result =>
          parsed = ((binary_of_idx index ++ binary_of_expr es) ++
            (binary_of_reference_type rt :: nil)) ++ binary_of_vec binary_of_expr inits /\
          result = Build_module_element rt inits (ME_active index es)))).
      { unfold parse_module_element; subopcode_dispatch 6%N Leaf. }
      apply (Complete m bound input prefix suffix _ Bytes).
      exists (binary_of_idx 6%N), (((binary_of_idx index ++ binary_of_expr es) ++
        (binary_of_reference_type rt :: nil)) ++ binary_of_vec binary_of_expr inits).
      split.
      * unfold binary_of_module_elem in Printed; simpl in Printed; rewrite Legacy in Printed.
        rewrite Printed; simpl; now repeat rewrite <- app_assoc.
      * split; [apply binary_of_index_encoding; unfold binary_index_wf; lia |split; reflexivity].
  - assert (Body : parser_complete (parse_module_element_7 (M := option) (n := n))
      (fun parsed result => parsed =
        (binary_of_reference_type rt :: nil) ++ binary_of_vec binary_of_expr inits /\
        result = Build_module_element rt inits ME_declarative)).
    { unfold parse_module_element_7.
      apply concrete_app with (f := fun els => Build_module_element rt els ME_declarative) (value := inits);
        [apply concrete_map with (value := rt); apply reference_concrete |].
      now apply expression_vector_concrete. }
    pose proof (asserted_body_complete 7%N _ _ Body) as Leaf.
    assert (Complete : parser_complete (parse_module_element (M := option) (n := n))
      (subopcode_encoding 7%N (fun parsed result => parsed =
        (binary_of_reference_type rt :: nil) ++ binary_of_vec binary_of_expr inits /\
        result = Build_module_element rt inits ME_declarative))).
    { unfold parse_module_element; subopcode_dispatch 7%N Leaf. }
    apply (Complete m bound input prefix suffix _ Bytes).
    exists (binary_of_idx 7%N),
      ((binary_of_reference_type rt :: nil) ++ binary_of_vec binary_of_expr inits).
    split; [exact Printed |]. split; [apply binary_of_index_encoding; unfold binary_index_wf; lia |].
    split; reflexivity.
Qed.

Theorem parse_elemsec_wrapper_printed_complete n :
  parser_complete (parse_elemsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf element_binary_wf binary_of_module_elem)
      binary_of_elemsec).
Proof.
  unfold parse_elemsec_wrapper, binary_of_elemsec.
  apply (wrapped_list_section_printed_complete x09); [discriminate |].
  unfold parse_elemsec; apply list_section_printed_complete.
  apply parse_module_element_printed_complete.
Qed.

Theorem parse_datasec_wrapper_printed_complete n :
  parser_complete (parse_datasec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf data_binary_wf binary_of_data)
      binary_of_datasec).
Proof.
  unfold parse_datasec_wrapper, binary_of_datasec.
  apply (wrapped_list_section_printed_complete x0b); [discriminate |].
  unfold parse_datasec; apply list_section_printed_complete.
  apply parse_module_data_printed_complete.
Qed.

Corollary binary_of_elemsec_wrapper_roundtrip elements :
  section_list_binary_wf element_binary_wf binary_of_module_elem elements ->
  run (binary_of_elemsec elements) (fun _ => parse_elemsec_wrapper) = Some elements.
Proof.
  intro Wf; apply (run_parser_complete _
    (printed_encoding (section_list_binary_wf element_binary_wf binary_of_module_elem)
      binary_of_elemsec)).
  - exact parse_elemsec_wrapper_printed_complete.
  - split; [exact Wf |reflexivity].
Qed.

Corollary binary_of_datasec_wrapper_roundtrip data :
  section_list_binary_wf data_binary_wf binary_of_data data ->
  run (binary_of_datasec data) (fun _ => parse_datasec_wrapper) = Some data.
Proof.
  intro Wf; apply (run_parser_complete _
    (printed_encoding (section_list_binary_wf data_binary_wf binary_of_data) binary_of_datasec)).
  - exact parse_datasec_wrapper_printed_complete.
  - split; [exact Wf |reflexivity].
Qed.
