(** Actual bounded name/import/export/start and index section printers. *)
From Stdlib Require Import List Strings.Byte NArith.
From parseque Require Import Parseque.
From Wasm Require Import datatypes utf8 binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_parser_lookahead_properties
  binary_format_language_properties binary_format_atomic_properties
  binary_format_numeric_complete binary_format_control_complete
  binary_format_print_encoding binary_format_vector_properties binary_format_vector_print
  binary_format_limits_properties binary_format_global_properties
  binary_format_code_properties binary_format_section_properties
  binary_format_custom_complete.
Local Notation byte := Byte.byte.
Ltac byte_type_dispatch tag Complete Head := control_byte_dispatch tag Complete Head.

Definition printed_encoding {A} (Wf : A -> Prop) (print : A -> list byte) bytes value :=
  Wf value /\ bytes = print value.

Lemma complete_printed_encoding {A n}
    (p : Parser (SizedList byte) byte option A n) Grammar Wf print :
  parser_complete p Grammar ->
  (forall value, Wf value -> Grammar (print value) value) ->
  parser_complete p (printed_encoding Wf print).
Proof.
  intros Complete Prints; eapply parser_complete_weaken; [exact Complete |].
  intros bytes value [WfValue Bytes]; subst bytes; now apply Prints.
Qed.

Definition name_binary_wf name :=
  utf8_valid name = true /\ binary_vector_length_wf name.

Theorem parse_name_printed_complete n :
  parser_complete (parse_name (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding name_binary_wf binary_of_name).
Proof.
  unfold parse_name.
  eapply parser_complete_guardM with
    (P := vector_encoding (fun bytes b => bytes = b :: nil)).
  - apply parse_vec_complete; apply parser_complete_anyTok.
  - intros bytes name [[Valid Count] Bytes]; subst bytes.
    exists name; split.
    + apply binary_of_vec_encoding; [|exact Count].
      apply Forall_forall; intros b Member; reflexivity.
    + now rewrite Valid.
Qed.

Lemma prefixed_printed_complete {A B n} tag
    (p : Parser (SizedList byte) byte option A n) Wf print (make : A -> B) :
  parser_complete p (printed_encoding Wf print) ->
  parser_complete
    (Combinators.rand (exact_byte tag) (box (Combinators.map make p)))
    (fun bytes value => exists a, Wf a /\ bytes = tag :: print a /\ value = make a).
Proof.
  intro Complete.
  apply parser_complete_prefix_byte with
    (Q := fun bytes value => exists a, printed_encoding Wf print bytes a /\ value = make a).
  - intros k lt; simpl; apply parser_complete_le_lower.
    eapply parser_complete_map; [exact Complete |].
    intros bytes value [a [E Value]]; exists a; auto.
  - intros bytes value [a [Valid [Bytes Value]]].
    exists (print a); split; [exact Bytes |].
    exists a; split; [split; [exact Valid |reflexivity] |exact Value].
Qed.

Lemma prefixed_printed_head {A B} (tag : byte) (Wf : A -> Prop) print (make : A -> B) bytes value :
  (exists a, Wf a /\ bytes = tag :: print a /\ value = make a) ->
  exists rest, bytes = tag :: rest.
Proof. intros [a [_ [Bytes _]]]; now exists (print a). Qed.

Lemma parse_index_printed_complete n :
  parser_complete (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding binary_index_wf binary_of_idx).
Proof.
  apply (complete_printed_encoding _ index_encoding).
  - apply leb128_properties.parse_u32_prefix_complete.
  - exact binary_of_index_encoding.
Qed.

Lemma parse_limits_printed_complete n :
  parser_complete (parse_limits (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding limits_binary_wf binary_of_limits).
Proof.
  apply (complete_printed_encoding _ limits_encoding).
  - apply parse_limits_complete.
  - exact binary_of_limits_encoding.
Qed.

Lemma parse_table_type_printed_complete n :
  parser_complete (parse_table_type (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding table_type_binary_wf binary_of_table_type).
Proof.
  apply (complete_printed_encoding _ table_type_encoding).
  - apply parse_table_type_complete.
  - intros tt [Limits Ref]; now apply binary_of_table_type_encoding.
Qed.

Lemma parse_memory_type_printed_complete n :
  parser_complete (parse_memory_type (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding limits_binary_wf binary_of_memory_type).
Proof.
  apply (complete_printed_encoding _ limits_encoding).
  - apply parse_memory_type_complete.
  - exact binary_of_limits_encoding.
Qed.

Lemma parse_global_type_printed_complete n :
  parser_complete (parse_global_type (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (fun gt => source_value_binary_wf gt.(tg_t)) binary_of_global_type).
Proof.
  apply (complete_printed_encoding _ global_type_encoding).
  - apply parse_global_type_complete.
  - exact global_type_printer_membership.
Qed.

Definition import_desc_binary_wf desc :=
  match desc with
  | MID_func x => binary_index_wf x
  | MID_table tabty => table_type_binary_wf tabty
  | MID_mem mt => limits_binary_wf mt
  | MID_global gt => source_value_binary_wf gt.(tg_t)
  | MID_tag x => binary_index_wf x
  end.

Theorem parse_import_desc_printed_complete n :
  parser_complete (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding import_desc_binary_wf binary_of_import_desc).
Proof.
  intros m bound input prefix suffix desc Bytes [Wf Printed].
  destruct desc as [x|tt|mt|gt|x].
  - pose proof (prefixed_printed_complete x00 (parse_u32_as_N (n := n))
      binary_index_wf binary_of_idx MID_func (parse_index_printed_complete n)) as Leaf.
    assert (Complete : parser_complete
      (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => exists a, binary_index_wf a /\
        bytes = x00 :: binary_of_idx a /\ value = MID_func a)).
    { unfold parse_import_desc; apply parser_complete_alt_left; exact Leaf. }
    apply (Complete m bound input prefix suffix (MID_func x) Bytes).
    exists x; auto.
  - pose proof (prefixed_printed_complete x01 (parse_table_type (n := n))
      table_type_binary_wf binary_of_table_type MID_table
      (parse_table_type_printed_complete n)) as Leaf.
    assert (Complete : parser_complete
      (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => exists a, table_type_binary_wf a /\
        bytes = x01 :: binary_of_table_type a /\ value = MID_table a)).
    { unfold parse_import_desc.
      byte_type_dispatch x01 Leaf
        (prefixed_printed_head x01 table_type_binary_wf
          binary_of_table_type MID_table). }
    apply (Complete m bound input prefix suffix (MID_table tt) Bytes).
    exists tt; auto.
  - pose proof (prefixed_printed_complete x02 (parse_memory_type (n := n))
      limits_binary_wf binary_of_memory_type MID_mem
      (parse_memory_type_printed_complete n)) as Leaf.
    assert (Complete : parser_complete
      (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => exists a, limits_binary_wf a /\
        bytes = x02 :: binary_of_memory_type a /\ value = MID_mem a)).
    { unfold parse_import_desc.
      byte_type_dispatch x02 Leaf
        (prefixed_printed_head x02 limits_binary_wf binary_of_memory_type MID_mem). }
    apply (Complete m bound input prefix suffix (MID_mem mt) Bytes).
    exists mt; auto.
  - pose proof (prefixed_printed_complete x03 (parse_global_type (n := n))
      (fun gt => source_value_binary_wf gt.(tg_t)) binary_of_global_type MID_global
      (parse_global_type_printed_complete n)) as Leaf.
    assert (Complete : parser_complete
      (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
      (fun bytes value => exists a, source_value_binary_wf a.(tg_t) /\
        bytes = x03 :: binary_of_global_type a /\ value = MID_global a)).
    { unfold parse_import_desc.
      byte_type_dispatch x03 Leaf
        (prefixed_printed_head x03 (fun gt => source_value_binary_wf gt.(tg_t))
          binary_of_global_type MID_global). }
    apply (Complete m bound input prefix suffix (MID_global gt) Bytes).
    exists gt; auto.
  - assert (Leaf : parser_complete
      (Combinators.rand (exact_byte (n := n) x04)
        (box (Combinators.rand (exact_byte x00) (box (Combinators.map MID_tag parse_typeidx)))))
      (fun bytes value => exists a, binary_index_wf a /\
        bytes = x04 :: x00 :: binary_of_idx a /\ value = MID_tag a)).
    { apply parser_complete_prefix_byte with
        (Q := fun bytes value => exists a, binary_index_wf a /\
          bytes = x00 :: binary_of_idx a /\ value = MID_tag a).
      - intros k lt; simpl; apply parser_complete_le_lower.
        apply prefixed_printed_complete; apply parse_index_printed_complete.
      - intros bytes value [a [Valid [Parts Value]]]; exists (x00 :: binary_of_idx a).
        split; [exact Parts |exists a; auto]. }
    assert (Complete : parser_complete (parse_import_desc (n := n))
      (fun bytes value => exists a, binary_index_wf a /\
        bytes = x04 :: x00 :: binary_of_idx a /\ value = MID_tag a)).
    { unfold parse_import_desc.
      assert (Head : forall bs value,
        (exists a, binary_index_wf a /\
          bs = x04 :: x00 :: binary_of_idx a /\ value = MID_tag a) ->
        exists rest, bs = x04 :: rest).
      { intros bs value [a [_ [Parts _]]]; exists (x00 :: binary_of_idx a); exact Parts. }
      byte_type_dispatch x04 Leaf Head. }
    apply (Complete m bound input prefix suffix (MID_tag x) Bytes); exists x; auto.
Qed.

Definition import_binary_wf imp :=
  name_binary_wf imp.(imp_module) /\ name_binary_wf imp.(imp_name) /\
  import_desc_binary_wf imp.(imp_desc).

Theorem parse_module_import_printed_complete n :
  parser_complete (parse_module_import (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding import_binary_wf binary_of_module_import).
Proof.
  unfold parse_module_import.
  eapply parser_complete_map with
    (P := fun bytes triple => exists first second third,
      bytes = first ++ second ++ third /\
      printed_encoding name_binary_wf binary_of_name first (fst (fst triple)) /\
      printed_encoding name_binary_wf binary_of_name second (snd (fst triple)) /\
      printed_encoding import_desc_binary_wf binary_of_import_desc third (snd triple)).
  - unfold Combinators.and.
    eapply parser_complete_andbind with
      (P := fun bytes pair => exists first second, bytes = first ++ second /\
        printed_encoding name_binary_wf binary_of_name first (fst pair) /\
        printed_encoding name_binary_wf binary_of_name second (snd pair))
      (Q := fun _ => printed_encoding import_desc_binary_wf binary_of_import_desc).
    + eapply parser_complete_andbind with
        (P := printed_encoding name_binary_wf binary_of_name)
        (Q := fun _ => printed_encoding name_binary_wf binary_of_name).
      * apply parse_name_printed_complete.
      * intros name k lt; simpl; apply parser_complete_le_lower; apply parse_name_printed_complete.
      * intros bytes first second E; exact E.
    + intros pair k lt; simpl; apply parser_complete_le_lower; apply parse_import_desc_printed_complete.
    + intros bytes [modul name] desc [first [second [third [Bytes [M [N D]]]]]].
      exists (first ++ second), third.
      split; [now rewrite <- app_assoc |]. split; [exists first, second; auto |exact D].
  - intros bytes [modul name desc] [[Module [Name Desc]] Bytes].
    exists (modul, name, desc); split; [|reflexivity].
    exists (binary_of_name modul), (binary_of_name name), (binary_of_import_desc desc).
    split; [exact Bytes |]. split; [split; [exact Module |reflexivity] |].
    split; split; assumption || reflexivity.
Qed.

Definition export_desc_binary_wf desc :=
  match desc with
  | MED_func x | MED_table x | MED_mem x | MED_global x | MED_tag x => binary_index_wf x
  end.

Ltac export_descriptor_case tag make n m bound input prefix suffix x Bytes Wf Printed :=
  let Leaf := fresh "Leaf" in
  pose proof (prefixed_printed_complete tag (parse_u32_as_N (n := n))
    binary_index_wf binary_of_idx make (parse_index_printed_complete n)) as Leaf;
  let Complete := fresh "Complete" in
  assert (Complete : parser_complete
    (parse_module_export_desc (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => exists a, binary_index_wf a /\
      bytes = tag :: binary_of_idx a /\ value = make a)) by
    (unfold parse_module_export_desc;
     byte_type_dispatch tag Leaf (prefixed_printed_head tag binary_index_wf binary_of_idx make));
  apply (Complete m bound input prefix suffix (make x) Bytes);
  exists x; split; [exact Wf |]; split; [exact Printed |reflexivity].

Theorem parse_export_desc_printed_complete n :
  parser_complete (parse_module_export_desc (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding export_desc_binary_wf binary_of_export_desc).
Proof.
  intros m bound input prefix suffix desc Bytes [Wf Printed].
   destruct desc as [x|x|x|x|x].
  - export_descriptor_case x00 MED_func n m bound input prefix suffix x Bytes Wf Printed.
  - export_descriptor_case x01 MED_table n m bound input prefix suffix x Bytes Wf Printed.
  - export_descriptor_case x02 MED_mem n m bound input prefix suffix x Bytes Wf Printed.
   - export_descriptor_case x03 MED_global n m bound input prefix suffix x Bytes Wf Printed.
   - export_descriptor_case x04 MED_tag n m bound input prefix suffix x Bytes Wf Printed.
Qed.

Definition export_binary_wf export :=
  name_binary_wf export.(modexp_name) /\ export_desc_binary_wf export.(modexp_desc).

Theorem parse_module_export_printed_complete n :
  parser_complete (parse_module_export (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding export_binary_wf binary_of_module_export).
Proof.
  unfold parse_module_export.
  eapply parser_complete_app with
    (P := fun bytes f => exists name, printed_encoding name_binary_wf binary_of_name bytes name /\
      f = (fun desc => Build_module_export name desc))
    (Q := printed_encoding export_desc_binary_wf binary_of_export_desc).
  - eapply parser_complete_map; [apply parse_name_printed_complete |].
    intros bytes f [name [E Value]]; exists name; auto.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_export_desc_printed_complete.
  - intros bytes [name desc] [[Name Desc] Bytes].
    exists (binary_of_name name), (binary_of_export_desc desc),
      (fun desc => Build_module_export name desc), desc.
    split; [exact Bytes |]. split.
    + exists name; split; [split; [exact Name |reflexivity] |reflexivity].
    + split; [split; [exact Desc |reflexivity] |reflexivity].
Qed.

Theorem parse_module_start_printed_complete n :
  parser_complete (parse_module_start (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (fun s => binary_index_wf s.(modstart_func)) binary_of_module_start).
Proof.
  unfold parse_module_start.
  eapply parser_complete_map; [apply parse_index_printed_complete |].
  intros bytes [index] [Wf Bytes]; exists index; split; [split; assumption |reflexivity].
Qed.

Definition section_list_binary_wf {A} (Wf : A -> Prop) print values :=
  Forall Wf values /\ binary_vector_length_wf values /\
  binary_vector_length_wf (binary_of_vec print values).

Lemma framed_printed_complete {A n} tag
    (p : Parser (SizedList byte) byte option A n) Wf print :
  parser_complete p (printed_encoding Wf print) ->
  parser_complete (Combinators.rand (exact_byte tag) (box (parse_section_payload p)))
    (printed_encoding (fun value => Wf value /\ binary_vector_length_wf (print value))
      (fun value => tag :: with_length (print value))).
Proof.
  intro Complete.
  apply (complete_printed_encoding _
    (fun bytes value => exists payload, bytes = tag :: payload /\
      section_payload_encoding (printed_encoding Wf print) payload value)).
  - apply parser_complete_prefix_byte with
      (Q := section_payload_encoding (printed_encoding Wf print)).
    + intros k lt; simpl; apply parser_complete_le_lower.
      now apply parse_section_payload_complete.
    + intros bytes value E; exact E.
  - intros value [Valid Size].
    exists (with_length (print value)); split; [reflexivity |].
    apply with_length_encoding; [split; [exact Valid |reflexivity] |exact Size].
Qed.

Lemma vector_printed_complete {A n}
    (p : Parser (SizedList byte) byte option A n) Wf print :
  parser_complete p (printed_encoding Wf print) ->
  parser_complete (parse_vec p)
    (printed_encoding (fun values => Forall Wf values /\ binary_vector_length_wf values)
      (binary_of_vec print)).
Proof.
  intro Complete; apply (complete_printed_encoding _ (vector_encoding (printed_encoding Wf print))).
  - now apply parse_vec_complete.
  - intros values [Valid Count].
    apply binary_of_vec_encoding; [|exact Count].
    clear Count; induction Valid; constructor; [split; [assumption |reflexivity] |assumption].
Qed.

Lemma list_section_printed_complete {A n} tag
    (p : Parser (SizedList byte) byte option A n) Wf print :
  parser_complete p (printed_encoding Wf print) ->
  parser_complete
    (Combinators.rand (exact_byte tag) (box (parse_section_payload (parse_vec p))))
    (printed_encoding (section_list_binary_wf Wf print)
      (fun values => tag :: with_length (binary_of_vec print values))).
Proof.
  intro Complete.
  eapply parser_complete_weaken.
  - apply framed_printed_complete; apply vector_printed_complete; exact Complete.
  - intros bytes values [[Valid [Count Size]] Bytes]; split; [|exact Bytes].
    split; [split; [exact Valid |exact Count] |exact Size].
Qed.

Lemma wrapped_list_section_printed_complete {A n} tag
    (p : Parser (SizedList byte) byte option (list A) n) Wf print :
  tag <> x00 ->
  parser_complete p (printed_encoding (section_list_binary_wf Wf print)
    (fun values => tag :: with_length (binary_of_vec print values))) ->
  parser_complete (parse_with_customsec_star_before p)
    (printed_encoding (section_list_binary_wf Wf print)
      (fun values => tag :: with_length (binary_of_vec print values))).
Proof.
  intros NotCustom Complete.
  apply parse_with_customsec_star_before_complete_without_custom; [|exact Complete].
  intros bytes values [_ Bytes].
  exists tag, (with_length (binary_of_vec print values)); auto.
Qed.

Theorem parse_importsec_wrapper_printed_complete n :
  parser_complete (parse_importsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf import_binary_wf binary_of_module_import)
      binary_of_importsec).
Proof.
  unfold parse_importsec_wrapper, binary_of_importsec.
  apply (wrapped_list_section_printed_complete x02); [discriminate |].
  unfold parse_importsec; apply list_section_printed_complete.
  apply parse_module_import_printed_complete.
Qed.

Theorem parse_exportsec_wrapper_printed_complete n :
  parser_complete (parse_exportsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf export_binary_wf binary_of_module_export)
      binary_of_exportssec).
Proof.
  unfold parse_exportsec_wrapper, binary_of_exportssec.
  apply (wrapped_list_section_printed_complete x07); [discriminate |].
  unfold parse_exportsec; apply list_section_printed_complete.
  apply parse_module_export_printed_complete.
Qed.

Theorem parse_funcsec_wrapper_printed_complete n :
  parser_complete (parse_funcsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding (section_list_binary_wf binary_index_wf binary_of_typeidx)
      (fun indices => x03 :: with_length (binary_of_vec binary_of_typeidx indices))).
Proof.
  unfold parse_funcsec_wrapper.
  apply (wrapped_list_section_printed_complete x03); [discriminate |].
  unfold parse_funcsec; apply list_section_printed_complete.
  apply parse_index_printed_complete.
Qed.

Theorem parse_startsec_wrapper_printed_complete n :
  parser_complete (parse_startsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding
      (fun s => binary_index_wf s.(modstart_func) /\
        binary_vector_length_wf (binary_of_module_start s)) binary_of_startsec).
Proof.
  unfold parse_startsec_wrapper.
  apply parse_with_customsec_star_before_complete_without_custom.
  - intros bytes s [_ Bytes]; exists x08, (with_length (binary_of_module_start s)).
    split; [exact Bytes |discriminate].
  - unfold parse_startsec; apply framed_printed_complete; apply parse_module_start_printed_complete.
Qed.

Theorem parse_datacountsec_wrapper_printed_complete n :
  parser_complete (parse_datacountsec_wrapper (Toks := SizedList byte) (M := option) (n := n))
    (printed_encoding
      (fun count => binary_index_wf count /\ binary_vector_length_wf (binary_of_u32 count))
      (fun count => x0c :: with_length (binary_of_u32 count))).
Proof.
  unfold parse_datacountsec_wrapper.
  apply parse_with_customsec_star_before_complete_without_custom.
  - intros bytes count [_ Bytes]; exists x0c, (with_length (binary_of_u32 count)).
    split; [exact Bytes |discriminate].
  - unfold parse_datacountsec; apply framed_printed_complete; apply parse_index_printed_complete.
Qed.
