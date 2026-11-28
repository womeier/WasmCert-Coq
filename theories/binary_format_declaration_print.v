(** Canonical printer membership for source recursive declarations. Domains
    constrain source AST fields/counts, not runs or byte-grammar membership. *)
From Stdlib Require Import List Strings.Byte NArith.
From Wasm Require Import datatypes gc_types binary_format_printer
  binary_format_declaration_properties binary_format_print_encoding
  binary_format_vector_properties.

Definition declaration_function_binary_wf ft :=
  match ft with Tf ins outs =>
    Forall declaration_value_binary_wf ins /\
    Forall declaration_value_binary_wf outs /\
    binary_vector_length_wf ins /\ binary_vector_length_wf outs
  end.

Definition declaration_storage_binary_wf storage :=
  match storage with ST_value value => declaration_value_binary_wf value
  | ST_packed _ => True end.

Definition declaration_field_binary_wf field :=
  declaration_storage_binary_wf (field_storage field).

Definition declaration_composite_binary_wf composite :=
  match composite with
  | Comp_func ft => declaration_function_binary_wf ft
  | Comp_struct fields => Forall declaration_field_binary_wf fields /\
      binary_vector_length_wf fields
  | Comp_array field => declaration_field_binary_wf field
  end.

Definition declaration_subtype_binary_wf subtype :=
  Forall binary_index_wf (subtype_supers subtype) /\
  binary_vector_length_wf (subtype_supers subtype) /\
  declaration_composite_binary_wf (subtype_composite subtype).

Definition recursive_type_binary_wf group :=
  Forall declaration_subtype_binary_wf group /\ binary_vector_length_wf group.

Lemma binary_of_declaration_values_encoding values :
  Forall declaration_value_binary_wf values ->
  binary_vector_length_wf values ->
  vector_encoding declaration_value_encoding (binary_of_value_types values) values.
Proof.
  intros Wf Count; apply binary_of_vec_encoding; [|exact Count].
  clear Count.
  induction Wf; constructor; [now apply binary_of_declaration_value_encoding|assumption].
Qed.

Lemma binary_of_declaration_function_encoding ft :
  declaration_function_binary_wf ft ->
  declaration_function_encoding (binary_of_functype ft) ft.
Proof.
  destruct ft as [ins outs]; intros [Ins [Outs [InCount OutCount]]].
  exists (binary_of_result_type ins ++ binary_of_result_type outs); split; [reflexivity|].
  exists (ins, outs); split; [|reflexivity].
  exists (binary_of_result_type ins), (binary_of_result_type outs), ins, outs.
  split; [reflexivity|]; split.
  - now apply binary_of_declaration_values_encoding.
  - split; [now apply binary_of_declaration_values_encoding|reflexivity].
Qed.

Lemma binary_of_declaration_storage_encoding storage :
  declaration_storage_binary_wf storage ->
  declaration_storage_encoding (binary_of_storage_type storage) storage.
Proof.
  destruct storage as [value|packed]; intro Wf.
  - right; right; exists value; split;
      [now apply binary_of_declaration_value_encoding|reflexivity].
  - destruct packed; [left|right; left]; auto.
Qed.

Lemma binary_of_declaration_field_encoding field :
  declaration_field_binary_wf field ->
  declaration_field_encoding (binary_of_field_type field) field.
Proof.
  destruct field as [mut storage]; intro Wf.
  exists (binary_of_storage_type storage),
    ((match mut with MUT_const => Byte.x00 | MUT_var => Byte.x01 end) :: nil),
    storage, mut.
  split; [reflexivity|]; split.
  - now apply binary_of_declaration_storage_encoding.
  - split; [destruct mut; [left|right]; auto|reflexivity].
Qed.

Lemma binary_of_declaration_composite_encoding composite :
  declaration_composite_binary_wf composite ->
  declaration_composite_encoding (binary_of_composite_type composite) composite.
Proof.
  destruct composite as [ft|fields|field]; intro Wf.
  - left; exists ft; split; [now apply binary_of_declaration_function_encoding|reflexivity].
  - right; left; exists (binary_of_vec binary_of_field_type fields).
    split; [reflexivity|].
    exists fields; split; [|reflexivity].
    destruct Wf as [Fields Count]; apply binary_of_vec_encoding; [|exact Count].
    clear Count.
    induction Fields; constructor; [now apply binary_of_declaration_field_encoding|assumption].
  - right; right; exists (binary_of_field_type field); split; [reflexivity|].
    exists field; split; [now apply binary_of_declaration_field_encoding|reflexivity].
Qed.

Lemma binary_of_declaration_subtype_encoding subtype :
  declaration_subtype_binary_wf subtype ->
  declaration_subtype_encoding (binary_of_subtype subtype) subtype.
Proof.
  destruct subtype as [final supers composite]; intros [Supers [Count Composite]].
  cbn in Supers, Count, Composite.
  assert (SuperEncoding : vector_encoding
      (fun bs x => leb128_properties.unsigned_leb bs x /\
        (x <= 4294967295)%N /\ length bs <= 5)
      (binary_of_vec binary_of_typeidx supers) supers).
  { apply binary_of_vec_encoding; [|exact Count].
    clear Count Composite.
    induction Supers; constructor; [now apply binary_of_index_encoding|assumption]. }
  pose proof (binary_of_declaration_composite_encoding composite Composite) as Encoded.
  destruct final, supers as [|super supers].
  - right; right; exists composite; auto.
  - right; left.
    exists (Byte.x4f :: binary_of_vec binary_of_typeidx (super :: supers)),
      (binary_of_composite_type composite), (super :: supers), composite.
    split; [reflexivity|]; split.
    + exists (binary_of_vec binary_of_typeidx (super :: supers)); auto.
    + auto.
  - left.
    exists (Byte.x50 :: binary_of_vec binary_of_typeidx nil),
      (binary_of_composite_type composite), nil, composite.
    split; [reflexivity|]; split.
    + exists (binary_of_vec binary_of_typeidx nil); auto.
    + auto.
  - left.
    exists (Byte.x50 :: binary_of_vec binary_of_typeidx (super :: supers)),
      (binary_of_composite_type composite), (super :: supers), composite.
    split; [reflexivity|]; split.
    + exists (binary_of_vec binary_of_typeidx (super :: supers)); auto.
    + auto.
Qed.

Theorem binary_of_recursive_type_encoding group :
  recursive_type_binary_wf group ->
  declaration_recursive_encoding (binary_of_recursive_type group) group.
Proof.
  intros [Items Count].
  assert (Vector : vector_encoding declaration_subtype_encoding
    (binary_of_vec binary_of_subtype group) group).
  { apply binary_of_vec_encoding; [|exact Count].
    clear Count.
    induction Items; constructor; [now apply binary_of_declaration_subtype_encoding|assumption]. }
  destruct group as [|subtype [|next rest]].
  - left; exists (binary_of_vec binary_of_subtype nil); auto.
  - right; exists subtype; split; [|reflexivity].
    inversion Items; now apply binary_of_declaration_subtype_encoding.
  - left; exists (binary_of_vec binary_of_subtype (subtype :: next :: rest)); auto.
Qed.
