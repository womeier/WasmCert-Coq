(** Minimal generic printer dependencies adapted from pinned bc7c190. *)
From Stdlib Require Import List Strings.Byte Arith NArith ZArith Lia.
From Wasm Require Import binary_format_printer binary_format_atomic_properties
  binary_format_vector_properties leb128_unsigned_printer_properties.
Local Notation byte := Byte.byte.

Definition binary_index_wf x := (x <= 4294967295)%N.
Definition binary_vector_length_wf {A} (xs : list A) :=
  (N.of_nat (length xs) <= 4294967295)%N.

Lemma binary_of_index_encoding x :
  binary_index_wf x -> index_encoding (binary_of_idx x) x.
Proof.
  intro Bound; unfold binary_of_idx, binary_of_u32, binary_of_N.
  split; [apply encode_unsigned_sound |]. split; [exact Bound |].
  apply (encode_unsigned_length_bound 4).
  change (Z.of_N x < 34359738368)%Z; unfold binary_index_wf in Bound; lia.
Qed.

Lemma binary_of_vec_encoding {A} (print : A -> list byte) Grammar values :
  Forall (fun value => Grammar (print value) value) values ->
  binary_vector_length_wf values ->
  vector_encoding Grammar (binary_of_vec print values) values.
Proof.
  intros Items Count.
  exists (binary_of_u32 (N.of_nat (length values))),
    (concat (List.map print values)).
  split; [reflexivity |].
  destruct (binary_of_index_encoding _ Count) as [Encoding [Range Width]].
  split; [exact Encoding |]. split; [exact Range |]. split; [exact Width |].
  clear Count Encoding Range Width.
  induction Items; simpl; constructor; assumption.
Qed.
