(** The local packer's semantic inverse, independently of byte encoding. *)
From Stdlib Require Import List PeanoNat NArith Lia Strings.Byte.
From parseque Require Import Parseque Success.
From mathcomp Require Import ssrbool eqtype.
From Wasm Require Import datatypes_properties binary_format_printer
  binary_format_parser binary_locals_properties binary_vector_properties
  binary_uleb128 binary_uleb128_printer gc_types.

Definition unpack_locals (decls : list (nat * value_type)) : list value_type :=
  List.concat (List.map (fun '(count, type) => List.repeat type count) decls).

Lemma unpack_locals_app : forall first second,
    unpack_locals (List.app first second) =
      List.app (unpack_locals first) (unpack_locals second).
Proof.
  intros first second. unfold unpack_locals.
  rewrite List.map_app, List.concat_app. reflexivity.
Qed.

Lemma bunch_locals_aux_positive : forall types current count acc,
    (0 < count)%nat ->
    List.Forall (fun decl => (0 < fst decl)%nat) acc ->
    List.Forall (fun decl => (0 < fst decl)%nat)
      (bunch_locals_aux current count acc types).
Proof.
  induction types as [|type types IH]; intros current count acc Hcount Hacc.
  - cbn [bunch_locals_aux]. apply List.Forall_rev.
    constructor; assumption.
  - cbn [bunch_locals_aux].
    destruct (current == type).
    + apply IH; [exact (Nat.lt_lt_add_r _ _ _ Hcount) | exact Hacc].
    + apply IH; [exact (Nat.lt_0_succ 0) |]. constructor; assumption.
Qed.

Lemma bunch_locals_positive : forall types,
    List.Forall (fun decl => (0 < fst decl)%nat) (bunch_locals types).
Proof.
  intros [|type types]; [constructor |].
  apply bunch_locals_aux_positive; [lia | constructor].
Qed.

Lemma unpack_locals_length_bound : forall decls,
    List.Forall (fun decl => (0 < fst decl)%nat) decls ->
    (List.length decls <= List.length (unpack_locals decls))%nat.
Proof.
  intros decls Hpositive.
  induction Hpositive as [|[count type] decls Hcount Htail IH].
  - reflexivity.
  - change (S (List.length decls) <=
      List.length (List.app (List.repeat type count) (unpack_locals decls)))%nat.
    rewrite List.length_app, List.repeat_length. cbn in Hcount. lia.
Qed.

Lemma bunch_locals_aux_inverse : forall types current count acc,
    unpack_locals (bunch_locals_aux current count acc types) =
      List.app (unpack_locals (List.rev acc))
        (List.app (List.repeat current count) types).
Proof.
  induction types as [|type types IH]; intros current count acc.
  - cbn [bunch_locals_aux].
    cbn [List.rev]. rewrite unpack_locals_app.
    cbn [unpack_locals List.map List.concat].
    now rewrite !List.app_nil_r.
  - cbn [bunch_locals_aux].
    destruct (current == type) eqn:Heq.
    + assert (Hequal : current = type) by exact (elimT eqP Heq).
      subst type.
      rewrite IH, List.repeat_app.
      cbn [List.repeat].
      now rewrite <- List.app_assoc.
    + rewrite IH. cbn [List.rev]. rewrite unpack_locals_app.
      cbn [unpack_locals List.map List.concat List.repeat].
      rewrite !List.app_nil_r.
      now rewrite <- List.app_assoc.
Qed.

Theorem bunch_locals_inverse : forall types,
    unpack_locals (bunch_locals types) = types.
Proof.
  intros [|type types]; [reflexivity |].
  unfold bunch_locals. rewrite bunch_locals_aux_inverse.
  reflexivity.
Qed.

Definition binary_local_decls (decls : list (nat * value_type)) :=
  List.map (fun '(count, type) => (N.of_nat count, type)) decls.

Lemma binary_local_decls_expansion : forall decls,
    locals_expansion (binary_local_decls decls) = unpack_locals decls.
Proof.
  induction decls as [|[count type] decls IH]; [reflexivity |].
  change (List.app (List.repeat type (N.to_nat (N.of_nat count)))
    (locals_expansion (binary_local_decls decls)) =
    List.app (List.repeat type count) (unpack_locals decls)).
  now rewrite Nat2N.id, IH.
Qed.

Lemma binary_local_decls_total_aux : forall decls acc,
    List.fold_left (fun a b => N.add a b)
      (List.map fst (binary_local_decls decls)) acc =
    N.add acc (N.of_nat (List.length (unpack_locals decls))).
Proof.
  induction decls as [|[count type] decls IH]; intro acc.
  - cbn. now rewrite N.add_0_r.
  - change (List.fold_left (fun a b => N.add a b)
      (List.map fst (binary_local_decls decls)) (N.add acc (N.of_nat count)) =
      N.add acc (N.of_nat (List.length
        (List.app (List.repeat type count) (unpack_locals decls))))).
    rewrite IH, List.length_app, List.repeat_length, Nat2N.inj_add.
    now rewrite N.add_assoc.
Qed.

Theorem bunch_locals_expansion : forall types,
    locals_expansion (binary_local_decls (bunch_locals types)) = types.
Proof.
  intro types. rewrite binary_local_decls_expansion.
  apply bunch_locals_inverse.
Qed.

Theorem bunch_locals_total : forall types,
    locals_total (binary_local_decls (bunch_locals types)) =
      N.of_nat (List.length types).
Proof.
  intro types. unfold locals_total.
  rewrite binary_local_decls_total_aux, N.add_0_l, bunch_locals_inverse.
  reflexivity.
Qed.

Corollary verify_bunched_locals : forall types,
    (N.of_nat (List.length types) < 4294967296)%N ->
    verify_locals (binary_local_decls (bunch_locals types)) = Some types.
Proof.
  intros types Hbound.
  rewrite <- (bunch_locals_expansion types) at 2.
  apply verify_locals_accept.
  now rewrite bunch_locals_total.
Qed.

(** Only types accepted by the current concrete binary value-type parser are
    claimed here. Indexed reference encodings belong to its shared extension. *)
Definition printable_local_type type :=
  match type with
  | T_num _ | T_vec _ => True
  | T_ref reference =>
      exists abstract, reference = shared_reference_of_abstract abstract
  | T_bot => False
  end.

Lemma printable_local_type_suffix : forall type suffix,
    printable_local_type type ->
    concrete_valtype_prefix (List.app (binary_of_value_type type) suffix) type suffix.
Proof.
  intros [number | vector | reference |] suffix Htype.
  - destruct number; constructor.
  - destruct vector; constructor.
  - destruct Htype as [[nullable heap] Hreference]. subst reference.
    destruct nullable, heap;
      eapply valtype_abstract_reference; constructor; constructor.
  - contradiction.
Qed.

Lemma unpack_locals_decl_bounds : forall decls,
    List.Forall (fun decl => (0 < fst decl)%nat) decls ->
    List.Forall printable_local_type (unpack_locals decls) ->
    List.Forall (fun decl =>
      (fst decl <= List.length (unpack_locals decls))%nat /\
      printable_local_type (snd decl)) decls.
Proof.
  induction decls as [|[count type] decls IH]; intros Hpositive Htypes.
  - constructor.
  - inversion Hpositive as [|decl rest Hcount Hrest]; subst.
    change (List.Forall printable_local_type
      (List.app (List.repeat type count) (unpack_locals decls))) in Htypes.
    apply List.Forall_app in Htypes as [Hrepeat Htypes].
    assert (Htype : printable_local_type type).
    { destruct count; [cbn in Hcount; lia |].
      inversion Hrepeat; assumption. }
    specialize (IH Hrest Htypes).
    change (List.Forall (fun decl =>
      (fst decl <= List.length
        (List.app (List.repeat type count) (unpack_locals decls)))%nat /\
      printable_local_type (snd decl)) ((count, type) :: decls)).
    rewrite List.length_app, List.repeat_length.
    constructor.
    + split; [cbn; lia | exact Htype].
    + eapply List.Forall_impl; [|exact IH].
      intros [n t] [Hn Ht]. split; [cbn in *; lia | exact Ht].
Qed.

Lemma binary_of_local_prefix : forall count type suffix,
    (N.of_nat count <= 4294967295)%N ->
    printable_local_type type ->
    local_decl_prefix (List.app (binary_of_local (count, type)) suffix)
      (N.of_nat count, type) suffix.
Proof.
  intros count type suffix Hcount Htype.
  unfold binary_of_local, binary_of_u32_nat.
  rewrite <- List.app_assoc.
  econstructor.
  - now apply binary_of_tailidx_correct.
  - now apply printable_local_type_suffix.
Qed.

Lemma binary_local_elements_prefix : forall decls suffix,
    List.Forall (fun decl =>
      (N.of_nat (fst decl) <= 4294967295)%N /\
      printable_local_type (snd decl)) decls ->
    elements_prefix local_decl_prefix
      (List.app (List.concat (List.map binary_of_local decls)) suffix)
      (binary_local_decls decls) suffix.
Proof.
  intros decls suffix Hdecls.
  induction Hdecls as [|[count type] decls [Hcount Htype] Hdecls IH].
  - constructor.
  - cbn [List.map List.concat binary_local_decls].
    rewrite <- List.app_assoc.
    econstructor; [now apply binary_of_local_prefix | exact IH].
Qed.

Theorem bunched_local_bytes_prefix : forall types suffix,
    (N.of_nat (List.length types) <= 4294967295)%N ->
    List.Forall printable_local_type types ->
    vector_prefix local_decl_prefix
      (List.app (binary_of_vec binary_of_local (bunch_locals types)) suffix)
      (binary_local_decls (bunch_locals types)) suffix.
Proof.
  intros types suffix Hlength Htypes.
  pose proof (bunch_locals_positive types) as Hpositive.
  pose proof (unpack_locals_length_bound _ Hpositive) as Hcount.
  pose proof (unpack_locals_decl_bounds _ Hpositive) as Hdecls.
  rewrite bunch_locals_inverse in Hcount, Hdecls.
  specialize (Hdecls Htypes).
  unfold binary_of_vec, binary_of_u32_nat.
  rewrite <- List.app_assoc.
  exists (List.app
    (List.concat (List.map binary_of_local (bunch_locals types))) suffix).
  split.
  - unfold binary_local_decls. rewrite List.length_map.
    apply binary_of_tailidx_correct. lia.
  - apply binary_local_elements_prefix.
    eapply List.Forall_impl; [|exact Hdecls].
    intros [count type] [Hbound Htype].
    split; [cbn in Hbound |- *; lia | exact Htype].
Qed.

Theorem bunched_local_bytes_roundtrip : forall n types suffix
    (Hle : (List.length (List.app
      (binary_of_vec binary_of_local (bunch_locals types)) suffix) <= n)%nat),
    (N.of_nat (List.length types) <= 4294967295)%N ->
    List.Forall printable_local_type types ->
    option_map observe_reader
      (runParser (parse_vec parse_locals :
        Parser (SizedList Byte.byte) Byte.byte option (list (N * value_type)) n)
        Hle (mkSizedList (List.app
          (binary_of_vec binary_of_local (bunch_locals types)) suffix))) =
      Some (binary_local_decls (bunch_locals types), suffix).
Proof.
  intros n types suffix Hle Hlength Htypes.
  apply parse_local_vector_prefix.
  now apply bunched_local_bytes_prefix.
Qed.
