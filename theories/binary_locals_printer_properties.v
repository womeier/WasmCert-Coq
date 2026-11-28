(** The local packer's semantic inverse, independently of byte encoding. *)
From Stdlib Require Import List PeanoNat NArith Lia.
From mathcomp Require Import ssrbool eqtype.
From Wasm Require Import datatypes_properties binary_format_printer
  binary_format_parser binary_locals_properties.

Definition unpack_locals (decls : list (nat * value_type)) : list value_type :=
  List.concat (List.map (fun '(count, type) => List.repeat type count) decls).

Lemma unpack_locals_app : forall first second,
    unpack_locals (List.app first second) =
      List.app (unpack_locals first) (unpack_locals second).
Proof.
  intros first second. unfold unpack_locals.
  rewrite List.map_app, List.concat_app. reflexivity.
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
