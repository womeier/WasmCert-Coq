(** Address-aware table primitives using the existing reference-value and
    list representations.  Bounds are checked in [N] BEFORE converting a
    successful index to [nat].  In particular, a high i64 address into a
    small table is rejected without traversing that many list elements.

    [valid] below is the limits invariant only.  Reference/store typing is
    deliberately not claimed by this development: that must be connected to
    the core store typing relation during the table-type migration. *)
From Wasm Require Import datatypes addressing.
From Stdlib Require Import ZArith NArith List Lia Bool.
Import ListNotations Addressing.

Module AddressingTable.

Record instance : Type := {
  declared_type : Addressing.table_type;
  elements : list value_ref;
}.

Definition size (t: instance) : N :=
  N.of_nat (List.length t.(elements)).

Definition valid (t: instance) : Prop :=
  table_type_valid t.(declared_type) = true /\
  size_in_limits t.(declared_type).(table_limits)
    (table_limit_bound t.(declared_type).(table_address_type)) (size t).

Definition allocate (tt: Addressing.table_type) : option instance :=
  if table_type_valid tt then
    Some {| declared_type := tt;
            elements := List.repeat (VAL_ref_null tt.(table_element_type))
              (N.to_nat tt.(table_limits).(lim_min)) |}
  else None.

Lemma allocate_valid tt t :
  allocate tt = Some t -> valid t.
Proof.
  unfold allocate.
  destruct (table_type_valid tt) eqn:Htype; [|discriminate].
  intros Hresult. inversion Hresult; subst; clear Hresult.
  unfold valid, size; cbn [declared_type elements].
  rewrite List.repeat_length, N2Nat.id.
  split; [assumption |].
  apply limit_valid_range_spec in Htype.
  unfold limits_valid in Htype.
  unfold size_in_limits.
  destruct (lim_max (table_limits tt)); simpl in *; intuition lia.
Qed.

Definition get (t: instance) (index: value_num) : option value_ref :=
  match address_of_value t.(declared_type).(table_address_type) index with
  | None => None
  | Some i =>
      if N.ltb i (size t) then List.nth_error t.(elements) (N.to_nat i)
      else None
  end.

Lemma get_spec t index v :
  get t index = Some v <->
  exists i,
    address_of_value t.(declared_type).(table_address_type) index = Some i /\
    (i < size t)%N /\
    List.nth_error t.(elements) (N.to_nat i) = Some v.
Proof.
  unfold get.
  destruct (address_of_value _ _) as [i|] eqn:Hindex.
  - destruct (N.ltb i (size t)) eqn:Hbound.
    + apply N.ltb_lt in Hbound.
      split; [intros H; exists i; auto |].
      intros [j [Hj [_ Hlookup]]]. inversion Hj; subst. assumption.
    + apply N.ltb_ge in Hbound.
      split; [discriminate |].
      intros [j [Hj [Hlt _]]]. inversion Hj; subst. lia.
  - split; [discriminate |].
    intros [i [Hi _]]. discriminate.
Qed.

Lemma get_in_bounds t index i :
  address_of_value t.(declared_type).(table_address_type) index = Some i ->
  (i < size t)%N ->
  exists v, get t index = Some v.
Proof.
  intros Hindex Hbound.
  unfold get. rewrite Hindex.
  assert (N.ltb i (size t) = true) as -> by now apply N.ltb_lt.
  destruct (List.nth_error t.(elements) (N.to_nat i)) eqn:Hlookup; [eauto |].
  apply List.nth_error_None in Hlookup.
  unfold size in Hbound. lia.
Qed.

(** This list update keeps length unchanged and never uses a filler value. *)
Fixpoint replace (vs: list value_ref) (i: nat) (v: value_ref)
    : list value_ref :=
  match vs, i with
  | [], _ => []
  | _ :: vs', O => v :: vs'
  | h :: vs', S i' => h :: replace vs' i' v
  end.

Lemma replace_length vs i v :
  List.length (replace vs i v) = List.length vs.
Proof. revert i. induction vs; intros [|i]; simpl; auto. Qed.

Lemma replace_same vs i v :
  (i < List.length vs)%nat -> List.nth_error (replace vs i v) i = Some v.
Proof.
  revert i. induction vs; intros [|i] Hbound; simpl in *; try lia; auto.
  apply IHvs. lia.
Qed.

Lemma replace_other vs i j v :
  i <> j ->
  List.nth_error (replace vs i v) j = List.nth_error vs j.
Proof.
  revert i j. induction vs; intros [|i] [|j] Hne; simpl; auto; try congruence.
Qed.

Definition set (t: instance) (index: value_num) (v: value_ref) : option instance :=
  match address_of_value t.(declared_type).(table_address_type) index with
  | None => None
  | Some i =>
      if N.ltb i (size t)
      then Some {| declared_type := t.(declared_type);
                   elements := replace t.(elements) (N.to_nat i) v |}
      else None
  end.

Lemma set_characterization t index v t' :
  set t index v = Some t' ->
  exists i,
    address_of_value t.(declared_type).(table_address_type) index = Some i /\
    (i < size t)%N /\
    t'.(declared_type) = t.(declared_type) /\
    t'.(elements) = replace t.(elements) (N.to_nat i) v.
Proof.
  unfold set.
  destruct (address_of_value _ _) as [i|] eqn:Hindex; [|discriminate].
  destruct (N.ltb i (size t)) eqn:Hbound; [|discriminate].
  apply N.ltb_lt in Hbound.
  intros Hresult. inversion Hresult; subst.
  exists i. auto.
Qed.

Lemma set_valid t index v t' :
  valid t -> set t index v = Some t' -> valid t'.
Proof.
  intros Hvalid Hset.
  apply set_characterization in Hset as [i [_ [_ [Htype Hdata]]]].
  unfold valid, size in *. rewrite Htype, Hdata, replace_length.
  assumption.
Qed.

Lemma get_after_set t index v t' :
  set t index v = Some t' -> get t' index = Some v.
Proof.
  intros Hset.
  apply set_characterization in Hset as [i [Hindex [Hbound [Htype Hdata]]]].
  apply get_spec. exists i. rewrite Htype.
  split; [assumption |].
  unfold size in *. rewrite Hdata, replace_length.
  split; [assumption |]. apply replace_same. lia.
Qed.

Definition grow (t: instance) (delta: value_num) (init: value_ref)
    : option (instance * value_num) :=
  let tt := t.(declared_type) in
  match address_of_value tt.(table_address_type) delta with
  | None => None
  | Some count =>
      match grow_size tt.(table_limits)
        (table_limit_bound tt.(table_address_type)) (size t) count with
      | None => None
      | Some _ =>
          Some ({| declared_type := tt;
                    elements := t.(elements) ++
                      List.repeat init (N.to_nat count) |},
                value_of_address tt.(table_address_type) (size t))
      end
  end.

Lemma grow_characterization t delta init t' result :
  grow t delta init = Some (t', result) ->
  exists count new_size,
    address_of_value t.(declared_type).(table_address_type) delta = Some count /\
    grow_size t.(declared_type).(table_limits)
      (table_limit_bound t.(declared_type).(table_address_type))
      (size t) count = Some new_size /\
    t'.(declared_type) = t.(declared_type) /\
    t'.(elements) = t.(elements) ++ List.repeat init (N.to_nat count) /\
    result = value_of_address t.(declared_type).(table_address_type) (size t).
Proof.
  unfold grow.
  destruct (address_of_value _ _) as [count|] eqn:Hcount; [|discriminate].
  destruct (grow_size _ _ _ _) as [new_size|] eqn:Hsize; [|discriminate].
  intros Hresult. inversion Hresult; subst.
  exists count, new_size. auto.
Qed.

Lemma grow_valid t delta init t' result :
  valid t ->
  grow t delta init = Some (t', result) ->
  valid t' /\
  (size t <= size t')%N /\
  address_of_value t.(declared_type).(table_address_type) result = Some (size t).
Proof.
  intros [Htype Hvalid] Hgrow.
  apply grow_characterization in Hgrow as
    [count [new_size [Hcount [Hsize [Htype' [Hdata Hresult]]]]]].
  apply grow_size_spec in Hsize as [_ [Hnew Hnewvalid]].
  assert (size t' = new_size) as Hsize'.
  { unfold size. rewrite Hdata, List.length_app, List.repeat_length.
    rewrite Nat2N.inj_add, N2Nat.id, Hnew. reflexivity. }
  split.
  - unfold valid. rewrite Htype', Hsize'. auto.
  - split; [rewrite Hsize', Hnew; lia |].
    rewrite Hresult. apply address_value_round_trip.
    apply table_size_fits_address.
    unfold size_in_limits in Hvalid. tauto.
Qed.

Lemma grow_preserves_elements t delta init t' result i :
  grow t delta init = Some (t', result) ->
  (i < size t)%N ->
  List.nth_error t'.(elements) (N.to_nat i) =
    List.nth_error t.(elements) (N.to_nat i).
Proof.
  intros Hgrow Hbound.
  apply grow_characterization in Hgrow as
    [count [new_size [_ [_ [_ [Hdata _]]]]]].
  rewrite Hdata. apply List.nth_error_app1.
  unfold size in Hbound. lia.
Qed.

End AddressingTable.
