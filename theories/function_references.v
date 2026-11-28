(* Typed function reference foundations.
   This module is an extension layer, not yet wired into basic_instruction.
   In particular it does not claim support in the extracted interpreter. *)
From Wasm Require Import typing subtyping_properties.
From Stdlib Require Import List Bool NArith.
Import ListNotations.

Set Implicit Arguments.

Module FunctionReferences.

(* Use the core representation, including its module-local index space.
   No parallel heap/reference representation is maintained here. *)
Definition ref_type := reference_type.
Notation Ref := Ref_type.
Notation Indexed := HT_type.
Definition nullable := ref_nullable.
Definition heap := ref_heap.
Definition lift_reference (t : reference_type) := t.
Definition non_null t := Ref false (heap t).

Inductive heap_subtype : heap_type -> heap_type -> Prop :=
| hs_refl : forall h, heap_subtype h h
| hs_func : forall i, heap_subtype (Indexed i) HT_func.

Definition heap_subtypeb h1 h2 :=
  if heap_type_eq_dec h1 h2 then true
  else match h1, h2 with
       | Indexed _, HT_func => true
       | _, _ => false
       end.

Lemma heap_subtypeb_spec h1 h2 :
  heap_subtypeb h1 h2 = true <-> heap_subtype h1 h2.
Proof.
  unfold heap_subtypeb.
  destruct (heap_type_eq_dec h1 h2) as [E | E].
  - subst h2. split; [intros _; constructor | reflexivity].
  - split.
    + destruct h1, h2; simpl; intros H; try discriminate; constructor.
    + intros H. inversion H; subst; [contradiction | reflexivity].
Qed.

Lemma heap_subtype_trans h1 h2 h3 :
  heap_subtype h1 h2 -> heap_subtype h2 h3 -> heap_subtype h1 h3.
Proof.
  intros H12 H23. destruct H12; auto.
  inversion H23; subst. constructor.
Qed.

Definition ref_subtype t1 t2 :=
  heap_subtype (heap t1) (heap t2) /\
  (nullable t1 = false \/ nullable t2 = true).

Definition ref_subtypeb t1 t2 :=
  andb (heap_subtypeb (heap t1) (heap t2))
       (orb (negb (nullable t1)) (nullable t2)).

Lemma ref_subtypeb_spec t1 t2 :
  ref_subtypeb t1 t2 = true <-> ref_subtype t1 t2.
Proof.
  unfold ref_subtypeb, ref_subtype.
  rewrite Bool.andb_true_iff, heap_subtypeb_spec.
  destruct (nullable t1), (nullable t2); simpl; intuition discriminate.
Qed.

Lemma ref_subtype_refl t : ref_subtype t t.
Proof.
  split; [constructor | destruct (nullable t); auto].
Qed.

Lemma ref_subtype_trans t1 t2 t3 :
  ref_subtype t1 t2 -> ref_subtype t2 t3 -> ref_subtype t1 t3.
Proof.
  intros [H12 N12] [H23 N23]. split.
  - eapply heap_subtype_trans; eauto.
  - destruct N12, N23; auto; congruence.
Qed.

Lemma non_null_subtype t : ref_subtype (non_null t) t.
Proof. split; [constructor | left; reflexivity]. Qed.

Definition heap_valid (types : list function_type) h :=
  match h with
  | Indexed i => exists ft, lookup_N types i = Some ft
  | _ => True
  end.

Definition erase_heap h :=
  match h with
  | Indexed _ => HT_func
  | _ => h
  end.

(* This signature checker handles the reference operand separately from the
   existing parameter/result types.  It reuses the existing result subtyping
   for tail calls.  Full validation still needs an extended operand stack. *)
Definition check_call_ref (types : list function_type)
    (return_type : option result_type) (tail : bool) (i : typeidx)
    : option function_type :=
  match lookup_N types i with
  | Some (Tf args results) =>
      if tail then
        match return_type with
        | Some expected =>
            if values_subtyping results expected
            then Some (Tf args results) else None
        | None => None
        end
      else Some (Tf args results)
  | None => None
  end.

Definition call_ref_valid types return_type tail i ft :=
  lookup_N types i = Some ft /\
  (tail = true ->
    exists expected, return_type = Some expected /\
      values_subtyping (match ft with Tf _ results => results end) expected = true).

Lemma check_call_ref_spec types return_type tail i ft :
  check_call_ref types return_type tail i = Some ft <->
  call_ref_valid types return_type tail i ft.
Proof.
  unfold check_call_ref, call_ref_valid.
  destruct (lookup_N types i) as [[args results] |] eqn:Hi.
  - destruct tail.
    + destruct return_type as [expected |].
      * destruct (values_subtyping results expected) eqn:Hs.
        -- split.
           ++ intro H. inversion H; subst. split; auto.
              intros _. exists expected. auto.
           ++ intros [H _]. inversion H. reflexivity.
        -- split; [discriminate |].
           intros [H Hr]. inversion H; subst.
           destruct (Hr eq_refl) as [expected' [He Hsub]].
           inversion He; subst. congruence.
      * split; [discriminate |].
        intros [_ Hr]. destruct (Hr eq_refl) as [? [He _]]. discriminate.
    + split.
      * intro H. split; auto. discriminate.
      * intros [H _]. exact H.
  - split; [discriminate | intros [H _]; discriminate].
Qed.

(* Runtime references are the existing value_ref, not a parallel store.
   A null at an indexed heap type erases to the existing function null. *)
Section Runtime.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Definition ref_has_type (s : store_record) (types : list function_type)
    (v : value_ref) (t : ref_type) : Prop :=
  heap_valid types (heap t) /\
  match v with
  | VAL_ref_null h => nullable t = true /\ h = erase_heap (heap t)
  | VAL_ref_func a =>
      exists ft, ext_func_typing s a = Some ft /\
        match heap t with
        | HT_func => True
        | Indexed i => lookup_N types i = Some ft
        | _ => False
        end
  | VAL_ref_extern _ => heap t = HT_extern
  | VAL_ref_exn _ => False
  | VAL_ref_i31 _ => False
  end.

(* The refinement layer is conservative over the existing runtime typing.
   Erasure forgets nullability and indexed function identity, but cannot turn
   an ill-typed or dangling runtime reference into a well-typed old value. *)
Lemma ref_has_type_erases s types v t :
  ref_has_type s types v t ->
  value_typing s (VAL_ref v) (T_ref (Ref_type true (erase_heap (heap t)))) = true.
Proof.
  intros [_ Hv]. destruct v as [h | a | a | a | n].
  - destruct Hv as [_ He]. subst h.
    unfold value_typing, typeof_value, typeof_ref. simpl.
    apply value_subtyping_eq.
  - destruct Hv as [ft [Ha Hheap]].
    unfold value_typing, typeof_value, typeof_ref. rewrite Ha.
    destruct (heap t); simpl in *; try contradiction; apply value_subtyping_eq.
  - unfold value_typing, typeof_value, typeof_ref.
    rewrite Hv. simpl. apply value_subtyping_eq.
  - contradiction.
  - contradiction.
Qed.

Lemma ref_has_type_weaken s types v t1 t2 :
  ref_has_type s types v t1 ->
  ref_subtype t1 t2 ->
  ref_has_type s types v t2.
Proof.
  destruct t1 as [n1 h1], t2 as [n2 h2].
  intros [Hv Hval] [Hheap Hnull]. simpl in *.
  destruct Hheap.
  - split; auto. destruct v; simpl in *; auto.
    destruct Hval as [Hn He]. split; auto.
    destruct Hnull; congruence.
  - split; [exact I |].
    destruct v; simpl in *.
    + destruct Hval as [Hn He]. split; auto.
      destruct Hnull; congruence.
    + destruct Hval as [ft [Ha Hft]]. exists ft. auto.
    + discriminate.
    + contradiction.
    + contradiction.
Qed.

Lemma non_null_not_null s types v t :
  ref_has_type s types v (non_null t) ->
  forall h, v <> VAL_ref_null h.
Proof.
  intros [_ Hv] h E. subst v. simpl in Hv. destruct Hv. discriminate.
Qed.

Lemma ref_has_type_non_null s types v t :
  ref_has_type s types v t ->
  (forall h, v <> VAL_ref_null h) ->
  ref_has_type s types v (non_null t).
Proof.
  intros [Hv Hval] Hnot. split; [exact Hv |].
  destruct v; simpl in *; auto.
  exfalso. eapply Hnot. reflexivity.
Qed.

Lemma ref_func_indexed s types a i ft :
  lookup_N types i = Some ft ->
  ext_func_typing s a = Some ft ->
  ref_has_type s types (VAL_ref_func a) (Ref false (Indexed i)).
Proof.
  intros Hi Ha. split; simpl; [exists ft; exact Hi |].
  exists ft. auto.
Qed.

(* call_ref performs no dynamic signature comparison: typing has established
   it.  return_call_ref selects the existing return-invoke administrative form.
   Extern references are not reducible (and must be rejected by validation). *)
Definition call_ref_step (tail : bool) (v : value_ref)
    : option administrative_instruction :=
  match v with
  | VAL_ref_null _ => Some AI_trap
  | VAL_ref_func a =>
      Some (if tail then AI_return_invoke a else AI_invoke a)
  | VAL_ref_extern _ => None
  | VAL_ref_exn _ => None
  | VAL_ref_i31 _ => None
  end.

Inductive call_ref_reduces (tail : bool) :
    value_ref -> administrative_instruction -> Prop :=
| cr_null : forall h, call_ref_reduces tail (VAL_ref_null h) AI_trap
| cr_func : forall a, call_ref_reduces tail (VAL_ref_func a)
    (if tail then AI_return_invoke a else AI_invoke a).

Lemma call_ref_step_spec tail v e :
  call_ref_step tail v = Some e <-> call_ref_reduces tail v e.
Proof.
  split.
  - destruct v; simpl; intro H; inversion H; constructor.
  - intro H. destruct H; reflexivity.
Qed.

Lemma call_ref_progress s types v n i ft tail :
  lookup_N types i = Some ft ->
  ref_has_type s types v (Ref n (Indexed i)) ->
  exists e, call_ref_step tail v = Some e /\
    (e = AI_trap \/
     exists a, ext_func_typing s a = Some ft /\
       e = if tail then AI_return_invoke a else AI_invoke a).
Proof.
  intros Hi [_ Hv]. destruct v as [h | a | a | a | n31]; simpl in Hv.
  - exists AI_trap. split; [reflexivity | auto].
  - destruct Hv as [ft' [Ha Hi']].
    assert (ft' = ft) by congruence. subst ft'.
    exists (if tail then AI_return_invoke a else AI_invoke a).
    split; [reflexivity | right; exists a; auto].
  - discriminate.
  - contradiction.
  - contradiction.
Qed.

Lemma call_ref_non_null_progress s types v i ft tail :
  lookup_N types i = Some ft ->
  ref_has_type s types v (Ref false (Indexed i)) ->
  exists a, ext_func_typing s a = Some ft /\
    call_ref_step tail v =
      Some (if tail then AI_return_invoke a else AI_invoke a).
Proof.
  intros Hi [_ Hv]. destruct v as [h | a | a | a | n31]; simpl in Hv.
  - destruct Hv as [Hn _]. discriminate.
  - destruct Hv as [ft' [Ha Hi']].
    assert (ft' = ft) by congruence. subst ft'.
    exists a. split; auto.
  - discriminate.
  - contradiction.
  - contradiction.
Qed.

Definition as_non_null_step (v : value_ref) : option value_ref :=
  match v with
  | VAL_ref_null _ => None
  | _ => Some v
  end.

Lemma as_non_null_step_preserves s types v t v' :
  ref_has_type s types v t ->
  as_non_null_step v = Some v' ->
  ref_has_type s types v' (non_null t).
Proof.
  intros Hv He. destruct v; simpl in He; inversion He; subst.
  - apply ref_has_type_non_null; auto. intros h H. discriminate.
  - apply ref_has_type_non_null; auto. intros h H. discriminate.
  - apply ref_has_type_non_null; auto. intros h H. discriminate.
  - apply ref_has_type_non_null; auto. intros h H. discriminate.
Qed.

Lemma as_non_null_step_traps v :
  as_non_null_step v = None <-> exists h, v = VAL_ref_null h.
Proof.
  destruct v; simpl.
  - split.
    + intros _. eexists. reflexivity.
    + intros _. reflexivity.
  - split; [discriminate | intros [h H]; discriminate].
  - split; [discriminate | intros [h H]; discriminate].
  - split; [discriminate | intros [h H]; discriminate].
  - split; [discriminate | intros [h H]; discriminate].
Qed.

End Runtime.

Definition default_reference t : option value_ref :=
  if nullable t then Some (VAL_ref_null (erase_heap (heap t))) else None.

Lemma default_reference_exists t :
  (exists v, default_reference t = Some v) <-> nullable t = true.
Proof.
  unfold default_reference. destruct (nullable t); split; auto.
  - intros _. eexists. reflexivity.
  - intros [v H]. discriminate.
  - discriminate.
Qed.

(* Null branch control transfer retains the original value on the non-null
   path of br_on_null and on the taken path of br_on_non_null. *)
Inductive null_branch_result :=
| Branch : option value_ref -> null_branch_result
| Continue : option value_ref -> null_branch_result.

Definition branch_on_null (v : value_ref) :=
  match v with
  | VAL_ref_null _ => Branch None
  | _ => Continue (Some v)
  end.

Definition branch_on_non_null (v : value_ref) :=
  match v with
  | VAL_ref_null _ => Continue None
  | _ => Branch (Some v)
  end.

Lemma branch_on_null_refines v v' :
  branch_on_null v = Continue (Some v') ->
  v' = v /\ forall h, v' <> VAL_ref_null h.
Proof.
  destruct v; simpl; intro H; inversion H; subst; split; auto;
    intros h E; discriminate.
Qed.

Lemma branch_on_non_null_refines v v' :
  branch_on_non_null v = Branch (Some v') ->
  v' = v /\ forall h, v' <> VAL_ref_null h.
Proof.
  destruct v; simpl; intro H; inversion H; subst; split; auto;
    intros h E; discriminate.
Qed.

(* Local initialization is independent of heap representation.  Keeping this
   generic lets the GC integration use the same analysis for non-defaultable
   struct/array references.  A scoped block must restore its entry flags:
   assignments inside it are not exported to the enclosing validation context. *)
Section LocalInitialization.
Context {T : Type}.

Definition local_context := list (T * bool).

Definition initial_locals (defaultable : T -> bool)
    (parameters locals : list T) : local_context :=
  map (fun t => (t, true)) parameters ++
  map (fun t => (t, defaultable t)) locals.

Lemma initial_locals_types defaultable parameters locals :
  map fst (initial_locals defaultable parameters locals) = parameters ++ locals.
Proof.
  unfold initial_locals. rewrite map_app, !map_map.
  change (map (fun t : T => t) parameters ++ map (fun t : T => t) locals =
    parameters ++ locals).
  rewrite !map_id. reflexivity.
Qed.

Definition read_local (ls : local_context) (i : nat) : option T :=
  match nth_error ls i with
  | Some (t, true) => Some t
  | _ => None
  end.

Fixpoint initialize_local (ls : local_context) (i : nat)
    : option local_context :=
  match ls, i with
  | [], _ => None
  | (t, _) :: ls', O => Some ((t, true) :: ls')
  | l :: ls', S i' =>
      option_map (cons l) (initialize_local ls' i')
  end.

Lemma initialize_local_types ls i ls' :
  initialize_local ls i = Some ls' -> map fst ls' = map fst ls.
Proof.
  revert i ls'. induction ls as [| [t b] ls IH];
    intros [|i] ls' H; simpl in H; try discriminate.
  - inversion H. reflexivity.
  - destruct (initialize_local ls i) as [rest |] eqn:E;
      simpl in H; inversion H; subst.
    simpl. f_equal. eapply IH; eauto.
Qed.

Lemma initialize_local_read ls i t :
  option_map fst (nth_error ls i) = Some t ->
  exists ls', initialize_local ls i = Some ls' /\
    read_local ls' i = Some t.
Proof.
  revert i. induction ls as [| [u b] ls IH]; intros [|i] H;
    simpl in H; try discriminate.
  - inversion H; subst. exists ((t, true) :: ls).
    split; reflexivity.
  - destruct (IH i H) as [rest [E Hr]].
    exists ((u, b) :: rest). simpl. rewrite E.
    split; [reflexivity | exact Hr].
Qed.

Lemma read_local_initialized ls i t :
  read_local ls i = Some t -> nth_error ls i = Some (t, true).
Proof.
  unfold read_local.
  destruct (nth_error ls i) as [[u b] |]; try discriminate.
  destruct b; intro H; inversion H. reflexivity.
Qed.

(* A set cannot forget initialization of another local. *)
Lemma initialize_local_preserves_read ls i ls' j t :
  initialize_local ls i = Some ls' ->
  read_local ls j = Some t ->
  read_local ls' j = Some t.
Proof.
  revert i ls' j. induction ls as [| [u b] ls IH];
    intros [|i] ls' j H Hr; simpl in H; try discriminate.
  - inversion H; subst. destruct j as [|j].
    + unfold read_local in *. simpl in *.
      destruct b; simpl in Hr; inversion Hr; reflexivity.
    + exact Hr.
  - destruct (initialize_local ls i) as [rest |] eqn:E;
      simpl in H; inversion H; subst.
    destruct j as [|j].
    + exact Hr.
    + change (read_local rest j = Some t).
      eapply IH; [exact E | exact Hr].
Qed.

End LocalInitialization.

(* An explicit table initializer must typecheck even when the minimum is zero.
   The allocation property itself is parametric in runtime reference typing. *)
Definition initialized_table (minimum : nat) (v : value_ref) :=
  repeat v minimum.

Lemma initialized_table_size n v : length (initialized_table n v) = n.
Proof. apply repeat_length. Qed.

Lemma initialized_table_typed (P : value_ref -> Prop) n v :
  P v -> Forall P (initialized_table n v).
Proof.
  intro H. induction n; simpl; constructor; auto.
Qed.

End FunctionReferences.
