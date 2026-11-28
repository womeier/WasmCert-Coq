From Wasm Require Import type_preservation local_initialization_properties.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Stdlib Require Import NArith List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Runtime.
Context `{ho : host}.

Lemma initialized_locals_lengths s slots ts I :
  initialized_locals_typing s slots ts I ->
  length slots = length ts /\ length I = length ts.
Proof. move => H; induction H; simpl; intuition congruence. Qed.

Lemma initialized_locals_available s slots ts I :
  initialized_locals_typing s slots ts I ->
  local_init_le I (initialized_slots slots).
Proof.
  move => H; induction H => /=; constructor => //.
Qed.

Lemma initialized_locals_weaken s slots ts I J :
  initialized_locals_typing s slots ts J ->
  local_init_le I J ->
  initialized_locals_typing s slots ts I.
Proof.
  move => Hlocals; move: I.
  induction Hlocals; move => bits Hle; inversion Hle; subst.
  - constructor.
  - constructor => //. by apply IHHlocals.
  - destruct x.
    + match goal with Hbad : true = true -> false = true |- _ =>
        specialize (Hbad (Logic.eq_refl true)); discriminate
      end.
    + constructor => //. by apply IHHlocals.
Qed.

Lemma initialized_locals_from_values s slots ts :
  local_values_typing s slots ts ->
  initialized_locals_typing s slots ts (List.repeat true (length ts)).
Proof.
  move: ts; induction slots as [|[v|] slots IH]; destruct ts => //=.
  - move => _. constructor.
  - move/andP => [Hv Hrest]. constructor => //. by apply IH.
Qed.

Lemma initialized_local_get s slots ts I x t :
  initialized_locals_typing s slots ts I ->
  lookup_N I x = Some true ->
  lookup_N ts x = Some t ->
  exists v, lookup_N slots x = Some (Some v) /\ value_typing s v t.
Proof.
  unfold lookup_N.
  move => Hlocals.
  generalize (N.to_nat x); move => n.
  move: n t; induction Hlocals; move => n target Hinit Htype.
  - by destruct n.
  - destruct n; simpl in Hinit, Htype |- *.
    + injection Htype as <-. by exists v.
    + by eapply IHHlocals.
  - destruct n; simpl in Hinit, Htype |- *; first discriminate.
    by eapply IHHlocals.
Qed.

Lemma initialized_local_set_nat s slots ts I n t v :
  initialized_locals_typing s slots ts I ->
  List.nth_error ts n = Some t ->
  value_typing s v t ->
  initialized_locals_typing s
    (set_nth (Some v) slots n (Some v)) ts (set_nth false I n true).
Proof.
  move => Hlocals.
  move: n t; induction Hlocals; move => n target Htype Hv.
  - by destruct n.
  - destruct n; simpl in Htype |- *.
    + injection Htype as <-. by constructor.
    + constructor => //. by eapply IHHlocals; eauto.
  - destruct n; simpl in Htype |- *.
    + injection Htype as <-. by constructor.
    + constructor => //. by eapply IHHlocals; eauto.
Qed.

Lemma initialized_locals_cat s xs ys ts us I J :
  initialized_locals_typing s xs ts I ->
  initialized_locals_typing s ys us J ->
  initialized_locals_typing s (xs ++ ys) (ts ++ us) (I ++ J).
Proof.
  move => Hxs Hys. induction Hxs => /=; first exact Hys.
  - by constructor.
  - by constructor.
Qed.

Lemma initialized_parameter_slots s vs ts :
  values_typing s vs ts ->
  initialized_locals_typing s (map Some vs) ts (List.repeat true (length ts)).
Proof.
  move: ts; induction vs; destruct ts => //=.
  - move => _. constructor.
  - move/andP => [Hv Hvs]. constructor => //. by apply IHvs.
Qed.

Lemma initialized_default_slots s ts :
  initialized_locals_typing s (map default_val ts) ts
    (map (fun t => default_val t != None) ts).
Proof.
  induction ts as [|t ts IH] => /=; first constructor.
  destruct (default_val t) eqn:E => /=.
  - constructor => //. by eapply default_value_typing; eauto.
  - constructor => //.
Qed.

(* This is the exact allocation used by r_invoke_native and the executable
   context interpreter. No defaultability hypothesis or null sentinel is used. *)
Theorem initialized_call_slots s args params locals :
  values_typing s args params ->
  initialized_locals_typing s
    (map Some args ++ map default_val locals)
    (params ++ locals) (initial_local_state params locals).
Proof.
  move => Hargs. apply initialized_locals_cat.
  - by apply initialized_parameter_slots.
  - apply initialized_default_slots.
Qed.

Lemma initialized_locals_extension s s' slots ts I :
  store_extension s s' ->
  initialized_locals_typing s slots ts I ->
  initialized_locals_typing s' slots ts I.
Proof.
  move => Hext Hlocals; induction Hlocals; constructor => //.
  by eapply value_typing_extension; eauto.
Qed.

Lemma initialized_local_read_step s f C I O x t hs :
  frame_typing_init s f C I ->
  local_init_instruction I (BI_local_get x) O ->
  lookup_N C.(tc_locals) x = Some t ->
  exists v, value_typing s v t /\
    reduce hs s f [::AI_basic (BI_local_get x)] hs s f [::v_to_e v].
Proof.
  unfold frame_typing_init.
  destruct (inst_typing s (f_inst f)) as [C0|] eqn:Hinst; last contradiction.
  move => [ts [-> Hlocals]] Hinit Htype.
  simpl in Htype.
  erewrite inst_t_context_local_empty in Htype; eauto.
  rewrite cats0 in Htype.
  inversion Hinit; subst; simpl in *; try discriminate.
  match goal with Hread : lookup_N ?bits x = Some true |- _ =>
    destruct (initialized_local_get Hlocals Hread Htype) as [v [Hv Htyped]]
  end.
  exists v; split; first exact Htyped.
  by apply r_local_get.
Qed.

Lemma initialized_local_write_step s f C I O x t v hs :
  frame_typing_init s f C I ->
  local_init_instruction I (BI_local_set x) O ->
  lookup_N C.(tc_locals) x = Some t ->
  value_typing s v t ->
  exists f',
    reduce hs s f [::v_to_e v; AI_basic (BI_local_set x)] hs s f' nil /\
    frame_typing_init s f' C O.
Proof.
  unfold frame_typing_init.
  destruct (inst_typing s (f_inst f)) as [C0|] eqn:Hinst; last contradiction.
  move => [ts [-> Hlocals]] Hinit Htype Hvalue.
  simpl in Htype.
  erewrite inst_t_context_local_empty in Htype; eauto.
  rewrite cats0 in Htype.
  inversion Hinit; subst; simpl in *; try discriminate.
  exists (Build_frame
    (set_nth (Some v) (f_locs f) (N.to_nat x) (Some v)) (f_inst f)).
  split.
  - apply r_local_set with (vd := v) => //=.
    destruct (initialized_locals_lengths Hlocals) as [Hlength _].
    rewrite Hlength.
    apply nth_error_Some_length in Htype.
    by lias.
  - simpl. rewrite Hinst.
    exists ts; split; first reflexivity.
    by eapply initialized_local_set_nat; eauto.
Qed.

End Runtime.
