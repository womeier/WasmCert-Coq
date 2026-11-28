From Wasm Require Import opsem properties local_initialization_properties.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Stdlib Require Import List NArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Semantics.
Context `{ho : host}.

Lemma initialized_slots_write (slots : list (option value)) n v vd :
  (n < length slots)%coq_nat ->
  initialized_slots (set_nth (Some vd) slots n (Some v)) =
    set_nth false (initialized_slots slots) n true.
Proof.
  move: n; induction slots as [|slot slots IH]; destruct n => /=; move => Hbound;
    try by lias.
  f_equal. apply IH. by lias.
Qed.

Lemma initialized_slots_write_monotone (slots : list (option value)) n v vd :
  (n < length slots)%coq_nat ->
  local_init_le (initialized_slots slots)
    (initialized_slots (set_nth (Some vd) slots n (Some v))).
Proof.
  move => Hbound.
  rewrite initialized_slots_write => //.
  have Hsize : n < length (initialized_slots slots).
  { rewrite /initialized_slots List.length_map. by lias. }
  destruct (nth_error_exists Hsize) as [b Hb].
  by eapply local_init_le_write; eauto.
Qed.

Theorem reduce_frame_initialization_monotone hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  local_init_le (initialized_slots f.(f_locs)) (initialized_slots f'.(f_locs)).
Proof.
  move => Hreduce.
  induction Hreduce; try apply local_init_le_refl; try assumption.
  rewrite H1.
  apply initialized_slots_write_monotone.
  by lias.
Qed.

Lemma local_init_le_terminal I O :
  local_init_le I O ->
  local_init_le O (List.repeat true (length I)).
Proof.
  move => H.
  apply List.Forall2_length in H.
  rewrite H. apply local_init_le_top.
Qed.

Theorem reduce_simple_initialization es es' :
  reduce_simple es es' ->
  forall I O, check_administrative_local_init_sequence es I = Some O ->
  exists O', check_administrative_local_init_sequence es' I = Some O' /\
    local_init_le O O'.
Proof.
  move => Hred; inversion Hred; subst; move => I O Hcheck;
    pose proof (administrative_local_init_sequence_grows Hcheck) as Hgrow;
    cbn [check_administrative_local_init_sequence
         check_administrative_local_init check_local_init_instruction] in Hcheck |- *;
    repeat rewrite administrative_local_init_value in Hcheck |- *;
    simpl in Hcheck |- *;
    try (injection Hcheck as <-; eexists; split; first reflexivity;
         first [apply local_init_le_refl | apply local_init_le_top]).
  all: try (exists O; split; [exact Hcheck | apply local_init_le_refl]).
  all: repeat match goal with
    | Hconst : is_true (const_list ?values) |- _ =>
      apply const_es_exists in Hconst as [vs ->]
    end.
  all: repeat rewrite administrative_local_init_app administrative_local_init_values
    in Hcheck |- *.
  all: simpl in Hcheck |- *.
  all: try (injection Hcheck as <-; eexists; split; first reflexivity;
         first [apply local_init_le_refl | apply local_init_le_top]).
  all: fold check_administrative_local_init_sequence in Hcheck |- *.
  all: fold check_local_init_sequence in Hcheck |- *.
  all: repeat rewrite administrative_local_init_values in Hcheck |- *.
  all: simpl in Hcheck |- *.
  all: try (injection Hcheck as <-; eexists; split; first reflexivity;
         first [apply local_init_le_refl | apply local_init_le_top]).
  all: try (exists (List.repeat true (length I)); split; first reflexivity;
    exact (local_init_le_terminal Hgrow)).
  all: repeat first [
    match goal with
    | |- context [check_local_init_sequence ?body ?bits] =>
      destruct (check_local_init_sequence body bits) eqn:?; simpl in Hcheck |- *
    end
    | match type of Hcheck with
      | context [check_local_init_sequence ?body ?bits] =>
        destruct (check_local_init_sequence body bits) eqn:?; simpl in Hcheck |- *
      | context [check_administrative_local_init_sequence ?body ?bits] =>
        destruct (check_administrative_local_init_sequence body bits) eqn:?;
          simpl in Hcheck |- *
      end].
  all: try discriminate.
  all: try (injection Hcheck as <-; eexists; split; first reflexivity;
         first [apply local_init_le_refl | apply local_init_le_top]).
  injection Hcheck as <-.
  apply const_es_exists in H as [values ->].
  rewrite administrative_local_init_app administrative_local_init_values /= Heqo0.
  exists l0; split; first reflexivity.
  by apply administrative_local_init_sequence_grows in Heqo0.
Qed.

Theorem reduce_initialization hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  store_typing s ->
  forall O,
    check_administrative_local_init_sequence es (initialized_slots f.(f_locs)) = Some O ->
    exists O',
      check_administrative_local_init_sequence es' (initialized_slots f'.(f_locs)) = Some O' /\
      local_init_le O O'.
Proof.
  move => Hred.
  induction Hred; move => Hstore O Hcheck;
    try by eapply reduce_simple_initialization; eauto.
  all: pose proof (administrative_local_init_sequence_grows Hcheck) as Hgrow.
  all: cbn [check_administrative_local_init_sequence
         check_administrative_local_init check_local_init_instruction] in Hcheck |- *.
  all: repeat rewrite administrative_local_init_value in Hcheck |- *.
  all: simpl in Hcheck |- *.
  all: try (injection Hcheck as <-; eexists; split; first reflexivity;
         first [apply local_init_le_refl | apply local_init_le_top]).
  all: try solve [exists (List.repeat true (length (initialized_slots (f_locs f))));
    split; first reflexivity; exact (local_init_le_terminal Hgrow)].
  all: subst.
  all: repeat match goal with
    | Hconst : _ |- _ => apply const_es_exists in Hconst as [values' ->]
    end.
  all: fold check_administrative_local_init_sequence in Hcheck |- *.
  all: fold check_local_init_sequence in Hcheck |- *.
  all: rewrite ?administrative_local_init_app ?administrative_local_init_values /=
    ?administrative_local_init_source in Hcheck |- *.
  all: cbn [check_administrative_local_init_sequence
         check_administrative_local_init check_local_init_instruction] in Hcheck |- *.
  all: fold check_administrative_local_init_sequence in Hcheck |- *.
  all: fold check_local_init_sequence in Hcheck |- *.
  all: rewrite ?administrative_local_init_values ?administrative_local_init_source
    in Hcheck |- *.
  all: try (injection Hcheck as <-; eexists; split; first reflexivity;
         first [apply local_init_le_refl | apply local_init_le_top]).
  all: try solve [exists O; split; [exact Hcheck | apply local_init_le_refl]].
  all: try solve [
    match type of Hcheck with
    | context [check_local_init_sequence ?body ?bits] =>
      destruct (check_local_init_sequence body bits); simpl in Hcheck |- *
    end; try discriminate; injection Hcheck as <-;
    eexists; split; first reflexivity; apply local_init_le_refl].
  all: try solve [
    match type of Hcheck with
    | context [lookup_N ?bits ?idx] =>
      destruct (lookup_N bits idx) as [[|]|]; simpl in Hcheck |- *
    end; try discriminate; injection Hcheck as <-;
    eexists; split; first reflexivity; apply local_init_le_refl].
  all: try solve [
    match type of Hcheck with
    | context [check_administrative_local_init_sequence ?body ?bits] =>
      destruct (check_administrative_local_init_sequence body bits); simpl in Hcheck |- *
    end; try discriminate; injection Hcheck as <-;
    eexists; split; first reflexivity; apply local_init_le_refl].
  - destruct (store_typing_func_lookup Hstore H) as [ft [<- [_ Hfunctype]]].
    simpl in Hfunctype.
    destruct (inst_typing s inst) as [C|] eqn:Hinst; last contradiction.
    unfold func_typing in Hfunctype; simpl in Hfunctype.
    destruct (lookup_function_type (tc_types C) x) as [[params results]|] eqn:Htype;
      last contradiction.
    destruct Hfunctype as [Heq [_ [Out Hinit]]].
    injection Heq as <- <-.
    have Hbody := (proj2 check_local_init_complete) _ _ _ Hinit.
    symmetry in H5.
    rewrite (@initialized_slots_call vs ts1 ts H5) Hbody.
    injection Hcheck as <-.
    eexists; split; first reflexivity. apply local_init_le_refl.
  - injection Hcheck as <-.
    destruct r as [returned|].
    + rewrite /result_to_stack administrative_local_init_values.
      eexists; split; first reflexivity. apply local_init_le_refl.
    + eexists; split; first reflexivity. apply local_init_le_top.
  - rewrite H1 initialized_slots_write; last by lias.
    destruct (lookup_N (initialized_slots (f_locs f)) i) eqn:E;
      simpl in Hcheck; try discriminate.
    injection Hcheck as <-.
    eexists; split; first reflexivity. apply local_init_le_refl.
  - eapply administrative_local_init_lfill_replace; last exact Hcheck.
    + by eapply reduce_frame_initialization_monotone; eauto.
    + move => M HM. by eapply IHHred; eauto.
  - destruct (check_administrative_local_init_sequence es
      (initialized_slots (f_locs f))) as [M|] eqn:Hbody;
      simpl in Hcheck; try discriminate.
    destruct (IHHred Hstore M (Logic.eq_refl _)) as [P [HP HMP]].
    rewrite HP.
    injection Hcheck as <-.
    eexists; split; first reflexivity. apply local_init_le_refl.
Qed.

End Semantics.
