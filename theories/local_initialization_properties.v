From Wasm Require Import local_initialization datatypes_properties operations.
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Stdlib Require Import List NArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma check_local_init_sequence_sound_from es :
  TProp.Forall (fun e => forall I J,
    check_local_init_instruction e I = Some J ->
    local_init_instruction I e J) es ->
  forall I J, check_local_init_sequence es I = Some J ->
    local_init_sequence I es J.
Proof.
  induction es as [|e es IH]; move => H I J Hcheck.
  - by injection Hcheck as <-; constructor.
  - inversion H; subst.
    simpl in Hcheck.
    destruct (check_local_init_instruction e I) as [K|] eqn:He; try discriminate.
    econstructor; [by eauto | by eapply IH; eauto].
Qed.

Lemma check_local_init_instruction_sound e I J :
  check_local_init_instruction e I = Some J ->
  local_init_instruction I e J.
Proof.
  move: I J.
  induction e using basic_instruction_ind'; intros I J Hcheck;
    try (injection Hcheck as <-; apply li_plain; reflexivity).
  - simpl in Hcheck.
    destruct (lookup_N I a) as [[|]|] eqn:E; try discriminate.
    injection Hcheck as <-. by apply li_get.
  - simpl in Hcheck. destruct (lookup_N I a) eqn:E; try discriminate.
    injection Hcheck as <-. by eapply li_set; eauto.
  - simpl in Hcheck. destruct (lookup_N I a) eqn:E; try discriminate.
    injection Hcheck as <-. by eapply li_tee; eauto.
  - change (match check_local_init_sequence a0 I with
            | Some _ => Some I | None => None end = Some J) in Hcheck.
    destruct (check_local_init_sequence a0 I) eqn:E; try discriminate.
    injection Hcheck as <-. eapply li_block.
    by eapply check_local_init_sequence_sound_from; eauto.
  - change (match check_local_init_sequence a0 I with
            | Some _ => Some I | None => None end = Some J) in Hcheck.
    destruct (check_local_init_sequence a0 I) eqn:E; try discriminate.
    injection Hcheck as <-. eapply li_loop.
    by eapply check_local_init_sequence_sound_from; eauto.
  - change (match check_local_init_sequence a0 I, check_local_init_sequence a1 I with
            | Some _, Some _ => Some I | _, _ => None end = Some J) in Hcheck.
    destruct (check_local_init_sequence a0 I) eqn:E1;
      destruct (check_local_init_sequence a1 I) eqn:E2; try discriminate.
    injection Hcheck as <-. eapply li_if;
      by eapply check_local_init_sequence_sound_from; eauto.
Qed.

Theorem check_local_init_sequence_sound es I J :
  check_local_init_sequence es I = Some J ->
  local_init_sequence I es J.
Proof.
  apply check_local_init_sequence_sound_from.
  induction es; constructor => //.
  exact (@check_local_init_instruction_sound a).
Qed.

Scheme local_init_instruction_ind' := Induction for local_init_instruction Sort Prop
  with local_init_sequence_ind' := Induction for local_init_sequence Sort Prop.
Combined Scheme local_init_mutind from
  local_init_instruction_ind', local_init_sequence_ind'.

Lemma check_local_init_complete :
  (forall I e J, local_init_instruction I e J ->
    check_local_init_instruction e I = Some J) /\
  (forall I es J, local_init_sequence I es J ->
    check_local_init_sequence es I = Some J).
Proof.
  apply local_init_mutind.
  - move => I e Hplain. by destruct e.
  - move => I x E. by simpl; rewrite E.
  - move => I x b E. by simpl; rewrite E.
  - move => I x b E. by simpl; rewrite E.
  - move => I J bt es _ IH.
    change (match check_local_init_sequence es I with
            | Some _ => Some I | None => None end = Some I).
    by rewrite IH.
  - move => I J bt es _ IH.
    change (match check_local_init_sequence es I with
            | Some _ => Some I | None => None end = Some I).
    by rewrite IH.
  - move => I J1 J2 bt es1 es2 _ IH1 _ IH2.
    change (match check_local_init_sequence es1 I, check_local_init_sequence es2 I with
            | Some _, Some _ => Some I | _, _ => None end = Some I).
    by rewrite IH1 IH2.
  - done.
  - move => I J K e es _ IH1 _ IH2. by simpl; rewrite IH1.
Qed.

Theorem check_local_init_sequence_correct es I J :
  check_local_init_sequence es I = Some J <-> local_init_sequence I es J.
Proof.
  split; first apply check_local_init_sequence_sound.
  exact ((proj2 check_local_init_complete) I es J).
Qed.

Lemma local_init_le_refl I : local_init_le I I.
Proof. induction I; constructor => //. Qed.

Lemma local_init_le_lookup I J n :
  local_init_le I J ->
  nth_error I n = Some true ->
  nth_error J n = Some true.
Proof.
  move => H; move: n.
  induction H; destruct n => //=.
  - move => [E]. subst x.
    have Etrue : true = true by reflexivity.
    by rewrite (H Etrue).
  - by apply IHForall2.
Qed.

Lemma local_init_le_lookup_exists I J n b :
  local_init_le I J ->
  nth_error I n = Some b ->
  exists b', nth_error J n = Some b'.
Proof.
  move => H; move: n.
  induction H; destruct n => //=.
  - move => _. by exists y.
  - by apply IHForall2.
Qed.

Lemma local_init_le_set I J n :
  local_init_le I J ->
  local_init_le (set_nth false I n true) (set_nth false J n true).
Proof.
  move => H; move: n.
  induction H as [|x y xs ys Hxy Hrel IH]; move => n.
  - apply local_init_le_refl.
  - destruct n => /=; constructor => //.
    by apply IH.
Qed.

Lemma local_init_monotone :
  (forall I e O, local_init_instruction I e O ->
    forall J, local_init_le I J ->
    exists P, local_init_instruction J e P /\ local_init_le O P) /\
  (forall I es O, local_init_sequence I es O ->
    forall J, local_init_le I J ->
    exists P, local_init_sequence J es P /\ local_init_le O P).
Proof.
  apply local_init_mutind.
  - move => I e Hplain J Hle. exists J; split => //.
    by apply li_plain.
  - move => I x Hget J Hle. exists J; split => //.
    apply li_get. by eapply local_init_le_lookup; eauto.
  - move => I x b Hget J Hle.
    destruct (local_init_le_lookup_exists Hle Hget) as [b' Hb'].
    exists (set_nth false J (N.to_nat x) true); split.
    + by eapply li_set; eauto.
    + by apply local_init_le_set.
  - move => I x b Hget J Hle.
    destruct (local_init_le_lookup_exists Hle Hget) as [b' Hb'].
    exists (set_nth false J (N.to_nat x) true); split.
    + by eapply li_tee; eauto.
    + by apply local_init_le_set.
  - move => I O bt es _ IH J Hle.
    destruct (IH J Hle) as [P [HP _]].
    exists J; split => //. by eapply li_block; eauto.
  - move => I O bt es _ IH J Hle.
    destruct (IH J Hle) as [P [HP _]].
    exists J; split => //. by eapply li_loop; eauto.
  - move => I O1 O2 bt es1 es2 _ IH1 _ IH2 J Hle.
    destruct (IH1 J Hle) as [P1 [HP1 _]].
    destruct (IH2 J Hle) as [P2 [HP2 _]].
    exists J; split => //. by eapply li_if; eauto.
  - move => I J Hle. exists J; split => //. constructor.
  - move => I M O e es _ IH1 _ IH2 J Hle.
    destruct (IH1 J Hle) as [M' [He Hle']].
    destruct (IH2 M' Hle') as [P [Hes Hle'']].
    exists P; split => //. by econstructor; eauto.
Qed.
