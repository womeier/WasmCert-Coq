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

Lemma local_init_le_trans I J K :
  local_init_le I J -> local_init_le J K -> local_init_le I K.
Proof.
  move => H; move: K.
  induction H; move => K HJK; inversion HJK; subst; constructor => //.
  - by auto.
  - by apply IHForall2.
Qed.

Lemma local_init_le_write I n b :
  nth_error I n = Some b ->
  local_init_le I (set_nth false I n true).
Proof.
  move: n; induction I as [|a I IH]; destruct n => //=.
  - move => _. constructor; first done. apply local_init_le_refl.
  - move => H. constructor; first done. by apply IH.
Qed.

Lemma local_init_grows :
  (forall I e O, local_init_instruction I e O -> local_init_le I O) /\
  (forall I es O, local_init_sequence I es O -> local_init_le I O).
Proof.
  apply local_init_mutind.
  - move => I e _. apply local_init_le_refl.
  - move => I x _. apply local_init_le_refl.
  - move => I x b H. by eapply local_init_le_write; eauto.
  - move => I x b H. by eapply local_init_le_write; eauto.
  - move => I O bt es _ _. apply local_init_le_refl.
  - move => I O bt es _ _. apply local_init_le_refl.
  - move => I O1 O2 bt es1 es2 _ _ _ _. apply local_init_le_refl.
  - move => I. apply local_init_le_refl.
  - move => I M O e es _ H1 _ H2. by eapply local_init_le_trans; eauto.
Qed.

Lemma local_init_le_top I :
  local_init_le I (List.repeat true (length I)).
Proof. induction I; constructor => //. Qed.

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

Lemma initialized_slots_cat {A} (xs ys : list (option A)) :
  initialized_slots (xs ++ ys) = initialized_slots xs ++ initialized_slots ys.
Proof. by rewrite /initialized_slots map_cat. Qed.

Lemma initialized_slots_some {A} (xs : list A) :
  initialized_slots (map Some xs) = List.repeat true (length xs).
Proof. induction xs => //=. by rewrite IHxs. Qed.

Lemma initialized_slots_defaults ts :
  initialized_slots (map default_val ts) =
    map (fun t => default_val t != None) ts.
Proof.
  induction ts as [|t ts IH] => //=.
  destruct (default_val t); simpl; by rewrite IH.
Qed.

Lemma initialized_slots_call args params locals :
  length args = length params ->
  initialized_slots (map Some args ++ map default_val locals) =
    initial_local_state params locals.
Proof.
  move => Hlength.
  by rewrite initialized_slots_cat initialized_slots_some
    initialized_slots_defaults Hlength.
Qed.

Section Administrative.
Context `{hfc : host_function_class}.

Lemma administrative_local_init_sequence_monotone_from es :
  TProp.Forall (fun e => forall I O J,
    check_administrative_local_init e I = Some O ->
    local_init_le I J ->
    exists P, check_administrative_local_init e J = Some P /\ local_init_le O P) es ->
  forall I O J,
    check_administrative_local_init_sequence es I = Some O ->
    local_init_le I J ->
    exists P, check_administrative_local_init_sequence es J = Some P /\
      local_init_le O P.
Proof.
  induction es as [|e es IH]; move => Hall I O J Hcheck Hle.
  - injection Hcheck as <-. by exists J.
  - inversion Hall; subst.
    simpl in Hcheck.
    destruct (check_administrative_local_init e I) as [M|] eqn:He; try discriminate.
    match goal with Hmono : forall I O J, _ |- _ =>
      destruct (Hmono _ _ _ He Hle) as [M' [He' Hle']]
    end.
    have Htail : exists P,
      check_administrative_local_init_sequence es M' = Some P /\ local_init_le O P.
    { eapply IH; eauto. }
    destruct Htail as [P [HP HOP]].
    exists P; split => //. by simpl; rewrite He'.
Qed.

Lemma administrative_local_init_monotone e I O J :
  check_administrative_local_init e I = Some O ->
  local_init_le I J ->
  exists P, check_administrative_local_init e J = Some P /\ local_init_le O P.
Proof.
  move: I O J.
  induction e using administrative_instruction_ind'; move => I O J Hcheck Hle.
  - apply check_local_init_instruction_sound in Hcheck.
    destruct ((proj1 local_init_monotone) _ _ _ Hcheck _ Hle) as [P [HP HOP]].
    exists P; split => //.
    by apply (proj1 check_local_init_complete).
  - injection Hcheck as <-.
    exists (List.repeat true (length J)); split; first reflexivity.
    apply List.Forall2_length in Hle.
    rewrite Hle. apply local_init_le_refl.
  - injection Hcheck as <-. by exists J.
  - injection Hcheck as <-. by exists J.
  - injection Hcheck as <-. by exists J.
  - injection Hcheck as <-. by exists J.
  - change
      (match check_administrative_local_init_sequence a1 I,
             check_administrative_local_init_sequence a0 I with
       | Some _, Some _ => Some I | _, _ => None end = Some O) in Hcheck.
    destruct (check_administrative_local_init_sequence a1 I) as [Ob|] eqn:Hbody;
      destruct (check_administrative_local_init_sequence a0 I) as [Oc|] eqn:Hcont;
      try discriminate.
    injection Hcheck as <-.
    destruct (administrative_local_init_sequence_monotone_from X0 Hbody Hle)
      as [Pb [HPb _]].
    destruct (administrative_local_init_sequence_monotone_from X Hcont Hle)
      as [Pc [HPc _]].
    exists J; split; last exact Hle.
    change
      (match check_administrative_local_init_sequence a1 J,
             check_administrative_local_init_sequence a0 J with
       | Some _, Some _ => Some J | _, _ => None end = Some J).
    by rewrite HPb HPc.
  - change
      (match check_administrative_local_init_sequence a1 (initialized_slots (f_locs a0)) with
       | Some _ => Some I | None => None end = Some O) in Hcheck.
    destruct (check_administrative_local_init_sequence a1 (initialized_slots (f_locs a0)))
      eqn:Hbody; try discriminate.
    injection Hcheck as <-. exists J; split; last exact Hle.
    change
      (match check_administrative_local_init_sequence a1 (initialized_slots (f_locs a0)) with
       | Some _ => Some J | None => None end = Some J).
    by rewrite Hbody.
  - injection Hcheck as <-. by exists J.
Qed.

Theorem administrative_local_init_sequence_monotone es I O J :
  check_administrative_local_init_sequence es I = Some O ->
  local_init_le I J ->
  exists P, check_administrative_local_init_sequence es J = Some P /\ local_init_le O P.
Proof.
  apply administrative_local_init_sequence_monotone_from.
  induction es as [|e es IH]; constructor => //.
  exact (@administrative_local_init_monotone e).
Qed.

Lemma administrative_local_init_grows e I O :
  check_administrative_local_init e I = Some O ->
  local_init_le I O.
Proof.
  destruct e; simpl.
  - move/check_local_init_instruction_sound.
    exact ((proj1 local_init_grows) I b O).
  - move => [<-]. apply local_init_le_top.
  - move => [<-]. apply local_init_le_refl.
  - move => [<-]. apply local_init_le_refl.
  - move => [<-]. apply local_init_le_refl.
  - move => [<-]. apply local_init_le_refl.
  - fold check_administrative_local_init_sequence.
    destruct (check_administrative_local_init_sequence l0 I);
      destruct (check_administrative_local_init_sequence l I) => //.
    move => [<-]. apply local_init_le_refl.
  - fold check_administrative_local_init_sequence.
    destruct (check_administrative_local_init_sequence l (initialized_slots (f_locs f))) => //.
    move => [<-]. apply local_init_le_refl.
  - move => [<-]. apply local_init_le_refl.
Qed.

Lemma administrative_local_init_sequence_grows es I O :
  check_administrative_local_init_sequence es I = Some O ->
  local_init_le I O.
Proof.
  move: I; induction es as [|e es IH]; move => I Hcheck.
  - by injection Hcheck as <-; apply local_init_le_refl.
  - simpl in Hcheck.
    destruct (check_administrative_local_init e I) as [M|] eqn:He; try discriminate.
    eapply local_init_le_trans.
    + by eapply administrative_local_init_grows; eauto.
    + by apply IH.
Qed.

Lemma administrative_local_init_app es1 es2 I :
  check_administrative_local_init_sequence (es1 ++ es2) I =
    match check_administrative_local_init_sequence es1 I with
    | Some J => check_administrative_local_init_sequence es2 J
    | None => None
    end.
Proof.
  move: I; induction es1 as [|e es1 IH]; move => I => //=.
  destruct (check_administrative_local_init e I) => //.
Qed.

Lemma administrative_local_init_value v I :
  check_administrative_local_init (v_to_e v) I = Some I.
Proof.
  destruct v as [n|v|[h|a|a|n]]; reflexivity.
Qed.

Lemma administrative_local_init_values vs I :
  check_administrative_local_init_sequence (v_to_e_list vs) I = Some I.
Proof.
  induction vs as [|v vs IH] => //=.
  by rewrite administrative_local_init_value IH.
Qed.

Lemma administrative_local_init_get I O x :
  check_administrative_local_init_sequence [::AI_basic (BI_local_get x)] I =
    Some O ->
  lookup_N I x = Some true.
Proof.
  simpl.
  destruct (lookup_N I x) as [[|]|] eqn:E => //=.
Qed.

Lemma administrative_local_init_frame_context values suffix arity f body I O :
  check_administrative_local_init_sequence
    (v_to_e_list values ++ [::AI_frame arity f body] ++ suffix) I = Some O ->
  exists J, check_administrative_local_init_sequence body
    (initialized_slots f.(f_locs)) = Some J.
Proof.
  rewrite administrative_local_init_app administrative_local_init_values /=.
  fold check_administrative_local_init_sequence.
  destruct (check_administrative_local_init_sequence body
    (initialized_slots (f_locs f))) eqn:E => //.
  move => _. by eexists.
Qed.

Lemma administrative_local_init_lfill k (lh : lholed k) es I O :
  check_administrative_local_init_sequence (lfill lh es) I = Some O ->
  exists J, check_administrative_local_init_sequence es I = Some J.
Proof.
  move: I O; induction lh; move => I O Hcheck.
  - simpl in Hcheck.
    rewrite administrative_local_init_app administrative_local_init_values /= in Hcheck.
    rewrite administrative_local_init_app in Hcheck.
    destruct (check_administrative_local_init_sequence es I) eqn:E;
      try discriminate.
    by eexists.
  - simpl lfill in Hcheck.
    rewrite administrative_local_init_app administrative_local_init_values /= in Hcheck.
    change
      (match
         match check_administrative_local_init_sequence (lfill lh es) I,
               check_administrative_local_init_sequence l0 I with
         | Some _, Some _ => Some I | _, _ => None
         end
       with
       | Some J => check_administrative_local_init_sequence l1 J
       | None => None
       end = Some O) in Hcheck.
    destruct (check_administrative_local_init_sequence (lfill lh es) I) eqn:Ebody;
      destruct (check_administrative_local_init_sequence l0 I) eqn:Econt;
      try discriminate.
    by eapply IHlh; eauto.
Qed.

Lemma administrative_local_init_lfill_replace k (lh : lholed k) es es' I I' O :
  local_init_le I I' ->
  (forall M, check_administrative_local_init_sequence es I = Some M ->
    exists M', check_administrative_local_init_sequence es' I' = Some M' /\
      local_init_le M M') ->
  check_administrative_local_init_sequence (lfill lh es) I = Some O ->
  exists O', check_administrative_local_init_sequence (lfill lh es') I' = Some O' /\
    local_init_le O O'.
Proof.
  move: I I' O; induction lh; move => I I' O Hle Hreplace Hcheck.
  - simpl in Hcheck.
    rewrite administrative_local_init_app administrative_local_init_values /=
      administrative_local_init_app in Hcheck.
    destruct (check_administrative_local_init_sequence es I) as [M|] eqn:He;
      try discriminate.
    destruct (Hreplace M (Logic.eq_refl _)) as [M' [He' Hle']].
    destruct (administrative_local_init_sequence_monotone Hcheck Hle')
      as [P [HP HOP]].
    exists P; split; last exact HOP.
    simpl. rewrite administrative_local_init_app administrative_local_init_values /=
      administrative_local_init_app He' HP. reflexivity.
  - simpl lfill in Hcheck.
    rewrite administrative_local_init_app administrative_local_init_values /= in Hcheck.
    change
      (match
         match check_administrative_local_init_sequence (lfill lh es) I,
               check_administrative_local_init_sequence l0 I with
         | Some _, Some _ => Some I | _, _ => None
         end
       with
       | Some J => check_administrative_local_init_sequence l1 J
       | None => None
       end = Some O) in Hcheck.
    destruct (check_administrative_local_init_sequence (lfill lh es) I) as [Ob|] eqn:Hbody;
      destruct (check_administrative_local_init_sequence l0 I) as [Oc|] eqn:Hcont;
      try discriminate.
    destruct (IHlh I I' Ob Hle Hreplace Hbody) as [Pb [HPb _]].
    destruct (administrative_local_init_sequence_monotone Hcont Hle) as [Pc [HPc _]].
    destruct (administrative_local_init_sequence_monotone Hcheck Hle) as [P [HP HOP]].
    exists P; split; last exact HOP.
    simpl lfill.
    rewrite administrative_local_init_app administrative_local_init_values /=.
    change
      (match
         match check_administrative_local_init_sequence (lfill lh es') I',
               check_administrative_local_init_sequence l0 I' with
         | Some _, Some _ => Some I' | _, _ => None
         end
       with
       | Some J => check_administrative_local_init_sequence l1 J
       | None => None
       end = Some P).
    by rewrite HPb HPc HP.
Qed.

Lemma administrative_local_init_source es I :
  check_administrative_local_init_sequence (to_e_list es) I =
    check_local_init_sequence es I.
Proof.
  move: I; induction es as [|e es IH]; move => I => //=.
  destruct (check_local_init_instruction e I) => //.
Qed.

Theorem initialized_native_frame_admissible args params locals body O inst arity I :
  length args = length params ->
  local_init_sequence (initial_local_state params locals) body O ->
  check_administrative_local_init
    (AI_frame arity
      (Build_frame (map Some args ++ map default_val locals) inst)
      [::AI_label arity nil (to_e_list body)]) I = Some I.
Proof.
  move => Hlength Hbody.
  have Hcheck := (proj2 check_local_init_complete) _ _ _ Hbody.
  simpl.
  fold check_administrative_local_init_sequence.
  rewrite (@initialized_slots_call args params locals Hlength).
  rewrite administrative_local_init_source Hcheck.
  reflexivity.
Qed.

Theorem initialized_native_body_admissible args params locals body O arity :
  length args = length params ->
  local_init_sequence (initial_local_state params locals) body O ->
  exists J,
    check_administrative_local_init_sequence [::AI_label arity nil (to_e_list body)]
      (initialized_slots (map Some args ++ map default_val locals)) = Some J.
Proof.
  move => Hlength Hbody.
  have Hcheck := (proj2 check_local_init_complete) _ _ _ Hbody.
  simpl.
  fold check_administrative_local_init_sequence.
  rewrite administrative_local_init_source
    (@initialized_slots_call args params locals Hlength) Hcheck.
  by eexists.
Qed.

End Administrative.
