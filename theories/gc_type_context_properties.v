(** Correctness properties for canonical recursive-group closing and lookup.
    Closing is not structural declaration validation. The bounded path
    characterization and checked rank invariant establish full declared-path
    matching completeness for registries returned by the public closer. *)
From Wasm Require Import datatypes gc_type_context.
From Stdlib Require Import List NArith Arith Bool Lia Relation_Operators.
Import ListNotations.

Lemma canonical_group_eqb_correct a b :
  canonical_group_eqb a b = true <-> a = b.
Proof.
  unfold canonical_group_eqb. destruct (canonical_group_eq_dec a b);
    split; intros; congruence.
Qed.

Lemma defined_type_eqb_correct a b :
  defined_type_eqb a b = true <-> a = b.
Proof.
  unfold defined_type_eqb. destruct (defined_type_eq_dec a b);
    split; intros; congruence.
Qed.

Lemma find_canonical_group_sound groups group i :
  find_canonical_group groups group = Some i ->
  nth_error groups i = Some group.
Proof.
  revert i. induction groups as [|head groups IH]; intros i E; simpl in E.
  - discriminate.
  - destruct (canonical_group_eqb head group) eqn:Same.
    + apply canonical_group_eqb_correct in Same. subst head.
      inversion E; subst. reflexivity.
    + destruct (find_canonical_group groups group) as [j|] eqn:Found;
        simpl in E; [|discriminate].
      inversion E; subst. simpl. now apply IH.
Qed.

Lemma find_canonical_group_complete groups group :
  In group groups -> exists i, find_canonical_group groups group = Some i.
Proof.
  induction groups as [|head groups IH]; simpl; [contradiction |].
  intro Member. destruct (canonical_group_eqb head group) eqn:Same.
  - exists 0. reflexivity.
  - destruct Member as [E|Member].
    + subst head. assert (canonical_group_eqb group group = true)
        by (apply canonical_group_eqb_correct; reflexivity). congruence.
    + destruct (IH Member) as [i E]. rewrite E. exists (S i). reflexivity.
Qed.

Lemma find_canonical_group_none groups group :
  find_canonical_group groups group = None <-> ~ In group groups.
Proof.
  split.
  - intros E Member.
    destruct (find_canonical_group_complete groups group Member) as [i Found].
    congruence.
  - intros Absent.
    destruct (find_canonical_group groups group) as [i|] eqn:E; [|reflexivity].
    apply find_canonical_group_sound in E.
    apply nth_error_In in E. contradiction.
Qed.

Lemma intern_group_lookup groups group :
  nth_error (fst (intern_group groups group))
    (N.to_nat (snd (intern_group groups group))) = Some group.
Proof.
  unfold intern_group.
  destruct (find_canonical_group groups group) as [i|] eqn:Found; simpl;
    rewrite Nat2N.id.
  - now apply find_canonical_group_sound.
  - rewrite nth_error_app2 by lia.
    now rewrite Nat.sub_diag.
Qed.

Lemma intern_group_extension groups group :
  exists suffix, fst (intern_group groups group) = groups ++ suffix.
Proof.
  unfold intern_group. destruct (find_canonical_group groups group); simpl.
  - exists []. now rewrite app_nil_r.
  - exists [group]. reflexivity.
Qed.

Lemma intern_group_preserves_lookup groups group i :
  i < length groups ->
  nth_error (fst (intern_group groups group)) i = nth_error groups i.
Proof.
  intro Bound.
  destruct (intern_group_extension groups group) as [suffix E].
  rewrite E. now apply nth_error_app1.
Qed.

Lemma intern_defined_lookup groups group i :
  lookup_defined_type (fst (intern_group groups group))
    (Def_type (snd (intern_group groups group)) (N.of_nat i)) =
  nth_error group i.
Proof.
  unfold lookup_defined_type; simpl.
  rewrite intern_group_lookup, Nat2N.id. reflexivity.
Qed.

Lemma close_type_index_prior prior members i t :
  (i < N.of_nat (length prior))%N ->
  nth_error prior (N.to_nat i) = Some t ->
  close_type_index prior members i = Some (CT_def t).
Proof.
  intros Bound Lookup. unfold close_type_index.
  assert (N.ltb i (N.of_nat (length prior)) = true) by (now apply N.ltb_lt).
  now rewrite H, Lookup.
Qed.

Lemma close_type_index_member prior members i :
  (i < members)%N ->
  close_type_index prior members (N.of_nat (length prior) + i)%N = Some (CT_rec i).
Proof.
  intro Bound. unfold close_type_index.
  assert (Earlier : N.ltb (N.of_nat (length prior) + i)
    (N.of_nat (length prior)) = false) by (apply N.ltb_ge; lia).
  rewrite Earlier.
  replace (N.of_nat (length prior) + i - N.of_nat (length prior))%N with i by lia.
  assert (N.ltb i members = true) by (now apply N.ltb_lt).
  now rewrite H.
Qed.

Lemma close_type_index_outside prior members i :
  (N.of_nat (length prior) + members <= i)%N ->
  close_type_index prior members i = None.
Proof.
  intro Outside. unfold close_type_index.
  assert (N.ltb i (N.of_nat (length prior)) = false) by (apply N.ltb_ge; lia).
  assert (N.ltb (i - N.of_nat (length prior)) members = false)
    by (apply N.ltb_ge; lia).
  now rewrite H, H0.
Qed.

Lemma close_type_index_scope prior members i u :
  close_type_index prior members i = Some u ->
  (exists t, u = CT_def t /\ In t prior) \/
  (exists j, u = CT_rec j /\ (j < members)%N).
Proof.
  unfold close_type_index.
  destruct (N.ltb i (N.of_nat (length prior))) eqn:Earlier.
  - destruct (nth_error prior (N.to_nat i)) as [t|] eqn:Lookup;
      simpl; [|discriminate].
    intro E; inversion E; subst. left. exists t.
    split; [reflexivity | now apply nth_error_In in Lookup].
  - destruct (N.ltb (i - N.of_nat (length prior)) members) eqn:Member;
      [|discriminate].
    intro E; inversion E; subst. right.
    eexists. split; [reflexivity | now apply N.ltb_lt].
Qed.

Lemma close_subtypes_length prior members offset source closed :
  close_subtypes prior members offset source = Some closed ->
  length closed = length source.
Proof.
  revert offset closed. induction source as [|t source IH]; intros offset closed E.
  - inversion E. reflexivity.
  - simpl in E.
    destruct (close_subtype prior members offset t) as [head|]; [|discriminate].
    destruct (close_subtypes prior members (N.succ offset) source) as [tail|]
      eqn:Tail; [|discriminate].
    inversion E; subst. simpl. now rewrite (IH _ _ Tail).
Qed.

Lemma group_defined_types_length group members :
  length (group_defined_types group members) = members.
Proof. unfold group_defined_types. now rewrite length_map, length_seq. Qed.

Lemma close_type_group_count groups prior source groups' ids :
  close_type_group groups prior source = Some (groups', ids) ->
  length ids = length source.
Proof.
  unfold close_type_group.
  destruct (close_subtypes prior (N.of_nat (length source)) 0 source)
    as [closed|] eqn:Closed; [|discriminate].
  destruct (intern_group groups closed) as [registry address] eqn:Intern.
  intro E; inversion E; subst.
  rewrite group_defined_types_length.
  now apply close_subtypes_length in Closed.
Qed.

Lemma close_type_group_extension groups prior source groups' ids :
  close_type_group groups prior source = Some (groups', ids) ->
  exists suffix, groups' = groups ++ suffix.
Proof.
  unfold close_type_group.
  destruct (close_subtypes prior (N.of_nat (length source)) 0 source)
    as [closed|] eqn:Closed; [|discriminate].
  pose proof (intern_group_extension groups closed) as Ext.
  destruct (intern_group groups closed) as [registry address]; simpl in Ext.
  intro E; inversion E; subst. exact Ext.
Qed.

Lemma close_type_groups_extension groups prior source groups' ids :
  close_type_groups_from groups prior source = Some (groups', ids) ->
  exists suffix, groups' = groups ++ suffix.
Proof.
  revert groups prior groups' ids.
  induction source as [|group source IH]; intros groups prior groups' ids E.
  - inversion E; subst. exists []. now rewrite app_nil_r.
  - simpl in E.
    destruct (close_type_group groups prior group) as [[registry types]|] eqn:Closed;
      [|discriminate].
    destruct (IH _ _ _ _ E) as [tail Ext].
    destruct (close_type_group_extension _ _ _ _ _ Closed) as [head Prefix].
    exists (head ++ tail). now rewrite Ext, Prefix, app_assoc.
Qed.

Lemma close_type_groups_count groups prior source groups' ids :
  close_type_groups_from groups prior source = Some (groups', ids) ->
  length ids = length prior + fold_right (fun g n => length g + n) 0 source.
Proof.
  revert groups prior groups' ids.
  induction source as [|group source IH]; intros groups prior groups' ids E.
  - inversion E; subst. simpl. lia.
  - simpl in E.
    destruct (close_type_group groups prior group) as [[registry types]|] eqn:Closed;
      [|discriminate].
    pose proof (close_type_group_count _ _ _ _ _ Closed).
    specialize (IH _ _ _ _ E). rewrite length_app in IH. simpl. lia.
Qed.

Lemma expand_recursive_heap self i :
  expand_heap_type self (CH_defined (CT_rec i)) =
    CH_defined (CT_def (Def_type (defined_group self) i)).
Proof. reflexivity. Qed.

Lemma expand_external_heap self t :
  expand_heap_type self (CH_defined (CT_def t)) = CH_defined (CT_def t).
Proof. reflexivity. Qed.

Lemma defined_type_matches_fuel_sound fuel groups a b :
  defined_type_matches_fuel fuel groups a b = true ->
  exists n, n <= fuel /\ declared_type_path groups n a b.
Proof.
  revert a b. induction fuel as [|fuel IH]; intros a b; simpl.
  - destruct (defined_type_eqb a b) eqn:Same; [|discriminate].
    apply defined_type_eqb_correct in Same. subst b.
    intro E. exists 0. split; [lia | constructor].
  - destruct (defined_type_eqb a b) eqn:Same.
    + apply defined_type_eqb_correct in Same. subst b.
      intro E. exists 0. split; [lia | constructor].
    + destruct (expand_defined_type groups a) as [st|] eqn:Expanded;
        [|discriminate].
      intro Match. apply existsb_exists in Match.
      destruct Match as [parent [Member Match]].
      destruct parent as [i|p]; [discriminate |].
      destruct (IH p b Match) as [n [Bound Path]].
      exists (S n). split; [lia |].
      eapply dtp_step with (b := p); [exists st; auto | exact Path].
Qed.

Lemma defined_type_matches_fuel_complete groups n a b :
  declared_type_path groups n a b ->
  forall fuel, n <= fuel -> defined_type_matches_fuel fuel groups a b = true.
Proof.
  intro Path. induction Path as [a|n a b c Step Path IH]; intros fuel Bound.
  - destruct fuel; simpl;
      assert (defined_type_eqb a a = true)
        by (apply defined_type_eqb_correct; reflexivity); now rewrite H.
  - destruct fuel as [|fuel]; [lia |]. simpl.
    destruct (defined_type_eqb a c) eqn:Same; [reflexivity |].
    destruct Step as [st [Expanded Member]]. rewrite Expanded.
    apply existsb_exists. exists (CT_def b). split; [exact Member |].
    simpl. apply IH. lia.
Qed.

Theorem defined_type_matches_fuel_correct fuel groups a b :
  defined_type_matches_fuel fuel groups a b = true <->
  exists n, n <= fuel /\ declared_type_path groups n a b.
Proof.
  split; [apply defined_type_matches_fuel_sound |].
  intros [n [Bound Path]]. now apply (defined_type_matches_fuel_complete _ _ _ _ Path).
Qed.

Theorem defined_type_matches_sound groups a b :
  defined_type_matches groups a b = true ->
  exists n, declared_type_path groups n a b.
Proof.
  intro Match. apply defined_type_matches_fuel_sound in Match.
  destruct Match as [n [_ Path]]. now exists n.
Qed.

Theorem defined_type_equiv_sound groups a b :
  defined_type_equiv groups a b = true ->
  (exists n, declared_type_path groups n a b) /\
  (exists n, declared_type_path groups n b a).
Proof.
  unfold defined_type_equiv. rewrite andb_true_iff.
  intros [Forward Backward]. split; now apply defined_type_matches_sound.
Qed.

Definition canonical_registry_super_wf groups : Prop :=
  forall a b, declared_type_step groups a b ->
    (exists parent, lookup_defined_type groups b = Some parent) /\
    defined_type_rank groups b < defined_type_rank groups a.

Lemma nth_error_index_bound {A} (xs : list A) i x :
  nth_error xs i = Some x -> i < length xs.
Proof.
  intro E.
  destruct (lt_dec i (length xs)); [assumption |].
  assert (nth_error xs i = None) by (apply nth_error_None; lia).
  congruence.
Qed.

Theorem canonical_registry_super_orderedb_sound groups :
  canonical_registry_super_orderedb groups = true ->
  canonical_registry_super_wf groups.
Proof.
  intros Checked a b [expanded [Expand Member]].
  unfold expand_defined_type in Expand.
  destruct (lookup_defined_type groups a) as [raw|] eqn:Lookup; [|discriminate].
  inversion Expand; subst expanded.
  change (In (CT_def b)
    (map (fun u => CT_def (resolve_type_use a u)) (subtype_supers raw))) in Member.
  apply in_map_iff in Member.
  destruct Member as [u [Resolved Member]].
  injection Resolved as Resolved.
  unfold lookup_defined_type in Lookup.
  destruct (nth_error groups (N.to_nat (defined_group a))) as [group|] eqn:Group;
    [|discriminate].
  unfold canonical_registry_super_orderedb in Checked.
  apply forallb_forall with (x := N.to_nat (defined_group a)) in Checked.
  2: { apply in_seq. split; [lia | now apply nth_error_index_bound in Group]. }
  rewrite Group in Checked.
  apply forallb_forall with (x := N.to_nat (defined_member a)) in Checked.
  2: { apply in_seq. split; [lia | now apply nth_error_index_bound in Lookup]. }
  rewrite Lookup in Checked.
  destruct a as [g i]. simpl in *.
  rewrite !N2Nat.id in Checked.
  apply forallb_forall with (x := u) in Checked; [|exact Member].
  rewrite Resolved in Checked.
  apply andb_true_iff in Checked. destruct Checked as [Valid Smaller].
  split.
  - unfold defined_type_validb in Valid.
    destruct (lookup_defined_type groups b) as [parent|] eqn:Parent;
      [now exists parent | discriminate].
  - now apply Nat.ltb_lt.
Qed.

Theorem close_type_groups_super_wf groups source registry types :
  close_type_groups groups source = Some (registry, types) ->
  canonical_registry_super_wf registry.
Proof.
  unfold close_type_groups.
  destruct (close_type_groups_from groups [] source) as [[output ids]|];
    [|discriminate].
  destruct (canonical_registry_super_orderedb output) eqn:Checked;
    [|discriminate].
  intro E; inversion E; subst.
  now apply canonical_registry_super_orderedb_sound.
Qed.

Lemma registry_prefix_member_bound groups gi group :
  nth_error groups gi = Some group ->
  canonical_registry_size (firstn gi groups) + length group <=
    canonical_registry_size groups.
Proof.
  revert gi group. induction groups as [|head groups IH]; intros gi group E.
  - destruct gi; discriminate.
  - destruct gi as [|gi].
    + inversion E; subst. simpl. lia.
    + simpl in E. specialize (IH _ _ E). simpl. lia.
Qed.

Lemma defined_type_rank_bound groups t raw :
  lookup_defined_type groups t = Some raw ->
  defined_type_rank groups t < canonical_registry_size groups.
Proof.
  unfold lookup_defined_type, defined_type_rank.
  destruct (nth_error groups (N.to_nat (defined_group t))) as [group|] eqn:Group;
    [|discriminate].
  intro Member.
  pose proof (registry_prefix_member_bound _ _ _ Group).
  apply nth_error_index_bound in Member. lia.
Qed.

Lemma declared_type_step_source_valid groups a b :
  declared_type_step groups a b ->
  exists raw, lookup_defined_type groups a = Some raw.
Proof.
  intros [st [Expand Member]]. unfold expand_defined_type in Expand.
  destruct (lookup_defined_type groups a) as [raw|] eqn:Raw;
    [now exists raw | discriminate].
Qed.

Lemma declared_type_path_rank_bound groups n a b :
  canonical_registry_super_wf groups ->
  declared_type_path groups n a b ->
  n <= defined_type_rank groups a.
Proof.
  intros WF Path. induction Path as [a|n a b c Step Path IH]; [lia |].
  destruct (WF a b Step) as [_ Smaller]. lia.
Qed.

Theorem defined_type_matches_complete groups n a b :
  canonical_registry_super_wf groups ->
  declared_type_path groups n a b ->
  defined_type_matches groups a b = true.
Proof.
  intros WF Path. unfold defined_type_matches.
  destruct n as [|n].
  - apply (defined_type_matches_fuel_complete _ _ _ _ Path). lia.
  - assert (Start : exists raw, lookup_defined_type groups a = Some raw).
    { inversion Path; subst. eapply declared_type_step_source_valid; eassumption. }
    destruct Start as [raw Raw].
    pose proof (defined_type_rank_bound _ _ _ Raw).
    pose proof (declared_type_path_rank_bound _ _ _ _ WF Path).
    apply (defined_type_matches_fuel_complete _ _ _ _ Path). lia.
Qed.

Theorem defined_type_matches_correct groups a b :
  canonical_registry_super_wf groups ->
  (defined_type_matches groups a b = true <->
    exists n, declared_type_path groups n a b).
Proof.
  intro WF. split; [apply defined_type_matches_sound |].
  intros [n Path]. now apply (defined_type_matches_complete groups n a b).
Qed.

Theorem closed_groups_matching_complete initial source groups types a b :
  close_type_groups initial source = Some (groups, types) ->
  (defined_type_matches groups a b = true <->
    exists n, declared_type_path groups n a b).
Proof.
  intro Closed. apply defined_type_matches_correct.
  now apply close_type_groups_super_wf in Closed.
Qed.

Lemma declared_type_path_append groups n a b m c :
  declared_type_path groups n a b ->
  declared_type_path groups m b c ->
  declared_type_path groups (n + m) a c.
Proof.
  intros First. revert m c.
  induction First as [a|n a b c Step First IH]; intros m d Last.
  - exact Last.
  - simpl. eapply dtp_step; [exact Step | now apply IH].
Qed.

Theorem defined_type_matches_trans groups a b c :
  canonical_registry_super_wf groups ->
  defined_type_matches groups a b = true ->
  defined_type_matches groups b c = true ->
  defined_type_matches groups a c = true.
Proof.
  intros WF First Last.
  apply defined_type_matches_sound in First.
  apply defined_type_matches_sound in Last.
  destruct First as [n First], Last as [m Last].
  apply (defined_type_matches_complete groups (n + m) a c WF).
  now apply declared_type_path_append with (b := b).
Qed.

Theorem defined_type_equiv_correct groups a b :
  canonical_registry_super_wf groups ->
  (defined_type_equiv groups a b = true <->
    (exists n, declared_type_path groups n a b) /\
    (exists n, declared_type_path groups n b a)).
Proof.
  intro WF. unfold defined_type_equiv.
  rewrite andb_true_iff, !defined_type_matches_correct by exact WF.
  reflexivity.
Qed.

Theorem close_type_groups_count_public initial source groups types :
  close_type_groups initial source = Some (groups, types) ->
  length types = fold_right (fun g n => length g + n) 0 source.
Proof.
  unfold close_type_groups.
  destruct (close_type_groups_from initial [] source) as [[registry ids]|]
    eqn:Closed; [|discriminate].
  destruct (canonical_registry_super_orderedb registry); [|discriminate].
  intro E; inversion E; subst.
  apply close_type_groups_count in Closed. exact Closed.
Qed.

Theorem close_type_groups_extension_public initial source groups types :
  close_type_groups initial source = Some (groups, types) ->
  exists suffix, groups = initial ++ suffix.
Proof.
  unfold close_type_groups.
  destruct (close_type_groups_from initial [] source) as [[registry ids]|]
    eqn:Closed; [|discriminate].
  destruct (canonical_registry_super_orderedb registry); [|discriminate].
  intro E; inversion E; subst.
  now apply close_type_groups_extension in Closed.
Qed.

Lemma lookup_defined_type_extension groups suffix t :
  N.to_nat (defined_group t) < length groups ->
  lookup_defined_type (groups ++ suffix) t = lookup_defined_type groups t.
Proof.
  intro Bound. unfold lookup_defined_type.
  now rewrite nth_error_app1.
Qed.

Theorem expand_defined_type_extension groups suffix t :
  N.to_nat (defined_group t) < length groups ->
  expand_defined_type (groups ++ suffix) t = expand_defined_type groups t.
Proof.
  intro Bound. unfold expand_defined_type.
  now rewrite lookup_defined_type_extension.
Qed.

Theorem expand_function_type_extension groups suffix t :
  N.to_nat (defined_group t) < length groups ->
  expand_function_type (groups ++ suffix) t = expand_function_type groups t.
Proof.
  intro Bound. unfold expand_function_type.
  now rewrite expand_defined_type_extension.
Qed.

Lemma NoDup_append_single {A} (xs : list A) x :
  NoDup xs -> ~ In x xs -> NoDup (xs ++ [x]).
Proof.
  intros Unique. induction Unique as [|head tail Notin Unique IH].
  - intro Absent. simpl. constructor; [simpl; tauto | constructor].
  - intro Absent. simpl. constructor.
    + intro Member. apply in_app_iff in Member.
      destruct Member as [Member|[E|False]]; [contradiction | |contradiction].
      subst x. apply Absent. now left.
    + apply IH. intro Member. apply Absent. now right.
Qed.

Theorem intern_group_nodup groups group :
  NoDup groups -> NoDup (fst (intern_group groups group)).
Proof.
  intro Unique. unfold intern_group.
  destruct (find_canonical_group groups group) eqn:Found; simpl; [exact Unique |].
  apply NoDup_append_single; [exact Unique |].
  now apply find_canonical_group_none.
Qed.

Lemma close_type_group_nodup groups prior source groups' ids :
  NoDup groups ->
  close_type_group groups prior source = Some (groups', ids) ->
  NoDup groups'.
Proof.
  intro Unique. unfold close_type_group.
  destruct (close_subtypes prior (N.of_nat (length source)) 0 source)
    as [closed|]; [|discriminate].
  pose proof (intern_group_nodup groups closed Unique) as Result.
  destruct (intern_group groups closed) as [registry address]; simpl in Result.
  intro E; inversion E; subst. exact Result.
Qed.

Lemma close_type_groups_nodup initial prior source groups types :
  NoDup initial ->
  close_type_groups_from initial prior source = Some (groups, types) ->
  NoDup groups.
Proof.
  revert initial prior groups types.
  induction source as [|group source IH]; intros initial prior groups types Unique Closed.
  - inversion Closed; subst. exact Unique.
  - simpl in Closed.
    destruct (close_type_group initial prior group) as [[registry ids]|] eqn:Group;
      [|discriminate].
    eapply IH; [|exact Closed].
    eapply close_type_group_nodup; eassumption.
Qed.

Theorem close_type_groups_nodup_public initial source groups types :
  NoDup initial ->
  close_type_groups initial source = Some (groups, types) ->
  NoDup groups.
Proof.
  intro Unique. unfold close_type_groups.
  destruct (close_type_groups_from initial [] source) as [[registry ids]|]
    eqn:Closed; [|discriminate].
  destruct (canonical_registry_super_orderedb registry); [|discriminate].
  intro E; inversion E; subst.
  now apply close_type_groups_nodup in Closed.
Qed.

Theorem canonical_group_identity_unique (groups : canonical_registry) i j group :
  NoDup groups ->
  nth_error groups i = Some group ->
  nth_error groups j = Some group ->
  i = j.
Proof.
  intro Unique. revert i j.
  induction Unique as [|head tail Notin Unique IH]; intros i j First Last.
  - destruct i; discriminate.
  - destruct i as [|i], j as [|j]; simpl in *.
    + reflexivity.
    + inversion First; subst. apply nth_error_In in Last. contradiction.
    + inversion Last; subst. apply nth_error_In in First. contradiction.
    + f_equal. now apply IH.
Qed.

Theorem defined_type_matches_refl groups a :
  defined_type_matches groups a a = true.
Proof.
  unfold defined_type_matches.
  apply (defined_type_matches_fuel_complete groups 0 a a); [constructor | lia].
Qed.

Lemma declared_type_path_rank_mono groups n a b :
  canonical_registry_super_wf groups ->
  declared_type_path groups n a b ->
  defined_type_rank groups b <= defined_type_rank groups a.
Proof.
  intros WF Path. induction Path as [a|n a b c Step Path IH]; [lia |].
  destruct (WF a b Step) as [_ Smaller]. lia.
Qed.

Lemma declared_type_path_positive_rank groups n a b :
  canonical_registry_super_wf groups ->
  declared_type_path groups (S n) a b ->
  defined_type_rank groups b < defined_type_rank groups a.
Proof.
  intros WF Path. inversion Path; subst.
  match goal with
  | Step : declared_type_step groups a ?middle,
    Tail : declared_type_path groups n ?middle b |- _ =>
      destruct (WF a middle Step) as [_ Smaller];
      pose proof (declared_type_path_rank_mono groups n middle b WF Tail); lia
  end.
Qed.

Theorem defined_type_equiv_eq groups a b :
  canonical_registry_super_wf groups ->
  (defined_type_equiv groups a b = true <-> a = b).
Proof.
  intro WF. split.
  - intro Equivalent. apply defined_type_equiv_sound in Equivalent.
    destruct Equivalent as [[n Forward] [m Backward]].
    destruct n as [|n].
    + now inversion Forward.
    + pose proof (declared_type_path_positive_rank groups n a b WF Forward).
      pose proof (declared_type_path_rank_mono groups m b a WF Backward).
      lia.
  - intro E; subst b. unfold defined_type_equiv.
    now rewrite defined_type_matches_refl.
Qed.

Definition defined_types_present groups ids : Prop :=
  Forall (fun t => exists st, lookup_defined_type groups t = Some st) ids.

Lemma defined_types_present_extension groups suffix ids :
  defined_types_present groups ids ->
  defined_types_present (groups ++ suffix) ids.
Proof.
  apply Forall_impl. intros t [st Lookup]. exists st.
  rewrite lookup_defined_type_extension; [exact Lookup |].
  unfold lookup_defined_type in Lookup.
  destruct (nth_error groups (N.to_nat (defined_group t))) eqn:Group;
    [now apply nth_error_index_bound in Group | discriminate].
Qed.

Lemma close_type_group_present groups prior source registry ids :
  close_type_group groups prior source = Some (registry, ids) ->
  defined_types_present registry ids.
Proof.
  unfold close_type_group.
  destruct (close_subtypes prior (N.of_nat (length source)) 0 source)
    as [closed|] eqn:Closed; [|discriminate].
  pose proof (intern_group_lookup groups closed) as Lookup.
  destruct (intern_group groups closed) as [output addr] eqn:Intern.
  simpl in Lookup. intro E; inversion E; subst.
  unfold defined_types_present, group_defined_types.
  apply Forall_forall. intros t Member. apply in_map_iff in Member.
  destruct Member as [i [Id Bound]]. subst t. apply in_seq in Bound.
  unfold lookup_defined_type. simpl. rewrite Nat2N.id, Lookup.
  destruct (nth_error closed i) as [st|] eqn:Member.
  - now exists st.
  - apply nth_error_None in Member. lia.
Qed.

Lemma close_type_groups_present initial prior source groups ids :
  defined_types_present initial prior ->
  close_type_groups_from initial prior source = Some (groups, ids) ->
  defined_types_present groups ids.
Proof.
  revert initial prior groups ids.
  induction source as [|head source IH]; intros initial prior groups ids Present Closed.
  - inversion Closed; subst. exact Present.
  - simpl in Closed.
    destruct (close_type_group initial prior head) as [[registry types]|] eqn:Group;
      [|discriminate].
    apply (IH registry (prior ++ types) groups ids); [|exact Closed].
    unfold defined_types_present. apply Forall_app. split.
    + destruct (close_type_group_extension _ _ _ _ _ Group) as [suffix Extension].
      rewrite Extension. now apply defined_types_present_extension.
    + now apply close_type_group_present in Group.
Qed.

Theorem close_type_groups_present_public initial source groups ids :
  close_type_groups initial source = Some (groups, ids) ->
  defined_types_present groups ids.
Proof.
  unfold close_type_groups.
  destruct (close_type_groups_from initial [] source) as [[registry types]|]
    eqn:Closed; [|discriminate].
  destruct (canonical_registry_super_orderedb registry); [|discriminate].
  intro E; inversion E; subst.
  apply close_type_groups_present in Closed; [exact Closed | constructor].
Qed.
