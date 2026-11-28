(** Correctness properties for canonical recursive-group closing and lookup.
    Closing is not structural declaration validation. In particular the
    bounded path characterization below states exactly what the executable
    matcher proves; its full well-formed-registry completeness is separate. *)
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
