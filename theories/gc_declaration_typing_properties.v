(** Reflection for closed declaration checking. Abstract matching premises
    reuse the proved abstract hierarchy; declared matching uses the checked
    registry rank invariant, not an unbounded executable recursion. *)
From Wasm Require Import datatypes gc_types gc_type_context
  gc_declaration_typing gc_type_context_properties.
From Stdlib Require Import List Bool Lia NArith.
Import ListNotations.

Lemma declaration_list_matchesb_correct {A} (f : A -> A -> bool)
    (R : A -> A -> Prop)
    (Correct : forall a b, f a b = true <-> R a b) xs ys :
  declaration_list_matchesb f xs ys = true <-> Forall2 R xs ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; simpl.
  - split; intro E; constructor.
  - split; intro E; discriminate || inversion E.
  - split; intro E; discriminate || inversion E.
  - rewrite andb_true_iff, Correct, IH.
    split; [intros [Head Tail]; now constructor | intro E; now inversion E].
Qed.

Lemma canonical_registry_nodupb_correct groups :
  canonical_registry_nodupb groups = true <-> NoDup groups.
Proof.
  induction groups as [|head tail IH]; simpl.
  - split; intro E; constructor.
  - rewrite andb_true_iff, IH.
    assert (Absent : forallb (fun g => negb (canonical_group_eqb head g)) tail = true
      <-> ~ In head tail).
    { rewrite forallb_forall. split.
      - intros All Member. specialize (All head Member).
        rewrite (proj2 (canonical_group_eqb_correct head head) eq_refl) in All.
        discriminate.
      - intros Notin g Member. apply negb_true_iff.
        destruct (canonical_group_eqb head g) eqn:Same; [|reflexivity].
        apply canonical_group_eqb_correct in Same. subst g. contradiction. }
    rewrite Absent. split.
    + intros [Notin Unique]. now constructor.
    + intro Unique. now inversion Unique.
Qed.

Definition canonical_registry_valid groups : Prop :=
  NoDup groups /\
  canonical_registry_super_wf groups /\
  forall gi group mi st,
    nth_error groups gi = Some group ->
    nth_error group mi = Some st ->
    defined_declaration_valid groups (Def_type (N.of_nat gi) (N.of_nat mi)).

Lemma declaration_forallb_correct {A} (f : A -> bool) (P : A -> Prop)
    (Correct : forall a, f a = true <-> P a) xs :
  forallb f xs = true <-> Forall P xs.
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; intro E; constructor.
  - rewrite andb_true_iff, Correct, IH.
    split; [intros [Head Tail]; now constructor | intro E; now inversion E].
Qed.

Lemma abstract_projection_roundtrip h a :
  abstract_reference_of_legacy (Ref_type false h) = Some a ->
  h = shared_heap_of_abstract (art_heap a).
Proof.
  destruct h; simpl; intro E; try discriminate; inversion E; reflexivity.
Qed.

Lemma abstract_heap_matchesb_correct a b :
  abstract_heap_matchesb a b = true <-> shared_abstract_heap_matches a b.
Proof.
  split.
  - assert (GC : forall x y,
        abstract_reference_of_legacy (Ref_type false x) <> None ->
        abstract_reference_of_legacy (Ref_type false y) <> None ->
        abstract_heap_matchesb x y = true ->
        shared_abstract_heap_matches x y).
    { intros x y X Y.
      assert (E : abstract_heap_matchesb x y =
        match abstract_reference_of_legacy (Ref_type false x),
              abstract_reference_of_legacy (Ref_type false y) with
        | Some ar, Some br => abstract_heap_subtyping (art_heap ar) (art_heap br)
        | _, _ => false end).
      { destruct x, y; simpl in *; try contradiction; reflexivity. }
      rewrite E.
      destruct (abstract_reference_of_legacy (Ref_type false x)) as [ar|] eqn:AR;
        [|contradiction].
      destruct (abstract_reference_of_legacy (Ref_type false y)) as [br|] eqn:BR;
        [|contradiction].
      intro Matches.
      rewrite (abstract_projection_roundtrip _ _ AR),
        (abstract_projection_roundtrip _ _ BR).
      constructor. now apply abstract_heap_subtyping_sound. }
    destruct a, b; intro E; try discriminate;
      try (eapply GC; [discriminate | discriminate | exact E]); constructor.
  - intro E. destruct E; try reflexivity.
    assert (E : abstract_heap_matchesb (shared_heap_of_abstract a)
        (shared_heap_of_abstract b) = abstract_heap_subtyping a b)
      by (destruct a, b; reflexivity).
    rewrite E. now apply abstract_heap_subtyping_complete.
Qed.

Lemma bottom_matches_definedb_correct a b :
  bottom_matches_definedb a b = true <-> bottom_matches_defined a b.
Proof.
  split.
  - destruct a, b; simpl; intro E; try discriminate; constructor.
  - intro E. destruct E; reflexivity.
Qed.

Theorem closed_heap_matchesb_correct groups a b :
  canonical_registry_super_wf groups ->
  (closed_heap_matchesb groups a b = true <-> closed_heap_matches groups a b).
Proof.
  intro WF. split.
  - destruct a as [a|[i|a]], b as [b|[j|b]]; simpl; try discriminate.
    + intro E. constructor. now apply abstract_heap_matchesb_correct.
    + destruct (defined_heap_kind groups b) as [kind|] eqn:Kind; [|discriminate].
      intro E. apply chm_bottom_defined with (kind := kind); [exact Kind |].
      now apply bottom_matches_definedb_correct.
    + destruct (defined_heap_kind groups a) as [kind|] eqn:Kind; [|discriminate].
      intro E. apply chm_defined_abstract with (kind := kind); [exact Kind |].
      now apply abstract_heap_matchesb_correct.
    + intro E. apply defined_type_matches_sound in E.
      destruct E as [n Path]. now apply chm_defined with (n := n).
  - intro E. destruct E; simpl.
    + now apply abstract_heap_matchesb_correct.
    + now apply defined_type_matches_complete with (n := n).
    + rewrite H. now apply abstract_heap_matchesb_correct.
    + rewrite H. now apply bottom_matches_definedb_correct.
Qed.

Lemma closed_value_eqb_correct a b :
  closed_value_eqb a b = true <-> a = b.
Proof.
  unfold closed_value_eqb. destruct (closed_value_type_eq_dec a b);
    split; intros; congruence.
Qed.

Theorem closed_value_matchesb_correct groups a b :
  canonical_registry_super_wf groups ->
  (closed_value_matchesb groups a b = true <-> closed_value_matches groups a b).
Proof.
  intro WF. split.
  - destruct a as [a|a|na ha], b as [b|b|nb hb]; simpl; try discriminate.
    + destruct a, b; simpl; intro E; try discriminate; constructor.
    + destruct a, b. intro E. constructor.
    + rewrite andb_true_iff. intros [Nullable Heap].
      constructor.
      * destruct na, nb; simpl in Nullable; intuition discriminate.
      * now apply closed_heap_matchesb_correct.
  - intro E. destruct E; simpl.
    + destruct n; reflexivity.
    + destruct v; reflexivity.
    + apply andb_true_iff. split.
      * destruct na, nb; simpl; intuition congruence.
      * now apply closed_heap_matchesb_correct.
Qed.

Theorem closed_field_matchesb_correct groups a b :
  canonical_registry_super_wf groups ->
  (closed_field_matchesb groups a b = true <-> closed_field_matches groups a b).
Proof.
  intro WF. apply gc_types.field_matchesb_correct.
  - intros. now apply closed_value_matchesb_correct.
  - apply closed_value_eqb_correct.
Qed.

Theorem closed_composite_matchesb_correct groups a b :
  canonical_registry_super_wf groups ->
  (closed_composite_matchesb groups a b = true <-> closed_composite_matches groups a b).
Proof.
  intro WF. split.
  - destruct a as [[aa ar]|a|a], b as [[ba br]|b|b]; simpl; try discriminate.
    + rewrite andb_true_iff.
      rewrite !declaration_list_matchesb_correct
        with (R := closed_value_matches groups)
        by (intros; now apply closed_value_matchesb_correct).
      intros [Args Results]. now constructor.
    + rewrite declaration_list_matchesb_correct
        with (R := closed_field_matches groups)
        by (intros; now apply closed_field_matchesb_correct).
      intro Fields. now constructor.
    + rewrite closed_field_matchesb_correct by exact WF.
      intro Field. now constructor.
  - intro E. destruct E; simpl.
    + apply andb_true_iff. split;
        apply declaration_list_matchesb_correct with (R := closed_value_matches groups);
        try assumption; intros; now apply closed_value_matchesb_correct.
    + apply declaration_list_matchesb_correct with (R := closed_field_matches groups);
        try assumption; intros; now apply closed_field_matchesb_correct.
    + now apply closed_field_matchesb_correct.
Qed.

Theorem closed_value_validb_correct groups v :
  closed_value_validb groups v = true <-> closed_value_valid groups v.
Proof.
  split.
  - destruct v as [n|v|n [h|[i|t]]]; simpl; try discriminate.
    + intro E. constructor.
    + intro E. constructor.
    + destruct h; simpl; intro E; try discriminate;
        apply cvv_abstract; intros i Eq; discriminate.
    + unfold defined_type_validb.
      destruct (lookup_defined_type groups t) as [st|] eqn:Lookup; [|discriminate].
      intro E. now apply cvv_defined with (st := st).
  - intro E. destruct E; simpl; try reflexivity.
    + destruct h; simpl; try reflexivity. exfalso. now apply (H t).
    + unfold defined_type_validb. now rewrite H.
Qed.

Theorem closed_storage_validb_correct groups t :
  closed_storage_validb groups t = true <-> closed_storage_valid groups t.
Proof.
  split.
  - destruct t; simpl.
    + rewrite closed_value_validb_correct. intro E. now constructor.
    + intro E. constructor.
  - intro E. destruct E; simpl; [now apply closed_value_validb_correct | reflexivity].
Qed.

Theorem closed_composite_validb_correct groups c :
  closed_composite_validb groups c = true <-> closed_composite_valid groups c.
Proof.
  split.
  - destruct c as [[args results]|fields|f]; simpl.
    + rewrite andb_true_iff, !declaration_forallb_correct
        with (P := closed_value_valid groups) by apply closed_value_validb_correct.
      intros [Args Results]. now constructor.
    + rewrite declaration_forallb_correct
        with (P := fun f => closed_storage_valid groups (field_storage f))
        by (intros; apply closed_storage_validb_correct).
      intro Fields. now constructor.
    + rewrite closed_storage_validb_correct. intro Field. now constructor.
  - intro E. destruct E; simpl.
    + apply andb_true_iff. split;
        apply declaration_forallb_correct with (P := closed_value_valid groups);
        try assumption; apply closed_value_validb_correct.
    + apply declaration_forallb_correct
        with (P := fun f => closed_storage_valid groups (field_storage f));
        try assumption; intros; apply closed_storage_validb_correct.
    + now apply closed_storage_validb_correct.
Qed.

Theorem closed_parent_validb_correct groups child u :
  canonical_registry_super_wf groups ->
  (closed_parent_validb groups child u = true <-> closed_parent_valid groups child u).
Proof.
  intro WF. split.
  - destruct u as [i|t]; simpl; [discriminate |].
    destruct (expand_defined_type groups t) as [parent|] eqn:Expand; [|discriminate].
    rewrite andb_true_iff, negb_true_iff, closed_composite_matchesb_correct by exact WF.
    intros [Final Matches]. now apply cpv_parent with (parent := parent).
  - intro E. destruct E. simpl. rewrite H.
    apply andb_true_iff. split; [now rewrite H0 |].
    now apply closed_composite_matchesb_correct.
Qed.

Theorem defined_declaration_validb_correct groups t :
  canonical_registry_super_wf groups ->
  (defined_declaration_validb groups t = true <-> defined_declaration_valid groups t).
Proof.
  intro WF. unfold defined_declaration_validb, defined_declaration_valid.
  destruct (expand_defined_type groups t) as [st|] eqn:Expand.
  - rewrite !andb_true_iff, PeanoNat.Nat.leb_le, closed_composite_validb_correct.
    rewrite declaration_forallb_correct
      with (P := closed_parent_valid groups (subtype_composite st))
      by (intros; now apply closed_parent_validb_correct).
    split.
    + intros [[Count Valid] Parents]. exists st. auto.
    + intros [other [E [Count [Valid Parents]]]]. inversion E; subst. auto.
  - split; [discriminate | intros [st [E _]]; discriminate].
Qed.

Theorem canonical_registry_validb_sound groups :
  canonical_registry_validb groups = true -> canonical_registry_valid groups.
Proof.
  unfold canonical_registry_validb.
  rewrite !andb_true_iff.
  intros [[Unique Ordered] Checked].
  pose proof (canonical_registry_super_orderedb_sound groups Ordered) as WF.
  split; [now apply canonical_registry_nodupb_correct |].
  split; [exact WF |].
  intros gi group mi st Group Member.
  apply forallb_forall with (x := gi) in Checked.
  2: { apply in_seq. split; [lia | now apply nth_error_index_bound in Group]. }
  rewrite Group in Checked.
  apply forallb_forall with (x := mi) in Checked.
  2: { apply in_seq. split; [lia | now apply nth_error_index_bound in Member]. }
  now apply defined_declaration_validb_correct.
Qed.

Theorem close_and_validate_type_groups_sound initial source groups ids :
  close_and_validate_type_groups initial source = Some (groups, ids) ->
  canonical_registry_valid groups /\
  close_type_groups initial source = Some (groups, ids).
Proof.
  unfold close_and_validate_type_groups.
  destruct (close_type_groups initial source) as [[registry names]|] eqn:Closed;
    [|discriminate].
  destruct (canonical_registry_validb registry) eqn:Valid; [|discriminate].
  intro E. inversion E; subst. split; [now apply canonical_registry_validb_sound | reflexivity].
Qed.

Lemma canonical_registry_super_orderedb_complete groups :
  canonical_registry_super_wf groups ->
  canonical_registry_super_orderedb groups = true.
Proof.
  intro WF. unfold canonical_registry_super_orderedb.
  apply forallb_forall. intros gi Gi. apply in_seq in Gi.
  destruct (nth_error groups gi) as [group|] eqn:Group.
  2: { apply nth_error_None in Group. lia. }
  apply forallb_forall. intros mi Mi. apply in_seq in Mi.
  destruct (nth_error group mi) as [st|] eqn:Member.
  2: { apply nth_error_None in Member. lia. }
  apply forallb_forall. intros u Parent.
  set (self := Def_type (N.of_nat gi) (N.of_nat mi)).
  assert (Lookup : lookup_defined_type groups self = Some st).
  { unfold lookup_defined_type, self. simpl. now rewrite !Nat2N.id, Group. }
  assert (Step : declared_type_step groups self (resolve_type_use self u)).
  { exists (expand_subtype self st). split.
    - unfold expand_defined_type. now rewrite Lookup.
    - simpl. apply in_map_iff. exists u. auto. }
  destruct (WF _ _ Step) as [[raw Valid] Smaller].
  apply andb_true_iff. split.
  - unfold defined_type_validb. now rewrite Valid.
  - now apply PeanoNat.Nat.ltb_lt.
Qed.

Theorem canonical_registry_validb_correct groups :
  canonical_registry_validb groups = true <-> canonical_registry_valid groups.
Proof.
  split; [apply canonical_registry_validb_sound |].
  intros [Unique [WF Declarations]].
  unfold canonical_registry_validb. apply andb_true_iff. split.
  - apply andb_true_iff. split.
    + now apply canonical_registry_nodupb_correct.
    + now apply canonical_registry_super_orderedb_complete.
  - apply forallb_forall. intros gi Gi. apply in_seq in Gi.
    destruct (nth_error groups gi) as [group|] eqn:Group.
    2: { apply nth_error_None in Group. lia. }
    apply forallb_forall. intros mi Mi. apply in_seq in Mi.
    destruct (nth_error group mi) as [st|] eqn:Member.
    2: { apply nth_error_None in Member. lia. }
    apply defined_declaration_validb_correct; [exact WF |].
    now apply (Declarations gi group mi st).
Qed.

Theorem close_and_validate_type_groups_correct initial source groups ids :
  close_and_validate_type_groups initial source = Some (groups, ids) <->
  close_type_groups initial source = Some (groups, ids) /\
  canonical_registry_valid groups.
Proof.
  split.
  - intro E. apply close_and_validate_type_groups_sound in E. tauto.
  - intros [Closed Valid]. unfold close_and_validate_type_groups.
    rewrite Closed, (proj2 (canonical_registry_validb_correct groups) Valid).
    reflexivity.
Qed.
