(** Function expansion along declared subtype paths, not just equal IDs. *)
From Wasm Require Import datatypes gc_types gc_type_context gc_type_context_properties
  gc_declaration_typing gc_declaration_typing_properties typing.
From Stdlib Require Import List Bool NArith Lia.
Import ListNotations.

Lemma registry_valid_declaration groups id raw :
  canonical_registry_valid groups ->
  lookup_defined_type groups id = Some raw ->
  defined_declaration_valid groups id.
Proof.
  intros [_ [_ Valid]] Lookup. unfold lookup_defined_type in Lookup.
  destruct (nth_error groups (N.to_nat (defined_group id))) as [group|] eqn:Group;
    [|discriminate].
  specialize (Valid _ _ _ _ Group Lookup).
  destruct id as [gi mi]; simpl in *. now rewrite !N2Nat.id in Valid.
Qed.

Lemma registry_valid_expanded_declaration groups id st :
  canonical_registry_valid groups ->
  expand_defined_type groups id = Some st ->
  closed_composite_valid groups st.(subtype_composite) /\
  Forall (closed_parent_valid groups st.(subtype_composite)) st.(subtype_supers).
Proof.
  intros Valid Expanded. unfold expand_defined_type in Expanded.
  destruct (lookup_defined_type groups id) as [raw|] eqn:Lookup; [|discriminate].
  destruct (registry_valid_declaration _ _ _ Valid Lookup)
    as [other [Other [_ [Composite Parents]]]].
  unfold expand_defined_type in Other. rewrite Lookup in Other.
  rewrite Other in Expanded. inversion Expanded; subst. auto.
Qed.

Lemma registry_valid_parent_composites groups a b :
  canonical_registry_valid groups ->
  declared_type_step groups a b ->
  exists child parent,
    expand_defined_type groups a = Some child /\
    expand_defined_type groups b = Some parent /\
    closed_composite_matches groups child.(subtype_composite) parent.(subtype_composite).
Proof.
  intros Valid [child [Expanded Member]].
  destruct (registry_valid_expanded_declaration _ _ _ Valid Expanded) as [_ Parents].
  rewrite Forall_forall in Parents.
  specialize (Parents (CT_def b) Member).
  inversion Parents; subst. exists child, parent. auto.
Qed.

Definition composite_heap_kind (c : composite_type closed_value_type closed_function_type) :=
  match c with Comp_func _ => HT_func | Comp_struct _ => HT_struct | Comp_array _ => HT_array end.

Lemma composite_matches_same_kind groups a b :
  closed_composite_matches groups a b -> composite_heap_kind a = composite_heap_kind b.
Proof. intro Match. destruct Match; reflexivity. Qed.

Lemma declared_type_path_heap_kind groups n a b :
  canonical_registry_valid groups ->
  declared_type_path groups n a b ->
  defined_heap_kind groups a = defined_heap_kind groups b.
Proof.
  intros Valid Path. induction Path as [a|n a b c Step Path IH]; [reflexivity |].
  destruct (registry_valid_parent_composites _ _ _ Valid Step)
    as [child [parent [Child [Parent Match]]]].
  unfold defined_heap_kind at 1.
  rewrite Child.
  assert (Kind : defined_heap_kind groups b = Some (composite_heap_kind parent.(subtype_composite))).
  { unfold defined_heap_kind. now rewrite Parent. }
  rewrite <-IH, Kind.
  f_equal. exact (composite_matches_same_kind groups _ _ Match).
Qed.

Lemma abstract_heap_matchesb_trans a b c :
  abstract_heap_matchesb a b = true ->
  abstract_heap_matchesb b c = true ->
  abstract_heap_matchesb a c = true.
Proof. destruct a, b, c; simpl; intros; congruence. Qed.

Lemma abstract_to_bottom_defined a b kind :
  abstract_heap_matchesb a b = true ->
  bottom_matches_definedb b kind = true ->
  bottom_matches_definedb a kind = true.
Proof. destruct a, b, kind; simpl; intros; congruence. Qed.

Lemma bottom_defined_to_abstract a kind b :
  bottom_matches_definedb a kind = true ->
  abstract_heap_matchesb kind b = true ->
  abstract_heap_matchesb a b = true.
Proof. destruct a, kind, b; simpl; intros; congruence. Qed.

Lemma defined_heap_kind_range groups id kind :
  defined_heap_kind groups id = Some kind ->
  kind = HT_func \/ kind = HT_struct \/ kind = HT_array.
Proof.
  unfold defined_heap_kind.
  destruct (expand_defined_type groups id) as [st|]; [|discriminate].
  destruct (subtype_composite st); intro E; inversion E; auto.
Qed.

Lemma defined_kind_cannot_match_bottom kind bottom target :
  (kind = HT_func \/ kind = HT_struct \/ kind = HT_array) ->
  abstract_heap_matchesb kind bottom = true ->
  bottom_matches_definedb bottom target = true -> False.
Proof.
  intros [-> | [-> | ->]]; destruct bottom, target; simpl; intros; congruence.
Qed.

Lemma closed_heap_matches_trans groups a b c :
  canonical_registry_valid groups ->
  closed_heap_matches groups a b ->
  closed_heap_matches groups b c ->
  closed_heap_matches groups a c.
Proof.
  intros Valid First Last.
  destruct First as [a b First|a b n Path|a b kind Kind First|a b kind Kind First].
  - inversion Last as [x y LastAbs | x y m LastPath |
      x y k LastKind LastAbs | x y k LastKind LastBottom]; subst.
    + constructor. apply abstract_heap_matchesb_correct in First.
      apply abstract_heap_matchesb_correct in LastAbs.
      apply abstract_heap_matchesb_correct. now apply (abstract_heap_matchesb_trans _ b).
    + apply chm_bottom_defined with (kind := k); [assumption |].
      apply abstract_heap_matchesb_correct in First.
      apply bottom_matches_definedb_correct in LastBottom.
      apply bottom_matches_definedb_correct. now apply (abstract_to_bottom_defined _ b).
  - inversion Last as [x y LastAbs | x y m LastPath |
      x y k LastKind LastAbs | x y k LastKind LastBottom]; subst.
    + apply chm_defined with (n := n + m).
      now apply declared_type_path_append with (b := b).
    + apply chm_defined_abstract with (kind := k); [|assumption].
      now rewrite (declared_type_path_heap_kind _ _ _ _ Valid Path).
  - inversion Last as [x y LastAbs | x y m LastPath |
      x y k LastKind LastAbs | x y k LastKind LastBottom]; subst.
    + apply chm_defined_abstract with (kind := kind); [exact Kind |].
      apply abstract_heap_matchesb_correct in First, LastAbs.
      apply abstract_heap_matchesb_correct. now apply (abstract_heap_matchesb_trans _ b).
    + exfalso. apply abstract_heap_matchesb_correct in First.
      apply bottom_matches_definedb_correct in LastBottom.
      exact (defined_kind_cannot_match_bottom _ _ _
        (defined_heap_kind_range _ _ _ Kind) First LastBottom).
  - inversion Last as [x y LastAbs | x y m LastPath |
      x y k LastKind LastAbs | x y k LastKind LastBottom]; subst.
    + apply chm_bottom_defined with (kind := kind).
      * now rewrite <-(declared_type_path_heap_kind _ _ _ _ Valid LastPath).
      * exact First.
    + constructor. apply bottom_matches_definedb_correct in First.
      apply abstract_heap_matchesb_correct in LastAbs.
      rewrite Kind in LastKind. inversion LastKind; subst k.
      apply abstract_heap_matchesb_correct. now apply (bottom_defined_to_abstract _ kind).
Qed.

Lemma closed_value_matches_trans groups a b c :
  canonical_registry_valid groups ->
  closed_value_matches groups a b ->
  closed_value_matches groups b c ->
  closed_value_matches groups a c.
Proof.
  intros Valid First Last. destruct First; inversion Last; subst; try constructor.
  - destruct na, nb, nb0; simpl in *; intuition congruence.
  - eapply closed_heap_matches_trans; eassumption.
Qed.

Lemma closed_value_matches_refl_valid groups value :
  closed_value_valid groups value -> closed_value_matches groups value value.
Proof.
  intro Valid. destruct Valid; constructor.
  - destruct n; auto.
  - constructor. apply abstract_heap_matchesb_correct.
    destruct h; simpl; try reflexivity. exfalso. now apply (H t).
  - destruct n; auto.
  - apply chm_defined with (n := 0). constructor.
Qed.

Lemma declared_path_validity groups n actual expected :
  canonical_registry_super_wf groups ->
  declared_type_path groups n actual expected ->
  (defined_type_validb groups actual = true <->
   defined_type_validb groups expected = true).
Proof.
  intros WF Path. induction Path as [id|n a parent b Step Path IH]; [tauto|].
  destruct (declared_type_step_source_valid _ _ _ Step) as [raw Source].
  destruct (WF _ _ Step) as [[parent_raw Parent] _].
  assert (AV : defined_type_validb groups a = true)
    by (unfold defined_type_validb; now rewrite Source).
  assert (PV : defined_type_validb groups parent = true)
    by (unfold defined_type_validb; now rewrite Parent).
  pose proof (proj1 IH PV) as BV. tauto.
Qed.

Lemma defined_kind_validity groups id kind :
  defined_heap_kind groups id = Some kind ->
  defined_type_validb groups id = true.
Proof.
  unfold defined_heap_kind, expand_defined_type, defined_type_validb.
  destruct (lookup_defined_type groups id); [reflexivity|discriminate].
Qed.

Lemma abstract_heap_matching_validity actual expected :
  abstract_heap_matchesb actual expected = true ->
  abstract_heap_validb actual = true /\ abstract_heap_validb expected = true.
Proof. destruct actual, expected; simpl; intros; try discriminate; auto. Qed.

Lemma bottom_matching_validity actual kind :
  bottom_matches_definedb actual kind = true ->
  abstract_heap_validb actual = true.
Proof. destruct actual, kind; simpl; intros; congruence. Qed.

Lemma closed_value_matchesb_validity groups actual expected :
  canonical_registry_super_wf groups ->
  closed_value_matchesb groups actual expected = true ->
  (closed_value_validb groups actual = true <-> closed_value_validb groups expected = true).
Proof.
  intro WF.
  destruct actual as [an|av|na ah], expected as [bn|bv|nb bh];
    simpl; intro Match; try tauto; try discriminate.
  apply andb_true_iff in Match as [_ Match].
  destruct ah as [ha|[ra|da]], bh as [hb|[rb|db]]; simpl in *; try discriminate.
  - now destruct (abstract_heap_matching_validity _ _ Match).
  - destruct (defined_heap_kind groups db) as [kind|] eqn:Kind; [|discriminate].
    pose proof (defined_kind_validity _ _ _ Kind).
    pose proof (bottom_matching_validity _ _ Match). tauto.
  - destruct (defined_heap_kind groups da) as [kind|] eqn:Kind; [|discriminate].
    pose proof (defined_kind_validity _ _ _ Kind).
    destruct (abstract_heap_matching_validity _ _ Match). tauto.
  - apply defined_type_matches_sound in Match. destruct Match as [n Path].
    exact (declared_path_validity _ _ _ _ WF Path).
Qed.

Lemma closed_list_matches_validity groups actual expected :
  canonical_registry_super_wf groups ->
  declaration_list_matchesb (closed_value_matchesb groups) actual expected = true ->
  (Forall (closed_value_valid groups) actual \/ Forall (closed_value_valid groups) expected) ->
  Forall2 (fun a b => closed_value_validb groups a = true /\
    closed_value_validb groups b = true /\ closed_value_matchesb groups a b = true)
    actual expected.
Proof.
  intros WF. revert expected.
  induction actual as [|a actual IH]; destruct expected as [|b expected];
    simpl; try discriminate.
  - intros; constructor.
  - rewrite andb_true_iff. intros [Head Tail] Valid.
    assert (AV : closed_value_validb groups a = true).
    { destruct Valid as [Left|Right].
      - inversion Left; subst. now apply closed_value_validb_correct.
      - inversion Right; subst.
        apply (proj2 (closed_value_matchesb_validity _ _ _ WF Head)).
        now apply closed_value_validb_correct. }
    constructor.
    + split; [exact AV|]. split; [|exact Head].
      exact (proj1 (closed_value_matchesb_validity _ _ _ WF Head) AV).
    + apply IH; [exact Tail|].
      destruct Valid as [Left|Right]; [left|right]; inversion Left || inversion Right; auto.
Qed.

Lemma source_results_matchb_from_closed groups actual_names expected_names
    actual_source expected_source actual expected :
  those0 (List.map (close_value_type actual_names 0) actual_source) = Some actual ->
  those0 (List.map (close_value_type expected_names 0) expected_source) = Some expected ->
  Forall2 (fun a b => closed_value_validb groups a = true /\
    closed_value_validb groups b = true /\ closed_value_matchesb groups a b = true)
    actual expected ->
  source_results_matchb groups actual_names expected_names actual_source expected_source = true.
Proof.
  revert expected_source actual expected.
  induction actual_source as [|a actual_source IH]; intros expected_source actual expected A E Related.
  - simpl in A. inversion A; subst actual. inversion Related; subst expected.
    destruct expected_source as [|b expected_source]; [reflexivity|].
    cbn [List.map those0] in E.
    destruct (close_value_type expected_names 0 b); [|discriminate].
    destruct (those0 (List.map (close_value_type expected_names 0) expected_source));
      discriminate.
  - destruct expected_source as [|b expected_source].
    + simpl in E. inversion E; subst expected. inversion Related; subst actual.
      cbn [List.map those0] in A.
      destruct (close_value_type actual_names 0 a); [|discriminate].
      destruct (those0 (List.map (close_value_type actual_names 0) actual_source));
        discriminate.
    + cbn [List.map those0] in A, E.
      destruct (close_value_type actual_names 0 a) as [ca|] eqn:CA; [|discriminate].
      destruct (those0 (List.map (close_value_type actual_names 0) actual_source))
        as [cas|] eqn:CAS; [|discriminate].
      destruct (close_value_type expected_names 0 b) as [cb|] eqn:CB; [|discriminate].
      destruct (those0 (List.map (close_value_type expected_names 0) expected_source))
        as [cbs|] eqn:CBS; [|discriminate].
      inversion A; inversion E; subst actual expected.
      inversion Related as [|x y xs ys [AV [EV Match]] Rest]; subst.
      cbn [source_results_matchb declaration_list_matchesb].
      unfold source_value_matchesb at 1. rewrite CA, CB.
      rewrite AV, EV, Match. simpl.
      exact (IH _ _ _ eq_refl CBS Rest).
Qed.

Lemma expanded_function_valid groups id args results :
  canonical_registry_valid groups ->
  expand_function_type groups id = Some (Closed_ft args results) ->
  Forall (closed_value_valid groups) args /\ Forall (closed_value_valid groups) results.
Proof.
  intros Valid Expanded. unfold expand_function_type in Expanded.
  destruct (expand_defined_type groups id) as [declaration|] eqn:Declaration;
    [|discriminate].
  destruct (registry_valid_expanded_declaration _ _ _ Valid Declaration) as [Composite _].
  destruct (subtype_composite declaration) as [[aa ar]|fields|field]; try discriminate.
  inversion Expanded; subst aa ar. inversion Composite; subst. auto.
Qed.

Lemma Forall2_transitive {A} (R : A -> A -> Prop) :
  (forall a b c, R a b -> R b c -> R a c) ->
  forall xs ys zs, Forall2 R xs ys -> Forall2 R ys zs -> Forall2 R xs zs.
Proof.
  intros Trans xs ys zs First. revert zs.
  induction First; intros zs Last; inversion Last; subst; constructor; eauto.
Qed.

Lemma declared_function_path_variance groups n actual expected args results :
  canonical_registry_valid groups ->
  declared_type_path groups n actual expected ->
  expand_function_type groups expected = Some (Closed_ft args results) ->
  exists actual_args actual_results,
    expand_function_type groups actual = Some (Closed_ft actual_args actual_results) /\
    Forall2 (closed_value_matches groups) args actual_args /\
    Forall2 (closed_value_matches groups) actual_results results.
Proof.
  intros Valid Path. revert args results.
  induction Path as [actual|n actual parent expected Step Path IH]; intros args results Expanded.
  - exists args, results. split; [exact Expanded |].
    unfold expand_function_type in Expanded.
    destruct (expand_defined_type groups actual) as [st|] eqn:Declaration; [|discriminate].
    destruct (registry_valid_expanded_declaration _ _ _ Valid Declaration) as [Composite _].
    destruct (subtype_composite st) as [[parameters returns]|fields|field] eqn:Kind;
      [|discriminate | discriminate].
    inversion Expanded; subst parameters returns. inversion Composite; subst.
    assert (Diag : forall xs, Forall (closed_value_valid groups) xs ->
        Forall2 (closed_value_matches groups) xs xs).
    { intros xs Typed. induction Typed; constructor; auto.
      now apply closed_value_matches_refl_valid. }
    split; apply Diag; assumption.
  - destruct (IH _ _ Expanded)
      as [parent_args [parent_results [ParentExpansion [Arguments Results]]]].
    destruct (registry_valid_parent_composites _ _ _ Valid Step)
      as [child [parent_type [Child [Parent Match]]]].
    unfold expand_function_type in ParentExpansion. rewrite Parent in ParentExpansion.
    destruct (subtype_composite parent_type) as [[pa pr]|fields|field] eqn:ParentKind;
      [|discriminate | discriminate].
    inversion ParentExpansion; subst pa pr.
    destruct (subtype_composite child) as [[aa ar]|fields|field] eqn:ChildKind;
      inversion Match; subst.
    exists aa, ar. split.
    + unfold expand_function_type. now rewrite Child, ChildKind.
    + split; eapply Forall2_transitive;
        try eassumption; intros x y z X Y;
        eapply closed_value_matches_trans; eassumption.
Qed.

Theorem defined_function_matches_variance groups actual expected args results :
  canonical_registry_valid groups ->
  defined_type_matches groups actual expected = true ->
  expand_function_type groups expected = Some (Closed_ft args results) ->
  exists actual_args actual_results,
    expand_function_type groups actual = Some (Closed_ft actual_args actual_results) /\
    declaration_list_matchesb (closed_value_matchesb groups) args actual_args = true /\
    declaration_list_matchesb (closed_value_matchesb groups) actual_results results = true.
Proof.
  intros Valid Matches Expected.
  apply defined_type_matches_sound in Matches. destruct Matches as [n Path].
  destruct (declared_function_path_variance _ _ _ _ _ _ Valid Path Expected)
    as [actual_args [actual_results [Expanded [Arguments Results]]]].
  exists actual_args, actual_results. split; [exact Expanded |].
  split; apply declaration_list_matchesb_correct with (R := closed_value_matches groups);
    try assumption; intros a b;
    apply closed_value_matchesb_correct; exact (proj1 (proj2 Valid)).
Qed.

Section Runtime.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Lemma closed_value_typing_subsumption s value actual expected :
  canonical_registry_valid s.(s_types) ->
  closed_value_typing s value actual = true ->
  closed_value_validb s.(s_types) expected = true ->
  closed_value_matchesb s.(s_types) actual expected = true ->
  closed_value_typing s value expected = true.
Proof.
  intros Valid Typed Expected Matches.
  unfold closed_value_typing in *.
  destruct (typeof_closed_value s value) as [principal|]; [|discriminate].
  rewrite !andb_true_iff in *.
  destruct Typed as [[Principal Actual] Typed].
  split; [now split |].
  pose proof (proj1 (proj2 Valid)) as WF.
  apply (proj2 (closed_value_matchesb_correct _ _ _ WF)).
  eapply closed_value_matches_trans with (b := actual); [exact Valid | |].
  - exact (proj1 (closed_value_matchesb_correct _ _ _ WF) Typed).
  - exact (proj1 (closed_value_matchesb_correct _ _ _ WF) Matches).
Qed.

Theorem closed_function_operand_inversion s address expected :
  closed_value_typing s (VAL_ref (VAL_ref_func address))
    (CV_ref true (CH_defined (CT_def expected))) = true ->
  exists actual,
    lookup_func_defined_type s address = Some actual /\
    defined_type_matches s.(s_types) actual expected = true.
Proof.
  unfold closed_value_typing, typeof_closed_value, typeof_closed_ref.
  destruct (lookup_func_defined_type s address) as [actual|] eqn:Actual; [|discriminate].
  simpl. rewrite !andb_true_iff. intros [[_ _] Matches].
  exists actual. auto.
Qed.

End Runtime.

(** Three distinct identities: both parameter contravariance and result
    covariance must compose across two edges, not collapse to ID equality. *)
Module StrictFunctionPathRegression.
Definition ref (h : heap_type) := CV_ref true (CH_abstract h).
Definition registry : canonical_registry :=
  [[Sub_type false [] (Comp_func (Closed_ft [ref HT_i31] [ref HT_any]))];
   [Sub_type false [CT_def (Def_type 0 0)]
     (Comp_func (Closed_ft [ref HT_eq] [ref HT_eq]))];
   [Sub_type true [CT_def (Def_type 1 0)]
     (Comp_func (Closed_ft [ref HT_any] [ref HT_i31]))]].

Example valid_registry : canonical_registry_valid registry.
Proof. apply canonical_registry_validb_sound. vm_compute. reflexivity. Qed.

Example strict_path : defined_type_matches registry (Def_type 2 0) (Def_type 0 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example strict_path_not_equality : Def_type 2 0 <> Def_type 0 0.
Proof. discriminate. Qed.

Example strict_path_variance :
  exists aa ar,
    expand_function_type registry (Def_type 2 0) = Some (Closed_ft aa ar) /\
    declaration_list_matchesb (closed_value_matchesb registry) [ref HT_i31] aa = true /\
    declaration_list_matchesb (closed_value_matchesb registry) ar [ref HT_any] = true.
Proof.
  eapply defined_function_matches_variance.
  - exact valid_registry.
  - exact strict_path.
  - reflexivity.
Qed.

Example reverse_path_rejected :
  defined_type_matches registry (Def_type 0 0) (Def_type 2 0) = false.
Proof. vm_compute. reflexivity. Qed.
End StrictFunctionPathRegression.

(** A source-indexed administrative stack cannot in general express the
    intermediate parameter type after a tail call removes a defining frame.
    The closed operand/parameter interval is inhabited, but its canonical ID
    need not occur in the remaining caller's source name map. *)
Module TailSourceContextRegression.
Definition parameter_id := Def_type 0 0.
Definition caller_id := Def_type 1 0.
Definition operand := CV_ref false (CH_defined (CT_def parameter_id)).
Definition parameter := CV_ref true (CH_defined (CT_def parameter_id)).
Definition registry : canonical_registry :=
  [[Sub_type true [] (Comp_func (Closed_ft [] []))];
   [Sub_type true [] (Comp_func (Closed_ft [] [CV_num T_i32]))];
   [Sub_type true [] (Comp_func (Closed_ft [parameter] [CV_num T_i32]))]].
Definition remaining_names := [caller_id].
Definition source_middle (source : value_type) : bool :=
  match close_value_type remaining_names 0 source with
  | Some middle =>
      closed_value_matchesb registry operand middle &&
      closed_value_matchesb registry middle parameter
  | None => false
  end.

Example registry_valid : canonical_registry_valid registry.
Proof. apply canonical_registry_validb_sound. vm_compute. reflexivity. Qed.

Example closed_middle_exists :
  closed_value_matchesb registry operand operand = true /\
  closed_value_matchesb registry operand parameter = true.
Proof. split; reflexivity. Qed.

Theorem no_source_middle source : source_middle source = false.
Proof.
  destruct source as [number|vector|[nullable heap]|]; try reflexivity.
  destruct nullable, heap; try reflexivity;
    destruct t as [|positive]; try reflexivity;
    destruct positive; reflexivity.
Qed.
End TailSourceContextRegression.
