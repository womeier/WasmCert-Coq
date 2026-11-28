(** Function expansion along declared subtype paths, not just equal IDs. *)
From Wasm Require Import datatypes gc_types gc_type_context gc_type_context_properties
  gc_declaration_typing gc_declaration_typing_properties typing
  gc_closed_runtime_properties.
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
