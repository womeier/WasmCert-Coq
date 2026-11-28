(** Renaming canonical group addresses. Member indices and recursive binders
    are preserved. Destination registries need not order field references. *)
From Wasm Require Import datatypes gc_types gc_type_context gc_type_context_properties
  gc_declaration_typing gc_declaration_typing_properties.
From Stdlib Require Import List NArith Arith Bool Lia.
Import ListNotations.

Definition rename_defined_type (rho : N -> N) (t : defined_type) : defined_type :=
  Def_type (rho t.(defined_group)) t.(defined_member).

Definition rename_type_use rho (u : closed_type_use) : closed_type_use :=
  match u with CT_rec i => CT_rec i | CT_def t => CT_def (rename_defined_type rho t) end.

Definition rename_heap_type rho (h : closed_heap_type) : closed_heap_type :=
  match h with CH_abstract h => CH_abstract h | CH_defined u => CH_defined (rename_type_use rho u) end.

Definition rename_value_type rho (v : closed_value_type) : closed_value_type :=
  match v with
  | CV_num n => CV_num n
  | CV_vec v => CV_vec v
  | CV_ref n h => CV_ref n (rename_heap_type rho h)
  end.

Definition rename_storage_type rho (s : storage_type closed_value_type) :=
  match s with
  | ST_value v => ST_value (rename_value_type rho v)
  | ST_packed p => ST_packed p
  end.

Definition rename_field_type rho (f : field_type closed_value_type) :=
  {| field_mutability := f.(field_mutability);
     field_storage := rename_storage_type rho f.(field_storage) |}.

Definition rename_composite_type rho
    (c : composite_type closed_value_type closed_function_type) :
    composite_type closed_value_type closed_function_type :=
  match c with
  | Comp_func (Closed_ft args results) =>
      Comp_func (Closed_ft (map (rename_value_type rho) args) (map (rename_value_type rho) results))
  | Comp_struct fs => Comp_struct (map (rename_field_type rho) fs)
  | Comp_array f => Comp_array (rename_field_type rho f)
  end.

Definition rename_subtype rho (s : closed_subtype) : closed_subtype :=
  Sub_type s.(subtype_final) (map (rename_type_use rho) s.(subtype_supers))
    (rename_composite_type rho s.(subtype_composite)).

Definition rename_group rho (group : canonical_group) : canonical_group :=
  map (rename_subtype rho) group.

Definition group_renaming_injective (rho : N -> N) :=
  forall a b, rho a = rho b -> a = b.

Lemma rename_defined_type_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_defined_type rho a = rename_defined_type rho b -> a = b.
Proof.
  intros Injective [a i] [b j] E. inversion E. f_equal; auto.
Qed.

Lemma rename_type_use_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_type_use rho a = rename_type_use rho b -> a = b.
Proof.
  intros Injective [a|a] [b|b] E; simpl in E; try discriminate.
  - now injection E as ->.
  - apply (f_equal (fun u => match u with CT_def d => d | _ => Def_type 0 0 end)) in E.
    f_equal. now apply (rename_defined_type_injective rho Injective).
Qed.

Lemma rename_heap_type_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_heap_type rho a = rename_heap_type rho b -> a = b.
Proof.
  intros Injective [a|a] [b|b] E; simpl in E; try discriminate.
  - now injection E as ->.
  - apply (f_equal (fun h => match h with CH_defined u => u | _ => CT_rec 0 end)) in E.
    f_equal. now apply (rename_type_use_injective rho Injective).
Qed.

Lemma rename_value_type_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_value_type rho a = rename_value_type rho b -> a = b.
Proof.
  intros Injective [a|a|na a] [b|b|nb b] E; simpl in E; try discriminate;
    inversion E; subst; try reflexivity.
  f_equal. now apply (rename_heap_type_injective rho Injective).
Qed.

Lemma map_injective_on {A B} (f : A -> B) :
  (forall a b, f a = f b -> a = b) ->
  forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
  intros Injective xs. induction xs as [|x xs IH]; intros [|y ys] E; simpl in E;
    try discriminate; [reflexivity |].
  injection E as Head Tail. f_equal; [now apply Injective | now apply IH].
Qed.

Lemma rename_storage_type_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_storage_type rho a = rename_storage_type rho b -> a = b.
Proof.
  intros Injective [a|a] [b|b] E; simpl in E; try discriminate;
    inversion E; subst; try reflexivity.
  f_equal. now apply (rename_value_type_injective rho Injective).
Qed.

Lemma rename_field_type_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_field_type rho a = rename_field_type rho b -> a = b.
Proof.
  intros Injective [ma a] [mb b] E. inversion E; subst.
  f_equal. now apply (rename_storage_type_injective rho Injective).
Qed.

Lemma rename_composite_type_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_composite_type rho a = rename_composite_type rho b -> a = b.
Proof.
  intros Injective [[aa ar]|a|a] [[ba br]|b|b] E; simpl in E; try discriminate.
  - injection E as Args Results.
    apply (map_injective_on _ (rename_value_type_injective rho Injective)) in Args.
    apply (map_injective_on _ (rename_value_type_injective rho Injective)) in Results.
    now subst.
  - injection E as Fields. f_equal.
    eapply map_injective_on; [apply rename_field_type_injective; exact Injective | exact Fields].
  - apply (f_equal (fun c => match c with Comp_array f => f | _ => a end)) in E.
    f_equal. now apply (rename_field_type_injective rho Injective).
Qed.

Lemma rename_subtype_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_subtype rho a = rename_subtype rho b -> a = b.
Proof.
  intros Injective [fa sa ca] [fb sb cb] E.
  injection E as Final Supers Composite. simpl in *. subst fb.
  f_equal.
  - eapply map_injective_on; [apply rename_type_use_injective; exact Injective | exact Supers].
  - now apply (rename_composite_type_injective rho Injective).
Qed.

Lemma rename_group_injective rho :
  group_renaming_injective rho ->
  forall a b, rename_group rho a = rename_group rho b -> a = b.
Proof.
  intros Injective. apply map_injective_on. now apply rename_subtype_injective.
Qed.

(** Extend a finite embedding by a transposition in its destination. Unlike a
    default-valued finite map this remains injective on *all* group addresses. *)
Definition swap_groups a b (x : N) : N :=
  if N.eq_dec x a then b else if N.eq_dec x b then a else x.

Lemma swap_groups_involutive a b x :
  swap_groups a b (swap_groups a b x) = x.
Proof.
  unfold swap_groups.
  repeat destruct N.eq_dec; subst; congruence.
Qed.

Lemma swap_groups_injective a b x y :
  swap_groups a b x = swap_groups a b y -> x = y.
Proof.
  intro E. apply (f_equal (swap_groups a b)) in E.
  now rewrite !swap_groups_involutive in E.
Qed.

Lemma swap_groups_fresh rho source target :
  group_renaming_injective rho ->
  group_renaming_injective (fun g => swap_groups (rho source) target (rho g)).
Proof.
  intros Injective a b E. apply Injective. now apply swap_groups_injective in E.
Qed.

Lemma swap_groups_maps_new (rho : N -> N) source target :
  swap_groups (rho source) target (rho source) = target.
Proof.
  unfold swap_groups. destruct (N.eq_dec (rho source) (rho source)); congruence.
Qed.

Lemma swap_groups_fixes_old rho source target old :
  group_renaming_injective rho ->
  old <> source ->
  rho old <> target ->
  swap_groups (rho source) target (rho old) = rho old.
Proof.
  intros Injective Different Fresh. unfold swap_groups.
  destruct (N.eq_dec (rho old) (rho source)) as [E|E].
  - apply Injective in E. contradiction.
  - destruct (N.eq_dec (rho old) target); congruence.
Qed.

Lemma those0_natural {A B C} (xs : list A) (f : A -> option B)
    (g : A -> option C) (rename : B -> C) :
  (forall x, g x = option_map rename (f x)) ->
  list_extra.those0 (map g xs) =
    option_map (map rename) (list_extra.those0 (map f xs)).
Proof.
  intro Natural. induction xs as [|x xs IH]; simpl; [reflexivity |].
  rewrite Natural, IH.
  destruct (f x), (list_extra.those0 (map f xs)); reflexivity.
Qed.

Lemma close_type_index_natural rho prior members index :
  close_type_index (map (rename_defined_type rho) prior) members index =
    option_map (rename_type_use rho) (close_type_index prior members index).
Proof.
  unfold close_type_index. rewrite length_map.
  destruct (N.ltb index (N.of_nat (length prior))).
  - rewrite nth_error_map.
    destruct (nth_error prior (N.to_nat index)); reflexivity.
  - destruct (N.ltb (index - N.of_nat (length prior)) members); reflexivity.
Qed.

Lemma close_heap_type_natural rho prior members h :
  close_heap_type (map (rename_defined_type rho) prior) members h =
    option_map (rename_heap_type rho) (close_heap_type prior members h).
Proof.
  destruct h; simpl; try reflexivity.
  rewrite close_type_index_natural. destruct (close_type_index prior members t); reflexivity.
Qed.

Lemma close_value_type_natural rho prior members v :
  close_value_type (map (rename_defined_type rho) prior) members v =
    option_map (rename_value_type rho) (close_value_type prior members v).
Proof.
  destruct v as [n|v|[nullable heap]|]; simpl; try reflexivity.
  rewrite close_heap_type_natural. destruct (close_heap_type prior members heap); reflexivity.
Qed.

Lemma close_storage_type_natural rho prior members t :
  close_storage_type (map (rename_defined_type rho) prior) members t =
    option_map (rename_storage_type rho) (close_storage_type prior members t).
Proof.
  destruct t; simpl; [|reflexivity].
  rewrite close_value_type_natural. destruct (close_value_type prior members v); reflexivity.
Qed.

Lemma close_field_type_natural rho prior members f :
  close_field_type (map (rename_defined_type rho) prior) members f =
    option_map (rename_field_type rho) (close_field_type prior members f).
Proof.
  unfold close_field_type. rewrite close_storage_type_natural.
  destruct (close_storage_type prior members (field_storage f)); reflexivity.
Qed.

Lemma close_function_type_natural rho prior members f :
  close_function_type (map (rename_defined_type rho) prior) members f =
    option_map
      (fun signature => let '(Closed_ft args results) := signature in
        Closed_ft (map (rename_value_type rho) args) (map (rename_value_type rho) results))
      (close_function_type prior members f).
Proof.
  destruct f as [args results]. unfold close_function_type.
  rewrite (those0_natural args _ _ _ (close_value_type_natural rho prior members)),
    (those0_natural results _ _ _ (close_value_type_natural rho prior members)).
  destruct (list_extra.those0 (map (close_value_type prior members) args)),
    (list_extra.those0 (map (close_value_type prior members) results)); reflexivity.
Qed.

Lemma close_composite_type_natural rho prior members c :
  close_composite_type (map (rename_defined_type rho) prior) members c =
    option_map (rename_composite_type rho) (close_composite_type prior members c).
Proof.
  destruct c as [f|fields|field]; simpl.
  - rewrite close_function_type_natural.
    destruct (close_function_type prior members f) as [[args results]|]; reflexivity.
  - rewrite (those0_natural fields (close_field_type prior members)
      (close_field_type (map (rename_defined_type rho) prior) members)
      (rename_field_type rho) (close_field_type_natural rho prior members)).
    destruct (list_extra.those0 (map (close_field_type prior members) fields)); reflexivity.
  - rewrite close_field_type_natural.
    destruct (close_field_type prior members field); reflexivity.
Qed.

Lemma close_subtype_natural rho prior members offset source :
  close_subtype (map (rename_defined_type rho) prior) members offset source =
    option_map (rename_subtype rho) (close_subtype prior members offset source).
Proof.
  unfold close_subtype. rewrite length_map.
  destruct (_ && _); [|reflexivity].
  rewrite close_composite_type_natural.
  rewrite (those0_natural (subtype_supers source) _ _ _
    (close_type_index_natural rho prior members)).
  destruct (list_extra.those0 (map (close_type_index prior members) (subtype_supers source))),
    (close_composite_type prior members (subtype_composite source)); reflexivity.
Qed.

Lemma close_subtypes_natural rho prior members offset sources :
  close_subtypes (map (rename_defined_type rho) prior) members offset sources =
    option_map (rename_group rho) (close_subtypes prior members offset sources).
Proof.
  revert offset. induction sources as [|source sources IH]; intro offset; simpl;
    [reflexivity |].
  rewrite close_subtype_natural, IH.
  destruct (close_subtype prior members offset source),
    (close_subtypes prior members (N.succ offset) sources); reflexivity.
Qed.

Lemma rename_resolve_type_use rho self use :
  rename_defined_type rho (resolve_type_use self use) =
    resolve_type_use (rename_defined_type rho self) (rename_type_use rho use).
Proof. destruct use; reflexivity. Qed.

Lemma rename_expand_heap_type rho self heap :
  rename_heap_type rho (expand_heap_type self heap) =
    expand_heap_type (rename_defined_type rho self) (rename_heap_type rho heap).
Proof. destruct heap as [heap|use]; simpl; [reflexivity |]. now rewrite rename_resolve_type_use. Qed.

Lemma rename_expand_value_type rho self value :
  rename_value_type rho (expand_value_type self value) =
    expand_value_type (rename_defined_type rho self) (rename_value_type rho value).
Proof. destruct value; simpl; try reflexivity. now rewrite rename_expand_heap_type. Qed.

Lemma rename_expand_storage_type rho self storage :
  rename_storage_type rho (expand_storage_type self storage) =
    expand_storage_type (rename_defined_type rho self) (rename_storage_type rho storage).
Proof. destruct storage; simpl; [now rewrite rename_expand_value_type | reflexivity]. Qed.

Lemma rename_expand_field_type rho self field :
  rename_field_type rho (expand_field_type self field) =
    expand_field_type (rename_defined_type rho self) (rename_field_type rho field).
Proof. unfold rename_field_type, expand_field_type; simpl. now rewrite rename_expand_storage_type. Qed.

Lemma rename_expand_composite_type rho self composite :
  rename_composite_type rho (expand_composite_type self composite) =
    expand_composite_type (rename_defined_type rho self) (rename_composite_type rho composite).
Proof.
  destruct composite as [[args results]|fields|field]; simpl.
  - rewrite !map_map. f_equal. f_equal; apply map_ext; apply rename_expand_value_type.
  - rewrite !map_map. f_equal. apply map_ext. apply rename_expand_field_type.
  - now rewrite rename_expand_field_type.
Qed.

Lemma rename_expand_subtype rho self subtype :
  rename_subtype rho (expand_subtype self subtype) =
    expand_subtype (rename_defined_type rho self) (rename_subtype rho subtype).
Proof.
  unfold rename_subtype, expand_subtype; simpl.
  rewrite rename_expand_composite_type, !map_map. f_equal.
  apply map_ext. intro use. simpl. now rewrite rename_resolve_type_use.
Qed.

Definition registry_embedding (rho : N -> N) (source target : canonical_registry) : Prop :=
  forall index group,
    nth_error source index = Some group ->
    nth_error target (N.to_nat (rho (N.of_nat index))) = Some (rename_group rho group).

Lemma registry_embedding_lookup rho source target t :
  registry_embedding rho source target ->
  N.to_nat t.(defined_group) < length source ->
  lookup_defined_type target (rename_defined_type rho t) =
    option_map (rename_subtype rho) (lookup_defined_type source t).
Proof.
  intros Embedding Bound. unfold lookup_defined_type. simpl.
  destruct (nth_error source (N.to_nat (defined_group t))) as [group|] eqn:Group.
  - specialize (Embedding _ _ Group).
    rewrite N2Nat.id in Embedding. rewrite Embedding.
    unfold rename_group. apply nth_error_map.
  - apply nth_error_None in Group. lia.
Qed.

Lemma registry_embedding_expansion rho source target t st :
  registry_embedding rho source target ->
  expand_defined_type source t = Some st ->
  expand_defined_type target (rename_defined_type rho t) = Some (rename_subtype rho st).
Proof.
  intros Embedding Expanded.
  unfold expand_defined_type in *.
  destruct (lookup_defined_type source t) as [raw|] eqn:Lookup; [|discriminate].
  assert (Bound : N.to_nat (defined_group t) < length source).
  { unfold lookup_defined_type in Lookup.
    destruct (nth_error source (N.to_nat (defined_group t))) eqn:Group;
      [now apply nth_error_index_bound in Group | discriminate]. }
  rewrite (registry_embedding_lookup _ _ _ _ Embedding Bound), Lookup.
  inversion Expanded; subst st. simpl. now rewrite rename_expand_subtype.
Qed.

Lemma registry_embedding_path rho source target n a b :
  registry_embedding rho source target ->
  declared_type_path source n a b ->
  declared_type_path target n (rename_defined_type rho a) (rename_defined_type rho b).
Proof.
  intros Embedding Path. induction Path as [a|n a b c Step Path IH].
  - constructor.
  - eapply dtp_step; [|exact IH].
    destruct Step as [st [Expanded Parent]].
    exists (rename_subtype rho st). split.
    + exact (registry_embedding_expansion rho source target a st Embedding Expanded).
    + change (In (rename_type_use rho (CT_def b))
        (map (rename_type_use rho) (subtype_supers st))).
      now apply in_map.
Qed.

Lemma registry_embedding_matches rho source target a b :
  registry_embedding rho source target ->
  canonical_registry_super_wf target ->
  defined_type_matches source a b = true ->
  defined_type_matches target (rename_defined_type rho a) (rename_defined_type rho b) = true.
Proof.
  intros Embedding WF Matches. apply defined_type_matches_sound in Matches.
  destruct Matches as [n Path].
  apply (defined_type_matches_complete _ n _ _ WF).
  exact (registry_embedding_path rho source target n a b Embedding Path).
Qed.

Definition renamings_agree_below bound (rho sigma : N -> N) : Prop :=
  forall group, (group < N.of_nat bound)%N -> rho group = sigma group.

Definition group_external_local bound group : Prop :=
  forall rho sigma, renamings_agree_below bound rho sigma ->
    rename_group rho group = rename_group sigma group.

Definition registry_external_local (groups : canonical_registry) : Prop :=
  forall index group, nth_error groups index = Some group ->
    group_external_local (length groups) group.

Lemma present_group_bound groups names id :
  defined_types_present groups names ->
  In id names ->
  (defined_group id < N.of_nat (length groups))%N.
Proof.
  unfold defined_types_present. rewrite Forall_forall.
  intros Present Member. destruct (Present _ Member) as [raw Lookup].
  unfold lookup_defined_type in Lookup.
  destruct (nth_error groups (N.to_nat (defined_group id))) eqn:Group;
    [|discriminate].
  apply nth_error_index_bound in Group.
  lia.
Qed.

Lemma rename_names_agree groups names rho sigma :
  defined_types_present groups names ->
  renamings_agree_below (length groups) rho sigma ->
  map (rename_defined_type rho) names = map (rename_defined_type sigma) names.
Proof.
  intros Present Agree. apply map_ext_in. intros [group member] Member.
  unfold rename_defined_type; simpl. f_equal. apply Agree.
  exact (present_group_bound _ _ _ Present Member).
Qed.

Lemma closed_group_external_local groups names members offset sources closed :
  defined_types_present groups names ->
  close_subtypes names members offset sources = Some closed ->
  group_external_local (length groups) closed.
Proof.
  intros Present Closed rho sigma Agree.
  pose proof (close_subtypes_natural rho names members offset sources) as Rho.
  pose proof (close_subtypes_natural sigma names members offset sources) as Sigma.
  rewrite Closed in Rho, Sigma.
  rewrite (rename_names_agree _ _ _ _ Present Agree) in Rho.
  rewrite Sigma in Rho. now injection Rho.
Qed.

Lemma group_external_local_weaken n m group :
  n <= m -> group_external_local n group -> group_external_local m group.
Proof.
  intros Bound Local rho sigma Agree. apply Local. intros g Below.
  apply Agree. lia.
Qed.

Lemma those0_member {A B} (xs : list A) (f : A -> option B) ys y :
  list_extra.those0 (map f xs) = Some ys ->
  In y ys ->
  exists x, In x xs /\ f x = Some y.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys Closed Member; simpl in Closed.
  - inversion Closed; subst; contradiction.
  - destruct (f x) as [head|] eqn:Head; [|discriminate].
    destruct (list_extra.those0 (map f xs)) as [tail|] eqn:Tail; [|discriminate].
    inversion Closed; subst ys.
    destruct Member as [Same|TailMember].
    + subst y. exists x. split; [now left | exact Head].
    + destruct (IH _ eq_refl TailMember) as [z [Inxs Fz]].
      exists z. split; [now right | exact Fz].
Qed.

Definition parent_use_scoped prior offset use : Prop :=
  (exists id, use = CT_def id /\ In id prior) \/
  (exists member, use = CT_rec member /\ (member < offset)%N).

Lemma close_super_index_scoped prior members offset index use :
  (index < N.of_nat (length prior) + offset)%N ->
  close_type_index prior members index = Some use ->
  parent_use_scoped prior offset use.
Proof.
  intros Bound. unfold close_type_index.
  destruct (N.ltb index (N.of_nat (length prior))) eqn:Earlier.
  - destruct (nth_error prior (N.to_nat index)) as [id|] eqn:Lookup;
      [|discriminate].
    intro E; inversion E; subst. left. exists id. split; [reflexivity |].
    now apply nth_error_In in Lookup.
  - destruct (N.ltb (index - N.of_nat (length prior)) members); [|discriminate].
    intro E; inversion E; subst. apply N.ltb_ge in Earlier.
    right. eexists. split; [reflexivity | lia].
Qed.

Lemma close_subtype_supers_scoped prior members offset source closed :
  close_subtype prior members offset source = Some closed ->
  Forall (parent_use_scoped prior offset) closed.(subtype_supers).
Proof.
  unfold close_subtype.
  destruct (_ && _) eqn:Checked; [|discriminate].
  apply andb_true_iff in Checked. destruct Checked as [_ Bounds].
  destruct (list_extra.those0 (map (close_type_index prior members) (subtype_supers source)))
    as [parents|] eqn:Parents; [|discriminate].
  destruct (close_composite_type prior members (subtype_composite source));
    [|discriminate].
  intro E; inversion E; subst. simpl.
  apply Forall_forall. intros use Member.
  destruct (those0_member _ _ _ _ Parents Member) as [index [Insource Closed]].
  apply forallb_forall with (x := index) in Bounds; [|exact Insource].
  apply N.ltb_lt in Bounds.
  exact (close_super_index_scoped _ _ _ _ _ Bounds Closed).
Qed.

Lemma close_subtypes_supers_scoped prior members offset sources closed index st :
  close_subtypes prior members offset sources = Some closed ->
  nth_error closed index = Some st ->
  Forall (parent_use_scoped prior (offset + N.of_nat index)%N) st.(subtype_supers).
Proof.
  revert offset closed index st.
  induction sources as [|source sources IH]; intros offset closed index st Closed Lookup.
  - simpl in Closed. inversion Closed; subst. destruct index; discriminate.
  - simpl in Closed.
    destruct (close_subtype prior members offset source) as [head|] eqn:Head;
      [|discriminate].
    destruct (close_subtypes prior members (N.succ offset) sources) as [tail|] eqn:Tail;
      [|discriminate].
    inversion Closed; subst closed.
    destruct index as [|index]; simpl in Lookup.
    + inversion Lookup; subst. rewrite N.add_0_r.
      now apply close_subtype_supers_scoped in Head.
    + specialize (IH _ _ _ _ Tail Lookup).
      replace (offset + N.of_nat (S index))%N
        with (N.succ offset + N.of_nat index)%N by (rewrite Nat2N.inj_succ; lia).
      exact IH.
Qed.

Lemma defined_type_rank_extension groups suffix id :
  N.to_nat id.(defined_group) < length groups ->
  defined_type_rank (groups ++ suffix) id = defined_type_rank groups id.
Proof.
  intro Bound. unfold defined_type_rank. rewrite firstn_app.
  replace (N.to_nat (defined_group id) - length groups) with 0 by lia.
  simpl. now rewrite app_nil_r.
Qed.

Lemma appended_group_rank groups group member :
  defined_type_rank (groups ++ [group]) (Def_type (N.of_nat (length groups)) member) =
    canonical_registry_size groups + N.to_nat member.
Proof.
  unfold defined_type_rank. simpl. rewrite Nat2N.id, firstn_app, firstn_all, Nat.sub_diag.
  simpl. now rewrite app_nil_r.
Qed.

Lemma declared_type_step_raw groups a b :
  declared_type_step groups a b ->
  exists raw use,
    lookup_defined_type groups a = Some raw /\
    In use raw.(subtype_supers) /\
    b = resolve_type_use a use.
Proof.
  intros [st [Expanded Parent]]. unfold expand_defined_type in Expanded.
  destruct (lookup_defined_type groups a) as [raw|] eqn:Lookup; [|discriminate].
  inversion Expanded; subst st.
  change (In (CT_def b)
    (map (fun u => CT_def (resolve_type_use a u)) (subtype_supers raw))) in Parent.
  apply in_map_iff in Parent. destruct Parent as [use [Same Member]].
  injection Same as Same. exists raw, use. auto.
Qed.

Lemma declared_type_step_from_raw groups a raw use :
  lookup_defined_type groups a = Some raw ->
  In use raw.(subtype_supers) ->
  declared_type_step groups a (resolve_type_use a use).
Proof.
  intros Lookup Member. exists (expand_subtype a raw). split.
  - unfold expand_defined_type. now rewrite Lookup.
  - change (In ((fun u => CT_def (resolve_type_use a u)) use)
      (map (fun u => CT_def (resolve_type_use a u)) (subtype_supers raw))).
    now apply in_map.
Qed.

Lemma append_group_super_wf groups prior group :
  canonical_registry_super_wf groups ->
  defined_types_present groups prior ->
  (forall index st, nth_error group index = Some st ->
    Forall (parent_use_scoped prior (N.of_nat index)) st.(subtype_supers)) ->
  canonical_registry_super_wf (groups ++ [group]).
Proof.
  intros WF Present Parents a b Step.
  destruct (declared_type_step_raw _ _ _ Step)
    as [raw [use [Lookup [Member Resolved]]]]. subst b.
  assert (GroupBound :
    N.to_nat a.(defined_group) < length groups + 1).
  { unfold lookup_defined_type in Lookup.
    destruct (nth_error (groups ++ [group]) (N.to_nat (defined_group a))) eqn:Group;
      [|discriminate].
    apply nth_error_index_bound in Group. rewrite length_app in Group. simpl in Group. lia. }
  destruct (lt_dec (N.to_nat a.(defined_group)) (length groups)) as [Old|New].
  - rewrite lookup_defined_type_extension in Lookup by exact Old.
    pose proof (declared_type_step_from_raw _ _ _ _ Lookup Member) as OldStep.
    destruct (WF _ _ OldStep) as [[parent Parent] Smaller].
    assert (ParentBound : N.to_nat (defined_group (resolve_type_use a use)) < length groups).
    { unfold lookup_defined_type in Parent.
      destruct (nth_error groups (N.to_nat (defined_group (resolve_type_use a use))))
        eqn:ParentGroup; [now apply nth_error_index_bound in ParentGroup | discriminate]. }
    split.
    + exists parent. now rewrite lookup_defined_type_extension.
    + rewrite !defined_type_rank_extension by assumption. exact Smaller.
  - assert (GroupIndex : defined_group a = N.of_nat (length groups)) by lia.
    destruct a as [gi mi]. simpl in *. subst gi.
    unfold lookup_defined_type in Lookup. simpl in Lookup.
    rewrite Nat2N.id, nth_error_app2 in Lookup by lia.
    rewrite Nat.sub_diag in Lookup. simpl in Lookup.
    specialize (Parents _ _ Lookup).
    rewrite Forall_forall in Parents. specialize (Parents use Member).
    destruct Parents as [[id [Same InPrior]]|[j [Same Smaller]]]; subst use; simpl.
    + unfold defined_types_present in Present. rewrite Forall_forall in Present.
      destruct (Present _ InPrior) as [parent Parent].
      assert (Bound : N.to_nat (defined_group id) < length groups).
      { unfold lookup_defined_type in Parent.
        destruct (nth_error groups (N.to_nat (defined_group id))) eqn:ParentGroup;
          [now apply nth_error_index_bound in ParentGroup | discriminate]. }
      split.
      * exists parent. now rewrite lookup_defined_type_extension.
      * rewrite defined_type_rank_extension by exact Bound.
        rewrite appended_group_rank.
        pose proof (defined_type_rank_bound _ _ _ Parent). lia.
    + rewrite N2Nat.id in Smaller.
      assert (Before : N.to_nat j < N.to_nat mi).
      { apply Nat.compare_lt_iff. rewrite <- N2Nat.inj_compare. now apply N.compare_lt_iff. }
      split.
      * assert (Bound : N.to_nat j < length group).
        { apply nth_error_index_bound in Lookup.
          exact (Nat.lt_trans _ _ _ Before Lookup). }
        destruct (nth_error group (N.to_nat j)) as [parent|] eqn:Parent.
        2: { apply nth_error_None in Parent. lia. }
        exists parent. unfold lookup_defined_type. simpl.
        rewrite Nat2N.id, nth_error_app2 by lia.
        now rewrite Nat.sub_diag.
      * rewrite !appended_group_rank. lia.
Qed.

Lemma intern_closed_group_super_wf groups prior members sources group :
  canonical_registry_super_wf groups ->
  defined_types_present groups prior ->
  close_subtypes prior members 0 sources = Some group ->
  canonical_registry_super_wf (fst (intern_group groups group)).
Proof.
  intros WF Present Closed. unfold intern_group.
  destruct (find_canonical_group groups group); simpl; [exact WF |].
  apply append_group_super_wf with (prior := prior); try assumption.
  intros index st Lookup.
  pose proof (close_subtypes_supers_scoped _ _ _ _ _ _ _ Closed Lookup) as Parents.
  exact Parents.
Qed.

Lemma rename_group_defined_types rho group members :
  map (rename_defined_type rho) (group_defined_types group members) =
    group_defined_types (rho group) members.
Proof. unfold group_defined_types. rewrite map_map. reflexivity. Qed.

Lemma intern_group_existing groups group index :
  NoDup groups ->
  nth_error groups index = Some group ->
  intern_group groups group = (groups, N.of_nat index).
Proof.
  intros Unique Lookup.
  assert (Member : In group groups) by (now apply nth_error_In in Lookup).
  destruct (find_canonical_group_complete _ _ Member) as [found Found].
  pose proof (find_canonical_group_sound _ _ _ Found) as AtFound.
  pose proof (canonical_group_identity_unique _ _ _ _ Unique AtFound Lookup) as Same.
  subst found. unfold intern_group. now rewrite Found.
Qed.

Definition registry_coverage (rho : N -> N)
    (source base target : canonical_registry) : Prop :=
  forall index group, nth_error target index = Some group ->
    nth_error base index = Some group \/
    exists source_index source_group,
      nth_error source source_index = Some source_group /\
      index = N.to_nat (rho (N.of_nat source_index)).

Record registry_correspondence rho source base target : Prop := {
  correspondence_injective : group_renaming_injective rho;
  correspondence_source_unique : NoDup source;
  correspondence_target_unique : NoDup target;
  correspondence_local : registry_external_local source;
  correspondence_embedding : registry_embedding rho source target;
  correspondence_coverage : registry_coverage rho source base target;
}.

Lemma registry_external_local_append source group :
  registry_external_local source ->
  group_external_local (length source) group ->
  registry_external_local (source ++ [group]).
Proof.
  intros Local GroupLocal index raw Lookup.
  rewrite length_app; simpl.
  destruct (lt_dec index (length source)) as [Old|New].
  - rewrite nth_error_app1 in Lookup by exact Old.
     eapply group_external_local_weaken with (n := length source);
       [lia | now apply (Local index)].
  - rewrite nth_error_app2 in Lookup by lia.
    destruct (index - length source) as [|offset]; simpl in Lookup.
     + inversion Lookup; subst. eapply group_external_local_weaken with (n := length source);
         [lia | exact GroupLocal].
    + destruct offset; discriminate.
Qed.

Lemma intern_group_correspondence rho source base target group :
  registry_correspondence rho source base target ->
  group_external_local (length source) group ->
  exists sigma,
    registry_correspondence sigma
      (fst (intern_group source group)) base
      (fst (intern_group target (rename_group rho group))) /\
    renamings_agree_below (length source) rho sigma /\
    sigma (snd (intern_group source group)) =
      snd (intern_group target (rename_group rho group)).
Proof.
  intros [Injective SourceUnique TargetUnique Local Embedding Coverage] GroupLocal.
  unfold intern_group at 1 3.
  destruct (find_canonical_group source group) as [index|] eqn:Found.
  - pose proof (find_canonical_group_sound _ _ _ Found) as SourceLookup.
    pose proof (Embedding _ _ SourceLookup) as TargetLookup.
    pose proof (intern_group_existing _ _ _ TargetUnique TargetLookup) as Intern.
    rewrite N2Nat.id in Intern. rewrite Intern. simpl.
    exists rho. split.
    + constructor; assumption.
    + split; [intros id Bound; reflexivity | reflexivity].
  - apply find_canonical_group_none in Found.
    set (next := N.of_nat (length source)).
    set (target_next := snd (intern_group target (rename_group rho group))).
    set (target' := fst (intern_group target (rename_group rho group))).
    assert (TargetGroup : nth_error target' (N.to_nat target_next) =
      Some (rename_group rho group)).
    { apply intern_group_lookup. }
    assert (Fresh : forall id, (id < next)%N -> rho id <> target_next).
    { intros id Bound Same.
      assert (NatBound : N.to_nat id < length source) by (unfold next in Bound; lia).
      destruct (nth_error source (N.to_nat id)) as [oldgroup|] eqn:Oldgroup.
      2: { apply nth_error_None in Oldgroup. lia. }
      pose proof (Embedding _ _ Oldgroup) as Image.
      rewrite N2Nat.id in Image.
      assert (ImageBound : N.to_nat (rho id) < length target)
        by (now apply nth_error_index_bound in Image).
      assert (StillImage : nth_error target' (N.to_nat (rho id)) =
        Some (rename_group rho oldgroup)).
      { unfold target'. rewrite intern_group_preserves_lookup by exact ImageBound.
        exact Image. }
      rewrite Same, TargetGroup in StillImage.
      injection StillImage as SameGroup.
      apply (rename_group_injective rho Injective) in SameGroup.
      subst oldgroup. apply Found. now apply nth_error_In in Oldgroup. }
    set (sigma := fun id => swap_groups (rho next) target_next (rho id)).
    assert (Agree : renamings_agree_below (length source) rho sigma).
    { intros id Bound. symmetry. unfold sigma.
      apply swap_groups_fixes_old; try assumption.
      - unfold next. lia.
      - now apply Fresh. }
    assert (NewImage : sigma next = target_next) by apply swap_groups_maps_new.
    assert (NewGroup : rename_group sigma group = rename_group rho group).
    { symmetry. now apply GroupLocal. }
    assert (UniqueTarget : NoDup target')
      by (apply intern_group_nodup; exact TargetUnique).
    assert (Embedding' : registry_embedding sigma (source ++ [group]) target').
    { intros i raw Lookup.
      destruct (lt_dec i (length source)) as [Old|New].
      - rewrite nth_error_app1 in Lookup by exact Old.
        pose proof (Embedding _ _ Lookup) as Image.
        assert (Bound : N.to_nat (rho (N.of_nat i)) < length target)
          by (now apply nth_error_index_bound in Image).
        rewrite <- (Agree (N.of_nat i)) by lia.
        unfold target'. rewrite intern_group_preserves_lookup by exact Bound.
        rewrite Image. f_equal. apply (Local i raw Lookup). exact Agree.
      - rewrite nth_error_app2 in Lookup by lia.
        assert (Index : i = length source).
        { apply nth_error_index_bound in Lookup. simpl in Lookup. lia. }
        subst i. rewrite Nat.sub_diag in Lookup. simpl in Lookup.
        inversion Lookup; subst raw.
        change (nth_error target' (N.to_nat (sigma next)) = Some (rename_group sigma group)).
        now rewrite NewImage, NewGroup. }
    assert (Coverage' : registry_coverage sigma (source ++ [group]) base target').
    { intros i raw Lookup.
      destruct (lt_dec i (length target)) as [Old|New].
      - assert (OldLookup : nth_error target i = Some raw).
        { unfold target' in Lookup. now rewrite intern_group_preserves_lookup in Lookup. }
        destruct (Coverage _ _ OldLookup) as [Base|[si [sg [SourceLookup Image]]]].
        + now left.
        + right. exists si, sg. split.
          * now rewrite nth_error_app1 by (now apply nth_error_index_bound in SourceLookup).
          * rewrite Image. f_equal. apply Agree.
            apply nth_error_index_bound in SourceLookup. lia.
      - unfold target', intern_group in Lookup.
        destruct (find_canonical_group target (rename_group rho group)) eqn:TargetFound.
        + simpl in Lookup. apply nth_error_index_bound in Lookup. lia.
        + simpl in Lookup. rewrite nth_error_app2 in Lookup by lia.
          assert (Index : i = length target)
            by (apply nth_error_index_bound in Lookup; simpl in Lookup; lia).
          subst i. right. exists (length source), group. split.
          * rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
          * change (length target = N.to_nat (sigma next)).
            rewrite NewImage. unfold target_next, intern_group. rewrite TargetFound.
            simpl. now rewrite Nat2N.id. }
    exists sigma. simpl. split.
    + constructor.
      * unfold sigma. now apply swap_groups_fresh.
      * now apply NoDup_append_single.
      * exact UniqueTarget.
      * now apply registry_external_local_append.
      * exact Embedding'.
      * exact Coverage'.
    + split; [exact Agree | exact NewImage].
Qed.

Lemma registry_embedding_present rho source target names :
  registry_embedding rho source target ->
  defined_types_present source names ->
  defined_types_present target (map (rename_defined_type rho) names).
Proof.
  intros Embedding Present. unfold defined_types_present in *.
  rewrite Forall_forall in *. intros id Member.
  apply in_map_iff in Member. destruct Member as [old [Same Member]]. subst id.
  destruct (Present _ Member) as [raw Lookup].
  assert (Bound : N.to_nat (defined_group old) < length source).
  { unfold lookup_defined_type in Lookup.
    destruct (nth_error source (N.to_nat (defined_group old))) eqn:Group;
      [now apply nth_error_index_bound in Group | discriminate]. }
  exists (rename_subtype rho raw).
  now rewrite (registry_embedding_lookup _ _ _ _ Embedding Bound), Lookup.
Qed.

Lemma close_type_group_correspondence rho source base target prior group source' names :
  registry_correspondence rho source base target ->
  defined_types_present source prior ->
  close_type_group source prior group = Some (source', names) ->
  exists sigma target' actual_names,
    close_type_group target (map (rename_defined_type rho) prior) group =
      Some (target', actual_names) /\
    registry_correspondence sigma source' base target' /\
    renamings_agree_below (length source) rho sigma /\
    actual_names = map (rename_defined_type sigma) names.
Proof.
  intros Correspondence Present Closed.
  unfold close_type_group in Closed.
  destruct (close_subtypes prior (N.of_nat (length group)) 0 group)
    as [raw|] eqn:Raw; [|discriminate].
  pose proof (closed_group_external_local _ _ _ _ _ _ Present Raw) as Local.
  destruct (intern_group_correspondence _ _ _ _ _ Correspondence Local)
    as [sigma [Correspondence' [Agree NewAddress]]].
  destruct (intern_group source raw) as [source_output address] eqn:SourceIntern.
  destruct (intern_group target (rename_group rho raw))
    as [target_output target_address] eqn:TargetIntern.
  simpl in Correspondence', NewAddress.
  inversion Closed; subst source' names.
  exists sigma, target_output, (group_defined_types target_address (length raw)).
  split.
  - unfold close_type_group. rewrite close_subtypes_natural, Raw.
    simpl. rewrite TargetIntern. unfold rename_group. now rewrite length_map.
  - split; [exact Correspondence' |]. split; [exact Agree |].
    rewrite rename_group_defined_types, NewAddress. reflexivity.
Qed.

Theorem close_type_groups_correspondence groups source base target prior rho output names :
  registry_correspondence rho source base target ->
  defined_types_present source prior ->
  canonical_registry_super_wf target ->
  close_type_groups_from source prior groups = Some (output, names) ->
  exists sigma target_output target_names,
    close_type_groups_from target (map (rename_defined_type rho) prior) groups =
      Some (target_output, target_names) /\
    registry_correspondence sigma output base target_output /\
    canonical_registry_super_wf target_output /\
    target_names = map (rename_defined_type sigma) names.
Proof.
  revert source target prior rho output names.
  induction groups as [|group groups IH];
    intros source target prior rho output names Correspondence Present WF Closed.
  - simpl in Closed. inversion Closed; subst.
    exists rho, target, (map (rename_defined_type rho) names). simpl. auto.
  - simpl in Closed.
    destruct (close_type_group source prior group) as [[source' new_names]|] eqn:Group;
      [|discriminate].
    destruct (close_type_group_correspondence _ _ _ _ _ _ _ _
      Correspondence Present Group)
      as [sigma [target' [actual_names [TargetGroup [Correspondence' [Agree NewNames]]]]]].
    assert (OldNames :
      map (rename_defined_type rho) prior = map (rename_defined_type sigma) prior)
      by (now apply (rename_names_agree source)).
    assert (Present' : defined_types_present source' (prior ++ new_names)).
    { unfold defined_types_present. apply Forall_app. split.
      - destruct (close_type_group_extension _ _ _ _ _ Group) as [suffix Extension].
        rewrite Extension. now apply defined_types_present_extension.
      - now apply close_type_group_present in Group. }
    assert (WF' : canonical_registry_super_wf target').
    { unfold close_type_group in TargetGroup.
      destruct (close_subtypes (map (rename_defined_type rho) prior)
        (N.of_nat (length group)) 0 group) as [raw|] eqn:Raw; [|discriminate].
      pose proof (intern_closed_group_super_wf target
        (map (rename_defined_type rho) prior) (N.of_nat (length group)) group raw WF) as InternWF.
      destruct Correspondence as [_ _ _ _ Embedding _].
      specialize (InternWF (registry_embedding_present _ _ _ _ Embedding Present) Raw).
      destruct (intern_group target raw) as [registry address]. simpl in InternWF.
      inversion TargetGroup; subst target'. exact InternWF. }
    destruct (IH _ _ _ _ _ _ Correspondence' Present' WF' Closed)
      as [final_rho [target_output [target_names [TargetClosed [FinalCorr [FinalWF FinalNames]]]]]].
    exists final_rho, target_output, target_names. split.
    + simpl. rewrite TargetGroup, OldNames, NewNames, <-map_app.
      exact TargetClosed.
    + auto.
Qed.

Lemma registry_embedding_heap_kind rho source target id kind :
  registry_embedding rho source target ->
  defined_heap_kind source id = Some kind ->
  defined_heap_kind target (rename_defined_type rho id) = Some kind.
Proof.
  intros Embedding Kind. unfold defined_heap_kind in *.
  destruct (expand_defined_type source id) as [st|] eqn:Expanded; [|discriminate].
  rewrite (registry_embedding_expansion _ _ _ _ _ Embedding Expanded).
  cbn [rename_subtype subtype_composite].
  destruct (subtype_composite st) as [[args results]|fields|field]; exact Kind.
Qed.

Lemma registry_embedding_heap_matches rho source target a b :
  registry_embedding rho source target ->
  closed_heap_matches source a b ->
  closed_heap_matches target (rename_heap_type rho a) (rename_heap_type rho b).
Proof.
  intros Embedding Matches. destruct Matches; simpl.
  - now constructor.
  - apply chm_defined with (n := n).
    exact (registry_embedding_path rho source target _ _ _ Embedding H).
  - apply chm_defined_abstract with (kind := kind); [|assumption].
    exact (registry_embedding_heap_kind rho source target _ _ Embedding H).
  - apply chm_bottom_defined with (kind := kind); [|assumption].
    exact (registry_embedding_heap_kind rho source target _ _ Embedding H).
Qed.

Lemma registry_embedding_value_matches rho source target a b :
  registry_embedding rho source target ->
  closed_value_matches source a b ->
  closed_value_matches target (rename_value_type rho a) (rename_value_type rho b).
Proof.
  intros Embedding Matches. destruct Matches; simpl; try constructor; try assumption.
  exact (registry_embedding_heap_matches rho source target _ _ Embedding H0).
Qed.

Lemma registry_embedding_storage_matches rho source target a b :
  registry_embedding rho source target ->
  @gc_types.storage_matches _ (closed_value_matches source) a b ->
  @gc_types.storage_matches _ (closed_value_matches target)
    (rename_storage_type rho a) (rename_storage_type rho b).
Proof.
  intros Embedding Matches. destruct Matches; simpl; constructor.
  exact (registry_embedding_value_matches rho source target _ _ Embedding H).
Qed.

Lemma registry_embedding_field_matches rho source target a b :
  registry_embedding rho source target ->
  closed_field_matches source a b ->
  closed_field_matches target (rename_field_type rho a) (rename_field_type rho b).
Proof.
  intros Embedding Matches. destruct Matches; unfold rename_field_type; simpl; constructor.
  exact (registry_embedding_storage_matches rho source target _ _ Embedding H).
Qed.

Lemma Forall2_map_transport {A B C D} (R : A -> B -> Prop) (S : C -> D -> Prop)
    (f : A -> C) (g : B -> D) xs ys :
  (forall x y, R x y -> S (f x) (g y)) ->
  Forall2 R xs ys -> Forall2 S (map f xs) (map g ys).
Proof.
  intros Transport Related. induction Related; simpl; constructor; auto.
Qed.

Lemma registry_embedding_composite_matches rho source target a b :
  registry_embedding rho source target ->
  closed_composite_matches source a b ->
  closed_composite_matches target (rename_composite_type rho a) (rename_composite_type rho b).
Proof.
  intros Embedding Matches. destruct Matches; simpl.
  - constructor; eapply Forall2_map_transport;
      try eassumption; intros x y Match;
      exact (registry_embedding_value_matches rho source target _ _ Embedding Match).
  - constructor. rewrite length_map, firstn_map.
    eapply Forall2_map_transport; [|exact H]. intros x y Match.
    exact (registry_embedding_field_matches rho source target _ _ Embedding Match).
  - constructor. exact (registry_embedding_field_matches rho source target _ _ Embedding H).
Qed.

Lemma registry_embedding_value_valid rho source target v :
  registry_embedding rho source target ->
  closed_value_valid source v ->
  closed_value_valid target (rename_value_type rho v).
Proof.
  intros Embedding Valid. destruct Valid; simpl; try (constructor; assumption).
  assert (Bound : N.to_nat (defined_group t) < length source).
  { unfold lookup_defined_type in H.
    destruct (nth_error source (N.to_nat (defined_group t))) eqn:Group;
      [now apply nth_error_index_bound in Group | discriminate]. }
  apply cvv_defined with (st := rename_subtype rho st).
  now rewrite (registry_embedding_lookup _ _ _ _ Embedding Bound), H.
Qed.

Lemma registry_embedding_storage_valid rho source target storage :
  registry_embedding rho source target ->
  closed_storage_valid source storage ->
  closed_storage_valid target (rename_storage_type rho storage).
Proof.
  intros Embedding Valid. destruct Valid; simpl; constructor.
  exact (registry_embedding_value_valid rho source target _ Embedding H).
Qed.

Lemma Forall_map_transport {A B} (P : A -> Prop) (Q : B -> Prop)
    (f : A -> B) xs :
  (forall x, P x -> Q (f x)) -> Forall P xs -> Forall Q (map f xs).
Proof.
  intros Transport Valid. induction Valid; simpl; constructor; auto.
Qed.

Lemma registry_embedding_composite_valid rho source target composite :
  registry_embedding rho source target ->
  closed_composite_valid source composite ->
  closed_composite_valid target (rename_composite_type rho composite).
Proof.
  intros Embedding Valid. destruct Valid; simpl.
  - constructor; eapply Forall_map_transport;
      try eassumption; intros x V;
      exact (registry_embedding_value_valid rho source target _ Embedding V).
  - constructor. eapply Forall_map_transport; [|exact H].
    intros field Valid. simpl.
    exact (registry_embedding_storage_valid rho source target _ Embedding Valid).
  - constructor. exact (registry_embedding_storage_valid rho source target _ Embedding H).
Qed.

Lemma registry_embedding_parent_valid rho source target composite use :
  registry_embedding rho source target ->
  closed_parent_valid source composite use ->
  closed_parent_valid target (rename_composite_type rho composite) (rename_type_use rho use).
Proof.
  intros Embedding Valid. destruct Valid; simpl.
  apply cpv_parent with (parent := rename_subtype rho parent).
  - exact (registry_embedding_expansion rho source target _ _ Embedding H).
  - exact H0.
  - exact (registry_embedding_composite_matches rho source target _ _ Embedding H1).
Qed.

Lemma registry_embedding_declaration_valid rho source target id :
  registry_embedding rho source target ->
  defined_declaration_valid source id ->
  defined_declaration_valid target (rename_defined_type rho id).
Proof.
  intros Embedding [st [Expanded [Count [Valid Parents]]]].
  exists (rename_subtype rho st). split.
  - exact (registry_embedding_expansion rho source target _ _ Embedding Expanded).
  - simpl. rewrite length_map. split; [exact Count |].
    split.
    + exact (registry_embedding_composite_valid rho source target _ Embedding Valid).
    + eapply Forall_map_transport; [|exact Parents]. intros use Parent.
      exact (registry_embedding_parent_valid rho source target _ _ Embedding Parent).
Qed.

Lemma rename_defined_type_identity id : rename_defined_type (fun x => x) id = id.
Proof. destruct id; reflexivity. Qed.

Lemma rename_value_type_identity v : rename_value_type (fun x => x) v = v.
Proof.
  destruct v as [n|v|nullable [h|[i|[g m]]]]; reflexivity.
Qed.

Lemma rename_field_type_identity field : rename_field_type (fun x => x) field = field.
Proof.
  destruct field as [mut [v|p]]; simpl; unfold rename_field_type; simpl;
    [now rewrite rename_value_type_identity | reflexivity].
Qed.

Lemma map_identity_by {A} (f : A -> A) xs :
  (forall x, f x = x) -> map f xs = xs.
Proof. intro Identity. induction xs; simpl; [reflexivity | now rewrite Identity, IHxs]. Qed.

Lemma rename_subtype_identity st : rename_subtype (fun x => x) st = st.
Proof.
  destruct st as [final supers composite]. unfold rename_subtype; simpl.
  assert (Uses : map (rename_type_use (fun x => x)) supers = supers).
  { apply map_identity_by. intros [i|[g m]]; reflexivity. }
  rewrite Uses. f_equal. destruct composite as [[args results]|fields|field]; simpl.
  - now rewrite !(map_identity_by _ _ rename_value_type_identity).
  - now rewrite (map_identity_by _ _ rename_field_type_identity).
  - now rewrite rename_field_type_identity.
Qed.

Lemma registry_embedding_prefix base target :
  (exists suffix, target = base ++ suffix) ->
  registry_embedding (fun x => x) base target.
Proof.
  intros [suffix ->] index group Lookup.
  rewrite Nat2N.id, nth_error_app1 by (now apply nth_error_index_bound in Lookup).
  rewrite Lookup. f_equal. symmetry. apply map_identity_by. apply rename_subtype_identity.
Qed.

Lemma registry_correspondence_valid rho source base target :
  registry_correspondence rho source base target ->
  canonical_registry_valid source ->
  canonical_registry_valid base ->
  canonical_registry_super_wf target ->
  (exists suffix, target = base ++ suffix) ->
  canonical_registry_valid target.
Proof.
  intros [_ _ Unique _ Embedding Coverage]
    [_ [_ SourceValid]] [_ [_ BaseValid]] WF Prefix.
  split; [exact Unique |]. split; [exact WF |].
  intros index group member raw Group Raw.
  destruct (Coverage _ _ Group) as [Old|[source_index [source_group [SourceGroup Image]]]].
  - pose proof (BaseValid _ _ _ _ Old Raw) as Valid.
    pose proof (registry_embedding_declaration_valid (fun x => x) base target
      (Def_type (N.of_nat index) (N.of_nat member))
      (registry_embedding_prefix _ _ Prefix) Valid) as Result.
    now rewrite rename_defined_type_identity in Result.
  - pose proof (Embedding _ _ SourceGroup) as ImageGroup.
    rewrite <-Image, Group in ImageGroup. injection ImageGroup as SameGroup.
    subst group. unfold rename_group in Raw. rewrite nth_error_map in Raw.
    destruct (nth_error source_group member) as [source_raw|] eqn:SourceRaw;
      [|discriminate].
    pose proof (SourceValid _ _ _ _ SourceGroup SourceRaw) as Valid.
    pose proof (registry_embedding_declaration_valid rho source target
      (Def_type (N.of_nat source_index) (N.of_nat member)) Embedding Valid) as Result.
    unfold rename_defined_type in Result. simpl in Result.
    rewrite Image, N2Nat.id. exact Result.
Qed.

Lemma registry_embedding_source_identities rho source target names declarations ids :
  registry_embedding rho source target ->
  source_type_identitiesb source names declarations ids = true ->
  source_type_identitiesb target (map (rename_defined_type rho) names)
    declarations (map (rename_defined_type rho) ids) = true.
Proof.
  intros Embedding Checked. apply source_type_identitiesb_correct in Checked.
  apply source_type_identitiesb_correct. induction Checked; simpl; constructor; [|exact IHChecked].
  destruct H as [closed [Closed Expanded]].
  exists (rename_subtype rho closed). split.
  - now rewrite close_subtype_natural, Closed.
  - exact (registry_embedding_expansion rho source target _ _ Embedding Expanded).
Qed.

Theorem validated_closing_portable base declarations source names :
  canonical_registry_valid base ->
  close_and_validate_type_groups [] declarations = Some (source, names) ->
  source_type_identitiesb source names (List.concat declarations) names = true ->
  exists target actual_names,
    close_and_validate_type_groups base declarations = Some (target, actual_names) /\
    source_type_identitiesb target actual_names (List.concat declarations) actual_names = true.
Proof.
  intros BaseValid Closed Consistent.
  pose proof (close_and_validate_type_groups_sound _ _ _ _ Closed)
    as [SourceValid SourceClosed].
  unfold close_type_groups in SourceClosed.
  destruct (close_type_groups_from [] [] declarations) as [[output ids]|] eqn:SourceRun;
    [|discriminate].
  destruct (canonical_registry_super_orderedb output); [|discriminate].
  inversion SourceClosed; subst output ids.
  assert (Initial : registry_correspondence (fun x => x) [] base base).
  { constructor.
    - intros a b Same. exact Same.
    - constructor.
    - exact (proj1 BaseValid).
    - intros i group Lookup. destruct i; discriminate.
    - intros i group Lookup. destruct i; discriminate.
    - intros i group Lookup. now left. }
  destruct (close_type_groups_correspondence declarations [] base base [] (fun x => x)
    source names Initial (Forall_nil _) (proj1 (proj2 BaseValid)) SourceRun)
    as [rho [target [actual_names [TargetRun [Correspondence [TargetWF Names]]]]]].
  simpl in TargetRun.
  pose proof (close_type_groups_extension _ _ _ _ _ TargetRun) as Prefix.
  pose proof (registry_correspondence_valid _ _ _ _ Correspondence
    SourceValid BaseValid TargetWF Prefix) as TargetValid.
  exists target, actual_names. split.
  - unfold close_and_validate_type_groups, close_type_groups.
    rewrite TargetRun, (canonical_registry_super_orderedb_complete _ TargetWF).
    rewrite (proj2 (canonical_registry_validb_correct _) TargetValid). reflexivity.
  - rewrite Names.
    exact (registry_embedding_source_identities rho source target names _ names
      (correspondence_embedding _ _ _ _ Correspondence) Consistent).
Qed.
