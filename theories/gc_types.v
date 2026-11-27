(** GC's context-independent type hierarchy.

    This file deliberately does not replace [reference_type]: that shared
    representation also needs typed function references and recursive type
    indices.  The abstract fragment here can be reused by that representation.
    In particular, [none] is NOT below [func] or [extern].

    Specification: WebAssembly Core 3.0, Types / Heap Types and
    Validation / Matching (https://www.w3.org/TR/wasm-core-3/). *)
From Wasm Require Import datatypes subtyping.
From Stdlib Require Import Bool.

Inductive abstract_heap_type : Set :=
| AH_any | AH_eq | AH_i31 | AH_struct | AH_array | AH_none
| AH_func | AH_nofunc | AH_extern | AH_noextern.

Scheme Equality for abstract_heap_type.

(** Executable matching, including reflexivity and the three disjoint
    hierarchies.  Defined types are intentionally not part of this fragment. *)
Definition abstract_heap_subtyping (a b : abstract_heap_type) : bool :=
  match a, b with
  | AH_any, AH_any
  | AH_eq, AH_eq | AH_eq, AH_any
  | AH_i31, AH_i31 | AH_i31, AH_eq | AH_i31, AH_any
  | AH_struct, AH_struct | AH_struct, AH_eq | AH_struct, AH_any
  | AH_array, AH_array | AH_array, AH_eq | AH_array, AH_any
  | AH_none, AH_none | AH_none, AH_i31 | AH_none, AH_struct
  | AH_none, AH_array | AH_none, AH_eq | AH_none, AH_any
  | AH_func, AH_func | AH_nofunc, AH_nofunc | AH_nofunc, AH_func
  | AH_extern, AH_extern | AH_noextern, AH_noextern
  | AH_noextern, AH_extern => true
  | _, _ => false
  end.

(** Declarative matching is the reflexive transitive closure of the immediate
    edges, rather than an alias for the executable check. *)
Inductive abstract_heap_matches : abstract_heap_type -> abstract_heap_type -> Prop :=
| ahm_refl : forall a, abstract_heap_matches a a
| ahm_trans : forall a b c,
    abstract_heap_matches a b -> abstract_heap_matches b c ->
    abstract_heap_matches a c
| ahm_eq_any : abstract_heap_matches AH_eq AH_any
| ahm_i31_eq : abstract_heap_matches AH_i31 AH_eq
| ahm_struct_eq : abstract_heap_matches AH_struct AH_eq
| ahm_array_eq : abstract_heap_matches AH_array AH_eq
| ahm_none_i31 : abstract_heap_matches AH_none AH_i31
| ahm_none_struct : abstract_heap_matches AH_none AH_struct
| ahm_none_array : abstract_heap_matches AH_none AH_array
| ahm_nofunc_func : abstract_heap_matches AH_nofunc AH_func
| ahm_noextern_extern : abstract_heap_matches AH_noextern AH_extern.

Lemma abstract_heap_subtyping_refl a :
  abstract_heap_subtyping a a = true.
Proof. destruct a; reflexivity. Qed.

Lemma abstract_heap_subtyping_trans a b c :
  abstract_heap_subtyping a b = true ->
  abstract_heap_subtyping b c = true ->
  abstract_heap_subtyping a c = true.
Proof. destruct a, b, c; simpl; intros; congruence. Qed.

Lemma abstract_heap_subtyping_antisym a b :
  abstract_heap_subtyping a b = true ->
  abstract_heap_subtyping b a = true -> a = b.
Proof. destruct a, b; simpl; intros; congruence. Qed.

Lemma abstract_heap_subtyping_sound a b :
  abstract_heap_subtyping a b = true -> abstract_heap_matches a b.
Proof.
  destruct a, b; simpl; intro H; try discriminate;
    eauto 4 using abstract_heap_matches.
Qed.

Lemma abstract_heap_subtyping_complete a b :
  abstract_heap_matches a b -> abstract_heap_subtyping a b = true.
Proof.
  intro H; induction H; try reflexivity.
  - apply abstract_heap_subtyping_refl.
  - eapply abstract_heap_subtyping_trans; eassumption.
Qed.

Lemma abstract_heap_subtyping_reflect a b :
  reflect (abstract_heap_matches a b) (abstract_heap_subtyping a b).
Proof.
  destruct (abstract_heap_subtyping a b) eqn:H.
  - constructor. now apply abstract_heap_subtyping_sound.
  - constructor. intro M.
    apply abstract_heap_subtyping_complete in M. congruence.
Qed.

Record abstract_reference_type : Set := {
  art_nullable : bool;
  art_heap : abstract_heap_type;
}.

Definition abstract_reference_subtyping
    (a b : abstract_reference_type) : bool :=
  implb a.(art_nullable) b.(art_nullable) &&
  abstract_heap_subtyping a.(art_heap) b.(art_heap).

Inductive abstract_reference_matches :
    abstract_reference_type -> abstract_reference_type -> Prop :=
| arm_intro : forall n1 n2 h1 h2,
    (n1 = false \/ n2 = true) ->
    abstract_heap_matches h1 h2 ->
    abstract_reference_matches
      {| art_nullable := n1; art_heap := h1 |}
      {| art_nullable := n2; art_heap := h2 |}.

Lemma abstract_reference_subtyping_correct a b :
  abstract_reference_subtyping a b = true <->
  abstract_reference_matches a b.
Proof.
  destruct a as [n1 h1], b as [n2 h2].
  unfold abstract_reference_subtyping; simpl.
  rewrite andb_true_iff.
  split.
  - intros [N H]. constructor.
    + destruct n1, n2; simpl in N; intuition discriminate.
    + now apply abstract_heap_subtyping_sound.
  - intro H. inversion H; subst. split.
    + destruct n1, n2; simpl in *; intuition discriminate.
    + now apply abstract_heap_subtyping_complete.
Qed.

Lemma abstract_reference_subtyping_refl a :
  abstract_reference_subtyping a a = true.
Proof.
  destruct a as [n h]; unfold abstract_reference_subtyping; simpl.
  rewrite abstract_heap_subtyping_refl.
  destruct n; reflexivity.
Qed.

Lemma abstract_reference_subtyping_trans a b c :
  abstract_reference_subtyping a b = true ->
  abstract_reference_subtyping b c = true ->
  abstract_reference_subtyping a c = true.
Proof.
  destruct a as [n1 h1], b as [n2 h2], c as [n3 h3].
  unfold abstract_reference_subtyping; simpl.
  rewrite !andb_true_iff.
  intros [N1 H1] [N2 H2]. split.
  - destruct n1, n2, n3; simpl in *; congruence.
  - eapply abstract_heap_subtyping_trans; eassumption.
Qed.

(** Project shared references into this abstract fragment. Exception and
    indexed heap types are outside the fragment, not aliases for a GC type. *)
Definition abstract_reference_of_legacy (t : reference_type) :
    option abstract_reference_type :=
  let heap :=
    match ref_heap t with
    | HT_func => Some AH_func | HT_extern => Some AH_extern
    | HT_any => Some AH_any | HT_eq => Some AH_eq
    | HT_i31 => Some AH_i31 | HT_struct => Some AH_struct
    | HT_array => Some AH_array | HT_none => Some AH_none
    | HT_nofunc => Some AH_nofunc | HT_noextern => Some AH_noextern
    | HT_exn | HT_noexn | HT_type _ => None
    end in
  option_map
    (fun h => {| art_nullable := ref_nullable t; art_heap := h |}) heap.

Lemma abstract_reference_legacy_conservative a b :
  (a = T_funcref \/ a = T_externref) ->
  (b = T_funcref \/ b = T_externref) ->
  exists ar br,
    abstract_reference_of_legacy a = Some ar /\
    abstract_reference_of_legacy b = Some br /\
    abstract_reference_subtyping ar br = value_subtyping (T_ref a) (T_ref b).
Proof.
  intros [-> | ->] [-> | ->];
    eexists; eexists; repeat split; reflexivity.
Qed.

(** Packed storage and fields are parameterized over the shared value-type
    representation, so they do not freeze the old Wasm 2.0 reference syntax.
    Mutable fields are invariant; immutable fields are covariant. *)
Inductive packed_type : Set := PT_i8 | PT_i16.
Scheme Equality for packed_type.

Inductive storage_type (V : Type) : Type :=
| ST_value : V -> storage_type V
| ST_packed : packed_type -> storage_type V.

Arguments ST_value {V} _.
Arguments ST_packed {V} _.

Record field_type (V : Type) : Type := {
  field_mutability : mutability;
  field_storage : storage_type V;
}.

Arguments field_mutability {V} _.
Arguments field_storage {V} _.

Section Fields.
  Context {V : Type}.
  Variable value_matches : V -> V -> Prop.

  Inductive storage_matches : storage_type V -> storage_type V -> Prop :=
  | sm_value : forall a b, value_matches a b ->
      storage_matches (ST_value a) (ST_value b)
  | sm_packed : forall p, storage_matches (ST_packed p) (ST_packed p).

  Inductive field_matches : field_type V -> field_type V -> Prop :=
  | fm_const : forall a b, storage_matches a b ->
      field_matches
        {| field_mutability := MUT_const; field_storage := a |}
        {| field_mutability := MUT_const; field_storage := b |}
  | fm_var : forall a,
      field_matches
        {| field_mutability := MUT_var; field_storage := a |}
        {| field_mutability := MUT_var; field_storage := a |}.

  Variable value_matchesb : V -> V -> bool.
  Variable value_eqb : V -> V -> bool.

  Definition storage_matchesb (a b : storage_type V) : bool :=
    match a, b with
    | ST_value x, ST_value y => value_matchesb x y
    | ST_packed x, ST_packed y => packed_type_beq x y
    | _, _ => false
    end.

  Definition storage_eqb (a b : storage_type V) : bool :=
    match a, b with
    | ST_value x, ST_value y => value_eqb x y
    | ST_packed x, ST_packed y => packed_type_beq x y
    | _, _ => false
    end.

  Definition field_matchesb (a b : field_type V) : bool :=
    match a.(field_mutability), b.(field_mutability) with
    | MUT_const, MUT_const => storage_matchesb a.(field_storage) b.(field_storage)
    | MUT_var, MUT_var => storage_eqb a.(field_storage) b.(field_storage)
    | _, _ => false
    end.

  Hypothesis value_matchesb_correct :
    forall a b, value_matchesb a b = true <-> value_matches a b.
  Hypothesis value_eqb_correct :
    forall a b, value_eqb a b = true <-> a = b.

  Lemma storage_matchesb_correct a b :
    storage_matchesb a b = true <-> storage_matches a b.
  Proof.
    destruct a as [a|a], b as [b|b]; simpl.
    - rewrite value_matchesb_correct. split; intro H.
      + now constructor.
      + now inversion H.
    - split; intro H; discriminate || inversion H.
    - split; intro H; discriminate || inversion H.
    - destruct a, b; simpl; split; intro H;
        try discriminate; try constructor; inversion H.
  Qed.

  Lemma storage_eqb_correct a b :
    storage_eqb a b = true <-> a = b.
  Proof.
    destruct a as [a|a], b as [b|b]; simpl.
    - rewrite value_eqb_correct. split; congruence.
    - split; discriminate.
    - split; discriminate.
    - destruct a, b; simpl; split; congruence.
  Qed.

  Lemma field_matchesb_correct a b :
    field_matchesb a b = true <-> field_matches a b.
  Proof.
    destruct a as [ma a], b as [mb b].
    destruct ma, mb; cbn [field_matchesb field_mutability field_storage].
    - rewrite storage_matchesb_correct.
      split; intro H; [now constructor | now inversion H].
    - split; intro H; discriminate || inversion H.
    - split; intro H; discriminate || inversion H.
    - rewrite storage_eqb_correct.
      split; intro H; [subst; constructor | now inversion H].
  Qed.
End Fields.
