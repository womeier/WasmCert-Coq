(** Structural validation of closed GC declarations.
    Closing/index normalization and this validation are separate: a declared
    edge is checked for parent finality and composite-type compatibility.
    In-group references have been resolved by expand_defined_type before
    structural checking, so CT_rec is not accepted as an operational type. *)
From Wasm Require Import datatypes_properties gc_types gc_type_context.
From Stdlib Require Import List Bool NArith.
Import ListNotations.

Definition abstract_heap_matchesb (a b : heap_type) : bool :=
  match a, b with
  | HT_exn, HT_exn | HT_noexn, HT_exn | HT_noexn, HT_noexn => true
  | _, _ =>
      match abstract_reference_of_legacy (Ref_type false a),
            abstract_reference_of_legacy (Ref_type false b) with
      | Some a, Some b => abstract_heap_subtyping (art_heap a) (art_heap b)
      | _, _ => false
      end
  end.

Definition defined_heap_kind groups t : option heap_type :=
  match expand_defined_type groups t with
  | None => None
  | Some st =>
      Some
        (match subtype_composite st with
         | Comp_func _ => HT_func
         | Comp_struct _ => HT_struct
         | Comp_array _ => HT_array
         end)
  end.

Definition bottom_matches_definedb (bottom kind : heap_type) : bool :=
  match bottom, kind with
  | HT_nofunc, HT_func | HT_none, HT_struct | HT_none, HT_array => true
  | _, _ => false
  end.

Definition closed_heap_matchesb groups (a b : closed_heap_type) : bool :=
  match a, b with
  | CH_abstract a, CH_abstract b => abstract_heap_matchesb a b
  | CH_defined (CT_def a), CH_defined (CT_def b) => defined_type_matches groups a b
  | CH_defined (CT_def a), CH_abstract b =>
      match defined_heap_kind groups a with
      | Some kind => abstract_heap_matchesb kind b
      | None => false
      end
  | CH_abstract a, CH_defined (CT_def b) =>
      match defined_heap_kind groups b with
      | Some kind => bottom_matches_definedb a kind
      | None => false
      end
  | _, _ => false
  end.

Definition closed_value_matchesb groups (a b : closed_value_type) : bool :=
  match a, b with
  | CV_num a, CV_num b => number_type_beq a b
  | CV_vec _, CV_vec _ => true
  | CV_ref na ha, CV_ref nb hb => implb na nb && closed_heap_matchesb groups ha hb
  | _, _ => false
  end.

Definition closed_value_eqb (a b : closed_value_type) : bool :=
  if closed_value_type_eq_dec a b then true else false.

Definition closed_field_matchesb groups :=
  @gc_types.field_matchesb closed_value_type
    (closed_value_matchesb groups) closed_value_eqb.

Fixpoint declaration_list_matchesb {A} (f : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => f x y && declaration_list_matchesb f xs ys
  | _, _ => false
  end.

Definition closed_composite_matchesb groups
    (a b : composite_type closed_value_type closed_function_type) : bool :=
  match a, b with
  | Comp_func (Closed_ft aa ar), Comp_func (Closed_ft ba br) =>
      declaration_list_matchesb (closed_value_matchesb groups) ba aa &&
      declaration_list_matchesb (closed_value_matchesb groups) ar br
  | Comp_struct a, Comp_struct b =>
      declaration_list_matchesb (closed_field_matchesb groups) (firstn (length b) a) b
  | Comp_array a, Comp_array b => closed_field_matchesb groups a b
  | _, _ => false
  end.

Definition abstract_heap_validb (h : heap_type) : bool :=
  match h with HT_type _ => false | _ => true end.

Definition closed_value_validb groups (v : closed_value_type) : bool :=
  match v with
  | CV_num _ | CV_vec _ => true
  | CV_ref _ (CH_abstract h) => abstract_heap_validb h
  | CV_ref _ (CH_defined (CT_def t)) => defined_type_validb groups t
  | CV_ref _ (CH_defined (CT_rec _)) => false
  end.

Definition closed_storage_validb groups (t : storage_type closed_value_type) : bool :=
  match t with
  | ST_value v => closed_value_validb groups v
  | ST_packed _ => true
  end.

Definition closed_composite_validb groups
    (c : composite_type closed_value_type closed_function_type) : bool :=
  match c with
  | Comp_func (Closed_ft args results) =>
      forallb (closed_value_validb groups) args &&
      forallb (closed_value_validb groups) results
  | Comp_struct fields =>
      forallb (fun f => closed_storage_validb groups (field_storage f)) fields
  | Comp_array f => closed_storage_validb groups (field_storage f)
  end.

Definition closed_parent_validb groups child (u : closed_type_use) : bool :=
  match u with
  | CT_rec _ => false
  | CT_def t =>
      match expand_defined_type groups t with
      | None => false
      | Some parent =>
          negb (subtype_final parent) &&
          closed_composite_matchesb groups child (subtype_composite parent)
      end
  end.

Definition defined_declaration_validb groups t : bool :=
  match expand_defined_type groups t with
  | None => false
  | Some st =>
      Nat.leb (length (subtype_supers st)) 1 &&
      closed_composite_validb groups (subtype_composite st) &&
      forallb (closed_parent_validb groups (subtype_composite st)) (subtype_supers st)
  end.

Fixpoint canonical_registry_nodupb (groups : canonical_registry) : bool :=
  match groups with
  | [] => true
  | head :: tail =>
      forallb (fun g => negb (canonical_group_eqb head g)) tail &&
      canonical_registry_nodupb tail
  end.

Definition canonical_registry_validb groups : bool :=
  canonical_registry_nodupb groups &&
  canonical_registry_super_orderedb groups &&
  forallb
    (fun gi =>
      match nth_error groups gi with
      | None => false
      | Some group =>
          forallb
            (fun mi => defined_declaration_validb groups
              (Def_type (N.of_nat gi) (N.of_nat mi)))
            (seq 0 (length group))
      end)
    (seq 0 (length groups)).

Definition close_and_validate_type_groups groups source :
    option (canonical_registry * list defined_type) :=
  match close_type_groups groups source with
  | None => None
  | Some (groups, types) =>
      if canonical_registry_validb groups then Some (groups, types) else None
  end.

(** Binary function declarations are singleton final recursive groups.
    This embedding is the migration path for the existing function-only
    module section; explicit recursive/aggregate syntax uses the same closer. *)
Definition function_type_groups (types : list function_type) : list recursive_type :=
  map (fun f => [Sub_type true [] (Comp_func f)]) types.

Definition close_reference_type names (source : reference_type) : option closed_reference_type :=
  option_map (Closed_ref source.(ref_nullable)) (close_heap_type names 0 source.(ref_heap)).

Definition close_table_type names (source : table_type) : option closed_table_type :=
  option_map (Build_table_type source.(tt_limits))
    (close_reference_type names source.(tt_elem_type)).

Definition close_global_type names (source : global_type) : option closed_global_type :=
  option_map (Build_global_type source.(tg_mut)) (close_value_type names 0 source.(tg_t)).

(** Source signatures are closed using the whole instance's identity map.
    Checking the resulting expansion makes the legacy signature view and
    the canonical runtime view agree; no source index is a runtime identity. *)
Definition function_type_identityb registry names source id : bool :=
  match close_function_type names 0 source, expand_function_type registry id with
  | Some expected, Some actual =>
      if closed_function_type_eq_dec expected actual then true else false
  | _, _ => false
  end.

Fixpoint function_type_identitiesb registry names
    (sources : list function_type) (ids : list defined_type) : bool :=
  match sources, ids with
  | [], [] => true
  | f :: fs, id :: ids =>
      function_type_identityb registry names f id &&
      function_type_identitiesb registry names fs ids
  | _, _ => false
  end.

Definition source_type_identityb registry names source id : bool :=
  match close_subtype names 0 0 source, expand_defined_type registry id with
  | Some expected, Some actual =>
      if closed_subtype_eq_dec expected actual then true else false
  | _, _ => false
  end.

Fixpoint source_type_identitiesb registry names
    (sources : type_context) (ids : list defined_type) : bool :=
  match sources, ids with
  | [], [] => true
  | source :: sources, id :: ids =>
      source_type_identityb registry names source id &&
      source_type_identitiesb registry names sources ids
  | _, _ => false
  end.

(** Declarative matching reuses the independent abstract hierarchy. Exception
    heaps add their separate bottom edge; source indices have no abstract rule. *)
Inductive shared_abstract_heap_matches : heap_type -> heap_type -> Prop :=
| sahm_gc : forall a b,
    abstract_heap_matches a b ->
    shared_abstract_heap_matches (shared_heap_of_abstract a) (shared_heap_of_abstract b)
| sahm_exn : shared_abstract_heap_matches HT_exn HT_exn
| sahm_noexn : shared_abstract_heap_matches HT_noexn HT_noexn
| sahm_noexn_exn : shared_abstract_heap_matches HT_noexn HT_exn.

Inductive bottom_matches_defined : heap_type -> heap_type -> Prop :=
| bmd_func : bottom_matches_defined HT_nofunc HT_func
| bmd_struct : bottom_matches_defined HT_none HT_struct
| bmd_array : bottom_matches_defined HT_none HT_array.

Inductive closed_heap_matches groups : closed_heap_type -> closed_heap_type -> Prop :=
| chm_abstract : forall a b,
    shared_abstract_heap_matches a b ->
    closed_heap_matches groups (CH_abstract a) (CH_abstract b)
| chm_defined : forall a b n,
    declared_type_path groups n a b ->
    closed_heap_matches groups (CH_defined (CT_def a)) (CH_defined (CT_def b))
| chm_defined_abstract : forall a b kind,
    defined_heap_kind groups a = Some kind ->
    shared_abstract_heap_matches kind b ->
    closed_heap_matches groups (CH_defined (CT_def a)) (CH_abstract b)
| chm_bottom_defined : forall a b kind,
    defined_heap_kind groups b = Some kind ->
    bottom_matches_defined a kind ->
    closed_heap_matches groups (CH_abstract a) (CH_defined (CT_def b)).

Inductive closed_value_matches groups : closed_value_type -> closed_value_type -> Prop :=
| cvm_num : forall n, closed_value_matches groups (CV_num n) (CV_num n)
| cvm_vec : forall v, closed_value_matches groups (CV_vec v) (CV_vec v)
| cvm_ref : forall na nb ha hb,
    (na = false \/ nb = true) ->
    closed_heap_matches groups ha hb ->
    closed_value_matches groups (CV_ref na ha) (CV_ref nb hb).

Definition closed_field_matches groups :=
  @gc_types.field_matches closed_value_type (closed_value_matches groups).

Inductive closed_composite_matches groups :
    composite_type closed_value_type closed_function_type ->
    composite_type closed_value_type closed_function_type -> Prop :=
| ccm_func : forall aa ar ba br,
    Forall2 (closed_value_matches groups) ba aa ->
    Forall2 (closed_value_matches groups) ar br ->
    closed_composite_matches groups
      (Comp_func (Closed_ft aa ar)) (Comp_func (Closed_ft ba br))
| ccm_struct : forall a b,
    Forall2 (closed_field_matches groups) (firstn (length b) a) b ->
    closed_composite_matches groups (Comp_struct a) (Comp_struct b)
| ccm_array : forall a b,
    closed_field_matches groups a b ->
    closed_composite_matches groups (Comp_array a) (Comp_array b).

Inductive closed_value_valid groups : closed_value_type -> Prop :=
| cvv_num : forall n, closed_value_valid groups (CV_num n)
| cvv_vec : forall v, closed_value_valid groups (CV_vec v)
| cvv_abstract : forall n h,
    (forall i, h <> HT_type i) ->
    closed_value_valid groups (CV_ref n (CH_abstract h))
| cvv_defined : forall n t st,
    lookup_defined_type groups t = Some st ->
    closed_value_valid groups (CV_ref n (CH_defined (CT_def t))).

Inductive closed_storage_valid groups : storage_type closed_value_type -> Prop :=
| csv_value : forall v, closed_value_valid groups v -> closed_storage_valid groups (ST_value v)
| csv_packed : forall p, closed_storage_valid groups (ST_packed p).

Inductive closed_composite_valid groups :
    composite_type closed_value_type closed_function_type -> Prop :=
| ccv_func : forall args results,
    Forall (closed_value_valid groups) args ->
    Forall (closed_value_valid groups) results ->
    closed_composite_valid groups (Comp_func (Closed_ft args results))
| ccv_struct : forall fields,
    Forall (fun f => closed_storage_valid groups (field_storage f)) fields ->
    closed_composite_valid groups (Comp_struct fields)
| ccv_array : forall f,
    closed_storage_valid groups (field_storage f) ->
    closed_composite_valid groups (Comp_array f).

Inductive closed_parent_valid groups child : closed_type_use -> Prop :=
| cpv_parent : forall t parent,
    expand_defined_type groups t = Some parent ->
    subtype_final parent = false ->
    closed_composite_matches groups child (subtype_composite parent) ->
    closed_parent_valid groups child (CT_def t).

Definition defined_declaration_valid groups t : Prop :=
  exists st,
    expand_defined_type groups t = Some st /\
    length (subtype_supers st) <= 1 /\
    closed_composite_valid groups (subtype_composite st) /\
    Forall (closed_parent_valid groups (subtype_composite st)) (subtype_supers st).
