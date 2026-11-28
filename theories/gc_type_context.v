(** Canonical closed recursive type groups.

    Source HT_type indices are resolved relative to a module's prior groups
    or normalized to a current-group binder. Registry identities are pairs
    (group, member), not source indices. The registry interns the entire
    normalized recursive group, preserving its member order.

    Closing and declaration validation are distinct phases: these operations
    check index scope and acyclic single-supertype syntax, but do not claim
    structural compatibility/finality validation of a declared supertype.
    The legacy module validator must not use closing alone as validation. *)
From Wasm Require Import datatypes_properties list_extra.
From Stdlib Require Import List NArith Bool Lia Relations Relation_Operators.
Import ListNotations.

Scheme Equality for defined_type.
Scheme Equality for closed_type_use.
Scheme Equality for closed_heap_type.
Scheme Equality for closed_value_type.

Definition closed_function_type_eq_dec (a b : closed_function_type) :
    {a = b} + {a <> b}.
Proof. decide equality; apply List.list_eq_dec; apply closed_value_type_eq_dec. Defined.

Definition closed_storage_type_eq_dec
    (a b : storage_type closed_value_type) : {a = b} + {a <> b}.
Proof. decide equality; [apply closed_value_type_eq_dec | apply gc_packed_type_eq_dec]. Defined.

Definition closed_field_type_eq_dec
    (a b : field_type closed_value_type) : {a = b} + {a <> b}.
Proof. decide equality; [apply closed_storage_type_eq_dec | apply mutability_eq_dec]. Defined.

Definition closed_composite_type_eq_dec
    (a b : composite_type closed_value_type closed_function_type) :
    {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply closed_function_type_eq_dec.
  - apply List.list_eq_dec. apply closed_field_type_eq_dec.
  - apply closed_field_type_eq_dec.
Defined.

Definition closed_subtype_eq_dec (a b : closed_subtype) : {a = b} + {a <> b}.
Proof.
  decide equality.
  - apply closed_composite_type_eq_dec.
  - apply List.list_eq_dec. apply closed_type_use_eq_dec.
  - decide equality.
Defined.

Definition canonical_group_eq_dec (a b : canonical_group) : {a = b} + {a <> b} :=
  List.list_eq_dec closed_subtype_eq_dec a b.

Definition canonical_group_eqb (a b : canonical_group) : bool :=
  if canonical_group_eq_dec a b then true else false.

Definition defined_type_eqb (a b : defined_type) : bool :=
  if defined_type_eq_dec a b then true else false.

Definition close_type_index (prior : list defined_type) (members : N)
    (i : typeidx) : option closed_type_use :=
  let base := N.of_nat (length prior) in
  if N.ltb i base
  then option_map CT_def (nth_error prior (N.to_nat i))
  else if N.ltb (i - base) members then Some (CT_rec (i - base)) else None.

Definition close_heap_type prior members (h : heap_type) : option closed_heap_type :=
  match h with
  | HT_type i => option_map CH_defined (close_type_index prior members i)
  | _ => Some (CH_abstract h)
  end.

Definition close_value_type prior members (v : value_type) : option closed_value_type :=
  match v with
  | T_num n => Some (CV_num n)
  | T_vec v => Some (CV_vec v)
  | T_ref r =>
      option_map (CV_ref (ref_nullable r))
        (close_heap_type prior members (ref_heap r))
  | T_bot => None
  end.

Definition close_storage_type prior members (t : storage_type value_type) :
    option (storage_type closed_value_type) :=
  match t with
  | ST_value v => option_map ST_value (close_value_type prior members v)
  | ST_packed p => Some (ST_packed p)
  end.

Definition close_field_type prior members (f : field_type value_type) :
    option (field_type closed_value_type) :=
  option_map
    (fun t => {| field_mutability := field_mutability f; field_storage := t |})
    (close_storage_type prior members (field_storage f)).

Definition close_function_type prior members (f : function_type) :
    option closed_function_type :=
  let '(Tf args results) := f in
  match those0 (map (close_value_type prior members) args),
        those0 (map (close_value_type prior members) results) with
  | Some args, Some results => Some (Closed_ft args results)
  | _, _ => None
  end.

Definition close_composite_type prior members
    (c : composite_type value_type function_type) :
    option (composite_type closed_value_type closed_function_type) :=
  match c with
  | Comp_func f => option_map (@Comp_func closed_value_type closed_function_type)
      (close_function_type prior members f)
  | Comp_struct fs =>
      option_map (@Comp_struct closed_value_type closed_function_type)
        (those0 (map (close_field_type prior members) fs))
  | Comp_array f => option_map (@Comp_array closed_value_type closed_function_type)
      (close_field_type prior members f)
  end.

Definition close_subtype prior members offset (t : source_subtype) :
    option closed_subtype :=
  let supers := subtype_supers t in
  if andb (Nat.leb (length supers) 1)
      (forallb (fun i => N.ltb i (N.of_nat (length prior) + offset)) supers)
  then
    match those0 (map (close_type_index prior members) supers),
          close_composite_type prior members (subtype_composite t) with
    | Some supers, Some c => Some (Sub_type (subtype_final t) supers c)
    | _, _ => None
    end
  else None.

Fixpoint close_subtypes prior members offset (ts : recursive_type) :
    option canonical_group :=
  match ts with
  | [] => Some []
  | t :: ts =>
      match close_subtype prior members offset t,
            close_subtypes prior members (N.succ offset) ts with
      | Some t, Some ts => Some (t :: ts)
      | _, _ => None
      end
  end.

Fixpoint find_canonical_group (groups : canonical_registry) (g : canonical_group) :
    option nat :=
  match groups with
  | [] => None
  | h :: rest =>
      if canonical_group_eqb h g then Some 0
      else option_map S (find_canonical_group rest g)
  end.

Definition intern_group (groups : canonical_registry) (g : canonical_group) :
    canonical_registry * N :=
  match find_canonical_group groups g with
  | Some i => (groups, N.of_nat i)
  | None => (groups ++ [g], N.of_nat (length groups))
  end.

Definition group_defined_types (group : N) (members : nat) : list defined_type :=
  map (fun i => Def_type group (N.of_nat i)) (seq 0 members).

Definition close_type_group (groups : canonical_registry) (prior : list defined_type)
    (source : recursive_type) : option (canonical_registry * list defined_type) :=
  match close_subtypes prior (N.of_nat (length source)) 0 source with
  | None => None
  | Some group =>
      let '(groups', addr) := intern_group groups group in
      Some (groups', group_defined_types addr (length group))
  end.

Fixpoint close_type_groups_from (groups : canonical_registry)
    (prior : list defined_type) (source : list recursive_type) :
    option (canonical_registry * list defined_type) :=
  match source with
  | [] => Some (groups, prior)
  | group :: rest =>
      match close_type_group groups prior group with
      | None => None
      | Some (groups', types) => close_type_groups_from groups' (prior ++ types) rest
      end
  end.

Definition resolve_type_use (self : defined_type) (u : closed_type_use) : defined_type :=
  match u with
  | CT_rec i => Def_type (defined_group self) i
  | CT_def t => t
  end.

Definition expand_heap_type self (h : closed_heap_type) : closed_heap_type :=
  match h with
  | CH_abstract h => CH_abstract h
  | CH_defined u => CH_defined (CT_def (resolve_type_use self u))
  end.

Definition expand_value_type self (v : closed_value_type) : closed_value_type :=
  match v with
  | CV_num n => CV_num n
  | CV_vec v => CV_vec v
  | CV_ref n h => CV_ref n (expand_heap_type self h)
  end.

Definition expand_storage_type self (t : storage_type closed_value_type) :=
  match t with
  | ST_value v => ST_value (expand_value_type self v)
  | ST_packed p => ST_packed p
  end.

Definition expand_field_type self (f : field_type closed_value_type) :=
  {| field_mutability := field_mutability f;
     field_storage := expand_storage_type self (field_storage f) |}.

Definition expand_composite_type self
    (c : composite_type closed_value_type closed_function_type) :=
  match c with
  | Comp_func (Closed_ft args results) =>
      Comp_func (Closed_ft (map (expand_value_type self) args)
        (map (expand_value_type self) results))
  | Comp_struct fs => Comp_struct (map (expand_field_type self) fs)
  | Comp_array f => Comp_array (expand_field_type self f)
  end.

Definition expand_subtype self (t : closed_subtype) : closed_subtype :=
  Sub_type (subtype_final t)
    (map (fun u => CT_def (resolve_type_use self u)) (subtype_supers t))
    (expand_composite_type self (subtype_composite t)).

Definition lookup_defined_type (groups : canonical_registry) (t : defined_type) :
    option closed_subtype :=
  match nth_error groups (N.to_nat (defined_group t)) with
  | None => None
  | Some group => nth_error group (N.to_nat (defined_member t))
  end.

Definition expand_defined_type groups t : option closed_subtype :=
  option_map (expand_subtype t) (lookup_defined_type groups t).

Definition expand_function_type groups t : option closed_function_type :=
  match expand_defined_type groups t with
  | Some st =>
      match subtype_composite st with
      | Comp_func f => Some f
      | _ => None
      end
  | None => None
  end.

Definition expand_struct_type groups t : option (list (field_type closed_value_type)) :=
  match expand_defined_type groups t with
  | Some st =>
      match subtype_composite st with
      | Comp_struct fs => Some fs
      | _ => None
      end
  | None => None
  end.

Definition expand_array_type groups t : option (field_type closed_value_type) :=
  match expand_defined_type groups t with
  | Some st =>
      match subtype_composite st with
      | Comp_array f => Some f
      | _ => None
      end
  | None => None
  end.

Definition declared_type_step groups (a b : defined_type) : Prop :=
  exists st, expand_defined_type groups a = Some st /\
    In (CT_def b) (subtype_supers st).

Inductive declared_type_path groups : nat -> defined_type -> defined_type -> Prop :=
| dtp_refl : forall a, declared_type_path groups 0 a a
| dtp_step : forall n a b c,
    declared_type_step groups a b ->
    declared_type_path groups n b c ->
    declared_type_path groups (S n) a c.

Fixpoint defined_type_matches_fuel fuel groups (a b : defined_type) : bool :=
  if defined_type_eqb a b then true
  else
    match fuel with
    | O => false
    | S fuel =>
        match expand_defined_type groups a with
        | None => false
        | Some st =>
            existsb
              (fun parent =>
                match parent with
                | CT_def p => defined_type_matches_fuel fuel groups p b
                | CT_rec _ => false
                end)
              (subtype_supers st)
        end
    end.

Definition canonical_registry_size (groups : canonical_registry) : nat :=
  fold_right (fun g size => length g + size) 0 groups.

Definition defined_type_matches groups a b :=
  defined_type_matches_fuel (canonical_registry_size groups) groups a b.

Definition defined_type_equiv groups a b :=
  andb (defined_type_matches groups a b) (defined_type_matches groups b a).

Definition defined_type_rank (groups : canonical_registry) (t : defined_type) : nat :=
  canonical_registry_size (firstn (N.to_nat (defined_group t)) groups) +
    N.to_nat (defined_member t).

Definition defined_type_validb groups t : bool :=
  match lookup_defined_type groups t with Some _ => true | None => false end.

(** Validate the finite declared-supertype graph independently of structural
    compatibility/finality validation. Every parent must be present and have
    a strictly smaller registry rank. This makes the public matcher's finite
    bound complete, rather than merely a sound approximation. *)
Definition canonical_registry_super_orderedb (groups : canonical_registry) : bool :=
  forallb
    (fun gi =>
      match nth_error groups gi with
      | None => false
      | Some group =>
          forallb
            (fun mi =>
              match nth_error group mi with
              | None => false
              | Some st =>
                  let self := Def_type (N.of_nat gi) (N.of_nat mi) in
                  forallb
                    (fun u =>
                      let parent := resolve_type_use self u in
                      andb (defined_type_validb groups parent)
                        (Nat.ltb (defined_type_rank groups parent)
                          (defined_type_rank groups self)))
                    (subtype_supers st)
              end)
            (seq 0 (length group))
      end)
    (seq 0 (length groups)).

Definition close_type_groups groups source :
    option (canonical_registry * list defined_type) :=
  match close_type_groups_from groups [] source with
  | None => None
  | Some (registry, types) =>
      if canonical_registry_super_orderedb registry
      then Some (registry, types) else None
  end.
