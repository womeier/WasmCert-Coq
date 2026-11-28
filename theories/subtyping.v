From Wasm Require Import datatypes_properties.
From mathcomp Require Import ssreflect eqtype ssrbool seq ssrnat.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

(** Main matching includes the independent final exception hierarchy and its
    nullability order. Other hierarchies retain the existing exact-match
    profile until their shared declared-type integration. Source HT_type
    indices are not canonical runtime identities. *)
Section Subtyping.

Definition exception_heap (h: heap_type) : bool :=
  match h with HT_exn | HT_noexn => true | _ => false end.

Definition exception_heap_subtyping (h1 h2: heap_type) : bool :=
  match h1, h2 with
  | HT_exn, HT_exn | HT_noexn, HT_exn | HT_noexn, HT_noexn => true
  | _, _ => false
  end.

Definition exception_reference_subtyping (r1 r2: reference_type) : bool :=
  exception_heap_subtyping (ref_heap r1) (ref_heap r2) &&
    (negb (ref_nullable r1) || ref_nullable r2).

Definition reference_subtyping (r1 r2: reference_type) : bool :=
  (r1 == r2) || exception_reference_subtyping r1 r2.

(* The context parameter is retained for canonical declared-type matching. *)
Definition reference_type_match (_C : type_context)
    (t1 t2 : reference_type) : bool :=
  reference_subtyping t1 t2.

Definition value_subtyping (t1: value_type) (t2: value_type) : bool :=
  (t1 == t2) || (t1 == T_bot) ||
  match t1, t2 with
  | T_ref r1, T_ref r2 => exception_reference_subtyping r1 r2
  | _, _ => false
  end.

Definition values_subtyping (ts1: list value_type) (ts2: list value_type) : bool :=
  all2 value_subtyping ts1 ts2.

(** Function subtyping and instruction subtyping are covariant on the types
produced and contravariant on the types consumed.
**)
Definition func_subtyping (tf tf': function_type) : bool :=
  let '(Tf ts1 ts2) := tf in
  let '(Tf ts1' ts2') := tf' in
    values_subtyping ts1' ts1 &&
    values_subtyping ts2 ts2'.

Definition instr_subtyping (tf tf': function_type) : Prop :=
  let '(Tf ts1 ts2) := tf in
  let '(Tf ts1' ts2') := tf' in
  exists ts ts' ts1_sub ts2_sub,
    ts1' = ts ++ ts1_sub /\
    ts2' = ts' ++ ts2_sub /\
    values_subtyping ts ts' /\  
    values_subtyping ts1_sub ts1 /\
    values_subtyping ts2 ts2_sub.

End Subtyping.

Notation "t1 <t: t2" := (value_subtyping t1 t2) (at level 30).
Notation "ts1 <ts: ts2" := (values_subtyping ts1 ts2) (at level 60).
Notation "tf1 <ti: tf2" := (instr_subtyping tf1 tf2) (at level 60).
Notation "tf1 <tf: tf2" := (func_subtyping tf1 tf2) (at level 60).

(* Meet/join of exception references is the product of nullability and the
   two-element exception heap chain. Other types keep their existing lattice. *)
Section Lattice.
  
  Definition t_inf (t1 t2: value_type) : value_type :=
    if (t1 == t2) then t1 else
    match t1, t2 with
    | T_ref r1, T_ref r2 =>
        if exception_heap (ref_heap r1) && exception_heap (ref_heap r2) then
          T_ref (Ref_type (ref_nullable r1 && ref_nullable r2)
            (match ref_heap r1, ref_heap r2 with
             | HT_exn, HT_exn => HT_exn | _, _ => HT_noexn end))
        else T_bot
    | _, _ => T_bot
    end.

  Definition t_sup (t1 t2: value_type) : option value_type :=
    if (t1 == T_bot) then Some t2
    else if (t2 == T_bot) then Some t1
         else if (t1 == t2) then Some t1 else
    match t1, t2 with
    | T_ref r1, T_ref r2 =>
        if exception_heap (ref_heap r1) && exception_heap (ref_heap r2) then
          Some (T_ref (Ref_type (ref_nullable r1 || ref_nullable r2)
            (match ref_heap r1, ref_heap r2 with
             | HT_noexn, HT_noexn => HT_noexn | _, _ => HT_exn end)))
        else None
    | _, _ => None
    end.

  Definition ts_inf (ts1 ts2: list value_type) : option (list value_type) :=
    if (List.length ts1 == List.length ts2) then
      Some (map (fun '(t1, t2) => t_inf t1 t2) (List.combine ts1 ts2))
    else
      None.
  
End Lattice.
