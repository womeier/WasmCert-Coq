From Wasm Require Import datatypes_properties.
From mathcomp Require Import ssreflect eqtype ssrbool seq ssrnat.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

(** Core subtyping includes bottom and same-heap reference nullability.
    Declared/recursive heap matching is supplied by the shared type layer;
    module-local indices are not global runtime identities. **)
Section Subtyping.

(* Shared validation entry point. This profile implements same-heap
   nullability matching. The explicit declaration context is the boundary
   at which recursive/declared matching must be added;
   a source HT_type index is not a closed runtime identity. *)
Definition reference_type_match (_C : type_context)
    (t1 t2 : reference_type) : bool :=
  (ref_heap t1 == ref_heap t2) &&
    (negb (ref_nullable t1) || ref_nullable t2).

Definition value_subtyping (t1: value_type) (t2: value_type) : bool :=
  (t1 == t2) || (t1 == T_bot) ||
  match t1, t2 with
  | T_ref r1, T_ref r2 => reference_type_match nil r1 r2
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

(* Within the same-heap profile, comparable types have their meet/join
   selected by subtyping. Unrelated types have bottom/no join respectively. *)
Section Lattice.
  
  Definition t_inf (t1 t2: value_type) : value_type :=
    if (t1 <t: t2) then t1
    else if (t2 <t: t1) then t2 else T_bot.

  Definition t_sup (t1 t2: value_type) : option value_type :=
    if (t1 <t: t2) then Some t2
    else if (t2 <t: t1) then Some t1 else None.

  Definition ts_inf (ts1 ts2: list value_type) : option (list value_type) :=
    if (List.length ts1 == List.length ts2) then
      Some (map (fun '(t1, t2) => t_inf t1 t2) (List.combine ts1 ts2))
    else
      None.
  
End Lattice.
