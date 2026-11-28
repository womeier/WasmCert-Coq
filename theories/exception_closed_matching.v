(** Agreement of the production EH matcher with GC's shared closed matcher.
    This does not introduce runtime descriptors or a second classifier.
    The indexed-payload bridge belongs to the GC-owned closed runtime wiring. *)
From Wasm Require Import typing subtyping_properties gc_type_context
  gc_declaration_typing.
From Stdlib Require Import List NArith.
From mathcomp Require Import ssreflect ssrbool.
Import ListNotations.
Open Scope N_scope.

Lemma exception_reference_closing names r :
  exception_heap (ref_heap r) ->
  close_value_type names 0 (T_ref r) =
    Some (CV_ref (ref_nullable r) (CH_abstract (ref_heap r))).
Proof. destruct r as [nullable h]; destruct h => //. Qed.

Lemma exception_closed_reference_match registry r1 r2 :
  exception_heap (ref_heap r1) ->
  closed_value_matchesb registry
    (CV_ref (ref_nullable r1) (CH_abstract (ref_heap r1)))
    (CV_ref (ref_nullable r2) (CH_abstract (ref_heap r2))) =
  reference_subtyping r1 r2.
Proof.
  destruct r1 as [n1 h1], r2 as [n2 h2].
  destruct h1, h2, n1, n2 => //.
Qed.

(** Closing against two different module maps agrees for exception types,
    since these abstract heaps contain no source-local identities. *)
Theorem exception_source_closed_matching names1 names2 registry r1 r2 t1 t2 :
  exception_heap (ref_heap r1) ->
  close_value_type names1 0 (T_ref r1) = Some t1 ->
  close_value_type names2 0 (T_ref r2) = Some t2 ->
  exception_heap (ref_heap r2) ->
  (T_ref r1 <t: T_ref r2) = closed_value_matchesb registry t1 t2.
Proof.
  move => Kind1 Close1 Close2 Kind2.
  rewrite (exception_reference_closing names1 r1 Kind1) in Close1.
  rewrite (exception_reference_closing names2 r2 Kind2) in Close2.
  injection Close1 as <-; injection Close2 as <-.
  by rewrite value_subtyping_ref exception_closed_reference_match.
Qed.

Section Host.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

(** Actual allocated exception addresses have the same type check on either
    side of the shared source/closed boundary, including nullability. *)
Theorem exception_address_closed_typing s address r :
  exception_heap (ref_heap r) ->
  value_typing s (VAL_ref (VAL_ref_exn address)) (T_ref r) =
  match lookup_N s.(s_exns) address with
  | Some _ => closed_value_matchesb s.(s_types)
      (CV_ref false (CH_abstract HT_exn))
      (CV_ref (ref_nullable r) (CH_abstract (ref_heap r)))
  | None => false
  end.
Proof.
  move => Kind.
  unfold value_typing, typeof_value, typeof_ref.
  destruct (lookup_N (s_exns s) address) => //=.
  by destruct r as [nullable h]; destruct h, nullable.
Qed.

Theorem exception_null_closed_typing s h r :
  exception_heap h ->
  value_typing s (VAL_ref (VAL_ref_null h)) (T_ref r) =
  closed_value_matchesb s.(s_types)
    (CV_ref true (CH_abstract h))
    (CV_ref (ref_nullable r) (CH_abstract (ref_heap r))).
Proof.
  move => Kind.
  unfold value_typing, typeof_value, typeof_ref => /=.
  destruct h => //.
  all: by destruct r as [nullable heap]; destruct heap, nullable.
Qed.

End Host.

Definition exception_reference_matrix_types : list reference_type :=
  [Ref_type false HT_noexn; Ref_type true HT_noexn;
   Ref_type false HT_exn; Ref_type true HT_exn].

Example main_exception_matching_all_sixteen_pairs :
  List.map (fun source =>
    List.map (reference_subtyping source) exception_reference_matrix_types)
      exception_reference_matrix_types =
  [[true; true; true; true]; [false; true; false; true];
   [false; false; true; true]; [false; false; false; true]].
Proof. reflexivity. Qed.

Example incomparable_exception_meet :
  t_inf (T_ref (Ref_type true HT_noexn))
    (T_ref (Ref_type false HT_exn)) =
  T_ref (Ref_type false HT_noexn).
Proof. reflexivity. Qed.

Example incomparable_exception_join :
  t_sup (T_ref (Ref_type true HT_noexn))
    (T_ref (Ref_type false HT_exn)) =
  Some (T_ref (Ref_type true HT_exn)).
Proof. reflexivity. Qed.
