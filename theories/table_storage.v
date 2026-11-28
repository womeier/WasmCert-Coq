(** Compact, persistent table entries. Runs represent repeated references
    without allocating one host cell per logical entry. The list view is a
    proof/printing interface only; execution uses size/get/set/all below. *)
From Stdlib Require Import List Arith NArith Lia.
From mathcomp Require Import ssreflect ssrnat ssrbool seq.
Set Implicit Arguments.

Module TableStorage.

(** Binary arithmetic is intentional: some legacy nat aliases extract to
    unary-recursive code despite the arbitrary-precision nat representation. *)
Definition count_add n m := N.to_nat (N.add (N.of_nat n) (N.of_nat m)).
Definition count_sub n m := N.to_nat (N.sub (N.of_nat n) (N.of_nat m)).
Definition count_lt n m := N.ltb (N.of_nat n) (N.of_nat m).

Lemma count_add_spec n m : count_add n m = Nat.add n m.
Proof. unfold count_add. now rewrite Nnat.N2Nat.inj_add !Nnat.Nat2N.id. Qed.
Lemma count_sub_spec n m : count_sub n m = Nat.sub n m.
Proof. unfold count_sub. now rewrite Nnat.N2Nat.inj_sub !Nnat.Nat2N.id. Qed.
Lemma count_lt_spec n m : count_lt n m = Nat.ltb n m.
Proof.
  unfold count_lt.
  destruct (N.ltb_spec0 (N.of_nat n) (N.of_nat m));
    destruct (Nat.ltb_spec0 n m); try reflexivity; lia.
Qed.

Arguments count_add n m : simpl never.
Arguments count_sub n m : simpl never.
Arguments count_lt n m : simpl never.

Record entries (A: Type) := { runs : list (nat * A) }.
Arguments runs {A}.

Fixpoint flatten_runs {A} (rs: list (nat * A)) : list A :=
  match rs with
  | nil => nil
  | (n, v) :: rest => List.repeat v n ++ flatten_runs rest
  end.

Definition to_list {A} (t: entries A) : list A := flatten_runs (runs t).
Coercion to_list : entries >-> list.

Definition empty {A} : entries A := {| runs := nil |}.
Definition repeat {A} (n: nat) (v: A) : entries A :=
  {| runs := (n, v) :: nil |}.
Definition append {A} (t u: entries A) : entries A :=
  {| runs := runs t ++ runs u |}.

Fixpoint size_runs {A} (rs: list (nat * A)) : nat :=
  match rs with nil => 0 | (n, _) :: rest => count_add n (size_runs rest) end.
Definition size {A} (t: entries A) := size_runs (runs t).

Fixpoint get_runs {A} (rs: list (nat * A)) (i: nat) : option A :=
  match rs with
  | nil => None
  | (n, v) :: rest =>
      if count_lt i n then Some v else get_runs rest (count_sub i n)
  end.
Definition get {A} (t: entries A) i := get_runs (runs t) i.

Definition cons_run {A} n (v: A) rest :=
  match n with 0 => rest | S _ => (n, v) :: rest end.

Fixpoint set_runs {A} (rs: list (nat * A)) (i: nat) (v: A) :=
  match rs with
  | nil => nil
  | (n, old) :: rest =>
      if count_lt i n then
        cons_run i old ((1, v) :: cons_run (count_sub n (S i)) old rest)
      else (n, old) :: set_runs rest (count_sub i n) v
  end.
Definition set {A} (t: entries A) i v : entries A :=
  {| runs := set_runs (runs t) i v |}.

Definition all {A} (p: A -> bool) (t: entries A) : bool :=
  List.forallb (fun '(n, v) => orb (Nat.eqb n 0) (p v)) (runs t).

Lemma size_spec {A} (t: entries A) :
  size t = List.length (to_list t).
Proof.
  destruct t as [rs]; unfold size, to_list; simpl.
  induction rs as [|[n v] rs IH]; simpl; first reflexivity.
  now rewrite count_add_spec List.length_app List.repeat_length IH.
Qed.

Lemma repeat_spec {A} n (v: A) : to_list (repeat n v) = List.repeat v n.
Proof. unfold to_list, repeat; simpl. now rewrite cats0. Qed.

Lemma empty_spec {A} : to_list (@empty A) = nil.
Proof. reflexivity. Qed.

Lemma append_spec {A} (t u: entries A) :
  to_list (append t u) = to_list t ++ to_list u.
Proof.
  destruct t as [rs], u as [us]; unfold to_list, append; simpl.
  induction rs as [|[n v] rs IH]; simpl; first reflexivity.
  now rewrite IH catA.
Qed.

Lemma repeat_get {A} n i (v: A) :
  (i < n)%coq_nat -> List.nth_error (List.repeat v n) i = Some v.
Proof.
  revert i; induction n; intros [|i] H; simpl in *; try lia; auto.
  apply IHn. lia.
Qed.

Lemma get_spec {A} (t: entries A) i :
  get t i = List.nth_error (to_list t) i.
Proof.
  destruct t as [rs]; unfold get, to_list; simpl; revert i.
  induction rs as [|[n v] rs IH]; intros i; simpl.
  - now destruct i.
  - rewrite count_lt_spec count_sub_spec.
    destruct (Nat.ltb i n) eqn:H.
    + apply Nat.ltb_lt in H.
      rewrite List.nth_error_app1; last now rewrite List.repeat_length.
      symmetry. now apply repeat_get.
    + apply Nat.ltb_ge in H.
      rewrite List.nth_error_app2; last now rewrite List.repeat_length.
      now rewrite List.repeat_length IH.
Qed.

Lemma cons_run_spec {A} n (v: A) rs :
  flatten_runs (cons_run n v rs) = List.repeat v n ++ flatten_runs rs.
Proof. destruct n; reflexivity. Qed.

Lemma set_nth_repeat {A} n i (old v: A) tail :
  (i < n)%coq_nat ->
  set_nth v (List.repeat old n ++ tail) i v =
    List.repeat old i ++ v :: (List.repeat old (Nat.sub n (S i)) ++ tail).
Proof.
  revert i; induction n; intros [|i] H; simpl in *; try lia.
  - now rewrite Nat.sub_0_r.
  - f_equal. apply IHn. lia.
Qed.

Lemma set_nth_app_ge {A} (xs ys: list A) i (v: A) :
  (List.length xs <= i)%coq_nat ->
  set_nth v (xs ++ ys) i v =
    xs ++ set_nth v ys (Nat.sub i (List.length xs)) v.
Proof.
  revert i; induction xs; intros [|i] H; simpl in *; try lia; auto.
  f_equal. apply IHxs. lia.
Qed.

Lemma set_spec {A} (t: entries A) i v :
  (i < size t)%coq_nat ->
  to_list (set t i v) = set_nth v (to_list t) i v.
Proof.
  destruct t as [rs]; unfold set, to_list, size; simpl; revert i.
  induction rs as [|[n old] rs IH]; intros i H; simpl in *; first lia.
  rewrite count_add_spec in H.
  rewrite count_lt_spec !count_sub_spec.
  destruct (Nat.ltb i n) eqn:Hi.
  - apply Nat.ltb_lt in Hi.
    rewrite cons_run_spec /= cons_run_spec.
    now rewrite set_nth_repeat.
  - apply Nat.ltb_ge in Hi.
    rewrite set_nth_app_ge; last now rewrite List.repeat_length.
    rewrite List.repeat_length.
    cbn [flatten_runs].
    rewrite IH; first reflexivity.
    lia.
Qed.

Lemma all_repeat {A} (p: A -> bool) n v :
  List.forallb p (List.repeat v n) = orb (Nat.eqb n 0) (p v).
Proof.
  destruct n; simpl; first reflexivity.
  induction n; simpl; destruct (p v); simpl in *; auto.
Qed.

Lemma cons_run_size {A} n (v: A) rs :
  size_runs (cons_run n v rs) = Nat.add n (size_runs rs).
Proof. destruct n; simpl; first reflexivity. apply count_add_spec. Qed.

Lemma set_size {A} (t: entries A) i v :
  (i < size t)%coq_nat -> size (set t i v) = size t.
Proof.
  destruct t as [rs]; unfold size, set; simpl; revert i.
  induction rs as [|[n old] rs IH]; intros i H; simpl in *; first lia.
  rewrite count_add_spec in H.
  rewrite count_lt_spec !count_sub_spec.
  destruct (Nat.ltb i n) eqn:Hi.
  - apply Nat.ltb_lt in Hi.
    rewrite cons_run_size /= cons_run_size !count_add_spec. lia.
  - apply Nat.ltb_ge in Hi.
    cbn [size_runs]. rewrite IH; first reflexivity. lia.
Qed.

Lemma all_spec {A} (p: A -> bool) (t: entries A) :
  all p t = seq.all p (to_list t).
Proof.
  destruct t as [rs]; unfold all, to_list; simpl.
  induction rs as [|[n v] rs IH]; simpl; first reflexivity.
  rewrite all_cat -IH.
  assert (seq.all p (List.repeat v n) = List.forallb p (List.repeat v n)) as E.
  { induction (List.repeat v n); simpl; congruence. }
  now rewrite E all_repeat.
Qed.

End TableStorage.

Coercion TableStorage.to_list : TableStorage.entries >-> list.

Arguments TableStorage.size {A} t : simpl never.
Arguments TableStorage.get {A} t i : simpl never.
Arguments TableStorage.all {A} p t : simpl never.
Arguments TableStorage.to_list {A} t : simpl never.

Ltac table_storage_view :=
  repeat match goal with
  | H: context [TableStorage.size ?t] |- _ => rewrite TableStorage.size_spec in H
  | H: context [TableStorage.get ?t ?i] |- _ => rewrite TableStorage.get_spec in H
  | H: context [TableStorage.all ?p ?t] |- _ => rewrite TableStorage.all_spec in H
  | H: context [TableStorage.to_list (TableStorage.repeat ?n ?v)] |- _ =>
      rewrite TableStorage.repeat_spec in H
  | H: context [TableStorage.to_list (TableStorage.append ?t ?u)] |- _ =>
      rewrite TableStorage.append_spec in H
  | |- context [TableStorage.size ?t] => rewrite TableStorage.size_spec
  | |- context [TableStorage.get ?t ?i] => rewrite TableStorage.get_spec
  | |- context [TableStorage.all ?p ?t] => rewrite TableStorage.all_spec
  | |- context [TableStorage.to_list (TableStorage.repeat ?n ?v)] =>
      rewrite TableStorage.repeat_spec
  | |- context [TableStorage.to_list (TableStorage.append ?t ?u)] =>
      rewrite TableStorage.append_spec
  end.
