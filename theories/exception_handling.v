(** Final Wasm exception-handling components.

    These components are deliberately separate from [basic_instruction] and the
    Wasm 2.0 store. In particular, [operand] is NOT a replacement for [value]:
    integration must use the shared nullable heap-reference representation.
    Payloads are polymorphic so exceptions can contain exception references.

    Catch labels are relative to the context OUTSIDE the try_table, not to its
    body's implicit label. There are no legacy try/catch/rethrow instructions.
    See core/exec/instructions.html#exception-instructions. *)
From Stdlib Require Import List NArith PeanoNat Lia.
From Wasm Require Import operations.
Import ListNotations.

Module EH.

Definition tagidx := u32.
Definition tagaddr := addr.
Definition exnaddr := addr.

(** A tag has parameters but no results. This conversion rejects function
    types with results, rather than silently discarding them. *)
Definition tag_parameters (tf : function_type) : option result_type :=
  match tf with
  | Tf ps [] => Some ps
  | _ => None
  end.

Lemma tag_parameters_spec tf ps :
  tag_parameters tf = Some ps <-> tf = Tf ps [].
Proof.
  destruct tf as [args results]; destruct results; simpl.
  - split; intro H; [inversion H | inversion H]; reflexivity.
  - split; discriminate.
Qed.

(** Tag allocation and linking helpers. Imported tags keep their address;
    allocating a definition always creates a fresh identity, even when two
    tags have identical parameter types. A store entry contains parameters
    only, so an ill-formed result-bearing signature cannot be allocated. *)
Definition resolve_tag_type (types : list function_type) (x : typeidx)
    : option result_type :=
  match lookup_N types x with
  | Some tf => tag_parameters tf
  | None => None
  end.

Lemma resolve_tag_type_spec types x ps :
  resolve_tag_type types x = Some ps <->
  lookup_N types x = Some (Tf ps []).
Proof.
  unfold resolve_tag_type.
  destruct (lookup_N types x) as [tf|] eqn:H; simpl.
  - rewrite tag_parameters_spec; split; intro E;
      [subst; reflexivity | inversion E; reflexivity].
  - split; discriminate.
Qed.

Definition alloc_tag (tags : list result_type) (ps : result_type)
    : list result_type * tagaddr :=
  (tags ++ [ps], N.of_nat (length tags)).

Lemma alloc_tag_fresh tags ps :
  lookup_N (fst (alloc_tag tags ps)) (snd (alloc_tag tags ps)) = Some ps.
Proof.
  unfold alloc_tag, lookup_N; simpl.
  rewrite Nat2N.id, nth_error_app2; [|lia].
  rewrite Nat.sub_diag; reflexivity.
Qed.

Lemma alloc_tag_new tags ps :
  lookup_N tags (snd (alloc_tag tags ps)) = None.
Proof.
  unfold alloc_tag, lookup_N; simpl.
  rewrite Nat2N.id; apply nth_error_None; lia.
Qed.

Lemma alloc_tag_preserves tags ps a old :
  lookup_N tags a = Some old ->
  lookup_N (fst (alloc_tag tags ps)) a = Some old.
Proof.
  unfold alloc_tag, lookup_N; simpl.
  intro H; rewrite nth_error_app1; [assumption|].
  apply nth_error_Some; rewrite H; discriminate.
Qed.

Definition tag_import_matches (tags : list result_type) (a : tagaddr)
    (expected : result_type) : bool :=
  match lookup_N tags a with
  | Some actual =>
      if function_type_eq_dec (Tf actual []) (Tf expected [])
      then true else false
  | None => false
  end.

Lemma tag_import_matches_spec tags a expected :
  tag_import_matches tags a expected = true <->
  lookup_N tags a = Some expected.
Proof.
  unfold tag_import_matches.
  destruct (lookup_N tags a) as [actual|] eqn:H; [|split; discriminate].
  destruct (function_type_eq_dec (Tf actual []) (Tf expected []))
    as [Heq|Hneq].
  - inversion Heq; subst; split; reflexivity.
  - split; [discriminate|].
    intro E; inversion E; subst; contradiction.
Qed.

(** Exactly the four final catch clauses. *)
Inductive catch_clause : Type :=
| Catch : tagidx -> labelidx -> catch_clause
| Catch_ref : tagidx -> labelidx -> catch_clause
| Catch_all : labelidx -> catch_clause
| Catch_all_ref : labelidx -> catch_clause.

Inductive handler : Type :=
| Handle : tagaddr -> labelidx -> handler
| Handle_ref : tagaddr -> labelidx -> handler
| Handle_all : labelidx -> handler
| Handle_all_ref : labelidx -> handler.

(** Resolve module tag indices once on entry to try_table. Matching must
    compare store identities, not tag indices or structural signatures. *)
Definition resolve_catch (tags : list tagaddr) (c : catch_clause)
    : option handler :=
  match c with
  | Catch x l =>
      option_map (fun a => Handle a l) (lookup_N tags x)
  | Catch_ref x l =>
      option_map (fun a => Handle_ref a l) (lookup_N tags x)
  | Catch_all l => Some (Handle_all l)
  | Catch_all_ref l => Some (Handle_all_ref l)
  end.

Fixpoint resolve_catches (tags : list tagaddr) (cs : list catch_clause)
    : option (list handler) :=
  match cs with
  | [] => Some []
  | c :: cs' =>
      match resolve_catch tags c, resolve_catches tags cs' with
      | Some h, Some hs => Some (h :: hs)
      | _, _ => None
      end
  end.

Inductive catches_resolve (tags : list tagaddr)
    : list catch_clause -> list handler -> Prop :=
| Resolve_nil : catches_resolve tags [] []
| Resolve_cons c h cs hs :
    resolve_catch tags c = Some h ->
    catches_resolve tags cs hs ->
    catches_resolve tags (c :: cs) (h :: hs).

Lemma resolve_catches_correct tags cs hs :
  resolve_catches tags cs = Some hs <-> catches_resolve tags cs hs.
Proof.
  split.
  - revert hs; induction cs as [|c cs IH]; intros hs H; simpl in H.
    + inversion H; constructor.
    + destruct (resolve_catch tags c) as [h|] eqn:Hc;
        destruct (resolve_catches tags cs) as [tail|] eqn:Ht;
        try discriminate.
      inversion H; subst; constructor; auto.
  - intro H; induction H; simpl; [reflexivity|].
    rewrite H, IHcatches_resolve; reflexivity.
Qed.

Section Runtime.
Context {V : Type}.

Record exception : Type := {
  exception_tag : tagaddr;
  exception_fields : list V
}.

(** Stack order here is specification order (bottom to top), as for payloads
    and result types, not the interpreter's reversed operand stack. *)
Inductive operand : Type :=
| Payload : V -> operand
| Exn_ref : exnaddr -> operand.

Record branch : Type := {
  branch_label : labelidx;
  branch_values : list operand
}.

Definition handle (a : exnaddr) (e : exception) (h : handler)
    : option branch :=
  let vs := map Payload e.(exception_fields) in
  match h with
  | Handle t l =>
      if N.eqb t e.(exception_tag)
      then Some {| branch_label := l; branch_values := vs |}
      else None
  | Handle_ref t l =>
      if N.eqb t e.(exception_tag)
      then Some {| branch_label := l;
                   branch_values := vs ++ [Exn_ref a] |}
      else None
  | Handle_all l =>
      Some {| branch_label := l; branch_values := [] |}
  | Handle_all_ref l =>
      Some {| branch_label := l; branch_values := [Exn_ref a] |}
  end.

Fixpoint dispatch (a : exnaddr) (e : exception) (hs : list handler)
    : option branch :=
  match hs with
  | [] => None
  | h :: hs' =>
      match handle a e h with
      | Some b => Some b
      | None => dispatch a e hs'
      end
  end.

(** Independent, ordered declarative rules: a matching clause prevents
    looking at any later clause, including a later catch_all. *)
Inductive first_handler (a : exnaddr) (e : exception)
    : list handler -> branch -> Prop :=
| First_hit h hs b :
    handle a e h = Some b -> first_handler a e (h :: hs) b
| First_skip h hs b :
    handle a e h = None ->
    first_handler a e hs b -> first_handler a e (h :: hs) b.

Lemma dispatch_correct a e hs b :
  dispatch a e hs = Some b <-> first_handler a e hs b.
Proof.
  split.
  - induction hs as [|h hs IH]; simpl; [discriminate|].
    destruct (handle a e h) as [b'|] eqn:Hh.
    + intro H; inversion H; subst; constructor; assumption.
    + intro H; apply First_skip; auto.
  - intro H; induction H; simpl; rewrite H; auto.
Qed.

Lemma first_handler_deterministic a e hs b1 b2 :
  first_handler a e hs b1 -> first_handler a e hs b2 -> b1 = b2.
Proof.
  intros H1 H2.
  apply dispatch_correct in H1; apply dispatch_correct in H2.
  rewrite H1 in H2; inversion H2; reflexivity.
Qed.

Lemma dispatch_none a e hs :
  dispatch a e hs = None <->
  Forall (fun h => handle a e h = None) hs.
Proof.
  induction hs as [|h hs IH]; simpl.
  - split; intro H; constructor.
  - destruct (handle a e h) as [b|] eqn:Hh.
    + split; [discriminate|].
      intro H; inversion H; congruence.
    + rewrite IH; split.
      * intro H; constructor; assumption.
      * intro H; inversion H; assumption.
Qed.

Lemma dispatch_prefix a e before after :
  dispatch a e before = None ->
  dispatch a e (before ++ after) = dispatch a e after.
Proof.
  induction before as [|h hs IH]; simpl; [reflexivity|].
  destruct (handle a e h); [discriminate|]; auto.
Qed.

Lemma dispatch_first a e before h after b :
  Forall (fun h' => handle a e h' = None) before ->
  handle a e h = Some b ->
  dispatch a e (before ++ h :: after) = Some b.
Proof.
  intros Hnone Hhit.
  apply dispatch_none in Hnone.
  rewrite (dispatch_prefix a e before (h :: after) Hnone).
  simpl; rewrite Hhit; reflexivity.
Qed.

(** Innermost try_table first. Ordinary labels and call frames are omitted
    here; the full interpreter must establish that they are crossed without
    intercepting exceptions. *)
Fixpoint unwind (a : exnaddr) (e : exception) (frames : list (list handler))
    : option (nat * branch) :=
  match frames with
  | [] => None
  | hs :: outer =>
      match dispatch a e hs with
      | Some b => Some (0, b)
      | None => option_map (fun '(n, b) => (S n, b)) (unwind a e outer)
      end
  end.

Inductive unwinds (a : exnaddr) (e : exception)
    : list (list handler) -> nat -> branch -> Prop :=
| Unwind_here hs outer b :
    first_handler a e hs b -> unwinds a e (hs :: outer) 0 b
| Unwind_outer hs outer n b :
    Forall (fun h => handle a e h = None) hs ->
    unwinds a e outer n b -> unwinds a e (hs :: outer) (S n) b.

Lemma unwind_correct a e frames n b :
  unwind a e frames = Some (n, b) <-> unwinds a e frames n b.
Proof.
  split.
  - revert n b; induction frames as [|hs outer IH]; intros n b H;
      simpl in H; [discriminate|].
    destruct (dispatch a e hs) as [b'|] eqn:Hd.
    + inversion H; subst; constructor; apply dispatch_correct; assumption.
    + destruct (unwind a e outer) as [[m b']|] eqn:Hu; simpl in H;
        try discriminate.
      inversion H; subst; constructor.
      * apply dispatch_none; assumption.
      * apply IH; reflexivity.
  - intro H; induction H; simpl.
    + apply dispatch_correct in H; rewrite H; reflexivity.
    + apply dispatch_none in H; rewrite H, IHunwinds; reflexivity.
Qed.

(** Null throw_ref traps; a non-null reference propagates the SAME exception
    address. In particular it must not allocate a copy of the exception. *)
Inductive throw_result : Type :=
| Throw_trap
| Throw_exception : exnaddr -> throw_result.

Definition throw_ref (r : option exnaddr) : throw_result :=
  match r with
  | None => Throw_trap
  | Some a => Throw_exception a
  end.

Lemma throw_ref_traps_iff r :
  throw_ref r = Throw_trap <-> r = None.
Proof. destruct r; simpl; split; congruence. Qed.

Definition alloc_exception (s : list exception) (e : exception)
    : list exception * exnaddr :=
  (s ++ [e], N.of_nat (length s)).

Lemma alloc_exception_fresh s e :
  lookup_N (fst (alloc_exception s e)) (snd (alloc_exception s e)) =
  Some e.
Proof.
  unfold alloc_exception, lookup_N; simpl.
  rewrite Nat2N.id, nth_error_app2; [|lia].
  rewrite Nat.sub_diag; reflexivity.
Qed.

Lemma alloc_exception_preserves s e a old :
  lookup_N s a = Some old ->
  lookup_N (fst (alloc_exception s e)) a = Some old.
Proof.
  unfold alloc_exception, lookup_N; simpl.
  intro H; rewrite nth_error_app1; [assumption|].
  apply nth_error_Some; rewrite H; discriminate.
Qed.

Lemma alloc_exception_new s e :
  lookup_N s (snd (alloc_exception s e)) = None.
Proof.
  unfold alloc_exception, lookup_N; simpl.
  rewrite Nat2N.id; apply nth_error_None; lia.
Qed.

End Runtime.

Arguments exception : clear implicits.
Arguments operand : clear implicits.
Arguments branch : clear implicits.

End EH.
