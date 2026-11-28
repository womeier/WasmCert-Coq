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

(** The exception-only fragment of the heap/reference lattice. This does not
    extend the global [reference_type], which currently has neither heap types
    nor nullability. Shared-reference integration must embed these two heaps
    as a separate hierarchy (not beneath any/eq/func/extern).

    [reference_shape_typing] classifies abstract exception-reference shapes,
    not store well-formedness: a non-null address additionally needs an
    allocated exception in the full store typing relation. *)
Inductive exception_heap_type : Set := HT_exn | HT_noexn.

Record exception_reference_type : Set := {
  exception_nullable : bool;
  exception_heap : exception_heap_type
}.

Definition exception_heap_matches (h1 h2 : exception_heap_type) : bool :=
  match h1, h2 with
  | HT_noexn, _ => true
  | HT_exn, HT_exn => true
  | HT_exn, HT_noexn => false
  end.

Definition exception_reference_matches
    (t1 t2 : exception_reference_type) : bool :=
  (negb t1.(exception_nullable) || t2.(exception_nullable)) &&
  exception_heap_matches t1.(exception_heap) t2.(exception_heap).

Definition reference_shape_typing (r : option exnaddr)
    (t : exception_reference_type) : bool :=
  match r with
  | None => t.(exception_nullable)
  | Some _ =>
      match t.(exception_heap) with
      | HT_exn => true
      | HT_noexn => false
      end
  end.

Lemma exception_reference_matches_spec t1 t2 :
  exception_reference_matches t1 t2 = true <->
  forall r, reference_shape_typing r t1 = true ->
            reference_shape_typing r t2 = true.
Proof.
  destruct t1 as [n1 h1], t2 as [n2 h2].
  destruct n1, h1, n2, h2; simpl; split; intro H;
    try discriminate; try reflexivity.
  all: try solve [intros [a|] Htype; simpl in *; congruence].
  all: try solve [specialize (H None eq_refl); discriminate].
  all: try solve [specialize (H (Some 0%N) eq_refl); discriminate].
Qed.

Lemma exception_reference_matches_refl t :
  exception_reference_matches t t = true.
Proof. apply exception_reference_matches_spec; auto. Qed.

Lemma exception_reference_matches_trans t1 t2 t3 :
  exception_reference_matches t1 t2 = true ->
  exception_reference_matches t2 t3 = true ->
  exception_reference_matches t1 t3 = true.
Proof.
  rewrite !exception_reference_matches_spec; eauto.
Qed.

Lemma nonnullable_noexn_uninhabited r :
  reference_shape_typing r
    {| exception_nullable := false; exception_heap := HT_noexn |} = false.
Proof. destruct r; reflexivity. Qed.

Lemma nullable_noexn_only_null r :
  reference_shape_typing r
    {| exception_nullable := true; exception_heap := HT_noexn |} = true <->
  r = None.
Proof. destruct r; simpl; split; congruence. Qed.

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

(** [throw] consumes the tag's parameters in specification stack order and
    allocates a fresh exception. [None] signals an ill-formed input state,
    not a Wasm trap: validation/progress must rule out these cases when this
    component is connected to the interpreter. *)
Record throw_state : Type := {
  throw_store : list exception;
  throw_stack : list V;
  throw_address : exnaddr
}.

Definition throw_tag (tags : list tagaddr) (tagtypes : list result_type)
    (s : list exception) (x : tagidx) (stack : list V)
    : option throw_state :=
  match lookup_N tags x with
  | Some tag =>
      match lookup_N tagtypes tag with
      | Some ps =>
          if Nat.leb (length ps) (length stack) then
            let split := (length stack - length ps)%nat in
            let e := {| exception_tag := tag;
                        exception_fields := skipn split stack |} in
            Some {| throw_store := s ++ [e];
                    throw_stack := firstn split stack;
                    throw_address := N.of_nat (length s) |}
          else None
      | None => None
      end
  | None => None
  end.

Inductive throws_tag (tags : list tagaddr) (tagtypes : list result_type)
    (s : list exception) (x : tagidx) : list V -> throw_state -> Prop :=
| Throw_tag_step tag ps prefix fields :
    lookup_N tags x = Some tag ->
    lookup_N tagtypes tag = Some ps ->
    length fields = length ps ->
    throws_tag tags tagtypes s x (prefix ++ fields)
      {| throw_store :=
           s ++ [{| exception_tag := tag; exception_fields := fields |}];
         throw_stack := prefix;
         throw_address := N.of_nat (length s) |}.

Theorem throw_tag_correct tags tagtypes s x stack out :
  throw_tag tags tagtypes s x stack = Some out <->
  throws_tag tags tagtypes s x stack out.
Proof.
  split.
  - unfold throw_tag.
    destruct (lookup_N tags x) as [tag|] eqn:Ht; [|discriminate].
    destruct (lookup_N tagtypes tag) as [ps|] eqn:Hp; [|discriminate].
    destruct (Nat.leb (length ps) (length stack)) eqn:Hlen; [|discriminate].
    intro H; inversion H; subst.
    rewrite <- (firstn_skipn (length stack - length ps) stack) at 1.
    econstructor; [exact Ht|exact Hp|].
    rewrite length_skipn; apply Nat.leb_le in Hlen; lia.
  - intro H; destruct H.
    unfold throw_tag; rewrite H, H0, length_app, <- H1.
    assert (Hlen : Nat.leb (length fields) (length prefix + length fields) = true).
    { apply Nat.leb_le; lia. }
    rewrite Hlen.
    replace (length prefix + length fields - length fields)%nat
      with (length prefix) by lia.
    rewrite firstn_app, firstn_all, Nat.sub_diag, skipn_app,
      skipn_all, Nat.sub_diag; simpl.
    rewrite app_nil_r; reflexivity.
Qed.

Lemma throw_tag_allocated tags tagtypes s x stack out :
  throws_tag tags tagtypes s x stack out ->
  exists tag fields,
    lookup_N tags x = Some tag /\
    lookup_N out.(throw_store) out.(throw_address) =
      Some {| exception_tag := tag; exception_fields := fields |} /\
    stack = out.(throw_stack) ++ fields.
Proof.
  intro H; destruct H; exists tag, fields; simpl.
  split; [assumption|]; split; [|reflexivity].
  apply alloc_exception_fresh.
Qed.

End Runtime.

Arguments exception : clear implicits.
Arguments operand : clear implicits.
Arguments branch : clear implicits.

End EH.
