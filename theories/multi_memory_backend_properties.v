(** Multi-memory-relevant backend obligations.
    The indexed-store lemmas prove actual production list lookup/replacement
    behavior, including duplicate imported addresses. Vector conversion bounds
    apply to the selected Rocq frontend, not to unchecked foreign OCaml calls.
    These results do not assume correctness of Parray's mutable reroot code. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import operations properties memory_vec.
From Stdlib Require Import List NArith PeanoNat Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** First-order algorithm used by the extraction substitution for lookup_N.
    It decreases the finite list, never converts the unbounded N to an OCaml
    int, and therefore returns None even for arbitrarily large missing indices.
    Equality below is unconditional on the index/list lengths. *)
Fixpoint lookup_N_scan {A: Type} (xs: list A) (n: N) : option A :=
  match xs with
  | nil => None
  | head :: tail =>
      if N.eqb n 0 then Some head else lookup_N_scan tail (N.pred n)
  end.

Theorem lookup_N_scan_spec : forall A (xs: list A) n,
  lookup_N_scan xs n = lookup_N xs n.
Proof.
  intros A xs. induction xs as [|head tail IH]; intros n.
  { unfold lookup_N. destruct (N.to_nat n); reflexivity. }
  destruct n as [|p]; [reflexivity|].
  change (lookup_N_scan tail (N.pred (N.pos p)) =
    List.nth_error (head :: tail) (N.to_nat (N.pos p))).
  rewrite IH. unfold lookup_N.
  replace (N.to_nat (N.pos p)) with (S (N.to_nat (N.pred (N.pos p)))) by lia.
  reflexivity.
Qed.

Lemma nth_error_replace_existing : forall A (xs: list A) n old new,
  List.nth_error xs n = Some old ->
  forall i, List.nth_error (set_nth new xs n new) i =
    if Nat.eqb i n then Some new else List.nth_error xs i.
Proof.
  intros A xs. induction xs as [|head tail IH]; intros [|n] old new H i;
    try discriminate; destruct i; simpl in *; try reflexivity.
  now apply (IH n old new H).
Qed.

Lemma lookup_N_replace_existing : forall A (xs: list A) addr old new,
  lookup_N xs addr = Some old ->
  forall i, lookup_N (set_nth new xs (N.to_nat addr) new) i =
    if N.eqb i addr then Some new else lookup_N xs i.
Proof.
  intros A xs addr old new H i. unfold lookup_N in *.
  rewrite (nth_error_replace_existing new H).
  destruct (N.eqb i addr) eqn:Heq.
  - apply N.eqb_eq in Heq. subst. now rewrite Nat.eqb_refl.
  - assert (Nat.eqb (N.to_nat i) (N.to_nat addr) = false).
    { apply Nat.eqb_neq. intros Hnat. apply N2Nat.inj in Hnat.
      subst. now rewrite N.eqb_refl in Heq. }
    now rewrite H0.
Qed.

Section Store.
Context `{memory: BlockUpdateMemory} `{hfc: host_function_class}.

Theorem smem_replace_address_observation : forall s inst addr old new,
  lookup_N s.(s_mems) addr = Some old ->
  forall y,
  smem (upd_s_mem s (set_nth new s.(s_mems) (N.to_nat addr) new)) inst y =
    match lookup_N inst.(inst_mems) y with
    | Some other =>
        if N.eqb other addr then Some new else smem s inst y
    | None => None
    end.
Proof.
  intros s inst addr old new H y. unfold smem.
  destruct (lookup_N (inst_mems inst) y) as [other|] eqn:Hy; [|reflexivity].
  cbn [upd_s_mem s_mems].
  exact (lookup_N_replace_existing new H other).
Qed.

Theorem smem_store_packed_address_effect : forall s inst x n off v tp s',
  smem_store_packed s inst x n off v tp = Some s' ->
  exists addr old new,
    lookup_N inst.(inst_mems) x = Some addr /\
    lookup_N s.(s_mems) addr = Some old /\
    store_packed old n off (serialise_num v) (tp_length tp) = Some new /\
    s' = upd_s_mem s (set_nth new s.(s_mems) (N.to_nat addr) new) /\
    forall y, smem s' inst y =
      match lookup_N inst.(inst_mems) y with
      | Some other => if N.eqb other addr then Some new else smem s inst y
      | None => None
      end.
Proof.
  intros s inst x n off v tp s' H. unfold smem_store_packed in H.
  destruct (lookup_N (inst_mems inst) x) as [addr|] eqn:Hx; [|discriminate].
  destruct (lookup_N (s_mems s) addr) as [old|] eqn:Hold; [|discriminate].
  destruct (store_packed old n off (serialise_num v) (tp_length tp))
    as [new|] eqn:Hnew; [|discriminate].
  inversion H; subst s'.
  exists addr, old, new. repeat split; try assumption; try reflexivity.
  now apply smem_replace_address_observation with (old := old).
Qed.

End Store.

Definition native63_nonnegative (n: N) := (n <= 4611686018427387903)%N.

Lemma vector_capacity_u32_bound : forall (v: memory_vec),
  (v_capacity v <= byte_limit)%N.
Proof.
  intros v. rewrite (v_capacity_eq v).
  pose proof (leb_length (v_data v)) as H.
  apply N.leb_le in H. exact H.
Qed.

Theorem mv_lookup_native_argument : forall (v: memory_vec) i b,
  mv_lookup i v = Some b ->
  (i < mv_length v <= byte_limit)%N /\ native63_nonnegative i.
Proof.
  intros v i b H.
  assert (Hi: (i < mv_length v)%N).
  { unfold mv_lookup, vector_lookup in H.
    destruct (N.ltb i (vector_length v)) eqn:Hl; [now apply N.ltb_lt|discriminate]. }
  pose proof (@vector_size_bound _ _ v) as Hv.
  unfold mv_length, vector_length, native63_nonnegative, byte_limit, page_size, page_limit in *.
  repeat split; lia.
Qed.

Theorem mv_block_update_native_arguments : forall (v v': memory_vec) n len gen,
  mv_update_gen n len gen v = Some v' ->
  (n + len <= mv_length v <= byte_limit)%N /\
  native63_nonnegative n /\ native63_nonnegative len /\
  native63_nonnegative (v_capacity v).
Proof.
  intros v v' n len gen H.
  assert (Hrange: (n + len <= mv_length v)%N).
  { destruct (N.leb (n + len) (mv_length v)) eqn:Hr; [now apply N.leb_le|].
    apply N.leb_gt in Hr.
    assert (Hnone: mv_update_gen n len gen v = None).
    { apply mv_update_gen_oob. lia. }
    rewrite Hnone in H.
    discriminate. }
  pose proof (@vector_size_bound _ _ v) as Hv.
  pose proof (vector_capacity_u32_bound (v := v)) as Hcap.
  unfold mv_length, vector_length, native63_nonnegative, byte_limit, page_size, page_limit in *.
  repeat split; lia.
Qed.
