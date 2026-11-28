(** Multi-memory-relevant backend obligations.
    The indexed-store lemmas prove actual production list lookup/replacement
    behavior, including duplicate imported addresses. Vector conversion bounds
    apply to the selected Rocq frontend, not to unchecked foreign OCaml calls.
    These results do not assume correctness of Parray's mutable reroot code. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import operations properties memory_vec.
From Stdlib Require Import List NArith ZArith PeanoNat Lia.

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

Theorem smem_grow_address_effect : forall s inst x delta s' previous,
  smem_grow s inst x delta = Some (s', previous) ->
  exists addr old new,
    lookup_N inst.(inst_mems) x = Some addr /\
    lookup_N s.(s_mems) addr = Some old /\
    operations.mem_grow old delta = Some new /\
    previous = mem_size old /\
    s' = upd_s_mem s (set_nth new s.(s_mems) (N.to_nat addr) new) /\
    forall y, smem s' inst y =
      match lookup_N inst.(inst_mems) y with
      | Some other => if N.eqb other addr then Some new else smem s inst y
      | None => None
      end.
Proof.
  intros s inst x delta s' previous H. unfold smem_grow in H.
  destruct (lookup_N (inst_mems inst) x) as [addr|] eqn:Hx; [|discriminate].
  destruct (lookup_N (s_mems s) addr) as [old|] eqn:Hold; [|discriminate].
  destruct (operations.mem_grow old delta) as [new|] eqn:Hnew; [|discriminate].
  inversion H; subst s' previous.
  exists addr, old, new. repeat split; try assumption; try reflexivity.
  now apply smem_replace_address_observation with (old := old).
Qed.

Theorem smem_missing_store_address : forall s inst x addr,
  lookup_N inst.(inst_mems) x = Some addr ->
  lookup_N s.(s_mems) addr = None ->
  smem s inst x = None /\
  (forall delta, smem_grow s inst x delta = None) /\
  (forall n off v tp, smem_store_packed s inst x n off v tp = None).
Proof.
  intros s inst x addr Hinst Hstore.
  unfold smem, smem_grow, smem_store_packed.
  rewrite Hinst Hstore. repeat split; reflexivity.
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

(** Closed functional snapshot specification for the selected vector API.
    The refinement proofs below expose the existing array laws in their
    assumption audits. They specify the real update contract; they do NOT
    prove that mutable Parray rerooting implements those laws. *)
Definition snapshot_write (before: N -> option byte) dst count gen i :=
  if andb (N.leb dst i) (N.ltb i (dst + count))
  then Some (gen (i - dst)%N)
  else before i.

Theorem mv_block_update_snapshot : forall (v v': memory_vec) dst count gen,
  mv_update_gen dst count gen v = Some v' ->
  forall i, mv_lookup i v' = snapshot_write (fun j => mv_lookup j v) dst count gen i.
Proof.
  intros v v' dst count gen H i. unfold snapshot_write.
  destruct (N.ltb i dst) eqn:Hleft.
  - apply N.ltb_lt in Hleft.
    assert (N.leb dst i = false) as Hb by (apply N.leb_gt; lia).
    rewrite Hb. now apply mv_update_gen_lookup_lt with (n := dst) (len := count) (gen := gen).
  - apply N.ltb_ge in Hleft.
    assert (N.leb dst i = true) as Hb by (apply N.leb_le; lia).
    rewrite Hb. cbn.
    destruct (N.ltb i (dst + count)) eqn:Hinside.
    + apply N.ltb_lt in Hinside.
      replace i with (dst + (i - dst))%N at 1 by lia.
      eapply mv_update_gen_lookup; [exact H|lia].
    + apply N.ltb_ge in Hinside.
      apply mv_update_gen_lookup_ge with (n := dst) (len := count) (gen := gen);
        [exact H|lia].
Qed.

Definition snapshot_source (source: memory_vec) src offset :=
  match mv_lookup (src + offset)%N source with
  | Some b => b
  | None => wasm_memory_default_byte
  end.

Theorem mv_snapshot_copy_observation : forall source destination result src dst count,
  (src + count <= mv_length source)%N ->
  mv_update_gen dst count (snapshot_source source src) destination = Some result ->
  forall i, mv_lookup i result =
    if andb (N.leb dst i) (N.ltb i (dst + count))
    then mv_lookup (src + (i - dst))%N source
    else mv_lookup i destination.
Proof.
  intros source destination result src dst count Hsource Hupdate i.
  rewrite (mv_block_update_snapshot Hupdate i). unfold snapshot_write.
  destruct (andb (N.leb dst i) (N.ltb i (dst + count))) eqn:Hinside;
    [|reflexivity].
  apply Bool.andb_true_iff in Hinside. destruct Hinside as [Hlo Hhi].
  apply N.leb_le in Hlo. apply N.ltb_lt in Hhi.
  unfold snapshot_source.
  destruct (mv_lookup (src + (i - dst)) source) eqn:Hread; [reflexivity|].
  exfalso.
  assert (Hvalid: mv_lookup (src + (i - dst)) source <> None).
  { apply mv_lookup_ib. lia. }
  exact (Hvalid Hread).
Qed.

Theorem mv_snapshot_copy_exists : forall source destination src dst count,
  (src + count <= mv_length source)%N ->
  (dst + count <= mv_length destination)%N ->
  exists result,
    mv_update_gen dst count (snapshot_source source src) destination = Some result.
Proof.
  intros source destination src dst count Hsource Hdestination.
  destruct (mv_update_gen dst count (snapshot_source source src) destination)
    as [result|] eqn:Hupdate; [now exists result|].
  exfalso.
  assert (Hvalid: mv_update_gen dst count (snapshot_source source src) destination <> None).
  { apply mv_update_gen_ib. exact Hdestination. }
  exact (Hvalid Hupdate).
Qed.

(** Array.init len generator in the staged native algorithm has precisely
    these immutable values. This lemma is independent of the Parray axioms;
    connecting mutable reroot/write code to it remains a separate obligation. *)
Definition staged_generator_values {A} (len: nat) (gen: N -> A) :=
  List.map (fun i => gen (N.of_nat i)) (List.seq 0 len).

Theorem staged_generator_lookup : forall A len (gen: N -> A) i,
  (i < len)%nat ->
  List.nth_error (staged_generator_values len gen) i = Some (gen (N.of_nat i)).
Proof.
  intros A len gen i H.
  move/ltP in H.
  unfold staged_generator_values. rewrite List.nth_error_map List.nth_error_seq.
  assert (Nat.ltb i len = true) as Hi by (now apply Nat.ltb_lt).
  now rewrite Hi.
Qed.

Definition vector_copy_capacity (v: memory_vec) (delta: N) :=
  N.min (N.max (v_size v + delta) (v_capacity v * 2)) byte_limit.

Theorem vector_growth_copy_native_arguments : forall (v: memory_vec) delta,
  (v_size v + delta <= byte_limit)%N ->
  (v_capacity v < v_size v + delta)%N ->
  (v_size v <= v_capacity v <= vector_copy_capacity v delta)%N /\
  (vector_copy_capacity v delta <= byte_limit)%N /\
  native63_nonnegative (v_size v) /\
  native63_nonnegative (vector_copy_capacity v delta).
Proof.
  intros v delta Hsize Hcopy.
  pose proof (vector_capacity_u32_bound (v := v)) as Hcap.
  pose proof (@v_size_valid _ _ v) as Hvalid.
  unfold vector_copy_capacity, native63_nonnegative.
  pose proof (N.le_max_l (v_size v + delta) (v_capacity v * 2)) as Hmax.
  pose proof (N.le_min_r (N.max (v_size v + delta) (v_capacity v * 2)) byte_limit) as Hmin.
  assert (v_capacity v <=
    N.min (N.max (v_size v + delta) (v_capacity v * 2)) byte_limit)%N.
  { apply N.min_glb; lia. }
  unfold byte_limit, page_size, page_limit in *.
  repeat split; lia.
Qed.

(** Arithmetic correspondence of the exact subtraction guard imported from
    44270f7. OCaml comparisons operate on signed native integers. Once start is
    checked against the nonnegative actual array length, the sole subtraction
    cannot overflow; unlike the old start+count test, no addition is evaluated
    on an invalid candidate range. This is arithmetic, not an OCaml heap proof. *)
Definition native63_signed (z: Z) :=
  (-4611686018427387904 <= z <= 4611686018427387903)%Z.

Theorem parray_subtraction_guard_spec : forall start count total,
  (0 <= total <= 4611686018427387903)%Z ->
  (0 < count)%Z ->
  ((0 <= start /\ start <= total /\ count <= total - start)%Z <->
   (0 <= start /\ start + count <= total)%Z) /\
  ((0 <= start /\ start <= total)%Z ->
    native63_signed (total - start)).
Proof.
  intros start count total Htotal Hcount.
  unfold native63_signed. split; [split|]; intros; lia.
Qed.

Theorem parray_accepted_block_native_bounds : forall start count total,
  (0 <= total <= 4611686018427387903)%Z ->
  (0 < count)%Z ->
  (0 <= start /\ start <= total /\ count <= total - start)%Z ->
  native63_signed start /\ native63_signed count /\
  native63_signed (total - start) /\ native63_signed (start + count) /\
  forall offset, (0 <= offset < count)%Z ->
    native63_signed (start + offset) /\ (0 <= start + offset < total)%Z.
Proof.
  intros start count total Htotal Hcount Hrange.
  unfold native63_signed. repeat split; intros; lia.
Qed.
