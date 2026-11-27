(** Sparse persistent memory with verified AVL-map scalar updates and snapshot
    bulk updates.  No native array, host-sized address conversion, or eager
    zero initialization is needed, even for the full memory64 address space. *)
From Wasm Require Import bytes memory.
From Stdlib Require Import ZArith NArith Lia Bool FSets.FMapAVL
  FSets.FMapFacts Structures.OrderedTypeEx.

Set Implicit Arguments.
Unset Strict Implicit.

Module SparseMap := FMapAVL.Make(N_as_OT).
Module SparseFacts := WFacts_fun N_as_OT SparseMap.

Record sparse_memory : Type := {
  sparse_length : N;
  sparse_base : N -> byte;
  sparse_edits : SparseMap.t byte;
}.

Definition sparse_read (data: sparse_memory) (i: N) : byte :=
  match SparseMap.find i data.(sparse_edits) with
  | Some b => b
  | None => data.(sparse_base) i
  end.

Definition sparse_make (len: N) : sparse_memory :=
  {| sparse_length := N.min len byte_limit;
     sparse_base := fun _ => wasm_memory_default_byte;
     sparse_edits := SparseMap.empty byte |}.

Definition sparse_lookup (i: N) (data: sparse_memory) : option byte :=
  if N.ltb i data.(sparse_length) then Some (sparse_read data i) else None.

Definition sparse_update (i: N) (b: byte) (data: sparse_memory)
    : option sparse_memory :=
  if N.ltb i data.(sparse_length) then
    Some {| sparse_length := data.(sparse_length);
            sparse_base := data.(sparse_base);
            sparse_edits := SparseMap.add i b data.(sparse_edits) |}
  else None.

Definition sparse_grow (n: N) (data: sparse_memory) : option sparse_memory :=
  let new_length := (data.(sparse_length) + n)%N in
  if N.leb new_length byte_limit then
    Some {| sparse_length := new_length;
            sparse_base := fun i =>
              if N.ltb i data.(sparse_length) then sparse_read data i
              else wasm_memory_default_byte;
            sparse_edits := SparseMap.empty byte |}
  else None.

(** Small stores are AVL-map updates.  Bulk stores retain one immutable
    snapshot function instead of materializing a potentially enormous range. *)
Fixpoint sparse_write (count: nat) (start: N) (gen: N -> byte)
    (edits: SparseMap.t byte) : SparseMap.t byte :=
  match count with
  | O => edits
  | S count' =>
      SparseMap.add (start + N.of_nat count')%N (gen (N.of_nat count'))
        (sparse_write count' start gen edits)
  end.

Lemma sparse_write_inside count start gen edits i :
  (start <= i < start + N.of_nat count)%N ->
  SparseMap.find i (sparse_write count start gen edits) =
    Some (gen (i - start)%N).
Proof.
  induction count as [|count IH]; intros Hbound; [simpl in Hbound; lia |].
  cbn [sparse_write].
  destruct (N.eq_dec (start + N.of_nat count)%N i) as [Heq|Hne].
  - rewrite SparseFacts.add_eq_o by exact Heq.
    f_equal. f_equal. lia.
  - rewrite SparseFacts.add_neq_o by exact Hne.
    apply IH. rewrite Nat2N.inj_succ in Hbound. lia.
Qed.

Lemma sparse_write_outside count start gen edits i :
  ((i < start)%N \/ (start + N.of_nat count <= i)%N) ->
  SparseMap.find i (sparse_write count start gen edits) = SparseMap.find i edits.
Proof.
  induction count as [|count IH]; intros Hbound; [reflexivity |].
  cbn [sparse_write].
  rewrite SparseFacts.add_neq_o.
  - apply IH. rewrite Nat2N.inj_succ in Hbound. lia.
  - rewrite Nat2N.inj_succ in Hbound. lia.
Qed.

Definition sparse_update_gen (start len: N) (gen: N -> byte)
    (data: sparse_memory) : option sparse_memory :=
  if N.leb (start + len) data.(sparse_length) then
    if N.leb len 16 then
      Some {| sparse_length := data.(sparse_length);
              sparse_base := data.(sparse_base);
              sparse_edits := sparse_write (N.to_nat len) start gen data.(sparse_edits) |}
    else
      Some {| sparse_length := data.(sparse_length);
              sparse_base := fun i =>
                if N.leb start i && N.ltb i (start + len)
                then gen (i - start)%N else sparse_read data i;
              sparse_edits := SparseMap.empty byte |}
  else None.

#[export] Instance SparseMemory : Memory.
Proof.
  refine {| mem_t := sparse_memory;
            mem_make := sparse_make;
            mem_length := sparse_length;
            mem_lookup := sparse_lookup;
            mem_grow := sparse_grow;
            mem_update := sparse_update |}.
  - intros data i Hbound. unfold sparse_lookup.
    assert (N.ltb i (sparse_length data) = true) as -> by now apply N.ltb_lt.
    discriminate.
  - intros data i Hbound. unfold sparse_lookup.
    assert (N.ltb i (sparse_length data) = false) as -> by (apply N.ltb_ge; lia).
    reflexivity.
  - reflexivity.
  - intros i len Hbound. unfold sparse_lookup, sparse_make; simpl.
    assert (N.ltb i (N.min len byte_limit) = true) as -> by now apply N.ltb_lt.
    unfold sparse_read; simpl. reflexivity.
  - intros data data' i b. unfold sparse_update.
    destruct (N.ltb i (sparse_length data)) eqn:Hbound; [|discriminate].
    intros Hresult. inversion Hresult; subst.
    unfold sparse_lookup; simpl. rewrite Hbound.
    unfold sparse_read; simpl. rewrite SparseFacts.add_eq_o by reflexivity. reflexivity.
  - intros data data' i j b Hne. unfold sparse_update.
    destruct (N.ltb j (sparse_length data)); [|discriminate].
    intros Hresult. inversion Hresult; subst.
    unfold sparse_lookup, sparse_read; simpl.
    rewrite SparseFacts.add_neq_o by congruence. reflexivity.
  - intros data i b Hbound. unfold sparse_update.
    assert (N.ltb i (sparse_length data) = true) as -> by now apply N.ltb_lt.
    discriminate.
  - intros data i b Hbound. unfold sparse_update.
    assert (N.ltb i (sparse_length data) = false) as -> by (apply N.ltb_ge; lia).
    reflexivity.
  - intros i n data data' Hbound. unfold sparse_grow.
    destruct (N.leb _ _); [|discriminate].
    intros Hresult. inversion Hresult; subst.
    unfold sparse_lookup; simpl.
    assert (N.ltb i (sparse_length data) = true) as Hinside by now apply N.ltb_lt.
    assert (N.ltb i (sparse_length data + n) = true) as -> by
      (apply N.ltb_lt; lia).
    rewrite Hinside. unfold sparse_read at 1; simpl.
    rewrite Hinside. reflexivity.
  - intros n data data'. unfold sparse_grow.
    destruct (N.leb _ _); [|discriminate].
    intros Hresult. inversion Hresult. reflexivity.
  - intros n len data data' i Hi. unfold sparse_grow.
    destruct (N.leb _ _); [|discriminate].
    intros Hresult Hlen. inversion Hresult; subst.
    unfold sparse_lookup; simpl.
    assert (N.ltb (sparse_length data + i) (sparse_length data + n) = true)
      as -> by (apply N.ltb_lt; lia).
    unfold sparse_read; simpl.
    assert (N.ltb (sparse_length data + i) (sparse_length data) = false)
      as -> by (apply N.ltb_ge; lia).
    reflexivity.
Defined.

Lemma sparse_update_gen_length start len gen data data' :
  sparse_update_gen start len gen data = Some data' ->
  sparse_length data' = sparse_length data.
Proof.
  unfold sparse_update_gen.
  destruct (N.leb _ _); [|discriminate].
  destruct (N.leb _ _); intros Hresult; inversion Hresult; reflexivity.
Qed.

Lemma sparse_update_gen_read_inside start len gen data data' i :
  sparse_update_gen start len gen data = Some data' ->
  (start <= i < start + len)%N ->
  sparse_read data' i = gen (i - start)%N.
Proof.
  unfold sparse_update_gen.
  destruct (N.leb _ _); [|discriminate].
  destruct (N.leb len 16); intros Hresult Hi; inversion Hresult; subst;
    unfold sparse_read; simpl.
  - rewrite sparse_write_inside; [reflexivity | rewrite N2Nat.id; assumption].
  -
    assert (N.leb start i = true) as -> by (apply N.leb_le; lia).
    assert (N.ltb i (start + len) = true) as -> by (apply N.ltb_lt; lia).
    reflexivity.
Qed.

Lemma sparse_update_gen_read_outside start len gen data data' i :
  sparse_update_gen start len gen data = Some data' ->
  ((i < start)%N \/ (start + len <= i)%N) ->
  sparse_read data' i = sparse_read data i.
Proof.
  unfold sparse_update_gen.
  destruct (N.leb _ _); [|discriminate].
  destruct (N.leb len 16); intros Hresult Hi; inversion Hresult; subst.
  - unfold sparse_read; simpl.
    rewrite sparse_write_outside; [reflexivity | rewrite N2Nat.id; assumption].
  - unfold sparse_read at 1; simpl.
    destruct (N.leb start i && N.ltb i (start + len)) eqn:Hrange; [|reflexivity].
    apply Bool.andb_true_iff in Hrange as [Hlo Hhi].
    apply N.leb_le in Hlo. apply N.ltb_lt in Hhi. lia.
Qed.

#[export] Instance SparseBlockMemory : BlockUpdateMemory.
Proof.
  refine {| m := SparseMemory; mem_update_gen := sparse_update_gen |}.
  - intros start len gen data Hbound. unfold sparse_update_gen.
    change (start + len <= sparse_length data)%N in Hbound.
    assert (N.leb (start + len) (sparse_length data) = true) as -> by
      now apply N.leb_le.
    destruct (N.leb len 16); discriminate.
  - intros start len gen data Hbound. unfold sparse_update_gen.
    change (start + len > sparse_length data)%N in Hbound.
    assert (N.leb (start + len) (sparse_length data) = false) as -> by
      (apply N.leb_gt; lia).
    reflexivity.
  - intros start len gen data data' i Hresult Hi.
    pose proof (sparse_update_gen_length Hresult) as Hlength.
    assert (start + len <= sparse_length data)%N as Hbound.
    { unfold sparse_update_gen in Hresult.
      destruct (N.leb _ _) eqn:Hbound; [now apply N.leb_le | discriminate]. }
    change (sparse_lookup (start + i) data' = Some (gen i)).
    unfold sparse_lookup. rewrite Hlength.
    assert (N.ltb (start + i) (sparse_length data) = true) as -> by
      (apply N.ltb_lt; lia).
    rewrite (sparse_update_gen_read_inside Hresult) by lia.
    replace (start + i - start)%N with i by lia. reflexivity.
  - intros start len gen data data' i Hresult Hi.
    pose proof (sparse_update_gen_length Hresult) as Hlength.
    change (sparse_lookup i data' = sparse_lookup i data).
    unfold sparse_lookup. rewrite Hlength.
    rewrite (sparse_update_gen_read_outside Hresult) by (left; assumption).
    reflexivity.
  - intros start len gen data data' i Hresult Hi.
    pose proof (sparse_update_gen_length Hresult) as Hlength.
    change (sparse_lookup i data' = sparse_lookup i data).
    unfold sparse_lookup. rewrite Hlength.
    rewrite (sparse_update_gen_read_outside Hresult) by (right; lia).
    reflexivity.
Defined.
