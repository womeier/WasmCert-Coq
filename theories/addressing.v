(** Address-width dependent operations shared by memory64 and table64.

    Indices into the module/store remain u32; only addresses into a memory or
    table have the width declared by its type.  In particular, this file does
    not encode a memory index in an address or in a load/store offset.

    The existing [limits] fields are aliases for [N], not bounded machine
    integers, so they already represent 64-bit limits without truncation.

    This is the address-arithmetic layer, not a replacement for the core
    instruction typing or reduction relations. *)
From Wasm Require Import datatypes.
From Stdlib Require Import ZArith NArith Lia Bool.

Module Addressing.

Inductive address_type : Set :=
| AT_i32
| AT_i64.

Definition address_bits (a: address_type) : N :=
  match a with AT_i32 => 32 | AT_i64 => 64 end.

Definition address_bound (a: address_type) : N :=
  2 ^ address_bits a.

Definition address_value_type (a: address_type) : value_type :=
  T_num (match a with AT_i32 => T_i32 | AT_i64 => T_i64 end).

Definition address_type_eqb (at1 at2: address_type) : bool :=
  match at1, at2 with
  | AT_i32, AT_i32 | AT_i64, AT_i64 => true
  | _, _ => false
  end.

Lemma address_type_eqb_spec at1 at2 :
  address_type_eqb at1 at2 = true <-> at1 = at2.
Proof. destruct at1, at2; simpl; intuition discriminate. Qed.

(** The length operand of a copy uses the smaller of the two widths.
    Initialization is different: segment source offsets and lengths stay i32. *)
Definition copy_address_type (dst src: address_type) : address_type :=
  match dst, src with
  | AT_i64, AT_i64 => AT_i64
  | _, _ => AT_i32
  end.

Record memory_type : Set := {
  memory_address_type : address_type;
  memory_limits : limits;
}.

Record table_type : Set := {
  table_address_type : address_type;
  table_limits : limits;
  table_element_type : reference_type;
}.

Definition memory_limit_bound (a: address_type) : N :=
  2 ^ (address_bits a - 16).

Definition table_limit_bound (a: address_type) : N :=
  address_bound a - 1.

Definition memory_type_valid (mt: memory_type) : bool :=
  limit_valid_range mt.(memory_limits)
    (memory_limit_bound mt.(memory_address_type)).

Definition table_type_valid (tt: table_type) : bool :=
  limit_valid_range tt.(table_limits)
    (table_limit_bound tt.(table_address_type)).

(** Legacy embeddings let clients migrate types independently of explicit
    memory-index changes.  These are not coercions: accidentally losing an
    address width must not be implicit. *)
Definition memory32 (mt: datatypes.memory_type) : memory_type :=
  {| memory_address_type := AT_i32; memory_limits := mt |}.

Definition table32 (tt: datatypes.table_type) : table_type :=
  {| table_address_type := AT_i32;
     table_limits := tt.(tt_limits);
     table_element_type := tt.(tt_elem_type) |}.

Lemma memory32_valid mt :
  memory_type_valid (memory32 mt) = memtype_valid mt.
Proof.
  assert (memory_limit_bound AT_i32 = mem_limit_bound) as Hbound by
    (vm_compute; reflexivity).
  unfold memory_type_valid, memory32, memtype_valid.
  change (limit_valid_range mt (memory_limit_bound AT_i32) =
          limit_valid_range mt mem_limit_bound).
  now rewrite Hbound.
Qed.

Lemma table32_valid tt :
  table_type_valid (table32 tt) = tabletype_valid tt.
Proof.
  assert (table_limit_bound AT_i32 = datatypes.table_limit_bound) as Hbound by
    (vm_compute; reflexivity).
  unfold table_type_valid, table32, tabletype_valid.
  change (limit_valid_range (tt_limits tt) (table_limit_bound AT_i32) =
          limit_valid_range (tt_limits tt) datatypes.table_limit_bound).
  now rewrite Hbound.
Qed.

Definition limits_valid (lim: limits) (bound: N) : Prop :=
  (lim.(lim_min) <= bound)%N /\
  match lim.(lim_max) with
  | None => True
  | Some maximum =>
      (lim.(lim_min) <= maximum)%N /\ (maximum <= bound)%N
  end.

Lemma limit_valid_range_spec lim bound :
  limit_valid_range lim bound = true <-> limits_valid lim bound.
Proof.
  unfold limit_valid_range, limits_valid.
  destruct (lim_max lim); rewrite Bool.andb_true_iff, N.leb_le.
  - rewrite Bool.andb_true_iff, !N.leb_le. reflexivity.
  - intuition.
Qed.

(** Values are decoded unsigned, without routing an i64 through [nat] or
    [Int32].  Returning [None] for a mismatched width is important for the
    executable validator/interpreter boundary. *)
Definition address_of_value (a: address_type) (v: value_num) : option N :=
  match a, v with
  | AT_i32, VAL_int32 n => Some (Wasm_int.N_of_uint i32m n)
  | AT_i64, VAL_int64 n => Some (Wasm_int.N_of_uint i64m n)
  | _, _ => None
  end.

Definition value_of_address (a: address_type) (n: N) : value_num :=
  match a with
  | AT_i32 => VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_N n))
  | AT_i64 => VAL_int64 (Wasm_int.int_of_Z i64m (Z.of_N n))
  end.

Definition grow_failure (a: address_type) : value_num :=
  value_of_address a (address_bound a - 1).

Lemma address_value_round_trip a n :
  (n < address_bound a)%N ->
  address_of_value a (value_of_address a n) = Some n.
Proof.
  destruct a; intros Hbound.
  - change (Some (Z.to_N (Wasm_int.Int32.unsigned
      (Wasm_int.Int32.repr (Z.of_N n)))) = Some n).
    rewrite Wasm_int.Int32.unsigned_repr.
    f_equal.
    + apply N2Z.id.
    + change (n < 4294967296)%N in Hbound.
      change (0 <= Z.of_N n <= 4294967295)%Z. lia.
  - change (Some (Z.to_N (Wasm_int.Int64.unsigned
      (Wasm_int.Int64.repr (Z.of_N n)))) = Some n).
    rewrite Wasm_int.Int64.unsigned_repr.
    f_equal.
    + apply N2Z.id.
    + change (n < 18446744073709551616)%N in Hbound.
      change (0 <= Z.of_N n <= 18446744073709551615)%Z. lia.
Qed.

Lemma address_of_value_bound a v n :
  address_of_value a v = Some n -> (n < address_bound a)%N.
Proof.
  destruct a, v as [i|i|f|f]; cbn [address_of_value]; try discriminate;
    intros H; inversion H; subst.
  - pose proof (Wasm_int.Int32.unsigned_range i).
    change (Z.to_N (Wasm_int.Int32.unsigned i) < 4294967296)%N.
    change (0 <= Wasm_int.Int32.unsigned i < 4294967296)%Z in H0.
    lia.
  - pose proof (Wasm_int.Int64.unsigned_range i).
    change (Z.to_N (Wasm_int.Int64.unsigned i) < 18446744073709551616)%N.
    change (0 <= Wasm_int.Int64.unsigned i < 18446744073709551616)%Z in H0.
    lia.
Qed.

(** Offsets are mathematical naturals.  Their validation is width-dependent;
    effective-address addition is deliberately NOT machine addition. *)
Definition offset_valid (a: address_type) (offset: N) : bool :=
  N.ltb offset (address_bound a).

Definition range_valid (start len size: N) : bool :=
  N.leb (start + len) size.

Definition effective_address (a: address_type)
    (base offset len size: N) : option N :=
  if offset_valid a base && offset_valid a offset &&
     range_valid (base + offset) len size
  then Some (base + offset)%N else None.

Lemma range_valid_spec start len size :
  range_valid start len size = true <-> (start + len <= size)%N.
Proof. apply N.leb_le. Qed.

Lemma effective_address_spec a base offset len size ea :
  effective_address a base offset len size = Some ea <->
  (base < address_bound a)%N /\ (offset < address_bound a)%N /\
  ea = (base + offset)%N /\ (ea + len <= size)%N.
Proof.
  unfold effective_address, offset_valid, range_valid.
  destruct (_ && _ && _) eqn:Hcheck.
  - apply Bool.andb_true_iff in Hcheck as [Hwidth Hrange].
    apply Bool.andb_true_iff in Hwidth as [Hbase Hoff].
    apply N.ltb_lt in Hbase. apply N.ltb_lt in Hoff.
    apply N.leb_le in Hrange.
    split; intros H; [inversion H; subst | destruct H as [_ [_ [-> _]]]];
      intuition.
  - split; [discriminate |].
    intros [Hbase [Hoff [-> Hrange]]].
    assert (N.ltb base (address_bound a) = true) as Hbase' by
      (apply N.ltb_lt; assumption).
    assert (N.ltb offset (address_bound a) = true) as Hoff' by
      (apply N.ltb_lt; assumption).
    assert (N.leb (base + offset + len) size = true) as Hrange' by
      (apply N.leb_le; assumption).
    rewrite Hbase', Hoff', Hrange' in Hcheck. discriminate.
Qed.

Lemma range_valid_each start len size i :
  range_valid start len size = true ->
  (i < len)%N -> (start + i < size)%N.
Proof. rewrite range_valid_spec. lia. Qed.

Lemma range_valid_zero start size :
  range_valid start 0 size = true <-> (start <= size)%N.
Proof. rewrite range_valid_spec, N.add_0_r. reflexivity. Qed.

Lemma effective_address_no_wrap a base offset len size ea :
  effective_address a base offset len size = Some ea ->
  ea = (base + offset)%N.
Proof. rewrite effective_address_spec. tauto. Qed.

(** This predicate applies both to memories (pages) and tables (entries).
    The address-width cap is checked even when the declared maximum is absent.
    The old size is checked too: callers cannot grow a malformed instance into
    an apparently valid one. *)
Definition size_valid (lim: limits) (bound size: N) : bool :=
  N.leb lim.(lim_min) size && N.leb size bound &&
  match lim.(lim_max) with
  | None => true
  | Some maximum => N.leb size maximum
  end.

Definition size_in_limits (lim: limits) (bound size: N) : Prop :=
  (lim.(lim_min) <= size)%N /\ (size <= bound)%N /\
  match lim.(lim_max) with
  | None => True
  | Some maximum => (size <= maximum)%N
  end.

Lemma size_valid_spec lim bound size :
  size_valid lim bound size = true <-> size_in_limits lim bound size.
Proof.
  unfold size_valid, size_in_limits.
  rewrite !Bool.andb_true_iff, !N.leb_le.
  destruct (lim_max lim); [rewrite N.leb_le |]; intuition.
Qed.

Definition grow_size (lim: limits) (bound old delta: N) : option N :=
  if size_valid lim bound old &&
     size_valid lim bound (old + delta)
  then Some (old + delta)%N else None.

Lemma grow_size_spec lim bound old delta new :
  grow_size lim bound old delta = Some new <->
  size_in_limits lim bound old /\
  new = (old + delta)%N /\ size_in_limits lim bound new.
Proof.
  unfold grow_size.
  destruct (_ && _) eqn:Hcheck.
  - apply Bool.andb_true_iff in Hcheck as [Hold Hnew].
    apply size_valid_spec in Hold. apply size_valid_spec in Hnew.
    split; intros H; [inversion H; subst | destruct H as [_ [-> _]]];
      intuition.
  - split; [discriminate |].
    intros [Hold [-> Hnew]].
    apply size_valid_spec in Hold. apply size_valid_spec in Hnew.
    rewrite Hold, Hnew in Hcheck. discriminate.
Qed.

Lemma grow_size_monotone lim bound old delta new :
  grow_size lim bound old delta = Some new -> (old <= new)%N.
Proof. rewrite grow_size_spec. intros [_ [-> _]]. lia. Qed.

Lemma grow_size_zero lim bound old :
  size_valid lim bound old = true ->
  grow_size lim bound old 0 = Some old.
Proof. unfold grow_size. rewrite N.add_0_r. intros ->. reflexivity. Qed.

Lemma memory_byte_bound a :
  (memory_limit_bound a * memory.page_size = address_bound a)%N.
Proof. destruct a; vm_compute; reflexivity. Qed.

Lemma memory_size_fits_address a pages :
  (pages <= memory_limit_bound a)%N ->
  (pages < address_bound a)%N.
Proof.
  destruct a.
  - change (pages <= 65536 -> pages < 4294967296)%N. lia.
  - change (pages <= 281474976710656 -> pages < 18446744073709551616)%N. lia.
Qed.

Lemma table_size_fits_address a entries :
  (entries <= table_limit_bound a)%N ->
  (entries < address_bound a)%N.
Proof.
  destruct a.
  - change (entries <= 4294967295 -> entries < 4294967296)%N. lia.
  - change (entries <= 18446744073709551615 ->
            entries < 18446744073709551616)%N. lia.
Qed.

(** Bulk copy checks both complete ranges before either destination is
    modified.  This includes the zero-length case, whose starting offsets
    still have to be in bounds (or exactly at the end). *)
Definition copy_ranges_valid (dst src len dst_size src_size: N) : bool :=
  range_valid dst len dst_size && range_valid src len src_size.

Lemma copy_ranges_valid_spec dst src len dst_size src_size :
  copy_ranges_valid dst src len dst_size src_size = true <->
  (dst + len <= dst_size)%N /\ (src + len <= src_size)%N.
Proof.
  unfold copy_ranges_valid.
  rewrite Bool.andb_true_iff, !range_valid_spec. reflexivity.
Qed.

End Addressing.
