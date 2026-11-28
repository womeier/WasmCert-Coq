(** Address-aware memory operations over the existing, verified [Memory]
    interface.  No host allocation or integer conversion is trusted here.

    The existing list/vector implementations can refuse growth above 4 GiB,
    which is a permitted growth failure but is not full memory64 capacity.
    [allocate] checks the interface's capped allocation result, so a large
    request can never silently instantiate a truncated memory.

    These operations are exported separately while the core instruction/store
    representation is being migrated. *)
From Wasm Require Import datatypes addressing memory.
From Stdlib Require Import ZArith Lia Bool.
Import Addressing.

Module AddressingMemory.

Section Operations.
Context `{Memory}.

Record instance : Type := {
  declared_type : Addressing.memory_type;
  contents : mem_t;
}.

Definition size (m: instance) : N :=
  (mem_length m.(contents) / page_size)%N.

Definition valid (m: instance) : Prop :=
  memory_type_valid m.(declared_type) = true /\
  mem_length m.(contents) = (size m * page_size)%N /\
  size_in_limits m.(declared_type).(memory_limits)
    (memory_limit_bound m.(declared_type).(memory_address_type)) (size m).

Definition allocate (mt: Addressing.memory_type) : option instance :=
  if memory_type_valid mt then
    let requested := (mt.(memory_limits).(lim_min) * page_size)%N in
    if N.leb requested byte_limit then
      let data := mem_make requested in
      if N.eqb (mem_length data) requested
      then Some {| declared_type := mt; contents := data |}
      else None
    else None
  else None.

Lemma page_size_nonzero : page_size <> 0%N.
Proof. discriminate. Qed.

Lemma allocate_valid mt m :
  allocate mt = Some m -> valid m.
Proof.
  unfold allocate.
  destruct (memory_type_valid mt) eqn:Htype; [|discriminate].
  destruct (N.leb _ _) eqn:Hcapacity; [|discriminate].
  destruct (N.eqb _ _) eqn:Hsize; [|discriminate].
  apply N.eqb_eq in Hsize.
  intros Hresult. inversion Hresult; subst; clear Hresult.
  unfold valid, size; cbn [declared_type contents].
  rewrite Hsize, N.div_mul by apply page_size_nonzero.
  split; [assumption |]. split; [reflexivity |].
  apply limit_valid_range_spec in Htype.
  unfold limits_valid in Htype.
  unfold size_in_limits.
  destruct (lim_max (memory_limits mt)); simpl in *; intuition lia.
Qed.

Lemma allocate_exact mt m :
  allocate mt = Some m ->
  declared_type m = mt /\
  mem_length (contents m) = (mt.(memory_limits).(lim_min) * page_size)%N.
Proof.
  unfold allocate.
  destruct (memory_type_valid mt); [|discriminate].
  destruct (N.leb _ _); [|discriminate].
  destruct (N.eqb _ _) eqn:Hsize; [|discriminate].
  apply N.eqb_eq in Hsize.
  intros Hresult. inversion Hresult; subst. auto.
Qed.

(** A failed [mem_make] capacity check is observable as allocation failure,
    not as success with fewer pages than the declared minimum. *)
Lemma allocate_over_capacity mt :
  (byte_limit < mt.(memory_limits).(lim_min) * page_size)%N ->
  allocate mt = None.
Proof.
  intros Hlarge. unfold allocate.
  destruct (memory_type_valid mt); [|reflexivity].
  destruct (N.leb _ _) eqn:Hcapacity; [|reflexivity].
  apply N.leb_le in Hcapacity. lia.
Qed.

Definition grow (m: instance) (delta: value_num)
    : option (instance * value_num) :=
  let mt := m.(declared_type) in
  match address_of_value mt.(memory_address_type) delta with
  | None => None
  | Some count =>
      match grow_size mt.(memory_limits)
        (memory_limit_bound mt.(memory_address_type)) (size m) count with
      | None => None
      | Some _ =>
          match mem_grow (count * page_size)%N m.(contents) with
          | None => None
          | Some data =>
              Some ({| declared_type := mt; contents := data |},
                value_of_address mt.(memory_address_type) (size m))
          end
      end
  end.

Lemma grow_characterization m delta m' result :
  grow m delta = Some (m', result) ->
  exists count new_size,
    address_of_value m.(declared_type).(memory_address_type) delta = Some count /\
    grow_size m.(declared_type).(memory_limits)
      (memory_limit_bound m.(declared_type).(memory_address_type))
      (size m) count = Some new_size /\
    mem_grow (count * page_size)%N m.(contents) = Some m'.(contents) /\
    m'.(declared_type) = m.(declared_type) /\
    result = value_of_address m.(declared_type).(memory_address_type) (size m).
Proof.
  unfold grow.
  destruct (address_of_value _ _) as [count|] eqn:Hdelta; [|discriminate].
  destruct (grow_size _ _ _ _) as [new_size|] eqn:Hsize; [|discriminate].
  destruct (mem_grow _ _) as [data|] eqn:Hgrow; [|discriminate].
  intros Hresult. inversion Hresult; subst.
  exists count, new_size. repeat split; assumption || reflexivity.
Qed.

Lemma grow_valid m delta m' result :
  valid m ->
  grow m delta = Some (m', result) ->
  valid m' /\
  (size m <= size m')%N /\
  address_of_value m.(declared_type).(memory_address_type) result = Some (size m).
Proof.
  intros [Htype [Haligned Hvalid]] Hgrow.
  apply grow_characterization in Hgrow as
    [count [new_size [Hdelta [Hsize [Hdata [Htype' Hresult]]]]]].
  apply grow_size_spec in Hsize as [_ [Hnew Hnewvalid]].
  assert (mem_length m'.(contents) = (new_size * page_size)%N) as Hlength.
  { rewrite (mem_grow_length Hdata), Haligned, Hnew.
    symmetry. apply N.mul_add_distr_r. }
  assert (size m' = new_size) as Hpages.
  { unfold size. rewrite Hlength, N.div_mul; [reflexivity | apply page_size_nonzero]. }
  split.
  - unfold valid. rewrite Htype', Hlength, Hpages. auto.
  - split; [rewrite Hpages, Hnew; lia |].
    rewrite Hresult. apply address_value_round_trip.
    apply memory_size_fits_address.
    unfold size_in_limits in Hvalid. tauto.
Qed.

Lemma grow_preserves_bytes m delta m' result i :
  grow m delta = Some (m', result) ->
  (i < mem_length m.(contents))%N ->
  mem_lookup i m'.(contents) = mem_lookup i m.(contents).
Proof.
  intros Hgrow Hi.
  apply grow_characterization in Hgrow as
    [count [new_size [_ [_ [Hdata _]]]]].
  eapply mem_grow_lookup; eassumption.
Qed.

Lemma grow_initializes_bytes m delta m' result i :
  grow m delta = Some (m', result) ->
  (mem_length m.(contents) <= i < mem_length m'.(contents))%N ->
  mem_lookup i m'.(contents) = Some wasm_memory_default_byte.
Proof.
  intros Hgrow [Hlo Hhi].
  apply grow_characterization in Hgrow as
    [count [new_size [_ [_ [Hdata _]]]]].
  pose proof (mem_grow_length Hdata) as Hlength.
  replace i with (mem_length m.(contents) + (i - mem_length m.(contents)))%N
    by lia.
  eapply mem_grow_default; [|exact Hdata |reflexivity]. lia.
Qed.

Definition load_byte (m: instance) (base: value_num) (offset: N)
    : option byte :=
  match address_of_value m.(declared_type).(memory_address_type) base with
  | None => None
  | Some address =>
      match effective_address m.(declared_type).(memory_address_type)
          address offset 1 (mem_length m.(contents)) with
      | None => None
      | Some ea => mem_lookup ea m.(contents)
      end
  end.

(** Progress for an in-bounds byte access uses the actual memory interface
    implementation; the bounds predicate is not substituted for the read. *)
Lemma load_byte_in_bounds m base address offset :
  address_of_value m.(declared_type).(memory_address_type) base = Some address ->
  (offset < address_bound m.(declared_type).(memory_address_type))%N ->
  (address + offset + 1 <= mem_length m.(contents))%N ->
  exists b, load_byte m base offset = Some b.
Proof.
  intros Hbase Hoff Hbound.
  assert (effective_address m.(declared_type).(memory_address_type)
      address offset 1 (mem_length m.(contents)) = Some (address + offset)%N)
    as Hea.
  { apply effective_address_spec. split.
    - eapply address_of_value_bound. exact Hbase.
    - split; [exact Hoff |]. split; [reflexivity | exact Hbound]. }
  unfold load_byte. rewrite Hbase, Hea.
  destruct (mem_lookup (address + offset)%N m.(contents)) eqn:Hlookup.
  - eauto.
  - exfalso.
    assert (address + offset < mem_length m.(contents))%N as Hinside by lia.
    exact (mem_lookup_ib Hinside Hlookup).
Qed.

Lemma load_byte_sound m base offset b :
  load_byte m base offset = Some b ->
  exists address,
    address_of_value m.(declared_type).(memory_address_type) base = Some address /\
    (offset < address_bound m.(declared_type).(memory_address_type))%N /\
    (address + offset < mem_length m.(contents))%N /\
    mem_lookup (address + offset)%N m.(contents) = Some b.
Proof.
  unfold load_byte.
  destruct (address_of_value _ _) as [address|] eqn:Hbase; [|discriminate].
  destruct (effective_address _ _ _ _ _) as [ea|] eqn:Hea; [|discriminate].
  apply effective_address_spec in Hea as [_ [Hoff [-> Hbound]]].
  intros Hlookup. exists address. repeat split; auto; lia.
Qed.

End Operations.
End AddressingMemory.
