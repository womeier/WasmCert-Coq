(** Address-dependent memory fill/copy over the existing verified block-update
    interface.  The source of a copy is the original memory, including for an
    overlapping self-copy; the generator never reads the updated destination.
    This API is separate from the legacy instruction/store representation. *)
From Wasm Require Import datatypes addressing addressing_memory memory.
From Stdlib Require Import ZArith Lia Bool.
Import Addressing.
Set Implicit Arguments.
Unset Strict Implicit.

Module AddressingBulk.
Section Operations.
Context `{BlockUpdateMemory}.

Definition write_range (dst: AddressingMemory.instance)
    (start len: N) (gen: N -> byte) : option AddressingMemory.instance :=
  if range_valid start len (mem_length dst.(AddressingMemory.contents)) then
    match mem_update_gen start len gen dst.(AddressingMemory.contents) with
    | None => None
    | Some data =>
        Some {| AddressingMemory.declared_type := dst.(AddressingMemory.declared_type);
                AddressingMemory.contents := data |}
    end
  else None.

Lemma write_range_characterization dst start len gen dst' :
  write_range dst start len gen = Some dst' ->
  (start + len <= mem_length dst.(AddressingMemory.contents))%N /\
  dst'.(AddressingMemory.declared_type) = dst.(AddressingMemory.declared_type) /\
  mem_update_gen start len gen dst.(AddressingMemory.contents) =
    Some dst'.(AddressingMemory.contents).
Proof.
  unfold write_range.
  destruct (range_valid _ _ _) eqn:Hrange; [|discriminate].
  apply range_valid_spec in Hrange.
  destruct (mem_update_gen _ _ _ _) eqn:Hwrite; [|discriminate].
  intros Hresult. inversion Hresult; subst. auto.
Qed.

Lemma write_range_progress dst start len gen :
  (start + len <= mem_length dst.(AddressingMemory.contents))%N ->
  exists dst', write_range dst start len gen = Some dst'.
Proof.
  intros Hbound. unfold write_range.
  assert (range_valid start len (mem_length dst.(AddressingMemory.contents)) = true)
    as -> by now apply range_valid_spec.
  destruct (mem_update_gen _ _ _ _) eqn:Hwrite; [eauto |].
  exfalso. exact (mem_update_gen_ib Hbound Hwrite).
Qed.

Lemma write_range_valid dst start len gen dst' :
  AddressingMemory.valid dst ->
  write_range dst start len gen = Some dst' ->
  AddressingMemory.valid dst'.
Proof.
  intros Hvalid Hwrite.
  apply write_range_characterization in Hwrite as [_ [Htype Hwrite]].
  pose proof (mem_update_gen_length Hwrite) as Hlength.
  unfold AddressingMemory.valid, AddressingMemory.size in *.
  unfold memory_from_bum in *.
  rewrite Htype.
  rewrite <- Hlength. assumption.
Qed.

Lemma write_range_lookup dst start len gen dst' i :
  write_range dst start len gen = Some dst' ->
  (i < len)%N ->
  mem_lookup (start + i)%N dst'.(AddressingMemory.contents) = Some (gen i).
Proof.
  intros Hwrite Hi.
  apply write_range_characterization in Hwrite as [_ [_ Hwrite]].
  eapply mem_update_gen_lookup; eassumption.
Qed.

Lemma write_range_unchanged dst start len gen dst' i :
  write_range dst start len gen = Some dst' ->
  ((i < start)%N \/ (start + len <= i)%N) ->
  mem_lookup i dst'.(AddressingMemory.contents) =
    mem_lookup i dst.(AddressingMemory.contents).
Proof.
  intros Hwrite Houtside.
  apply write_range_characterization in Hwrite as [_ [_ Hwrite]].
  destruct Houtside as [Hlt|Hge].
  - eapply mem_update_gen_lookup_lt; eassumption.
  - eapply mem_update_gen_lookup_ge; [exact Hwrite | lia].
Qed.

Definition fill (dst: AddressingMemory.instance) (start len: value_num)
    (b: byte) : option AddressingMemory.instance :=
  let a := dst.(AddressingMemory.declared_type).(memory_address_type) in
  match address_of_value a start, address_of_value a len with
  | Some first, Some count => write_range dst first count (fun _ => b)
  | _, _ => None
  end.

Lemma fill_valid dst start len b dst' :
  AddressingMemory.valid dst ->
  fill dst start len b = Some dst' ->
  AddressingMemory.valid dst'.
Proof.
  intros Hvalid. unfold fill.
  destruct (address_of_value _ start); [|discriminate].
  destruct (address_of_value _ len); [|discriminate].
  eapply write_range_valid. exact Hvalid.
Qed.

Definition copy (dst src: AddressingMemory.instance)
    (dst_start src_start len: value_num) : option AddressingMemory.instance :=
  let dst_a := dst.(AddressingMemory.declared_type).(memory_address_type) in
  let src_a := src.(AddressingMemory.declared_type).(memory_address_type) in
  match address_of_value dst_a dst_start,
        address_of_value src_a src_start,
        address_of_value (copy_address_type dst_a src_a) len with
  | Some first, Some source, Some count =>
      if copy_ranges_valid first source count
          (mem_length dst.(AddressingMemory.contents))
          (mem_length src.(AddressingMemory.contents)) then
        write_range dst first count
          (fun off =>
             match mem_lookup (source + off)%N src.(AddressingMemory.contents) with
             | Some b => b
             | None => wasm_memory_default_byte
             end)
      else None
  | _, _, _ => None
  end.

Lemma copy_characterization dst src dst_start src_start len dst' :
  copy dst src dst_start src_start len = Some dst' ->
  exists first source count,
    address_of_value dst.(AddressingMemory.declared_type).(memory_address_type)
      dst_start = Some first /\
    address_of_value src.(AddressingMemory.declared_type).(memory_address_type)
      src_start = Some source /\
    address_of_value
      (copy_address_type dst.(AddressingMemory.declared_type).(memory_address_type)
                         src.(AddressingMemory.declared_type).(memory_address_type))
      len = Some count /\
    (first + count <= mem_length dst.(AddressingMemory.contents))%N /\
    (source + count <= mem_length src.(AddressingMemory.contents))%N /\
    write_range dst first count
      (fun off =>
         match mem_lookup (source + off)%N src.(AddressingMemory.contents) with
         | Some b => b
         | None => wasm_memory_default_byte
         end) = Some dst'.
Proof.
  unfold copy.
  destruct (address_of_value _ dst_start) as [first|] eqn:Hfirst; [|discriminate].
  destruct (address_of_value _ src_start) as [source|] eqn:Hsource; [|discriminate].
  destruct (address_of_value _ len) as [count|] eqn:Hcount; [|discriminate].
  destruct (copy_ranges_valid _ _ _ _ _) eqn:Hranges; [|discriminate].
  apply copy_ranges_valid_spec in Hranges as [Hdst Hsrc].
  intros Hwrite. exists first, source, count.
  repeat split; assumption || reflexivity.
Qed.

Lemma copy_valid dst src dst_start src_start len dst' :
  AddressingMemory.valid dst ->
  copy dst src dst_start src_start len = Some dst' ->
  AddressingMemory.valid dst'.
Proof.
  intros Hvalid Hcopy.
  apply copy_characterization in Hcopy as
    [first [source [count [_ [_ [_ [_ [_ Hwrite]]]]]]]].
  eapply write_range_valid; eassumption.
Qed.

(** The fallback byte in the generator is unreachable on a successful copy,
    rather than a semantic workaround for an out-of-bounds source read. *)
Lemma copy_source_byte dst src dst_start src_start len dst' :
  copy dst src dst_start src_start len = Some dst' ->
  exists first source count,
    (source + count <= mem_length src.(AddressingMemory.contents))%N /\
    forall i, (i < count)%N ->
      mem_lookup (first + i)%N dst'.(AddressingMemory.contents) =
        mem_lookup (source + i)%N src.(AddressingMemory.contents).
Proof.
  intros Hcopy.
  apply copy_characterization in Hcopy as
    [first [source [count [_ [_ [_ [_ [Hsrc Hwrite]]]]]]]].
  exists first, source, count. split; [assumption |].
  intros i Hi.
  rewrite (write_range_lookup Hwrite Hi).
  destruct (mem_lookup (source + i)%N src.(AddressingMemory.contents))
    eqn:Hlookup; [reflexivity |].
  exfalso.
  assert (source + i < mem_length src.(AddressingMemory.contents))%N as Hinside by lia.
  exact (mem_lookup_ib Hinside Hlookup).
Qed.

End Operations.
End AddressingBulk.
