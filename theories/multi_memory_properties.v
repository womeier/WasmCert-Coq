(** Indexed memarg flag correctness for the helpers used by the binary parser
    and printer. This is not a general LEB128/Parseque correctness theorem. *)
From Stdlib Require Import ZArith Lia.
From Wasm Require Import operations.

Lemma memarg_flags_round_trip : forall marg,
  (memarg_align marg < 64)%N ->
  decode_memarg_flags (memarg_flags marg) =
    Some (memarg_align marg, negb (N.eqb (memarg_memory marg) 0)).
Proof.
  intros [off align x] Halign.
  unfold memarg_flags, decode_memarg_flags; simpl in *.
  destruct (N.eqb x 0).
  - apply N.ltb_lt in Halign. rewrite Halign. reflexivity.
  - assert (Hlo: N.ltb (align + 64) 64 = false) by (apply N.ltb_ge; lia).
    assert (Hhi: N.ltb (align + 64) 128 = true) by (apply N.ltb_lt; lia).
    rewrite Hlo, Hhi.
    replace (align + 64 - 64)%N with align by lia.
    reflexivity.
Qed.

Lemma decoded_memarg_flags_range : forall flags align explicit,
  decode_memarg_flags flags = Some (align, explicit) ->
  (align < 64)%N /\
    flags = (align + if explicit then 64 else 0)%N.
Proof.
  intros flags align explicit Hdecode.
  unfold decode_memarg_flags in Hdecode.
  destruct (N.ltb flags 64) eqn:Hlo.
  - inversion Hdecode; subst. apply N.ltb_lt in Hlo. split; lia.
  - destruct (N.ltb flags 128) eqn:Hhi; try discriminate.
    inversion Hdecode; subst.
    apply N.ltb_ge in Hlo. apply N.ltb_lt in Hhi.
    split; lia.
Qed.

Lemma reserved_memarg_flags_rejected : forall flags,
  (128 <= flags)%N ->
  decode_memarg_flags flags = None.
Proof.
  intros flags Hflags.
  unfold decode_memarg_flags.
  assert (Hlo: N.ltb flags 64 = false) by (apply N.ltb_ge; lia).
  assert (Hhi: N.ltb flags 128 = false) by (apply N.ltb_ge; lia).
  rewrite Hlo, Hhi. reflexivity.
Qed.
