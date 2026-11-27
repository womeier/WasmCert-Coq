(** Alignment of tail-call result matching with the current type fragment.
    Wasm 3.0 permits covariant results. For the concrete types represented here,
    matching is equality: T_bot is an internal stack type, not a binary result
    type. Typed/non-null references will require extending this bridge and the
    tail-call rules together with the function-references development. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Wasm Require Import typing subtyping_properties.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma tail_call_results_match : forall ts us,
    List.Forall (fun t => t <> T_bot) ts ->
    ts <ts: us ->
    ts = us.
Proof.
  move => ts us Htypes.
  move: us.
  induction Htypes as [| t ts Ht Hts IH]; intros [| u us] Hsub => //.
  move/andP: Hsub => [Hhead Htail].
  unfold value_subtyping in Hhead.
  move/orP: Hhead => [/eqP Heq | /eqP Hbot]; last by contradiction.
  subst u.
  by rewrite (IH us Htail).
Qed.

Section Host.
Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.

(** The final matching premise derives the existing rule for every concrete
    result type in this fragment, without changing validator/proof assumptions. *)
Lemma bet_return_call_matching : forall C x args results returns prefix outputs,
    lookup_N (tc_funcs C) x = Some (Tf args results) ->
    tc_return C = Some returns ->
    List.Forall (fun t => t <> T_bot) results ->
    results <ts: returns ->
    be_typing C (BI_return_call x :: nil) (Tf (prefix ++ args) outputs).
Proof.
  intros C x args results returns prefix outputs Hfunc Hret Htypes Hsub.
  apply tail_call_results_match in Hsub => //.
  subst returns.
  by eapply bet_return_call; eauto.
Qed.

Lemma bet_return_call_indirect_matching :
    forall C x y tab args results returns prefix outputs,
    lookup_N (tc_tables C) x = Some tab ->
    tt_elem_type tab = T_funcref ->
    lookup_N (tc_types C) y = Some (Tf args results) ->
    tc_return C = Some returns ->
    List.Forall (fun t => t <> T_bot) results ->
    results <ts: returns ->
    be_typing C (BI_return_call_indirect x y :: nil)
      (Tf (prefix ++ args ++ (T_num T_i32 :: nil)) outputs).
Proof.
  intros C x y tab args results returns prefix outputs
    Htab Helem Htype Hret Htypes Hsub.
  apply tail_call_results_match in Hsub => //.
  subst returns.
  by eapply bet_return_call_indirect; eauto.
Qed.
End Host.
