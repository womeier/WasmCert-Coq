(** Final covariant tail-call typing. Result matching is not equality once
    non-null and nullable references share the production type system. *)
From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Wasm Require Import typing subtyping_properties.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma tail_result_covariance_not_equality :
    [::T_ref (Ref_type false HT_func)] <ts: [::T_ref T_funcref] /\
    [::T_ref (Ref_type false HT_func)] <> [::T_ref T_funcref].
Proof.
  split; [vm_compute; reflexivity | discriminate].
Qed.

Section Host.
Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.

(** These bridges no longer collapse covariance to equality and no longer need
    the old non-bottom-result side condition. *)
Lemma bet_return_call_matching : forall C x args results returns prefix outputs,
    lookup_N (tc_funcs C) x = Some (Tf args results) ->
    tc_return C = Some returns ->
    results <ts: returns ->
    be_typing C (BI_return_call x :: nil) (Tf (prefix ++ args) outputs).
Proof.
  intros C x args results returns prefix outputs Hfunc Hret Hsub.
  by eapply bet_return_call; eauto.
Qed.

Lemma bet_return_call_indirect_matching :
    forall C x y tab args results returns prefix outputs,
    lookup_N (tc_tables C) x = Some tab ->
    ref_heap (tt_elem_type tab) = HT_func ->
    lookup_function_type (tc_types C) y = Some (Tf args results) ->
    tc_return C = Some returns ->
    results <ts: returns ->
    be_typing C (BI_return_call_indirect x y :: nil)
      (Tf (prefix ++ args ++ (T_num T_i32 :: nil)) outputs).
Proof.
  intros C x y tab args results returns prefix outputs
    Htab Helem Htype Hret Hsub.
  by eapply bet_return_call_indirect; eauto.
Qed.
End Host.
