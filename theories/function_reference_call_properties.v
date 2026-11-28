(** Reference-call integration at the GC-owned canonical identity boundary.
    These lemmas do not equate source signatures from different modules and do
    not enable validation before closed operand typing/transport is available. *)
From Wasm Require Import typing properties gc_type_context gc_runtime_type_properties
  gc_type_context_properties opsem.
From Stdlib Require Import List NArith Lia.
From mathcomp Require Import ssrbool.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma reference_call_expected_operand inst index id nullable :
  resolve_inst_type inst index = Some id ->
  close_value_type inst.(inst_defined_types) 0
    (T_ref (Ref_type nullable (HT_type index))) =
  Some (CV_ref nullable (CH_defined (CT_def id))).
Proof.
  unfold resolve_inst_type, lookup_N.
  intro Lookup.
  assert (Bound : (index < N.of_nat (length inst.(inst_defined_types)))%N).
  { assert (B : (N.to_nat index < length inst.(inst_defined_types))%nat).
    { apply nth_error_Some. rewrite Lookup. discriminate. }
    lia. }
  unfold close_value_type, close_heap_type. simpl.
  rewrite (close_type_index_prior _ _ _ _ Bound Lookup). reflexivity.
Qed.

(** Canonical identity agreement supplies a common CLOSED signature even when
    the caller and producer use different local indices for its reference leaves.
    Native and host functions are covered by the same production lookup API. *)
Theorem reference_call_target_signature s inst C index expected address id :
  store_typing s ->
  inst_typing s inst = Some C ->
  lookup_function_type inst.(inst_types) index = Some expected ->
  resolve_inst_type inst index = Some id ->
  lookup_func_defined_type s address = Some id ->
  exists fi signature,
    lookup_N s.(s_funcs) address = Some fi /\
    close_function_type inst.(inst_defined_types) 0 expected = Some signature /\
    close_function_type (funcinst_type_names fi) 0 (cl_type fi) = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Store Instance Expected Resolved Target.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Instance Expected)
    as [expected_id [signature [Identity [Closed Expanded]]]].
  rewrite Resolved in Identity. injection Identity as Same. subst expected_id.
  pose proof Target as TargetLookup.
  unfold lookup_func_defined_type in TargetLookup.
  destruct (lookup_N s.(s_funcs) address) as [fi|] eqn:Function;
    [|discriminate].
  destruct (store_typing_function_expansion_agreement _ _ _ Store Function)
    as [actual_id [actual_signature [Actual [ActualClosed ActualExpanded]]]].
  rewrite Target in Actual. injection Actual as Same. subst actual_id.
  rewrite Expanded in ActualExpanded.
  injection ActualExpanded as Same. subst actual_signature.
  exists fi, signature. repeat split; assumption.
Qed.

Theorem reference_call_target_signature_extension s s' inst C index expected address id :
  store_typing s ->
  store_extension s s' ->
  inst_typing s inst = Some C ->
  lookup_function_type inst.(inst_types) index = Some expected ->
  resolve_inst_type inst index = Some id ->
  lookup_func_defined_type s address = Some id ->
  exists fi signature,
    lookup_N s'.(s_funcs) address = Some fi /\
    lookup_func_defined_type s' address = Some id /\
    close_function_type inst.(inst_defined_types) 0 expected = Some signature /\
    close_function_type (funcinst_type_names fi) 0 (cl_type fi) = Some signature /\
    expand_function_type s'.(s_types) id = Some signature.
Proof.
  intros Store Extension Instance Expected Resolved Target.
  destruct (reference_call_target_signature Store Instance Expected Resolved Target)
    as [fi [signature [Function [Closed [ActualClosed Expanded]]]]].
  exists fi, signature. split.
  - now apply (store_extension_lookup_func Extension).
  - split.
    + now apply (store_extension_native_function_identity _ _ _ _ Extension).
    + split; [exact Closed |]. split; [exact ActualClosed |].
      now apply (store_extension_function_expansion _ _ _ _ Extension).
Qed.

(** Actual dispatch has no dynamic signature check. The eventual operand
    typing inversion must supply the canonical identity premise above. *)
Theorem reference_call_dispatch_signature s f C index expected address id hs :
  store_typing s ->
  inst_typing s f.(f_inst) = Some C ->
  lookup_function_type f.(f_inst).(inst_types) index = Some expected ->
  resolve_inst_type f.(f_inst) index = Some id ->
  lookup_func_defined_type s address = Some id ->
  (reduce hs s f [AI_ref address; AI_basic (BI_call_ref index)]
     hs s f [AI_invoke address] /\
   reduce hs s f [AI_ref address; AI_basic (BI_return_call_ref index)]
     hs s f [AI_return_invoke address]) /\
  exists fi signature,
    lookup_N s.(s_funcs) address = Some fi /\
    close_function_type f.(f_inst).(inst_defined_types) 0 expected = Some signature /\
    close_function_type (funcinst_type_names fi) 0 (cl_type fi) = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Store Instance Expected Resolved Target.
  split.
  - split; [apply r_call_ref | apply r_return_call_ref].
  - exact (reference_call_target_signature Store Instance Expected Resolved Target).
Qed.

End Host.
