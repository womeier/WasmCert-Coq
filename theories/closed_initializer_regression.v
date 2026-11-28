(* Address bounds alone do not justify canonical ref.func values.  The
   initializer preservation helper predates canonical function registration. *)
From Wasm Require Import typing properties opsem host typing_inversion
  closed_source_translation gc_runtime_type_properties type_preservation instantiation_spec
  closed_initializer_properties.
From Stdlib Require Import List NArith Lia.
Import ListNotations.

Section Initializers.
Context `{ho : host}.

Definition unregistered_function : funcinst :=
  FC_func_native (Tf [] []) empty_moduleinst (Build_module_func N0 [] []).

Definition unregistered_store : store_record :=
  Build_store_record [unregistered_function] [] [] [] [] [] [].

Definition initializer_source : t_context :=
  Build_t_context [] [Tf [] []] [] [] [] [] [] [] [] None [N0] [].

Definition initializer_closed : closed_t_context :=
  Build_t_context [] [Closed_ft [] []] [] [] [] [] [] [] [] None [N0] [].

Definition unregistered_instance : moduleinst :=
  Build_moduleinst [] [N0] [] [] [] [] [] [] [] initializer_source.

Definition unregistered_frame : frame :=
  Build_frame [] unregistered_instance.

Lemma initializer_source_closes :
  close_t_context initializer_source = Some initializer_closed.
Proof. reflexivity. Qed.

Lemma unregistered_initializer_is_constant :
  extended_const_exprs initializer_source [BI_ref_func N0] = true.
Proof. reflexivity. Qed.

Lemma unregistered_initializer_global_contract :
  forall index value descriptor,
    sglob_val unregistered_store unregistered_instance index = Some value ->
    lookup_N initializer_closed.(tc_globals) index = Some descriptor ->
    closed_value_typing unregistered_store value descriptor.(tg_t) = true.
Proof.
  intros index value descriptor Get Lookup.
  unfold lookup_N in Lookup. simpl in Lookup.
  destruct (N.to_nat index); discriminate.
Qed.

Lemma bounded_unregistered_initializer :
  forall n address,
  List.nth_error unregistered_instance.(inst_funcs) n = Some address ->
  (address < N.of_nat (length unregistered_store.(s_funcs)))%N.
Proof.
  intros [|n] address Lookup; simpl in Lookup.
  - inversion Lookup; subst. reflexivity.
  - destruct n; discriminate.
Qed.

Lemma unregistered_initializer_entry :
  e_typing unregistered_store initializer_closed
    [AI_basic (BI_ref_func N0)]
    (Closed_ft [] [CO_value (CV_ref true (CH_abstract HT_func))]).
Proof.
  change (e_typing unregistered_store initializer_closed
    (to_e_list [BI_ref_func N0])
    (interpret_instr_type [] (Tf [] [T_ref T_funcref]))).
  eapply (source_structural_entry unregistered_store initializer_source
    initializer_closed [BI_ref_func N0] (Tf [] [T_ref T_funcref]));
    [|exact initializer_source_closes].
  eapply bet_ref_func; [reflexivity|].
  simpl. now left.
Qed.

Lemma unregistered_initializer_step hs :
  reduce hs unregistered_store unregistered_frame [AI_basic (BI_ref_func N0)]
    hs unregistered_store unregistered_frame [AI_ref N0].
Proof. apply r_ref_func. reflexivity. Qed.

Lemma unregistered_reference_untypable :
  ~ e_typing unregistered_store initializer_closed [AI_ref N0]
    (Closed_ft [] [CO_value (CV_ref true (CH_abstract HT_func))]).
Proof.
  intro Typed.
  change (e_typing unregistered_store initializer_closed
    [v_to_e (VAL_ref (VAL_ref_func N0))]
    (Closed_ft [] [CO_value (CV_ref true (CH_abstract HT_func))])) in Typed.
  destruct (Value_typing_inversion Typed) as [concrete [_ Value]].
  vm_compute in Value. discriminate.
Qed.

Lemma unregistered_store_rejected : ~ store_typing unregistered_store.
Proof.
  intro Store.
  pose proof (function_reference_abstract_typing unregistered_store [] N0
    unregistered_function Store eq_refl) as Value.
  vm_compute in Value. discriminate.
Qed.

Lemma runtime_preserves_registered_references hs s f es hs' s' f' es' results :
  reduce hs s f es hs' s' f' es' ->
  config_typing s (f, es) results ->
  registered_function_references s'.
Proof.
  intros Step Typed.
  apply checked_store_registers_function_references.
  exact (proj1 (t_preservation Step Typed)).
Qed.

End Initializers.
