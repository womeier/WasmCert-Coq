(* Actual Extraction_instance entry points.  Adapted from exact fe3c7ea,
   with canonical imports and closed configurations.  Parsing below is an
   actual-parser-result premise, not a claim of whole-module codec verification. *)
From Stdlib Require Import List Strings.String Relations.Relation_Operators Lia.
From mathcomp Require Import ssrbool.
From Wasm Require Import datatypes operations typing opsem type_preservation type_progress
  instantiation_spec instantiation_sound interp_instantiate_sound extraction_instance
  typing_inversion closed_typing_properties module_validation_complete
  extended_const_complete canonical_import_properties.

Section Generic.
Context `{ho : host}.

Lemma configuration_empty_values_nil s f vs :
  config_typing s (f, v_to_e_list vs) nil -> vs = nil.
Proof.
  intros [Store Thread].
  destruct (et_thread_typing Thread) as [C [Frame Typed]].
  destruct (Values_typing_inversion Typed) as [ts [Subtype Values]].
  pose proof (closed_instr_size_exact _ _ _ _ _ Subtype) as Size.
  pose proof (closed_values_length _ _ _ Values) as Count.
  rewrite lift_closed_result_length in Size.
  destruct vs; [reflexivity|]. simpl in Count, Size. lia.
Qed.

Lemma configuration_preservation_trans x y ts :
  reduce_trans x y ->
  (let '(_, s, f, es) := x in config_typing s (f, es) ts) ->
  (let '(_, s, f, es) := y in config_typing s (f, es) ts).
Proof.
  intro Reduction; induction Reduction as [x y Step|x|x y z First IHfirst Last IHlast].
  - destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
    cbn in *. now apply (t_preservation Step).
  - trivial.
  - intro Typed; apply IHlast. now apply IHfirst.
Qed.
End Generic.

Module Closed_extraction_safety (PH : Parametric_host).
Module Runtime := Extraction_instance PH.
Import Runtime.

Definition extracted_step_outcome hs cfg depth :=
  match Runtime.run_one_step hs cfg depth with
  | RSC_normal _ cfg' _ _ _ => ctx_cfg_typing cfg' nil
  | RSC_value s f vs _ => vs = nil /\ config_typing s (f, v_to_e_list vs) nil
  | RSC_trap s f _ => config_typing s (f, AI_trap :: nil) nil
  | RSC_invalid _ => False
  | RSC_error _ => False
  end.

Definition extracted_step_shape hs cfg depth :=
  match Runtime.run_one_step hs cfg depth with
  | RSC_normal _ cfg' _ _ _ => valid_cfg_ctx cfg'
  | _ => True
  end.

Lemma extracted_step_reforms_shape hs cfg depth :
  extracted_step_shape hs cfg depth.
Proof.
  unfold extracted_step_shape, Runtime.run_one_step, interpreter_ctx.run_one_step.
  destruct (@interpreter_ctx.run_one_step_ctx PH.hfc extraction_instance.memory_instance
    Runtime.host_instance Runtime.host_apply_pure Runtime.host_application_impl_correct hs cfg depth)
    as [hs' cfg' depth' Reduction Shape|s f vs Fill|s f Fill|Invalid|Error];
    try exact I.
  destruct cfg' as [[[s ccs] sc] oe].
  cbn -[interpreter_ctx.run_step_reform_valid].
  match goal with
  | |- context [interpreter_ctx.run_step_reform_valid ?s ?sc ?oe ?Valid] =>
      destruct (interpreter_ctx.run_step_reform_valid s sc oe Valid)
        as [reformed [Reform [Fill ValidShape]]]
  end.
  exact ValidShape.
Qed.

Lemma extracted_step_typed hs cfg depth :
  valid_cfg_ctx cfg -> ctx_cfg_typing cfg nil -> extracted_step_outcome hs cfg depth.
Proof.
  intros Valid Typed. unfold extracted_step_outcome.
  destruct (Runtime.run_one_step hs cfg depth)
    as [hs' cfg' depth' Reduction Shape|s f vs Fill|s f Fill|Invalid|Error].
  - unfold reduce_ctx in Reduction. unfold ctx_cfg_typing in *.
    destruct (ctx_to_cfg cfg) as [[s [f es]]|] eqn:Before; [|contradiction].
    destruct (ctx_to_cfg cfg') as [[s' [f' es']]|] eqn:After; [|contradiction].
    now apply (t_preservation Reduction).
  - unfold ctx_cfg_typing in Typed. rewrite Fill in Typed.
    split; [now apply (configuration_empty_values_nil _ _ _ Typed)|exact Typed].
  - unfold ctx_cfg_typing in Typed. now rewrite Fill in Typed.
  - exact (Invalid Valid).
  - exact (Error nil Typed).
Qed.

Fixpoint extracted_execution_prefix_safe fuel hs cfg depth : Prop :=
  valid_cfg_ctx cfg /\ ctx_cfg_typing cfg nil /\
  match fuel with
  | 0 => True
  | S remaining =>
      match Runtime.run_one_step hs cfg depth with
      | RSC_normal hs' cfg' depth' _ _ =>
          extracted_execution_prefix_safe remaining hs' cfg' depth'
      | RSC_value s f vs _ => vs = nil /\ config_typing s (f, v_to_e_list vs) nil
      | RSC_trap s f _ => config_typing s (f, AI_trap :: nil) nil
      | RSC_invalid _ => False
      | RSC_error _ => False
      end
  end.

Lemma extracted_execution_prefix_typed fuel hs cfg depth :
  valid_cfg_ctx cfg -> ctx_cfg_typing cfg nil ->
  extracted_execution_prefix_safe fuel hs cfg depth.
Proof.
  revert hs cfg depth; induction fuel as [|remaining IH]; intros hs cfg depth Valid Typed.
  - split; [exact Valid|split; [exact Typed|exact I]].
  - split; [exact Valid|split; [exact Typed|]].
    pose proof (extracted_step_typed hs cfg depth Valid Typed) as Step.
    pose proof (extracted_step_reforms_shape hs cfg depth) as Shape.
    unfold extracted_step_outcome in Step. unfold extracted_step_shape in Shape.
    cbn -[Runtime.run_one_step].
    destruct (Runtime.run_one_step hs cfg depth)
      as [hs' cfg' depth' Reduction ValidCC|s f vs Fill|s f Fill|Invalid|Error];
      try exact Step.
    now apply IH.
Qed.

Theorem extracted_instantiate_wrapper_configuration hs s m imps s' f es message :
  store_typing s ->
  Runtime.interp_instantiate_wrapper hs s m imps =
    (Some (s', (f, es)), message) ->
  config_typing s' (f, es) nil /\ store_extension s s'.
Proof.
  intros Store Run. unfold Runtime.interp_instantiate_wrapper in Run.
  destruct (instantiation_func.interp_instantiate hs s m imps)
    as [[[[[hs0 s0] f0] code]|] str] eqn:Instantiated; [|discriminate].
  injection Run as Stores Frames Code Message. subst s0 f0 es.
  eapply instantiation_sound_configuration; [exact Store|].
  eapply interp_instantiate_imp_instantiate; exact Instantiated.
Qed.

Theorem extracted_instantiate_reachable_safety hs s m imps s0 f0 es0 message
    hs1 s1 f1 es1 :
  store_typing s ->
  Runtime.interp_instantiate_wrapper hs s m imps =
    (Some (s0, (f0, es0)), message) ->
  reduce_trans (hs, s0, f0, es0) (hs1, s1, f1, es1) ->
  config_typing s1 (f1, es1) nil /\
  (terminal_form es1 \/ exists hs2 s2 f2 es2, reduce hs1 s1 f1 es1 hs2 s2 f2 es2).
Proof.
  intros Store Run Reduction.
  destruct (extracted_instantiate_wrapper_configuration hs s m imps s0 f0 es0
    message Store Run) as [Initial Extension].
  assert (Typed : config_typing s1 (f1, es1) nil).
  { exact (configuration_preservation_trans _ _ _ Reduction Initial). }
  split; [exact Typed|].
  eapply t_progress_interp_ctx; [exact Runtime.host_application_impl_correct|exact Typed].
Qed.

Theorem extracted_valid_binary_execution_complete source m hs s
    imps actual expected exports :
  Runtime.run_parse_module_str source = Some m ->
  instantiation_spec.module_typing m expected exports ->
  store_typing s ->
  List.Forall2 (external_typing s) imps actual ->
  canonical_module_imports s m actual ->
  exists s' f code,
    Runtime.interp_instantiate_wrapper hs s m imps =
      (Some (s', (f, to_e_list code)), String.EmptyString) /\
    store_extension s s' /\
    forall fuel depth,
      extracted_execution_prefix_safe fuel hs
        (proj1_sig (Runtime.interp_cfg_of_wasm (s', (f, to_e_list code)))) depth.
Proof.
  intros Parsed Valid Store Imports Matching.
  pose proof (module_type_checker_complete m expected exports Valid) as Checked.
  destruct (interp_instantiate_complete hs s m imps actual expected exports
    _ Store Checked Imports Matching) as [s' [f [code Run]]].
  assert (Wrapper : Runtime.interp_instantiate_wrapper hs s m imps =
      (Some (s', (f, to_e_list code)), String.EmptyString)).
  { unfold Runtime.interp_instantiate_wrapper. now rewrite Run. }
  destruct (extracted_instantiate_wrapper_configuration hs s m imps s' f
    (to_e_list code) String.EmptyString Store Wrapper) as [Typed Extension].
  exists s', f, code. split; [exact Wrapper|split; [exact Extension|]].
  intros fuel depth.
  destruct (Runtime.interp_cfg_of_wasm (s', (f, to_e_list code))) as [cfg [Fill Shape]].
  cbn. apply extracted_execution_prefix_typed; [exact Shape|].
  unfold ctx_cfg_typing. now rewrite Fill.
Qed.

End Closed_extraction_safety.
