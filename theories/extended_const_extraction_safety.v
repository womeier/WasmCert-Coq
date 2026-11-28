(** Safety through the actual parametric extraction entry points.
    PH is the existing trusted host contract, not a new host implementation. *)
From Stdlib Require Import List Strings.String Relations.Relation_Operators Lia.
From mathcomp Require Import ssrbool.
From Wasm Require Import datatypes operations typing opsem type_preservation type_progress
  instantiation_spec instantiation_sound interp_instantiate_sound extraction_instance
  typing_inversion subtyping_properties
  binary_format_module_grammar binary_format_module_sound binary_format_module_roundtrip
  binary_format_printer extended_const_end_to_end.

Section Generic.
Context `{ho : host}.

Lemma configuration_empty_values_nil s f vs :
  config_typing s (f, v_to_e_list vs) nil -> vs = nil.
Proof.
  intros [Store Thread].
  destruct (et_thread_typing Thread) as [C [Frame Typed]].
  destruct (Values_typing_inversion Typed) as [ts [Subtype Values]].
  pose proof (instr_subtyping_size_exact Subtype) as Size.
  pose proof (values_typing_size Values) as Count.
  repeat rewrite ssrnat.addn0 in Size; repeat rewrite ssrnat.add0n in Size.
  destruct vs as [|v rest]; [reflexivity |].
  cbn in Count, Size; lia.
Qed.

Lemma configuration_preservation_trans x y ts :
  reduce_trans x y ->
  (let '(_, s, f, es) := x in config_typing s (f, es) ts) ->
  (let '(_, s, f, es) := y in config_typing s (f, es) ts).
Proof.
  intro Reduction; induction Reduction as [x y Step|x|x y z First IHfirst Last IHlast].
  - destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
    cbn in *; now apply (t_preservation Step).
  - trivial.
  - intro Typed; apply IHlast; now apply IHfirst.
Qed.
End Generic.

Module Extended_const_extraction_safety (PH : Parametric_host).
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
  valid_cfg_ctx cfg ->
  ctx_cfg_typing cfg nil ->
  extracted_step_outcome hs cfg depth.
Proof.
  intros Valid Typed; unfold extracted_step_outcome.
  destruct (Runtime.run_one_step hs cfg depth)
    as [hs' cfg' depth' Reduction Shape|s f vs Fill|s f Fill|Invalid|Error].
  - unfold reduce_ctx in Reduction; unfold ctx_cfg_typing in *.
    destruct (ctx_to_cfg cfg) as [[s [f es]]|] eqn:Before; [|contradiction].
    destruct (ctx_to_cfg cfg') as [[s' [f' es']]|] eqn:After; [|contradiction].
    now apply (t_preservation Reduction).
  - unfold ctx_cfg_typing in Typed; rewrite Fill in Typed.
    split; [now apply (configuration_empty_values_nil _ _ _ Typed) |exact Typed].
  - unfold ctx_cfg_typing in Typed; now rewrite Fill in Typed.
  - exact (Invalid Valid).
  - exact (Error nil Typed).
Qed.

(** A logical observation of finite prefixes of the actual extracted step
    entry point, not a replacement evaluator. Normal steps preserve both
    representation validity and empty-result configuration typing. Values and
    traps are allowed; invalid/ill-typed outcomes are excluded. *)
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
  valid_cfg_ctx cfg ->
  ctx_cfg_typing cfg nil ->
  extracted_execution_prefix_safe fuel hs cfg depth.
Proof.
  revert hs cfg depth; induction fuel as [|remaining IH]; intros hs cfg depth Valid Typed.
  - split; [exact Valid |split; [exact Typed |exact I]].
  - split; [exact Valid |split; [exact Typed |]].
  pose proof (extracted_step_typed hs cfg depth Valid Typed) as Step.
  pose proof (extracted_step_reforms_shape hs cfg depth) as Shape.
  unfold extracted_step_outcome in Step; unfold extracted_step_shape in Shape.
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
  intros Store Run.
  unfold Runtime.interp_instantiate_wrapper in Run.
  destruct (instantiation_func.interp_instantiate hs s m imps)
    as [[[[[hs0 s0] f0] code]|] str] eqn:Instantiated; [|discriminate].
  injection Run as Stores Frames Code Message; subst s0 f0 es.
  eapply instantiation_sound_configuration; [exact Store |].
  eapply interp_instantiate_imp_instantiate; exact Instantiated.
Qed.

Theorem extracted_instantiate_reachable_safety hs s m imps s0 f0 es0 message
    hs1 s1 f1 es1 :
  store_typing s ->
  Runtime.interp_instantiate_wrapper hs s m imps =
    (Some (s0, (f0, es0)), message) ->
  reduce_trans (hs, s0, f0, es0) (hs1, s1, f1, es1) ->
  config_typing s1 (f1, es1) nil /\
    (terminal_form es1 \/
      exists hs2 s2 f2 es2, reduce hs1 s1 f1 es1 hs2 s2 f2 es2).
Proof.
  intros Store Run Reduction.
  destruct (extracted_instantiate_wrapper_configuration hs s m imps s0 f0 es0
    message Store Run) as [Initial Extension].
  assert (Typed : config_typing s1 (f1, es1) nil).
  { exact (configuration_preservation_trans _ _ _ Reduction Initial). }
  split; [exact Typed |].
  eapply t_progress_interp_ctx; [exact Runtime.host_application_impl_correct |exact Typed].
Qed.

Theorem extracted_instantiate_first_step hs s m imps s0 f0 es0 message depth :
  store_typing s ->
  Runtime.interp_instantiate_wrapper hs s m imps =
    (Some (s0, (f0, es0)), message) ->
  let cfg := proj1_sig (Runtime.interp_cfg_of_wasm (s0, (f0, es0))) in
  extracted_step_outcome hs cfg depth.
Proof.
  intros Store Run.
  destruct (Runtime.interp_cfg_of_wasm (s0, (f0, es0))) as [cfg [Fill Valid]].
  cbn; apply extracted_step_typed; [exact Valid |].
  unfold ctx_cfg_typing; rewrite Fill.
  exact (proj1 (extracted_instantiate_wrapper_configuration hs s m imps s0 f0 es0
    message Store Run)).
Qed.

Theorem extracted_valid_binary_configuration_complete source m hs s
    imps actual expected exports :
  module_binary_encoding (String.list_byte_of_string source) m ->
  instantiation_spec.module_typing m expected exports ->
  store_typing s ->
  List.Forall2 (external_typing s) imps actual ->
  List.Forall2 instantiation_spec.import_subtyping actual expected ->
  exists s' f code,
    Runtime.run_parse_module_str source = Some m /\
    Runtime.interp_instantiate_wrapper hs s m imps =
      (Some (s', (f, to_e_list code)), String.EmptyString) /\
    config_typing s' (f, to_e_list code) nil /\ store_extension s s'.
Proof.
  intros Encoding Valid Store Imports Subtypes.
  destruct (binary_valid_module_configuration_complete
    (String.list_byte_of_string source) m hs s imps actual expected exports
    Encoding Valid Store Imports Subtypes)
    as [s' [f [code [Parsed [Run [Typed Extension]]]]]].
  exists s', f, code; split; [exact Parsed |].
  split.
  - unfold Runtime.interp_instantiate_wrapper; now rewrite Run.
  - split; assumption.
Qed.

Theorem extracted_valid_binary_execution_complete source m hs s
    imps actual expected exports :
  module_binary_encoding (String.list_byte_of_string source) m ->
  instantiation_spec.module_typing m expected exports ->
  store_typing s ->
  List.Forall2 (external_typing s) imps actual ->
  List.Forall2 instantiation_spec.import_subtyping actual expected ->
  exists s' f code,
    Runtime.run_parse_module_str source = Some m /\
    Runtime.interp_instantiate_wrapper hs s m imps =
      (Some (s', (f, to_e_list code)), String.EmptyString) /\
    forall fuel depth,
      extracted_execution_prefix_safe fuel hs
        (proj1_sig (Runtime.interp_cfg_of_wasm (s', (f, to_e_list code)))) depth.
Proof.
  intros Encoding Valid Store Imports Subtypes.
  destruct (extracted_valid_binary_configuration_complete source m hs s imps
    actual expected exports Encoding Valid Store Imports Subtypes)
    as [s' [f [code [Parsed [Run [Typed Extension]]]]]].
  exists s', f, code; split; [exact Parsed |split; [exact Run |]].
  intros fuel depth.
  destruct (Runtime.interp_cfg_of_wasm (s', (f, to_e_list code)))
    as [cfg [Fill Shape]].
  cbn; apply extracted_execution_prefix_typed; [exact Shape |].
  unfold ctx_cfg_typing; now rewrite Fill.
Qed.

Corollary extracted_printed_valid_module_execution_complete m hs s
    imps actual expected exports :
  module_binary_wf m ->
  instantiation_spec.module_typing m expected exports ->
  store_typing s ->
  List.Forall2 (external_typing s) imps actual ->
  List.Forall2 instantiation_spec.import_subtyping actual expected ->
  exists s' f code,
    Runtime.run_parse_module_str (String.string_of_list_byte (binary_of_module m)) = Some m /\
    Runtime.interp_instantiate_wrapper hs s m imps =
      (Some (s', (f, to_e_list code)), String.EmptyString) /\
    forall fuel depth,
      extracted_execution_prefix_safe fuel hs
        (proj1_sig (Runtime.interp_cfg_of_wasm (s', (f, to_e_list code)))) depth.
Proof.
  intros Wire Valid Store Imports Subtypes.
  apply (extracted_valid_binary_execution_complete
    (String.string_of_list_byte (binary_of_module m)) m hs s imps actual expected exports);
    try assumption.
  rewrite String.list_byte_of_string_of_list_byte.
  apply run_parse_module_general_sound; now apply binary_of_module_roundtrip.
Qed.
End Extended_const_extraction_safety.
