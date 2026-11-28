(** Connect the production binary codec, relational validator and sequential
    initializer/allocator, including typing of generated segment/start code.
    Execution may trap as permitted by the specification. *)
From Stdlib Require Import List.
From mathcomp Require Import ssrbool.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_module_grammar binary_format_module_sound
  binary_format_module_complete binary_format_module_roundtrip
  module_validation_complete instantiation_func instantiation_spec
  interp_instantiate_sound instantiation_sound extended_const_complete.

Section Host.
Context `{ho : host}.

Theorem binary_valid_module_instantiation_complete bytes m hs s
    v_imps t_imps t_imps_mod t_exps :
  module_binary_encoding bytes m ->
  module_typing m t_imps_mod t_exps ->
  store_typing s ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.Forall2 import_subtyping t_imps t_imps_mod ->
  exists s' f es,
    run_parse_module bytes = Some m /\
    interp_instantiate hs s m v_imps =
      (Some (hs, s', f, es), String.EmptyString) /\
    instantiate s m v_imps (s', f, es) /\
    store_typing s' /\ store_extension s s' /\
    (exists C, frame_typing s' f C).
Proof.
  intros Encoding Valid Store Imports Subtypes.
  pose proof (module_type_checker_complete m t_imps_mod t_exps Valid) as Check.
  destruct (interp_instantiate_complete hs s m v_imps t_imps t_imps_mod t_exps
    _ Store Check Imports Subtypes) as [s' [f [es Run]]].
  assert (Relational : instantiate s m v_imps (s', f, es)).
  { eapply interp_instantiate_imp_instantiate; exact Run. }
  assert (Typed : store_typing s' /\ store_extension s s' /\
    (exists C, frame_typing s' f C)).
  { eapply instantiation_sound; eauto. }
  exists s', f, es; split; [now apply run_parse_module_general_complete |].
  split; [exact Run |split; assumption].
Qed.

Corollary printed_valid_module_instantiation_complete m hs s
    v_imps t_imps t_imps_mod t_exps :
  module_binary_wf m ->
  module_typing m t_imps_mod t_exps ->
  store_typing s ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.Forall2 import_subtyping t_imps t_imps_mod ->
  exists s' f es,
    run_parse_module (binary_of_module m) = Some m /\
    interp_instantiate hs s m v_imps =
      (Some (hs, s', f, es), String.EmptyString) /\
    instantiate s m v_imps (s', f, es) /\
    store_typing s' /\ store_extension s s' /\
    (exists C, frame_typing s' f C).
Proof.
  intros Wire Valid Store Imports Subtypes.
  apply (binary_valid_module_instantiation_complete (binary_of_module m) m hs s
    v_imps t_imps t_imps_mod t_exps); try assumption.
  apply run_parse_module_general_sound; now apply binary_of_module_roundtrip.
Qed.

Theorem binary_valid_module_configuration_complete bytes m hs s
    v_imps t_imps t_imps_mod t_exps :
  module_binary_encoding bytes m ->
  module_typing m t_imps_mod t_exps ->
  store_typing s ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.Forall2 import_subtyping t_imps t_imps_mod ->
  exists s' f code,
    run_parse_module bytes = Some m /\
    interp_instantiate hs s m v_imps =
      (Some (hs, s', f, code), String.EmptyString) /\
    config_typing s' (f, operations.to_e_list code) nil /\
    store_extension s s'.
Proof.
  intros Encoding Valid Store Imports Subtypes.
  destruct (binary_valid_module_instantiation_complete bytes m hs s
    v_imps t_imps t_imps_mod t_exps Encoding Valid Store Imports Subtypes)
    as [s' [f [code [Parsed [Run [Instantiated Typed]]]]]].
  exists s', f, code; split; [exact Parsed |].
  split; [exact Run |].
  now apply (instantiation_sound_configuration Store Instantiated).
Qed.
End Host.
