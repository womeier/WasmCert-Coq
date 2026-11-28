(* Generated administrative sequences use concrete canonical operand stacks.
   Source declarations are consulted only at their singleton entry boundary. *)
From Wasm Require Import typing properties typing_inversion closed_typing_properties
  closed_operand_properties closed_source_translation closed_context_properties
  gc_declaration_typing gc_declaration_typing_properties gc_closed_runtime_properties
  gc_runtime_type_properties gc_function_subtyping_properties.
From Stdlib Require Import List Bool NArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Bulk.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Lemma closed_instruction_cons s C instruction tail inputs middle outputs :
  e_typing s C [::instruction] (Closed_ft inputs middle) ->
  e_typing s C tail (Closed_ft middle outputs) ->
  e_typing s C (instruction :: tail) (Closed_ft inputs outputs).
Proof.
  move => Head Tail.
  change (instruction :: tail) with ([::instruction] ++ tail).
  by eapply et_composition'; eauto.
Qed.

Lemma closed_operand_cons s C value operand tail inputs outputs :
  closed_operand_typing s value operand ->
  e_typing s C tail (Closed_ft (inputs ++ [::operand]) outputs) ->
  e_typing s C (v_to_e value :: tail) (Closed_ft inputs outputs).
Proof.
  destruct operand as [concrete|]; last discriminate.
  move => Value Tail. by eapply value_cons_e_typing; eauto.
Qed.

Lemma closed_instr_input_suffix registry inputs outputs inputs' outputs' suffix :
  closed_instr_subtyping registry (Closed_ft inputs outputs)
    (Closed_ft inputs' outputs') ->
  closed_instr_subtyping registry (Closed_ft (inputs ++ suffix) outputs)
    (Closed_ft (inputs' ++ suffix) outputs').
Proof.
  move => [prefix [prefix' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  exists prefix, prefix', (isub ++ suffix), osub.
  split; first by rewrite catA.
  split; first reflexivity.
  split; first exact Prefix.
  split; last exact Outputs.
  apply closed_stack_results_append; [exact Inputs|apply closed_stack_results_refl].
Qed.

Lemma source_table_entries s source C index raw expected :
  close_t_context source = Some C ->
  lookup_N source.(tc_tables) index = Some raw ->
  close_table_type source.(tc_defined_types) raw = Some expected ->
  e_typing s C [::AI_basic (BI_table_set index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected.(tt_elem_type))] nil) /\
  e_typing s C [::AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected.(tt_elem_type));
      CO_value (CV_num T_i32)] nil).
Proof.
  move => Context Lookup Closed.
  destruct (close_table_type_metadata _ _ _ Closed) as [_ Reference].
  have ValueClosed := close_reference_type_value _ _ _ Reference.
  have Operand : interpret_operand_type (tc_defined_types source)
      (T_ref (tt_elem_type raw)) =
      CO_value (closed_reference_value (tt_elem_type expected)).
  { unfold interpret_operand_type.
    by rewrite (close_concrete_operand _ _ _ ValueClosed). }
  split.
  - have Entry : be_typing source [::BI_table_set index]
      (Tf [::T_num T_i32; T_ref (tt_elem_type raw)] nil).
    { by eapply bet_table_set; eauto. }
    have Typed := source_structural_entry s source C _ _ Entry Context.
    cbn [interpret_instr_type interpret_operand_results List.map] in Typed.
    by rewrite Operand in Typed.
  - have Entry : be_typing source [::BI_table_fill index]
      (Tf [::T_num T_i32; T_ref (tt_elem_type raw); T_num T_i32] nil).
    { by eapply bet_table_fill; eauto. }
    have Typed := source_structural_entry s source C _ _ Entry Context.
    cbn [interpret_instr_type interpret_operand_results List.map] in Typed.
    by rewrite Operand in Typed.
Qed.

Lemma closed_table_fill_continuation s C index ref element next count :
  closed_value_typing s (VAL_ref ref) (closed_reference_value element) ->
  e_typing s C [::AI_basic (BI_table_set index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value element)] nil) ->
  e_typing s C [::AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value element); CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::vref_to_e ref; AI_basic (BI_table_set index);
      $VN (VAL_int32 next); vref_to_e ref; $VN (VAL_int32 count);
      AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32)] nil).
Proof.
  move => Value SetEntry FillEntry.
  change (e_typing s C
    (v_to_e (VAL_ref ref) :: AI_basic (BI_table_set index) ::
      $VN (VAL_int32 next) :: v_to_e (VAL_ref ref) ::
      $VN (VAL_int32 count) :: [::AI_basic (BI_table_fill index)])
    (Closed_ft [::CO_value (CV_num T_i32)] nil)).
  apply (value_cons_e_typing Value).
  eapply closed_instruction_cons; first exact SetEntry.
  apply value_num_cons_e_typing.
  apply (value_cons_e_typing Value).
  apply value_num_cons_e_typing. exact FillEntry.
Qed.

Lemma closed_table_entries_transport s C index actual expected :
  closed_stack_value_subtyping (s_types s)
    (CO_value (closed_reference_value actual))
    (CO_value (closed_reference_value expected)) ->
  e_typing s C [::AI_basic (BI_table_set index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected)] nil) ->
  e_typing s C [::AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected); CO_value (CV_num T_i32)] nil) ->
  e_typing s C [::AI_basic (BI_table_set index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value actual)] nil) /\
  e_typing s C [::AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value actual); CO_value (CV_num T_i32)] nil).
Proof.
  move => Element SetEntry FillEntry. split.
  - eapply ety_subtyping; first exact SetEntry.
    exists nil, nil, [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value actual)], nil.
    split; [reflexivity|]. split; [reflexivity|].
    split; [constructor|]. split; [|constructor].
    constructor; [apply csv_refl|]. constructor; [exact Element|constructor].
  - eapply ety_subtyping; first exact FillEntry.
    exists nil, nil, [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value actual); CO_value (CV_num T_i32)], nil.
    split; [reflexivity|]. split; [reflexivity|].
    split; [constructor|]. split; [|constructor].
    constructor; [apply csv_refl|]. constructor; [exact Element|].
    constructor; [apply csv_refl|constructor].
Qed.

Lemma closed_table_fill_invariant_continuation s C index ref principal expected stored next count :
  canonical_registry_valid s.(s_types) ->
  closed_value_typing s (VAL_ref ref) principal ->
  closed_stack_value_subtyping s.(s_types) (CO_value principal)
    (CO_value (closed_reference_value expected)) ->
  closed_value_matchesb s.(s_types) (closed_reference_value expected)
    (closed_reference_value stored) ->
  closed_value_matchesb s.(s_types) (closed_reference_value stored)
    (closed_reference_value expected) ->
  e_typing s C [::AI_basic (BI_table_set index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected)] nil) ->
  e_typing s C [::AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected); CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::vref_to_e ref; AI_basic (BI_table_set index);
      $VN (VAL_int32 next); vref_to_e ref; $VN (VAL_int32 count);
      AI_basic (BI_table_fill index)]
    (Closed_ft [::CO_value (CV_num T_i32)] nil).
Proof.
  move => Registry Value Subtype Forward Backward SetEntry FillEntry.
  have Expected : closed_value_typing s (VAL_ref ref) (closed_reference_value expected).
  { eapply operand_subtyping_acceptance with (actual := CO_value principal)
      (expected := CO_value (closed_reference_value expected));
      eauto. }
  have Stored : closed_value_typing s (VAL_ref ref) (closed_reference_value stored).
  { eapply operand_subtyping_acceptance with
      (actual := CO_value (closed_reference_value expected))
      (expected := CO_value (closed_reference_value stored)); eauto.
    by apply csv_match. }
  destruct (closed_table_entries_transport (actual := stored)
    (expected := expected) ltac:(apply csv_match; exact Backward) SetEntry FillEntry)
    as [StoredSet StoredFill].
  by eapply closed_table_fill_continuation; eauto.
Qed.

Lemma source_table_copy_entries s source C destination origin raw_destination raw_origin expected :
  close_t_context source = Some C ->
  lookup_N source.(tc_tables) destination = Some raw_destination ->
  lookup_N source.(tc_tables) origin = Some raw_origin ->
  raw_origin.(tt_elem_type) = raw_destination.(tt_elem_type) ->
  close_reference_type source.(tc_defined_types) raw_origin.(tt_elem_type) = Some expected ->
  e_typing s C [::AI_basic (BI_table_get origin)]
    (Closed_ft [::CO_value (CV_num T_i32)]
      [::CO_value (closed_reference_value expected)]) /\
  e_typing s C [::AI_basic (BI_table_set destination)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected)] nil) /\
  e_typing s C [::AI_basic (BI_table_copy destination origin)]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil).
Proof.
  move => Context Destination Origin Same Reference.
  have ValueClosed := close_reference_type_value _ _ _ Reference.
  have Operand : interpret_operand_type (tc_defined_types source)
      (T_ref (tt_elem_type raw_origin)) = CO_value (closed_reference_value expected).
  { unfold interpret_operand_type.
    by rewrite (close_concrete_operand _ _ _ ValueClosed). }
  split.
  - have Entry : be_typing source [::BI_table_get origin]
        (Tf [::T_num T_i32] [::T_ref (tt_elem_type raw_origin)]).
    { by eapply bet_table_get; eauto. }
    have Typed := source_structural_entry s source C _ _ Entry Context.
    cbn [interpret_instr_type interpret_operand_results List.map] in Typed.
    by rewrite Operand in Typed.
  - split.
    + have Entry : be_typing source [::BI_table_set destination]
        (Tf [::T_num T_i32; T_ref (tt_elem_type raw_origin)] nil).
      { by eapply bet_table_set; eauto. }
      have Typed := source_structural_entry s source C _ _ Entry Context.
      cbn [interpret_instr_type interpret_operand_results List.map] in Typed.
      by rewrite Operand in Typed.
    + have Entry : be_typing source [::BI_table_copy destination origin]
        (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] nil).
      { by eapply bet_table_copy; eauto. }
      exact (source_structural_entry s source C _ _ Entry Context).
Qed.

Lemma closed_table_copy_continuation s C destination origin expected stored next_destination next_origin count :
  closed_value_matchesb s.(s_types) (closed_reference_value expected)
    (closed_reference_value stored) ->
  closed_value_matchesb s.(s_types) (closed_reference_value stored)
    (closed_reference_value expected) ->
  e_typing s C [::AI_basic (BI_table_get origin)]
    (Closed_ft [::CO_value (CV_num T_i32)]
      [::CO_value (closed_reference_value expected)]) ->
  e_typing s C [::AI_basic (BI_table_set destination)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected)] nil) ->
  e_typing s C [::AI_basic (BI_table_copy destination origin)]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::AI_basic (BI_table_get origin); AI_basic (BI_table_set destination);
      $VN (VAL_int32 next_destination); $VN (VAL_int32 next_origin);
      $VN (VAL_int32 count); AI_basic (BI_table_copy destination origin)]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)] nil).
Proof.
  move => Forward Backward GetEntry SetEntry CopyEntry.
  have StoredGet : e_typing s C [::AI_basic (BI_table_get origin)]
      (Closed_ft [::CO_value (CV_num T_i32)]
        [::CO_value (closed_reference_value stored)]).
  { eapply ety_subtyping; first exact GetEntry.
    exists nil, nil, [::CO_value (CV_num T_i32)],
      [::CO_value (closed_reference_value stored)].
    split; [reflexivity|]. split; [reflexivity|].
    split; [constructor|]. split.
    - apply closed_stack_results_refl.
    - constructor; [by apply csv_match|constructor]. }
  have StoredSet : e_typing s C [::AI_basic (BI_table_set destination)]
      (Closed_ft [::CO_value (CV_num T_i32);
        CO_value (closed_reference_value stored)] nil).
  { eapply ety_subtyping; first exact SetEntry.
    exists nil, nil, [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value stored)], nil.
    split; [reflexivity|]. split; [reflexivity|].
    split; [constructor|]. split; [|constructor].
    constructor; [apply csv_refl|].
    constructor; [by apply csv_match|constructor]. }
  eapply closed_instruction_cons with
    (middle := [::CO_value (CV_num T_i32); CO_value (closed_reference_value stored)]).
  - eapply ety_subtyping; first exact StoredGet.
    exact (closed_instr_weakening (s_types s) _ _ [::CO_value (CV_num T_i32)]).
  - eapply closed_instruction_cons; first exact StoredSet.
    apply value_num_cons_e_typing.
    apply value_num_cons_e_typing.
    apply value_num_cons_e_typing. exact CopyEntry.
Qed.

Lemma closed_element_read s element actual offset ref :
  eleminst_typing s element = Some actual ->
  lookup_N element.(eleminst_elem) offset = Some ref ->
  closed_value_typing s (VAL_ref ref) (closed_reference_value actual).
Proof.
  destruct element as [descriptor refs].
  cbn [eleminst_typing eleminst_elem].
  destruct (closed_value_validb (s_types s) (closed_reference_value descriptor) &&
    all (fun ref => closed_value_typing s (VAL_ref ref)
      (closed_reference_value descriptor)) refs) eqn:Valid; last discriminate.
  move => Equal Lookup. injection Equal as <-.
  move/andP: Valid => [_ Values].
  unfold lookup_N in Lookup.
  eapply all_projection in Values; [exact Values|exact Lookup].
Qed.

Lemma closed_element_view_read s names address source expected element offset ref :
  store_typing s ->
  instance_element_view s names address source ->
  lookup_N s.(s_elems) address = Some element ->
  close_reference_type names source = Some expected ->
  lookup_N element.(eleminst_elem) offset = Some ref ->
  closed_value_typing s (VAL_ref ref) (closed_reference_value expected).
Proof.
  move => Store View Element Closed Lookup.
  unfold instance_element_view in View. rewrite Element Closed in View.
  destruct (eleminst_typing s element) as [actual|] eqn:Typed; last discriminate.
  move/andP: View => [/andP [Valid Match] _].
  eapply closed_value_typing_subsumption.
  - exact (store_typing_canonical_registry _ Store).
  - by eapply closed_element_read; eauto.
  - exact Valid.
  - exact Match.
Qed.

Lemma source_table_init_entries s source C destination segment raw expected :
  close_t_context source = Some C ->
  lookup_N source.(tc_tables) destination = Some raw ->
  lookup_N source.(tc_elems) segment = Some raw.(tt_elem_type) ->
  close_table_type source.(tc_defined_types) raw = Some expected ->
  e_typing s C [::AI_basic (BI_table_set destination)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected.(tt_elem_type))] nil) /\
  e_typing s C [::AI_basic (BI_table_init destination segment)]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil).
Proof.
  move => Context Table Element Closed.
  destruct (source_table_entries s Context Table Closed) as [SetEntry _].
  split; first exact SetEntry.
  have Entry : be_typing source [::BI_table_init destination segment]
      (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] nil).
  { by eapply bet_table_init; eauto. }
  exact (source_structural_entry s source C _ _ Entry Context).
Qed.

Lemma closed_table_init_continuation s C destination segment ref element next_destination next_origin count :
  closed_value_typing s (VAL_ref ref) (closed_reference_value element) ->
  e_typing s C [::AI_basic (BI_table_set destination)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value element)] nil) ->
  e_typing s C [::AI_basic (BI_table_init destination segment)]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::vref_to_e ref; AI_basic (BI_table_set destination);
      $VN (VAL_int32 next_destination); $VN (VAL_int32 next_origin);
      $VN (VAL_int32 count); AI_basic (BI_table_init destination segment)]
    (Closed_ft [::CO_value (CV_num T_i32)] nil).
Proof.
  move => Value SetEntry InitEntry.
  change (e_typing s C
    (v_to_e (VAL_ref ref) :: AI_basic (BI_table_set destination) ::
      $VN (VAL_int32 next_destination) :: $VN (VAL_int32 next_origin) ::
      $VN (VAL_int32 count) :: [::AI_basic (BI_table_init destination segment)])
    (Closed_ft [::CO_value (CV_num T_i32)] nil)).
  apply (value_cons_e_typing Value).
  eapply closed_instruction_cons; first exact SetEntry.
  apply value_num_cons_e_typing.
  apply value_num_cons_e_typing.
  apply value_num_cons_e_typing. exact InitEntry.
Qed.

Lemma closed_table_init_invariant_continuation s C destination segment ref expected stored
    next_destination next_origin count :
  canonical_registry_valid s.(s_types) ->
  closed_value_typing s (VAL_ref ref) (closed_reference_value expected) ->
  closed_value_matchesb s.(s_types) (closed_reference_value expected)
    (closed_reference_value stored) ->
  closed_value_matchesb s.(s_types) (closed_reference_value stored)
    (closed_reference_value expected) ->
  e_typing s C [::AI_basic (BI_table_set destination)]
    (Closed_ft [::CO_value (CV_num T_i32);
      CO_value (closed_reference_value expected)] nil) ->
  e_typing s C [::AI_basic (BI_table_init destination segment)]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::vref_to_e ref; AI_basic (BI_table_set destination);
      $VN (VAL_int32 next_destination); $VN (VAL_int32 next_origin);
      $VN (VAL_int32 count); AI_basic (BI_table_init destination segment)]
    (Closed_ft [::CO_value (CV_num T_i32)] nil).
Proof.
  move => Registry Value Forward Backward SetEntry InitEntry.
  have Stored : closed_value_typing s (VAL_ref ref) (closed_reference_value stored).
  { eapply operand_subtyping_acceptance with
      (actual := CO_value (closed_reference_value expected))
      (expected := CO_value (closed_reference_value stored)); eauto.
    by apply csv_match. }
  eapply closed_table_init_continuation; [exact Stored| |exact InitEntry].
  eapply ety_subtyping; first exact SetEntry.
  exists nil, nil, [::CO_value (CV_num T_i32);
    CO_value (closed_reference_value stored)], nil.
  split; [reflexivity|]. split; [reflexivity|].
  split; [constructor|]. split; [|constructor].
  constructor; [apply csv_refl|].
  constructor; [by apply csv_match|constructor].
Qed.

Lemma source_memory_byte_entries s source C memory_type :
  close_t_context source = Some C ->
  lookup_N source.(tc_mems) N0 = Some memory_type ->
  e_typing s C
    [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U))
      (Build_memarg N0 N0))]
    (Closed_ft [::CO_value (CV_num T_i32)] [::CO_value (CV_num T_i32)]) /\
  e_typing s C
    [::AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0))]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)] nil).
Proof.
  move => Context Memory. split.
  - have Entry : be_typing source
      [::BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg N0 N0)]
      (Tf [::T_num T_i32] [::T_num T_i32]).
    { eapply bet_load; [exact Memory|reflexivity]. }
    exact (source_structural_entry s source C _ _ Entry Context).
  - have Entry : be_typing source
      [::BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0)]
      (Tf [::T_num T_i32; T_num T_i32] nil).
    { eapply bet_store; [exact Memory|reflexivity]. }
    exact (source_structural_entry s source C _ _ Entry Context).
Qed.

Lemma closed_memory_store_continuation s C operation first second count :
  e_typing s C
    [::AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0))]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)] nil) ->
  e_typing s C [::AI_basic operation]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0));
      $VN (VAL_int32 first); $VN (VAL_int32 second); $VN (VAL_int32 count);
      AI_basic operation]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)] nil).
Proof.
  move => StoreEntry BulkEntry.
  eapply closed_instruction_cons; first exact StoreEntry.
  apply value_num_cons_e_typing.
  apply value_num_cons_e_typing.
  apply value_num_cons_e_typing. exact BulkEntry.
Qed.

Lemma closed_memory_copy_continuation s C first second count :
  e_typing s C
    [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg N0 N0))]
    (Closed_ft [::CO_value (CV_num T_i32)] [::CO_value (CV_num T_i32)]) ->
  e_typing s C
    [::AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0))]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)] nil) ->
  e_typing s C [::AI_basic BI_memory_copy]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32);
      CO_value (CV_num T_i32)] nil) ->
  e_typing s C
    [::AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) (Build_memarg N0 N0));
      AI_basic (BI_store T_i32 (Some Tp_i8) (Build_memarg N0 N0));
      $VN (VAL_int32 first); $VN (VAL_int32 second); $VN (VAL_int32 count);
      AI_basic BI_memory_copy]
    (Closed_ft [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)] nil).
Proof.
  move => LoadEntry StoreEntry CopyEntry.
  eapply closed_instruction_cons with
    (middle := [::CO_value (CV_num T_i32); CO_value (CV_num T_i32)]).
  - eapply ety_subtyping; first exact LoadEntry.
    exact (closed_instr_weakening (s_types s) _ _ [::CO_value (CV_num T_i32)]).
  - by apply closed_memory_store_continuation.
Qed.

End Bulk.
