(** Production source/closed signature agreement for the flat final function
    section. Store typing checks the identity map, and store extension preserves
    the canonical registry prefix, including across host applications. *)
From Wasm Require Import typing properties gc_type_context gc_type_context_properties
  gc_declaration_typing gc_declaration_typing_properties.
From Stdlib Require Import List NArith.
From mathcomp Require Import ssreflect ssrbool.
Import ListNotations.

Section Host.
Context `{hfc : host_function_class} `{memory : BlockUpdateMemory}.

Theorem store_typing_canonical_registry s :
  store_typing s -> canonical_registry_valid s.(s_types).
Proof.
  intros [Valid _]. now apply canonical_registry_validb_correct.
Qed.

Theorem inst_typing_function_expansion_agreement s inst C index source :
  inst_typing s inst = Some C ->
  lookup_N inst.(inst_types) index = Some source ->
  exists id signature,
    resolve_inst_type inst index = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Typed Lookup.
  pose proof (inst_typing_identities Typed) as Agreement.
  apply function_type_identitiesb_correct in Agreement.
  unfold lookup_N in Lookup.
  eapply Forall2_lookup in Agreement; [|exact Lookup].
  destruct Agreement as [id [Resolved [signature [Closed Expanded]]]].
  exists id, signature. repeat split; assumption.
Qed.

Theorem funcinst_typing_defined_type_expansion s source inst code tf :
  funcinst_typing s (FC_func_native source inst code) tf ->
  exists C id signature,
    inst_typing s inst = Some C /\
    native_func_defined_type (FC_func_native source inst code) = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros [_ [_ Typed]].
  destruct (inst_typing s inst) as [C|] eqn:Instance; [|contradiction].
  unfold func_typing in Typed. destruct code as [index locals body]. simpl in *.
  destruct (lookup_N C.(tc_types) index) as [[args results]|] eqn:Lookup;
    [|contradiction].
  destruct Typed as [Same _]. subst source.
  rewrite <- (inst_typing_type_lookup index Instance) in Lookup.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Instance Lookup)
    as [id [signature [Resolved [Closed Expanded]]]].
  exists C, id, signature. repeat split; assumption.
Qed.

Theorem store_typing_native_function_expansion s address source inst code :
  store_typing s ->
  lookup_N s.(s_funcs) address = Some (FC_func_native source inst code) ->
  exists id signature,
    lookup_func_defined_type s address = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s.(s_types) id = Some signature.
Proof.
  intros Typed Lookup.
  destruct (store_typing_func_lookup Typed Lookup) as [tf Function].
  apply funcinst_typing_defined_type_expansion in Function.
  destruct Function as [C [id [signature [_ [Resolved [Closed Expanded]]]]]].
  exists id, signature. repeat split; try assumption.
  unfold lookup_func_defined_type. now rewrite Lookup.
Qed.

Theorem store_extension_function_expansion s s' id signature :
  store_extension s s' ->
  expand_function_type s.(s_types) id = Some signature ->
  expand_function_type s'.(s_types) id = Some signature.
Proof.
  intros Extends Expanded.
  destruct (store_extension_type_groups Extends) as [suffix Registry].
  rewrite Registry.
  rewrite expand_function_type_extension; [exact Expanded |].
  unfold expand_function_type, expand_defined_type in Expanded.
  destruct (lookup_defined_type s.(s_types) id) as [st|] eqn:Lookup; [|discriminate].
  unfold lookup_defined_type in Lookup.
  destruct (nth_error s.(s_types) (N.to_nat (defined_group id))) eqn:Group;
    [now apply nth_error_index_bound in Group | discriminate].
Qed.

Theorem store_extension_native_function_identity s s' address id :
  store_extension s s' ->
  lookup_func_defined_type s address = Some id ->
  lookup_func_defined_type s' address = Some id.
Proof.
  intros Extends Resolved.
  unfold lookup_func_defined_type in *.
  destruct (lookup_N s.(s_funcs) address) as [fi|] eqn:Lookup; [|discriminate].
  rewrite (store_extension_lookup_func Extends Lookup). exact Resolved.
Qed.

Theorem store_extension_native_function_expansion s s' address source inst code :
  store_typing s ->
  store_extension s s' ->
  lookup_N s.(s_funcs) address = Some (FC_func_native source inst code) ->
  exists id signature,
    lookup_func_defined_type s' address = Some id /\
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_function_type s'.(s_types) id = Some signature.
Proof.
  intros Typed Extends Lookup.
  destruct (store_typing_native_function_expansion _ _ _ _ _ Typed Lookup)
    as [id [signature [Resolved [Closed Expanded]]]].
  exists id, signature. split.
  - now apply (store_extension_native_function_identity _ _ _ _ Extends).
  - split; [exact Closed |].
    now apply (store_extension_function_expansion _ _ _ _ Extends).
Qed.

Theorem inst_typing_equivalent_defined_types s inst1 C1 index1 source1
    inst2 C2 index2 source2 id1 id2 :
  store_typing s ->
  inst_typing s inst1 = Some C1 ->
  inst_typing s inst2 = Some C2 ->
  lookup_N inst1.(inst_types) index1 = Some source1 ->
  lookup_N inst2.(inst_types) index2 = Some source2 ->
  resolve_inst_type inst1 index1 = Some id1 ->
  resolve_inst_type inst2 index2 = Some id2 ->
  defined_type_equiv s.(s_types) id1 id2 = true ->
  exists signature,
    close_function_type inst1.(inst_defined_types) 0 source1 = Some signature /\
    close_function_type inst2.(inst_defined_types) 0 source2 = Some signature.
Proof.
  intros Store Typed1 Typed2 Lookup1 Lookup2 Resolved1 Resolved2 Equivalent.
  pose proof (store_typing_canonical_registry _ Store) as [_ [WF _]].
  apply (proj1 (defined_type_equiv_eq _ _ _ WF)) in Equivalent. subst id2.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Typed1 Lookup1)
    as [a [sig1 [Id1 [Closed1 Expanded1]]]].
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Typed2 Lookup2)
    as [b [sig2 [Id2 [Closed2 Expanded2]]]].
  rewrite Resolved1 in Id1. injection Id1 as Id1. subst a.
  rewrite Resolved2 in Id2. injection Id2 as Id2. subst b.
  rewrite Expanded1 in Expanded2. injection Expanded2 as Same. subst sig2.
  exists sig1. auto.
Qed.

Theorem store_extension_instantiated_function_agreement s s' inst C index source id :
  store_extension s s' ->
  inst_typing s inst = Some C ->
  lookup_N inst.(inst_types) index = Some source ->
  resolve_inst_type inst index = Some id ->
  exists signature,
    close_function_type inst.(inst_defined_types) 0 source = Some signature /\
    expand_inst_function_type s' inst index = Some signature.
Proof.
  intros Extension Typed Lookup Resolved.
  destruct (inst_typing_function_expansion_agreement _ _ _ _ _ Typed Lookup)
    as [actual [signature [Id [Closed Expanded]]]].
  rewrite Resolved in Id. injection Id as Same. subst actual.
  exists signature. split; [exact Closed |].
  unfold expand_inst_function_type. rewrite Resolved.
  now apply (store_extension_function_expansion _ _ _ _ Extension).
Qed.

End Host.
