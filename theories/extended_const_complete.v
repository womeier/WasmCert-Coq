(** Total evaluation of validated constant expressions and initializer chains.
    Runtime operands are related to the actual validator's reversed type stack.
    A separate typing store permits references to functions allocated later in
    module instantiation; no circular assumption that the output store is typed
    is needed. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Stdlib Require Import NArith List Arith.PeanoNat.
From Wasm Require Import instantiation_func extended_const
  instantiation_properties type_checker_reflects_typing interp_instantiate_sound module_validation_complete.
From Wasm Require Import gc_declaration_typing.
From Wasm Require Import gc_declaration_typing_properties gc_type_transport.
From Wasm Require Import closed_initializer_properties closed_instantiation_properties
  canonical_import_properties gc_closed_runtime_properties gc_type_context gc_runtime_type_properties.

Set SsrOldRewriteGoalsOrder.

Section Host.
Context `{ho : host}.

Definition const_environment_typed (typing_store runtime_store : store_record)
    (f : frame) (C : t_context) : Prop :=
  (forall i, (N.to_nat i < length C.(tc_funcs))%coq_nat ->
    exists addr, lookup_N f.(f_inst).(inst_funcs) i = Some addr /\
       value_typing typing_store f.(f_inst).(inst_defined_types)
         (VAL_ref (VAL_ref_func addr)) (T_ref T_funcref)) /\
  (forall i gt, lookup_N C.(tc_globals) i = Some gt ->
    exists v, sglob_val runtime_store f.(f_inst) i = Some v /\
       value_typing typing_store f.(f_inst).(inst_defined_types) v gt.(tg_t)) /\
   length f.(f_inst).(inst_globals) = length C.(tc_globals) /\
   canonical_registry_valid typing_store.(s_types) /\
   runtime_store.(s_types) = typing_store.(s_types) /\
   runtime_store.(s_funcs) = typing_store.(s_funcs) /\
   length C.(tc_types) = length f.(f_inst).(inst_defined_types) /\
   List.Forall (fun id => exists declaration,
     expand_defined_type typing_store.(s_types) id = Some declaration)
     f.(f_inst).(inst_defined_types).

Lemma const_value_num_inv s names v t :
   value_typing s names v (T_num t) ->
  exists vn, v = VAL_num vn /\ typeof_num vn = t.
Proof.
  destruct v as [vn|vv|vr].
  - exists vn; split => //.
    by destruct vn, t.
  - by destruct vv, t.
   - unfold value_typing, closed_value_typing, typeof_closed_value.
     destruct (typeof_closed_ref s vr); simpl; by rewrite ?andbF.
Qed.

Lemma const_checker_step_complete typing_store runtime_store f C e ts vs ct' :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_expr C e ->
   List.Forall2 (fun v t =>
     value_typing typing_store f.(f_inst).(inst_defined_types) v t) vs ts ->
  type_checker.check_single C (Some (type_checker.Build_checker_type ts false)) e = Some ct' ->
  exists ts' vs',
    ct' = type_checker.Build_checker_type ts' false /\
    interp_const_step runtime_store f e vs = Some vs' /\
     List.Forall2 (fun v t =>
       value_typing typing_store f.(f_inst).(inst_defined_types) v t) vs' ts'.
Proof.
   move => [Hfunc [Hglob [Hlength [Registry [Types [Functions [Scope Registered]]]]]]]
     Hconst Hstack Hcheck.
  destruct e; cbn [extended_const_expr const_expr] in Hconst => //.
  - (* numeric constant *)
    cbn [type_checker.check_single type_checker.type_update type_checker.consume
      type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    do 2 eexists; split; first reflexivity.
    split; first reflexivity.
    constructor => //.
    by apply value_num_principal_typing.
  - (* integer arithmetic *)
    cbn [type_checker.check_single] in Hcheck.
    destruct (binop_type_agree n b) eqn:Hagree => //.
    unfold type_checker.type_update in Hcheck.
    destruct ts as [|t2 ts].
    { by cbn [type_checker.type_update type_checker.consume type_checker.CT_type type_checker.CT_unr] in Hcheck. }
    cbn [type_checker.type_update type_checker.consume type_checker.CT_type type_checker.CT_unr] in Hcheck.
    destruct (t2 <t: T_num n) eqn:Hsub2 => //.
    destruct ts as [|t1 ts].
    { by cbn [type_checker.consume type_checker.CT_type type_checker.CT_unr] in Hcheck. }
    cbn [type_checker.consume type_checker.CT_type type_checker.CT_unr] in Hcheck.
    destruct (t1 <t: T_num n) eqn:Hsub1 => //.
    cbn [type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    inversion Hstack as [|v2 ? ? ? Hv2 Htail]; subst.
    inversion Htail as [|v1 ? ? ? Hv1 Hrest]; subst.
    specialize (value_typing_trans Hv2 Hsub2) as Hv2n.
    specialize (value_typing_trans Hv1 Hsub1) as Hv1n.
     specialize (const_value_num_inv _ _ _ _ Hv2n) as [v2n [-> Ht2]].
     specialize (const_value_num_inv _ _ _ _ Hv1n) as [v1n [-> Ht1]].
    assert (binop_typecheck v1n v2n n b) as Htc.
    { by rewrite /binop_typecheck Ht1 Ht2 Hagree !eq_refl. }
    specialize (const_binop_total _ _ _ _ Hconst Htc) as [v [Happ Htv]].
    do 2 eexists; split; first reflexivity.
    split.
    + by cbn [interp_const_step]; rewrite Hconst Htc Happ.
    + constructor => //.
       rewrite -Htv. apply value_num_principal_typing.
  - (* vector constant *)
    cbn [type_checker.check_single type_checker.type_update type_checker.consume
      type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    do 2 eexists; split; first reflexivity.
    split; first reflexivity.
    constructor => //.
  - (* ref.null *)
    cbn [type_checker.check_single] in Hcheck.
    destruct (source_heap_scopedb (tc_types C) h) eqn:Scoped => //.
    cbn [type_checker.check_single type_checker.type_update type_checker.consume
      type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    have RuntimeRegistered : List.Forall (fun id => exists declaration,
        expand_defined_type (s_types runtime_store) id = Some declaration)
        (inst_defined_types (f_inst f)) by rewrite Types.
    destruct (registered_source_null_total (s := runtime_store)
      (inst := f_inst f) Scope RuntimeRegistered Scoped) as [ref Lower].
    do 2 eexists; split; first reflexivity.
    split; first by rewrite /interp_const_step Lower.
    constructor => //.
    apply lower_source_null_typed.
    unfold lower_source_null in Lower |- *. by rewrite Types in Lower.
  - (* ref.func *)
    cbn [type_checker.check_single] in Hcheck.
     destruct (lookup_N (tc_funcs C) f0) as [ft|] eqn:Hlookup => //.
    destruct (f0 \in tc_refs C) => //.
    cbn [type_checker.type_update type_checker.consume type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    assert ((N.to_nat f0 < length (tc_funcs C))%coq_nat) as Hbound.
    { by apply nth_error_Some_length in Hlookup. }
    specialize (Hfunc _ Hbound) as [addr [Haddr Htyped]].
    do 2 eexists; split; first reflexivity.
    split.
    + by cbn [interp_const_step]; rewrite Haddr.
    + by constructor.
  - (* global.get *)
    cbn [type_checker.check_single] in Hcheck.
    destruct (lookup_N (tc_globals C) g) as [gt|] eqn:Hlookup => //.
    cbn [type_checker.type_update type_checker.consume type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    specialize (Hglob _ _ Hlookup) as [v [Hget Htyped]].
    do 2 eexists; split; first reflexivity.
    split.
     + by cbn [interp_const_step]; rewrite Hget.
     + by constructor.
  - (* ref.i31 *)
    cbn [type_checker.check_single] in Hcheck.
    unfold type_checker.type_update in Hcheck.
    destruct ts as [|t ts].
    { by cbn [type_checker.consume type_checker.CT_type type_checker.CT_unr] in Hcheck. }
    cbn [type_checker.consume type_checker.CT_type type_checker.CT_unr] in Hcheck.
    destruct (t <t: T_num T_i32) eqn:Hsub => //.
    cbn [type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    inversion Hstack as [|v ? ? ? Hv Htail]; subst.
    specialize (value_typing_trans Hv Hsub) as Hnumeric.
     destruct (const_value_num_inv _ _ _ _ Hnumeric) as [number [-> Hnumber]].
    destruct number => //.
    do 2 eexists; split; first reflexivity.
    split; first reflexivity.
    constructor => //.
Qed.

Lemma const_checker_fold_complete typing_store runtime_store f C es ts vs ct' :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_exprs C es ->
   List.Forall2 (fun v t =>
     value_typing typing_store f.(f_inst).(inst_defined_types) v t) vs ts ->
  type_checker.check C es (Some (type_checker.Build_checker_type ts false)) = Some ct' ->
  exists ts' vs',
    ct' = type_checker.Build_checker_type ts' false /\
    interp_const_stack runtime_store f es vs = Some vs' /\
     List.Forall2 (fun v t =>
       value_typing typing_store f.(f_inst).(inst_defined_types) v t) vs' ts'.
Proof.
  move => Henv.
  move: ts vs ct'.
  induction es as [|e es IH]; move => ts vs ct' Hconst Hstack Hcheck.
  - injection Hcheck as <-.
    exists ts, vs; by repeat split.
  - move/andP: Hconst => [He Hes].
    change (type_checker.check C es
      (type_checker.check_single C (Some (type_checker.Build_checker_type ts false)) e)
      = Some ct') in Hcheck.
    destruct (type_checker.check_single C
      (Some (type_checker.Build_checker_type ts false)) e) as [ct1|] eqn:Hsingle.
    2: by rewrite check_None in Hcheck.
    specialize (const_checker_step_complete _ _ _ _ _ _ _ _ Henv He Hstack Hsingle)
      as [ts1 [vs1 [-> [Hstep Hstack1]]]].
    specialize (IH _ _ _ Hes Hstack1 Hcheck) as [ts' [vs' [Hct [Heval Hstack']]]].
    exists ts', vs'; repeat split => //.
    by cbn [interp_const_stack]; rewrite Hstep.
Qed.

Lemma const_environment_reverse typing_store runtime_store f C :
  const_environment_typed typing_store runtime_store f C ->
  const_environment_typed typing_store runtime_store f (type_checker.context_reverse C).
Proof.
   move => [Hfunc [Hglob [Hlen [Registry [Types [Functions [Scope Registered]]]]]]].
   split.
   - move => i Hbound. apply Hfunc.
     by rewrite /= List.length_map in Hbound.
   - repeat split => //.
     by rewrite /= List.length_map.
Qed.

Lemma const_exprs_reverse C es :
  extended_const_exprs (type_checker.context_reverse C) es = extended_const_exprs C es.
Proof.
  apply eq_all => e.
  by destruct e.
Qed.

Theorem interp_get_const_validated typing_store runtime_store f C es t :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_exprs C es ->
  type_checker.b_e_type_checker C es (Tf nil [::t]) ->
  exists v, interp_get_const runtime_store f es = Some v /\
     value_typing typing_store f.(f_inst).(inst_defined_types) v t.
Proof.
  move => Henv Hconst Hcheck.
  apply const_environment_reverse in Henv.
  rewrite <- const_exprs_reverse in Hconst.
  unfold type_checker.b_e_type_checker, type_checker.b_e_type_checker_aux in Hcheck.
  change (is_true (match type_checker.check (type_checker.context_reverse C) es
    (Some (type_checker.Build_checker_type nil false)) with
    | Some ct => type_checker.c_types_agree ct [::t]
    | None => false end)) in Hcheck.
  destruct (type_checker.check _ es _) as [ct|] eqn:Hchecked => //.
  specialize (const_checker_fold_complete _ _ _ _ _ _ nil _ Henv Hconst
    (List.Forall2_nil _) Hchecked) as [ts [vs [-> [Heval Htyped]]]].
  cbn [type_checker.c_types_agree type_checker.CT_unr type_checker.CT_type] in Hcheck.
  specialize (values_subtyping_size Hcheck) as Hsize.
  destruct ts as [|t0 [|t1 ts]] => //.
  inversion Htyped as [|v rest ? ? Hv Hrest]; subst.
  inversion Hrest; subst.
  exists v; split.
  - by rewrite interp_get_const_stack Heval.
  - eapply value_typing_trans; eauto.
    by move/andP: Hcheck => [Hsub _].
Qed.

Corollary interp_get_const_complete typing_store runtime_store f C es t :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_exprs C es ->
  be_typing C es (Tf nil [::t]) ->
  exists v, interp_get_const runtime_store f es = Some v /\
     value_typing typing_store f.(f_inst).(inst_defined_types) v t.
Proof.
  move => Henv Hconst /b_e_type_checker_reflects_typing Hcheck.
  by eapply interp_get_const_validated; eauto.
Qed.

Lemma sglob_val_added s f source g v :
  sglob_val (add_glob s (gen_global_instance g v))
    (const_frame_add_global f (N.of_nat (length s.(s_globals))) source).(f_inst)
    (N.of_nat (length f.(f_inst).(inst_globals))) = Some v.
Proof.
  unfold sglob_val, sglob, sglob_ind, lookup_N.
  cbn [const_frame_add_global add_glob].
  rewrite Nnat.Nat2N.id List.nth_error_app2; last reflexivity.
  rewrite Nat.sub_diag /= Nnat.Nat2N.id List.nth_error_app2; last reflexivity.
  by rewrite Nat.sub_diag.
Qed.

Lemma const_environment_add_global typing_store runtime_store f C g closed v :
  const_environment_typed typing_store runtime_store f C ->
  value_typing typing_store f.(f_inst).(inst_defined_types) v g.(modglob_type).(tg_t) ->
  const_environment_typed typing_store
    (add_glob runtime_store (gen_global_instance closed v))
    (const_frame_add_global f (N.of_nat (length runtime_store.(s_globals))) g.(modglob_type))
    (const_context_add_global C g.(modglob_type)).
Proof.
  move => [Hfunc [Hglob [Hlen [Registry [Types [Functions [Scope Registered]]]]]]] Hvalue.
  split; first exact Hfunc.
  split.
  - move => i gt Hlookup.
    change (lookup_N (C.(tc_globals) ++ [::g.(modglob_type)]) i = Some gt) in Hlookup.
    unfold lookup_N in Hlookup.
    destruct (Nat.lt_ge_cases (N.to_nat i) (length C.(tc_globals))) as [Hlt|Hge].
    + rewrite List.nth_error_app1 in Hlookup; last exact Hlt.
      specialize (Hglob _ _ Hlookup) as [w [Hget Htype]].
      exists w; split => //.
      by apply const_global_extension.
    + rewrite List.nth_error_app2 in Hlookup; last exact Hge.
      destruct (N.to_nat i - length C.(tc_globals))%coq_nat as [|j] eqn:Hi.
      2: { by cbn in Hlookup; rewrite List.nth_error_nil in Hlookup. }
      injection Hlookup as <-.
      exists v; split => //.
      assert (i = N.of_nat (length f.(f_inst).(inst_globals))) as Hidx.
      { apply Nnat.N2Nat.inj.
        rewrite Nnat.Nat2N.id Hlen.
        by lias.
      }
      by rewrite Hidx; apply sglob_val_added.
  - split.
    + change (length (f.(f_inst).(inst_globals) ++ [::N.of_nat (length runtime_store.(s_globals))]) =
      length (C.(tc_globals) ++ [::g.(modglob_type)])).
      by rewrite !List.length_app /= Hlen.
    + split; first exact Registry.
      split; first exact Types.
      split; first exact Functions.
      split; [exact Scope|exact Registered].
Qed.

Theorem interp_global_chain_complete typing_store runtime_store f C gs :
  const_environment_typed typing_store runtime_store f C ->
  extended_globals_typing C gs ->
  exists s' f' vs,
    interp_global_chain runtime_store f gs = Some (s', f', vs) /\
    List.Forall2 (fun g v => value_typing typing_store
      f.(f_inst).(inst_defined_types) v g.(modglob_type).(tg_t)) gs vs /\
    const_environment_typed typing_store s' f'
      (const_context_add_globals C (seq.map modglob_type gs)).
Proof.
  move: runtime_store f C.
  induction gs as [|g gs IH]; move => runtime_store f C Henv Hvalid.
  - exists runtime_store, f, nil; split; first reflexivity.
    split; first constructor.
    by destruct C; rewrite /const_context_add_globals /= cats0.
  - destruct Hvalid as [[Hconst Htype] Htail].
    specialize (interp_get_const_complete _ _ _ _ _ _ Henv Hconst Htype)
      as [v [Heval Hvalue]].
    have Closing : exists closed,
        close_global_type (inst_defined_types (f_inst f)) (modglob_type g) = Some closed /\
        closed_value_typing typing_store v (tg_t closed).
    { unfold value_typing in Hvalue.
      unfold close_global_type.
      destruct (close_value_type (inst_defined_types (f_inst f)) N0 (tg_t (modglob_type g)))
        as [value_type|] eqn:Value; last discriminate.
      eexists. split; [reflexivity|exact Hvalue]. }
    destruct Closing as [closed [Closed Accepted]].
    have RuntimeAccepted : closed_value_typing runtime_store v (tg_t closed).
    { destruct Henv as [Fun [Global [Len [Reg [Types [Functions Tail]]]]]].
      rewrite (closed_value_typing_world v (tg_t closed) Types Functions).
      exact Accepted. }
    specialize (const_environment_add_global _ _ _ _ _ closed _ Henv Hvalue) as Henv1.
    specialize (IH _ _ _ Henv1 Htail) as [s' [f' [vs [Hchain [Hvalues Henv']]]]].
    exists s', f', (v :: vs).
    split.
    + cbn [interp_global_chain]; rewrite Heval Closed RuntimeAccepted.
      by cbn [alloc_glob]; rewrite Hchain.
    + split; first by constructor.
      replace (const_context_add_globals C (seq.map modglob_type (g :: gs)))
        with (const_context_add_globals (const_context_add_global C g.(modglob_type))
          (seq.map modglob_type gs)); first exact Henv'.
      by destruct C; rewrite /const_context_add_globals /const_context_add_global /= -catA.
Qed.

Lemma const_value_functions_extension s s' names added v t :
  store_extension s s' ->
  s'.(s_funcs) = s.(s_funcs) ++ added ->
  value_typing s names v t ->
  value_typing s' names v t.
Proof.
  move => Extension Functions Typed.
  by eapply value_typing_extension; eauto.
Qed.

Lemma const_initial_environment old preview f C v_imps actual expected added :
  store_typing old ->
  store_extension old preview ->
  canonical_registry_valid preview.(s_types) ->
  registered_function_references preview ->
  List.Forall2 (external_typing old) v_imps actual ->
  List.Forall2 (closed_import_subtyping preview.(s_types)) actual expected ->
  preview.(s_funcs) = old.(s_funcs) ++ added ->
  preview.(s_globals) = old.(s_globals) ->
  f.(f_inst).(inst_funcs) = ext_funcs v_imps ++
    iota_N (length old.(s_funcs)) (length added) ->
  f.(f_inst).(inst_globals) = ext_globals v_imps ->
  length f.(f_inst).(inst_funcs) = length C.(tc_funcs) ->
  those (map (close_global_type f.(f_inst).(inst_defined_types)) C.(tc_globals)) =
    Some (closed_ext_t_globals expected) ->
  length C.(tc_types) = length f.(f_inst).(inst_defined_types) ->
  List.Forall (fun id => exists declaration,
    expand_defined_type preview.(s_types) id = Some declaration)
      f.(f_inst).(inst_defined_types) ->
  const_environment_typed preview preview f C.
Proof.
  move => HST Extension Registry Registered Himps Hsub Hstore Hglobals Hfunc Hglob
    Hnfunc ClosedGlobals Scope Expansions.
  specialize (vt_imps_comp_len Himps) as [Hflen [_ [_ Hglen]]].
  specialize (closed_import_component_lengths Hsub) as [_ [_ [_ Hglen']]].
  split.
  - move => i Hbound.
    assert ((N.to_nat i < length f.(f_inst).(inst_funcs))%coq_nat) as Hlen.
    { by rewrite Hnfunc. }
    destruct (lookup_N f.(f_inst).(inst_funcs) i) as [addr|] eqn:Haddr.
    2: { apply List.nth_error_None in Haddr; by lias. }
    exists addr; split => //.
    assert ((N.to_nat addr < length preview.(s_funcs))%coq_nat) as Haddrbound.
    { rewrite Hfunc in Haddr.
      unfold lookup_N in Haddr.
      apply cat_lookup in Haddr as [Himport | Hdefined].
      - apply ext_funcs_lookup_exist in Himport as [n Hnth].
        specialize (Forall2_lookup Himps Hnth) as [et [Hntht Htype]].
        unfold external_typing, ext_typing, lookup_func_defined_type in Htype.
        destruct (lookup_N (s_funcs old) addr) as [cl|] eqn:Hcl => //.
        apply nth_error_Some_length in Hcl.
        rewrite Hstore List.length_app; by lias.
      - apply iota_N_lookup_Some in Hdefined as [-> Hrange].
        rewrite Nnat.Nat2N.id Hstore List.length_app; by lias.
    }
    destruct (lookup_N (s_funcs preview) addr) as [cl|] eqn:Hcl.
    + exact (Registered addr cl Hcl).
    + apply List.nth_error_None in Hcl; by lias.
  - split.
    + move => i gt Hlookup.
      destruct (those_map_lookup ClosedGlobals Hlookup) as [expected_global [Closed Slot]].
      specialize (closed_import_globals_lookup Hsub Slot)
        as [gt' [Hnthsub Hsubgt]].
      specialize (vt_imps_globals_typing Himps Hnthsub) as [addr [Haddr Htext]].
      change (lookup_N (ext_globals v_imps) i = Some addr) in Haddr.
      unfold external_typing, ext_typing, ext_global_typing in Htext.
      destruct (lookup_N (s_globals old) addr) as [gi|] eqn:Hgi => //.
      injection Htext as <-.
      exists gi.(g_val); split.
      * by unfold sglob_val, sglob, sglob_ind; rewrite Hglob Haddr Hglobals Hgi.
      * have Get : sglob_val preview (f_inst f) i = Some (g_val gi)
          by unfold sglob_val, sglob, sglob_ind; rewrite Hglob Haddr Hglobals Hgi.
        have Value : closed_value_typing preview (g_val gi) (tg_t expected_global).
        { eapply imported_global_value_typing with (s := old)
            (v_imps := v_imps) (t_imps := actual) (t_imps_mod := expected)
            (added_globals := nil) (added_addrs := nil); try eassumption.
          - by rewrite cats0.
          - by rewrite cats0. }
        destruct (close_global_type_agreement _ _ _ Closed) as [_ ValueClosed].
        unfold value_typing. by rewrite ValueClosed.
    + split.
      * have Length := those_length ClosedGlobals.
        rewrite List.length_map in Length.
        by rewrite Hglob Hglen Hglen' Length.
      * split; first exact Registry.
        split; first reflexivity.
        split; first reflexivity.
        split; [exact Scope|exact Expansions].
Qed.

Lemma interp_get_vref_complete typing_store runtime_store f C es rt :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_exprs C es ->
  type_checker.b_e_type_checker C es (Tf nil [::T_ref rt]) ->
  exists r, interp_get_vref runtime_store f es = Some r.
Proof.
  move => Henv Hconst Hcheck.
  specialize (interp_get_const_validated _ _ _ _ _ _ Henv Hconst Hcheck)
    as [v [Heval Htype]].
  destruct v as [vn|vv|vr].
  - by apply value_num_expected in Htype.
  - by apply value_vec_expected in Htype.
  - exists vr.
    by unfold interp_get_vref; rewrite Heval.
Qed.

Lemma get_elem_inits_complete typing_store runtime_store f C elems :
  const_environment_typed typing_store runtime_store f C ->
  all (module_elem_type_checker C) elems ->
  exists refs, get_elem_inits runtime_store f elems = Some refs.
Proof.
  move => Henv.
  induction elems as [|elem elems IH] => //=.
  { by exists nil. }
  move/andP => [Hcheck Hchecks].
  specialize (IH Hchecks) as [refs Hrefs].
  destruct elem as [rt inits mode].
  move/andP: Hcheck => [/andP [Hconst Htype] Hmode].
  assert (exists rs, those (map (interp_get_vref runtime_store f) inits) = Some rs) as [rs Hrs].
  { clear Hrefs Hmode Hchecks refs elems.
    induction inits as [|es inits IH] => //=.
    { by exists nil. }
    move/andP: Hconst => [Hconst Hconsts].
    move/andP: Htype => [Htype Htypes].
    specialize (IH Hconsts Htypes) as [rs Hrs].
    specialize (interp_get_vref_complete _ _ _ _ _ _ Henv Hconst Htype) as [r Hr].
    exists (r :: rs).
    by rewrite Hr -those_those0 /= those_those0 Hrs.
  }
  exists (rs :: refs).
  unfold get_elem_inits in Hrefs |- *.
  cbn [seq.map modelem_init].
  by rewrite Hrs -those_those0 /= those_those0 Hrefs.
Qed.

Theorem module_initializers_complete s m v_imps t_imps t_imps_mod t_exps message
    registry typeids source expected allocated addresses :
  store_typing s ->
  module_type_checker m = (Some (t_imps_mod, t_exps), message) ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  close_and_validate_type_groups (s_types s) (module_type_groups m) =
    Some (registry, typeids) ->
  source_type_identitiesb registry typeids (List.concat (mod_types m)) typeids ->
  module_source_context m = Some source ->
  those (map (close_import_desc registry typeids) (map imp_desc (mod_imports m))) =
    Some expected ->
  List.Forall2 (closed_import_subtyping registry) t_imps expected ->
  alloc_funcs s (mod_funcs m) (module_runtime_instance s m v_imps typeids source) =
    (allocated, addresses) ->
  exists s_init f_init g_inits r_inits,
    interp_global_chain (upd_s_types allocated registry)
      (module_init_frame s m v_imps typeids source) m.(mod_globals) =
      Some (s_init, f_init, g_inits) /\
    get_elem_inits s_init f_init m.(mod_elems) = Some r_inits /\
    List.Forall2 (fun g v => value_typing (upd_s_types allocated registry) typeids
      v (tg_t (modglob_type g))) (mod_globals m) g_inits.
Proof.
  move => HST Hcheck Himps Hclosed Hidentity Hsource Hexpected Hsub Hallocated.
  destruct (function_preview_properties HST Hclosed Hidentity Hsource Hallocated)
    as [Extension [Registry Registered]].
  have Allocation := alloc_func_iota_N Hallocated.
  specialize (module_type_checker_sound _ _ _ _ Hcheck) as Hvalid.
  destruct m.
  cbn [datatypes.mod_types datatypes.mod_imports datatypes.mod_funcs] in
    Hidentity, Hexpected, Hallocated, Allocation.
  destruct Hvalid as [Hdecl Hvalid].
  unfold module_components_typing in Hvalid.
  destruct Hvalid as [fts [tts [mts [gts [rts [dts
    [Hmtypes [Hmfuncs [Hmtabs [Hmmems [Hmemcount [[Hgts Hglobals]
    [Hmelems [Hmdatas [Hstart [Hmimports [Hmexports Hnames]]]]]]]]]]]]]]]]].
  match type of Hglobals with extended_globals_typing ?C0 _ => pose Cinit := C0 end.
  change (extended_globals_typing Cinit mod_globals) in Hglobals.
  pose added := (map (fun mf => gen_func_instance mf
    (module_runtime_instance s (Build_module mod_types mod_funcs mod_tables mod_mems
      mod_globals mod_elems mod_datas mod_start mod_imports mod_exports)
      v_imps typeids source)) mod_funcs : list (@funcinst hfc)).
  pose preview := upd_s_types allocated registry.
  assert (const_environment_typed preview preview
    (module_init_frame s (Build_module mod_types mod_funcs mod_tables mod_mems
      mod_globals mod_elems mod_datas mod_start mod_imports mod_exports) v_imps typeids source)
    Cinit) as Henv.
  { eapply const_initial_environment with (old := s) (actual := t_imps)
      (expected := expected) (added := added); try eassumption.
    - destruct Allocation as [_ [Functions _]]. exact Functions.
    - destruct Allocation as [_ [_ [_ [_ [Globals _]]]]]. symmetry. exact Globals.
    - change (ext_funcs v_imps ++ iota_N (length (s_funcs s)) (length mod_funcs) =
        ext_funcs v_imps ++ iota_N (length (s_funcs s)) (length added)).
      by rewrite /added List.length_map.
    - reflexivity.
    - change (length (ext_funcs v_imps ++ iota_N (length (s_funcs s)) (length mod_funcs)) =
        length (ext_t_funcs t_imps_mod ++ fts)).
      have Count := closed_import_function_count Hmimports Hexpected.
      destruct (closed_import_component_lengths Hsub) as [MatchLength _].
      destruct (vt_imps_comp_len Himps) as [ImportLength _].
      rewrite !List.length_app iota_N_length.
      have FunctionsLength := List.Forall2_length Hmfuncs. by lias.
    - exact (closed_import_global_projection Hmimports Hexpected).
    - have Identity := Hidentity. apply source_type_identitiesb_correct in Identity.
      exact (List.Forall2_length Identity).
    - exact (registered_type_expansions Hidentity).
  }
  specialize (interp_global_chain_complete _ _ _ _ _ Henv Hglobals)
    as [s_init [f_init [g_inits [Hchain [Htyped Henv_final]]]]].
  assert (all (module_elem_type_checker
    (const_context_add_globals Cinit (seq.map modglob_type mod_globals))) mod_elems) as Helems.
  { rewrite <-Hgts.
    eapply module_components_all; last exact Hmelems.
    move => el rt.
    apply module_elem_type_checker_complete.
  }
  specialize (get_elem_inits_complete _ _ _ _ _ Henv_final Helems) as [r_inits Helems_init].
  exists s_init, f_init, g_inits, r_inits. by repeat split.
Qed.

Theorem interp_instantiate_complete hs s m v_imps t_imps t_imps_mod t_exps message :
  store_typing s ->
  module_type_checker m = (Some (t_imps_mod, t_exps), message) ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  canonical_module_imports s m t_imps ->
  exists s' f es,
    interp_instantiate hs s m v_imps =
      (Some (hs, s', f, es), String.EmptyString).
Proof.
  move => HST Hcheck Himps Hsub.
  pose proof (module_type_checker_sound _ _ _ _ Hcheck) as Hvalid.
  destruct Hvalid as [[old_registry [old_names [Hclosed [Hconsistent Hruntime]]]] Hcomponents].
  assert (Hregistry : canonical_registry_valid s.(s_types)).
  { apply canonical_registry_validb_correct. exact (proj1 HST). }
  destruct Hsub as [registry [typeids [expected [Hcanonical [Hexpected Matching]]]]].
  destruct (validated_closing_portable _ _ _ _ Hregistry Hclosed Hconsistent)
    as [portable_registry [portable_names [Hportable Hidentities]]].
  rewrite Hcanonical in Hportable. injection Hportable as <- <-.
  have Registry := proj1 (close_and_validate_type_groups_sound _ _ _ _ Hcanonical).
  have Hmatch : List.Forall2 (closed_import_subtyping registry) t_imps expected.
  { eapply Forall2_impl; last exact Matching.
    move => actual expected_type Match.
    exact (proj2 (canonical_extern_matching_correct _ _ Registry) Match). }
  have Runtime := Hruntime.
  unfold module_runtime_types_closedb in Runtime.
  destruct (module_source_context m) as [source|] eqn:Hsource; last discriminate.
  have OldIdentity := Hconsistent.
  apply source_type_identitiesb_correct in OldIdentity.
  have NewIdentity := Hidentities.
  apply source_type_identitiesb_correct in NewIdentity.
  have OldLength := List.Forall2_length OldIdentity.
  have NewLength := List.Forall2_length NewIdentity.
  have NamesLength : length old_names = length typeids.
  { rewrite -OldLength. exact NewLength. }
  have ValidTables : List.Forall tabletype_valid (map modtab_type (mod_tables m)).
  { destruct m. unfold module_components_typing in Hcomponents.
    destruct Hcomponents as [fts [tts [mts [gts [rts [dts
      [Types [Functions [Tables Rest]]]]]]]]].
    change (List.Forall tabletype_valid (map modtab_type mod_tables)).
    apply Forall_spec. move => n table Table.
    rewrite nth_error_map' in Table.
    destruct (List.nth_error mod_tables n) as [entry|] eqn:Entry; last discriminate.
    injection Table as <-.
    destruct (Forall2_lookup Tables Entry) as [declared [_ Typed]].
    by move/andP: Typed => [Valid _]. }
  destruct (module_storage_closings_portable Hruntime NamesLength
      (registered_type_names Hidentities) (registered_type_expansions Hidentities)
      ValidTables)
    as [tables [globals [elements [TablesClosed [GlobalsClosed ElementsClosed]]]]].
  destruct (alloc_funcs s (mod_funcs m) (module_runtime_instance s m v_imps typeids source))
    as [allocated addresses] eqn:Hallocated.
  destruct (module_initializers_complete s m v_imps t_imps t_imps_mod t_exps message
      registry typeids source expected allocated addresses HST Hcheck Himps Hcanonical
      Hidentities Hsource Hexpected Hmatch Hallocated)
    as [s_init [f_init [g_inits [r_inits [Hglobals [Helems GlobalValues]]]]]].
  assert (those (seq.map (external_type_checker s) v_imps) = Some t_imps) as Himports.
  { apply those_spec.
    - rewrite List.length_map.
      by apply List.Forall2_length in Himps.
    - move => n t Hnth.
      rewrite nth_error_map'.
      specialize (Forall2_nth_impl' Himps Hnth) as [v [Hnthv Htype]].
      rewrite Hnthv /=.
      by rewrite /external_type_checker Htype.
  }
  have Hmatchb : all2 (closed_import_subtyping registry) t_imps expected
    by apply Forall2_all2.
  have GlobalCount := interp_global_chain_length _ _ _ _ _ _ Hglobals.
  have ElementCount := those_length Helems.
  rewrite List.length_map in ElementCount.
  have ClosedGlobalCount := those_length GlobalsClosed.
  have ClosedElementCount := those_length ElementsClosed.
  rewrite !List.length_map in ClosedGlobalCount.
  rewrite !List.length_map in ClosedElementCount.
  have GLength : length g_inits = length globals by lias.
  have ELength : length r_inits = length elements by lias.
  have Allocated : exists s' inst,
      interp_alloc_module s m v_imps g_inits r_inits registry typeids = Some (s', inst).
  { unfold interp_alloc_module.
    rewrite Hsource TablesClosed GlobalsClosed ElementsClosed GLength ELength !eq_refl /=.
    rewrite Hallocated.
    destruct (alloc_tabs allocated tables) as [s2 table_addresses].
    destruct (alloc_mems s2 (seq.map modmem_type (mod_mems m))) as [s3 memory_addresses].
    destruct (alloc_globs s3 globals g_inits) as [s4 global_addresses].
    destruct (alloc_elems s4 elements r_inits) as [s5 element_addresses].
    destruct (alloc_datas s5 (mod_datas m)) as [s6 data_addresses].
    by do 2 eexists. }
  destruct Allocated as [s' [inst Allocated]].
  unfold interp_instantiate.
  rewrite Hcheck Hcanonical Hidentities Himports Hexpected Hsource Hmatchb Hallocated
    Hglobals Helems Allocated.
  by do 3 eexists.
Qed.

(* The historical equality-interface profile remains sufficient when source
   closure is CHECKED to give the same canonical descriptors as the imports.
   Raw source-signature equality alone is deliberately not a premise here. *)
Corollary interp_instantiate_closed_identity_profile_complete
    hs s m v_imps actual expected exports message :
  store_typing s ->
  module_type_checker m = (Some (expected, exports), message) ->
  List.Forall2 (external_typing s) v_imps actual ->
  (exists registry names,
    close_and_validate_type_groups (s_types s) (module_type_groups m) =
      Some (registry, names) /\
    those (map (close_import_desc registry names) (map imp_desc (mod_imports m))) =
      Some actual) ->
  exists s' f code, interp_instantiate hs s m v_imps =
    (Some (hs, s', f, code), String.EmptyString).
Proof.
  move => Store Check Imports [registry [names [Closed Expected]]].
  eapply interp_instantiate_complete; try eassumption.
  have Valid := module_type_checker_sound _ _ _ _ Check.
  destruct Valid as [[source_registry [source_names [Source [Consistent Runtime]]]] _].
  have BaseValid : canonical_registry_valid (s_types s).
  { apply canonical_registry_validb_correct. exact (proj1 Store). }
  destruct (validated_closing_portable _ _ _ _ BaseValid Source Consistent)
    as [portable [portable_names [Portable Identities]]].
  rewrite Closed in Portable. injection Portable as <- <-.
  exact (checked_identity_imports Closed Identities Expected).
Qed.

End Host.
