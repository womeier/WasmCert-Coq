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

Set SsrOldRewriteGoalsOrder.

Section Host.
Context `{ho : host}.

Definition const_environment_typed (typing_store runtime_store : store_record)
    (f : frame) (C : t_context) : Prop :=
  (forall i, (N.to_nat i < length C.(tc_funcs))%coq_nat ->
    exists addr, lookup_N f.(f_inst).(inst_funcs) i = Some addr /\
      value_typing typing_store (VAL_ref (VAL_ref_func addr)) (T_ref T_funcref)) /\
  (forall i gt, lookup_N C.(tc_globals) i = Some gt ->
    exists v, sglob_val runtime_store f.(f_inst) i = Some v /\
      value_typing typing_store v gt.(tg_t)) /\
  length f.(f_inst).(inst_globals) = length C.(tc_globals).

Lemma const_value_num_inv s v t :
  value_typing s v (T_num t) ->
  exists vn, v = VAL_num vn /\ typeof_num vn = t.
Proof.
  destruct v as [vn|vv|vr].
  - exists vn; split => //.
    by destruct vn, t.
  - by destruct vv, t.
  - destruct vr as [rt|addr|extern|payload]; unfold value_typing, typeof_value, typeof_ref; simpl => //.
    by destruct (ext_func_typing s addr).
Qed.

Lemma const_checker_step_complete typing_store runtime_store f C e ts vs ct' :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_expr C e ->
  List.Forall2 (fun v t => value_typing typing_store v t) vs ts ->
  type_checker.check_single C (Some (type_checker.Build_checker_type ts false)) e = Some ct' ->
  exists ts' vs',
    ct' = type_checker.Build_checker_type ts' false /\
    interp_const_step runtime_store f e vs = Some vs' /\
    List.Forall2 (fun v t => value_typing typing_store v t) vs' ts'.
Proof.
  move => [Hfunc [Hglob Hlength]] Hconst Hstack Hcheck.
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
    specialize (const_value_num_inv _ _ _ Hv2n) as [v2n [-> Ht2]].
    specialize (const_value_num_inv _ _ _ Hv1n) as [v1n [-> Ht1]].
    assert (binop_typecheck v1n v2n n b) as Htc.
    { by rewrite /binop_typecheck Ht1 Ht2 Hagree !eq_refl. }
    specialize (const_binop_total _ _ _ _ Hconst Htc) as [v [Happ Htv]].
    do 2 eexists; split; first reflexivity.
    split.
    + by cbn [interp_const_step]; rewrite Hconst Htc Happ.
    + constructor => //.
      by unfold value_typing; simpl; rewrite Htv value_subtyping_eq.
  - (* vector constant *)
    cbn [type_checker.check_single type_checker.type_update type_checker.consume
      type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    do 2 eexists; split; first reflexivity.
    split; first reflexivity.
    constructor => //.
    by apply value_vec_principal_typing.
  - (* ref.null *)
    cbn [type_checker.check_single type_checker.type_update type_checker.consume
      type_checker.produce] in Hcheck.
    injection Hcheck as <-.
    do 2 eexists; split; first reflexivity.
    split; first reflexivity.
    constructor => //.
    by unfold value_typing; simpl; apply value_subtyping_eq.
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
Qed.

Lemma const_checker_fold_complete typing_store runtime_store f C es ts vs ct' :
  const_environment_typed typing_store runtime_store f C ->
  extended_const_exprs C es ->
  List.Forall2 (fun v t => value_typing typing_store v t) vs ts ->
  type_checker.check C es (Some (type_checker.Build_checker_type ts false)) = Some ct' ->
  exists ts' vs',
    ct' = type_checker.Build_checker_type ts' false /\
    interp_const_stack runtime_store f es vs = Some vs' /\
    List.Forall2 (fun v t => value_typing typing_store v t) vs' ts'.
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
  move => [Hfunc [Hglob Hlen]].
  repeat split => //.
  move => i Hbound.
  apply Hfunc.
  by rewrite /= List.length_map in Hbound.
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
    value_typing typing_store v t.
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
    value_typing typing_store v t.
Proof.
  move => Henv Hconst /b_e_type_checker_reflects_typing Hcheck.
  by eapply interp_get_const_validated; eauto.
Qed.

Lemma sglob_val_added s f g v :
  sglob_val (add_glob s (gen_global_instance g v))
    (const_frame_add_global f (N.of_nat (length s.(s_globals)))).(f_inst)
    (N.of_nat (length f.(f_inst).(inst_globals))) = Some v.
Proof.
  unfold sglob_val, sglob, sglob_ind, lookup_N.
  cbn [const_frame_add_global add_glob].
  rewrite Nnat.Nat2N.id List.nth_error_app2; last reflexivity.
  rewrite Nat.sub_diag /= Nnat.Nat2N.id List.nth_error_app2; last reflexivity.
  by rewrite Nat.sub_diag.
Qed.

Lemma const_environment_add_global typing_store runtime_store f C g v :
  const_environment_typed typing_store runtime_store f C ->
  value_typing typing_store v g.(modglob_type).(tg_t) ->
  const_environment_typed typing_store
    (add_glob runtime_store (gen_global_instance g v))
    (const_frame_add_global f (N.of_nat (length runtime_store.(s_globals))))
    (const_context_add_global C g.(modglob_type)).
Proof.
  move => [Hfunc [Hglob Hlen]] Hvalue.
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
  - change (length (f.(f_inst).(inst_globals) ++ [::N.of_nat (length runtime_store.(s_globals))]) =
      length (C.(tc_globals) ++ [::g.(modglob_type)])).
    by rewrite !List.length_app /= Hlen.
Qed.

Theorem interp_global_chain_complete typing_store runtime_store f C gs :
  const_environment_typed typing_store runtime_store f C ->
  extended_globals_typing C gs ->
  exists s' f' vs,
    interp_global_chain runtime_store f gs = Some (s', f', vs) /\
    List.Forall2 (fun g v => value_typing typing_store v g.(modglob_type).(tg_t)) gs vs /\
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
    specialize (const_environment_add_global _ _ _ _ _ _ Henv Hvalue) as Henv1.
    specialize (IH _ _ _ Henv1 Htail) as [s' [f' [vs [Hchain [Hvalues Henv']]]]].
    exists s', f', (v :: vs).
    split.
    + cbn [interp_global_chain]; rewrite Heval.
      by cbn [alloc_glob]; rewrite Hchain.
    + split; first by constructor.
      replace (const_context_add_globals C (seq.map modglob_type (g :: gs)))
        with (const_context_add_globals (const_context_add_global C g.(modglob_type))
          (seq.map modglob_type gs)); first exact Henv'.
      by destruct C; rewrite /const_context_add_globals /const_context_add_global /= -catA.
Qed.

Lemma const_value_functions_extension s s' added v t :
  s'.(s_funcs) = s.(s_funcs) ++ added ->
  value_typing s v t ->
  value_typing s' v t.
Proof.
  move => Hfunc.
  destruct v as [vn|vv|vr] => //.
  destruct vr as [rt|addr|external|payload] => //.
  unfold value_typing, typeof_value, typeof_ref, ext_func_typing.
  destruct (lookup_N (s_funcs s) addr) as [cl|] eqn:Hlookup => //.
  rewrite Hfunc /lookup_N.
  unfold lookup_N in Hlookup.
  rewrite List.nth_error_app1; first by rewrite Hlookup.
  by apply nth_error_Some_length in Hlookup.
Qed.

Lemma const_initial_environment typing_store runtime_store f C v_imps t_imps t_imps_mod added :
  store_typing runtime_store ->
  List.Forall2 (external_typing runtime_store) v_imps t_imps ->
  List.Forall2 import_subtyping t_imps t_imps_mod ->
  typing_store.(s_funcs) = runtime_store.(s_funcs) ++ added ->
  f.(f_inst).(inst_funcs) = ext_funcs v_imps ++
    iota_N (length runtime_store.(s_funcs)) (length added) ->
  f.(f_inst).(inst_globals) = ext_globals v_imps ->
  length C.(tc_funcs) = length (ext_t_funcs t_imps_mod) + length added ->
  C.(tc_globals) = ext_t_globals t_imps_mod ->
  const_environment_typed typing_store runtime_store f C.
Proof.
  move => HST Himps Hsub Hstore Hfunc Hglob Hnfunc Hglobaltypes.
  specialize (vt_imps_comp_len Himps) as [Hflen [_ [_ Hglen]]].
  specialize (import_subtyping_comp_len Hsub) as [Hflen' [_ [_ Hglen']]].
  split.
  - move => i Hbound.
    assert ((N.to_nat i < length f.(f_inst).(inst_funcs))%coq_nat) as Hlen.
    { rewrite Hfunc List.length_app iota_N_length.
      by lias.
    }
    destruct (lookup_N f.(f_inst).(inst_funcs) i) as [addr|] eqn:Haddr.
    2: { apply List.nth_error_None in Haddr; by lias. }
    exists addr; split => //.
    assert ((N.to_nat addr < length typing_store.(s_funcs))%coq_nat) as Haddrbound.
    { rewrite Hfunc in Haddr.
      unfold lookup_N in Haddr.
      apply cat_lookup in Haddr as [Himport | Hdefined].
      - apply ext_funcs_lookup_exist in Himport as [n Hnth].
        specialize (Forall2_lookup Himps Hnth) as [et [Hntht Htype]].
        unfold external_typing, ext_typing, ext_func_typing in Htype.
        destruct (lookup_N (s_funcs runtime_store) addr) as [cl|] eqn:Hcl => //.
        apply nth_error_Some_length in Hcl.
        rewrite Hstore List.length_app; by lias.
      - apply iota_N_lookup_Some in Hdefined as [-> Hrange].
        rewrite Nnat.Nat2N.id Hstore List.length_app; by lias.
    }
    unfold value_typing, typeof_value, typeof_ref, ext_func_typing.
    destruct (lookup_N (s_funcs typing_store) addr) as [cl|] eqn:Hcl.
    + by apply value_subtyping_eq.
    + apply List.nth_error_None in Hcl; by lias.
  - split.
    + move => i gt Hlookup.
      rewrite Hglobaltypes in Hlookup.
      specialize (import_subtyping_globs_impl' Hsub Hlookup)
        as [gt' [Hnthsub Hsubgt]].
      move/eqP: Hsubgt => Hsubgt; subst gt'.
      specialize (vt_imps_globals_typing Himps Hnthsub) as [addr [Haddr Htext]].
      change (lookup_N (ext_globals v_imps) i = Some addr) in Haddr.
      unfold external_typing, ext_typing, ext_global_typing in Htext.
      destruct (lookup_N (s_globals runtime_store) addr) as [gi|] eqn:Hgi => //.
      injection Htext as <-.
      exists gi.(g_val); split.
      * by unfold sglob_val, sglob, sglob_ind; rewrite Hglob Haddr Hgi.
      * eapply const_value_functions_extension; first exact Hstore.
        destruct runtime_store; simpl in *.
        destruct HST as [_ [_ [_ [_ [Hglobals _]]]]].
        specialize (Forall_lookup Hglobals Hgi) as [gt Htyped].
        unfold globalinst_typing in Htyped.
        destruct gi => /=.
        remove_bools_options; by subst.
    + rewrite Hglob Hglobaltypes; by lias.
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
  - by destruct vn, rt.
  - by destruct vv, rt.
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

Theorem module_initializers_complete s m v_imps t_imps t_imps_mod t_exps message :
  store_typing s ->
  module_type_checker m = (Some (t_imps_mod, t_exps), message) ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.Forall2 import_subtyping t_imps t_imps_mod ->
  exists s_init f_init g_inits r_inits,
    interp_global_chain s (module_init_frame s m v_imps) m.(mod_globals) =
      Some (s_init, f_init, g_inits) /\
    get_elem_inits s_init f_init m.(mod_elems) = Some r_inits.
Proof.
  move => HST Hcheck Himps Hsub.
  specialize (module_type_checker_sound _ _ _ _ Hcheck) as Hvalid.
  destruct m.
  destruct Hvalid as [Hdecl Hvalid].
  unfold module_components_typing in Hvalid.
  destruct Hvalid as [fts [tts [mts [gts [rts [dts
    [Hmtypes [Hmfuncs [Hmtabs [Hmmems [Hmemcount [[Hgts Hglobals]
    [Hmelems [Hmdatas [Hstart [Hmimports [Hmexports Hnames]]]]]]]]]]]]]]]]].
  match type of Hglobals with extended_globals_typing ?C0 _ => pose Cinit := C0 end.
  change (extended_globals_typing Cinit mod_globals) in Hglobals.
  pose added := (map (fun mf => gen_func_instance mf empty_moduleinst) mod_funcs : list (@funcinst hfc)).
  pose typing_store := Build_store_record (s.(s_funcs) ++ added)
    s.(s_tables) s.(s_mems) s.(s_globals) s.(s_elems) s.(s_datas) s.(s_types).
  assert (const_environment_typed typing_store s
    (module_init_frame s (Build_module mod_types mod_funcs mod_tables mod_mems
      mod_globals mod_elems mod_datas mod_start mod_imports mod_exports) v_imps)
    Cinit) as Henv.
  { eapply const_initial_environment; eauto.
    - reflexivity.
    - cbn [module_init_frame f_inst inst_funcs datatypes.mod_funcs].
      by rewrite /added List.length_map.
    - change (length (ext_t_funcs t_imps_mod ++ fts) =
        length (ext_t_funcs t_imps_mod) + length added).
      rewrite List.length_app /added List.length_map.
      by rewrite (List.Forall2_length Hmfuncs).
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
  exists s_init, f_init, g_inits, r_inits; by split.
Qed.

Theorem interp_instantiate_complete hs s m v_imps t_imps t_imps_mod t_exps message :
  store_typing s ->
  module_type_checker m = (Some (t_imps_mod, t_exps), message) ->
  List.Forall2 (external_typing s) v_imps t_imps ->
  List.Forall2 import_subtyping t_imps t_imps_mod ->
  exists s' f es,
    interp_instantiate hs s m v_imps =
      (Some (hs, s', f, es), String.EmptyString).
Proof.
  move => HST Hcheck Himps Hsub.
  pose proof (module_type_checker_sound _ _ _ _ Hcheck) as Hvalid.
  destruct Hvalid as [[source [names [Hclosed Hconsistent]]] _].
  assert (Hregistry : canonical_registry_valid s.(s_types)).
  { apply canonical_registry_validb_correct. exact (proj1 HST). }
  destruct (validated_closing_portable _ _ _ _ Hregistry Hclosed Hconsistent)
    as [registry [typeids [Hcanonical Hidentities]]].
  specialize (module_initializers_complete _ _ _ _ _ _ _ HST Hcheck Himps Hsub)
    as [s_init [f_init [g_inits [r_inits [Hglobals Helems]]]]].
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
  assert (all2 import_subtyping t_imps t_imps_mod) as Hmatch.
  { by apply Forall2_all2. }
  unfold interp_instantiate.
  rewrite Hcheck Hcanonical Hidentities Himports Hmatch Hglobals Helems.
  destruct (interp_alloc_module s m v_imps g_inits r_inits registry typeids)
    as [s' inst].
  by do 3 eexists.
Qed.

End Host.
