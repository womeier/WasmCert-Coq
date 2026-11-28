(** Soundness of the executable instantiation wrt the relational version. **)
(** The main proof to be done is the algorithm for breaking circularities
    in the evaluation of various initialisers. **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_ctx instantiation_func instantiation_properties type_checker_reflects_typing.
From Wasm Require Import gc_declaration_typing.
From Wasm Require Import extended_const.
From Stdlib Require Import Program.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Section Host.

Context `{ho: host}.
  
Lemma module_type_checker_sound: forall m t_imps t_exps str,
  module_type_checker m = (Some (t_imps, t_exps), str) ->
  module_typing m t_imps t_exps.
Proof.
  move => m t_imps t_exps str Hmodcheck.
  unfold module_type_checker in Hmodcheck.
  destruct (close_and_validate_type_groups nil (module_type_groups m))
    as [[registry ids]|] eqn:Hclosed => //.
  destruct (source_type_identitiesb registry ids (List.concat (mod_types m)) ids)
    eqn:Hidentity => //.
  destruct (module_runtime_types_closedb registry ids m) eqn:Hruntime => //.
  split; first by exists registry, ids; repeat split.
  unfold module_components_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types (List.concat mod_types) mod_funcs) as [fts | ] eqn:Hmftypes => //;
    destruct (module_imports_typer (List.concat mod_types) mod_imports) as [impts | ] eqn:Hmitypes => //.
  destruct (gather_m_e_types (ext_t_tables impts ++ map modtab_type mod_tables) mod_elems) as [ets | ] eqn:Hmetypes => //.
  destruct (gather_m_d_types (ext_t_mems impts ++ map modmem_type mod_mems) mod_datas) as [dts | ] eqn:Hmdtypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ && _ && _) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hnameunique].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobalcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcountcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htablecheck].
  unfold module_components_typing.
  injection Hmodcheck as ->->.
  
  exists fts, (map modtab_type mod_tables), (map modmem_type mod_mems), (gather_m_g_types mod_globals), ets, dts.
  repeat split => //.

  (* types *)
  { apply Forall_spec. intros n x Lookup. by rewrite source_subtype_valid_true. }
  
  (* funcs *)
  { clear - Hfunccheck Hmftypes hfc.
    unfold gather_m_f_types in Hmftypes.
    apply Forall2_spec => //; first by apply those_length in Hmftypes; rewrite List.length_map in Hmftypes.
    move => n mfunc [tx ty] Hfuncnth Hftsnth.
    eapply all_projection in Hfunccheck; eauto.
    eapply those_map_lookup in Hmftypes as [ft [Hmap Hnth]]; eauto.
    destruct mfunc, ft.
    unfold gather_m_f_type in Hmap.
    Opaque type_checker.b_e_type_checker.
    simpl in *.
    simplify_multieq.
    split => //.
    rewrite Hmap in Hfunccheck.
    remove_bools_options.
    split => //; last by apply/eqP.
    by apply/b_e_type_checker_reflects_typing.
  }
  (* tables *)
  { apply Forall2_spec => //; first by rewrite List.length_map.
    move => n mtable [tx ty] Htablenth Hftsnth.
    eapply all_projection in Htablecheck; eauto.
    simpl in *.
    unfold module_table_typing, module_table_type_checker in *; rewrite Htablecheck => /=.
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    by apply/eqP.
  }
  (* memories *)
  { apply Forall2_spec => //; first by rewrite List.length_map.
    move => n mmem [tx ty] Hmemnth Hftsnth.
    eapply all_projection in Hmemcheck; eauto.
    simpl in *.
    unfold module_mem_typing, module_mem_type_checker in *; rewrite Hmemcheck => /=.
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    by apply/eqP.
  }
  (* globals *)
  { clear -Hglobalcheck hfc.
    by apply/extended_globals_type_checker_reflects.
  }
  (* elem *)
  { clear -Helemcheck Hmetypes hfc.
    unfold gather_m_e_types in Hmetypes.
    apply Forall2_spec => //; first by apply those_length in Hmetypes; rewrite List.length_map in Hmetypes.
    move => n x tref Hnthelem Hntht.
    eapply those_map_lookup in Hmetypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Helemcheck; eauto.
    unfold module_elem_typing.
    unfold module_elem_type_checker in Helemcheck.
    destruct x; simpl in *.
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hmode].
    move/andP in Helemcheck; destruct Helemcheck as [Hconst Hbet].
    assert (t = modelem_type) as Hteq.
    { unfold gather_m_e_type in Hmap.
      destruct modelem_mode; simpl in *; try by inversion Hmap.
      remove_bools_options. by apply/eqP.
    }
    subst t.
    repeat split => //.
    { apply Forall_spec.
      move => m be Hnth.
      split.
      - by eapply all_projection in Hconst; eauto.
      - eapply all_projection in Hbet; eauto.
        by move/b_e_type_checker_reflects_typing in Hbet.
    }
    { unfold module_elem_mode_checker in Hmode; destruct modelem_mode; simpl in * => //.
      remove_bools_options.
      eexists; split; first by eauto.
      destruct t0; repeat split => //.
      by move/b_e_type_checker_reflects_typing in H1.
    }
  }
  (* data *)
  { clear -Hdatacheck Hmdtypes hfc.
    unfold gather_m_d_types in Hmdtypes.
    apply Forall2_spec => //; first by apply those_length in Hmdtypes; rewrite List.length_map in Hmdtypes.
    move => n x tref Hnthdata Hntht.
    eapply those_map_lookup in Hmdtypes as [t [Hmap Hnth]]; eauto; simpl in *.
    simplify_multieq.
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_typing.
    unfold module_data_type_checker in Hdatacheck.
    destruct x; simpl in *.
    unfold module_data_mode_checker in Hdatacheck; destruct moddata_mode; simpl in * => //; try repeat split => //; remove_bools_options => //.
    eexists; split; first by eauto.
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in H.
  }
  (* imports *)
  { clear - Hmitypes.
    unfold module_imports_typer in Hmitypes.
    apply Forall2_spec; first by apply those_length in Hmitypes; rewrite List.length_map in Hmitypes.
    move => n mi extt Hminth Htinth.
    eapply those_map_lookup in Hmitypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct mi; simpl in *.
    unfold module_import_desc_typer in Hmap.
    unfold module_import_typing.
    destruct imp_desc; apply/eqP => /=; remove_bools_options => //; by rewrite eq_refl.
  }
  (* exports *)
  { clear - Hmexptypes.
    unfold module_exports_typer in Hmexptypes.
    apply Forall2_spec; first by apply those_length in Hmexptypes; rewrite List.length_map in Hmexptypes.
    move => n me extt Hmexpth Htexpth.
    eapply those_map_lookup in Hmexptypes as [Htext [Hmap Hnth]]; eauto.
    simplify_multieq.
    destruct me; simpl in *.
    unfold module_export_typer in Hmap.
    unfold module_export_typing.
    simpl in *.
    destruct modexp_desc => //=; remove_bools_options; unfold module_export_desc_typing => /=; rewrite Hoption; by apply/eqP.
  }
Qed.

Lemma external_type_checker_sound: forall s ext t,
  external_type_checker s ext = Some t ->
  external_typing s ext t.
Proof.
  move => s ext t Hextcheck.
  unfold external_type_checker in Hextcheck; move/eqP in Hextcheck.
  by destruct ext; destruct t => //; remove_bools_options; subst.
Qed.

Lemma interp_alloc_sound: forall s m v_imps g_inits r_inits registry typeids s' inst,
  close_and_validate_type_groups s.(s_types) (module_type_groups m) = Some (registry, typeids) ->
  source_type_identitiesb registry typeids (List.concat m.(mod_types)) typeids = true ->
  length g_inits = length m.(mod_globals) ->
  length r_inits = length m.(mod_elems) ->
  interp_alloc_module s m v_imps g_inits r_inits registry typeids = Some (s', inst) ->
  alloc_module s m v_imps g_inits r_inits (s', inst).
Proof.
  move => s m v_imps g_inits r_inits registry typeids s' inst Hclosed Hidentity Hgvs_len Hrvs_len Halloc.
  unfold interp_alloc_module in Halloc.
  destruct (module_source_context m) as [source|] eqn:Source => //.
  destruct (those (map (close_table_initial registry typeids)
    (map modtab_type (mod_tables m)))) as [tables|] eqn:Tables => //.
  destruct (those (map (close_global_type typeids)
    (map modglob_type (mod_globals m)))) as [globals|] eqn:Globals => //.
  destruct (those (map (close_reference_type typeids)
    (map modelem_type (mod_elems m)))) as [elements|] eqn:Elements => //.
  destruct ((length g_inits == length globals) &&
    (length r_inits == length elements)) eqn:Lengths => //.
  move/andP: Lengths => [/eqP GlobalLength /eqP ElementLength].
  unfold alloc_module; simpl.
  exists registry, typeids, source, tables, globals, elements.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <- <-.
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs Hallocelems Hallocdatas => /=.
  apply alloc_func_iota_N in Hallocfuncs.
  apply alloc_table_iota_N in Halloctabs.
  apply alloc_mem_iota_N in Hallocmems.
  apply alloc_global_iota_N in Hallocglobs; last exact GlobalLength.
  apply alloc_elem_iota_N in Hallocelems; last exact ElementLength.
  apply alloc_data_iota_N in Hallocdatas.

  have TableLength := those_length Tables.
  have ClosedGlobalLength := those_length Globals.
  have ClosedElementLength := those_length Elements.
  rewrite !List.length_map in TableLength ClosedGlobalLength ClosedElementLength.
  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  subst.
  repeat rewrite List.length_map.
  unfold module_runtime_instance.
  repeat rewrite TableLength.
  repeat rewrite ClosedGlobalLength.
  repeat rewrite ClosedElementLength.
  by repeat split.
Qed.

(* Each initializer sees imports and the types of preceding defined globals. *)
Lemma module_typecheck_glob_aux: forall m t_imps t_exps str,
    module_type_checker m = (Some (t_imps, t_exps), str) ->
    exists c, extended_globals_type_checker c m.(mod_globals).
Proof.
  move => m t_imps t_exps str.
  unfold module_type_checker, module_components_type_checker.
  move => Hmodcheck.
  destruct (close_and_validate_type_groups nil (module_type_groups m))
    as [[registry typeids]|] => //.
  destruct (source_type_identitiesb registry typeids (List.concat (mod_types m)) typeids) => //.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.

Lemma module_typecheck_elem_aux: forall m t_imps t_exps str,
    module_type_checker m = (Some (t_imps, t_exps), str) ->
    exists c, all (module_elem_type_checker c) m.(mod_elems).
Proof.
  move => m t_imps t_exps str.
  unfold module_type_checker, module_components_type_checker.
  move => Hmodcheck.
  destruct (close_and_validate_type_groups nil (module_type_groups m))
    as [[registry typeids]|] => //.
  destruct (source_type_identitiesb registry typeids (List.concat (mod_types m)) typeids) => //.
  destruct m.
  remove_bools_options.
  simpl in *.
  by eexists; eauto.
Qed.

Lemma interp_instantiate_imp_instantiate : forall hs hs' s m v_imps s_end f bes str,
  interp_instantiate hs s m v_imps = (Some (hs', s_end, f, bes), str) ->
  instantiate s m v_imps (s_end, f, bes).
Proof.
  move => hs hs' s m v_imps s_end f bes str.
  unfold interp_instantiate, instantiate.
  move => Hinterp.
  destruct (module_type_checker m) as [[[t_imps_mod t_exps]|] str'] eqn:Hmodcheck => //.
  destruct (close_and_validate_type_groups (s_types s) (module_type_groups m))
    as [[registry typeids]|] eqn:Hclosed => //.
  destruct (source_type_identitiesb registry typeids (List.concat (mod_types m)) typeids)
    eqn:Hidentity => //.
  destruct (those _) as [t_imps | ] eqn:Hextcheck => //.
  destruct (those (map (close_import_desc registry typeids)
    (map imp_desc (mod_imports m)))) as [expected|] eqn:Hexpected => //.
  destruct (module_source_context m) as [source|] eqn:Hsource => //.
  destruct (all2 (closed_import_subtyping registry) _ _) eqn:Hextsubtyping => //.
  destruct (alloc_funcs s (mod_funcs m)
    (module_runtime_instance s m v_imps typeids source)) as [preview ifs0] eqn:Hpreview.
  destruct (interp_global_chain _ _ (mod_globals m)) as [[[s_init f_init_final] g_inits] |] eqn:Hglobinit => //.
  destruct (get_elem_inits _ _ (mod_elems m)) as [r_inits |] eqn:Heleminit => //.
  destruct (interp_alloc_module s m v_imps g_inits r_inits registry typeids)
    as [[s' inst']|] eqn:Halloc => //.
  injection Hinterp as <- <- Heq.

  exists t_imps_mod, t_imps, t_exps, hs, inst', g_inits, r_inits, expected.

  (* Proving these first so they can be used in the reasoning for initialisers later *)
  assert (module_typing m t_imps_mod t_exps) as Hmodtype; first by eapply module_type_checker_sound; eauto.
  
  assert (alloc_module s m v_imps g_inits r_inits (s', inst')) as Hallocmodule.
  { eapply interp_alloc_sound; eauto.
    - by eapply interp_global_chain_length; eauto.
    - by apply those_length in Heleminit; rewrite length_is_size size_map -length_is_size in Heleminit.
  }
  
  assert (List.Forall2 (external_typing s) v_imps t_imps) as Hexttype.
  { apply Forall2_spec.
    - apply those_length in Hextcheck.
      by rewrite List.length_map in Hextcheck.
    - move => n vext text Hnthv Hntht.
      apply external_type_checker_sound.
      eapply those_map_lookup in Hextcheck as [text' [Hmap Hnth]]; eauto.
      by simplify_multieq.
  }
  
  assert (Hgvs_len : length g_inits = length m.(mod_globals)).
  {
    by eapply interp_global_chain_length; eauto.
  }
  
  assert (Hrvs_len : length r_inits = length m.(mod_elems)).
  {
    apply those_length in Heleminit.
    rewrite length_is_size size_map in Heleminit.
    by rewrite length_is_size.
  }

  (* store *)
  unfold interp_alloc_module in Halloc.
  rewrite Hsource in Halloc.
  destruct (those (map (close_table_initial registry typeids)
    (map modtab_type (mod_tables m)))) as [tables|] eqn:Htables => //.
  destruct (those (map (close_global_type typeids)
    (map modglob_type (mod_globals m)))) as [globals|] eqn:Hglobals => //.
  destruct (those (map (close_reference_type typeids)
    (map modelem_type (mod_elems m)))) as [elements|] eqn:Helements => //.
  destruct ((length g_inits == length globals) &&
    (length r_inits == length elements)) eqn:Hlengths => //.
  move/andP: Hlengths => [/eqP GlobalLength /eqP ElementLength].
  rewrite Hpreview in Halloc.
  have Hallocfuncs := Hpreview.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <- Heqinst.
  specialize (alloc_func_iota_N Hallocfuncs) as Hfuncaddrs.
  specialize (alloc_table_iota_N Halloctabs) as Htableaddrs.
  specialize (alloc_mem_iota_N Hallocmems) as Hmemaddrs.
  specialize (alloc_global_iota_N Hallocglobs GlobalLength) as Hglobaladdrs.
  specialize (alloc_elem_iota_N Hallocelems ElementLength) as Helemaddrs.
  specialize (alloc_data_iota_N Hallocdatas) as Hdataaddrs.

  extract_premise.
  specialize (interp_global_chain_results _ _ _ _ _ _ Hglobinit)
    as [Hinitfuncs [Hinitglobals Hinitresults]].
  specialize (interp_global_chain_shape _ _ _ _ _ _ Hglobinit)
    as [initial_globals [Hinitclosing [Hinitstore Hinitaddrs]]].
  destruct (interp_global_chain_type_world _ _ _ _ _ _ Hglobinit)
    as [Hinittypes Hinitnames].
  cbn [module_init_frame f_inst inst_defined_types] in Hinitclosing.
  change (those (List.map (close_global_type typeids)
    (List.map modglob_type (mod_globals m))) = Some globals) in Hglobals.
  rewrite List.map_map in Hglobals.
  rewrite Hglobals in Hinitclosing.
  injection Hinitclosing as <-.

  destruct s, preview, s2, s3, s4, s5, s6; simpl in *.
  repeat split => //.
  - (* subtyping *)
    by eapply Forall2_all2_impl; eauto.
  - (* global initialisers -- hardest case, since it's the main difference in the 
       executable version *)
    unfold instantiate_globals.
    apply Forall2_spec => //.
    move => n mglob gv Hnth1 Hnth2.
    eapply Forall2_lookup in Hinitresults as [gi [Hnth Hmap]]; last by eauto.
    simplify_multieq.
    apply interp_get_const_sound.
     eapply (interp_get_const_environment s_init f_init_final); last exact Hmap.
     + by symmetry.
     + reflexivity.
     + by rewrite Hinitfuncs.
    + move => i v.
      unfold sglob_val, sglob, sglob_ind.
      by rewrite Hinitstore Hinitaddrs.
  - subst.
    unfold instantiate_elems.
    apply Forall2_spec => //.
    move => n melem vs Hnth1 Hnth2.
    eapply those_map_lookup in Heleminit as [ei [Hmap Hnth]]; last by eauto.
    simplify_multieq.
    apply Forall2_spec => //=.
    + apply those_length in Hmap.
      by rewrite List.length_map in Hmap; simpl in Hmap.
    + move => i bes vref Hnthinit Hnthei.
      eapply those_map_lookup in Hmap as [vref' [Hmap Hnth']]; eauto.
      unfold interp_get_vref in Hmap.
      destruct (interp_get_const _ _ bes) as [[v|v|v]|] eqn:Heval => //.
      injection Hmap as <-.
      simplify_multieq.
      apply (interp_get_const_sound _ _ _ _ (VAL_ref v)).
       eapply (interp_get_const_environment s_init f_init_final); last exact Heval.
       * by symmetry.
       * reflexivity.
      * by rewrite Hinitfuncs.
      * move => j w.
        unfold sglob_val, sglob, sglob_ind.
        by rewrite Hinitstore Hinitaddrs.
Qed.

End Host.
