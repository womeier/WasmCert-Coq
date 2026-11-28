(** Soundness of the executable instantiation wrt the relational version. **)
(** The main proof to be done is the algorithm for breaking circularities
    in the evaluation of various initialisers. **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_ctx instantiation_func instantiation_properties type_checker_reflects_typing.
From Stdlib Require Import Program Arith.PeanoNat.
From Wasm Require Import gc_declaration_typing.
From Wasm Require Import gc_runtime_type_properties.
From Wasm Require Import gc_type_context.

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
  destruct (source_type_identitiesb registry ids (List.concat (mod_types m)) ids &&
    module_source_types_closingb registry ids m) eqn:Hscope => //.
  move/andP in Hscope; destruct Hscope as [Hidentity Hscope].
  split.
  { exists registry, ids; split; first exact Hclosed.
    split; first exact Hidentity.
    apply (proj1 (module_source_types_closingb_correct registry ids m)); exact Hscope. }
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
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htablecheck].
  move/andP in Hfunccheck; destruct Hfunccheck as [Htypescheck Hfunccheck].
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
    move => n mtable [tx ty a] Htablenth Hftsnth.
    eapply all_projection in Htablecheck; eauto.
    simpl in *.
    unfold module_table_typing, module_table_type_checker in *.
    move/andP in Htablecheck; destruct Htablecheck as [Htablecheck Hbet].
    move/andP in Htablecheck; destruct Htablecheck as [Htablecheck Htable_scope].
    move/andP in Htablecheck; destruct Htablecheck as [Hvalid Hconst].
    apply nth_error_map in Hftsnth as [mtab [??]].
    simplify_multieq.
    repeat split => //.
    - move/source_heap_in_contextb_correct in Htable_scope.
      by rewrite H1 in Htable_scope.
    - move/b_e_type_checker_reflects_typing in Hbet.
      by rewrite H1 in Hbet.
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
    unfold gather_m_g_types.
    apply Forall2_spec; first by rewrite List.length_map.
    move => n mglob gt Hgnth Hmgnth.
    erewrite List.map_nth_error in Hmgnth; last by eauto.
    injection Hmgnth as <-.
    unfold module_global_typing.
    destruct mglob => /=.
    eapply all_projection in Hglobalcheck; eauto.
    unfold module_global_type_checker in Hglobalcheck.
    move/andP in Hglobalcheck; destruct Hglobalcheck as [? Hbet].
    repeat split => //.
    by move/b_e_type_checker_reflects_typing in Hbet.
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
      by remove_bools_options.
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
  destruct ext as [a|a|a|a]; simpl in Hextcheck; try exact Hextcheck.
   unfold external_type_checker in Hextcheck.
  destruct (lookup_N (s_funcs s) a) as [cl|] eqn:Hlookup; try discriminate.
  destruct (funcinst_defined_type s cl) as [id|]; try discriminate.
  destruct (close_function_type (funcinst_type_names cl) BinNums.N0 (cl_type cl))
    as [closed|]; try discriminate.
  destruct (expand_function_type (s_types s) id) as [expanded|]; try discriminate.
  destruct (closed_function_type_eq_dec closed expanded); try discriminate.
  inversion Hextcheck; subst.
  by unfold external_typing, ext_typing, ext_func_typing; rewrite Hlookup.
Qed.

Lemma external_type_checker_complete s ext t :
  store_typing s ->
  external_typing s ext t ->
  external_type_checker s ext = Some t.
Proof.
  move => Hstore Hext.
  destruct ext as [a|a|a|a]; try exact Hext.
  unfold external_typing, ext_typing in Hext.
  unfold ext_func_typing in Hext.
  destruct (lookup_N (s_funcs s) a) as [fi|] eqn:Hlookup;
    simpl in Hext; try discriminate.
  inversion Hext; subst t.
  destruct (store_typing_function_expansion_agreement s a fi Hstore Hlookup)
    as [id [signature [Identity [Closed Expanded]]]].
  unfold lookup_func_defined_type in Identity; rewrite Hlookup in Identity.
  unfold external_type_checker; rewrite Hlookup Identity Closed Expanded.
  destruct (closed_function_type_eq_dec signature signature); [reflexivity|contradiction].
Qed.

Lemma external_type_checker_correct s ext t :
  store_typing s ->
  (external_type_checker s ext = Some t <-> external_typing s ext t).
Proof.
  move => Hstore; split.
  - apply external_type_checker_sound.
  - by apply external_type_checker_complete.
Qed.

Lemma interp_alloc_sound: forall s m v_imps g_inits r_inits t_inits registry typeids s' inst,
  close_and_validate_type_groups s.(s_types) (module_type_groups m) = Some (registry, typeids) ->
  source_type_identitiesb registry typeids (List.concat m.(mod_types)) typeids = true ->
  length g_inits = length m.(mod_globals) ->
  length r_inits = length m.(mod_elems) ->
  length t_inits = length m.(mod_tables) ->
  interp_alloc_module s m v_imps g_inits r_inits t_inits registry typeids = (s', inst) ->
  alloc_module s m v_imps g_inits r_inits t_inits (s', inst).
Proof.
  move => s m v_imps g_inits r_inits t_inits registry typeids s' inst Hclosed Hidentity Hgvs_len Hrvs_len Htvs_len Halloc.
  unfold interp_alloc_module in Halloc.
  unfold alloc_module; simpl in *.
  exists registry, typeids.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs_with_init _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <-<-.
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs Hallocelems Hallocdatas => /=.
  apply alloc_func_iota_N in Hallocfuncs.
  apply alloc_table_inits_iota_N in Halloctabs.
  rewrite List.length_combine List.length_map Htvs_len Nat.min_id in Halloctabs.
  apply alloc_mem_iota_N in Hallocmems.
  apply alloc_global_iota_N in Hallocglobs; last assumption.
  apply alloc_elem_iota_N in Hallocelems; last assumption.
  apply alloc_data_iota_N in Hallocdatas.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  subst.
  repeat rewrite List.length_map.
  by repeat rewrite eq_refl => /=.
Qed.

(* Breaking circularity: the global initialisers need to be well-typed under a
   context with only the imported globals added. *)
Lemma module_typecheck_glob_aux: forall m t_imps t_exps str,
    module_type_checker m = (Some (t_imps, t_exps), str) ->
    exists c, all (module_global_type_checker c) m.(mod_globals).
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

Lemma module_typecheck_table_aux: forall m t_imps t_exps str,
    module_type_checker m = (Some (t_imps, t_exps), str) ->
    exists c, all (module_table_type_checker c) m.(mod_tables).
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

Lemma interp_get_vref_const s f es r :
  interp_get_vref s f es = Some r ->
  interp_get_const s f es = Some (VAL_ref r).
Proof.
  unfold interp_get_vref.
  destruct (interp_get_const s f es) as [v|] eqn:E; try discriminate.
  destruct v as [v|v|v]; try discriminate.
  by move => [<-].
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
  destruct (all2 import_subtyping _ _) eqn:Hextsubtyping => //.
  destruct (get_table_inits _ _ (mod_tables m)) as [t_inits|] eqn:Htableinit => //.
  destruct (get_global_inits _ _ (mod_globals m)) as [g_inits |] eqn:Hglobinit => //.
  destruct (get_elem_inits _ _ (mod_elems m)) as [r_inits |] eqn:Heleminit => //.
  destruct (interp_alloc_module s m v_imps g_inits r_inits t_inits registry typeids) as [s' inst'] eqn:Halloc => //.
  injection Hinterp as <- <- Heq.

  exists t_imps_mod, t_imps, t_exps, hs, inst', g_inits, r_inits, t_inits.

  (* Proving these first so they can be used in the reasoning for initialisers later *)
  assert (module_typing m t_imps_mod t_exps) as Hmodtype; first by eapply module_type_checker_sound; eauto.
  
  assert (alloc_module s m v_imps g_inits r_inits t_inits (s', inst')) as Hallocmodule.
  { eapply interp_alloc_sound; eauto.
    - by apply those_length in Hglobinit; rewrite length_is_size size_map -length_is_size in Hglobinit.
    - by apply those_length in Heleminit; rewrite length_is_size size_map -length_is_size in Heleminit.
    - by apply those_length in Htableinit; rewrite length_is_size size_map -length_is_size in Htableinit.
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
    apply those_length in Hglobinit.
    rewrite length_is_size size_map in Hglobinit.
    by rewrite length_is_size.
  }
  
  assert (Hrvs_len : length r_inits = length m.(mod_elems)).
  {
    apply those_length in Heleminit.
    rewrite length_is_size size_map in Heleminit.
    by rewrite length_is_size.
  }

  assert (Htvs_len : length t_inits = length m.(mod_tables)).
  {
    apply those_length in Htableinit.
    rewrite length_is_size size_map in Htableinit.
    by rewrite length_is_size.
  }

  (* store *)
  unfold interp_alloc_module in Halloc.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs_with_init _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  injection Halloc as <- Heqinst.
  specialize (alloc_func_iota_N Hallocfuncs) as Hfuncaddrs.
  specialize (alloc_table_inits_iota_N Halloctabs) as Htableaddrs.
  rewrite List.length_combine List.length_map Htvs_len Nat.min_id in Htableaddrs.
  specialize (alloc_mem_iota_N Hallocmems) as Hmemaddrs.
  specialize (alloc_global_iota_N Hallocglobs Hgvs_len) as Hglobaladdrs.
  specialize (alloc_elem_iota_N Hallocelems Hrvs_len) as Helemaddrs.
  specialize (alloc_data_iota_N Hallocdatas) as Hdataaddrs.

  extract_premise.

  destruct s, s1, s2, s3, s4, s5, s6; simpl in *.
  repeat split => //.
  - (* subtyping *)
    by eapply Forall2_all2_impl; eauto.
  - (* table initialisers *)
    unfold instantiate_tables.
    apply Forall2_spec => //.
    move => n mtable tv Hnth1 Hnth2.
    eapply those_map_lookup in Htableinit as [ti [Hmap Hnth]]; last by eauto.
    apply interp_get_vref_const in Hmap.
    apply module_typecheck_table_aux in Hmodcheck as [C Hmodcheck].
    unfold module_table_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    move/andP in Hmodcheck; destruct Hmodcheck as [Hchecks Hbetype].
    move/andP in Hchecks; destruct Hchecks as [Hchecks Hscope_table].
    move/andP in Hchecks; destruct Hchecks as [_ Hconstexpr].
    move/b_e_type_checker_reflects_typing in Hbetype.
    eapply const_exprs_impl in Hconstexpr; last by eauto.
    destruct Hconstexpr as [e [Hinit Hconst]].
    rewrite Hinit in Hmap |- *.
    unfold const_expr in Hconst.
    destruct e => //; simpl in Hmap; try discriminate.
    + injection Hmap as <-; simpl in *; simplify_multieq; by constructor.
    + remove_bools_options; simplify_multieq.
      by constructor; apply r_ref_func => /=.
    + remove_bools_options; simplify_multieq.
      constructor; apply r_global_get => /=.
      unfold sglob_val, sglob, sglob_ind in *; simpl in *.
      remove_bools_options.
      lookup_N_to_nth_error.
      by erewrite nth_error_app_Some; eauto.
  - (* global initialisers -- hardest case, since it's the main difference in the 
       executable version *)
    unfold instantiate_globals.
    apply Forall2_spec => //.
    move => n mglob gv Hnth1 Hnth2.
    eapply those_map_lookup in Hglobinit as [gi [Hmap Hnth]]; last by eauto.
    apply module_typecheck_glob_aux in Hmodcheck as [C Hmodcheck].
    unfold module_global_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct mglob.
    move/andP in Hmodcheck.
    destruct Hmodcheck as [Hconstexpr Hbetype].
    move/b_e_type_checker_reflects_typing in Hbetype.
    eapply const_exprs_impl in Hconstexpr; last by eauto.
    destruct Hconstexpr as [e [-> Hconst]].
    unfold const_expr in Hconst.
    destruct e => //; subst; simpl in Hmap.
    1,2,3: (* const_num/const_vec/ref_null *)
      injection Hmap as <-;
      simpl in *;
      simplify_multieq;
      by constructor.
    { (* ref_func *)
      remove_bools_options; simplify_multieq.
      by constructor; apply r_ref_func => /=.
    }
    { (* global_get *)
      remove_bools_options; simplify_multieq.
      constructor; apply r_global_get => /=.
      unfold sglob_val, sglob, sglob_ind in *; simpl in *.
      remove_bools_options.
      lookup_N_to_nth_error.
      by erewrite nth_error_app_Some; eauto.
    }
  - subst.
    unfold instantiate_elems.
    apply Forall2_spec => //.
    move => n melem vs Hnth1 Hnth2.
    eapply those_map_lookup in Heleminit as [ei [Hmap Hnth]]; last by eauto.
    apply module_typecheck_elem_aux in Hmodcheck as [C Hmodcheck].
    unfold module_elem_type_checker in Hmodcheck.
    eapply all_projection in Hmodcheck; eauto.
    destruct melem.
    move/andP in Hmodcheck; destruct Hmodcheck as [Hmodcheck Hmode].
    move/andP in Hmodcheck; destruct Hmodcheck as [Hconstexpr Hbetype].
    simplify_multieq.
    apply Forall2_spec => //=.
    + apply those_length in Hmap.
      by rewrite List.length_map in Hmap; simpl in Hmap.
    + move => i bes vref Hnthinit Hnthei.
      eapply all_projection in Hbetype; eauto.
      eapply all_projection in Hconstexpr; eauto.
      eapply those_map_lookup in Hmap as [vref' [Hmap Hnth']]; eauto.
      move/b_e_type_checker_reflects_typing in Hbetype.
      eapply const_exprs_impl in Hconstexpr; last by eauto.
      destruct Hconstexpr as [e [-> Hconst]].
      unfold const_expr in Hconst.
      destruct e => //; subst; simpl in Hmap.
      { (* ref_null *)
        injection Hmap as <-.
        simpl in *.
        simplify_multieq.
        by constructor.
      }
      { (* ref_func *)
        remove_bools_options; simplify_multieq.
        constructor => /=.
        unfold interp_get_vref in Hmap.
        simpl in Hmap; remove_bools_options.
        by apply r_ref_func.
      }
      { (* global_get *)
        unfold interp_get_vref in Hmap; simpl in Hmap.
        remove_bools_options; simplify_multieq; destruct v => //.
        injection Hmap as ->.
        constructor.
        replace (vref_to_e vref') with (v_to_e (VAL_ref vref')) => //.
        eapply r_global_get => /=.
        unfold sglob_val, sglob, sglob_ind in *; simpl in *.
        remove_bools_options.
        lookup_N_to_nth_error.
        by erewrite nth_error_app_Some; eauto.
      }
Qed.

End Host.
