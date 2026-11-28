(** Several soundness properties of the relational instantiation. **)
(** Most notably, the post-instantiation store is a well-typed extension
    of the old store, and the generated module instance is well-typed in 
    that store. **)

From mathcomp Require Import ssreflect ssrbool eqtype seq ssrnat.
From Wasm Require Import instantiation_spec instantiation_properties type_preservation.
From Wasm Require Import gc_type_context_properties gc_declaration_typing_properties.
From Wasm Require Import extended_const.
From Wasm Require Import closed_initializer_properties.
From Wasm Require Import closed_instantiation_properties.
From Wasm Require Import gc_closed_runtime_properties.
From Wasm Require Import instantiation_code_typing closed_source_translation closed_context_properties.
From Stdlib Require Import ZArith.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.

(* Replacing the imported types by subtypes preserves the typing of a program *)
Lemma bet_import_subtyping: forall ts fts tts mts gts ets dts locs labs ret refs names imps1 imps2 bes tf,
    List.Forall2 import_subtyping imps2 imps1 ->
    be_typing (Build_t_context ts (ext_t_funcs imps1 ++ fts) (ext_t_tables imps1 ++ tts) (ext_t_mems imps1 ++ mts) (ext_t_globals imps1 ++ gts) ets dts locs labs ret refs names) bes tf ->
    be_typing (Build_t_context ts (ext_t_funcs imps2 ++ fts) (ext_t_tables imps2 ++ tts) (ext_t_mems imps2 ++ mts) (ext_t_globals imps2 ++ gts) ets dts locs labs ret refs names) bes tf.
Proof.
  move => ts fts tts mts gts ets dts locs labs ret refs names imps1 imps2 bes tf Hall2 Hbet.
  eapply context_agree_be_typing; eauto.
  unfold context_agree => /=.
  repeat rewrite eq_refl => /=.
  specialize (import_subtyping_comp_len Hall2) as [Hflen [Htlen [Hmlen Hglen]]].
  apply import_subtyping_components in Hall2 as [Hfsub [Htsub [Hmsub Hgsub]]].
  repeat rewrite length_is_size in Hflen.
  repeat rewrite length_is_size in Htlen.
  repeat rewrite length_is_size in Hmlen.
  repeat rewrite length_is_size in Hglen.
  repeat (apply/andP; split) => //; rewrite all2_cat => //; (apply/andP; split; last by apply reflexive_all2_same; move => ?; apply/eqP); apply all2_spec => //; move => n t1 t2 Hnth1 Hnth2.
  { eapply Forall2_lookup in Hfsub as [t [Hnth Hsub]]; eauto.
    by unfold import_func_subtyping in Hsub; remove_bools_options; simplify_multieq; subst; apply/eqP.
  }
  { eapply Forall2_lookup in Htsub as [t [Hnth Hsub]]; eauto.
    by unfold import_table_subtyping in Hsub; remove_bools_options; simplify_multieq; subst; apply/eqP.
  }
  { eapply Forall2_lookup in Hgsub as [t [Hnth Hsub]]; eauto.
    by unfold import_global_subtyping in Hsub; remove_bools_options; simplify_multieq; subst; apply/eqP.
  }
Qed.

Lemma bet_skip_refcheck: forall C C' bes tf,
  C' = upd_refs C (iota_N 0 (length C.(tc_funcs))) ->
  be_typing C bes tf ->
  be_typing C' bes tf.
Proof.
  move => C C' bes [tx ty] HC' Hbet.
  move: C' HC'.
  induction Hbet; move => C' HC'; subst C' => /=; (try by econstructor; eauto).
  (* ref_func *)
  - apply bet_ref_func with (t := t) => //=.
    + apply nth_error_Some_length in H.
      apply List.nth_error_In with (n := (N.to_nat x)).
      rewrite iota_N_lookup.
      by rewrite add0n Nnat.N2Nat.id.
    + by lias.
Qed.

(** Soundness of the module instantiation operation
The post-instantiation store is a valid extension of the old store,
and the post-instantiation frame is well-typed within the new store.
**)
Lemma instantiation_sound_with_code: forall (s: store_record) m v_imps s' f exps,
  store_typing s ->
  instantiate s m v_imps (s', f, exps) ->
  (store_typing s') /\
  (store_extension s s') /\
  (exists C, frame_typing s' f C) /\
  config_typing s' (f, to_e_list exps) nil.
Proof.
  move => s m v_imps s' f exps HST Hinst.
  unfold instantiate in Hinst.
  destruct Hinst as [t_imps_mod [t_imps [t_exps [hs' [inst [g_inits [r_inits
    [closed_expected [Hmodtype [Himptype [Hclosedimports [Hsubtype
      [Hallocmodule [Hinstglob [Hinstelem [Heqf Heqexps]]]]]]]]]]]]]]]].

  destruct (allocated_module_initializer_registration HST Hallocmodule)
    as [Hregistry Hregistered].

  unfold alloc_module in Hallocmodule.
  destruct Hallocmodule as [registry [typeids [source [closed_tables
    [closed_globals [closed_elements [Hclosed [Hidentity [Htypeids
      [Hsource [Hinstcontext [Htables [Hglobals [Helements Hallocmodule]]]]]]]]]]]]]].
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _ _) as [s4 igs] eqn:Hallocglobs.
  destruct (alloc_elems _ _ _) as [s5 ies] eqn:Hallocelems.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hallocdatas.

  remove_bools_options.

  apply alloc_func_iota_N in Hallocfuncs.
  apply alloc_table_iota_N in Halloctabs.
  apply alloc_mem_iota_N in Hallocmems.
  have Hgloblen : length g_inits = length closed_globals.
  { apply List.Forall2_length in Hinstglob.
    have Length := those_length Hglobals.
    rewrite !List.length_map in Length. by lias. }
  have Helemlen : length r_inits = length closed_elements.
  { apply List.Forall2_length in Hinstelem.
    have Length := those_length Helements.
    rewrite !List.length_map in Length. by lias. }
  apply alloc_global_iota_N in Hallocglobs; last exact Hgloblen.
  apply alloc_elem_iota_N in Hallocelems; last exact Helemlen.
  apply alloc_data_iota_N in Hallocdatas.

  (* Important to prove the goals first separately as there is some sort of dependency *)
  assert (store_extension s s') as Hstoreext.
  { 
    extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    unfold store_extension => /=.
    apply/andP; split; last first.
    { apply gc_type_context_properties.canonical_registry_prefixb_correct.
      apply gc_declaration_typing_properties.close_and_validate_type_groups_sound in Hclosed.
      destruct Hclosed as [_ Hclosed].
      by apply gc_type_context_properties.close_type_groups_extension_public in Hclosed. }
    erewrite component_extension_extend; eauto; last by apply all2_func_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_table_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_mem_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_global_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_elem_extension_same.
    erewrite component_extension_extend; eauto; last by apply all2_data_extension_same.
  }

  destruct Hmodtype as [Hdecl Hmodtype].
  destruct m; unfold module_components_typing in Hmodtype; simpl in *.
  destruct Hmodtype as [fts [tts [mts [gts [rts [dts [Hmtypes [Hmfunctype [Hmtabletype [Hmmemtype [Hmemcount [Hmglobaltype [Hmelemtype [Hmdatatype [Hstarttype [Hmimptype [Hmexptype Hexpunique]]]]]]]]]]]]]]]]].
  destruct Hmglobaltype as [Hgts Hprefix].
  assert (List.Forall2 (fun g gt => gt = g.(modglob_type)) mod_globals gts) as Hmglobaltype.
  { rewrite Hgts.
    apply Forall2_spec; first by rewrite List.length_map.
    move => n g gt Hg Hgt.
    erewrite List.map_nth_error in Hgt; last exact Hg.
    by injection Hgt.
  }
  match type of Hprefix with extended_globals_typing ?C0 _ => pose Csource := C0 end.
  change (extended_globals_typing Csource mod_globals) in Hprefix.
  set Cinit := initializer_type_names Csource typeids.
  have Rebased := initializer_globals_type_names typeids Hprefix.
  change (extended_globals_typing Cinit mod_globals) in Rebased.
  clear Hprefix. rename Rebased into Hprefix.
  set f_init := Build_frame nil inst.
  fold f_init in Hinstglob, Hinstelem.
  rewrite Htypeids in Hclosedimports.
  have ImportGlobals := closed_import_global_projection Hmimptype Hclosedimports.
  have ImportTables := closed_import_table_projection Hmimptype Hclosedimports.
  match type of Hmfunctype with
  | List.Forall2 (module_func_typing ?Full) _ _ => pose Cmodule := Full
  end.
  destruct (imported_function_context_closing (C := Cmodule) Hidentity Hmimptype)
    as [import_functions CloseImportFunctions].
  destruct (defined_function_context_closing (C := Cmodule) Hidentity Hmfunctype)
    as [defined_functions CloseDefinedFunctions].
  have TableTypes : tts = map modtab_type mod_tables.
  { apply List.nth_error_ext. move => n.
    destruct (List.nth_error mod_tables n) as [table|] eqn:Lookup.
    - destruct (Forall2_lookup Hmtabletype Lookup) as [declared [Slot Typed]].
      rewrite Slot nth_error_map' Lookup /=.
      unfold module_table_typing in Typed.
      move/andP: Typed => [_ /eqP ->]. reflexivity.
    - have Length := List.Forall2_length Hmtabletype.
      have Beyond : List.nth_error tts n = None.
      { apply List.nth_error_None. apply List.nth_error_None in Lookup. by lias. }
      by rewrite Beyond nth_error_map' Lookup. }
  have DeclaredTables := allocated_table_context_closing Htables.
  have FunctionsClosed := those_cat CloseImportFunctions CloseDefinedFunctions.
  have TablesClosed := those_cat ImportTables DeclaredTables.
  rewrite -TableTypes in TablesClosed.
  have ContextClosed : exists closed, close_t_context Cinit = Some closed.
  { unfold Cinit, initializer_type_names, Csource, close_t_context.
    cbn [tc_defined_types tc_funcs tc_tables tc_globals tc_elems tc_locals
      tc_labels tc_return tc_types tc_mems tc_datas tc_refs].
    rewrite !List.map_app FunctionsClosed TablesClosed ImportGlobals.
    by eexists. }
  destruct ContextClosed as [closed_init CloseInit].
  have RegistryWorld : s_types s' = registry.
  { by rewrite (proj1 Hallocmodule). }
  have IdentitiesLater :
      gc_declaration_typing.source_type_identitiesb (s_types s') typeids
        Cmodule.(tc_types) typeids.
  { rewrite RegistryWorld. exact Hidentity. }
  have ImportedFunctionViews := imported_function_views Hstoreext Hregistry
    IdentitiesLater Hmimptype Himptype Hsubtype Hclosedimports.
  assert (length (ext_t_globals t_imps_mod) = length (ext_globals v_imps)) as Himportslen.
  { specialize (vt_imps_comp_len Himptype) as [_ [_ [_ Hlen]]].
    have Projection := closed_import_global_projection Hmimptype Hclosedimports.
    have Length := those_length Projection.
    rewrite List.length_map in Length.
    specialize (closed_import_component_lengths Hsubtype) as [_ [_ [_ Hlen']]].
    by lias.
  }
  assert (forall n addr, List.nth_error f_init.(f_inst).(inst_funcs) n = Some addr ->
    (addr < N.of_nat (length s'.(s_funcs)))%N) as Hinitfunc.
  { unfold f_init.
    extract_premise.
    destruct inst, s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    move => n addr Hnth.
    rewrite List.length_app List.length_map.
    apply cat_lookup in Hnth as [Hnth | Hnth].
    - apply ext_funcs_lookup_exist in Hnth as [k Hnthaddr].
      eapply Forall2_nth_impl in Himptype as [et [Hnthext Hext]]; last by apply Hnthaddr.
       unfold external_typing, ext_typing, lookup_func_defined_type in Hext; simpl in Hext.
      remove_bools_options.
      unfold lookup_N in *.
       match goal with
       | Found : List.nth_error _ _ = Some _ |- _ =>
           apply nth_error_Some_length in Found
       end.
       by lias.
    - apply iota_N_lookup_Some in Hnth as [-> Hlength].
      by lias.
  }
  assert (forall idx v gt, sglob_val s' f_init.(f_inst) idx = Some v ->
    lookup_N Cinit.(tc_globals) idx = Some gt ->
    value_typing s' inst.(inst_defined_types) v gt.(tg_t)) as Hinitimport.
  { move => idx v gt Get Lookup.
    change (lookup_N (ext_t_globals t_imps_mod) idx = Some gt) in Lookup.
    destruct (those_map_lookup ImportGlobals Lookup) as [expected [Closed Slot]].
    have Value : closed_value_typing s' v expected.(tg_t).
    { eapply imported_global_value_typing with (s := s) (v_imps := v_imps)
        (t_imps := t_imps) (t_imps_mod := closed_expected)
        (added_globals := map (fun '(g, v) => gen_global_instance g v)
          (List.combine closed_globals g_inits))
        (added_addrs := iota_N (length s.(s_globals)) (length closed_globals));
        try eassumption.
    - rewrite global_instances_map.
      extract_premise.
      destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
      reflexivity.
    - unfold f_init.
      extract_premise.
      destruct inst, s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
      reflexivity. }
    unfold value_typing. rewrite Htypeids.
    destruct (close_global_type_agreement _ _ _ Closed)
      as [_ ValueClosed].
    by rewrite ValueClosed.
  }
  assert (forall j g v, List.nth_error mod_globals j = Some g ->
    List.nth_error g_inits j = Some v ->
    sglob_val s' f_init.(f_inst) (N.of_nat (length Cinit.(tc_globals) + j)) = Some v) as Hinitdefined.
  { move => j g v Hg Hv.
    change (sglob_val s' f_init.(f_inst)
      (N.of_nat (length (ext_t_globals t_imps_mod) + j)) = Some v).
     rewrite Himportslen.
     have SourceGlobal : List.nth_error (map modglob_type mod_globals) j =
         Some (modglob_type g) by rewrite nth_error_map' Hg.
     destruct (those_map_lookup Hglobals SourceGlobal)
       as [descriptor [Closed Slot]].
     eapply sglob_val_defined with (oldgs := s.(s_globals)) (imports := ext_globals v_imps)
      (gs := closed_globals) (vs := g_inits); eauto.
    - rewrite global_instances_map.
      extract_premise.
      destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
      reflexivity.
    - unfold f_init.
      extract_premise.
      destruct inst, s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
      reflexivity.
  }
  assert (List.Forall2 (fun g v =>
    value_typing s' inst.(inst_defined_types) v g.(modglob_type).(tg_t))
     mod_globals g_inits) as Hglobalvalues.
  { eapply global_init_values_typing with (C := Cinit) (f := f_init); eauto. }
  assert (forall idx v gt, sglob_val s' f_init.(f_inst) idx = Some v ->
    lookup_N (Cinit.(tc_globals) ++ gts) idx = Some gt ->
    value_typing s' inst.(inst_defined_types) v gt.(tg_t)) as Hinitall.
  { rewrite Hgts.
    by eapply global_init_context_typing; eauto.
  }
  have RegisteredNames := registered_type_names IdentitiesLater.
  have SourceGlobalValues : List.Forall2 (fun g v =>
      value_typing s' typeids v (tg_t (modglob_type g))) mod_globals g_inits.
  { by rewrite -Htypeids. }
  have ClosedGlobalValues := closed_global_initial_values SourceGlobalValues Hglobals.
  have NewGlobalsTyped := closed_global_instances_typed ClosedGlobalValues.
  have TablesValid : List.Forall tabletype_valid (map modtab_type mod_tables).
  { apply Forall_spec. move => n table Lookup.
    rewrite nth_error_map' in Lookup.
    destruct (List.nth_error mod_tables n) as [entry|] eqn:Entry; last discriminate.
    injection Lookup as <-.
    destruct (Forall2_lookup Hmtabletype Entry) as [declared [_ Typed]].
    by move/andP: Typed => [Valid _]. }
  have NewTablesTyped : List.Forall
      (fun ti => exists t, tableinst_typing s' ti = Some t)
      (map (fun '(t, ref) => gen_table_instance t ref) closed_tables).
  { eapply closed_table_instances_typed with (names := typeids); first exact TablesValid.
    rewrite RegistryWorld. exact Htables. }
  have ClosingGlobals : those (List.map
      (gc_declaration_typing.close_global_type (tc_defined_types Cinit)) gts) =
      Some closed_globals.
  { rewrite Hgts. exact Hglobals. }
  have CloseElementContext := close_initializer_globals CloseInit ClosingGlobals.
  have ElementValues : List.Forall2 (fun e refs =>
      List.Forall (fun ref => value_typing s' typeids (VAL_ref ref)
        (T_ref (modelem_type e))) refs) mod_elems r_inits.
  { apply Forall2_spec; first by apply List.Forall2_length in Hinstelem.
    move => n element refs Element References.
    destruct (Forall2_lookup Hmelemtype Element) as [source_type [TypeSlot Typed]].
    destruct (Forall2_lookup Hinstelem Element) as [values [ValueSlot Reductions]].
    rewrite References in ValueSlot. injection ValueSlot as <-.
    unfold module_elem_typing in Typed.
    destruct element as [reference initializers mode].
    destruct Typed as [Same [Initializers Mode]]. simpl in *. subst source_type.
    apply Forall_spec. move => j ref Reference.
    destruct (Forall2_nth_impl' Reductions Reference) as [bes [Expression Reduction]].
    destruct (Forall_lookup Initializers Expression) as [Constant Entry].
    rewrite -Htypeids.
    change (value_typing s' (inst_defined_types (f_inst f_init)) (VAL_ref ref)
      (T_ref reference)).
    eapply extended_init_value_typing with
      (C := const_context_add_globals Cinit gts) (f := f_init);
      try eassumption.
    - change (be_typing
        (initializer_type_names (const_context_add_globals Csource gts) typeids)
        bes (Tf nil [::T_ref reference])).
      by apply initializer_source_type_names.
    - symmetry. exact Htypeids.
  }
  have NewElementsTyped := closed_element_instances_typed RegisteredNames ElementValues Helements.
  have AllocationWorld :
      s_funcs s' = s_funcs s ++ map (fun code => gen_func_instance code inst) mod_funcs /\
      s_tables s' = s_tables s ++ map (fun '(t, ref) => gen_table_instance t ref) closed_tables /\
      s_mems s' = s_mems s ++ map gen_mem_instance (map modmem_type mod_mems) /\
      s_globals s' = s_globals s ++
        map (fun '(t, v) => gen_global_instance t v) (List.combine closed_globals g_inits) /\
      s_elems s' = s_elems s ++
        map (fun '(t, refs) => Build_eleminst t refs) (List.combine closed_elements r_inits) /\
      s_datas s' = s_datas s ++ map (fun d => Build_datainst (moddata_init d)) mod_datas /\
      inst_funcs inst = ext_funcs v_imps ++ iota_N (length (s_funcs s)) (length mod_funcs) /\
      inst_tables inst = ext_tables v_imps ++ iota_N (length (s_tables s)) (length closed_tables) /\
      inst_mems inst = ext_mems v_imps ++ iota_N (length (s_mems s)) (length mod_mems) /\
      inst_globals inst = ext_globals v_imps ++ iota_N (length (s_globals s)) (length closed_globals) /\
      inst_elems inst = iota_N (length (s_elems s)) (length closed_elements) /\
      inst_datas inst = iota_N (length (s_datas s)) (length mod_datas).
  { extract_premise.
    destruct s, s1, s2, s3, s4, s5, s6; simpl in *; subst.
    repeat split; try reflexivity; try assumption.
    by rewrite List.length_map in Hconjl3.
  }
  destruct AllocationWorld as [FunctionWorld [TableWorld [MemoryWorld [GlobalWorld
    [ElementWorld [DataWorld [FunctionAddresses [TableAddresses [MemoryAddresses
      [GlobalAddresses [ElementAddresses DataAddresses]]]]]]]]]]].
  have SourceImports := source_import_signatures Hmimptype.
  change (those (map (source_import_signature (List.concat mod_types)) mod_imports) =
    Some t_imps_mod) in SourceImports.
  unfold source_import_signature in SourceImports.
  have SourceFunctions := source_function_signatures Hmfunctype.
  change (those (map (fun code => lookup_function_type (List.concat mod_types)
    (modfunc_type code)) mod_funcs) = Some fts) in SourceFunctions.
  have ValidatedSource := Hsource.
  unfold module_source_context in Hsource. simpl in Hsource.
  rewrite SourceImports SourceFunctions in Hsource.
  injection Hsource as SourceShape.
  have ElementTypes : rts = map modelem_type mod_elems.
  { apply List.nth_error_ext. move => n.
    destruct (List.nth_error mod_elems n) as [element|] eqn:Element.
    - destruct (Forall2_lookup Hmelemtype Element) as [reference [Slot Typed]].
      rewrite Slot nth_error_map' Element /=.
      destruct element. destruct Typed as [-> _]. reflexivity.
    - have Length := List.Forall2_length Hmelemtype.
      have Beyond : List.nth_error rts n = None.
      { apply List.nth_error_None. apply List.nth_error_None in Element. by lias. }
      by rewrite Beyond nth_error_map' Element. }
  have ImportedTableViews := imported_table_views Hstoreext Hregistry
    IdentitiesLater Hmimptype Himptype Hsubtype Hclosedimports.
  have ImportedGlobalViews := imported_global_views Hstoreext Hregistry
    IdentitiesLater Hmimptype Himptype Hsubtype Hclosedimports.
  have InstTypes := proj1 (proj2 Hallocmodule).
  have NewFunctionViews : all2 (instance_function_view s' typeids)
      (iota_N (length (s_funcs s)) (length mod_funcs)) fts.
  { rewrite -(List.length_map (fun code => gen_func_instance code inst) mod_funcs).
    apply appended_instance_views.
    apply Forall2_spec; first by rewrite List.length_map; apply List.Forall2_length in Hmfunctype.
    move => n native signature Native Signature address Lookup.
    rewrite nth_error_map' in Native.
    destruct (List.nth_error mod_funcs n) as [code|] eqn:Code; last discriminate.
    injection Native as <-.
    destruct (Forall2_lookup Hmfunctype Code) as [declared [Declared Typed]].
    rewrite Signature in Declared. injection Declared as <-.
    rewrite -Htypeids.
    eapply allocated_native_function_view with (code := code) (inst := inst).
    - exact Hregistry.
    - by rewrite Htypeids InstTypes.
    - unfold module_func_typing in Typed.
      destruct code, signature. destruct Typed as [Function _].
       rewrite InstTypes. exact Function.
    - by rewrite FunctionWorld. }
  have NewTableViews : all2 (instance_table_view s' typeids)
      (iota_N (length (s_tables s)) (length closed_tables)) tts.
  { rewrite -(List.length_map (fun '(t, ref) => gen_table_instance t ref) closed_tables).
    apply appended_instance_views.
    apply Forall2_spec.
    - have Length := those_length Htables.
      rewrite !List.length_map in Length.
      rewrite List.length_map TableTypes List.length_map. by lias.
    - move => n table source_table Table Source address Lookup.
      rewrite TableTypes nth_error_map' in Source.
      destruct (List.nth_error mod_tables n) as [source_entry|] eqn:SourceEntry;
        last discriminate.
      injection Source as <-.
      have SourceType : List.nth_error (map modtab_type mod_tables) n =
          Some (modtab_type source_entry) by rewrite nth_error_map' SourceEntry.
      destruct (those_map_lookup Htables SourceType)
        as [[descriptor initial] [Closed Slot]].
      rewrite nth_error_map' Slot /= in Table. injection Table as <-.
      have Descriptor : gc_declaration_typing.close_table_type typeids
          (modtab_type source_entry) = Some descriptor.
      { unfold close_table_initial in Closed.
        destruct (gc_declaration_typing.close_table_type typeids
          (modtab_type source_entry)) as [actual|] eqn:Actual; last discriminate.
        destruct (gc_declaration_typing.lower_closed_null registry
          (closed_ref_heap (tt_elem_type actual))); last discriminate.
        by injection Closed as <- _. }
      eapply defined_table_view; try eassumption.
      + unfold ext_table_typing. rewrite TableWorld Lookup.
        by destruct descriptor as [[minimum maximum] reference].
      + exact (registered_closed_table_valid RegisteredNames Descriptor). }
  have NewGlobalViews : all2 (instance_global_view s' typeids)
      (iota_N (length (s_globals s)) (length closed_globals)) gts.
  { have Length : length (map (fun '(t, v) => gen_global_instance t v)
        (List.combine closed_globals g_inits)) = length closed_globals.
    { by rewrite List.length_map List.length_combine Hgloblen Nat.min_id. }
    rewrite -Length. apply appended_instance_views.
    apply Forall2_spec.
    - have ClosedLength := those_length Hglobals.
      rewrite !List.length_map in ClosedLength.
      rewrite Length Hgts List.length_map. by lias.
    - move => n global source_global Global Source address Lookup.
      have Closing : those (map (gc_declaration_typing.close_global_type typeids) gts) =
          Some closed_globals by rewrite Hgts.
      destruct (those_map_lookup Closing Source) as [descriptor [Closed Slot]].
      rewrite nth_error_map' in Global.
      destruct (List.nth_error (List.combine closed_globals g_inits) n)
        as [[actual value]|] eqn:Pair; last discriminate.
      injection Global as <-.
      destruct (combine_lookup Pair) as [Actual Value].
      rewrite Slot in Actual. injection Actual as <-.
      eapply defined_global_view; try eassumption.
      + unfold ext_global_typing. rewrite GlobalWorld Lookup. reflexivity.
      + exact (registered_closed_global_valid RegisteredNames Closed). }
  have NewElementViews : all2 (instance_element_view s' typeids)
      (iota_N (length (s_elems s)) (length closed_elements)) rts.
  { have Length : length (map (fun '(t, refs) => Build_eleminst t refs)
        (List.combine closed_elements r_inits)) = length closed_elements.
    { by rewrite List.length_map List.length_combine Helemlen Nat.min_id. }
    rewrite -Length. apply appended_instance_views.
    apply Forall2_spec.
    - have ClosedLength := those_length Helements.
      rewrite !List.length_map in ClosedLength.
      rewrite Length ElementTypes List.length_map. by lias.
    - move => n element source_reference Element Source address Lookup.
      have Closing : those (map (gc_declaration_typing.close_reference_type typeids) rts) =
          Some closed_elements by rewrite ElementTypes.
      destruct (those_map_lookup Closing Source) as [descriptor [Closed Slot]].
      rewrite nth_error_map' in Element.
      destruct (List.nth_error (List.combine closed_elements r_inits) n)
        as [[actual refs]|] eqn:Pair; last discriminate.
      injection Element as <-.
      destruct (combine_lookup Pair) as [Actual Refs].
      rewrite Slot in Actual. injection Actual as <-.
      have Stored : List.nth_error
          (map (fun '(t, refs) => Build_eleminst t refs)
            (List.combine closed_elements r_inits)) n =
          Some (Build_eleminst descriptor refs) by rewrite nth_error_map' Pair.
      destruct (Forall_lookup NewElementsTyped Stored) as [typed Typed].
      have DescriptorType : typed = descriptor.
      { unfold eleminst_typing in Typed.
        destruct (_ && _) eqn:Accepted; last discriminate.
        by injection Typed. }
      subst typed.
      eapply defined_element_view; try eassumption.
      by rewrite ElementWorld. }
  have FunctionViews : all2 (instance_function_view s' typeids)
      (inst_funcs inst) (ext_t_funcs t_imps_mod ++ fts).
  { rewrite FunctionAddresses all2_cat; first by rewrite ImportedFunctionViews NewFunctionViews.
    exact (all2_size ImportedFunctionViews). }
  have TableViews : all2 (instance_table_view s' typeids)
      (inst_tables inst) (ext_t_tables t_imps_mod ++ tts).
  { rewrite TableAddresses all2_cat; first by rewrite ImportedTableViews NewTableViews.
    exact (all2_size ImportedTableViews). }
  have GlobalViews : all2 (instance_global_view s' typeids)
      (inst_globals inst) (ext_t_globals t_imps_mod ++ gts).
  { rewrite GlobalAddresses all2_cat; first by rewrite ImportedGlobalViews NewGlobalViews.
    exact (all2_size ImportedGlobalViews). }
  have ElementViews : all2 (instance_element_view s' typeids)
      (inst_elems inst) rts by rewrite ElementAddresses.
  have MemoryTypes : mts = map modmem_type mod_mems.
  { apply List.nth_error_ext. move => n.
    destruct (List.nth_error mod_mems n) as [memory_entry|] eqn:Memory.
    - destruct (Forall2_lookup Hmmemtype Memory) as [declared [Slot Typed]].
      rewrite Slot nth_error_map' Memory /=.
      unfold module_mem_typing in Typed.
      move/andP: Typed => [_ /eqP ->]. reflexivity.
    - have Length := List.Forall2_length Hmmemtype.
      have Beyond : List.nth_error mts n = None.
      { apply List.nth_error_None. apply List.nth_error_None in Memory. by lias. }
      by rewrite Beyond nth_error_map' Memory. }
  have ImportedMemories : those (map (ext_mem_typing s') (ext_mems v_imps)) =
      Some (closed_ext_t_mems t_imps).
  { apply those_spec.
    - rewrite List.length_map.
      exact (proj1 (proj2 (proj2 (vt_imps_comp_len Himptype)))).
    - move => n descriptor Source.
      destruct (vt_imps_mems_lookup Himptype Source)
        as [j [address [Address [ValueType TypeSlot]]]].
      destruct (Forall2_lookup Himptype ValueType) as [actual [Actual Typed]].
      rewrite TypeSlot in Actual. injection Actual as <-.
      unfold external_typing, ext_typing, ext_mem_typing in Typed.
      destruct (lookup_N (s_mems s) address) as [memory_entry|] eqn:Memory;
        last discriminate.
      injection Typed as <-.
      rewrite nth_error_map' Address /=.
      unfold ext_mem_typing. rewrite MemoryWorld.
      unfold lookup_N in Memory |- *.
      rewrite List.nth_error_app1; [by rewrite Memory|].
      by apply nth_error_Some_length in Memory. }
  have DefinedMemories : those (map (ext_mem_typing s')
      (iota_N (length (s_mems s)) (length mod_mems))) = Some mts.
  { have MemoryComponents := appended_component_types (s_mems s)
      (map gen_mem_instance (map modmem_type mod_mems)) meminst_type.
    rewrite !List.length_map in MemoryComponents.
    have Types : map meminst_type (map gen_mem_instance (map modmem_type mod_mems)) =
        map modmem_type mod_mems.
    { rewrite -!map_comp. apply eq_map.
      move => entry /=. unfold gen_mem_instance.
      by destruct (modmem_type entry). }
    rewrite Types -MemoryTypes in MemoryComponents.
    unfold ext_mem_typing. rewrite MemoryWorld.
    change (those (map (fun address => option_map meminst_type
      (lookup_N (s_mems s ++ map gen_mem_instance (map modmem_type mod_mems)) address))
      (iota_N (length (s_mems s)) (length mod_mems))) = Some mts).
    rewrite MemoryTypes. rewrite MemoryTypes in MemoryComponents.
    exact MemoryComponents. }
  have MemViews : those (map (ext_mem_typing s') (inst_mems inst)) =
      Some (closed_ext_t_mems t_imps ++ mts).
  { rewrite MemoryAddresses map_cat. by apply those_cat. }
  have DataViews : those (map (fun address =>
      match lookup_N (s_datas s') address with
      | Some data => datainst_typing s' data | None => None end) (inst_datas inst)) = Some dts.
  { rewrite DataAddresses. apply those_spec.
    - rewrite List.length_map iota_N_length.
      exact (List.Forall2_length Hmdatatype).
    - move => n descriptor Descriptor.
      destruct descriptor.
      have Length := List.Forall2_length Hmdatatype.
      have Bound : n < length mod_datas.
      { apply nth_error_Some_length in Descriptor. by lias. }
      rewrite nth_error_map' iota_N_lookup; last exact Bound.
      cbn [option_map]. rewrite DataWorld.
      unfold lookup_N. rewrite Nnat.Nat2N.id List.nth_error_app2; last by lias.
      replace (length (s_datas s) + n - length (s_datas s))%coq_nat with n; last by lias.
      rewrite nth_error_map'.
      destruct (List.nth_error mod_datas n) as [entry|] eqn:Entry; first reflexivity.
      apply List.nth_error_None in Entry. by lias. }
  have MemoryImportCount : length (closed_ext_t_mems t_imps) =
      length (ext_t_mems t_imps_mod).
  { have Projection := closed_import_memory_projection Hmimptype Hclosedimports.
    destruct (closed_import_component_lengths Hsubtype) as [_ [_ [Length _]]].
    by rewrite Projection in Length. }
  have FunctionCount : length (inst_funcs inst) =
      length (ext_t_funcs t_imps_mod ++ fts).
  { have Count := all2_size FunctionViews. by rewrite -!length_is_size in Count. }
  have RuntimeDefaults : forall n code, List.nth_error mod_funcs n = Some code ->
      runtime_default_vals (s_types s') typeids (modfunc_locals code) <> None.
  { move => n code Code.
    destruct Hdecl as [source_registry [source_names [Closing [Identity Runtime]]]].
    unfold module_runtime_types_closedb in Runtime.
    rewrite ValidatedSource in Runtime.
    move/andP: Runtime => [_ Defaults].
    have Default := all_projection Defaults Code.
    move/eqP: Default => Default.
    have OldIdentities := Identity.
    apply source_type_identitiesb_correct in OldIdentities.
    have NewIdentities := IdentitiesLater.
    apply source_type_identitiesb_correct in NewIdentities.
    have OldLength := List.Forall2_length OldIdentities.
    have NewLength := List.Forall2_length NewIdentities.
    have NamesLength : length source_names = length typeids by simpl in NewLength; lias.
    eapply runtime_default_vals_portable; eauto. }

  remember (Build_t_context (List.concat mod_types)
    (ext_t_funcs t_imps_mod ++ fts) (ext_t_tables t_imps_mod ++ tts)
    (closed_ext_t_mems t_imps ++ mts) (ext_t_globals t_imps_mod ++ gts)
    rts dts nil nil None (iota_N 0 (length inst.(inst_funcs))) typeids : t_context) as C.

  assert (inst_typing s' f.(f_inst) = Some C) as HIT.
  { unfold inst_typing.
    rewrite Heqf /= Hinstcontext -SourceShape Htypeids InstTypes.
    cbn [tc_funcs tc_tables tc_globals tc_elems].
    rewrite -TableTypes -Hgts -ElementTypes.
    have SourcesValid : all source_subtype_valid (List.concat mod_types) = true.
    { apply/allP. move => entry Member. apply source_subtype_valid_true. }
    have Identities : gc_declaration_typing.source_type_identitiesb
        (s_types s') typeids (List.concat mod_types) typeids.
    { by rewrite RegistryWorld. }
    rewrite SourcesValid Identities FunctionViews TableViews GlobalViews ElementViews /=.
    rewrite MemViews DataViews. subst C. reflexivity.
  }
  have InstanceTyped := HIT.
  rewrite Heqf /= in InstanceTyped.
  have NewFunctionsTyped : List.Forall
      (fun native => exists signature, funcinst_typing s' native signature)
      (map (fun code => gen_func_instance code inst) mod_funcs).
  { apply Forall_spec. move => n native Native.
    rewrite nth_error_map' in Native.
    destruct (List.nth_error mod_funcs n) as [code|] eqn:Code; last discriminate.
    injection Native as <-.
    destruct (Forall2_lookup Hmfunctype Code) as [signature [Signature Typed]].
    have Defaults := RuntimeDefaults n code Code.
    destruct code as [index locals body], signature as [args results].
    cbn [module_func_typing] in Typed.
    destruct Typed as [Function [Body SourceDefaults]].
    exists (Tf args results).
    unfold gen_func_instance. simpl. rewrite InstTypes Function.
    unfold funcinst_typing. simpl. split; first reflexivity.
    split; first reflexivity. rewrite InstanceTyped. split.
    - unfold func_typing.
      rewrite HeqC /= Function. split; first reflexivity.
      split; last exact SourceDefaults.
      have Rebased := initializer_source_type_names typeids Body.
      have Unlimited : be_typing
          (upd_refs
            (initializer_type_names
              (upd_local_label_return Cmodule (args ++ locals) [::results] (Some results))
              typeids)
            (iota_N 0 (length (tc_funcs Cmodule))))
          body (Tf nil results).
      { eapply bet_skip_refcheck with
          (C := initializer_type_names
            (upd_local_label_return Cmodule (args ++ locals) [::results] (Some results))
            typeids); first reflexivity.
        exact Rebased. }
      have MemoryLength :
          size (closed_ext_t_mems t_imps ++ mts) =
          size (tc_mems
            (upd_refs
              (initializer_type_names
                (upd_local_label_return Cmodule (args ++ locals) [::results] (Some results))
                typeids)
              (iota_N 0 (length (tc_funcs Cmodule))))).
      { change (size (closed_ext_t_mems t_imps ++ mts) =
          size (ext_t_mems t_imps_mod ++ mts)).
        by rewrite !size_cat -!length_is_size MemoryImportCount. }
      have Relimited := source_context_memories_typing MemoryLength Unlimited.
      rewrite FunctionCount. exact Relimited.
    - by rewrite Htypeids. }


  have NewMemoriesTyped : List.Forall
      (fun memory => exists t, meminst_typing s' memory = Some t)
      (map gen_mem_instance (map modmem_type mod_mems)).
  { apply Forall_spec. move => n memory_entry Entry.
    rewrite !nth_error_map' in Entry.
    destruct (List.nth_error mod_mems n) as [source_entry|] eqn:SourceEntry;
      last discriminate.
    injection Entry as <-.
    destruct (Forall2_lookup Hmmemtype SourceEntry) as [declared [_ Typed]].
    unfold module_mem_typing in Typed. move/andP: Typed => [Valid _].
    exists (modmem_type source_entry).
    unfold meminst_typing, gen_mem_instance, mem_length. simpl.
    rewrite Valid mem_make_length.
    have Bound : (page_size * lim_min (modmem_type source_entry) <= byte_limit)%N.
    { unfold memtype_valid, limit_valid_range in Valid.
      move/andP: Valid => [Valid _].
      unfold mem_limit_bound in Valid.
      unfold byte_limit, page_size, page_limit. by lias. }
    rewrite N.min_l; last exact Bound.
    rewrite N.mul_comm eq_refl. reflexivity. }
  have OldComponents :
      List.Forall (fun x => exists t, funcinst_typing s x t) (s_funcs s) /\
      List.Forall (fun x => exists t, tableinst_typing s x = Some t) (s_tables s) /\
      List.Forall (fun x => exists t, meminst_typing s x = Some t) (s_mems s) /\
      List.Forall (fun x => exists t, globalinst_typing s x = Some t) (s_globals s) /\
      List.Forall (fun x => exists t, eleminst_typing s x = Some t) (s_elems s) /\
      List.Forall (fun x => exists t, datainst_typing s x = Some t) (s_datas s).
  { destruct s. exact (proj2 HST). }
  destruct OldComponents as [OldFunctions [OldTables [OldMemories
    [OldGlobals [OldElements OldData]]]]].
  have TypedFunctions : List.Forall (fun x => exists t, funcinst_typing s' x t) (s_funcs s').
  { rewrite FunctionWorld List.Forall_app. split; last exact NewFunctionsTyped.
    by eapply store_extension_funcs_typing; eauto. }
  have TypedTables : List.Forall (fun x => exists t, tableinst_typing s' x = Some t) (s_tables s').
  { rewrite TableWorld List.Forall_app. split; last exact NewTablesTyped.
    by eapply store_extension_tables_typing; eauto. }
  have TypedMemories : List.Forall (fun x => exists t, meminst_typing s' x = Some t) (s_mems s').
  { rewrite MemoryWorld List.Forall_app. split; last exact NewMemoriesTyped.
    by eapply store_extension_mems_typing; eauto. }
  have TypedGlobals : List.Forall (fun x => exists t, globalinst_typing s' x = Some t) (s_globals s').
  { rewrite GlobalWorld List.Forall_app. split; last exact NewGlobalsTyped.
    by eapply store_extension_globals_typing; eauto. }
  have TypedElements : List.Forall (fun x => exists t, eleminst_typing s' x = Some t) (s_elems s').
  { rewrite ElementWorld List.Forall_app. split; last exact NewElementsTyped.
    by eapply store_extension_elems_typing; eauto. }
  have TypedData : List.Forall (fun x => exists t, datainst_typing s' x = Some t) (s_datas s').
  { rewrite DataWorld List.Forall_app. split.
    - by eapply store_extension_datas_typing; eauto.
    - apply Forall_spec. move => n data Data. by exists tt. }
  assert (store_typing s') as HST'.
  { split.
    - by apply canonical_registry_validb_correct.
    - destruct s'. by repeat split. }
  have PendingSource : be_typing Cmodule
      (get_init_expr_elems mod_elems ++ get_init_expr_datas mod_datas ++
        get_init_expr_start mod_start) (Tf nil nil).
  { eapply pending_initialization_code_typing with
      (Cinit := const_context_add_globals Csource gts); try reflexivity; try eassumption.
    change (size (ext_t_mems t_imps_mod ++ mts) <= 1).
    rewrite size_cat -!length_is_size MemoryTypes List.length_map addnC.
    exact Hmemcount. }
  have PendingTyped : be_typing C exps (Tf nil nil).
  { rewrite Heqexps.
    have Rebased := initializer_source_type_names typeids PendingSource.
    have Unlimited : be_typing
        (upd_refs (initializer_type_names Cmodule typeids)
          (iota_N 0 (length (tc_funcs Cmodule))))
        (get_init_expr_elems mod_elems ++ get_init_expr_datas mod_datas ++
          get_init_expr_start mod_start) (Tf nil nil).
    { eapply bet_skip_refcheck with (C := initializer_type_names Cmodule typeids);
        first reflexivity. exact Rebased. }
    have MemoryLength :
        size (closed_ext_t_mems t_imps ++ mts) =
        size (tc_mems (upd_refs (initializer_type_names Cmodule typeids)
          (iota_N 0 (length (tc_funcs Cmodule))))).
    { change (size (closed_ext_t_mems t_imps ++ mts) =
        size (ext_t_mems t_imps_mod ++ mts)).
      by rewrite !size_cat -!length_is_size MemoryImportCount. }
    have Relimited := source_context_memories_typing MemoryLength Unlimited.
    rewrite HeqC /= FunctionCount. exact Relimited. }
  have FullGlobalsClosed := those_cat ImportGlobals ClosingGlobals.
  have FullElementsClosed : those (List.map
      (gc_declaration_typing.close_reference_type typeids) rts) = Some closed_elements.
  { rewrite ElementTypes. exact Helements. }
  have ClosedContext : exists closed, close_t_context C = Some closed.
  { rewrite HeqC. unfold close_t_context.
    cbn [tc_defined_types tc_funcs tc_tables tc_globals tc_elems tc_locals
      tc_labels tc_return tc_types tc_mems tc_datas tc_refs].
    rewrite !List.map_app FunctionsClosed TablesClosed FullGlobalsClosed FullElementsClosed.
    by eexists. }
  destruct ClosedContext as [closed CloseC].
  have Frame : frame_typing s' f C.
  { unfold frame_typing. rewrite HIT. exists nil. rewrite Heqf HeqC. by split. }
  have ClosedFrame : closed_frame_typing s' f closed.
  { exists C, closed, nil. split; first exact HIT.
    split; first exact CloseC. split.
    - by destruct closed.
    - by rewrite Heqf. }
  have Return : upd_return closed None = closed.
  { have Metadata := closing_context_return_values _ _ CloseC.
    rewrite HeqC /= in Metadata.
    destruct closed. simpl in Metadata. subst. reflexivity. }
  have Admin := source_structural_entry s' C closed _ _ PendingTyped CloseC.
  split; first exact HST'.
  split; first exact Hstoreext.
  split; first by exists C.
  split; first exact HST'.
  eapply mk_thread_typing with (C := closed) (C' := closed).
  - exact ClosedFrame.
  - by rewrite Return.
  - exact Admin.
Qed.

Lemma instantiation_sound: forall (s: store_record) m v_imps s' f exps,
  store_typing s ->
  instantiate s m v_imps (s', f, exps) ->
  store_typing s' /\ store_extension s s' /\ exists C, frame_typing s' f C.
Proof.
  move => s m v_imps s' f exps Store Instantiated.
  destruct (instantiation_sound_with_code Store Instantiated)
    as [Typed [Extension [Frame Code]]].
  auto.
Qed.

Lemma instantiation_sound_configuration s m v_imps s' f exps :
  store_typing s ->
  instantiate s m v_imps (s', f, exps) ->
  config_typing s' (f, to_e_list exps) nil /\ store_extension s s'.
Proof.
  move => Store Instantiated.
  destruct (instantiation_sound_with_code Store Instantiated)
    as [Typed [Extension [Frame Code]]].
  auto.
Qed.
  
End Host.
