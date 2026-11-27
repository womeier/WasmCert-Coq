(** Completeness of executable module validation. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func instantiation_properties
  interp_instantiate_sound type_checker_reflects_typing extended_const.
From Stdlib Require Import String.

Set SsrOldRewriteGoalsOrder.
Local Opaque type_checker.b_e_type_checker.

Section Host.
Context `{ho : host}.

Lemma module_func_type_checker_complete c mf tf :
  c.(tc_locals) = nil ->
  c.(tc_labels) = nil ->
  module_func_typing c mf tf -> module_func_type_checker c mf.
Proof.
  move => Hlocals Hlabels.
  destruct c; simpl in *; subst.
  destruct mf as [idx locals body], tf as [params results].
  rewrite /module_func_typing /module_func_type_checker /=.
  move => [Hlookup [Htype Hdefaults]].
  rewrite Hlookup.
  apply/andP; split.
  - by apply/b_e_type_checker_reflects_typing.
  - by apply/eqP.
Qed.

Lemma module_elem_type_checker_complete c e t :
  module_elem_typing c e t -> module_elem_type_checker c e.
Proof.
  destruct e as [rt inits mode].
  rewrite /module_elem_typing /module_elem_type_checker /=.
  move => [-> [Hinits Hmode]].
  apply/andP; split.
  - apply/andP; split; apply Forall_all.
    + eapply List.Forall_impl; last exact Hinits.
      by move => es [Hconst Htype].
    + eapply List.Forall_impl; last exact Hinits.
      move => es [Hconst Htype].
      by apply/b_e_type_checker_reflects_typing.
  - unfold elemmode_valid in Hmode.
    unfold module_elem_mode_checker.
    destruct mode => //.
    destruct Hmode as [[limits elem] [Hlookup [Hrt [Htype Hconst]]]].
    rewrite Hlookup -Hrt eq_refl Hconst andbT.
    by apply/b_e_type_checker_reflects_typing.
Qed.

Lemma module_data_type_checker_complete c d t :
  module_data_typing c d t -> module_data_type_checker c d.
Proof.
  destruct d as [bytes mode].
  rewrite /module_data_typing /module_data_type_checker /datamode_valid
    /module_data_mode_checker /=.
  destruct mode => //.
  move => [[mem [Hlookup [Htype Hconst]]] _].
  rewrite Hlookup Hconst andbT.
  by apply/b_e_type_checker_reflects_typing.
Qed.

Lemma gather_m_f_types_complete c fs fts :
  List.Forall2 (module_func_typing c) fs fts ->
  gather_m_f_types c.(tc_types) fs = Some fts.
Proof.
  move => Htypes.
  unfold gather_m_f_types.
  apply those_spec.
  - rewrite List.length_map.
    by apply List.Forall2_length in Htypes.
  - move => n ft Hnth.
    rewrite nth_error_map'.
    eapply Forall2_nth_impl' in Htypes as [mf [Hmf Htype]]; eauto.
    rewrite Hmf /=.
    destruct mf, ft.
    destruct Htype as [Hlookup _].
    by rewrite /gather_m_f_type /= Hlookup.
Qed.

Lemma gather_m_e_types_complete c els rts :
  List.Forall2 (module_elem_typing c) els rts ->
  gather_m_e_types c.(tc_tables) els = Some rts.
Proof.
  move => Htypes.
  unfold gather_m_e_types.
  apply those_spec.
  - rewrite List.length_map.
    by apply List.Forall2_length in Htypes.
  - move => n rt Hnth.
    rewrite nth_error_map'.
    eapply Forall2_nth_impl' in Htypes as [el [Hel Htype]]; eauto.
    rewrite Hel /=.
    destruct el as [t inits mode].
    destruct Htype as [-> [Hinits Hmode]].
    unfold gather_m_e_type => /=.
    destruct mode => //.
    destruct Hmode as [[limits elem] [Hlookup [Hrt _]]].
    by rewrite Hlookup /= Hrt eq_refl.
Qed.

Lemma gather_m_d_types_complete c ds dts :
  List.Forall2 (module_data_typing c) ds dts ->
  gather_m_d_types c.(tc_mems) ds = Some dts.
Proof.
  move => Htypes.
  unfold gather_m_d_types.
  apply those_spec.
  - rewrite List.length_map.
    by apply List.Forall2_length in Htypes.
  - move => n t Hnth.
    rewrite nth_error_map'.
    eapply Forall2_nth_impl' in Htypes as [d [Hd Htype]]; eauto.
    rewrite Hd /=.
    destruct d as [bytes mode].
    destruct Htype as [Hmode ->].
    unfold gather_m_d_type => /=.
    destruct mode => //.
    destruct Hmode as [mem [Hlookup _]].
    by rewrite Hlookup.
Qed.

Lemma module_import_typer_complete c imp t :
  module_import_typing c imp t ->
  module_import_desc_typer c.(tc_types) imp.(imp_desc) = Some t.
Proof.
  destruct imp as [modname item desc].
  rewrite /module_import_typing /module_import_desc_typing /module_import_desc_typer /=.
  destruct desc => /=.
  - by move/eqP.
  - move/andP => [Hvalid /eqP Heq].
    by rewrite Hvalid Heq.
  - move/andP => [Hvalid /eqP Heq].
    by rewrite Hvalid Heq.
  - by move/eqP => ->.
Qed.

Lemma module_imports_typer_complete c imps impts :
  List.Forall2 (module_import_typing c) imps impts ->
  module_imports_typer c.(tc_types) imps = Some impts.
Proof.
  move => Htypes.
  unfold module_imports_typer.
  apply those_spec.
  - rewrite List.length_map.
    by apply List.Forall2_length in Htypes.
  - move => n t Hnth.
    rewrite nth_error_map'.
    eapply Forall2_nth_impl' in Htypes as [imp [Himp Htype]]; eauto.
    rewrite Himp /=.
    by rewrite (module_import_typer_complete _ _ _ Htype).
Qed.

Lemma module_export_typer_complete c exp t :
  module_export_typing c exp t ->
  module_export_typer c exp.(modexp_desc) = Some t.
Proof.
  destruct exp as [name desc].
  rewrite /module_export_typing /module_export_desc_typing /module_export_typer /=.
  destruct desc, t => //=.
  all: destruct (lookup_N _ _) eqn:Hlookup => //=;
    by move/eqP => <-.
Qed.

Lemma module_exports_typer_complete c exps expts :
  List.Forall2 (module_export_typing c) exps expts ->
  module_exports_typer c exps = Some expts.
Proof.
  move => Htypes.
  unfold module_exports_typer.
  apply those_spec.
  - rewrite List.length_map.
    by apply List.Forall2_length in Htypes.
  - move => n t Hnth.
    rewrite nth_error_map'.
    eapply Forall2_nth_impl' in Htypes as [exp [Hexp Htype]]; eauto.
    rewrite Hexp /=.
    by rewrite (module_export_typer_complete _ _ _ Htype).
Qed.

Lemma module_table_types_complete c tabs tts :
  List.Forall2 (module_table_typing c) tabs tts ->
  tts = map modtab_type tabs.
Proof.
  move => Htypes; induction Htypes => //=.
  move/andP: H => [_ /eqP ->].
  by rewrite IHHtypes.
Qed.

Lemma module_mem_types_complete c mems mts :
  List.Forall2 (module_mem_typing c) mems mts ->
  mts = map modmem_type mems.
Proof.
  move => Htypes; induction Htypes => //=.
  move/andP: H => [_ /eqP ->].
  by rewrite IHHtypes.
Qed.

Lemma module_components_all {A B} (P : A -> B -> Prop) (check : A -> bool) xs ys :
  (forall x y, P x y -> check x) ->
  List.Forall2 P xs ys -> all check xs.
Proof.
  move => Hcheck Htypes; induction Htypes => //=.
  by rewrite (Hcheck _ _ H) IHHtypes.
Qed.

Theorem module_type_checker_complete m impts expts :
  module_typing m impts expts ->
  module_type_checker m = (Some (impts, expts), "ok"%string).
Proof.
  destruct m.
  rewrite /module_typing.
  move => [fts [tts [mts [gts [rts [dts
    [Hmtypes [Hmfuncs [Hmtabs [Hmmems [Hmglobals
    [Hmelems [Hmdatas [Hstart [Hmimports [Hmexports Hnames]]]]]]]]]]]]]]]].
  destruct Hmglobals as [Hgts Hglobals].
  specialize (module_table_types_complete _ _ _ Hmtabs) as Htts.
  specialize (module_mem_types_complete _ _ _ Hmmems) as Hmts.
  subst tts mts gts.
  match type of Hmfuncs with List.Forall2 (module_func_typing ?C0) _ _ => pose Cfull := C0 end.
  match type of Hglobals with extended_globals_typing ?C0 _ => pose Cinit := C0 end.
  fold Cfull in Hmfuncs, Hmimports, Hmexports, Hstart.
  fold Cinit in Hglobals, Hmtabs, Hmmems, Hmelems, Hmdatas.
  specialize (gather_m_f_types_complete _ _ _ Hmfuncs) as Hfts.
  specialize (module_imports_typer_complete _ _ _ Hmimports) as Himpts.
  specialize (gather_m_e_types_complete _ _ _ Hmelems) as Hrts.
  specialize (gather_m_d_types_complete _ _ _ Hmdatas) as Hdts.
  specialize (module_exports_typer_complete _ _ _ Hmexports) as Hexpts.
  assert (all (module_func_type_checker Cfull) mod_funcs) as Hfs.
  { eapply module_components_all; last exact Hmfuncs.
    move => mf tf Htype.
    by eapply module_func_type_checker_complete; eauto.
  }
  assert (all (module_table_type_checker Cfull) mod_tables) as Htabs.
  { eapply module_components_all; last exact Hmtabs.
    by move => tab tt /andP [Hvalid _].
  }
  assert (all (module_mem_type_checker Cfull) mod_mems) as Hmems.
  { eapply module_components_all; last exact Hmmems.
    by move => mem mt /andP [Hvalid _].
  }
  assert (extended_globals_type_checker Cinit mod_globals) as Hgs.
  { by apply/extended_globals_type_checker_reflects. }
  assert (all (module_elem_type_checker (const_context_add_globals Cinit
    (map modglob_type mod_globals))) mod_elems) as Hels.
  { by eapply module_components_all; last exact Hmelems;
      move => el rt; apply module_elem_type_checker_complete. }
  assert (all (module_data_type_checker (const_context_add_globals Cinit
    (map modglob_type mod_globals))) mod_datas) as Hds.
  { by eapply module_components_all; last exact Hmdatas;
      move => d t; apply module_data_type_checker_complete. }
  change (gather_m_f_types mod_types mod_funcs = Some fts) in Hfts.
  change (module_imports_typer mod_types mod_imports = Some impts) in Himpts.
  cbn [tc_tables const_context_add_globals] in Hrts.
  cbn [tc_mems const_context_add_globals] in Hdts.
  unfold module_type_checker.
  rewrite Hfts Himpts Hrts Hdts.
  change ((if all (module_func_type_checker Cfull) mod_funcs &&
    all (module_table_type_checker Cfull) mod_tables &&
    all (module_mem_type_checker Cfull) mod_mems &&
    extended_globals_type_checker Cinit mod_globals &&
    all (module_elem_type_checker (const_context_add_globals Cinit
      (map modglob_type mod_globals))) mod_elems &&
    all (module_data_type_checker (const_context_add_globals Cinit
      (map modglob_type mod_globals))) mod_datas &&
    pred_option (module_start_type_checker Cfull) mod_start &&
    export_name_unique mod_exports
    then match module_exports_typer Cfull mod_exports with
         | Some ts => (Some (impts, ts), "ok"%string)
         | None => (None, "invalid module export type"%string)
         end
    else (None, "invalid module components"%string)) =
      (Some (impts, expts), "ok"%string)).
  rewrite Hfs Htabs Hmems Hgs Hels Hds Hstart Hnames /= Hexpts.
  reflexivity.
Qed.

Corollary module_type_checker_spec m impts expts :
  module_typing m impts expts <->
  exists message, module_type_checker m = (Some (impts, expts), message).
Proof.
  split.
  - move => Htype.
    exists "ok"%string.
    by apply module_type_checker_complete.
  - move => [message Hcheck].
    by eapply module_type_checker_sound; eauto.
Qed.

End Host.
