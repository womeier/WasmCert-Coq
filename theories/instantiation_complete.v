(** Completeness of executable module validation. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func instantiation_properties
  type_checker_reflects_typing interp_instantiate_sound.
From Stdlib Require Import List String.

Set SsrOldRewriteGoalsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho: host}.
Local Opaque type_checker.b_e_type_checker.

Lemma Forall2_map_typer : forall A B (R: A -> B -> Prop) f xs ys,
  (forall x y, R x y -> f x = Some y) ->
  List.Forall2 R xs ys ->
  those (map f xs) = Some ys.
Proof.
  move => A B R f xs ys Hf Hrel.
  rewrite -those_those0.
  induction Hrel => /=; first reflexivity.
  rewrite (Hf _ _ H).
  by rewrite IHHrel.
Qed.

Lemma Forall2_all_left : forall A B (R: A -> B -> Prop) (p: A -> bool) xs ys,
  (forall x y, R x y -> p x) ->
  List.Forall2 R xs ys ->
  all p xs.
Proof.
  move => A B R p xs ys Hp Hrel.
  induction Hrel => //=.
  by rewrite (Hp _ _ H) IHHrel.
Qed.

Lemma module_import_typer_complete : forall C imp et,
  module_import_typing C imp et ->
  module_import_desc_typer C.(tc_types) imp.(imp_desc) = Some et.
Proof.
  move => C [mn nm desc] et Htype.
  unfold module_import_typing, module_import_desc_typing in Htype.
  destruct desc; simpl in *.
  - move/eqP in Htype.
    destruct (lookup_N (tc_types C) t); simpl in *; try discriminate.
    by inversion Htype.
  - move/andP: Htype => [Hvalid /eqP ->].
    by rewrite Hvalid.
  - move/andP: Htype => [Hvalid /eqP ->].
    by rewrite Hvalid.
  - by move/eqP in Htype; subst.
Qed.

Lemma gather_m_f_types_complete : forall C fs fts,
  List.Forall2 (module_func_typing C) fs fts ->
  gather_m_f_types C.(tc_types) fs = Some fts.
Proof.
  move => C fs fts Htype.
  apply Forall2_map_typer with (R := module_func_typing C) => //.
  move => [x locs body] [tn tm] /= [Hlookup _].
  by apply Hlookup.
Qed.

Lemma module_func_checker_complete : forall C f ft,
  C.(tc_locals) = nil ->
  C.(tc_labels) = nil ->
  module_func_typing C f ft ->
  module_func_type_checker C f.
Proof.
  move => C [x locs body] [tn tm] Hloc Hlab [Hlookup [Hbody Hdefault]].
  unfold module_func_type_checker => /=.
  rewrite Hlookup Hloc Hlab => /=.
  apply/andP; split; last by apply/eqP.
  apply/b_e_type_checker_reflects_typing.
  by apply Hbody.
Qed.

Lemma module_global_checker_complete : forall C g gt,
  module_global_typing C g gt ->
  module_global_type_checker C g.
Proof.
  move => C [gt' body] gt [Hconst [-> Hbody]].
  unfold module_global_type_checker => /=.
  apply/andP; split => //.
  by apply/b_e_type_checker_reflects_typing.
Qed.

Lemma module_data_checker_complete : forall C d dt,
  module_data_typing C d dt ->
  module_data_type_checker C d.
Proof.
  move => C [init mode] dt [Hmode _].
  unfold module_data_type_checker, module_data_mode_checker => /=.
  destruct mode => //=.
  destruct Hmode as [mt [Hmem [Hoffset Hconst]]].
  rewrite Hmem. apply/andP; split => //.
  by apply/b_e_type_checker_reflects_typing.
Qed.

Lemma gather_m_d_type_complete : forall C d dt,
  module_data_typing C d dt ->
  gather_m_d_type C.(tc_mems) d.(moddata_mode) = Some dt.
Proof.
  move => C [init mode] dt [Hmode ->].
  unfold gather_m_d_type => /=.
  destruct mode => //=.
  destruct Hmode as [mt [Hmem _]].
  by rewrite Hmem.
Qed.

Lemma gather_m_e_type_complete : forall C e et,
  module_elem_typing C e et ->
  gather_m_e_type C.(tc_tables) e = Some et.
Proof.
  move => C [rt init mode] et [-> [Hinit Hmode]].
  unfold gather_m_e_type => /=.
  destruct mode => //=.
  destruct Hmode as [[lim rt'] [Htab [-> _]]].
  by rewrite Htab /= eq_refl.
Qed.

Lemma module_elem_checker_complete : forall C e et,
  module_elem_typing C e et ->
  module_elem_type_checker C e.
Proof.
  move => C [rt init mode] et [-> [Hinit Hmode]].
  unfold module_elem_type_checker => /=.
  apply/andP; split.
  - apply/andP; split; apply/allP; move => body Hin;
      move/List.Forall_forall: Hinit => Hinit;
      move/inP in Hin;
      specialize (Hinit body Hin) as [Hconst Hbody] => //.
    by apply/b_e_type_checker_reflects_typing.
  - unfold module_elem_mode_checker.
    destruct mode => //=.
    destruct Hmode as [[lim rt'] [Htab [-> [Hoffset Hconst]]]].
    rewrite Htab /= eq_refl => /=.
    apply/andP; split => //.
    by apply/b_e_type_checker_reflects_typing.
Qed.

Lemma module_export_typer_complete : forall C exp et,
  module_export_typing C exp et ->
  module_export_typer C exp.(modexp_desc) = Some et.
Proof.
  move => C [nm desc] et Htype.
  unfold module_export_typing, module_export_desc_typing in Htype.
  destruct desc, et; simpl in *; try discriminate;
    destruct (lookup_N _ _); simpl in *; try discriminate;
    move/eqP in Htype; subst; reflexivity.
Qed.

Lemma Forall2_map_right : forall A B (R: A -> B -> Prop) f xs ys,
  (forall x y, R x y -> f x = y) ->
  List.Forall2 R xs ys ->
  ys = map f xs.
Proof.
  move => A B R f xs ys Hf Hrel.
  induction Hrel => //=.
  by rewrite (Hf _ _ H) IHHrel.
Qed.

Theorem module_type_checker_complete : forall m impts expts,
  module_typing m impts expts ->
  module_type_checker m = (Some (impts, expts), "ok"%string).
Proof.
  move => m impts expts Htype.
  destruct m.
  unfold module_typing in Htype; simpl in Htype.
  destruct Htype as [fts [tts [mts [gts [rts [dts
    [Htypes [Hfunc [Htable [Hmem [Hglobal [Helem [Hdata
      [Hstart [Himport [Hexport Hunique]]]]]]]]]]]]]]]].
  have Htts: tts = map modtab_type mod_tables.
  { eapply Forall2_map_right; last exact Htable.
    move => t tt /andP [_ /eqP Heq]. exact Heq. }
  have Hmts: mts = map modmem_type mod_mems.
  { eapply Forall2_map_right; last exact Hmem.
    move => mm mt /andP [_ /eqP Heq]. exact Heq. }
  have Hgts: gts = gather_m_g_types mod_globals.
  { eapply Forall2_map_right; last exact Hglobal.
    move => [gt init] ty [_ [Heq _]]. simpl in *. by symmetry. }
  subst tts mts gts.
  set C := Build_t_context mod_types
    (ext_t_funcs impts ++ fts)
    (ext_t_tables impts ++ map modtab_type mod_tables)
    (ext_t_mems impts ++ map modmem_type mod_mems)
    (ext_t_globals impts ++ gather_m_g_types mod_globals)
    rts dts nil nil None
    (module_filter_funcidx
      (Build_module mod_types mod_funcs mod_tables mod_mems mod_globals
        mod_elems mod_datas mod_start mod_imports mod_exports)).
  set Cg := Build_t_context nil C.(tc_funcs) C.(tc_tables) C.(tc_mems)
    (ext_t_globals impts) nil nil nil nil None C.(tc_refs).
  change (List.Forall2 (module_func_typing C) mod_funcs fts) in Hfunc.
  change (List.Forall2 (module_table_typing Cg) mod_tables
    (map modtab_type mod_tables)) in Htable.
  change (List.Forall2 (module_mem_typing Cg) mod_mems
    (map modmem_type mod_mems)) in Hmem.
  change (List.Forall2 (module_global_typing Cg) mod_globals
    (gather_m_g_types mod_globals)) in Hglobal.
  change (List.Forall2 (module_elem_typing Cg) mod_elems rts) in Helem.
  change (List.Forall2 (module_data_typing Cg) mod_datas dts) in Hdata.
  change (List.Forall2 (module_import_typing C) mod_imports impts) in Himport.
  change (List.Forall2 (module_export_typing C) mod_exports expts) in Hexport.
  change (is_true (pred_option (module_start_typing C) mod_start)) in Hstart.
  have Hft: gather_m_f_types mod_types mod_funcs = Some fts.
  { exact (gather_m_f_types_complete Hfunc). }
  have Hit: module_imports_typer mod_types mod_imports = Some impts.
  { apply Forall2_map_typer with (R := module_import_typing C) => //.
    move => imp et Himp. exact (module_import_typer_complete Himp). }
  have Het: gather_m_e_types C.(tc_tables) mod_elems = Some rts.
  { apply Forall2_map_typer with (R := module_elem_typing Cg) => //.
    move => elem et He. exact (gather_m_e_type_complete He). }
  have Hdt: gather_m_d_types C.(tc_mems) mod_datas = Some dts.
  { apply Forall2_map_typer with (R := module_data_typing Cg) => //.
    move => data dt Hd. exact (gather_m_d_type_complete Hd). }
  have Hext: module_exports_typer C mod_exports = Some expts.
  { apply Forall2_map_typer with (R := module_export_typing C) => //.
    move => exp et He. exact (module_export_typer_complete He). }
  have Hfc: all (module_func_type_checker C) mod_funcs.
  { eapply Forall2_all_left; last exact Hfunc.
    move => f ft Hf. by eapply module_func_checker_complete; eauto. }
  have Htc: all (module_table_type_checker C) mod_tables.
  { eapply Forall2_all_left; last exact Htable.
    move => t tt /andP [Hvalid _]. exact Hvalid. }
  have Hmc: all (module_mem_type_checker C) mod_mems.
  { eapply Forall2_all_left; last exact Hmem.
    move => mm mt /andP [Hvalid _]. exact Hvalid. }
  have Hgc: all (module_global_type_checker Cg) mod_globals.
  { eapply Forall2_all_left; last exact Hglobal.
    move => g gt Hg. by eapply module_global_checker_complete; eauto. }
  have Hec: all (module_elem_type_checker Cg) mod_elems.
  { eapply Forall2_all_left; last exact Helem.
    move => elem et He. by eapply module_elem_checker_complete; eauto. }
  have Hdc: all (module_data_type_checker Cg) mod_datas.
  { eapply Forall2_all_left; last exact Hdata.
    move => data dt Hd. by eapply module_data_checker_complete; eauto. }
  unfold module_type_checker.
  rewrite Hft Hit.
  rewrite Het Hdt.
  fold C. fold Cg.
  by rewrite Hfc Htc Hmc Hgc Hec Hdc Hstart Hunique Hext.
Qed.

Theorem module_type_checker_spec : forall m impts expts,
  module_typing m impts expts <->
  exists message, module_type_checker m = (Some (impts, expts), message).
Proof.
  move => m impts expts; split.
  - move => Htype. exists "ok"%string.
    now apply module_type_checker_complete.
  - move => [message Hcheck].
    by eapply module_type_checker_sound; eauto.
Qed.

End Host.
