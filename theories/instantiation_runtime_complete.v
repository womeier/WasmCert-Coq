(** Executable/declarative instantiation correspondence, independent of the
    recursive binary parser framework. The result is the allocated store,
    frame and pending initialization code of the existing instantiate relation.
    Execution of that code and extraction/backend correspondence are separate.
    Allocation is assumption-free; reductions retain inherited opsem oracles. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func instantiation_properties
  instantiation_complete interp_instantiate_sound type_checker_reflects_typing.
From Stdlib Require Import String List NArith.

Set SsrOldRewriteGoalsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho: host}.
Local Opaque type_checker.b_e_type_checker.

Definition allocated_module_instance s m imps : moduleinst :=
  let ifs := ext_funcs imps ++ iota_N (length s.(s_funcs)) (length m.(mod_funcs)) in
  let its := ext_tables imps ++ iota_N (length s.(s_tables)) (length m.(mod_tables)) in
  let ims := ext_mems imps ++ iota_N (length s.(s_mems)) (length m.(mod_mems)) in
  let igs := ext_globals imps ++ iota_N (length s.(s_globals)) (length m.(mod_globals)) in
  Build_moduleinst m.(mod_types) ifs its ims igs
    (iota_N (length s.(s_elems)) (length m.(mod_elems)))
    (iota_N (length s.(s_datas)) (length m.(mod_datas)))
    (map (get_exportinst (Build_moduleinst nil ifs its ims igs nil nil nil))
      m.(mod_exports)).

Lemma alloc_module_instance_unique : forall s m imps gvs rvs s' inst,
  length gvs = length m.(mod_globals) ->
  length rvs = length m.(mod_elems) ->
  alloc_module s m imps gvs rvs (s', inst) ->
  inst = allocated_module_instance s m imps.
Proof.
  move => s m imps gvs rvs s' inst Hg Hr Halloc.
  unfold alloc_module in Halloc.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hf.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Ht.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hm.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hgalloc.
  destruct (alloc_elems _ _) as [s5 ies] eqn:He.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hd.
  apply alloc_func_iota_N in Hf.
  apply alloc_table_iota_N in Ht.
  apply alloc_mem_iota_N in Hm.
  apply alloc_global_iota_N in Hgalloc; last exact Hg.
  apply alloc_elem_iota_N in He; last exact Hr.
  apply alloc_data_iota_N in Hd.
  extract_premise.
  destruct s, s1, s2, s3, s4, s5, s6, inst.
  simpl in *. subst.
  unfold allocated_module_instance => /=.
  rewrite !length_is_size !size_map.
  rewrite !length_is_size !size_map in Hconjr0.
  f_equal.
  match goal with
  | H: ?exports = ?rhs |- ?exports = _ => rewrite H
  end.
  apply List.map_ext. move => [nm desc].
  unfold get_exportinst, export_get_v_ext => /=.
  by destruct desc.
Qed.

Lemma interp_alloc_complete : forall s m imps gvs rvs s' inst,
  length gvs = length m.(mod_globals) ->
  length rvs = length m.(mod_elems) ->
  alloc_module s m imps gvs rvs (s', inst) ->
  interp_alloc_module s m imps gvs rvs = (s', inst).
Proof.
  move => s m imps gvs rvs s' inst Hg Hr Halloc.
  have Hinst := alloc_module_instance_unique Hg Hr Halloc.
  unfold interp_alloc_module.
  change ((let inst0 := allocated_module_instance s m imps in
    let '(s1, _) := alloc_funcs s m.(mod_funcs) inst0 in
    let '(s2, _) := alloc_tabs s1 (map modtab_type m.(mod_tables)) in
    let '(s3, _) := alloc_mems s2 (map modmem_type m.(mod_mems)) in
    let '(s4, _) := alloc_globs s3 m.(mod_globals) gvs in
    let '(s5, _) := alloc_elems s4 m.(mod_elems) rvs in
    let '(s6, _) := alloc_datas s5 m.(mod_datas) in
    (s6, inst0)) = (s', inst)).
  rewrite -Hinst.
  cbv zeta.
  unfold alloc_module in Halloc.
  destruct (alloc_funcs _ _ _) as [s1 ifs].
  destruct (alloc_tabs _ _) as [s2 its].
  destruct (alloc_mems _ _) as [s3 ims].
  destruct (alloc_globs _ _) as [s4 igs].
  destruct (alloc_elems _ _) as [s5 ies].
  destruct (alloc_datas _ _) as [s6 ids].
  by destruct Halloc as [-> _].
Qed.

Theorem interp_alloc_spec : forall s m imps gvs rvs s' inst,
  length gvs = length m.(mod_globals) ->
  length rvs = length m.(mod_elems) ->
  (alloc_module s m imps gvs rvs (s', inst) <->
    interp_alloc_module s m imps gvs rvs = (s', inst)).
Proof.
  move => s m imps gvs rvs s' inst Hg Hr; split.
  - exact (interp_alloc_complete Hg Hr).
  - move => Hrun. by eapply interp_alloc_sound; eauto.
Qed.

Theorem instantiate_prechecks_complete : forall s m imps s' f bes,
  instantiate s m imps (s', f, bes) ->
  exists expected actual exports,
    module_type_checker m = (Some (expected, exports), "ok"%string) /\
    those (map (external_type_checker s) imps) = Some actual /\
    all2 import_subtyping actual expected.
Proof.
  move => s m imps s' f bes Hinst.
  destruct Hinst as [expected [actual [exports [hs [inst [gvs [rvs
    [Htype [Hext [Hsub _]]]]]]]]]].
  exists expected, actual, exports. split.
  - now apply module_type_checker_complete.
  - split.
    + eapply Forall2_map_typer; last exact Hext.
      move => v t H. exact H.
    + by apply Forall2_all2.
Qed.

(** Unlike the low-level allocation specification, this corollary needs no
    initializer-length premises: declarative instantiation supplies them via
    its two Forall2 initializer judgments. It does not assume executable
    initializer evaluation or claim complete interp_instantiate equivalence. *)
Theorem instantiate_allocation_realized : forall s m imps s' f bes,
  instantiate s m imps (s', f, bes) ->
  exists gvs rvs inst,
    interp_alloc_module s m imps gvs rvs = (s', inst) /\
    f = Build_frame nil inst /\
    bes = get_init_expr_elems m.(mod_elems) ++
      get_init_expr_datas m.(mod_datas) ++ get_init_expr_start m.(mod_start).
Proof.
  move => s m imps s' f bes Hinst.
  destruct Hinst as [expected [actual [exports [hs [inst [gvs [rvs
    [Htype [Hext [Hsub [Halloc [Hglobals [Helems [Hframe Hbes]]]]]]]]]]]]]].
  exists gvs, rvs, inst. split; last by split.
  apply interp_alloc_complete => //.
  - symmetry. exact (List.Forall2_length Hglobals).
  - symmetry. exact (List.Forall2_length Helems).
Qed.

Lemma interp_get_const_singleton_sound : forall hs s f e v,
  interp_get_const s f [::e] = Some v ->
  opsem.reduce_trans (hs, s, f, to_e_list [::e])
    (hs, s, f, [::v_to_e v]).
Proof.
  move => hs s f e v Hrun.
  destruct e; simpl in Hrun; try discriminate.
  1,2,3: injection Hrun as <-; by constructor.
  - destruct (lookup_N (inst_funcs (f_inst f)) f0) eqn:Hlookup => //.
    injection Hrun as <-. constructor. by apply opsem.r_ref_func.
  - constructor. by apply opsem.r_global_get.
Qed.

Theorem interp_get_const_reduction_complete : forall C es t hs hs' s s' f f' v,
  const_exprs C es ->
  be_typing C es (Tf nil [::t]) ->
  opsem.reduce_trans (hs, s, f, to_e_list es)
    (hs', s', f', [::v_to_e v]) ->
  interp_get_const s f es = Some v.
Proof.
  move => C es t hs hs' s s' f f' v Hconst Htype Hred.
  eapply const_exprs_impl in Hconst as [e [-> Hconst]]; last exact Htype.
  unfold const_expr in Hconst.
  destruct e => //=.
  - have Heq := reduce_trans_value (v1 := VAL_num v0) Hred.
    by subst.
  - have Heq := reduce_trans_value (v1 := VAL_vec v0) Hred.
    by subst.
  - have Heq := reduce_trans_value (v1 := VAL_ref (VAL_ref_null r)) Hred.
    by subst.
  - apply reduce_trans_ref_func in Hred.
    destruct Hred as [addr [Hlookup ->]]. by rewrite Hlookup.
  - exact (reduce_trans_global_get Hred).
Qed.

Theorem interp_get_const_reduction_spec : forall C es t hs s f v,
  const_exprs C es ->
  be_typing C es (Tf nil [::t]) ->
  (interp_get_const s f es = Some v <->
    opsem.reduce_trans (hs, s, f, to_e_list es) (hs, s, f, [::v_to_e v])).
Proof.
  move => C es t hs s f v Hconst Htype; split.
  - move => Hrun.
    eapply const_exprs_impl in Hconst as [e [-> Hconst]]; last exact Htype.
    exact (interp_get_const_singleton_sound hs Hrun).
  - move => Hred. by eapply interp_get_const_reduction_complete; eauto.
Qed.

Lemma global_initializer_reductions_complete : forall C hs s f gs vs,
  all (module_global_type_checker C) gs ->
  List.Forall2 (fun g v =>
    opsem.reduce_trans (hs, s, f, to_e_list g.(modglob_init))
      (hs, s, f, [::v_to_e v])) gs vs ->
  get_global_inits s f gs = Some vs.
Proof.
  move => C hs s f gs vs Hcheck Hred.
  unfold get_global_inits. rewrite -those_those0.
  revert Hcheck. induction Hred; move => /= Hcheck; first reflexivity.
  move/andP: Hcheck => [Hhead Htail].
  destruct x as [gt body]. cbn in Hhead.
  move/andP: Hhead => [Hconst Htype].
  move/b_e_type_checker_reflects_typing in Htype.
  have Heval: interp_get_const s f body = Some y.
  { by eapply interp_get_const_reduction_complete; eauto. }
  cbn. rewrite Heval. by rewrite (IHHred Htail).
Qed.

Lemma reference_initializer_reductions_complete : forall C t hs s f es rs,
  all (const_exprs C) es ->
  all (fun body => type_checker.b_e_type_checker C body (Tf nil [::T_ref t])) es ->
  List.Forall2 (fun body r =>
    opsem.reduce_trans (hs, s, f, to_e_list body)
      (hs, s, f, [::v_to_e (VAL_ref r)])) es rs ->
  those (map (interp_get_vref s f) es) = Some rs.
Proof.
  move => C t hs s f es rs Hconst Htype Hred.
  rewrite -those_those0.
  revert Hconst Htype. induction Hred; move => /= Hconst Htype; first reflexivity.
  move/andP: Hconst => [Hc Hcs].
  move/andP: Htype => [Ht Hts].
  move/b_e_type_checker_reflects_typing in Ht.
  have Heval: interp_get_const s f x = Some (VAL_ref y).
  { by eapply interp_get_const_reduction_complete; eauto. }
  unfold interp_get_vref. rewrite Heval. by rewrite (IHHred Hcs Hts).
Qed.

Lemma element_initializer_reductions_complete : forall C hs s f els rs,
  all (module_elem_type_checker C) els ->
  List.Forall2 (fun el vs =>
    List.Forall2 (fun body r =>
      opsem.reduce_trans (hs, s, f, to_e_list body)
        (hs, s, f, [::v_to_e (VAL_ref r)])) el.(modelem_init) vs) els rs ->
  get_elem_inits s f els = Some rs.
Proof.
  move => C hs s f els rs Hcheck Hred.
  unfold get_elem_inits. rewrite -those_those0.
  revert Hcheck. induction Hred; move => /= Hcheck; first reflexivity.
  move/andP: Hcheck => [Hhead Htail].
  destruct x as [rt init mode]. cbn in Hhead.
  move/andP: Hhead => [/andP [Hconst Htype] Hmode].
  have Heval: those (map (interp_get_vref s f) init) = Some y.
  { by eapply reference_initializer_reductions_complete; eauto. }
  cbn. rewrite Heval. by rewrite (IHHred Htail).
Qed.

Theorem instantiate_allocated_initializers_complete : forall s m imps s' f bes,
  instantiate s m imps (s', f, bes) ->
  exists inst gvs rvs,
    alloc_module s m imps gvs rvs (s', inst) /\
    let f_init := Build_frame nil
      (Build_moduleinst nil inst.(inst_funcs) nil nil (ext_globals imps) nil nil nil) in
    get_global_inits s' f_init m.(mod_globals) = Some gvs /\
    get_elem_inits s' f_init m.(mod_elems) = Some rvs.
Proof.
  move => s m imps s' f bes Hinst.
  destruct Hinst as [expected [actual [exports [hs [inst [gvs [rvs
    [Htype [Hext [Hsub [Halloc [Hglobals [Helems [Hframe Hbes]]]]]]]]]]]]]].
  exists inst, gvs, rvs. split; first exact Halloc.
  have Hcheck := module_type_checker_complete Htype.
  have Hcheck' := Hcheck.
  apply module_typecheck_glob_aux in Hcheck as [Cg Hgcheck].
  apply module_typecheck_elem_aux in Hcheck' as [Ce Hecheck].
  split.
  - by eapply global_initializer_reductions_complete; eauto.
  - by eapply element_initializer_reductions_complete; eauto.
Qed.

Lemma alloc_module_globals_extension : forall s m imps gvs rvs s' inst,
  length gvs = length m.(mod_globals) ->
  length rvs = length m.(mod_elems) ->
  alloc_module s m imps gvs rvs (s', inst) ->
  exists added, s'.(s_globals) = s.(s_globals) ++ added.
Proof.
  move => s m imps gvs rvs s' inst Hg Hr Halloc.
  unfold alloc_module in Halloc.
  destruct (alloc_funcs _ _ _) as [s1 ifs] eqn:Hf.
  destruct (alloc_tabs _ _) as [s2 its] eqn:Ht.
  destruct (alloc_mems _ _) as [s3 ims] eqn:Hm.
  destruct (alloc_globs _ _) as [s4 igs] eqn:Hgalloc.
  destruct (alloc_elems _ _) as [s5 ies] eqn:He.
  destruct (alloc_datas _ _) as [s6 ids] eqn:Hd.
  apply alloc_func_iota_N in Hf.
  apply alloc_table_iota_N in Ht.
  apply alloc_mem_iota_N in Hm.
  apply alloc_global_iota_N in Hgalloc; last exact Hg.
  apply alloc_elem_iota_N in He; last exact Hr.
  apply alloc_data_iota_N in Hd.
  extract_premise.
  destruct s, s1, s2, s3, s4, s5, s6.
  simpl in *. subst. by eexists.
Qed.

Lemma imported_global_values_extension : forall s s' imps types inst added,
  List.Forall2 (external_typing s) imps types ->
  inst.(inst_globals) = ext_globals imps ->
  s'.(s_globals) = s.(s_globals) ++ added ->
  forall i, sglob_val s' inst i = sglob_val s inst i.
Proof.
  move => s s' imps types inst added Hext Hglobals Hstore i.
  unfold sglob_val, sglob, sglob_ind. rewrite Hglobals.
  destruct (lookup_N (ext_globals imps) i) as [addr|] eqn:Haddr => //.
  unfold lookup_N in Haddr.
  apply ext_globals_lookup_exist in Haddr as [k Himp].
  eapply Forall2_lookup in Hext; last exact Himp.
  destruct Hext as [et [_ Htyped]].
  unfold external_typing, ext_typing, ext_global_typing in Htyped.
  destruct (lookup_N (s_globals s) addr) as [g|] eqn:Hg; [|discriminate].
  rewrite Hstore. unfold lookup_N in *.
  erewrite nth_error_app_Some; last exact Hg.
  reflexivity.
Qed.

Lemma interp_get_const_store_extension : forall s s' f imps types added,
  List.Forall2 (external_typing s) imps types ->
  f.(f_inst).(inst_globals) = ext_globals imps ->
  s'.(s_globals) = s.(s_globals) ++ added ->
  forall es, interp_get_const s' f es = interp_get_const s f es.
Proof.
  move => s s' f imps types added Hext Hglobals Hstore es.
  destruct es as [|e [|e' rest]] => //.
  destruct e => //=.
  by eapply imported_global_values_extension; eauto.
Qed.

Lemma initializer_evaluators_store_extension : forall s s' f imps types added m,
  List.Forall2 (external_typing s) imps types ->
  f.(f_inst).(inst_globals) = ext_globals imps ->
  s'.(s_globals) = s.(s_globals) ++ added ->
  get_global_inits s' f m.(mod_globals) = get_global_inits s f m.(mod_globals) /\
  get_elem_inits s' f m.(mod_elems) = get_elem_inits s f m.(mod_elems).
Proof.
  move => s s' f imps types added m Hext Hglobals Hstore.
  have Hconst: forall es, interp_get_const s' f es = interp_get_const s f es.
  { by eapply interp_get_const_store_extension; eauto. }
  split.
  - unfold get_global_inits. f_equal. apply List.map_ext.
    move => g. exact (Hconst g.(modglob_init)).
  - unfold get_elem_inits. f_equal. apply List.map_ext.
    move => el. f_equal. apply List.map_ext.
    move => es. by unfold interp_get_vref; rewrite Hconst.
Qed.

Theorem interp_instantiate_complete : forall hs s m imps s' f bes,
  instantiate s m imps (s', f, bes) ->
  interp_instantiate hs s m imps = (Some (hs, s', f, bes), ""%string).
Proof.
  move => hs s m imps s' f bes Hinst.
  destruct Hinst as [expected [actual [exports [hs_decl [inst [gvs [rvs
    [Htype [Hext [Hsub [Halloc [Hglobals [Helems [Hframe Hbes]]]]]]]]]]]]]].
  have Hg: length gvs = length m.(mod_globals).
  { symmetry. exact (List.Forall2_length Hglobals). }
  have Hr: length rvs = length m.(mod_elems).
  { symmetry. exact (List.Forall2_length Helems). }
  have Hshape := alloc_module_instance_unique Hg Hr Halloc.
  subst inst.
  set init := Build_frame nil
    (Build_moduleinst nil
      (ext_funcs imps ++ iota_N (length s.(s_funcs)) (length m.(mod_funcs)))
      nil nil (ext_globals imps) nil nil nil).
  have Hcheck := module_type_checker_complete Htype.
  have Hcheckg := Hcheck.
  have Hchecke := Hcheck.
  apply module_typecheck_glob_aux in Hcheckg as [Cg Hgcheck].
  apply module_typecheck_elem_aux in Hchecke as [Ce Hecheck].
  have Hglobal_end: get_global_inits s' init m.(mod_globals) = Some gvs.
  { by eapply global_initializer_reductions_complete; eauto. }
  have Helem_end: get_elem_inits s' init m.(mod_elems) = Some rvs.
  { by eapply element_initializer_reductions_complete; eauto. }
  have [added Hstore] := alloc_module_globals_extension Hg Hr Halloc.
  have Heval:
    get_global_inits s' init m.(mod_globals) =
      get_global_inits s init m.(mod_globals) /\
    get_elem_inits s' init m.(mod_elems) =
      get_elem_inits s init m.(mod_elems).
  { by eapply initializer_evaluators_store_extension; eauto. }
  destruct Heval as [Hgg Hge].
  rewrite Hgg in Hglobal_end. rewrite Hge in Helem_end.
  have Hexternal: those (map (external_type_checker s) imps) = Some actual.
  { eapply Forall2_map_typer; last exact Hext.
    move => v t H. exact H. }
  have Hsubcheck: all2 import_subtyping actual expected.
  { by apply Forall2_all2. }
  have Halloc_run := interp_alloc_complete Hg Hr Halloc.
  unfold interp_instantiate.
  rewrite Hcheck Hexternal Hsubcheck.
  change (get_global_inits s
    (Build_frame nil (Build_moduleinst nil
      (ext_funcs imps ++ map N.of_nat (iota (length s.(s_funcs)) (length m.(mod_funcs))))
      nil nil (ext_globals imps) nil nil nil))
    m.(mod_globals) = Some gvs) in Hglobal_end.
  rewrite Hglobal_end.
  change (get_elem_inits s
    (Build_frame nil (Build_moduleinst nil
      (ext_funcs imps ++ map N.of_nat (iota (length s.(s_funcs)) (length m.(mod_funcs))))
      nil nil (ext_globals imps) nil nil nil))
    m.(mod_elems) = Some rvs) in Helem_end.
  rewrite Helem_end Halloc_run.
  by rewrite Hframe Hbes.
Qed.

Theorem interp_instantiate_spec : forall hs s m imps s' f bes,
  instantiate s m imps (s', f, bes) <->
  exists message, interp_instantiate hs s m imps =
    (Some (hs, s', f, bes), message).
Proof.
  move => hs s m imps s' f bes; split.
  - move => H. exists ""%string. now apply interp_instantiate_complete.
  - move => [message H].
    by eapply interp_instantiate_imp_instantiate; eauto.
Qed.

End Host.
