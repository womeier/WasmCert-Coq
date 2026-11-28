(** Allocation correspondence, independent of recursive binary parser proofs.
    This discharges allocation determinism/completeness, not evaluation of
    declarative initializer reductions or extraction/backend correspondence. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func instantiation_properties
  instantiation_complete interp_instantiate_sound.
From Stdlib Require Import String List.

Set SsrOldRewriteGoalsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho: host}.

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

End Host.
