(** Proof of preservation **)

From Wasm Require Export typing_inversion tactic.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Stdlib Require Import Program.Equality ZArith.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{ho: host}.

(* Equality for the stateful parts (instances) of the typing context *)
Definition inst_match C C' : bool :=
  (C.(tc_tags) == C'.(tc_tags)) &&
  (C.(tc_types) == C'.(tc_types)) &&
  (C.(tc_funcs) == C'.(tc_funcs)) &&
  (C.(tc_tables) == C'.(tc_tables)) &&
  (C.(tc_mems) == C'.(tc_mems)) &&
  (C.(tc_globals) == C'.(tc_globals)) &&
  (C.(tc_elems) == C'.(tc_elems)) &&
  (C.(tc_datas) == C'.(tc_datas)) &&
  (C.(tc_refs) == C'.(tc_refs)).

Lemma inst_match_tags C C' :
  inst_match C C' -> C.(tc_tags) = C'.(tc_tags).
Proof. unfold inst_match; move => H; remove_bools_options; done. Qed.

Lemma throw_payload_typing s C vs x ps tin tout :
  e_typing s C (v_to_e_list vs ++ [::AI_basic (BI_throw x)]) (Tf tin tout) ->
  lookup_N C.(tc_tags) x = Some ps ->
  length vs = length ps ->
  values_typing s vs ps.
Proof.
  move => Htype Htag Hlen.
  apply e_composition_typing in Htype as [middle [Hvalues Hthrow]].
  apply Values_typing_inversion in Hvalues as [vts [Hsubv Hvals]].
  apply e_typing_inversion in Hthrow as [[args results] [Hsubt Hprincipal]].
  simpl in Hprincipal.
  destruct Hprincipal as [prefix [out [params [Heq Hlookup]]]].
  injection Heq as Heq1 Heq2; subst args results.
  rewrite Htag in Hlookup; injection Hlookup as <-.
  assert (Hsize: size vts = size ps).
  { pose proof (values_typing_size Hvals) as Hsizes.
    rewrite !length_is_size in Hlen; lias. }
  pose proof (instr_subtyping_suffix_prod_cons Hsubv Hsubt Hsize) as Hsub.
  by eapply values_typing_trans; eauto.
Qed.

(* Preservation for some less trivial operations *)
Lemma app_binop_type_preserve: forall op v1 v2 v,
    app_binop op v1 v2 = Some v ->
    typeof_num v = typeof_num v1.
Proof.
  move => op v1 v2 v.
  by elim: op; elim: v1; elim: v2 => //=; move => c1 c2 op H; destruct op; remove_bools_options.
Qed.

Lemma eval_cvt_type_preserve: forall op t1 t2 sx v1 v2,
    cvtop_valid t2 op t1 sx ->
    typeof_num v1 = t1 ->
    eval_cvt t2 op sx v1 = Some v2 ->
    typeof_num v2 = t2.
Proof.
  move => op t1 t2 sx v1 v2 Hcvtvalid Htype Heval.
  (* Just use brute force -- probably sledgehammer in some other theorem prover *)
  destruct op, t1, t2 => //; destruct sx as [[|] |] => //; cbn in Hcvtvalid => //; destruct v1 => //; simpl in * => //; by remove_bools_options => //=; inversion Heval.
Qed.

(* Typing of constants is not completely agnostic in Wasm 2.0 now -- since reference typings are dependent on the store. *)
Lemma et_const_agnostic: forall s C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es [ts1 ts2] HConst HType.
  apply const_es_exists in HConst as [vs Hve]; subst.
  invert_e_typing.
  eapply ety_subtyping; first by apply et_values_typing; eauto.
  done.
Qed.

Lemma v128_extract_lanes_typing: forall sh s vv vs,
    v128_extract_lanes sh s vv = vs ->
    List.Forall (fun v => typeof_num v = typeof_shape_unpacked sh) vs.
Proof.
  move => sh s vv vs; unfold v128_extract_lanes.
  destruct sh as [[] | []];
  destruct s; move => <-; apply List.Forall_map => /=;
  by apply List.Forall_forall.
Qed.
  
Lemma app_extract_vec_typing: forall sh os n v1,
    typeof_num (app_extract_vec sh os n v1) = typeof_shape_unpacked sh.
Proof.
  intros; unfold app_extract_vec.
  destruct (lookup_N _ _) eqn:Hlookup; last by destruct sh as [[] | []].
  by eapply Forall_lookup in Hlookup; last by eapply v128_extract_lanes_typing; eauto.
Qed.

(* It's better to just set `instr_subtyping` opaque and unset it when necessary, since most of the times we do not want to unfold this definition by simpl. But the simpl nomatch method doesn't prevent it from being unfolded for some reason. *)
Transparent instr_subtyping.

Lemma instr_subtyping_polymorphic_input tx ty tin tout out :
  Tf tx ty <ti: Tf tin tout ->
  exists extra, Tf (extra ++ tx) out <ti: Tf tin out.
Proof.
  move => Hsub.
  unfold instr_subtyping in Hsub.
  destruct Hsub as [extra [extra' [args [res [-> [-> [Hprefix [Hargs Hres]]]]]]]].
  exists extra.
  exists nil, nil, (extra ++ args), out; repeat split => //.
  - by apply values_subtyping_weaken.
  - by apply values_subtyping_eq.
Qed.

Opaque instr_subtyping.

Lemma control_output_typing s C e tin tout out :
  (exists l, e = AI_basic (BI_br l)) \/
  e = AI_basic BI_return \/ (exists a, e = AI_return_invoke a) ->
  e_typing s C [::e] (Tf tin tout) ->
  e_typing s C [::e] (Tf tin out).
Proof.
  move => [[l ->]|[->|[a ->]]] Htype;
    invert_e_typing;
    destruct (instr_subtyping_polymorphic_input out Htisub) as [extra Hsub].
  - eapply ety_subtyping; last exact Hsub.
    apply ety_a with (bes := [::BI_br l]); simpl.
    rewrite catA; by apply bet_br.
  - eapply ety_subtyping; last exact Hsub.
    apply ety_a with (bes := [::BI_return]); simpl.
    rewrite catA; by apply bet_return.
  - eapply ety_subtyping; last exact Hsub.
    rewrite catA; by eapply ety_return_invoke; eauto.
Qed.

Lemma control_suffix_typing s C vs e es ts :
  (exists l, e = AI_basic (BI_br l)) \/
  e = AI_basic BI_return \/ (exists a, e = AI_return_invoke a) ->
  e_typing s C (v_to_e_list vs ++ e :: es) (Tf nil ts) ->
  e_typing s C (v_to_e_list vs ++ [::e]) (Tf nil ts).
Proof.
  move => Hcontrol Htype.
  apply e_composition_typing in Htype as [middle [Hvalues Hrest]].
  rewrite -cat1s in Hrest.
  apply e_composition_typing in Hrest as [middle' [Hsingle Hsuffix]].
  eapply ety_composition; first exact Hvalues.
  by eapply control_output_typing; eauto.
Qed.

Lemma handler_control_typing s C vs e es ts1 ts2 n cs :
  (exists l, e = AI_basic (BI_br l)) \/
  e = AI_basic BI_return \/ (exists a, e = AI_return_invoke a) ->
  e_typing s C [::AI_handler n cs (v_to_e_list vs ++ e :: es)] (Tf ts1 ts2) ->
  e_typing s C (v_to_e_list vs ++ [::e]) (Tf ts1 ts2).
Proof.
  move => Hcontrol Htype.
  apply e_typing_inversion in Htype as [[tin tout] [Hsub Hprincipal]].
  simpl in Hprincipal.
  destruct Hprincipal as [ts [Heq [Hcatches [Hbody Hlen]]]].
  injection Heq as Heq1 Heq2; subst tin tout.
  eapply ety_subtyping; last exact Hsub.
  by eapply control_suffix_typing; eauto.
Qed.

Theorem t_simple_preservation: forall s es es' C tf,
    e_typing s C es tf ->
    reduce_simple es es' ->
    e_typing s C es' tf.
Proof.
  move => s es es' C [ts1 ts2] HType HReduce.
  inversion HReduce; subst; (try by apply ety_trap).
  all: try (eapply handler_control_typing; last exact HType;
    solve [left; by eexists | right; left; reflexivity | right; right; by eexists]).
  all: invert_e_typing; extract_premise => //; repeat (unify_principal => //; resolve_e_typing => //).
  - (* Unop *)
    replace (typeof_num (app_unop op v)) with (typeof_num v); last by destruct op, v.
    by resolve_subtyping.
  - (* Binop_success *)
    erewrite app_binop_type_preserve with (v1 := v1); eauto.
    by resolve_subtyping.
  - (* Cvtop *)
    erewrite eval_cvt_type_preserve; eauto.
    by resolve_subtyping.
  - (* Extract_vec *)
    replace (typeof_num (app_extract_vec sh sx x v1)) with (typeof_shape_unpacked sh); first by resolve_subtyping.
    by rewrite app_extract_vec_typing.
  - (* Br *)
    eapply et_composition'; eauto; resolve_e_typing.
    by eapply Lfilled_break_typing with (tss := nil) in Hconjl1; eauto => //=; try (by apply v_to_e_const); last by lias.
  - (* Br_if false *)
    instantiate (1 := extr).
    instantiate (1 := nil) => /=.
    by resolve_subtyping.
  - (* Br_br_table *)
    rewrite catA size_cat addnK take_size_cat => //.
    rewrite cats0.
    unfold lookup_N in *.
    eapply Forall_lookup with (x := j) (n := N.to_nat (Wasm_int.N_of_uint i32m c)) in Hconjr; eauto; last first.
    { rewrite List.nth_error_app1 => //.
      by lias.
    }
    {
      destruct Hconjr as [ts' [Hnth Hsub2]].
      apply ety_subtyping with (t1s := (extr ++ ts')) (t2s := extr0).
      { by apply ety_a' => //; econstructor; eauto => //. }
      { eapply instr_subtyping_weaken1 with (tx1 := extr ++ extr1); eauto; by resolve_subtyping. }
    }
  - (* Br_br_table_oob *)
    rewrite catA size_cat addnK take_size_cat => //.
    rewrite cats0.
    unfold lookup_N in *.
    eapply Forall_lookup with (x := i) (n := length iss) in Hconjr; eauto; last first.
    { rewrite List.nth_error_app2 => //.
      by rewrite Nat.sub_diag.
    }
    {
      destruct Hconjr as [ts' [Hnth Hsub2]].
      apply ety_subtyping with (t1s := (extr ++ ts')) (t2s := extr0).
      { by apply ety_a' => //; econstructor; eauto => //. }
      { eapply instr_subtyping_weaken1 with (tx1 := extr ++ extr1); eauto; by resolve_subtyping. }
    }
  - (* Frame_return *)
    eapply Lfilled_return_typing in Hetype; (try reflexivity); eauto.
    + invert_e_typing.
      by resolve_e_typing.
    + by apply v_to_e_const.
  - rewrite size_cat /= addn1 subn1 drop_size_cat in Hsub.
    rewrite size_cat /= addn1 subn1 take_size_cat in Hprincipal.
    instantiate (1 := extr).
    instantiate (1 := nil) => /=.
    Transparent instr_subtyping.
    unfold instr_subtyping.
    exists nil, nil, (extr ++ [::ts_value]), extr.
    repeat split => //=; by resolve_subtyping.
  Unshelve.
  all: try by resolve_subtyping.
Qed.
Opaque instr_subtyping.

(* Various properties preserved by a store extension *)
Lemma ext_func_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_func_typing s a = Some tf ->
    ext_func_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_func_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_func in Hoption; eauto.
  by rewrite Hoption.
Qed.

Lemma ext_table_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_table_typing s a = Some tf ->
    exists tf', ext_table_typing s' a = Some tf' /\
    table_type_extension tf tf'.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_table_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_table in Hoption; last by apply Hext.
  destruct Hoption as [tab [Hnth Htableext]].
  rewrite Hnth.
  unfold table_extension in Htableext.
  by remove_bools_options; exists (tableinst_type tab).
Qed.

Lemma ext_mem_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_mem_typing s a = Some tf ->
    exists tf', ext_mem_typing s' a = Some tf' /\
    limits_extension tf tf'.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_mem_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_mem in Hoption; last by apply Hext.
  destruct Hoption as [mem [Hnth Hmemext]].
  rewrite Hnth.
  unfold mem_extension in Hmemext.
  by remove_bools_options; exists (meminst_type mem).
Qed.

Lemma ext_global_typing_extension: forall s s' a tf,
    store_extension s s' ->
    ext_global_typing s a = Some tf ->
    ext_global_typing s' a = Some tf.
Proof.
  move => s s' a tf Hext Htype.
  unfold ext_global_typing in *.
  remove_bools_options.
  eapply store_extension_lookup_global in Hoption; eauto.
  destruct Hoption as [? [Hnth Hglobalext]].
  rewrite Hnth.
  unfold global_extension in Hglobalext.
  remove_bools_options.
  by rewrite H.
Qed.

Lemma typeof_ref_extension: forall s s' v t,
    store_extension s s' ->
    typeof_ref s v = Some t ->
    typeof_ref s' v = Some t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  - remove_bools_options.
    eapply ext_func_typing_extension in Hoption; eauto.
    by rewrite Hoption.
  - remove_bools_options.
    eapply store_extension_lookup_exn in Hoption; eauto.
    by rewrite Hoption.
Qed.
  
Lemma value_typing_extension: forall s s' v t,
    store_extension s s' ->
    value_typing s v t ->
    value_typing s' v t.
Proof.
  move => s s' v t Hext Htype.
  destruct v; simpl in * => //=.
  remove_bools_options.
  unfold value_typing in *; simpl in *; remove_bools_options.
  eapply typeof_ref_extension in Hoption0; eauto.
  by rewrite Hoption0.
Qed.
  
Lemma values_typing_extension: forall s s' vs ts,
    store_extension s s' ->
    values_typing s vs ts ->
    values_typing s' vs ts.
Proof.
  move => s s'; elim => //=.
  move => v vs IH => //=; case.
  - move => HST Hvt => //=; by apply values_typing_length in Hvt.
  - move => t ts Hext Hvt; unfold values_typing => /=.
    remove_bools_options.
    by erewrite value_typing_extension; eauto.
Qed.  

Lemma eleminst_typing_extension: forall s s' a a' tf,
    store_extension s s' ->
    elem_extension a a' ->
    eleminst_typing s a = Some tf ->
    eleminst_typing s' a' = Some tf.
Proof.
  move => s s' [et ei] [et' ei'] tf Hsext Hext Htype.
  unfold eleminst_typing in *.
  unfold elem_extension in *.
  move: ei' Hext.
  induction ei; move => ei' Hext; simpl in *; remove_bools_options => //=.
  erewrite value_typing_extension; (try by apply Hsext) => //=.
  apply IHei; first by rewrite H2.
  repeat rewrite eq_refl.
  by lias.
Qed.
  
Lemma datainst_typing_extension: forall s s' a a' tf,
    store_extension s s' ->
    data_extension a a' ->
    datainst_typing s a = Some tf ->
    datainst_typing s' a' = Some tf.
Proof.
  move => s s' d tf Hext Htype.
  by unfold datainst_typing in *.
Qed.

Lemma those_map_impl {T T1 T2: Type}: forall f g (r: T1 -> T2 -> bool) (l: list T) (l': list T1),
    (forall x y, f x = Some y -> exists z, g x = Some z /\ r y z) ->
    those (map f l) = Some l' ->
    exists l'', those (map g l) = Some l'' /\ all2 r l' l''.
Proof.
  move => f g r.
  setoid_rewrite <- those_those0.
  elim => //=; first by case => //; exists nil.
  move => x l IH l' Hr Hf.
  remove_bools_options.
  specialize (Hr x t Hoption) as Hz; destruct Hz as [z [Hg Hryz]].
  specialize (IH l0 Hr erefl) as Hl''; destruct Hl'' as [l'' [Hthose Hrall]].
  exists (z :: l'') => /=.
  by rewrite Hg Hthose Hryz Hrall => /=.
Qed.

Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i = Some C ->
    exists C',
      inst_typing s' i = Some C' /\
      context_extension C C'.
Proof.
  move => s s' i C HST HIT.
  unfold inst_typing in *.
  destruct i.
  remove_bools_options.
  (* Functions *)
  eapply those_map_impl in Hoption; last first.
  { move => x y Hext.
    exists y; eapply ext_func_typing_extension in Hext; eauto.
    split; first by apply Hext.
    by apply eq_refl.
  }
  destruct Hoption as [tfs [Hthosef Hfeq]]; rewrite Hthosef.
  rewrite -eqseq_all in Hfeq; move/eqP in Hfeq; subst.
  (* Tables *)
  eapply those_map_impl in Hoption0; last first.
  { move => x y Hext.
    by eapply ext_table_typing_extension in Hext; eauto.
  }
  destruct Hoption0 as [tts [Hthoset Htr]]; rewrite Hthoset.
  (* Memories *)
  eapply those_map_impl in Hoption1; last first.
  { move => x y Hext.
    by eapply ext_mem_typing_extension in Hext; eauto.
  }
  destruct Hoption1 as [tms [Hthosem Hmr]]; rewrite Hthosem.
  (* Globals *)
  eapply those_map_impl in Hoption2; last first.
  { move => x y Hext.
    exists y; eapply ext_global_typing_extension in Hext; eauto.
    split; first by apply Hext.
    by apply eq_refl.
  }
  destruct Hoption2 as [tgs [Hthoseg Hgeq]]; rewrite Hthoseg.
  rewrite -eqseq_all in Hgeq; move/eqP in Hgeq; subst.
  (* Elems *)
  eapply those_map_impl in Hoption3; last first.
  { move => x y Hext.
    instantiate (3 := fun x =>
                        match lookup_N (s_elems s') x with
                        | Some ei => eleminst_typing s' ei
                        | None => None
                        end
                ).
    remove_bools_options.
    eapply store_extension_lookup_elem in Hoption; eauto.
    destruct Hoption as [elem [Hnth Helemext]].
    eapply eleminst_typing_extension in Helemext; eauto.
    exists y; split; last by apply eq_refl.
    by rewrite Hnth /= Helemext.
  }
  destruct Hoption3 as [tes [Hthosee Heeq]]; rewrite Hthosee.
  rewrite -eqseq_all in Heeq; move/eqP in Heeq; subst.
  (* Datas *)
  eapply those_map_impl in Hoption4; last first.
  { move => x y Hext.
    instantiate (3 := fun x =>
                        match lookup_N (s_datas s') x with
                        | Some ei => datainst_typing s' ei
                        | None => None
                        end
                ).
    remove_bools_options.
    eapply store_extension_lookup_data in Hoption; eauto.
    destruct Hoption as [data [Hnth Hdataext]].
    eapply datainst_typing_extension in Hdataext; eauto.
    exists y; split; last by apply eq_refl.
    by rewrite Hnth /= Hdataext.
  }
  destruct Hoption4 as [tds [Hthosed Hdeq]]; rewrite Hthosed.
  rewrite -eqseq_all in Hdeq; move/eqP in Hdeq; subst.
  (* Tags are immutable and retain their exact parameter types. *)
  eapply those_map_impl in Hoption5; last first.
  { move => x y Hlookup.
    instantiate (3 := lookup_N (s_tags s')).
    exists y; split; first by eapply store_extension_lookup_tag; eauto.
    by apply eq_refl.
  }
  destruct Hoption5 as [jts [Hthosej Hjeq]]; rewrite Hthosej.
  rewrite -eqseq_all in Hjeq; move/eqP in Hjeq; subst.
  eexists; split; first by eauto.
  unfold context_extension => /=; repeat rewrite eq_refl => /=.
  by rewrite Htr Hmr.
Qed.  

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    exists C',
      frame_typing s' f C' /\
      context_extension C C'.
Proof.
  move => s s' f C HST HIT.
  unfold frame_typing in *.
  remove_bools_options.
  destruct HIT as [ts [-> Hvts]].
  specialize (inst_typing_extension HST Hoption) as [C' [Hit Hext]].
  erewrite -> inst_t_context_local_empty in *; eauto.
  rewrite cats0.
  exists (upd_local C' ts); split => //.
  - rewrite Hit.
    exists ts.
    eapply values_typing_extension in Hvts; eauto.
    rewrite Hvts.
    by erewrite inst_t_context_local_empty; eauto; by rewrite cats0.
  - unfold context_extension in *.
    by lias.
Qed.

(* If a program fragment enclosed can be well-typed when enclosed in a
   lh context, then it can be fragment-well-typed on its own with a
   corresponding update on the typing context. *)
Lemma lfilled_es_type_exists {k}: forall (lh: lholed k) es les s C tf,
    lfill lh es = les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  elim.
  - move => vs es es' LI s C [ts1 ts2] <- /= Htype.
    invert_e_typing.
    exists (tc_labels C); repeat eexists => //=.
    uapply H1_comp0.
    by destruct C.
  - move => k' vs n es lh IH es' es'' LI s C [ts1 ts2] <- /= Htype.
    rewrite -cat1s in Htype.
    invert_e_typing.
    by edestruct IH; eauto.
  - move => k' vs n cs lh IH es' es'' LI s C [ts1 ts2] <- /= Htype.
    rewrite -cat1s in Htype.
    invert_e_typing.
    by edestruct IH; eauto.
Qed.

Lemma update_label_agree C C' lab:
  context_agree C C' ->
  context_agree (upd_label C lab) (upd_label C' lab).
Proof.
  unfold context_agree in *; destruct C, C'; simpl in *; intros; remove_bools_options; subst.
  by lias.
Qed.

Lemma context_agree_func_type C C' n ft:
  context_agree C C' ->
  lookup_N C.(tc_funcs) n = Some ft ->
  lookup_N C'.(tc_funcs) n = Some ft.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  eapply all2_nth_impl in H9 as [ft' [Hnth' Hfext]]; eauto.
  by unfold func_agree in Hfext; remove_bools_options; subst.
Qed.
  
Lemma context_agree_table_type C C' n tabt:
  context_agree C C' ->
  lookup_N C.(tc_tables) n = Some tabt ->
  exists tabt', lookup_N C'.(tc_tables) n = Some tabt' /\
             table_agree tabt tabt'.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  by eapply all2_nth_impl in H8 as [tabt' [Hnth' Htabext]]; eauto.
Qed.

Lemma context_agree_mem_type C C' n memt:
  context_agree C C' ->
  lookup_N C.(tc_mems) n = Some memt ->
  exists memt',
    lookup_N C'.(tc_mems) n = Some memt' /\
    mem_agree memt memt'.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  by eapply all2_nth_impl in H7 as [memt' [Hnth' Hmemext]]; eauto.
Qed.

Lemma context_agree_global_type C C' n gt:
  context_agree C C' ->
  lookup_N C.(tc_globals) n = Some gt ->
  lookup_N C'.(tc_globals) n = Some gt.
Proof.
  move => Hext Hnth.
  unfold context_agree in Hext; remove_bools_options.
  unfold lookup_N in *.
  eapply all2_nth_impl in H6 as [gt' [Hnth' Hfext]]; eauto.
  by unfold global_agree in Hfext; remove_bools_options; subst.
Qed.

Lemma catch_clause_context_agree C C' c :
  context_agree C C' ->
  catch_clause_typing C c = catch_clause_typing C' c.
Proof.
  move => Hagree.
  pose proof (context_agree_tags Hagree) as Htags.
  assert (Hlabels: tc_labels C = tc_labels C').
  { unfold context_agree in Hagree; remove_bools_options; done. }
  destruct c; unfold catch_clause_typing; by rewrite Hlabels ?Htags.
Qed.

Ltac rewrite_context_agree:=
  repeat match goal with
    | Hext: is_true (context_agree ?C ?C') |-
      context [ all (catch_clause_typing ?C') ?cs ] =>
        rewrite -(eq_all (fun c => catch_clause_context_agree c Hext))
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_tags ?C' ] =>
        replace (tc_tags C') with (tc_tags C) => //; eauto;
          last by apply context_agree_tags
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_types ?C' ] =>
        replace (tc_types C') with (tc_types C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_elems ?C' ] =>
        replace (tc_elems C') with (tc_elems C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_datas ?C' ] =>
        replace (tc_datas C') with (tc_datas C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_locals ?C' ] =>
        replace (tc_locals C') with (tc_locals C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_labels ?C' ] =>
        replace (tc_labels C') with (tc_labels C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_return ?C' ] =>
        replace (tc_return C') with (tc_return C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | Hext: is_true (context_agree ?C ?C') |-
      context [ tc_refs ?C' ] =>
        replace (tc_refs C') with (tc_refs C) => //; eauto; last by unfold context_agree in Hext; remove_bools_options; destruct C, C'; lias
    | _ : is_true (context_agree ?C ?C') |- is_true (context_agree (upd_label ?C ?lab) (upd_label ?C' ?lab)) =>
        by apply update_label_agree
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C'.(tc_tables) ?n = Some ?t,
      Helemtype: (tt_elem_type ?t) = ?tref |- _ =>
      let Htableagree := fresh "Htableagree" in
      specialize (context_agree_table_type Hext Hnth) as [tabt_ctxext [Hnth_ctxext Htableagree]]; unfold table_agree in Htableagree; remove_bools_options; subst; try rewrite - Htableagree
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_tables) ?n = Some ?t |- _ =>
      specialize (context_agree_table_type Hext Hnth) as [tabt_ctxext [Hnth_ctxext Htableagree]]; unfold table_agree in *; remove_bools_options; subst
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_mems) ?n = Some ?t |- _ =>
      (* Not creating fresh names to make sure this only triggers once -- a bit stupid *)
      specialize (context_agree_mem_type Hext Hnth) as [memt_ctxext [Hnth_ctxext Hmemagree]]
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_funcs) ?n = Some ?t |- _ =>
      specialize (context_agree_func_type Hext Hnth) as Hnthfunc'
    | Hext : is_true (context_agree ?C ?C'),
      Hnth : lookup_N ?C.(tc_globals) ?n = Some ?t |- _ =>
      specialize (context_agree_global_type Hext Hnth) as Hnthglobal'
    end.

(* Curiously, this lemma works in both directions *)
Lemma context_agree_be_typing: forall C C' es tf,
    context_agree C C' ->
    be_typing C es tf ->
    be_typing C' es tf.
Proof.
  move => C C' es tf Hext Hetype.
  move: C' Hext.
  induction Hetype; move => C' Hext; (try by econstructor; eauto); try (by econstructor; eauto; rewrite_context_agree; eauto); try (by rewrite_context_agree; econstructor; eauto; rewrite_context_agree).
  (* block *)
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    by apply IHHetype; rewrite_context_agree.
  (* loop *)
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    by apply IHHetype; by rewrite_context_agree.
  (* if *)
  - econstructor; eauto; unfold expand_t in *; rewrite_context_agree.
    + apply IHHetype1; by rewrite_context_agree.
    + apply IHHetype2; by rewrite_context_agree.
  (* try_table *)
  - eapply bet_try_table.
    + unfold expand_t in *; by rewrite_context_agree.
    + rewrite_context_agree; eauto.
    + apply IHHetype; by rewrite_context_agree.
  (* call_indirect *)
  - rewrite_context_agree.
    econstructor; eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
  (* return_call_indirect *)
  - rewrite_context_agree.
    econstructor; eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
    + by rewrite_context_agree.
  (* table_copy *)
  - rewrite_context_agree.
    eapply context_agree_table_type in H as [tabt [Hnth Hagree]]; eauto; unfold table_agree in *; move/eqP in Hagree.
    econstructor.
    + by apply Hnth.
    + reflexivity.
    + by apply Hnth_ctxext.
    + by rewrite - Hagree - H2.
  (* table init *)
  - rewrite_context_agree.
    econstructor; first by eauto.
    + by rewrite - Htableagree.
    + by rewrite_context_agree.
Qed.

(* Two agreeing contexts respect typing of each other *)
Lemma context_agree_typing: forall s C C' es tf,
    context_agree C C' ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es tf Hext Hetype.
  move: C' Hext.
  induction Hetype; subst; move => C' Hext; try by econstructor; eauto.
  - (* be *)
    apply ety_a.
    by eapply context_agree_be_typing; eauto.
   - (* Handler *)
     eapply ety_handler; eauto.
     by rewrite_context_agree.
   - (* Return_invoke *)
    eapply ety_return_invoke; eauto.
    by rewrite_context_agree.
  - (* Label *)
    eapply ety_label; eauto.
    eapply IHHetype2.
    by rewrite_context_agree.
Qed.

(* Context extension is a special case of context agreement. *)
Lemma context_extension_typing: forall s C C' es tf,
    context_extension C C' ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  intros.
  eapply context_agree_typing; last by eauto.
  by apply context_extension_agree.
Qed.

(* A valid store extension preserves the fragment typing relation. *)
Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es tf ->
    e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 HST2 Hext HType. move: s' HST1 HST2 Hext.
  eapply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_typing s' ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs th ts (_ : thread_typing s rs th ts) => forall s',
             store_typing s ->
             store_typing s' ->
             store_extension s s' ->
             thread_typing s' rs th ts); clear HType s C es tf.
  (* basic *)
  - move=> s C bes tf HType s' HST1 HST2 Hext.
    apply ety_a'; first by apply to_e_list_basic.
    replace (to_b_list (to_e_list bes)) with bes => //; last by apply b_e_elim.
  (* composition *)
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  (* subtyping *)
  - move=> s C es t1s t2s t1s' t2s' HType IHHType Hsub s' HST1 HST2 Hext.
    by eapply ety_subtyping; eauto.
  (* trap *)
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_trap.
  (* exception *)
  - move=> s C a ex tf Hlookup s' HST1 HST2 Hext.
    eapply ety_raise.
    by eapply store_extension_lookup_exn; eauto.
  (* ref_extern *)
  - move=> s C n cs es ts Hcatches Hbody IHbody Hlen s' HST1 HST2 Hext.
    eapply ety_handler; eauto.
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_ref_extern.
  (* ref *)
  - move=> s C a ex Hlookup s' HST1 HST2 Hext.
    eapply ety_ref_exn.
    by eapply store_extension_lookup_exn; eauto.
  - move=> s C a tf Hextfunc s' HST1 HST2 Hext.
    eapply ety_ref; eauto.
    by eapply ext_func_typing_extension; eauto.
  (* invoke *)
  - move=> s a C tf Hextfunc s' HST1 HST2 Hext.
    eapply ety_invoke; eauto => //.
    by eapply ext_func_typing_extension; eauto.
  (* return_invoke *)
  - move => s a C ts1 ts2 ts3 ts4 Hextfunc Hret s' HST1 HST2 Hext.
    eapply ety_return_invoke; eauto.
    by eapply ext_func_typing_extension; eauto.
  (* Label *)
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 HST2 Hext.
    by eapply ety_label => //; eauto.
  (* Frame *)
  - move=> s C n f es ts HType IHHType E s' HST1 HST2 Hext.
    apply ety_frame => //.
    by eapply IHHType; try apply HST1 => //.
  (* Thread *)
  - move=> s f es rs ts C C' HFType HContext HType IHHType s' HST1 HST2 Hext.
    remove_bools_options.
    eapply frame_typing_extension in HFType; eauto.
    destruct HFType as [C'' [HFType Hcext]].
    eapply mk_thread_typing with (C := C''); eauto.
    apply context_extension_typing with (C := C') => //; last by apply IHHType.
    subst C'.
    unfold context_extension in *.
    by lias.
Qed.

Lemma glob_extension_update_nth: forall sglobs n g g',
  List.nth_error sglobs n = Some g ->
  global_extension g g' ->
  all2 global_extension sglobs (set_nth g' sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_global_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + by apply global_extension_refl. 
    + by eapply IHn; eauto.
Qed.

Lemma write_bytes_gen_preserve_length: forall m pos len gen m',
  write_bytes_gen m pos len gen = Some m' ->
  memory.mem_length m = memory.mem_length m'.
Proof.
  move => m pos len gen m' Hwrite.
  unfold write_bytes_gen in Hwrite.
  by apply mem_update_gen_length in Hwrite.
Qed.

Lemma write_bytes_meminst_preserve_type: forall m pos len gen m',
  write_bytes_gen_meminst m pos len gen = Some m' ->
  meminst_type m = meminst_type m' /\
  mem_length m = mem_length m'.
Proof.
  move => m pos len gen m' Hwrite.
  unfold write_bytes_gen_meminst in Hwrite.
  remove_bools_options; split => //=.
  by eapply write_bytes_gen_preserve_length; eauto.
Qed.

Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
Qed.

(** Interaction among instruction operations, store extensions, and types **)
Lemma context_extension_func_typing: forall C C' x t,
    context_extension C C' ->
    func_typing C x t ->
    func_typing C' x t.
Proof.
  move => C C' x t Hcext Hft.
  unfold func_typing in *; destruct x; remove_bools_options.
  specialize (context_extension_agree Hcext) as Hagree.
  rewrite_context_agree.
  rewrite Hoption.
  destruct f; destruct Hft as [-> [Het Hdefault]]; repeat split => //.
  eapply context_agree_be_typing; last by eauto.
  unfold context_agree in *; remove_bools_options; destruct C, C'; subst; by lias.
Qed.
  
Lemma store_extension_funcinst_typing: forall s s' x t,
    store_extension s s' ->
    funcinst_typing s x t ->
    funcinst_typing s' x t.
Proof.
  move => s s' x t Hst Hft.
  unfold funcinst_typing in *; destruct Hft as [<- Hft]; remove_bools_options; split => //.
  destruct x => //; destruct Hft as [? Hft]; split => //.
  remove_bools_options.
  eapply inst_typing_extension in Hoption; last by apply Hst.
  destruct Hoption as [C' [Hit' Hcext]].
  rewrite Hit'.
  unfold func_typing in *.
  by eapply context_extension_func_typing; eauto.
Qed.

Lemma store_extension_tableinst_typing: forall s s' x t,
    store_extension s s' ->
    tableinst_typing s x = Some t ->
    tableinst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold tableinst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  move/allP in Hif1.
  move/inP in Hin.
  apply Hif1 in Hin.
  by eapply value_typing_extension in Hin; eauto.
Qed.

Lemma store_extension_meminst_typing: forall s s' x t,
    store_extension s s' ->
    meminst_typing s x = Some t ->
    meminst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  by unfold meminst_typing in *; destruct x; remove_bools_options.
Qed.

Lemma store_extension_globalinst_typing: forall s s' x t,
    store_extension s s' ->
    globalinst_typing s x = Some t ->
    globalinst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold globalinst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  by eapply value_typing_extension; eauto.
Qed.

Lemma store_extension_eleminst_typing: forall s s' x t,
    store_extension s s' ->
    eleminst_typing s x = Some t ->
    eleminst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  unfold eleminst_typing in *; destruct x; remove_bools_options.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  move/allP in Hif.
  move/inP in Hin.
  apply Hif in Hin.
  move/eqP in Hin.
  remove_bools_options.
  by eapply value_typing_extension; eauto.
Qed.

Lemma store_extension_datainst_typing: forall s s' x t,
    store_extension s s' ->
    datainst_typing s x = Some t ->
    datainst_typing s' x = Some t.
Proof.
  move => s s' x t Hst Ht.
  by unfold datainst_typing in *; destruct x; remove_bools_options.
Qed.

Lemma store_extension_funcs_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, funcinst_typing s x t) xs ->
    List.Forall (fun x => exists t, funcinst_typing s' x t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_funcinst_typing; eauto.
Qed.

Lemma store_extension_tables_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, tableinst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, tableinst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_tableinst_typing; eauto.
Qed.

Lemma store_extension_mems_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, meminst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, meminst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_meminst_typing; eauto.
Qed.

Lemma store_extension_globals_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, globalinst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, globalinst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_globalinst_typing; eauto.
Qed.

Lemma store_extension_elems_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, eleminst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, eleminst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_eleminst_typing; eauto.
Qed.

Lemma store_extension_datas_typing: forall s s' xs,
    store_extension s s' ->
    List.Forall (fun x => exists t, datainst_typing s x = Some t) xs ->
    List.Forall (fun x => exists t, datainst_typing s' x = Some t) xs.
Proof.
  move => s s' xs Hst Hall.
  eapply List.Forall_impl; eauto.
  move => x /=[t Ht].
  by exists t; eapply store_extension_datainst_typing; eauto.
Qed.

Lemma exninst_typing_extension s s' e :
  store_extension s s' ->
  exninst_typing s e -> exninst_typing s' e.
Proof.
  move => Hext [ps [Htag Hfields]].
  exists ps; split.
  - by eapply store_extension_lookup_tag; eauto.
  - by eapply values_typing_extension; eauto.
Qed.

Lemma store_extension_exns_typing s s' es :
  store_extension s s' ->
  List.Forall (exninst_typing s) es ->
  List.Forall (exninst_typing s') es.
Proof.
  move => Hext Hall.
  eapply List.Forall_impl; last exact Hall.
  move => e Htype; by eapply exninst_typing_extension; eauto.
Qed.

Ltac resolve_store_extension :=
  repeat lazymatch goal with
  | |- context [ component_extension (@operations.func_extension _) ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := func_extension); last by apply func_extension_refl
  | |- context [ component_extension table_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := table_extension); last by apply table_extension_refl
  | |- context [ component_extension mem_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := mem_extension); last by apply mem_extension_refl
  | |- context [ component_extension global_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := global_extension); last by apply global_extension_refl
  | |- context [ component_extension elem_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := elem_extension); last by apply elem_extension_refl
  | |- context [ component_extension data_extension ?x ?x ] =>
      rewrite -> component_extension_same_refl with (f := data_extension); last by apply data_extension_refl
  | |- context [ component_extension (fun (ps ps': seq value_type) => ps == ps') ?x ?x ] =>
      rewrite -> component_extension_same_refl
        with (f := fun (ps ps': seq value_type) => ps == ps');
        last (let p := fresh "params" in move => p; by rewrite eq_refl)
  | |- context [ component_extension (fun (e e': exninst) => e == e') ?x ?x ] =>
      rewrite -> component_extension_same_refl
        with (f := fun (e e': exninst) => e == e');
        last (let ex := fresh "exception" in move => ex; by apply/eqexninstP)
    | _ => repeat rewrite andbT
    end; cbn.

Ltac resolve_store_typing :=
  repeat match goal with
  | H: _ /\ _ |- _ =>
      let H' := fresh "Hcomponent" in destruct H as [H H']
  end;
  repeat split;
  repeat lazymatch goal with
  | |- List.Forall (fun x => exists t, funcinst_typing ?s x t) _ =>
      by eapply store_extension_funcs_typing; eauto
  | |- List.Forall (fun x => exists t, tableinst_typing ?s x = Some t) _ =>
      by eapply store_extension_tables_typing; eauto
  | |- List.Forall (fun x => exists t, meminst_typing ?s x = Some t) _ =>
      by eapply store_extension_mems_typing; eauto
  | |- List.Forall (fun x => exists t, globalinst_typing ?s x = Some t) _ =>
      by eapply store_extension_globals_typing; eauto
  | |- List.Forall (fun x => exists t, eleminst_typing ?s x = Some t) _ =>
      by eapply store_extension_elems_typing; eauto
  | |- List.Forall (fun x => exists t, datainst_typing ?s x = Some t) _ =>
      by eapply store_extension_datas_typing; eauto
  | |- List.Forall (exninst_typing ?s) _ =>
      by eapply store_extension_exns_typing; eauto
    end.

Lemma alloc_exn_extension s e :
  store_extension s (fst (alloc_exn s e)).
Proof.
  unfold alloc_exn, upd_s_exns, store_extension => /=.
  resolve_store_extension.
  change (component_extension (fun (x y: exninst) => x == y)
            s.(s_exns) (s.(s_exns) ++ [::e])).
  eapply component_extension_extend; first reflexivity.
  move => l; apply reflexive_all2_same; move => x; by rewrite eq_refl.
Qed.

Lemma alloc_exn_typing s e :
  store_typing s -> exninst_typing s e ->
  store_typing (fst (alloc_exn s e)).
Proof.
  move => Hstore He.
  pose proof (alloc_exn_extension s e) as Hext.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hstore as [Hfs [Hts [Hms [Hgs [Hes [Hds Hxs]]]]]].
  repeat split.
  - by eapply store_extension_funcs_typing; eauto.
  - by eapply store_extension_tables_typing; eauto.
  - by eapply store_extension_mems_typing; eauto.
  - by eapply store_extension_globals_typing; eauto.
  - by eapply store_extension_elems_typing; eauto.
  - by eapply store_extension_datas_typing; eauto.
  - apply List.Forall_app; split.
    + by eapply store_extension_exns_typing; eauto.
    + constructor; last constructor.
      by eapply exninst_typing_extension; eauto.
Qed.

Lemma alloc_exn_lookup s e :
  lookup_N (s_exns (fst (alloc_exn s e))) (snd (alloc_exn s e)) = Some e.
Proof.
  unfold alloc_exn, upd_s_exns, lookup_N => /=.
  rewrite Nnat.Nat2N.id List.nth_error_app2; last by lias.
  by rewrite Nat.sub_diag.
Qed.

Lemma supdate_glob_extension: forall s f i v s' C gt,
  store_typing s ->
  supdate_glob s (f_inst f) i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s v (tg_t gt) ->
  lookup_N (tc_globals C) i = Some gt ->
  is_mut gt ->
  store_extension s s'.
Proof.
  move => s f i v s' C gt Hst Hupd Hinst Hvaltype Hnth Hmut.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct g0.
  remove_bools_options.
  move/eqP in Hif0.
  eapply component_extension_update; eauto; first by apply global_extension_refl.
  unfold global_extension => /=.
  rewrite eq_refl => /=.
  destruct gt0.
  apply/orP; left; apply/eqP.
  simpl in *.
  rewrite Hnthgt in Hnth.
  injection Hnth as <-.
  unfold is_mut in *; simpl in *; by move/eqP in Hmut.
Qed.

Lemma supdate_glob_typing: forall s f i v s' C gt,
  store_typing s ->
  supdate_glob s (f_inst f) i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s v (tg_t gt) ->
  lookup_N (tc_globals C) i = Some gt ->
  is_mut gt ->
  store_typing s'.
Proof.
  move => s f i v s' C gt Hst Hupd Hinst Hvaltype Hnth Hmut.
  assert (store_extension s s') as Hstext; first by eapply supdate_glob_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct g0; remove_bools_options; simpl in *.
  rewrite Hnthgt in Hnth; injection Hnth as ->.
  eapply value_typing_extension in Hvaltype; eauto.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Het Hdt.
  eapply Forall_set; eauto; last by apply nth_error_Some_length in Hoption1; lias.
  eapply Forall_lookup in Hoption1; eauto; simpl in *.
  destruct Hoption1 as [t' Ht]; remove_bools_options.
  exists t'; rewrite Hvaltype.
  by resolve_subtyping.
Qed.
    
Lemma stab_update_extension: forall s f x i v s' C tabt,
  store_typing s ->
  stab_update s (f_inst f) x i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_extension s s'.
Proof.
  move => s f x i v s' C tabt Hst Hupd Hinst Hvaltype Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct t0; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply table_extension_refl.
  unfold table_extension, table_type_extension, limits_extension => /=; rewrite eq_refl => /=.
  apply/andP; split; first by lias.
  unfold tab_size in *; simpl in *.
  erewrite nth_error_set_nth_length => //.
  apply nth_error_nth with (x := (VAL_ref_null HT_func)).
  move/N.ltb_spec0 in Hif.
  by lias.
Qed.

Lemma stab_update_typing: forall s f x i v s' C tabt,
  store_typing s ->
  stab_update s (f_inst f) x i v = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_typing s'.
Proof.
  move => s f x i v s' C tabt Hst Hupd Hinst Hvaltype Hnth.
  assert (store_extension s s') as Hstext; first by eapply stab_update_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct t0; remove_bools_options; simpl in *.
  rewrite Hnthtabt in Hnth; injection Hnth as ->.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Hmt Hgt Het Hdt.
  eapply Forall_set; eauto; last by apply nth_error_Some_length in Hoption1; lias.
  eapply Forall_lookup in Hoption1; eauto; simpl in *.
  destruct Hoption1 as [vt Ht]; remove_bools_options.
  unfold tab_size in *; simpl in *.
  erewrite set_nth_length; last by lias.
  move/eqP in Hif4.
  rewrite Hif4 eq_refl.
  exists vt.
  resolve_if_true_eq.
  apply list_all_forall.
  move => a Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m [Hneq Hnth]]].
  - by eapply value_typing_extension in Hvaltype; eauto.
  - eapply list_all_forall in Hif5; eauto.
    + by apply List.nth_error_In in Hnth.
    + by lias.
Qed.

Lemma stab_grow_extension: forall s f x i v s' sz C tabt,
  store_typing s ->
  stab_grow s (f_inst f) x i v = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_extension s s'.
Proof.
  move => s f x i v s' sz C tabt Hst Hupd Hinst Hvaltype Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct t0, tabt0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply table_extension_refl.
  unfold table_extension, table_type_extension, limits_extension => /=; repeat rewrite eq_refl => /=.
  clear Hif Hif3.
  move/eqP in Hif1; rewrite - Hif1.
  unfold tab_size in *; simpl in *.
  do 2 (try (apply/andP; split => //)); try by lias.
  rewrite List.length_app List.repeat_length.
  by lias.
Qed.

Lemma stab_grow_typing: forall s f x i v s' sz C tabt,
  store_typing s ->
  stab_grow s (f_inst f) x i v = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  value_typing s (VAL_ref v) (T_ref (tt_elem_type tabt)) ->
  lookup_N (tc_tables C) x = Some tabt ->
  store_typing s'.
Proof.
  move => s f x i v s' sz C tabt Hst Hupd Hinst Hvaltype Hnth.
  assert (store_extension s s') as Hstext; first by eapply stab_grow_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct t0, tabt0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthtabt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Hmt Hgt Het Hdt.
  unfold tab_size in *; simpl in *.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m [Hneq Hnth]]].
  - unfold tableinst_typing => /=.
    exists (Build_table_type (Build_limits (N.of_nat (length tableinst_elem) + i)%N (lim_max tt_limits)) tt_elem_type).
    unfold tabletype_valid => /=.
    rewrite Hif3 List.length_app List.repeat_length.
    replace (_ == _) with true; last first.
    { symmetry; apply/eqP. by lias. }
    { move/andP: Hif0 => [Hnullable _].
      rewrite Hnullable /=.
      resolve_if_true_eq.
      rewrite all_cat.
      apply/andP; split => //.
      apply all_repeat.
      by eapply value_typing_extension in Hvaltype; try by apply Hstext.
    }
  - eapply List.Forall_forall in Htt; eauto.
    + by apply List.nth_error_In in Hnth.
    + by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma selem_drop_extension: forall s f x s' C tref,
  store_typing s ->
  selem_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_elems C) x = Some tref ->
  store_extension s s'.
Proof.
  move => s f x s' C tref Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  destruct e0; simpl in *; remove_bools_options; simpl in *.
  resolve_store_extension.
  eapply component_extension_update; eauto; first by apply elem_extension_refl.
  unfold elem_extension => /=; repeat rewrite eq_refl => /=.
  rewrite Hnth in Hnthet; injection Hnthet as <-.
  rewrite Hoption0 in Hnthselem; injection Hnthselem as <-.
  by lias.
Qed.

Lemma selem_drop_typing: forall s f x s' C tref,
  store_typing s ->
  selem_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_elems C) x = Some tref ->
  store_typing s'.
Proof.
  move => s f x s' C tref Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply selem_drop_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct e0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthselem in Hoption0; injection Hoption0 as ->.
  rewrite Hnth in Hnthet; injection Hnthet as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Hgt Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m [Hneq Hnth']]] => //=; first by exists tref.
  - eapply List.Forall_forall in Het; eauto.
    + by apply List.nth_error_In in Hnth'.
    + by apply nth_error_Some_length in Hnthselem; lias.
Qed.

Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (serialise_num v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  remove_bools_options.
  apply write_bytes_meminst_preserve_type in HStore as [Htype Hlen].
  apply/andP; split; last by lias.
  destruct m, mem.
  unfold limits_extension.
  simpl in *; subst.
  by lias.
Qed.

Lemma mem_extension_store_vec: forall m n v marg mem,
    store_vec m n v marg = Some mem ->
    mem_extension m mem.
Proof.
  move => m n v marg mem HStore.
  unfold mem_extension.
  unfold store_vec in HStore.
  remove_bools_options.
  apply write_bytes_meminst_preserve_type in HStore as [Htype Hlen].
  apply/andP; split; last by lias.
  destruct m, mem.
  unfold limits_extension.
  simpl in *; subst.
  by lias.
Qed.

Lemma mem_extension_store_vec_lane: forall m n v width marg x mem,
    store_vec_lane m n v width marg x = Some mem ->
    mem_extension m mem.
Proof.
  move => m n v width marg x mem HStore.
  unfold mem_extension.
  unfold store_vec_lane in HStore.
  remove_bools_options.
  apply write_bytes_meminst_preserve_type in HStore as [Htype Hlen].
  apply/andP; split; last by lias.
  destruct m, mem.
  unfold limits_extension.
  simpl in *; subst.
  by lias.
Qed.
  
Lemma mem_extension_grow: forall s m c mem t,
    meminst_typing s m = Some t ->
    mem_grow m c = (Some mem) ->
    mem_extension m mem /\
      exists mt, meminst_typing s mem = Some mt.
Proof.
  move => s m c mem t Htype HMGrow.
  unfold meminst_typing in Htype; destruct m.
  remove_bools_options.
  unfold mem_extension, limits_extension => /=.
  unfold mem_grow in HMGrow.
  unfold mem_size, mem_length in *.
  simpl in *.
  unfold memtype_valid, limit_valid_range in *.
  remove_bools_options; simpl in *; move/eqP in Hif0; rewrite Hif0.
  - split.
    + apply/andP; split.
      apply/andP; split => //.
      rewrite N.div_mul => //; by lias.
    + erewrite mem_grow_length; last by eauto.
      rewrite Hif0.
      by lias.
    + unfold memtype_valid, limit_valid_range => /=.
      resolve_if_true_eq => /=.
      { rewrite N.div_mul => //.
        rewrite H1.
        rewrite Hif0 in Hif1.
        rewrite N.div_mul in Hif1 => //.
        by lias.
      }
      { resolve_if_true_eq; last by eexists; eauto.
        unfold mem_length => /=.
        erewrite mem_grow_length; last by eauto.
        rewrite N.div_mul => //.
        by lias.
      }
  - split.
    + apply/andP; split.
      apply/andP; split => //.
      rewrite N.div_mul => //; by lias.
    + erewrite mem_grow_length; last by eauto.
      rewrite Hif0.
      by lias.
    + unfold memtype_valid, limit_valid_range => /=.
      resolve_if_true_eq => /=.
      { rewrite N.div_mul => //.
        rewrite Hif0 in Hif.
        rewrite N.div_mul in Hif => //.
        by lias.
      }
      { resolve_if_true_eq; last by eexists; eauto.
        unfold mem_length => /=.
        erewrite mem_grow_length; last by eauto.
        rewrite N.div_mul => //.
        by lias.
      }
Qed.

Lemma smem_store_extension: forall s f n off v s' C t mt,
  store_typing s ->
  smem_store s (f_inst f) n off v t = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n off v s' C t mt Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by apply mem_extension_store in Hoption1.
Qed.

Lemma smem_store_typing: forall s f n off v s' C t mt,
  store_typing s ->
  smem_store s (f_inst f) n off v t = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n off v s' C t mt Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_store_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    + by apply List.nth_error_In in Hnth'.
    + by apply nth_error_Some_length in Hoption2; lias.
Qed.

(* Currently same as store *)
Lemma smem_store_packed_extension: forall s f n off v tp s' C mt,
  store_typing s ->
  smem_store_packed s (f_inst f) n off v tp = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n off v tp s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by apply mem_extension_store in Hoption1.
Qed.

(* Currently store_packed is the same as store *)
Lemma smem_store_packed_typing: forall s f n off v tp s' C mt,
  store_typing s ->
  smem_store_packed s (f_inst f) n off v tp = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n off v tp s' C a Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_store_packed_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_packed, store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
  - by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_store_vec_extension: forall s f n v marg s' C mt,
  store_typing s ->
  smem_store_vec s (f_inst f) n v marg = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n v marg s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by eapply mem_extension_store_vec in Hoption1.
Qed.

Lemma smem_store_vec_typing: forall s f n v marg s' C mt,
  store_typing s ->
  smem_store_vec s (f_inst f) n v marg = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n v marg s' C a Hst Hupd Hit Hnth.

  assert (store_extension s s') as Hstext; first by eapply smem_store_vec_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_vec, store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
  - by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_store_vec_lane_extension: forall s f n v width marg x s' C mt,
  store_typing s ->
  smem_store_vec_lane s (f_inst f) n v width marg x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n v width marg x s' C a Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  by eapply mem_extension_store_vec_lane in Hoption1.
Qed.

Lemma smem_store_vec_lane_typing: forall s f n v width marg x s' C mt,
  store_typing s ->
  smem_store_vec_lane s (f_inst f) n v width marg x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n v width marg x s' C a Hst Hupd Hit Hnth.

  assert (store_extension s s') as Hstext; first by eapply smem_store_vec_lane_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - exists m1.(meminst_type).
    unfold meminst_typing => /=.
    destruct m1 => //=.
    unfold store_vec_lane, store in Hoption1; remove_bools_options.
    apply write_bytes_meminst_preserve_type in Hoption1; simpl in *.
    destruct Hoption1 as [-> Hmemlen].
    unfold mem_length in *; simpl in *.
    rewrite Hif.
    resolve_if_true_eq.
    by lias.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
  - by apply nth_error_Some_length in Hoption2; lias.
Qed.

Lemma smem_grow_extension: forall s f n s' sz C mt,
  store_typing s ->
  smem_grow s (f_inst f) n = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_extension s s'.
Proof.
  move => s f n s' sz C a Hst Hupd Hit Hnth.
  unfold smem_grow in Hupd.
  unfold store_extension => /=; remove_bools_options; resolve_store_inst_lookup => /=.
  resolve_store_extension.
  remove_bools_options.
  destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnth in Hnthmt; injection Hnthmt as ->.
  eapply component_extension_update; eauto; first by apply mem_extension_refl.
  eapply mem_extension_grow with (s := s) (t := mt) in Hoption1 as [??]; eauto.
  unfold meminst_typing.
  by rewrite Hif Hif0.
Qed.

Lemma smem_grow_typing: forall s f n s' sz C mt,
  store_typing s ->
  smem_grow s (f_inst f) n = Some (s', sz) ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_mems C) 0%N = Some mt ->
  store_typing s'.
Proof.
  move => s f n s' sz C a Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply smem_grow_extension; eauto.
  unfold smem_grow in Hupd; remove_bools_options.
  resolve_store_inst_lookup; destruct m0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthmt in Hnth; injection Hnth as <-.
  unfold store_typing in *; destruct s; simpl in *.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hgt Het Hdt.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin; last by apply nth_error_Some_length in Hoption2; lias.
  clear Hstext.
  destruct Hin as [-> | [m0 [Hneq Hnth']]] => //=.
  - eapply mem_extension_grow in Hoption1 as [??]; eauto.
    unfold meminst_typing.
    by rewrite Hif Hif0.
  - eapply List.Forall_forall in Hmt; eauto.
    by apply List.nth_error_In in Hnth'.
Qed.
    
Lemma sdata_drop_extension: forall s f x s' C t,
  store_typing s ->
  sdata_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_datas C) x = Some t ->
  store_extension s s'.
Proof.
  move => s f x s' C t Hst Hupd Hit Hnth.
  unfold store_extension; unfold_store_operations => /=; resolve_store_extension; resolve_store_inst_lookup; remove_bools_options => /=.
  rewrite Hoption0 in Hnthsdata; injection Hnthsdata as ->.
  rewrite Hnth in Hnthdt; injection Hnthdt as ->.
  eapply component_extension_update; eauto; first by apply data_extension_refl.
  unfold data_extension => /=; rewrite eq_refl. by lias.
Qed.

Lemma sdata_drop_typing: forall s f x s' C t,
  store_typing s ->
  sdata_drop s (f_inst f) x = Some s' ->
  inst_typing s (f_inst f) = Some C -> 
  lookup_N (tc_datas C) x = Some t ->
  store_typing s'.
Proof.
  move => s f x s' C t Hst Hupd Hit Hnth.
  assert (store_extension s s') as Hstext; first by eapply sdata_drop_extension; eauto.
  unfold_store_operations; remove_bools_options.
  resolve_store_inst_lookup; destruct d0; simpl in *; remove_bools_options; simpl in *.
  rewrite Hnthsdata in Hoption0; injection Hoption0 as ->.
  rewrite Hnth in Hnthdt; injection Hnthdt as <-.
  unfold store_typing in *; destruct s; simpl in *.
  unfold_store_operations; remove_bools_options.
  destruct Hst as [Hft [Htt [Hmt [Hgt [Het Hdt]]]]].
  resolve_store_typing; simpl in *; clear Hft Htt Hmt Hgt Het.
  apply List.Forall_forall.
  move => x0 Hin.
  apply set_nth_In in Hin; last by apply nth_error_Some_length in Hnthsdata; lias.
  destruct Hin as [-> | [m [Hneq Hnth']]] => //=.
  - exists tt.
    by unfold datainst_typing.
  - eapply List.Forall_forall in Hdt; eauto.
    by apply List.nth_error_In in Hnthsdata; eauto.
Qed.
    
(* Note that although config_typing gives a much stronger constraint on C', we allow much more flexibility here due to the need in inductive cases. *)
Lemma store_extension_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_extension s s'.
Proof.
  move => s f es s' f' es' C C' tf hs hs' HReduce.
  move: tf C C'.
  induction HReduce => //; subst; try (move => tf C C' HIT Hmatch HType HST; intros; destruct tf; invert_e_typing => //; (try by apply store_extension_same)).
  - (* Invoke host *)
    by eapply host_application_extension; eauto.
  - (* global_set *)
    unify_principal; simpl in Hsub; remove_bools_options.
    eapply supdate_glob_extension; eauto; first by resolve_value_principal_typing.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* table update *)
    unify_principal; simpl in Hsub; remove_bools_options.
    eapply stab_update_extension; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* table grow *)
    unify_principal; simpl in Hsub0; remove_bools_options.
    eapply stab_grow_extension; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* elem drop *)
    eapply selem_drop_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* memory store *)
    eapply smem_store_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_packed *)
    eapply smem_store_packed_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_vec *)
    eapply smem_store_vec_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_vec_lane *)
    eapply smem_store_vec_lane_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory grow *)
    eapply smem_grow_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* data drop *)
    eapply sdata_drop_extension; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab [t1s [t2s Hetype]]].
    by eapply IHHReduce in Hetype; eauto.
  - (* frame *)
    unfold frame_typing in Hframetype; remove_bools_options.
    destruct Hframetype as [ts [-> Hvaltype]].
    eapply IHHReduce in Hetype; eauto.
    by unfold inst_match; lias.
  - (* throw allocates an immutable exception instance *)
    by apply alloc_exn_extension.
  - (* handler body *)
    by eapply IHHReduce; eauto.
Qed.
    
Lemma store_typing_reduce: forall s f es s' f' es' C C' tf hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    store_typing s ->
    store_typing s'.
Proof.
  move => s f es s' f' es' C C' tf hs hs' HReduce.
  move: tf C C'.
  induction HReduce => //; subst;
    try (move => tf C C' HIT Hmatch HType HST; intros;
      destruct tf; invert_e_typing => //).
  - (* host call *)
    by eapply host_application_typing; eauto.
  - (* global_set *)
    unify_principal; simpl in Hsub; remove_bools_options.
    eapply supdate_glob_typing; eauto; first by resolve_value_principal_typing.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* table update *)
    unify_principal; simpl in Hsub; remove_bools_options.
    eapply stab_update_typing; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* table grow *)
    unify_principal; simpl in Hsub0; remove_bools_options.
    eapply stab_grow_typing; eauto; last by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
    by resolve_value_principal_typing.
  - (* elem drop *)
    eapply selem_drop_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* memory store *)
    eapply smem_store_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_packed *)
    eapply smem_store_packed_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_vec *)
    eapply smem_store_vec_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory store_vec *)
    eapply smem_store_vec_lane_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjl0; f_equal.
  - (* memory grow *)
    eapply smem_grow_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* data drop *)
    eapply sdata_drop_typing; eauto.
    by unfold inst_match in Hmatch; remove_bools_options; uapply Hconjr; f_equal.
  - (* label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab [t1s [t2s Hetype]]].
    by eapply IHHReduce in Hetype; eauto.
  - (* frame *)
    unfold frame_typing in Hframetype; remove_bools_options.
    destruct Hframetype as [ts [-> Hvaltype]].
    eapply IHHReduce in Hetype; eauto.
    by unfold inst_match; lias.
  - (* throw payloads have the declared tag parameters *)
    apply alloc_exn_typing => //.
    exists ps; split => //.
    destruct (inst_typing_tag_lookup HIT H) as [params [Hparams Hcontext]].
    rewrite H0 in Hparams; injection Hparams as <-.
    rewrite (inst_match_tags Hmatch) in Hcontext.
    rewrite Hcontext in Hconjr; injection Hconjr as <-.
    assert (Hsize: size ts_values = size ps).
    { pose proof (values_typing_size H2_values) as Hsizes.
      rewrite !length_is_size in H1; lias. }
    pose proof (instr_subtyping_suffix_prod_cons H1_values Htisub Hsize) as Hsub.
    by eapply values_typing_trans; eauto.
  - (* handler body *)
    by eapply IHHReduce; eauto.
Qed.

Lemma inst_typing_reduce: forall hs s f es hs' s' f' es' C C' tf,
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C' ->
    e_typing s C' es tf ->
    exists C', inst_typing s' f'.(f_inst) = Some C' /\ context_extension C C'.
Proof.
  move => hs s f es hs' s' f' es' C C' tf Hreduce Hst Hit Hmatch Htype.
  erewrite <- reduce_inst_unchanged; eauto.
  eapply inst_typing_extension; last by apply Hit.
  eapply store_extension_reduce in Hreduce; by eauto.
Qed.

(* A weakening of the store_extension_e_typing lemma, so that the new
   context only needs to be an extension of the old (instead of being equal).
*)
Lemma extensions_e_typing: forall s s' C C' es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    context_extension C C' ->
    e_typing s C es tf ->
    e_typing s' C' es tf.
Proof.
  move => s s' C C' es tf Hst1 Hst2 Hsext Hcext Hetype.
  eapply context_extension_typing; eauto.
  by eapply store_extension_e_typing in Hetype; eauto.
Qed.

Lemma result_e_type: forall r ts s C,
    result_types_agree s ts r ->
    e_typing s C (result_to_stack r) (Tf [::] ts).
Proof.
  move => r ts s C HResType.
  destruct r => /=; last by apply ety_trap.
  simpl in *.
  by apply et_values_typing.
Qed.

Lemma t_preservation_locs_type_aux: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Tf t1s t2s) ->
    values_typing s f.(f_locs) ts ->
    values_typing s f'.(f_locs) ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT.
  move: C0 t1s t2s.
  induction HReduce => //; move => C0 t1s' t2s' Hmatch Hlocs HType Hvaltype; invert_e_typing; try by eexists; rewrite Hvaltype; split => //; resolve_subtyping.
  - unify_principal.
    simpl in Hsub; remove_bools_options.
    rewrite H1.
    unfold values_typing in *.
    eapply all2_set_nth1; eauto; by resolve_value_principal_typing.
  - eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [ts1 [ts2 Hetype]]].
    by eapply IHHReduce; (try apply Hetype); eauto.
  - by eapply IHHReduce; eauto.
Qed.

Lemma upd_local_label_return_overwrite: forall C loc1 lab1 ret1 loc2 lab2 ret2,
    upd_local_label_return (upd_local_label_return C loc2 lab2 ret2) loc1 lab1 ret1 = upd_local_label_return C loc1 lab1 ret1.
Proof.
  done.
Qed.
  
Lemma t_preservation_locs_type: forall s f es s' f' es' C C0 ts t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    inst_typing s f.(f_inst) = Some C ->
    inst_match C C0 ->
    C0.(tc_locals) = ts ->
    e_typing s C0 es (Tf t1s t2s) ->
    values_typing s f.(f_locs) ts ->
    values_typing s' f'.(f_locs) ts.
Proof.
  move => s f es s' f' es' C C0 ts t1s t2s hs hs' HReduce HST HIT Hmatch Hlocs HType Hvaltype.
  eapply t_preservation_locs_type_aux in Hvaltype; eauto.
  eapply values_typing_extension in Hvaltype; eauto.
  by eapply store_extension_reduce; eauto.
Qed.

(* Auxiliary lemmas for dealing with tail call reduction premises *)
Lemma r_return_call_invert: forall hs s f i hs' s' f' a,
    reduce hs s f [:: AI_basic (BI_call i)] hs' s' f' [:: AI_invoke a] ->
    lookup_N (inst_funcs (f_inst f)) i = Some a.
Proof.
  move => hs s f i hs' s' f' a Hreduce.
  dependent induction Hreduce => //.
  - by inversion H.
  - by repeat (destruct ves => //).
  - destruct (lfill_singleton_invert H x) as [[? Hlheq] [-> ->]] => //.
    by apply IHHreduce.
Qed.

Lemma r_return_call_indirect_invert: forall hs s f v x y hs' s' f' a,
    reduce hs s f [:: $V v; AI_basic (BI_call_indirect x y)] hs' s' f' [:: AI_invoke a] ->
    exists cl i,
      $V v = $VN (VAL_int32 i) /\
        lookup_N (s_funcs s) a = Some cl /\
        lookup_N (inst_types (f_inst f)) y = Some (cl_type cl) /\
        stab_elem s (f_inst f) x (Wasm_int.N_of_uint i32m i) = Some (VAL_ref_func a).
Proof.
  move => hs s f v x y hs' s' f' a Hreduce.
  dependent induction Hreduce => //.
  - by inversion H.
  - by exists cl, i.
  - by repeat (destruct ves => //).
  - destruct (lfill_singleton_invert H x) as [[? Hlheq] [-> ->]] => //.
    + destruct v as [v|v|v] => //=; by destruct v.
    + by apply IHHreduce.
Qed.
  
Lemma handler_all_typing s C n l cs es tf :
  e_typing s C [::AI_handler n (Catch_all l :: cs) es] tf ->
  e_typing s C [::AI_basic (BI_br l)] tf.
Proof.
  destruct tf as [tin tout]; move => Htype.
  apply e_typing_inversion in Htype as [[args results] [Hsub Hprincipal]].
  simpl in Hprincipal.
  destruct Hprincipal as [ts [Heq [Hcatches [Hbody Hlen]]]].
  injection Heq as Heq1 Heq2; subst args results.
  simpl in Hcatches; remove_bools_options.
  destruct r => //.
  eapply ety_subtyping; last exact Hsub.
  apply ety_a with (bes := [::BI_br l]).
  by apply bet_br with (t1s := nil).
Qed.

(* Main preservation lemma *)
Lemma t_preservation_e: forall s f es s' f' es' tlocs C C' t1s t2s lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) = Some C ->
    inst_typing s' f'.(f_inst) = Some C' ->
    values_typing s f.(f_locs) tlocs ->
    e_typing s (upd_local_label_return C tlocs lab ret) es (Tf t1s t2s) ->
    e_typing s' (upd_local_label_return C' tlocs lab ret) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' tlocs C C' t1s t2s lab ret hs hs' HReduce.
  move: C C' ret lab t1s t2s tlocs.
  induction HReduce; move => C C' ret lab tx ty tlocs HST1 HST2 HIT1 HIT2 Hloctype HType; subst; try eauto.
  all: try (by apply ety_trap).
  all: try (by eapply ety_raise; apply alloc_exn_lookup).
  all: try (apply handler_all_typing in HType; exact HType).
  all: try invert_e_typing; simpl in *; unify_principal; resolve_e_typing => //.
  all: unfold_store_operations; resolve_store_inst_lookup; remove_bools_options => //=; simpl in *; simplify_multieq; unify_principal; resolve_e_typing.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Ref_func *)
    eapply inst_typing_func_lookup in H; eauto.
    destruct H as [tf [Hext Hnth]].
    simplify_multieq.
    by eapply ety_ref; eauto.
  - (* Block *)
    erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
    rewrite Hconjl0 in H; injection H as <- <-.
    specialize (values_typing_length H2_values) as Hlen.
    repeat rewrite length_is_size in H2.
    repeat rewrite length_is_size in Hlen.
    rewrite v_to_e_size in H2.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply ety_subtyping; last by apply Hsubi.
    {
      eapply ety_label; eauto; first by apply et_empty; resolve_subtyping.
      eapply et_composition'; eauto; resolve_e_typing; first reflexivity.
      eapply ety_a in Hconjr0; eauto.
      eapply ety_subtyping; eauto.
      eapply instr_subtyping_weaken1; eauto.
      by resolve_subtyping.
    }
  - (* Loop *)
    remember Hconjl0 as Het; clear HeqHet.
    erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
    rewrite Hconjl0 in H; injection H as <- <-.
    specialize (values_typing_length H2_values) as Hlen.
    repeat rewrite length_is_size in H2.
    repeat rewrite length_is_size in Hlen.
    rewrite v_to_e_size in H2.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply ety_subtyping; last by apply Hsubi.
    {
      eapply ety_label; eauto.
      { apply ety_a' => //=.
        by apply bet_loop; eauto.
      }
      { eapply et_composition'; eauto; resolve_e_typing; first reflexivity.
        eapply ety_a in Hconjr0; eauto.
        eapply ety_subtyping; eauto.
        eapply instr_subtyping_weaken1; eauto.
        by resolve_subtyping.
      }
    }
  - (* Call *)
    eapply inst_typing_func_lookup in H as [t0 [Hft Hnth]]; eauto.
    destruct (cl_type f0) as [ts1 ts2] eqn:Htf.
    simplify_multieq.
    by eapply ety_subtyping; eauto; first by apply ety_invoke; eauto.
  - (* Call_indirect *)
    destruct Hft as [<- ?].
    apply ety_invoke.
    { unfold ext_func_typing.
      by rewrite H0 -Hinj => //=.
    }
  - (* Return_call *)
    (* Due to the opsem being defined based on the corresponding reduction
    of call, this is now an inductive case. Same for Return_call_indirect below *)
    apply r_return_call_invert in HReduce.
    eapply inst_typing_func_lookup in HReduce as [[ts1 ts2] [Hft Hnth]]; eauto.
    rewrite Hconjl0 in Hnth; injection Hnth as <- <-.
    by eapply ety_return_invoke; eauto.
  - (* Return_call_indirect *)
    apply r_return_call_indirect_invert in HReduce.
    destruct HReduce as [cl [i [Hveq [Hnthfunc [Hnthinsttype Hstab]]]]].
    replace (size extr1 + (size extr + 1) - 1) with (size extr1 + size extr); last by lias.
    rewrite catA take_size_cat; last by rewrite size_cat.
    unfold stab_elem in Hstab.
    remove_bools_options.
    specialize (inst_typing_type_lookup y HIT1) as Hnthtypes.
    rewrite Hconjl2 in Hnthtypes.
    rewrite Hnthtypes in Hnthinsttype.
    injection Hnthinsttype as Hcltype.
    eapply ety_return_invoke with (ts2 := extr0); eauto.
    unfold ext_func_typing.
    by rewrite Hnthfunc Hcltype.
  - (* Invoke native *)
    destruct extr as [ts1' ts2'].
    destruct Hft as [<- [Hvalid Hftype]].
    simpl in Hftype; remove_bools_options; destruct f0.
    destruct Hftype as [Heq [Hetype _]].
    injection Heq as <- <-.
    unfold ext_func_typing in Hconjr.
    rewrite H in Hconjr; simpl in Hconjr; injection Hconjr as <- <-.
    specialize (values_typing_length H2_values) as Hlen.
    repeat rewrite length_is_size in H5.
    repeat rewrite length_is_size in Hlen.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply ety_subtyping; first apply ety_frame; try by eauto.
    econstructor.
    + unfold frame_typing => /=.
      rewrite Hoption.
      eexists; split; first done.
      specialize (values_typing_trans H2_values Hsubt) as Hvts.
      erewrite values_typing_cat; by [done | apply Hvts | eapply default_values_typing; eauto].
    + by erewrite -> inst_t_context_local_empty; eauto.
    + rewrite cats0.
      eapply ety_label; eauto.
      * eapply ety_subtyping with (t1s := nil) (t2s := nil); first apply et_empty; by resolve_subtyping.
      * apply ety_a with (s := s) in Hetype.
        uapply Hetype => /=.
        by erewrite inst_t_context_label_empty; eauto.
        
  - (* Invoke host *)
    unfold ext_func_typing in Hconjr.
    remove_bools_options; simpl in Hft; destruct Hft as [<- Hvalid].
    simpl cl_type in Htisub.
    assert (length vcs = length ts_values) as Hlen; first by apply values_typing_length in H2_values.
    rewrite - H3 in Hlen.
    repeat rewrite length_is_size in Hlen.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    clear H1_values Htisub.
    eapply values_typing_trans in H2_values; eauto.
    by eapply ety_subtyping; first apply result_e_type; first eapply host_application_respect; eauto.

  - (* Return_invoke *)
    eapply lfilled_es_type_exists in Hetype; eauto.
    destruct Hetype as [labs [ts1 [ts2 Hetype]]].
    invert_e_typing.
    injection Hconjr1 as <-.
    resolve_e_typing.
    eapply ety_subtyping; first by eapply ety_invoke; eauto.
    unfold ext_func_typing in Hconjl0.
    rewrite H H0 in Hconjl0.
    injection Hconjl0 as <- <-.
    eapply instr_subtyping_weaken1; first by apply instr_subtyping_eq.
    (* This almost seems impossible, but the subtyping relation can indeed be
derived from the two transitive pairs on the suffixes. Stated as an individual lemma. *)
    eapply instr_subtyping_suffix_prod_cons; eauto.
    repeat rewrite length_is_size in H4.
    rewrite v_to_e_size in H4.
    apply values_typing_size in H2_values.
    by lias.
  - (* Local_get *)
    unfold lookup_N in *.
    eapply all2_nth_impl in Hloctype; eauto.
    destruct Hloctype as [vt [Hvaltype Hnth]].
    simplify_multieq.
    by resolve_e_typing.
  - (* Global_get *)
    destruct g; remove_bools_options; simpl in *.
    eapply et_value_typing'; eauto; reflexivity.
    
  - (* Table_get *)
    destruct t0; remove_bools_options.
    eapply all_projection in Hif1; eauto.
    by resolve_e_typing.
  - (* Table fill *)
    destruct tab; remove_bools_options.
    rewrite -cat1s.
    eapply et_composition'.
    + resolve_e_typing.
      eapply instr_subtyping_weaken1; first reflexivity.
      simpl.
      by resolve_subtyping.
    + resolve_e_typing.
      eapply instr_subtyping_weaken1; first reflexivity.
      simpl.
      by resolve_subtyping.
  - (* Table copy 1 *)
    destruct taby; simpl in *.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_ref (tt_elem_type extr)]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; reflexivity.
    }
    rewrite -cat1s; apply et_composition' with (t2s := nil); by resolve_e_typing.
  - (* Table copy 2 *)
    destruct taby; simpl in *.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_ref (tt_elem_type extr)]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; reflexivity.
    }
    rewrite -cat1s; apply et_composition' with (t2s := nil); by resolve_e_typing.
  - (* Table_init *)
    destruct tab; simpl in *.
    remove_bools_options.
    specialize (inst_typing_elem_lookup HIT1 Hoption0) as [elemt [ei [Hselem [Helemt Hnthet]]]].
    specialize (store_typing_elem_lookup HST1 H0) as [et Het].
    simplify_multieq.
    unfold eleminst_typing in Helemt.
    destruct ei.
    remove_bools_options.
    eapply all_projection in Hif2; eauto.   
    resolve_e_typing => //.
    rewrite -cat1s; apply et_composition' with (t2s := nil); by resolve_e_typing.
      
  - (* Load None *)
    destruct t => /=; by resolve_subtyping.
  - (* Load Some *)
    destruct t => /=; by resolve_subtyping.
  - (* Load_vec *)
    destruct v => /=; by resolve_subtyping.
  - (* Load_lane_vec *)
    destruct v' => /=; by resolve_subtyping.
  - (* Memory fill *)
    destruct mem.
    remove_bools_options.
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
  - (* Memory copy 1 *)
    destruct mem.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_num T_i32]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; by resolve_subtyping.
    }
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
  - (* Memory copy 2 *)
    destruct mem.
    remove_bools_options.
    rewrite -cat1s; apply et_composition' with (t2s := [::T_num T_i32; T_num T_i32]).
    { resolve_e_typing.
      simplify_lists.
      apply instr_subtyping_weaken; by resolve_subtyping.
    }
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
    destruct mem.
    remove_bools_options.
  - (* Memory init *)
    by rewrite -cat1s; apply et_composition' with (t2s := nil); resolve_e_typing.
    
  - (* Label *)
    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; (try by apply HType); eauto.
      - by eapply r_label; eauto.
      - unfold inst_match => /=.
        by repeat rewrite eq_refl.
    }
    remember HIT2 as HIT3; clear HeqHIT3.
    erewrite <- reduce_inst_unchanged in HIT2; eauto.
    specialize (inst_typing_extension Hext HIT1) as [C'' [Hit Hcext]].
    simplify_multieq.
    assert (values_typing s' f'.(f_locs) tlocs) as Hvaltype.
    {
      specialize (lfilled_es_type_exists erefl HType) as Hestype.
      destruct Hestype as [lab' [ts1 [ts2 Hestype]]].
      eapply t_preservation_locs_type; eauto.
      - unfold inst_match; by repeat rewrite eq_refl.
      - done.
    }
    remember (lfill lh es) as les.
    remember (lfill lh es') as les'.
    generalize dependent les'.
    generalize dependent les.
    move: lh lab tx ty.
    elim.
    + move => vs es0 lab tx ty ? ? Hetype ? ?; subst; simpl in *.
      invert_e_typing.
      apply et_composition' with (t2s := tx ++ ts_values).
      { apply et_weakening_empty_1.
        apply et_values_typing.
        by specialize (values_typing_extension Hext H2_values) as Hvalues'.
      }
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      }
      eapply IHHReduce; eauto.
      eapply ety_subtyping; try by apply H1_comp0.
      eapply instr_subtyping_weaken1; first reflexivity.
      by apply instr_subtyping_empty1_impl' in H1_values.
    + move => k0 vs n es1 lh' IH es2 lab tx ty ? -> /=Hetype ? ->.
      invert_e_typing.
      eapply et_composition' with (t2s := tx ++ ts_values); eauto.
      { apply et_weakening_empty_1.
        apply et_values_typing.
        by eapply values_typing_extension; eauto.
      }
      rewrite -cat1s.
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      }
      eapply IH in Hconjl1; eauto.
      eapply ety_subtyping; first eapply ety_label; eauto.
      * eapply extensions_e_typing; (try by apply Hext); (try by apply Hconjl0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      * specialize (instr_subtyping_compose_ge H1_values Htisub) as [Hsubi Hsubt]; first by lias.
        apply instr_subtyping_empty1_impl' in Hsubi.
        simpl in Hsubi; rewrite subn0 take_size in Hsubi.
        apply instr_subtyping_empty1_impl.
         by rewrite -catA.
    + move => k0 vs n cs lh' IH es2 lab tx ty ? -> /= Hetype ? ->.
      invert_e_typing.
      eapply et_composition' with (t2s := tx ++ ts_values); eauto.
      { apply et_weakening_empty_1.
        apply et_values_typing.
        by eapply values_typing_extension; eauto.
      }
      rewrite -cat1s.
      eapply et_composition'; eauto; last first.
      { eapply extensions_e_typing; (try by apply H2_comp0); eauto.
        by unfold context_extension in *; destruct C, C''; remove_bools_options; lias.
      }
      eapply IH in Hconjl1; eauto.
      eapply ety_subtyping; first eapply ety_handler; eauto.
      * assert (context_extension
          (upd_local_label_return C tlocs lab ret)
          (upd_local_label_return C'' tlocs lab ret)) as Hctx.
        { by unfold context_extension in *; destruct C, C''; remove_bools_options; lias. }
        pose proof (context_extension_agree Hctx) as Hagree.
        by rewrite -(eq_all (fun c => catch_clause_context_agree c Hagree)).
      * specialize (instr_subtyping_compose_ge H1_values Htisub) as [Hsubi Hsubt]; first by lias.
        apply instr_subtyping_empty1_impl' in Hsubi.
        simpl in Hsubi; rewrite subn0 take_size in Hsubi.
        apply instr_subtyping_empty1_impl.
        by rewrite -catA.

  - (* r_frame *)
    unfold frame_typing in Hframetype.
    remove_bools_options.
    destruct Hframetype as [ts [-> Hvaltype]].

    assert (store_extension s s') as Hext.
    { eapply store_extension_reduce; eauto.
      unfold inst_match => /=.
      by repeat rewrite eq_refl.
    }
    assert (values_typing s' f'.(f_locs) ts) as Hvaltype'.
    {
      eapply t_preservation_locs_type; eauto => /=.
      - unfold inst_match; by repeat rewrite eq_refl.
      - simpl. by erewrite inst_t_context_local_empty; eauto; rewrite cats0.
    }
    erewrite -> inst_t_context_local_empty in *; eauto.
    rewrite -> cats0 in *.
    assert (inst_match t (upd_return (upd_local t ts) (Some extr))) as Hmatch; first by unfold inst_match; lias.
    specialize (inst_typing_reduce HReduce HST1 Hoption Hmatch Hetype) as [C'' [Hit Hcext]].
    apply ety_frame => //.
    eapply mk_thread_typing; eauto.
    { unfold frame_typing.
      rewrite Hit.
      by erewrite -> inst_t_context_local_empty; eauto.
    }
    {
      rewrite cats0.
      unfold upd_return, upd_local in *; simpl in *.
      rewrite -> upd_local_label_return_overwrite in *.
      eapply IHHReduce; eauto.
       by erewrite -> inst_t_context_label_empty in *; eauto.
    }
  - (* try_table: handler outside the implicit body label *)
    erewrite <- inst_typing_expand_eq in Hconjl0; eauto.
    rewrite Hconjl0 in H; injection H as <- <-.
    pose proof (values_typing_length H2_values) as Hlen.
    rewrite !length_is_size in H0 Hlen.
    specialize (instr_subtyping_compose_eq H1_values Htisub) as [Hsubi Hsubt]; first by lias.
    eapply ety_subtyping; last exact Hsubi.
    eapply ety_handler; eauto.
    eapply ety_label; eauto; first by apply et_empty; resolve_subtyping.
    eapply et_composition'; eauto; resolve_e_typing; first reflexivity.
    eapply ety_a in Hconjr; eauto.
    eapply ety_subtyping; eauto.
    eapply instr_subtyping_weaken1; eauto.
    by resolve_subtyping.
  - (* handler body *)
    eapply ety_handler; eauto.
    assert (inst_match C (upd_local_label_return C tlocs lab ret)) as Hmatch.
    { by unfold inst_match; lias. }
    destruct (inst_typing_reduce HReduce HST1 HIT1 Hmatch Hconjl1)
      as [C'' [Hit Hcext]].
    rewrite HIT2 in Hit; injection Hit as <-.
    assert (context_extension
      (upd_local_label_return C tlocs lab ret)
      (upd_local_label_return C' tlocs lab ret)) as Hctx.
    { by unfold context_extension in *; destruct C, C'; remove_bools_options; lias. }
    pose proof (context_extension_agree Hctx) as Hagree.
    by rewrite -(eq_all (fun c => catch_clause_context_agree c Hagree)).
  - (* matching tag handler *)
    destruct (store_typing_exn_lookup HST1 H) as [ps [Htag Hfields]].
    destruct (inst_typing_tag_lookup HIT1 H0) as [ps' [Htag' Hctx]].
    rewrite Htag in Htag'; injection Htag' as <-.
    rewrite Hoption in Hctx; injection Hctx as <-.
    eapply ety_composition.
    + apply et_values_typing.
      by eapply values_typing_trans; eauto.
    + apply ety_a with (bes := [::BI_br l]).
      apply bet_br with (t1s := nil); exact Hoption0.
  - (* nonmatching tag: continue ordered handler search *)
    eapply ety_handler; eauto.
    by eapply ety_raise; eauto.
  - apply instr_subtyping_eq.
  Unshelve.
  all: try exact nil.
  - destruct (store_typing_exn_lookup HST1 H) as [ps [Htag Hfields]].
    destruct (inst_typing_tag_lookup HIT1 H0) as [ps' [Htag' Hctx]].
    rewrite Htag in Htag'; injection Htag' as <-.
    rewrite Hoption in Hctx; injection Hctx as <-.
    replace (v_to_e_list (exninst_fields extr0) ++
      [::AI_ref_exn a; AI_basic (BI_br l)])
      with (v_to_e_list (exninst_fields extr0 ++ [::VAL_ref (VAL_ref_exn a)]) ++
        [::AI_basic (BI_br l)]).
    2: { by rewrite /v_to_e_list map_cat /= -catA. }
    eapply ety_composition.
    + apply et_values_typing.
      eapply values_typing_trans; last exact H1.
      unfold values_typing.
      rewrite all2_cat; last by apply values_typing_size in Hfields.
      unfold values_typing in Hfields.
      rewrite Hfields /= /value_typing /= H.
      by simpl.
    + apply ety_a with (bes := [::BI_br l]).
      by apply bet_br with (t1s := nil).
  - eapply ety_handler; eauto.
    by eapply ety_raise; eauto.
  - change (e_typing s (upd_local_label_return C' tlocs lab ret)
      ([::AI_ref_exn a] ++ [::AI_basic (BI_br l)]) (Tf nil extr)).
    eapply ety_composition with (t2s := [::T_ref reference]).
    + eapply ety_subtyping; first by eapply ety_ref_exn; eauto.
      apply instr_subtyping_weaken2 with
        (ty2 := [::T_ref (Ref_type false HT_exn)]); first apply instr_subtyping_eq.
      by rewrite -value_values_subtyping value_subtyping_ref.
    + apply ety_a with (bes := [::BI_br l]).
      by apply bet_br with (t1s := nil).
Qed.

Theorem t_preservation: forall s f es s' f' es' ts hs hs',
    reduce hs s f es hs' s' f' es' ->
    config_typing s (f, es) ts ->
    config_typing s' (f', es') ts.
Proof.
  move => s f es s' f' es' ts hs hs' HReduce HType.
  inversion HType; inversion H0; subst; clear HType.
  unfold frame_typing in H3; remove_bools_options.
  destruct H3 as [tlocs [-> Hloctype]].

  assert (store_extension s s') as Hstoreext.
  { eapply store_extension_reduce; eauto.
    by unfold inst_match; repeat rewrite eq_refl.
  }
  assert (store_typing s') as Hstoretype.
  { eapply store_typing_reduce; try (by apply H8); eauto.
    by unfold inst_match; repeat rewrite eq_refl.
  }

  specialize (inst_typing_extension Hstoreext Hoption) as Hit'.
  erewrite -> reduce_inst_unchanged in Hit'; eauto.
  destruct Hit' as [C' [Hit' Hcext]].

  erewrite -> inst_t_context_local_empty in *; eauto.
  rewrite -> cats0 in *.

  constructor => //.
  econstructor; eauto.
  - unfold frame_typing.
    rewrite Hit'.
    exists tlocs.
    split; first done.
    eapply t_preservation_locs_type in Hloctype; eauto; try by [].
    unfold inst_match; destruct t => /=; by lias.
  - unfold upd_return, upd_local in *.
    rewrite -> upd_local_label_return_overwrite in *.
    simpl in *.
    erewrite -> inst_t_context_local_empty in *; eauto.
    erewrite -> inst_t_context_label_empty in *; eauto.
    rewrite -> cats0 in *.
    by eapply t_preservation_e; eauto.
Qed.

End Host.
