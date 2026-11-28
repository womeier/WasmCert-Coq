(** Correctness of the terminating extended-constant evaluator. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func type_checker_reflects_typing type_preservation.
From Wasm Require Import closed_initializer_properties closed_typing_properties
  closed_context_properties closed_source_translation closed_operand_properties
  gc_closed_runtime_properties gc_runtime_type_properties gc_declaration_typing_properties
  gc_declaration_typing.
From Stdlib Require Import Relations Relation_Operators NArith Arith.Wf_nat Arith.PeanoNat.

Set SsrOldRewriteGoalsOrder.

Section Host.
Context `{ho : host}.

Lemma const_binop_total t op v1 v2 :
  const_binop t op ->
  binop_typecheck v1 v2 t op ->
  exists v, app_binop op v1 v2 = Some v /\ typeof_num v = t.
Proof.
  destruct t, op as [op|op]; destruct op => //;
    destruct v1, v2 => //=; eauto.
Qed.

(* This syntactic invariant deliberately includes all binary numeric operations
   and traps: preservation does not require totality, and a failed numeric
   operation still preserves typing.  Control and state-changing instructions
   are excluded. *)
Definition const_admin (e : administrative_instruction) : bool :=
  match e with
  | AI_basic (BI_const_num _) | AI_basic (BI_const_vec _)
  | AI_basic (BI_ref_null _) | AI_basic (BI_ref_func _)
   | AI_basic (BI_global_get _) | AI_basic (BI_binop _ _)
   | AI_basic BI_ref_i31
   | AI_ref_null _ | AI_ref _ | AI_ref_extern _ | AI_ref_i31 _ | AI_trap => true
  | _ => false
  end.

Lemma const_admin_values vs : all const_admin (v_to_e_list vs).
Proof.
  apply/allP => e.
  rewrite /v_to_e_list => /mapP [v _ ->].
  by destruct v as [v|v|v]; destruct v.
Qed.

Lemma const_admin_preservation hs s f es hs' s' f' es' :
  reduce hs s f es hs' s' f' es' ->
  forall C tf,
  all const_admin es ->
  e_typing s C es tf ->
  registered_function_references s ->
  C.(tc_defined_types) = f.(f_inst).(inst_defined_types) ->
  (forall n addr, List.nth_error f.(f_inst).(inst_funcs) n = Some addr ->
     (addr < N.of_nat (length s.(s_funcs)))%N) ->
  (forall gidx v gt, sglob_val s f.(f_inst) gidx = Some v ->
     lookup_N C.(tc_globals) gidx = Some gt ->
      closed_value_typing s v gt.(tg_t)) ->
  hs' = hs /\ s' = s /\ f' = f /\
  all const_admin es' /\ e_typing s C es' tf.
Proof.
  move => Hred.
   induction Hred; move => C tf Hcode Htype Hregistered Hnames Hfunc Hglob;
    subst; try (by repeat rewrite all_cat in Hcode; simpl in Hcode;
                   rewrite ?andbF ?andFb in Hcode).
  - (* simple *)
    repeat split => //; last by eapply t_simple_preservation; eauto.
    inversion H; subst; simpl in Hcode;
      try (by repeat rewrite all_cat in Hcode; simpl in Hcode;
                   rewrite ?andbF ?andFb in Hcode).
  - (* ref.func *)
    repeat split => //.
    destruct tf as [tx ty].
    invert_e_typing.
    assert (exists cl, lookup_N (s_funcs s) addr = Some cl) as [cl Hcl].
    { unfold lookup_N in *.
      destruct (List.nth_error (s_funcs s) (N.to_nat addr)) as [cl|] eqn:Hcl.
      - by eexists.
      - apply List.nth_error_None in Hcl.
        apply Hfunc in H.
        exfalso; lias.
    }
    eapply ety_subtyping; last eauto.
    apply ety_ref with (t := Closed_ref true (CH_abstract HT_func)).
    exact (Hregistered addr cl Hcl).
  - (* Source nulls are lowered under the actual initializer instance names. *)
    repeat split => //.
    + exact (const_admin_values [::VAL_ref ref]).
    + destruct tf as [tx ty]. invert_e_typing.
      fold_closed_subtyping.
      have Names := close_context_names _ _ HSourceContext.
      have Value : closed_operand_typing s (VAL_ref ref)
          (interpret_operand_type (tc_defined_types SourceContext)
            (T_ref (Ref_type true heap))).
      { rewrite interpret_operand_acceptance -Names Hnames.
        exact (lower_source_null_typed _ _ _ _ H). }
      cbn [interpret_operand_results List.map] in Htisub.
      remember (interpret_operand_type (tc_defined_types SourceContext)
        (T_ref (Ref_type true heap))) as operand eqn:Operand.
      destruct operand as [concrete|]; last discriminate.
      eapply ety_subtyping; last exact Htisub.
      change (e_typing s C [::v_to_e (VAL_ref ref)]
        (Closed_ft nil [::CO_value concrete])).
      by apply et_value_typing.
  - (* global.get *)
    repeat split => //.
    + exact: (const_admin_values [::v]).
    + destruct tf as [tx ty].
      invert_e_typing.
      destruct (close_context_global_lookup HSourceContext Hconjl0)
        as [expected [Closed Lookup]].
      destruct (close_global_type_agreement _ _ _ Closed) as [_ ValueClosed].
      have Operand : interpret_operand_type (tc_defined_types SourceContext) (tg_t extr) =
          CO_value (tg_t expected).
      { unfold interpret_operand_type.
        by rewrite (close_concrete_operand _ _ _ ValueClosed). }
      cbn [interpret_operand_results List.map] in Htisub.
      rewrite Operand in Htisub. fold_closed_subtyping.
      eapply et_value_typing'; last exact Htisub.
      by eapply Hglob; eauto.
  - (* evaluation context: nonzero-depth contexts contain a label, which
       cannot occur in this fragment. *)
    destruct lh as [vs tail|k vs n body lh tail].
    + simpl in *.
      rewrite !all_cat in Hcode.
      move/andP: Hcode => [Hvs /andP [Hes Htail]].
      destruct tf as [tx ty].
      invert_e_typing.
      specialize (IHHred _ _ Hes H1_comp0 Hregistered Hnames Hfunc Hglob)
        as [-> [-> [-> [Hes' Htype']]]].
      repeat split => //.
      * by rewrite !all_cat Hvs Hes' Htail.
      * eapply et_composition'; first by eapply et_values_typing'; eauto.
        by eapply et_composition'; eauto.
    + simpl in Hcode.
      rewrite all_cat /= andbF in Hcode.
      done.
Qed.

Lemma const_admin_trans_preservation x y :
  reduce_trans x y ->
  let '(hs, s, f, es) := x in
  let '(hs', s', f', es') := y in
  forall C tf,
  all const_admin es ->
  e_typing s C es tf ->
  registered_function_references s ->
  C.(tc_defined_types) = f.(f_inst).(inst_defined_types) ->
  (forall n addr, List.nth_error f.(f_inst).(inst_funcs) n = Some addr ->
     (addr < N.of_nat (length s.(s_funcs)))%N) ->
  (forall gidx v gt, sglob_val s f.(f_inst) gidx = Some v ->
     lookup_N C.(tc_globals) gidx = Some gt ->
      closed_value_typing s v gt.(tg_t)) ->
  hs' = hs /\ s' = s /\ f' = f /\
  all const_admin es' /\ e_typing s C es' tf.
Proof.
  move => Hred.
  induction Hred.
  - destruct x as [[[hs s] f] es], y as [[[hs' s'] f'] es'].
    by apply const_admin_preservation.
   - destruct x as [[[hs s] f] es] => C tf Hcode Htype Hregistered Hnames Hfunc Hglob.
    by repeat split.
  - destruct x as [[[hs s] f] es], y as [[[hs1 s1] f1] es1],
      z as [[[hs2 s2] f2] es2].
    move => C tf Hcode Htype Hregistered Hnames Hfunc Hglob.
    specialize (IHHred1 C tf Hcode Htype Hregistered Hnames Hfunc Hglob)
      as [-> [-> [-> [Hcode1 Htype1]]]].
    by apply IHHred2.
Qed.

Lemma extended_const_exprs_admin c es :
  extended_const_exprs c es -> all const_admin (to_e_list es).
Proof.
  induction es as [|e es IH] => //=.
  move/andP => [He Hes].
  rewrite IH // andbT.
  by destruct e.
Qed.

Theorem extended_init_value_typing C closed hs s f bes v t :
  reduce_trans (hs, s, f, to_e_list bes) (hs, s, f, [::v_to_e v]) ->
  extended_const_exprs C bes ->
  be_typing C bes (Tf nil [::t]) ->
  canonical_registry_valid s.(s_types) ->
  registered_function_references s ->
  close_t_context C = Some closed ->
  C.(tc_defined_types) = f.(f_inst).(inst_defined_types) ->
  (forall n addr, List.nth_error f.(f_inst).(inst_funcs) n = Some addr ->
     (addr < N.of_nat (length s.(s_funcs)))%N) ->
  (forall gidx v gt, sglob_val s f.(f_inst) gidx = Some v ->
     lookup_N C.(tc_globals) gidx = Some gt ->
      value_typing s f.(f_inst).(inst_defined_types) v gt.(tg_t)) ->
  value_typing s f.(f_inst).(inst_defined_types) v t.
Proof.
  move => Hred Hconst Hbet Registry Registered Context Names Hfunc Hglob.
  apply extended_const_exprs_admin in Hconst.
  have Entry := source_structural_entry s C closed _ _ Hbet Context.
  have ClosedNames : tc_defined_types closed = inst_defined_types (f_inst f).
  { by rewrite (close_context_names _ _ Context). }
  have Globals : forall index value descriptor,
      sglob_val s (f_inst f) index = Some value ->
      lookup_N (tc_globals closed) index = Some descriptor ->
      closed_value_typing s value (tg_t descriptor).
  { move => index value descriptor Get Lookup.
    destruct (close_context_global_lookup_inv Context Lookup)
      as [raw [Closed Slot]].
    have Value := Hglob _ _ _ Get Slot.
    destruct (close_global_type_agreement _ _ _ Closed) as [_ ValueClosed].
    unfold value_typing in Value. rewrite -Names ValueClosed in Value.
    exact Value. }
  specialize (const_admin_trans_preservation _ _ Hred closed _ Hconst Entry
    Registered ClosedNames Hfunc Globals)
    as [_ [_ [_ [_ Htype]]]].
  destruct (Value_typing_inversion Htype) as [actual [Subtype Value]].
  apply closed_instr_empty_input_elim in Subtype.
  cbn [interpret_instr_type interpret_operand_results List.map] in Subtype.
  inversion Subtype; subst.
  rewrite -Names -interpret_operand_acceptance.
  eapply operand_subtyping_acceptance with (actual := CO_value actual).
  - exact Registry.
  - exact Value.
  - eassumption.
Qed.

Theorem extended_global_type_checker_reflects c g :
  reflect (extended_global_typing c g) (extended_global_type_checker c g).
Proof.
  rewrite /extended_global_type_checker /extended_global_typing.
  apply (iffP andP).
  - move => [Hconst Htype]; split => //.
    by apply/b_e_type_checker_reflects_typing.
  - move => [Hconst Htype]; split => //.
    by apply/b_e_type_checker_reflects_typing.
Qed.

Theorem extended_globals_type_checker_reflects c gs :
  reflect (extended_globals_typing c gs) (extended_globals_type_checker c gs).
Proof.
  move: c.
  induction gs as [|g gs IH]; move => c; simpl.
  - by apply ReflectT.
  - apply (iffP andP).
    + move => [Hg Hgs]; split.
      * by apply/extended_global_type_checker_reflects.
      * by apply/IH.
    + move => [Hg Hgs]; split.
      * by apply/extended_global_type_checker_reflects.
      * by apply/IH.
Qed.

Lemma extended_globals_typing_nth c gs n g :
  extended_globals_typing c gs ->
  List.nth_error gs n = Some g ->
  exists c',
    c'.(tc_globals) = c.(tc_globals) ++ map modglob_type (take n gs) /\
    extended_global_typing c' g.
Proof.
  move: c n.
  induction gs as [|g0 gs IH]; move => c [|n] //=.
  - move => [Hg Hgs] [<-].
    exists c; by rewrite cats0.
  - move => [Hg Hgs] Hnth.
    specialize (IH _ _ Hgs Hnth) as [c' [Hglobals Htype]].
    exists c'; split => //.
    by rewrite Hglobals /= -catA.
Qed.

Lemma extended_globals_typing_prefix c gs n g :
  extended_globals_typing c gs ->
  List.nth_error gs n = Some g ->
  extended_global_typing
    (const_context_add_globals c (map modglob_type (take n gs))) g.
Proof.
  move: c n. induction gs as [|first gs IH]; move => c [|n] //=.
  - move => [Typed _] [<-].
    rewrite /const_context_add_globals /= cats0.
    by destruct c.
  - move => [_ Typed] Lookup.
    have Tail := IH _ _ Typed Lookup.
    move: Tail. by rewrite /const_context_add_global /const_context_add_globals /= -catA.
Qed.

Lemma global_init_values_typing C closed closed_globals hs s f gs vs :
  extended_globals_typing C gs ->
  List.Forall2 (fun g v =>
    reduce_trans (hs, s, f, to_e_list g.(modglob_init))
                  (hs, s, f, [::v_to_e v])) gs vs ->
  canonical_registry_valid s.(s_types) ->
  registered_function_references s ->
  close_t_context C = Some closed ->
  C.(tc_defined_types) = f.(f_inst).(inst_defined_types) ->
  those (List.map (close_global_type C.(tc_defined_types))
    (map modglob_type gs)) = Some closed_globals ->
  (forall n addr, List.nth_error f.(f_inst).(inst_funcs) n = Some addr ->
     (addr < N.of_nat (length s.(s_funcs)))%N) ->
  (forall gidx v gt, sglob_val s f.(f_inst) gidx = Some v ->
     lookup_N C.(tc_globals) gidx = Some gt ->
      value_typing s f.(f_inst).(inst_defined_types) v gt.(tg_t)) ->
  (forall j g v, List.nth_error gs j = Some g ->
     List.nth_error vs j = Some v ->
     sglob_val s f.(f_inst) (N.of_nat (length C.(tc_globals) + j)) = Some v) ->
  List.Forall2 (fun g v =>
    value_typing s f.(f_inst).(inst_defined_types) v g.(modglob_type).(tg_t)) gs vs.
Proof.
  move => Hprefix Hreduce Registry Registered Context Names ClosedGlobals Hfunc Himport Hdefined.
  specialize (List.Forall2_length Hreduce) as Hlen.
  apply Forall2_spec => //.
  move => n.
  induction n using lt_wf_ind.
  move => g v Hnthg Hnthv.
  have PrefixTyping := extended_globals_typing_prefix _ _ _ _ Hprefix Hnthg.
  set Cn := const_context_add_globals C (map modglob_type (take n gs)).
  change (extended_global_typing Cn g) in PrefixTyping.
  destruct PrefixTyping as [Hconst Hbet].
  have Hglobals : tc_globals Cn = tc_globals C ++ map modglob_type (take n gs).
  { reflexivity. }
  have PrefixClosed : those (List.map (close_global_type (tc_defined_types C))
      (map modglob_type (take n gs))) = Some (take n closed_globals).
  { rewrite map_take.
    exact (those_map_take n ClosedGlobals). }
  have PrefixContext := close_initializer_globals Context PrefixClosed.
  specialize (Forall2_lookup Hreduce Hnthg) as [v0 [Hnthv0 Hred]].
  rewrite Hnthv in Hnthv0; injection Hnthv0 as <-.
  eapply extended_init_value_typing; try eassumption.
  move => idx w gt Hget Hlookup.
  rewrite Hglobals in Hlookup.
  unfold lookup_N in Hlookup.
  destruct (Nat.lt_ge_cases (N.to_nat idx) (length (tc_globals C))) as [Hlt|Hge].
  - rewrite List.nth_error_app1 in Hlookup; last exact Hlt.
    by eapply Himport; eauto.
  - rewrite List.nth_error_app2 in Hlookup; last exact Hge.
    apply nth_error_map in Hlookup as [g' [Htake <-]].
    set j := (N.to_nat idx - length (tc_globals C))%coq_nat.
    fold j in Htake.
    assert (j < n) as Hjn.
    { apply nth_error_Some_length in Htake.
      rewrite length_is_size size_take in Htake.
      by destruct (n < size gs) eqn:Hnlt; lias.
    }
    assert (List.nth_error gs j = Some g') as Hnthg'.
    { by rewrite (nth_error_take_longer _ Hjn). }
    destruct (List.nth_error vs j) as [v'|] eqn:Hnthv'.
    2: { apply List.nth_error_None in Hnthv'.
         apply nth_error_Some_length in Hnthg'.
         by lias.
    }
    specialize (Hdefined _ _ _ Hnthg' Hnthv').
    assert (idx = N.of_nat (length (tc_globals C) + j)) as Hidx.
    { apply Nnat.N2Nat.inj.
      rewrite Nnat.Nat2N.id.
      unfold j; by lias.
    }
    rewrite Hidx Hdefined in Hget.
    injection Hget as <-.
    by eapply H; eauto; lias.
Qed.

Lemma sglob_val_defined s f oldgs imports gs vs j g v :
  s.(s_globals) = oldgs ++ map (fun '(g, v) => gen_global_instance g v) (List.combine gs vs) ->
  f.(f_inst).(inst_globals) = imports ++ iota_N (length oldgs) (length gs) ->
  List.nth_error gs j = Some g ->
  List.nth_error vs j = Some v ->
  sglob_val s f.(f_inst) (N.of_nat (length imports + j)) = Some v.
Proof.
  move => Hstore Hinst Hg Hv.
  unfold sglob_val, sglob, sglob_ind.
  rewrite Hinst /lookup_N Nnat.Nat2N.id.
  rewrite List.nth_error_app2; last exact (Nat.le_add_r _ _).
  rewrite /addn Nat.add_sub_swap; last exact (Nat.le_refl _).
  rewrite Nat.sub_diag /=.
  rewrite iota_N_lookup; last by apply nth_error_Some_length in Hg; lias.
  rewrite Hstore Nnat.Nat2N.id.
  rewrite List.nth_error_app2; last by lias.
  rewrite /addn Nat.add_sub_swap; last exact (Nat.le_refl _).
  rewrite Nat.sub_diag /=.
  assert (List.nth_error (List.combine gs vs) j = Some (g, v)) as Hpair.
  { clear - Hg Hv.
    move: gs vs Hg Hv.
    induction j; move => [|g0 gs] [|v0 vs] //= Hg Hv.
    - by injection Hg as ->; injection Hv as ->.
    - by apply IHj.
  }
  by rewrite nth_error_map' Hpair.
Qed.

Lemma global_instances_map gs vs :
  map (fun '(g, v) => gen_global_instance g v) (List.combine gs vs) =
  map (fun '(gt, v) => {| g_type := gt; g_val := v |})
      (List.combine gs vs).
Proof.
  apply eq_map.
  by move => [gt v].
Qed.

Lemma global_init_context_typing (C : t_context) s f gs vs :
  List.Forall2 (fun g v =>
    value_typing s f.(f_inst).(inst_defined_types) v g.(modglob_type).(tg_t)) gs vs ->
  (forall idx v gt, sglob_val s f.(f_inst) idx = Some v ->
      lookup_N C.(tc_globals) idx = Some gt ->
      value_typing s f.(f_inst).(inst_defined_types) v gt.(tg_t)) ->
  (forall j g v, List.nth_error gs j = Some g ->
     List.nth_error vs j = Some v ->
     sglob_val s f.(f_inst) (N.of_nat (length C.(tc_globals) + j)) = Some v) ->
  forall idx v gt, sglob_val s f.(f_inst) idx = Some v ->
    lookup_N (C.(tc_globals) ++ map modglob_type gs) idx = Some gt ->
    value_typing s f.(f_inst).(inst_defined_types) v gt.(tg_t).
Proof.
  move => Hvalues Himport Hdefined idx v gt Hget Hlookup.
  unfold lookup_N in Hlookup.
  destruct (Nat.lt_ge_cases (N.to_nat idx) (length (tc_globals C))) as [Hlt|Hge].
  - rewrite List.nth_error_app1 in Hlookup; last exact Hlt.
    by eapply Himport; eauto.
  - rewrite List.nth_error_app2 in Hlookup; last exact Hge.
    apply nth_error_map in Hlookup as [g [Hnthg <-]].
    specialize (Forall2_lookup Hvalues Hnthg) as [w [Hnthw Htype]].
    specialize (Hdefined _ _ _ Hnthg Hnthw).
    assert (idx = N.of_nat (length (tc_globals C) +
      (N.to_nat idx - length (tc_globals C)))) as Hidx.
    { apply Nnat.N2Nat.inj; rewrite Nnat.Nat2N.id; by lias. }
    rewrite Hidx Hdefined in Hget.
    by injection Hget as <-.
Qed.

Lemma const_reduce_context hs s f vs es es' tail :
  reduce hs s f es hs s f es' ->
  reduce hs s f (v_to_e_list vs ++ es ++ tail)
               hs s f (v_to_e_list vs ++ es' ++ tail).
Proof.
  move => Hred.
  by eapply r_label with (lh := LH_base vs tail); eauto.
Qed.

Lemma interp_const_step_sound hs s f e vs ws :
  interp_const_step s f e vs = Some ws ->
  reduce_trans (hs, s, f, v_to_e_list (rev vs) ++ [::AI_basic e])
               (hs, s, f, v_to_e_list (rev ws)).
Proof.
  destruct e; cbn [interp_const_step] => //.
  - (* numeric constant *)
    move => [<-].
    rewrite rev_cons /v_to_e_list map_rcons -cats1 /=.
    apply rt_refl.
  - (* binop *)
    destruct (const_binop n b) eqn:Hconst => //.
    destruct vs as [|v2 vs] => //.
    destruct v2 as [v2| |] => //.
    destruct vs as [|v1 vs] => //.
    destruct v1 as [v1| |] => //.
    destruct (binop_typecheck v1 v2 n b) eqn:Htype => //.
    destruct (app_binop b v1 v2) as [v|] eqn:Happ => //.
    move => [<-].
    repeat rewrite rev_cons.
    rewrite /v_to_e_list !map_rcons -!cats1 /= -!catA.
    apply rt_step.
    change (reduce hs s f
      (v_to_e_list (rev vs) ++ [::$VN v1; $VN v2; AI_basic (BI_binop n b)] ++ nil)
      hs s f (v_to_e_list (rev vs) ++ [::$VN v] ++ nil)).
    apply const_reduce_context.
    apply r_simple.
    by eapply rs_binop_success; eauto.
  - (* vector constant *)
    move => [<-].
    rewrite rev_cons /v_to_e_list map_rcons -cats1 /=.
    apply rt_refl.
  - (* ref.null *)
    destruct (lower_source_null s (f_inst f) h) as [ref|] eqn:Lower => //.
    move => [<-].
    rewrite rev_cons /v_to_e_list map_rcons -cats1 /=.
    apply rt_step.
    change (reduce hs s f
      (v_to_e_list (rev vs) ++ [::AI_basic (BI_ref_null h)] ++ nil)
      hs s f (v_to_e_list (rev vs) ++ [::$V (VAL_ref ref)] ++ nil)).
    apply const_reduce_context.
    by apply r_ref_null.
  - (* ref.func *)
    destruct (lookup_N (inst_funcs (f_inst f)) f0) as [addr|] eqn:Hlookup => //.
    move => [<-].
    rewrite rev_cons /v_to_e_list map_rcons -cats1 /=.
    apply rt_step.
    change (reduce hs s f
      (v_to_e_list (rev vs) ++ [::AI_basic (BI_ref_func f0)] ++ nil)
      hs s f (v_to_e_list (rev vs) ++ [::$V (VAL_ref (VAL_ref_func addr))] ++ nil)).
    apply const_reduce_context.
    by apply r_ref_func.
  - (* global.get *)
    destruct (sglob_val s (f_inst f) g) as [v|] eqn:Hlookup => //.
    move => [<-].
    rewrite rev_cons /v_to_e_list map_rcons -cats1 /=.
    apply rt_step.
    change (reduce hs s f
      (v_to_e_list (rev vs) ++ [::AI_basic (BI_global_get g)] ++ nil)
      hs s f (v_to_e_list (rev vs) ++ [::$V v] ++ nil)).
    apply const_reduce_context.
    by apply r_global_get.
  - (* ref.i31 *)
    destruct vs as [|v vs]; [discriminate |].
    destruct v as [[n|n|n|n]|v|v]; try discriminate.
    move => [<-].
    rewrite !rev_cons /v_to_e_list !map_rcons -!cats1 /= -!catA.
    apply rt_step.
    change (reduce hs s f
      (v_to_e_list (rev vs) ++ [::$VN (VAL_int32 n); AI_basic BI_ref_i31] ++ nil)
      hs s f
      (v_to_e_list (rev vs) ++ [::$V (VAL_ref (VAL_ref_i31 (i31bits_of_i32 n)))] ++ nil)).
    apply const_reduce_context. apply r_simple. apply rs_ref_i31.
Qed.

Lemma const_reduce_trans_suffix hs s f es es' tail :
  reduce_trans (hs, s, f, es) (hs, s, f, es') ->
  reduce_trans (hs, s, f, es ++ tail) (hs, s, f, es' ++ tail).
Proof.
  let append_tail := constr:(fun x : host_state * store_record * frame * list administrative_instruction =>
    let '(hs, s, f, es) := x in (hs, s, f, es ++ tail)) in
  suff Hlift : forall x y, reduce_trans x y ->
    reduce_trans (append_tail x) (append_tail y) by apply Hlift.
  move => x y Hred.
  induction Hred.
  - destruct x as [[[hs1 s1] f1] es1], y as [[[hs2 s2] f2] es2].
    apply rt_step => /=.
    by eapply r_label with (lh := LH_base nil tail); eauto.
  - apply rt_refl.
  - by eapply rt_trans; eauto.
Qed.

Lemma interp_const_stack_sound hs s f es vs ws :
  interp_const_stack s f es vs = Some ws ->
  reduce_trans (hs, s, f, v_to_e_list (rev vs) ++ to_e_list es)
               (hs, s, f, v_to_e_list (rev ws)).
Proof.
  move: vs ws.
  induction es as [|e es IH]; move => vs ws Heval.
  - simpl in Heval; injection Heval as <-.
    rewrite /= cats0.
    apply rt_refl.
  - cbn [interp_const_stack] in Heval.
    destruct (interp_const_step s f e vs) as [vs'|] eqn:Hstep => //.
    eapply rt_trans; last by eapply IH; eauto.
    change (reduce_trans
      (hs, s, f, v_to_e_list (rev vs) ++ [::AI_basic e] ++ to_e_list es)
      (hs, s, f, v_to_e_list (rev vs') ++ to_e_list es)).
    rewrite catA.
    apply const_reduce_trans_suffix.
    by apply interp_const_step_sound.
Qed.

Lemma interp_get_const_stack s f es :
  interp_get_const s f es =
    match interp_const_stack s f es nil with
    | Some [::v] => Some v
    | _ => None
    end.
Proof.
  destruct es as [|e [|e' es]] => //.
  all: destruct e => //=.
   - by destruct (lower_source_null s (f_inst f) h).
   - by destruct (lookup_N (inst_funcs (f_inst f)) f0).
  - by destruct (sglob_val s (f_inst f) g).
Qed.

Theorem interp_get_const_sound hs s f es v :
  interp_get_const s f es = Some v ->
  reduce_trans (hs, s, f, to_e_list es) (hs, s, f, [::v_to_e v]).
Proof.
  rewrite interp_get_const_stack.
  destruct (interp_const_stack s f es nil) as [ws|] eqn:Heval => //.
  destruct ws as [|w [|w' ws]] => //.
  move => [<-].
  by apply (interp_const_stack_sound hs _ _ _ _ _ Heval).
Qed.

Lemma interp_const_step_environment s f s' f' e vs ws :
  s'.(s_types) = s.(s_types) ->
  f'.(f_inst).(inst_defined_types) = f.(f_inst).(inst_defined_types) ->
  f'.(f_inst).(inst_funcs) = f.(f_inst).(inst_funcs) ->
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f'.(f_inst) i = Some v) ->
  interp_const_step s f e vs = Some ws ->
  interp_const_step s' f' e vs = Some ws.
Proof.
  move => Htypes Hnames Hfunc Hglob.
  destruct e => //=.
  - by rewrite /lower_source_null Hnames Htypes.
  - by rewrite Hfunc.
  - destruct (sglob_val s (f_inst f) g) as [v|] eqn:Hget => //.
    by rewrite (Hglob _ _ Hget).
Qed.

Lemma interp_const_stack_environment s f s' f' es vs ws :
  s'.(s_types) = s.(s_types) ->
  f'.(f_inst).(inst_defined_types) = f.(f_inst).(inst_defined_types) ->
  f'.(f_inst).(inst_funcs) = f.(f_inst).(inst_funcs) ->
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f'.(f_inst) i = Some v) ->
  interp_const_stack s f es vs = Some ws ->
  interp_const_stack s' f' es vs = Some ws.
Proof.
  move => Htypes Hnames Hfunc Hglob.
  move: vs ws.
  induction es as [|e es IH]; move => vs ws //=.
  destruct (interp_const_step s f e vs) as [vs'|] eqn:Hstep => //.
  erewrite interp_const_step_environment; eauto.
Qed.

Lemma interp_get_const_environment s f s' f' es v :
  s'.(s_types) = s.(s_types) ->
  f'.(f_inst).(inst_defined_types) = f.(f_inst).(inst_defined_types) ->
  f'.(f_inst).(inst_funcs) = f.(f_inst).(inst_funcs) ->
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f'.(f_inst) i = Some v) ->
  interp_get_const s f es = Some v ->
  interp_get_const s' f' es = Some v.
Proof.
  move => Htypes Hnames Hfunc Hglob.
  rewrite !interp_get_const_stack.
  destruct (interp_const_stack s f es nil) as [ws|] eqn:Heval => //.
  erewrite interp_const_stack_environment; eauto.
Qed.

Lemma const_global_extension s f source g v :
  forall i w, sglob_val s f.(f_inst) i = Some w ->
  sglob_val (add_glob s (gen_global_instance g v))
    (const_frame_add_global f (N.of_nat (length s.(s_globals))) source).(f_inst) i = Some w.
Proof.
  move => i w.
  unfold sglob_val, sglob, sglob_ind, lookup_N.
  cbn [const_frame_add_global add_glob].
  destruct (List.nth_error (inst_globals (f_inst f)) (N.to_nat i))
    as [addr|] eqn:Haddr => //.
  rewrite List.nth_error_app1; last by apply List.nth_error_Some; rewrite Haddr.
  rewrite Haddr.
  destruct (List.nth_error (s_globals s) (N.to_nat addr)) as [gi|] eqn:Hgi => //.
  rewrite List.nth_error_app1; first by rewrite Hgi.
  by apply List.nth_error_Some; rewrite Hgi.
Qed.

Lemma interp_global_chain_type_world s f gs s' f' vs :
  interp_global_chain s f gs = Some (s', f', vs) ->
  s'.(s_types) = s.(s_types) /\
  f'.(f_inst).(inst_defined_types) = f.(f_inst).(inst_defined_types).
Proof.
  move: s f s' f' vs.
  induction gs as [|g gs IH]; move => s f s' f' vs; cbn [interp_global_chain].
  - move => Equal. inversion Equal; subst. by split.
  - destruct (interp_get_const s f (modglob_init g)) as [v|] eqn:Heval => //.
    destruct (close_global_type (inst_defined_types (f_inst f)) (modglob_type g))
      as [closed|] eqn:Closed => //.
    destruct (closed_value_typing s v (tg_t closed)) eqn:Accepted => //.
    cbn [alloc_glob].
    destruct (interp_global_chain _ _ gs) as [[[s2 f2] ws]|] eqn:Hchain => //.
    move => Equal. inversion Equal; subst.
    exact (IH _ _ _ _ _ Hchain).
Qed.

Theorem interp_global_chain_results s f gs s' f' vs :
  interp_global_chain s f gs = Some (s', f', vs) ->
  f'.(f_inst).(inst_funcs) = f.(f_inst).(inst_funcs) /\
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f'.(f_inst) i = Some v) /\
  List.Forall2 (fun g v => interp_get_const s' f' g.(modglob_init) = Some v) gs vs.
Proof.
  move: s f s' f' vs.
  induction gs as [|g gs IH]; move => s f s' f' vs; cbn [interp_global_chain].
  - move => [<- <- <-].
    repeat split => //; constructor.
   - destruct (interp_get_const s f (modglob_init g)) as [v|] eqn:Heval => //.
     destruct (close_global_type (inst_defined_types (f_inst f)) (modglob_type g))
       as [closed|] eqn:Closed => //.
     destruct (closed_value_typing s v (tg_t closed)) eqn:Accepted => //.
    cbn [alloc_glob].
    destruct (interp_global_chain _ _ gs) as [[[s2 f2] ws]|] eqn:Hchain => //.
     move => [<- <- <-].
     destruct (interp_global_chain_type_world _ _ _ _ _ _ Hchain)
       as [Htypes Hnames].
    specialize (IH _ _ _ _ _ Hchain) as [Hfunc [Hglob Hresults]].
    assert (forall i w, sglob_val s f.(f_inst) i = Some w ->
      sglob_val s2 f2.(f_inst) i = Some w) as Hglob'.
    { move => i w Hget.
      apply Hglob.
      by apply const_global_extension.
    }
    repeat split => //.
    constructor => //.
    by eapply (interp_get_const_environment s f s2 f2 _ v); eauto.
Qed.

Lemma interp_global_chain_shape s f gs s' f' vs :
  interp_global_chain s f gs = Some (s', f', vs) ->
  exists closed_globals,
  those (List.map (fun g =>
    close_global_type f.(f_inst).(inst_defined_types) g.(modglob_type)) gs) =
    Some closed_globals /\
  s'.(s_globals) = s.(s_globals) ++
    map (fun '(g, v) => gen_global_instance g v) (List.combine closed_globals vs) /\
  f'.(f_inst).(inst_globals) = f.(f_inst).(inst_globals) ++
    iota_N (length s.(s_globals)) (length gs).
Proof.
  move: s f s' f' vs.
  induction gs as [|g gs IH]; move => s f s' f' vs; cbn [interp_global_chain].
  - move => [<- <- <-].
    exists nil. by rewrite /= !cats0.
  - destruct (interp_get_const s f (modglob_init g)) as [v|] eqn:Heval => //.
    destruct (close_global_type (inst_defined_types (f_inst f)) (modglob_type g))
      as [closed|] eqn:Closed => //.
    destruct (closed_value_typing s v (tg_t closed)) eqn:Accepted => //.
    cbn [alloc_glob].
    destruct (interp_global_chain _ _ gs) as [[[s2 f2] ws]|] eqn:Hchain => //.
    move => [<- <- <-].
    specialize (IH _ _ _ _ _ Hchain) as [closed_globals [Closing [Hglobals Hinst]]].
    exists (closed :: closed_globals). split.
    + cbn [List.map those]. rewrite Closed /=.
      change (those (List.map (fun g =>
        close_global_type (inst_defined_types (f_inst f)) (modglob_type g)) gs) =
        Some closed_globals) in Closing.
      rewrite -those_those0 in Closing.
      by rewrite -those_those0 /= Closing.
    + split.
      * by rewrite Hglobals /= -catA.
      * rewrite Hinst /= List.length_app /= Nat.add_1_r -catA.
        reflexivity.
Qed.

Lemma interp_const_step_store_extension s s' f e vs ws :
  s'.(s_types) = s.(s_types) ->
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f.(f_inst) i = Some v) ->
  interp_const_step s f e vs = Some ws ->
  interp_const_step s' f e vs = Some ws.
Proof.
  move => Htypes Hglob.
  destruct e => //=.
  - by rewrite /lower_source_null Htypes.
  -
  destruct (sglob_val s (f_inst f) g) as [v|] eqn:Hget => //.
  by rewrite (Hglob _ _ Hget).
Qed.

Lemma interp_const_stack_store_extension s s' f es vs ws :
  s'.(s_types) = s.(s_types) ->
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f.(f_inst) i = Some v) ->
  interp_const_stack s f es vs = Some ws ->
  interp_const_stack s' f es vs = Some ws.
Proof.
  move => Htypes Hglob.
  move: vs ws.
  induction es as [|e es IH]; move => vs ws //=.
  destruct (interp_const_step s f e vs) as [vs'|] eqn:Hstep => //.
  erewrite interp_const_step_store_extension; eauto.
Qed.

Lemma interp_get_const_store_extension s s' f es v :
  s'.(s_types) = s.(s_types) ->
  (forall i v, sglob_val s f.(f_inst) i = Some v ->
     sglob_val s' f.(f_inst) i = Some v) ->
  interp_get_const s f es = Some v ->
  interp_get_const s' f es = Some v.
Proof.
  move => Htypes Hglob.
  rewrite !interp_get_const_stack.
  destruct (interp_const_stack s f es nil) as [ws|] eqn:Heval => //.
  erewrite interp_const_stack_store_extension; eauto.
Qed.

Lemma interp_get_const_sound_global_extension hs s s' f es v gs :
  s'.(s_types) = s.(s_types) ->
  s'.(s_globals) = s.(s_globals) ++ gs ->
  interp_get_const s f es = Some v ->
  reduce_trans (hs, s', f, to_e_list es) (hs, s', f, [::v_to_e v]).
Proof.
  move => Htypes Hgs Heval.
  apply interp_get_const_sound.
  eapply (interp_get_const_store_extension s s' f es v); last exact Heval.
  - exact Htypes.
  -
  move => i w.
  unfold sglob_val, sglob, sglob_ind.
  destruct (lookup_N (inst_globals (f_inst f)) i) as [addr|] => //.
  rewrite Hgs.
  unfold lookup_N.
  destruct (List.nth_error (s_globals s) (N.to_nat addr)) as [g|] eqn:Hget => //.
  rewrite List.nth_error_app1; first by rewrite Hget.
  by apply List.nth_error_Some; rewrite Hget.
Qed.

Theorem interp_global_chain_sound hs s f gs s' f' vs :
  interp_global_chain s f gs = Some (s', f', vs) ->
  global_init_chain hs s f gs s' f' vs.
Proof.
  move: s f s' f' vs.
  induction gs as [|g gs IH]; move => s f s' f' vs; cbn [interp_global_chain].
  - move => [<- <- <-].
    constructor.
  - destruct (interp_get_const s f (modglob_init g)) as [v|] eqn:Heval => //.
    destruct (close_global_type (inst_defined_types (f_inst f)) (modglob_type g))
      as [closed|] eqn:Closed => //.
    destruct (closed_value_typing s v (tg_t closed)) eqn:Accepted => //.
    destruct (alloc_glob s (closed, v)) as [s1 addr] eqn:Halloc.
    destruct (interp_global_chain s1 (const_frame_add_global f addr (modglob_type g)) gs)
      as [[[s2 f2] ws]|] eqn:Hchain => //.
    move => [<- <- <-].
    eapply global_init_chain_cons; eauto.
    by apply interp_get_const_sound.
Qed.

Lemma interp_global_chain_length s f gs s' f' vs :
  interp_global_chain s f gs = Some (s', f', vs) ->
  length vs = length gs.
Proof.
  move: s f s' f' vs.
  induction gs as [|g gs IH]; move => s f s' f' vs; cbn [interp_global_chain].
  - move => H; by inversion H.
  - destruct (interp_get_const s f (modglob_init g)) as [v|] => //.
    destruct (close_global_type (inst_defined_types (f_inst f)) (modglob_type g))
      as [closed|] => //.
    destruct (closed_value_typing s v (tg_t closed)) => //.
    destruct (alloc_glob s (closed, v)) as [s1 addr].
    destruct (interp_global_chain s1 (const_frame_add_global f addr (modglob_type g)) gs)
      as [[[s2 f2] ws]|] eqn:Hchain => //.
    move => H; injection H as _ _ <- => /=.
    by rewrite (IH _ _ _ _ _ Hchain).
Qed.

End Host.
