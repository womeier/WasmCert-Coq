(** Soundness of the executable instantiation wrt the relational version. **)
(** The main proof to be done is the algorithm for breaking circularities
    in the evaluation of various initialisers. **)

From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import interpreter_ctx instantiation_func instantiation_properties type_checker_reflects_typing instantiation_sound.
From Coq Require Import Program.

Lemma Forall2_all2_impl {X Y: Type} (f: X -> Y -> bool) (fprop: X -> Y -> Prop) l1 l2:
  (forall x y, f x y = true -> fprop x y) ->
  all2 f l1 l2 ->
  List.Forall2 fprop l1 l2.
Proof.
  move: l2.
  induction l1; destruct l2 => //=; move => Himpl Hall.
  move/andP in Hall; destruct Hall as [Hf Hall].
  constructor; last by apply IHl1.
  by apply Himpl.
Qed.

Lemma module_type_checker_sound: forall m t_imps t_exps,
  module_type_checker m = Some (t_imps, t_exps) ->
  module_typing m t_imps t_exps.
Proof.
  move => m t_imps t_exps Hmodcheck.
  unfold module_type_checker in Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) as [impts | ] eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hmemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hfunccheck Htabcheck].
  simpl in *.
  unfold module_typing.
  injection Hmodcheck as ->->.
  
  exists fts, (gather_m_g_types mod_globals).
  repeat split => //.
  
  (* funcs *)
  { clear - Hfunccheck Hmftypes.
    unfold gather_m_f_types in Hmftypes.
    apply Forall2_spec; first by apply those_length in Hmftypes; rewrite List.map_length in Hmftypes.
    move => n mfunc tf Hfuncnth Hftsnth.
    eapply all_projection in Hfunccheck; eauto.
    eapply those_spec in Hmftypes; eauto.
    rewrite List.nth_error_map in Hmftypes.
    destruct (mod_funcs !! n) as [mf |] eqn:Hmfnth => //.
    destruct mfunc, modfunc_type, mf, modfunc_type.
    unfold gather_m_f_type in Hmftypes.
    Opaque type_checker.b_e_type_checker.
    simpl in *.
    destruct (n1 < length mod_types) eqn:Hlt => //.
    injection Hmftypes as Hmtnth.
    injection Hfuncnth as ->->->.
    rewrite Hlt Hmtnth in Hfunccheck.
    move/andP in Hfunccheck; destruct Hfunccheck as [_ Hfunccheck].
    destruct tf as [tn tm].
    move/b_e_type_checker_reflects_typing in Hfunccheck.
    repeat split => //.
    erewrite List.nth_error_nth; by eauto.
    admit.
  }
  (* globals *)
  { clear -Hglobcheck.
    unfold gather_m_g_types.
    apply Forall2_spec; first by rewrite List.map_length.
    move => n mglob gt Hgnth Hmgnth.
    erewrite List.map_nth_error in Hmgnth; last by eauto.
    injection Hmgnth as <-.
    unfold module_glob_typing.
    destruct mglob => /=.
    eapply all_projection in Hglobcheck; eauto.
    unfold module_glob_type_checker in Hglobcheck.
    move/andP in Hglobcheck; destruct Hglobcheck as [? Hbet].
    admit. (*by move/b_e_type_checker_reflects_typing in Hbet. *)
  }
  (* elem *)
  { clear -Helemcheck.
    apply Forall_spec.
    move => n x Hnth.
    eapply all_projection in Helemcheck; eauto.
    unfold module_elem_typing.
    unfold module_elem_type_checker in Helemcheck.
    destruct x, modelem_table => /=.
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hinit].
    move/andP in Helemcheck; destruct Helemcheck as [Helemcheck Hlen].
    move/andP in Helemcheck; destruct Helemcheck as [Hconst Hbet].
    admit. (* by move/b_e_type_checker_reflects_typing in Hbet. *)
  }
  (* data *)
  { clear -Hdatacheck.
    apply Forall_spec.
    move => n x Hnth.
    eapply all_projection in Hdatacheck; eauto.
    unfold module_data_typing.
    unfold module_data_type_checker in Hdatacheck.
    destruct x, moddata_data => /=.
    move/andP in Hdatacheck; destruct Hdatacheck as [Hdatacheck Hinit].
    move/andP in Hdatacheck; destruct Hdatacheck as [Hconst Hbet].
    admit. (* by move/b_e_type_checker_reflects_typing in Hbet. *)
  }
  (* imports *)
  { clear - Hmitypes.
    unfold module_imports_typer in Hmitypes.
    apply Forall2_spec; first by apply those_length in Hmitypes; rewrite List.map_length in Hmitypes.
    move => n mi extt Hminth Htinth.
    eapply those_spec in Hmitypes; eauto.
    rewrite List.nth_error_map in Hmitypes.
    rewrite Hminth in Hmitypes.
    simpl in Hmitypes.
    destruct mi; simpl in *.
    injection Hmitypes as Hmitypes.
    unfold module_import_typer in Hmitypes.
    unfold module_import_typing.
    destruct imp_desc => //=.
    (* func *)
    { destruct (n0 < length mod_types) eqn:Hlt => //.
      destruct (mod_types !! n0) eqn:Hmtnth => //.
      injection Hmitypes as <-.
      by apply/andP.
    }
    (* tab *)
    { destruct (module_tab_typing _) eqn:Hmtt => //.
      injection Hmitypes as <-.
      by apply/andP.
    }
    (* mem *)
    { destruct (module_mem_typing _) eqn:Hmtt => //.
      injection Hmitypes as <-.
      by apply/andP.
    }
    (* glob *)
    { by injection Hmitypes as <-. }
  }
  (* exports *)
  { clear - Hmexptypes.
    unfold module_exports_typer in Hmexptypes.
    apply Forall2_spec; first by apply those_length in Hmexptypes; rewrite List.map_length in Hmexptypes.
    move => n me extt Hmexpth Htexpth.
    eapply those_spec in Hmexptypes; eauto.
    rewrite List.nth_error_map in Hmexptypes.
    rewrite Hmexpth in Hmexptypes.
    simpl in Hmexptypes.
    destruct me; simpl in *.
    injection Hmexptypes as Hmexptypes.
    unfold module_export_typer in Hmexptypes.
    unfold module_export_typing.
    simpl in *.
    destruct modexp_desc => //=.
    (* func *)
    { destruct f => /=.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
    (* tab *)
    { destruct t.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
    (* mem *)
    { destruct m.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
    (* glob *)
    { destruct g.
      destruct (n0 < _) eqn:Hlt => //.
      destruct (_ !! n0) eqn:Hnth => //.
      injection Hmexptypes as <-.
      by apply/andP.
    }
  }
Admitted.

Section Interp_instantiate.
  
Import interpreter_func.EmptyHost.
Import Interpreter_ctx_extract.

Let instantiate := instantiate host_function_eqType host_instance.

Lemma external_type_checker_sound: forall s ext t,
  external_type_checker s ext t = true ->
  external_typing host_function_eqType s ext t.
Proof.
  move => s ext t Hextcheck.
  unfold external_type_checker in Hextcheck.
  destruct ext as [[i] | [i] | [i] | [i]]; destruct t => //; remove_bools_options; subst.
  - by eapply ETY_func; eauto.
  - by eapply ETY_tab; eauto.
  - by eapply ETY_mem; eauto.
  - by eapply ETY_glob; eauto.
Qed.

Lemma interp_alloc_sound: forall s m v_imps g_inits s' inst' v_exps',
  length g_inits = length m.(mod_globals) ->
  interp_alloc_module host_function_eqType s m v_imps g_inits = (s', inst', v_exps') ->
  alloc_module host_function_eqType s m v_imps g_inits (s', inst', v_exps').
Proof.
  move => s m v_imps g_inits s' inst' v_exps' Hgvs_len Halloc.
  unfold interp_alloc_module in Halloc.
  unfold alloc_module.
  destruct (alloc_funcs _ _ _ _) as [s1 ifs] eqn:Hallocfuncs.
  destruct (alloc_tabs _ _ _) as [s2 its] eqn:Halloctabs.
  destruct (alloc_mems _ _ _) as [s3 ims] eqn:Hallocmems.
  destruct (alloc_globs _ _ _) as [s4 igs] eqn:Hallocglobs.

  injection Halloc as <-<-<-.
  rewrite Hallocfuncs Halloctabs Hallocmems Hallocglobs => /=.
  apply alloc_func_gen_index in Hallocfuncs.
  apply alloc_tab_gen_index in Halloctabs.
  apply alloc_mem_gen_index in Hallocmems.
  
  apply alloc_glob_gen_index in Hallocglobs; last assumption.

  destruct Hallocfuncs as [Hifs [Hfunc1 [Htab1 [Hmem1 Hglob1]]]]; simpl in *.
  destruct Halloctabs as [Hits [Htab2 [Hfunc2 [Hmem2 Hglob2]]]]; simpl in *.
  destruct Hallocmems as [Hims [Hmem3 [Hfunc3 [Htab3 Hglob3]]]]; simpl in *.
  destruct Hallocglobs as [Higs [Hglob4 [Hfunc4 [Htab4 Hmem4]]]]; simpl in *.

  destruct s, s1, s2, s3, s4; simpl in *.
  rewrite <- Hfunc4 in *. rewrite <- Hfunc3 in *. rewrite <- Hfunc2 in *. rewrite -> Hfunc1 in *.
  rewrite <- Htab4 in *. rewrite <- Htab3 in *. rewrite -> Htab2 in *. rewrite <- Htab1 in *.
  rewrite <- Hmem4 in *. rewrite -> Hmem3 in *. rewrite <- Hmem2 in *. rewrite <- Hmem1 in *.
  rewrite -> Hglob4 in *. rewrite <- Hglob3 in *. rewrite <- Hglob2 in *. rewrite <- Hglob1 in *.
  rewrite gen_index_iota in Hifs.
  rewrite List.map_length gen_index_iota in Hits.
  rewrite gen_index_iota in Hims.
  rewrite gen_index_iota in Higs.
  repeat (apply/andP; split => //).
  - rewrite - Hifs => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction ifs as [ | a ?] => //=; destruct a; f_equal => //.
  - rewrite - Hits => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction its as [ | a ?] => //=; destruct a; f_equal => //.
  - rewrite - Hims => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction ims as [ | a ?] => //=; destruct a; f_equal => //.
  - rewrite Hgvs_len PeanoNat.Nat.min_id -Higs => /=.
    apply/eqP; repeat f_equal.
    clear.
    by induction igs as [ | a ?] => //=; destruct a; f_equal => //.
Qed.

(* Breaking circularity: the global initialisers need to be well-typed under a
   context with only the imported globals added. *)
Lemma module_typecheck_glob_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    let c' :=
      {|
        tc_types_t := [::];
        tc_func_t := [::];
        tc_global := ext_t_globs t_imps;
        tc_table := [::];
        tc_memory := [::];
        tc_local := [::];
        tc_label := [::];
        tc_return := None
      |} in
    all (module_glob_type_checker c') m.(mod_globals).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  simpl in *.
  by injection Hmodcheck as ->->.
Qed.

Lemma module_typecheck_elem_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_elem_type_checker c) m.(mod_elem).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  simpl in *.
  by eexists; apply Helemcheck.
Qed.

Lemma module_typecheck_data_aux: forall m t_imps t_exps,
    module_type_checker m = Some (t_imps, t_exps) ->
    exists c, all (module_data_type_checker c) m.(mod_data).
Proof.
  move => m t_imps t_exps.
  unfold module_type_checker.
  move => Hmodcheck.
  destruct m.
  destruct (gather_m_f_types mod_types mod_funcs) as [fts | ] eqn:Hmftypes => //;
  destruct (module_imports_typer mod_types mod_imports) eqn:Hmitypes => //.
  destruct (all _ _ && _ && _ && _ && _ && _ && _ ) eqn:Hallcond => //.
  destruct (module_exports_typer _ mod_exports) eqn:Hmexptypes => //.
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hstartcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hdatacheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Helemcheck].
  move/andP in Hallcond; destruct Hallcond as [Hallcond Hglobcheck].
  simpl in *.
  by eexists; apply Hdatacheck.
Qed.

(* A slightly difficult proof due to having to prove additional properties of the certified interpreter.
   Note that the reduction property can be obtained trivially, but any additional proofs on top are difficult.
   In this case, we're 'misusing' the interpreter (running with the technically 'wrong' store) and proving that 
   the result is still correct regardless -- therefore the predictable trouble here. *)
Lemma interp_get_v_sglob: forall s inst j k,
    interp_get_v s inst [::BI_get_global j] = Some k ->
    sglob_val s inst j = Some k.
Proof.
  move => s inst j k Heval.
  unfold interp_get_v, run_multi_step_raw, interpreter_ctx.run_multi_step_raw in Heval.
  destruct (interpreter_ctx.run_v_init s _) eqn:Hrvi => //.
  cbn in Hrvi.
  injection Hrvi as <-.
  destruct (run_multi_step_ctx _ _) as [ | vs] eqn:Hrmsc => //.
  do 2 destruct vs => //.
  injection Heval as ->.
  unfold run_multi_step_ctx in Hrmsc.
  
  destruct (interpreter_ctx.run_one_step_ctx _ _) as [? cfg Hred | rvs | | ] eqn:Hrosc => //; last by destruct rvs => //.
  destruct cfg as [[[hs ccs] sc] e].
  simpl in Hred.

  simpl in Hrosc.

  move: Hrosc.

  (* Coq's destruct has no clue on how to generalize the terms correctly. *)
  move: (@Logic.eq_refl (option value) (sglob_val s inst j)).
  case: {2 3} (sglob_val s inst j) => /=.

  - move => v Hsglob Heval.
    inversion Heval; subst; clear Heval.
    simpl in Hrmsc.
    inversion Hrmsc; subst.
Admitted.
    
Lemma interp_get_v_reduce: forall hs s c inst k bes,
    const_exprs c bes ->
    be_typing c bes (Tf [::] [::T_i32]) ->
    interp_get_v s inst bes = Some k ->
    @reduce_trans host_function_eqType host_instance (hs, s, (Build_frame nil inst), (to_e_list bes))
                 (hs, s, (Build_frame nil inst), [::AI_basic (BI_const k)]).
Proof.
  move => hs s c inst bes k Hconst Hbet Heval.
  eapply const_exprs_impl in Hconst; eauto.
  destruct Hconst as [be [-> Hconst]].
  destruct be => //=.
  - apply interp_get_v_sglob in Heval.
    constructor.
    unfold reduce_tuple.
    by apply r_get_global.
  - unfold interp_get_v in Heval.
    simpl in Heval.
Admitted.

Lemma interp_instantiate_imp_instantiate :
  forall s m v_imps s_end inst v_exps start,
  interp_instantiate s m v_imps = Some ((s_end, inst, v_exps), start) ->
  instantiate s m v_imps ((s_end, inst, v_exps), start).
Proof.
Admitted.

End Interp_instantiate.
