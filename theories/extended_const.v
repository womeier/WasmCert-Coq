(** Correctness of the terminating extended-constant evaluator. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import instantiation_func type_checker_reflects_typing.
From Stdlib Require Import Relations Relation_Operators.

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
    move => [<-].
    rewrite rev_cons /v_to_e_list map_rcons -cats1 /=.
    apply rt_refl.
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

Theorem interp_global_chain_sound hs s f gs s' f' vs :
  interp_global_chain s f gs = Some (s', f', vs) ->
  global_init_chain hs s f gs s' f' vs.
Proof.
  move: s f s' f' vs.
  induction gs as [|g gs IH]; move => s f s' f' vs; cbn [interp_global_chain].
  - move => [<- <- <-].
    constructor.
  - destruct (interp_get_const s f (modglob_init g)) as [v|] eqn:Heval => //.
    destruct (alloc_glob s (g, v)) as [s1 addr] eqn:Halloc.
    destruct (interp_global_chain s1 (const_frame_add_global f addr) gs)
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
    destruct (alloc_glob s (g, v)) as [s1 addr].
    destruct (interp_global_chain s1 (const_frame_add_global f addr) gs)
      as [[[s2 f2] ws]|] eqn:Hchain => //.
    move => H; injection H as _ _ <- => /=.
    by rewrite (IH _ _ _ _ _ Hchain).
Qed.

End Host.
