(* Adapted from the exact fe3c7ea pending-code proof, not a branch import.
   Type the actual mapi-generated segment and start instructions. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Stdlib Require Import List NArith Lia.
From Wasm Require Import instantiation_spec type_checker_reflects_typing type_preservation.
Set SsrOldRewriteGoalsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.
Context `{ho : host}.

Lemma const_check_context C D es ct :
  tc_types C = tc_types D -> tc_funcs C = tc_funcs D ->
  tc_globals C = tc_globals D -> tc_refs C = tc_refs D ->
  const_exprs C es ->
  type_checker.check C es ct = type_checker.check D es ct.
Proof.
  move => T F G R; move: ct.
  induction es as [|e es IH]; move => ct /= All; first reflexivity.
  move/andP: All => [Head Tail].
  have Step : type_checker.check_single C ct e = type_checker.check_single D ct e.
  { destruct e; cbn [const_expr] in Head => //;
      cbn [type_checker.check_single]; by rewrite ?T ?F ?G ?R. }
  change (type_checker.check C es (type_checker.check_single C ct e) =
    type_checker.check D es (type_checker.check_single D ct e)).
  rewrite Step. by apply IH.
Qed.

Lemma const_typing_context C D es tf :
  tc_types C = tc_types D -> tc_funcs C = tc_funcs D ->
  tc_globals C = tc_globals D -> tc_refs C = tc_refs D ->
  const_exprs C es -> be_typing C es tf -> be_typing D es tf.
Proof.
  move => T F G R Const Typed.
  apply/b_e_type_checker_reflects_typing.
  move/b_e_type_checker_reflects_typing: Typed => Typed.
  destruct tf as [ins outs].
  unfold type_checker.b_e_type_checker, type_checker.b_e_type_checker_aux in *.
  have Equal :
      List.fold_left (type_checker.check_single (type_checker.context_reverse C)) es
        (Some (type_checker.Build_checker_type (seq.rev ins) false)) =
      List.fold_left (type_checker.check_single (type_checker.context_reverse D)) es
        (Some (type_checker.Build_checker_type (seq.rev ins) false)).
  { apply const_check_context.
    - cbn. by rewrite T.
    - cbn. by rewrite F.
    - exact G.
    - exact R.
    - exact Const. }
  rewrite -Equal. exact Typed.
Qed.

Lemma get_init_expr_elem_typing C i elem rt :
  lookup_N C.(tc_elems) (N.of_nat i) = Some rt ->
  module_elem_typing C elem rt ->
  be_typing C (get_init_expr_elem i elem) (Tf nil nil).
Proof.
  move => Elem Typed.
  destruct elem as [et inits mode].
  destruct Typed as [Equal [Inits Mode]]; subst rt.
  destruct mode as [|tidx offset|]; cbn in *.
  - apply bet_empty.
  - destruct Mode as [[limits element] [Table [Element [Offset Const]]]].
    eapply bet_composition'; first exact Offset.
    eapply bet_composition_front with (t2s := [::T_num T_i32; T_num T_i32]).
    + apply bet_weakening_empty_1 with (ts := [::T_num T_i32]). apply bet_const_num.
    + eapply bet_composition_front with (t2s := [::T_num T_i32; T_num T_i32; T_num T_i32]).
      * apply bet_weakening_empty_1 with (ts := [::T_num T_i32; T_num T_i32]).
        apply bet_const_num.
      * eapply bet_composition_front with (t2s := nil).
        -- eapply bet_table_init; eauto.
        -- eapply bet_elem_drop; eauto.
  - eapply bet_elem_drop; eauto.
Qed.

Lemma get_init_expr_start_typing C start :
  pred_option (module_start_typing C) start ->
  be_typing C (get_init_expr_start start) (Tf nil nil).
Proof.
  destruct start as [[idx]|]; cbn; [|move => _; apply bet_empty].
  unfold module_start_typing; cbn.
  destruct (lookup_N (tc_funcs C) idx) as [tf|] eqn:Lookup => //.
  move/eqP => Typed; subst tf. by apply bet_call.
Qed.

Lemma mapi_forall {A B} (P : B -> Prop) (f : nat -> A -> B) xs :
  (forall n a, List.nth_error xs n = Some a -> P (f n a)) ->
  List.Forall P (mapi f xs).
Proof.
  unfold mapi.
  suff Aux : forall rest i acc,
      List.Forall P acc ->
      (forall n a, List.nth_error rest n = Some a -> P (f (i + n)%coq_nat a)) ->
      List.Forall P (mapi_aux (i, acc) f rest).
  { move => Each; apply Aux; [constructor|].
    move => n a Lookup. exact (Each n a Lookup). }
  move => rest; induction rest as [|a rest IH]; move => i acc Acc Each.
  - cbn [mapi_aux]. now apply List.Forall_rev.
  - cbn [mapi_aux]; apply IH.
    + constructor; [|exact Acc].
      replace i with (i + 0)%coq_nat by lia.
      apply Each with (n := 0%coq_nat). reflexivity.
    + move => n b Lookup.
      change (P (f (Nat.add (Nat.add i 1) n) b)).
      replace (Nat.add (Nat.add i 1) n) with (Nat.add i (S n)) by lia.
      exact (Each (S n) b Lookup).
Qed.

Lemma concat_initializers_typing C codes :
  List.Forall (fun code => be_typing C code (Tf nil nil)) codes ->
  be_typing C (List.concat codes) (Tf nil nil).
Proof.
  move => All; induction All; cbn; [apply bet_empty|].
  by eapply bet_composition'; eauto.
Qed.

Lemma get_init_expr_data_typing C i data :
  size C.(tc_mems) <= 1 ->
  lookup_N C.(tc_datas) (N.of_nat i) = Some tt ->
  module_data_typing C data tt ->
  be_typing C (get_init_expr_data i data) (Tf nil nil).
Proof.
  move => Count Data Typed. destruct data as [init [|midx offset]]; cbn in *.
  - apply bet_empty.
  - destruct Typed as [[mem [Memory [Offset Const]]] _].
    have Index : midx = N0.
    { apply nth_error_Some_length in Memory.
      have CountNat : (length (tc_mems C) <= 1)%coq_nat.
      { apply/leP. by rewrite length_is_size. }
      apply Nnat.N2Nat.inj. simpl.
      lia. }
    subst midx.
    eapply bet_composition'; first exact Offset.
    eapply bet_composition_front with (t2s := [::T_num T_i32; T_num T_i32]).
    + apply bet_weakening_empty_1 with (ts := [::T_num T_i32]). apply bet_const_num.
    + eapply bet_composition_front with (t2s := [::T_num T_i32; T_num T_i32; T_num T_i32]).
      * apply bet_weakening_empty_1 with (ts := [::T_num T_i32; T_num T_i32]).
        apply bet_const_num.
      * eapply bet_composition_front with (t2s := nil).
        -- eapply bet_memory_init; eauto.
        -- eapply bet_data_drop; eauto.
Qed.

Lemma const_exprs_context C D es :
  tc_globals C = tc_globals D -> const_exprs C es = const_exprs D es.
Proof.
  move => Globals. unfold const_exprs. apply eq_all.
  move => e. by destruct e; cbn [const_expr]; rewrite ?Globals.
Qed.

Lemma module_elem_typing_context C D elem rt :
  tc_types C = tc_types D -> tc_funcs C = tc_funcs D ->
  tc_globals C = tc_globals D -> tc_refs C = tc_refs D ->
  tc_tables C = tc_tables D ->
  module_elem_typing C elem rt -> module_elem_typing D elem rt.
Proof.
  move => Types Funcs Globals Refs Tables.
  destruct elem as [et inits mode]; move => [Equal [Inits Mode]].
  split; [exact Equal|]; split.
  - eapply List.Forall_impl; last exact Inits.
    move => es [Const Typed]; split; first by rewrite -(const_exprs_context es Globals).
    eapply const_typing_context; eauto.
  - destruct mode as [|idx offset|] => //.
    destruct Mode as [[limits element] [Lookup [Elem [Offset Const]]]].
    exists (Build_table_type limits element); split.
    + by rewrite -Tables.
    + split; first exact Elem. split; last by rewrite -(const_exprs_context offset Globals).
      eapply const_typing_context; eauto.
Qed.

Lemma module_data_typing_context C D data dat :
  tc_types C = tc_types D -> tc_funcs C = tc_funcs D ->
  tc_globals C = tc_globals D -> tc_refs C = tc_refs D ->
  tc_mems C = tc_mems D ->
  module_data_typing C data dat -> module_data_typing D data dat.
Proof.
  move => Types Funcs Globals Refs Memories.
  destruct data as [init mode]; move => [Mode Equal].
  split; last exact Equal.
  destruct mode as [|idx offset] => //.
  destruct Mode as [mem [Lookup [Offset Const]]].
  exists mem; split; first by rewrite -Memories.
  split; last by rewrite -(const_exprs_context offset Globals).
  eapply const_typing_context; eauto.
Qed.

Theorem pending_initialization_code_typing Cinit C elems datas start :
  tc_types Cinit = tc_types C -> tc_funcs Cinit = tc_funcs C ->
  tc_globals Cinit = tc_globals C -> tc_refs Cinit = tc_refs C ->
  tc_tables Cinit = tc_tables C -> tc_mems Cinit = tc_mems C ->
  size C.(tc_mems) <= 1 ->
  List.Forall2 (module_elem_typing Cinit) elems C.(tc_elems) ->
  List.Forall2 (module_data_typing Cinit) datas C.(tc_datas) ->
  pred_option (module_start_typing C) start ->
  be_typing C
    (get_init_expr_elems elems ++ get_init_expr_datas datas ++ get_init_expr_start start)
    (Tf nil nil).
Proof.
  move => Types Funcs Globals Refs Tables Memories Count Elems Datas Start.
  eapply bet_composition'.
  - unfold get_init_expr_elems; apply concat_initializers_typing; apply mapi_forall.
    move => n elem Lookup.
    destruct (Forall2_nth_impl Elems Lookup) as [rt [Rt Typed]].
    eapply get_init_expr_elem_typing.
    + unfold lookup_N. rewrite Nnat.Nat2N.id. exact Rt.
    + eapply module_elem_typing_context; eauto.
  - eapply bet_composition'.
    + unfold get_init_expr_datas; apply concat_initializers_typing; apply mapi_forall.
      move => n data Lookup.
      destruct (Forall2_nth_impl Datas Lookup) as [dat [Dat Typed]].
       destruct dat. eapply get_init_expr_data_typing.
       * exact Count.
       * unfold lookup_N. rewrite Nnat.Nat2N.id. exact Dat.
      * eapply module_data_typing_context; eauto.
    + by apply get_init_expr_start_typing.
Qed.

End Host.
