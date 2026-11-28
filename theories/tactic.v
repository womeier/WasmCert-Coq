From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import properties typing_inversion closed_typing_properties.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Ltac size_unequal H :=
  repeat rewrite length_is_size in H;
  revert H;
  repeat rewrite size_cat; repeat rewrite size_rev; repeat rewrite size_map; repeat rewrite size_drop; repeat rewrite size_take; simpl; lias.

(** A common pattern in the proof: using an hypothesis on the form [rev l = l'] to rewrite [l]. **)
Ltac subst_rev_const_list :=
 repeat lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

(** Simplify the lists in the goal. **)
Ltac simplify_lists :=
  (** Common rewriting rules. **)
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK
    | rewrite length_is_size
    | rewrite size_take
    | rewrite size_drop
    | rewrite size_rev
    | rewrite size_cat
    | rewrite v_to_e_size
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat
    | rewrite -v_to_e_rev
    | rewrite -v_to_e_take
    | rewrite -v_to_e_drop];
  (** Putting all the lists into a normal form, as concatenations of as many things.
    Because [cat1s] conflicts with [cats0], replacing any occurence of [[X]] to
    [[X] ++ [::]], it has to be done separately.
    Rewrite with the associated [math goal with] is avoid to deal with existential
    vairables. **)
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end;
  repeat lazymatch goal with
  | |- context C [[::] ++ _] => rewrite cat0s
  | |- context C [_ ++ [::]] => rewrite cats0
  | |- context C [_ + ?n - ?n] => rewrite addnK
  | |- context C [size (_ ++ _)] => rewrite size_cat
  | |- context C [take (size ?l) (?l ++ _)] => rewrite take_size_cat
  | |- context C [rcons _ _] => rewrite -cats1
  | |- context C [(_ ++ _) ++ _] => rewrite -catA
  | |- context C [rev [::]] => rewrite rev0
  | |- context C [v_to_e_list [::]] => simpl v_to_e_list at 1
  | |- context C [v_to_e_list [:: _]] => simpl v_to_e_list at 1
  end;
  try subst_rev_const_list.

(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail).


(* Looking up from instances, stores, and contexts *)
Ltac inst_typing_lookup :=
  try multimatch goal with
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_function_type (inst_types ?i) ?n = Some _ |- _ =>
      let Hteq := fresh "Hteq" in
      specialize (Logic.eq_sym (inst_typing_type_lookup n H1)) as Hteq;
      rewrite H2 in Hteq
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_funcs ?i) _ = Some _ |- _ =>
      let ft := fresh "ft" in
      let Hextft := fresh "Hextft" in
      let Hnthft := fresh "Hnthft" in
      specialize (inst_typing_func_lookup H1 H2) as [ft [Hextft Hnthft]];
      unfold instance_function_view, lookup_func_defined_type in Hextft
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_tables ?i) _ = Some _ |- _ =>
      let tabt := fresh "tabt" in
      let Hexttabt := fresh "Hexttabt" in
      let Hnthtabt := fresh "Hnthtabt" in
      specialize (inst_typing_table_lookup H1 H2) as [tabt [Hexttabt Hnthtabt]];
      unfold instance_table_view, ext_table_typing in Hexttabt
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_mems ?i) _ = Some _ |- _ =>
      let mt := fresh "mt" in
      let Hextmt := fresh "Hextmt" in
      let Hnthmt := fresh "Hnthmt" in
      specialize (inst_typing_mem_lookup H1 H2) as [mt [Hextmt Hnthmt]];
      unfold ext_mem_typing in Hextmt
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_globals ?i) _ = Some _ |- _ =>
      let gt := fresh "gt" in
      let Hextgt := fresh "Hextgt" in
      let Hnthgt := fresh "Hnthgt" in
      specialize (inst_typing_global_lookup H1 H2) as [gt [Hextgt Hnthgt]];
      unfold instance_global_view, ext_global_typing in Hextgt
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_elems ?i) _ = Some _ |- _ =>
      let et := fresh "et" in
      let ei := fresh "ei" in
      let Hnthselem := fresh "Hnthselem" in
      let Helemtype := fresh "Helemtype" in
      let Hnthet := fresh "Hnthet" in
      specialize (inst_typing_elem_lookup H1 H2) as [et [ei [Hnthselem [Helemtype Hnthet]]]];
      unfold instance_element_view in Helemtype
  | H1: inst_typing ?s ?i = Some ?t,
    H2: lookup_N (inst_datas ?i) _ = Some _ |- _ =>
      let dt := fresh "et" in
      let di := fresh "di" in
      let Hnthsdata := fresh "Hnthsdata" in
      let Hdatatype := fresh "Hdatatype" in
      let Hnthdt := fresh "Hnthdt" in
      specialize (inst_typing_data_lookup H1 H2) as [dt [di [Hnthsdata [Hdatatype Hnthdt]]]]
  end.

Ltac store_typing_lookup :=
  try multimatch goal with
  | H1: store_typing ?s,
      H2: lookup_N (s_funcs ?s) _ = Some _ |- _ =>
      let ft := fresh "ft" in
      let Hft := fresh "Hft" in
      specialize (store_typing_func_lookup H1 H2) as [ft Hft];
      unfold funcinst_typing in Hft
  | H1: store_typing ?s,
      H2: lookup_N (s_tables ?s) _ = Some _ |- _ =>
      let tabt := fresh "tabt" in
      let Htabt := fresh "Htabt" in
      specialize (store_typing_table_lookup H1 H2) as [tabt Htabt];
      unfold tableinst_typing in Htabt
  | H1: store_typing ?s,
      H2: lookup_N (s_mems ?s) _ = Some _ |- _ =>
      let mt := fresh "mt" in
      let Hmt := fresh "Hmt" in
      specialize (store_typing_mem_lookup H1 H2) as [mt Hmt];
      unfold meminst_typing in Hmt
  | H1: store_typing ?s,
      H2: lookup_N (s_globals ?s) _ = Some _ |- _ =>
      let gt := fresh "gt" in
      let Hgt := fresh "Hgt" in
      specialize (store_typing_global_lookup H1 H2) as [gt Hgt];
      unfold globalinst_typing in Hgt
  | H1: store_typing ?s,
      H2: lookup_N (s_elems ?s) _ = Some _ |- _ =>
      let et := fresh "et" in
      let Het := fresh "Het" in
      specialize (store_typing_elem_lookup H1 H2) as [et Het];
      unfold eleminst_typing in Het
  | H1: store_typing ?s,
      H2: lookup_N (s_datas ?s) _ = Some _ |- _ =>
      let dt := fresh "dt" in
      let Hdt := fresh "Hdt" in
      specialize (store_typing_data_lookup H1 H2) as [dt Hdt];
      unfold datainst_typing in Hdt
  end.

Ltac resolve_store_inst_lookup :=
  store_typing_lookup; inst_typing_lookup.

Ltac unfold_store_operations :=
  repeat match goal with
    | _: context [ stab_update _ _ _ _ ] |- _ =>
        unfold stab_update in *; remove_bools_options
    | _: context [ supdate_glob _ _ _ _ ] |- _ =>
        unfold supdate_glob, supdate_glob_s, sglob_ind, option_bind, option_map in *; remove_bools_options
    | _: context [ sglob_val _ _ ] |- _ =>
        unfold sglob_val, sglob, sglob_ind in *; remove_bools_options
    | _: context [ stab_elem _ _ ] |- _ =>
        unfold stab_elem in *; remove_bools_options
    | _: context [ stab_grow _ _ ] |- _ =>
        unfold stab_grow, growtable in *; remove_bools_options
    | _: context [ mem_grow _ _ ] |- _ =>
        unfold mem_grow in *; remove_bools_options
    | _: context [ stab _ _ ] |- _ =>
        unfold stab in *; remove_bools_options
    | _: context [ smem _ _ ] |- _ =>
        unfold smem in *; remove_bools_options
    | _: context [ smem_store _ _ ] |- _ =>
        unfold smem_store in *; remove_bools_options
    | _: context [ smem_store_packed _ _ ] |- _ =>
        unfold smem_store_packed in *; remove_bools_options
    | _: context [ smem_store_vec _ _ ] |- _ =>
        unfold smem_store_vec in *; remove_bools_options
    | _: context [ smem_store_vec_lane _ _ ] |- _ =>
        unfold smem_store_vec_lane in *; remove_bools_options
    | _: context [ smem_grow _ _ ] |- _ =>
        unfold smem_grow in *; remove_bools_options
    | _: context [ smem_ind _ _ ] |- _ =>
        unfold smem_ind in *; remove_bools_options
    | _: context [ selem _ _ ] |- _ =>
        unfold selem in *; remove_bools_options
    | _: context [ sdata _ _ ] |- _ =>
        unfold sdata in *; remove_bools_options
    | _: context [ selem_drop _ _ _ ] |- _ =>
        unfold selem_drop, selem in *; remove_bools_options
    | _: context [ sdata_drop _ _ _ ] |- _ =>
        unfold sdata_drop, sdata in *; remove_bools_options
    end.

Ltac resolve_if_true_eq :=
  match goal with
  | |- match ?expr with
            | true => Some ?x
            | false => None
            end = Some ?x =>
      let Htrue := fresh "Htrue" in
      assert (expr = true) as Htrue; last by rewrite Htrue
  | |- exists x, match ?expr with
            | true => _
            | false => None
            end = Some x =>
      let Htrue := fresh "Htrue" in
      assert (expr = true) as Htrue; last rewrite Htrue
  | |- match ?expr with
            | Some _ => _
            | None => None
            end = Some ?x =>
      let Hsome := fresh "Hsome" in
      let x := fresh "x" in
      assert (exists x, expr = Some x) as [x Hsome]; last rewrite Hsome
  | |- exists x, match ?expr with
            | Some _ => _
            | None => None
            end = Some x =>
      let Hsome := fresh "Hsome" in
      let y := fresh "y" in
      assert (exists y, expr = Some y) as [y Hsome]; last rewrite Hsome
  end.

Ltac simplify_multieq :=
  repeat match goal with
  | H1: ?expr = ?x,
    H2: ?expr = ?y |- _ =>
      rewrite H1 in H2
  | H: Some ?x = Some ?y |- _ =>
      let Hinj := fresh "Hinj" in
     injection H as Hinj; try subst
    end.

Ltac simplify_closed_operands :=
  repeat match goal with
  | H: is_true (closed_value_typing ?s (VAL_num ?n) ?t) |- _ =>
    let Equal := fresh "NumberType" in
    pose proof (closed_num_type s n t H) as Equal; clear H;
    first [is_var t; subst t | inversion Equal; subst; clear Equal]
  | H: is_true (closed_value_typing ?s (VAL_vec ?v) ?t) |- _ =>
    let Equal := fresh "VectorType" in
    pose proof (closed_vec_type s v t H) as Equal; clear H;
    first [is_var t; subst t | inversion Equal; subst; clear Equal]
  | H: closed_stack_results_subtyping _ nil _ |- _ =>
    inversion H; subst; clear H
  | H: closed_stack_results_subtyping _ (cons _ _) (cons _ _) |- _ =>
    inversion H; subst; clear H
  | H: closed_stack_value_subtyping ?registry (CO_value (CV_num ?n)) ?t |- _ =>
    let Equal := fresh "NumberSubtype" in
    pose proof (closed_num_operand_subtype registry n t H) as Equal;
    clear H; cbn [interpret_operand_type close_operand_type
      gc_type_context.close_value_type] in Equal;
    inversion Equal; subst; clear Equal
  | H: closed_stack_value_subtyping ?registry (CO_value (CV_vec ?v)) ?t |- _ =>
    let Equal := fresh "VectorSubtype" in
    pose proof (closed_vec_operand_subtype registry v t H) as Equal;
    clear H; cbn [interpret_operand_type close_operand_type
      gc_type_context.close_value_type] in Equal;
    inversion Equal; subst; clear Equal
  end.

Ltac fold_closed_subtyping :=
  repeat match goal with
  | H: (exists p p' ins outs,
      ?expected_inputs = p ++ ins /\
      ?expected_outputs = p' ++ outs /\
      closed_stack_results_subtyping ?registry p p' /\
      closed_stack_results_subtyping ?registry ins ?inputs /\
      closed_stack_results_subtyping ?registry ?outputs outs) |- _ =>
    progress change (closed_instr_subtyping registry (Closed_ft inputs outputs)
      (Closed_ft expected_inputs expected_outputs)) in H
  end.

(** Only established closed algebra is used here. Unequal-sized overlaps are
    left to explicit proof rather than guessed concrete/source intermediates. *)
Ltac unify_closed_principal :=
  fold_closed_subtyping;
  repeat match goal with
  | First: closed_instr_subtyping ?registry (Closed_ft ?a ?b) (Closed_ft ?x ?y),
    Last: closed_instr_subtyping ?registry (Closed_ft ?b' ?c) (Closed_ft ?y ?z) |- _ =>
    let Principal := fresh "Hprincipal" in
    let Middle := fresh "Hsub" in
    first [
      constr_eq b (@nil closed_operand_type);
      pose proof (closed_instr_compose_nil1 registry a b' c x y z First Last) as Principal
    | constr_eq b' (@nil closed_operand_type);
      pose proof (closed_instr_compose_nil2 registry a b c x y z First Last) as Principal
    | let Length := fresh "MiddleLength" in
      assert (Length : length b = length b') by reflexivity;
      destruct (closed_instr_compose_eq registry a b b' c x y z First Last Length)
        as [Principal Middle]; clear Length
    ]; clear First Last
  end;
  simplify_closed_operands.

Ltac resolve_closed_subtyping :=
  fold_closed_subtyping;
  try fold closed_instr_subtyping;
  first [assumption
    | match goal with
      | First: closed_instr_subtyping ?r ?a ?b,
        Last: closed_instr_subtyping ?r ?b ?c |-
          closed_instr_subtyping ?r ?a ?c =>
        exact (closed_instr_trans r a b c First Last)
      end
    | apply closed_instr_refl | apply closed_stack_results_refl
    | apply csv_refl | apply csv_bot].

Ltac resolve_e_typing :=
  repeat lazymatch goal with
    (* This is usually required and should be applied at highest priority *)
    | H: is_true (?ts1 <ts: ?ts2) |-
        e_typing _ _ _ (Tf ?ts1 ?ts2) =>
        eapply ety_subtyping; try by eapply instr_subtyping_empty_impl; apply H
    | H: ((Tf ?ts1 ?ts2) <ti: (Tf ?ts3 ?ts4)) |-
        e_typing _ _ _ (Tf ?ts3 ?ts4) =>
        eapply ety_subtyping; try by apply H
     | |- e_typing _ _ nil _ =>
         try eapply ety_subtyping; first (by apply ety_empty); eauto => //
    | |- e_typing _ _ [::AI_basic _] _ =>
         try eapply ety_subtyping; first (by apply ety_a' => //; econstructor; eauto; try apply instr_subtyping_eq); eauto => //
     | |- e_typing _ _ [::AI_ref_i31 _] _ =>
          try eapply ety_subtyping;
           first (apply ety_ref_i31 with (t := Closed_ref false (CH_abstract HT_i31)); reflexivity);
          eauto => //
    | |- e_typing _ _ (v_to_e_list _) _ =>
        try eapply ety_subtyping; first (by eapply et_values_typing; eauto); eauto => //
    | |- e_typing _ _ ((cons ($VN ?v) ?es)) _ =>
        apply value_num_cons_e_typing
    | |- e_typing _ _ ((cons ($V (VAL_vec ?v)) ?es)) _ =>
        apply value_vec_cons_e_typing
     | H: is_true (value_typing ?s ?names ?v ?t) |-
        e_typing _ _ ((cons ($V ?v) ?es)) _ =>
        apply (value_cons_e_typing H)
     | H: is_true (value_typing ?s ?names (VAL_ref ?v) ?t) |-
        e_typing _ _ ((cons (vref_to_e ?v) ?es)) _ =>
        replace (vref_to_e v) with ($V (VAL_ref v)); last done;
        apply (value_cons_e_typing H)
     | H: is_true (values_typing ?s ?names ?vs ?ts) |-
        e_typing _ _ ((v_to_e_list ?vs ++ ?es)) _ =>
        apply (values_cat_e_typing H)
    | H : is_true (const_list _) |- _ =>
        let vs := fresh "vs" in
        apply const_es_exists in H as [vs ->]; invert_e_typing
     | _ => try solve [resolve_closed_subtyping];
         unfold_store_operations; resolve_subtyping => //; simplify_lists; simplify_multieq; simpl in * => //
    end.
