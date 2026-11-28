(** Typing inversion lemmas **)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Stdlib Require Import Program.Equality NArith ZArith.
From Wasm Require Export common properties subtyping_properties.
From Wasm Require Import gc_function_subtyping_properties
  gc_declaration_typing gc_declaration_typing_properties closed_typing_properties
  closed_operand_properties closed_source_translation.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Typing_inversion_be.

Context `{memory: BlockUpdateMemory}.
  
(* Some quality of life lemmas *)
(* Upd: these lemmas are deprecated; it is encouraged to directly use subtyping rule. *)
Lemma bet_weakening: forall C es ts ts1 ts2,
    be_typing C es (Tf ts1 ts2) ->
    be_typing C es (Tf (ts ++ ts1) (ts ++ ts2)).
Proof.
  intros ????? Hbet.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  eapply bet_subtyping; eauto.
  by resolve_subtyping.
Qed.

Hint Constructors be_typing : core.

(* Structural inversions *)
Lemma empty_typing: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s <ts: t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //; extract_premise.
  - by destruct es.
  - unfold instr_subtyping in *.
    by extract_premise; subst.
Qed.

(* Defining a principal typing 'condition' for each instruction.
   
 *)
Definition be_principal_typing (C: t_context) (be: basic_instruction) (tf: instr_type) : Prop :=
  match be with
  | BI_const_num c =>
      tf = (Tf nil [::T_num (typeof_num c)])
  | BI_const_vec c =>
      tf = (Tf nil [::T_vec (typeof_vec c)])
  | BI_ref_null t =>
      tf = (Tf nil [::T_ref (Ref_type true t)]) /\
        source_heap_scopedb C.(tc_types) t
  | BI_ref_is_null =>
      exists t, tf = (Tf [::T_ref t] [::T_num T_i32])
  | BI_ref_i31 =>
      tf = (Tf [::T_num T_i32] [::T_ref (Ref_type false HT_i31)])
  | BI_i31_get _ =>
      exists nullable, tf =
        (Tf [::T_ref (Ref_type nullable HT_i31)] [::T_num T_i32])
  | BI_ref_as_non_null =>
      exists t, tf = (Tf [::t] [::t]) /\ is_ref_t t
  | BI_call_ref _ | BI_return_call_ref _ => False
  | BI_br_on_non_null x =>
      exists ts t,
        tf = Tf (ts ++ [::t]) ts /\
        lookup_N C.(tc_labels) x = Some (ts ++ [::t]) /\
        is_ref_t t
  | BI_ref_func x =>
      exists t, tf = (Tf [::] [::T_ref T_funcref]) /\
             lookup_N (tc_funcs C) x = Some t /\
             List.In x (tc_refs C)
  | BI_unop t op =>
      tf = (Tf [::T_num t] [::T_num t]) /\
        unop_type_agree t op
  | BI_binop t op =>
      tf = (Tf [::T_num t; T_num t] [::T_num t]) /\
        binop_type_agree t op
  | BI_testop t op =>
      tf = (Tf [::T_num t] [::T_num T_i32]) /\
        is_int_t t
  | BI_relop t op =>
      tf = (Tf [::T_num t; T_num t] [::T_num T_i32]) /\
        relop_type_agree t op
  | BI_cvtop t2 op t1 sx =>
      tf = (Tf [::T_num t1] [::T_num t2]) /\
        cvtop_valid t2 op t1 sx
  | BI_vunop op =>
      tf = (Tf [::T_vec T_v128] [::T_vec T_v128])
  | BI_vbinop op =>
      tf = (Tf [::T_vec T_v128; T_vec T_v128] [::T_vec T_v128])
  | BI_vternop op =>
      tf = (Tf [::T_vec T_v128; T_vec T_v128; T_vec T_v128] [::T_vec T_v128])
  | BI_vtestop op =>
      tf = (Tf [::T_vec T_v128] [::T_num T_i32])
  | BI_vshiftop op =>
      tf = (Tf [::T_vec T_v128; T_num T_i32] [::T_vec T_v128])
  | BI_splat_vec shape =>
      tf = (Tf [::T_num (typeof_shape_unpacked shape)] [::T_vec T_v128])
  | BI_extract_vec shape sx x =>
      tf = (Tf [::T_vec T_v128] [::T_num (typeof_shape_unpacked shape)]) /\
      N.ltb x (shape_dim shape) = true
  | BI_replace_vec shape x =>
      tf = (Tf [::T_vec T_v128; T_num (typeof_shape_unpacked shape)] [::T_vec T_v128]) /\
      N.ltb x (shape_dim shape) = true
  | BI_unreachable =>
      True (* Equivalently, put existential quantifiers and trivial equalities *)
  | BI_nop =>
      tf = (Tf nil nil)
  | BI_drop =>
      exists t, tf = (Tf [::t] nil)
  | BI_select ot =>
      exists t, tf = (Tf [::t; t; T_num T_i32] [::t]) /\
             match ot with
             | Some [::t0] => t = t0
             | None => is_numeric_type t
             | _ => False
             end
  | BI_block tb es =>
      exists tn tm,
      tf = (Tf tn tm) /\
        expand_t C tb = Some (Tf tn tm) /\
        be_typing (upd_label C ([::tm] ++ (tc_labels C))) es (Tf tn tm)
  | BI_loop tb es =>
      exists tn tm,
      tf = (Tf tn tm) /\
        expand_t C tb = Some (Tf tn tm) /\
        be_typing (upd_label C ([::tn] ++ (tc_labels C))) es (Tf tn tm)
  | BI_if tb es1 es2 =>
      exists tn tm,
      tf = (Tf (tn ++ [::T_num T_i32]) tm) /\
        expand_t C tb = Some (Tf tn tm) /\
        be_typing (upd_label C ([::tm] ++ (tc_labels C))) es1 (Tf tn tm) /\
        be_typing (upd_label C ([::tm] ++ (tc_labels C))) es2 (Tf tn tm)
  | BI_br k =>
      exists tx ty ts,
      tf = (Tf (tx ++ ts) ty) /\
        lookup_N C.(tc_labels) k = Some ts
  | BI_br_if k =>
      exists ts,
      tf = (Tf (ts ++ [::T_num T_i32]) ts) /\
        lookup_N C.(tc_labels) k = Some ts
  | BI_br_table ins k =>
      exists tx ty ts,
      tf = (Tf (tx ++ (ts ++ [::T_num T_i32])) ty) /\
        List.Forall (fun i => (exists ts', lookup_N C.(tc_labels) i = Some ts' /\ ts <ts: ts')) (ins ++ [::k])
  | BI_return =>
      exists tx ty ts,
      tf = (Tf (tx ++ ts) ty) /\
        tc_return C = Some ts
  | BI_call n =>
      exists tf0,
      tf = tf0 /\
        lookup_N (tc_funcs C) n = Some tf0
  | BI_call_indirect x y =>
      exists ts1 ts2 tabt,
      tf = (Tf (ts1 ++ [::T_num T_i32]) ts2)/\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = T_funcref /\
        lookup_function_type (tc_types C) y = Some (Tf ts1 ts2)
  | BI_return_call n =>
      exists ts1 ts2 ts3 ts4,
      tf = (Tf (ts3 ++ ts1) ts4) /\
        lookup_N (tc_funcs C) n = Some (Tf ts1 ts2) /\
        tc_return C = Some ts2
  | BI_return_call_indirect x y =>
      exists ts1 ts2 ts3 ts4 tabt,
      tf = (Tf (ts3 ++ ts1 ++ [::T_num T_i32]) ts4)/\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = T_funcref /\
        lookup_function_type (tc_types C) y = Some (Tf ts1 ts2) /\
        tc_return C = Some ts2
  | BI_local_get x =>
      exists t,
      tf = (Tf nil [::t]) /\
        lookup_N (tc_locals C) x = Some t
  | BI_local_set x =>
      exists t,
      tf = (Tf [::t] nil) /\
        lookup_N (tc_locals C) x = Some t
  | BI_local_tee x =>
      exists t,
      tf = (Tf [::t] [::t]) /\
        lookup_N (tc_locals C) x = Some t
  | BI_global_get x =>
      exists gt t,
      tf = (Tf nil [::t]) /\
        lookup_N (tc_globals C) x = Some gt /\
        tg_t gt = t
  | BI_global_set x =>
      exists gt t,
      tf = (Tf [::t] nil) /\
        lookup_N (tc_globals C) x = Some gt /\
        tg_t gt = t /\
        is_mut gt
  | BI_table_get x =>
      exists tabt t,
      tf = (Tf [::T_num T_i32] [::T_ref t]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_set x =>
      exists tabt t,
      tf = (Tf [::T_num T_i32; T_ref t] [::]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_size x =>
      exists tabt,
      tf = (Tf [::] [::T_num T_i32]) /\
        lookup_N (tc_tables C) x = Some tabt
  | BI_table_grow x =>
      exists tabt t,
      tf = (Tf [::T_ref t; T_num T_i32] [::T_num T_i32]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_fill x =>
      exists tabt t,
      tf = (Tf [::T_num T_i32; T_ref t; T_num T_i32] nil) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t
  | BI_table_copy x y =>
      exists tabt1 tabt2 t,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_tables C) x = Some tabt1 /\
        tabt1.(tt_elem_type) = t /\
        lookup_N (tc_tables C) y = Some tabt2 /\
        tabt2.(tt_elem_type) = t
  | BI_table_init x y =>
      exists tabt t,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_tables C) x = Some tabt /\
        tabt.(tt_elem_type) = t /\
        lookup_N (tc_elems C) y = Some t
  | BI_elem_drop x =>
      exists t,
      tf = (Tf nil nil) /\
        lookup_N (tc_elems C) x = Some t
  | BI_load t tp_sx marg =>
      exists mt,
      tf = (Tf [::T_num T_i32] [::T_num t]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_store_t_bounds marg.(memarg_align) (option_projl tp_sx) t
  | BI_load_vec lvarg marg =>
      exists mt,
      tf = (Tf [::T_num T_i32] [::T_vec T_v128]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_vec_bounds lvarg marg
  | BI_load_vec_lane width marg x =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_vec T_v128] [::T_vec T_v128]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_store_vec_lane_bounds width marg x
  | BI_store t tp marg =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_num t] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_store_t_bounds marg.(memarg_align) tp t
  | BI_store_vec marg =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_vec T_v128] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_vec_bounds LVA_none marg
  | BI_store_vec_lane width marg x =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_vec T_v128] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        load_store_vec_lane_bounds width marg x
  | BI_memory_size =>
      exists mt,
      tf = (Tf [::] [::T_num T_i32]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_grow =>
      exists mt,
      tf = (Tf [::T_num T_i32] [::T_num T_i32]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_fill =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_copy =>
      exists mt,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt
  | BI_memory_init x =>
      exists mt dt,
      tf = (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::]) /\
        lookup_N (tc_mems C) 0%N = Some mt /\
        lookup_N (tc_datas C) x = Some dt
  | BI_data_drop x =>
      exists dt,
      tf = (Tf nil nil) /\
        lookup_N (tc_datas C) x = Some dt
  end.

Lemma be_typing_inversion: forall C be tf,
    be_typing C [::be] tf ->
    exists tf_principal,
      tf_principal <ti: tf /\
      be_principal_typing C be tf_principal.
Proof.
  move => C be tf HType.
  gen_ind_subst HType => //; try by (eexists; split; first (by apply instr_subtyping_eq); try by repeat (eexists; eauto)).
  (* Composition *)
  - extract_listn; extract_premise.
    apply empty_typing in HType1.
    exists extr; split => //.
    destruct extr as [tx ty].
    unfold instr_subtyping in *.
    extract_premise; subst.
    apply values_subtyping_split1 in HType1; remove_bools_options.
    exists (take (size extr) t1s), extr0, (drop (size extr) t1s), extr2; repeat split => //; resolve_subtyping => //.
    by rewrite cat_take_drop.
  (* Subtyping *)
  - extract_premise.
    exists extr; split => //.
    by resolve_subtyping.
Qed.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists t3s, be_typing _ [::] (Tf ?tx _) /\ _ =>
    try exists tx; split; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

(* Note that this lemma is still true in the context of subtyping. *)
Lemma be_composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C [::e] (Tf t3s t2s).
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  - by destruct es1 => //=.
  - by exists t2s.
  - unfold instr_subtyping in H.
    extract_premise; subst.
    exists (extr0 ++ extr); split.
    + eapply bet_subtyping; eauto.
      unfold instr_subtyping.
      exists extr0, extr0, extr2, extr; by resolve_subtyping.
    + eapply bet_subtyping; eauto.
      unfold instr_subtyping.
      exists extr0, extr1, extr, extr3; by resolve_subtyping.
Qed.

Lemma be_composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists t3s, be_typing C es1 (Tf t1s t3s) /\
           be_typing C es2 (Tf t3s t2s).
Proof.
  move => C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 t1s t2s HType.
  - rewrite cats0 in HType.
    exists t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite catA in HType.
    apply be_composition_typing_single in HType as [ts3 [Hbet1 Hbet2]].
    apply IHes2 in Hbet1 as [ts3' [Hbet3 Hbet4]].
    exists ts3'.
    repeat split => //.
    by eapply bet_composition; eauto.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 t1s t2s t3s Hbet1 Hbet2.
  - apply empty_typing in Hbet2; rewrite cats0; subst.
    eapply bet_subtyping; eauto.
    unfold instr_subtyping.
    exists nil, nil, t1s, t3s.
    by resolve_subtyping.
  - apply be_composition_typing in Hbet2 as [ts3 [Hbet3 Hbet4]].
    rewrite catA. eapply bet_composition; last by eauto.
    by eapply IHes2; eauto.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

End Typing_inversion_be.

Lemma upd_label_overwrite {V R F O : Set}: forall (C : t_context_gen V R F O) l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Ltac resolve_list_eq :=
  repeat match goal with
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ [::_] = _ ++ _ ++ [::_] |- _ =>
    rewrite catA in H; apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ _ ++ [::_] = _ ++ [::_] |- _ =>
    rewrite catA in H; apply concat_cancel_last in H; destruct H; subst
  | H: _ ++ [::_; _] = (?l ++ [::?x]) ++ [::?y] |- _ =>
    rewrite -catA in H; simpl in H; apply concat_cancel_last_n in H; remove_bools_options
  | H: (?l ++ [::?x1; ?x2]) ++ [:: ?y] = _ ++ [::_; _; _] |- _ =>
    rewrite -catA in H; simpl in H; apply concat_cancel_last_n in H; remove_bools_options
  | H: [:: _; _] = [::_; _] |- _ =>
    inversion H; subst; clear H
  | H: [:: _; _; _] = [::_; _; _] |- _ =>
    inversion H; subst; clear H
   | H: Tf _ _ = Tf _ _ |- _ =>
     inversion H; subst; clear H
   | H: Closed_ft _ _ = Closed_ft _ _ |- _ =>
     inversion H; subst; clear H
  | H: T_num _ = T_num _ |- _ =>
    inversion H; subst; clear H
    end.

Ltac invert_be_typing :=
  repeat match goal with
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [::_] _ |- _ =>
    let tf_principal := fresh "tf_principal" in
    let Htisub := fresh "Htisub" in
    let Hinvgoal := fresh "Hinvgoal" in
    apply be_typing_inversion in H as [tf_principal [Htisub Hinvgoal]]; simpl in Hinvgoal; extract_premise
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts3 := fresh "ts3_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    apply be_composition_typing in H; destruct H as [ts3 [H1 H2]]
  | H: be_typing _ (cons ?x ?l) _ |- _ =>
    let cats := constr:(ltac:(cons_chain_to_cat (cons x l))) in
    replace (cons x l) with cats in H; last reflexivity
  | _ => try by simpl; try resolve_list_eq
  end.

Ltac e_typing_ind HType :=
  match type of HType with
   | e_typing _ _ _ (Closed_ft ?ts1 ?ts2) =>
      let tf := fresh "tf" in
      let Heqtf := fresh "Heqtf" in
       remember (Closed_ft ts1 ts2: closed_instr_type) as tr eqn:Heqtf;
      move: ts1 ts2 Heqtf;
      dependent induction HType; intros; subst
  end.

Section Typing_inversion_e.
             
Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.

(** Typing lemmas **)

(* A reformulation of [ety_a] that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    closed_be_typing s.(s_types) C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Closed_ft [::] t2s) ->
    e_typing s C es (Closed_ft ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  eapply ety_subtyping; eauto.
  have Weaken := closed_instr_weakening (s_types s) nil t2s ts.
  rewrite List.app_nil_r in Weaken. exact Weaken.
Qed.

Lemma et_weakening_empty_2: forall s C es ts t2s,
    e_typing s C es (Closed_ft t2s nil) ->
    e_typing s C es (Closed_ft (ts ++ t2s) ts).
Proof.
  move => s C es ts t2s HType.
  eapply ety_subtyping; eauto.
  have Weaken := closed_instr_weakening (s_types s) t2s nil ts.
  rewrite List.app_nil_r in Weaken. exact Weaken.
Qed.

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es tf,
    es_is_basic es ->
    e_typing s C es tf ->
    closed_be_typing s.(s_types) C (to_b_list es) tf.
Proof.
  move => s C es tf HBasic HType.
  dependent induction HType; basic_inversion => //.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
   + apply cbet_empty.
   + rewrite to_b_list_concat.
    apply basic_concat in HBasic.
    move/andP in HBasic.
    destruct HBasic as [Hbes Hbe].
     eapply cbet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply IHHType in HBasic.
     by eapply cbet_subtyping; eauto.
   + apply cbet_num.
   + apply cbet_vec.
Qed.

Definition e_principal_typing (s: store_record) (C: closed_t_context) (e: administrative_instruction) (tf: closed_instr_type) : Prop :=
  match e with
  | AI_basic b =>
      closed_be_typing s.(s_types) C [::b] tf
  | AI_trap =>
      True (* Equivalently, add trivial equalities *)
  | AI_ref_extern a =>
      exists t, tf = (Closed_ft nil [::CO_value (closed_reference_value t)]) /\
        closed_value_typing s (VAL_ref (VAL_ref_extern a)) (closed_reference_value t)
  | AI_ref_i31 n =>
      exists t, tf = (Closed_ft nil [::CO_value (closed_reference_value t)]) /\
        closed_value_typing s (VAL_ref (VAL_ref_i31 n)) (closed_reference_value t)
  | AI_ref_null h =>
      exists t, tf = (Closed_ft nil [::CO_value (closed_reference_value t)]) /\
        closed_value_typing s (VAL_ref (VAL_ref_null h)) (closed_reference_value t)
  | AI_ref a =>
      exists t, tf = (Closed_ft nil [::CO_value (closed_reference_value t)]) /\
        closed_value_typing s (VAL_ref (VAL_ref_func a)) (closed_reference_value t)
  | AI_invoke a =>
      exists tf0, tf = lift_closed_function_type tf0 /\
        closed_function_view s a tf0
  | AI_return_invoke a =>
      exists ts1 ts2 ts3 ts4, tf = (Closed_ft (ts3 ++ lift_closed_result_type ts1) ts4) /\
       closed_function_view s a (Closed_ft ts1 ts2) /\
      tc_return C = Some (lift_closed_result_type ts2)
  | AI_label n es0 es =>
      exists ts1 ts2,
      tf = (Closed_ft nil ts2) /\
        e_typing s C es0 (Closed_ft ts1 ts2) /\
        e_typing s (upd_label C ([::ts1] ++ tc_labels C)) es (Closed_ft nil ts2) /\
        length ts1 = n
  | AI_frame n f es =>
      exists ts actual_ts,
       tf = (Closed_ft nil ts) /\
        thread_typing s (Some actual_ts) (f, es) actual_ts /\
        canonical_registry_validb s.(s_types) /\
        closed_stack_results_subtyping s.(s_types) actual_ts ts /\
        length ts = n
  end.
  
Lemma closable_source_subtyping_equal names actual expected closed :
  close_result_type names actual = Some closed ->
  values_subtyping actual expected ->
  actual = expected.
Proof.
  unfold close_result_type. rewrite <-those_those0.
  move: expected closed.
  induction actual as [|a actual IH]; destruct expected as [|b expected];
    move => closed Closed Subtype; try discriminate; first reflexivity.
  cbn [List.map those0] in Closed.
  destruct (gc_type_context.close_value_type names 0 a) as [ca|] eqn:Head;
    last discriminate.
  destruct (those0 (List.map (gc_type_context.close_value_type names 0) actual))
    as [tail|] eqn:Tail; last discriminate.
  move/andP: Subtype => [AB Rest].
  have Same : a = b.
  { unfold value_subtyping in AB.
    move/orP: AB => [/eqP Same|/eqP Same]; first exact Same.
    subst a. discriminate. }
  subst b. f_equal. exact (IH _ _ (Logic.eq_refl _) Rest).
Qed.

Lemma closed_instr_preserves_empty registry inputs outputs inputs' outputs' :
  closed_stack_results_subtyping registry inputs outputs ->
  closed_instr_subtyping registry (Closed_ft inputs outputs) (Closed_ft inputs' outputs') ->
  closed_stack_results_subtyping registry inputs' outputs'.
Proof.
  move => Original [p [p' [isub [osub [-> [-> [Prefix [Inputs Outputs]]]]]]]].
  apply closed_stack_results_append; first exact Prefix.
  eapply closed_stack_results_trans; first exact Inputs.
  eapply closed_stack_results_trans; eauto.
Qed.

Lemma empty_closed_be_typing registry C inputs outputs :
  closed_be_typing registry C nil (Closed_ft inputs outputs) ->
  closed_stack_results_subtyping registry inputs outputs.
Proof.
  move => Typed. remember nil as bes eqn:Empty.
  remember (Closed_ft inputs outputs) as signature eqn:Signature.
  move: inputs outputs Signature Empty.
  induction Typed; move => ins outs Signature Empty; inversion Signature; subst;
    try discriminate; try apply closed_stack_results_refl.
  - apply List.app_eq_nil in Empty as [Left Right].
    eapply closed_stack_results_trans.
    + exact (IHTyped1 _ _ (Logic.eq_refl _) Left).
    + exact (IHTyped2 _ _ (Logic.eq_refl _) Right).
  - eapply closed_instr_preserves_empty; last exact H.
    exact (IHTyped _ _ (Logic.eq_refl _) (Logic.eq_refl _)).
Qed.

Lemma empty_e_typing: forall s C t1s t2s,
    e_typing s C [::] (Closed_ft t1s t2s) ->
    closed_stack_results_subtyping s.(s_types) t1s t2s.
Proof.
  move => s C t1s t2s HType.
  apply et_to_bet in HType => //.
  by apply empty_closed_be_typing in HType.
Qed.

Lemma et_empty: forall s C ts1 ts2,
    closed_stack_results_subtyping s.(s_types) ts1 ts2 ->
    e_typing s C nil (Closed_ft ts1 ts2).
Proof.
  move => s C ts1 ts2 Hsub.
  eapply ety_subtyping; first apply ety_empty.
  unfold closed_instr_subtyping.
  exists ts1, ts2, nil, nil.
  rewrite !cats0.
  repeat split => //; constructor.
Qed.

Lemma e_typing_inversion: forall s C e tf,
    e_typing s C [::e] tf ->
    exists tf_principal,
      closed_instr_subtyping s.(s_types) tf_principal tf /\
      e_principal_typing s C e tf_principal.
Proof.
  move => s C e tf HType.
  dependent induction HType; try by (eexists; split; first (by apply closed_instr_refl); try by repeat (eexists; eauto)).
  (* bet *)
  - do 2 (try destruct bes => //).
    destruct e => //.
    simpl in x; inversion x; subst; clear x.
    exists tf. split; first apply closed_instr_refl. exact H.
  (* Composition *)
  - apply List.app_eq_unit in x as [[Left Right]|[Left Right]]; subst.
    + destruct (IHHType2 Right) as [principal [Subtype Principal]].
      exists principal. split; last exact Principal.
      eapply closed_instr_trans; first exact Subtype.
      exists nil, nil, t1s, t3s.
      repeat split => //; try apply closed_stack_results_refl.
      by apply empty_e_typing in HType1.
    + discriminate.
  (* Subtyping *)
  - extract_premise.
    exists extr; split => //.
    by eapply closed_instr_trans; eauto.
  - eexists. split; first apply closed_instr_refl.
    apply cbet_num.
  - eexists. split; first apply closed_instr_refl.
    apply cbet_vec.
Qed.
  
(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_et:=
  repeat lazymatch goal with
  | H: _ |- exists t3s, e_typing _ _ [::] (Closed_ft ?tx _) /\ _ =>
    try exists tx; split; try eauto
  | H: _ |- e_typing _ _ [::] (Closed_ft ?es ?es) =>
    apply et_empty; apply closed_stack_results_refl
  end.

Lemma cbet_identity registry C operands :
  closed_be_typing registry C nil (Closed_ft operands operands).
Proof.
  eapply cbet_subtyping; first apply cbet_empty.
  exists operands, operands, nil, nil.
  rewrite !cats0. repeat split => //; apply closed_stack_results_refl.
Qed.

Lemma cbet_composition_typing_single registry C left instruction inputs outputs :
  closed_be_typing registry C (left ++ [::instruction]) (Closed_ft inputs outputs) ->
  exists middle,
    closed_be_typing registry C left (Closed_ft inputs middle) /\
    closed_be_typing registry C [::instruction] (Closed_ft middle outputs).
Proof.
  move => Typed. gen_ind_subst Typed; extract_listn;
    try solve [
      match goal with
      | |- exists middle, closed_be_typing _ _ nil (Closed_ft ?ins _) /\ _ =>
        exists ins; split; [apply cbet_identity|econstructor; eauto]
      end].
  - exists inputs. split; first apply cbet_identity.
    rewrite <-EClosed_ft. eapply close_be_typing; eauto.
  - by destruct left.
  - eexists; split; eassumption.
  - extract_premise.
    destruct (IHTyped _ _ (Logic.eq_refl _)) as [middle [Left Right]].
    destruct (closed_instr_split registry inputs outputs inputs0 outputs0 middle H)
      as [middle' [First Last]].
    exists middle'. split; eapply cbet_subtyping; eauto.
Qed.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Closed_ft t1s t2s) ->
    exists t3s, e_typing s C es1 (Closed_ft t1s t3s) /\
           e_typing s C [::e] (Closed_ft t3s t2s).
Proof.
  move => s C es1 es2 t1s t2s HType.
  e_typing_ind HType; extract_listn; resolve_list_eq; auto_prove_et => //; try by econstructor; eauto.
  - (* basic *)
    apply b_e_elim in x. destruct x. subst.
    rewrite to_b_list_concat in H.
    apply cbet_composition_typing_single in H as [middle [Left Right]].
    apply basic_concat in H1. move/andP in H1. destruct H1.
    exists middle.
    by repeat split => //=; apply ety_a' => //=.
  - by destruct es1.
  - (* subtyping *)
    extract_premise.
    destruct (IHHType _ _ (Logic.eq_refl _)) as [middle [Left Right]].
    destruct (closed_instr_split (s_types s) t1s t2s t1s0 t2s0 middle H)
      as [middle' [First Last]].
    exists middle'. split; eapply ety_subtyping; eauto.
  - rewrite <-Heqtf. by apply ety_invoke.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Closed_ft t1s t2s) ->
    exists t3s, e_typing s C es1 (Closed_ft t1s t3s) /\
           e_typing s C es2 (Closed_ft t3s t2s).
Proof.
  move => s C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 ts1 ts2 HType.
  - rewrite cats0 in HType.
    exists ts2.
    repeat split => //=.
    apply et_empty. apply closed_stack_results_refl.
  - rewrite catA in HType.
    apply e_composition_typing_single in HType as [ts3 [Het1 Het2]].
    apply IHes2 in Het1 as [ts3' [Het3 Het4]].
    exists ts3'.
    repeat split => //.
    by eapply ety_composition; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Closed_ft t1s t2s) ->
    e_typing s C es2 (Closed_ft t2s t3s) ->
    e_typing s C (es1 ++ es2) (Closed_ft t1s t3s).
Proof.
  move => s C es1 es2.
  move: es1.
  induction es2 using List.rev_ind; move => es1 ts1 ts2 ts3 Het1 Het2.
  - apply empty_e_typing in Het2.
    rewrite cats0.
    eapply ety_subtyping; eauto.
    unfold closed_instr_subtyping.
    exists nil, nil, ts1, ts3.
    repeat split => //; apply closed_stack_results_refl.
  - apply e_composition_typing in Het2 as [ts3' [Het3 Het4]].
    rewrite catA. eapply ety_composition => //=.
    eapply IHes2; eauto.
    by eauto.
Qed.

Definition literal_closed_signature instruction : option closed_instr_type :=
  match instruction with
  | BI_const_num n => Some (Closed_ft nil [::CO_value (CV_num (typeof_num n))])
  | BI_const_vec _ => Some (Closed_ft nil [::CO_value (CV_vec T_v128)])
  | _ => None
  end.

Lemma source_literal_inversion registry source instruction signature principal :
  literal_closed_signature instruction = Some principal ->
  be_typing source [::instruction] signature ->
  closed_instr_subtyping registry principal
    (interpret_instr_type source.(tc_defined_types) signature).
Proof.
  move => Literal Typed.
  apply be_typing_inversion in Typed as [original [Subtype Principal]].
  destruct instruction; simpl in Literal; try discriminate;
    injection Literal as <-; simpl in Principal; subst original.
  - exact (interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype).
  - destruct v.
    exact (interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype).
Qed.

Lemma cbet_literal_inversion registry C instruction signature principal :
  closed_be_typing registry C [::instruction] signature ->
  literal_closed_signature instruction = Some principal ->
  closed_instr_subtyping registry principal signature.
Proof.
  move => Typed Literal. gen_ind_subst Typed;
    try discriminate.
  - eapply source_literal_inversion; eauto.
  - injection Literal as <-. apply closed_instr_refl.
  - injection Literal as <-. apply closed_instr_refl.
  - extract_listn; extract_premise.
    eapply closed_instr_trans; first (eapply IHTyped2; eauto).
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - eapply closed_instr_trans; last exact H.
    eapply IHTyped; eauto.
Qed.

Lemma Value_typing_inversion: forall s C v ts1 ts2,
    e_typing s C [::v_to_e v] (Closed_ft ts1 ts2) ->
    exists t, closed_instr_subtyping s.(s_types)
      (Closed_ft nil [::CO_value t]) (Closed_ft ts1 ts2) /\
           closed_value_typing s v t.
Proof.
  move => s C v ts1 ts2 HType.
  destruct v as [number|vector|ref].
  - apply e_typing_inversion in HType as [principal [Subtype Principal]].
    exists (CV_num (typeof_num number)). split.
    + eapply closed_instr_trans; last exact Subtype.
      eapply cbet_literal_inversion; first exact Principal.
      reflexivity.
    + destruct number; reflexivity.
  - apply e_typing_inversion in HType as [principal [Subtype Principal]].
    exists (CV_vec T_v128). split.
    + eapply closed_instr_trans; last exact Subtype.
      eapply cbet_literal_inversion; first exact Principal.
      reflexivity.
    + destruct vector; reflexivity.
  - destruct ref;
      apply e_typing_inversion in HType as [principal [Subtype Principal]];
      simpl in Principal;
      destruct Principal as [t [-> Value]];
      exists (closed_reference_value t); split; assumption.
Qed.

Lemma Values_typing_inversion: forall s C vs ts1 ts2,
    e_typing s C (v_to_e_list vs) (Closed_ft ts1 ts2) ->
    exists ts, closed_instr_subtyping s.(s_types)
      (Closed_ft nil (lift_closed_result_type ts)) (Closed_ft ts1 ts2) /\
           closed_values_typing s vs ts.
Proof.
  move => s C vs. induction vs using List.rev_ind; move => inputs outputs Typed.
  - apply empty_e_typing in Typed.
    exists nil. split; last reflexivity.
    apply closed_instr_empty_input_intro. by rewrite List.app_nil_r.
  - rewrite -v_to_e_cat in Typed.
    apply e_composition_typing_single in Typed as [middle [Left Right]].
    destruct (IHvs _ _ Left) as [types [Prefix Values]].
    destruct (Value_typing_inversion Right) as [t [Last Value]].
    exists (types ++ [::t]). split.
    + apply closed_instr_empty_input_intro.
      apply closed_instr_empty_input_elim in Prefix, Last.
      unfold lift_closed_result_type. rewrite List.map_app.
      rewrite List.app_assoc.
      eapply closed_stack_results_trans; last exact Last.
      apply closed_stack_results_append; first exact Prefix.
      apply closed_stack_results_refl.
    + apply closed_values_append; first exact Values.
      simpl. by rewrite Value.
Qed.

(* In Wasm 2.0, values are no longer always well-typed, and typing needs to be done under e_typing. *)
Lemma et_value_typing: forall s C v t,
    closed_value_typing s v t ->
    e_typing s C [::v_to_e v] (Closed_ft nil [::CO_value t]).
Proof.
  exact closed_value_instruction.
Qed.

Lemma et_values_typing: forall s C vs ts,
    closed_values_typing s vs ts ->
    e_typing s C (v_to_e_list vs) (Closed_ft nil (lift_closed_result_type ts)).
Proof.
  exact closed_values_instruction.
Qed.

Lemma closed_values_source_typing s names fields source closed :
  those0 (map (gc_type_context.close_value_type names 0) source) = Some closed ->
  all2 (closed_value_typing s) fields closed ->
  values_typing s names fields source.
Proof.
  move: fields closed.
  induction source as [|t ts IH]; move => fields closed Closed Typed.
  - simpl in Closed. injection Closed as <-.
    by destruct fields.
  - simpl in Closed.
    destruct (gc_type_context.close_value_type names 0 t) as [ct|] eqn:Head;
      last discriminate.
    destruct (those0 (map (gc_type_context.close_value_type names 0) ts))
      as [cts|] eqn:Tail; last discriminate.
    injection Closed as <-.
    destruct fields as [|value fields]; first discriminate.
    move/andP: Typed => [Value Values].
    apply/andP; split.
    + by unfold value_typing; rewrite Head.
    + exact (IH _ _ (Logic.eq_refl _) Values).
Qed.

Theorem closed_values_emission s C names fields source closed :
  C.(tc_defined_types) = names ->
  gc_type_context.close_function_type names 0 (Tf source nil) =
    Some (Closed_ft closed nil) ->
  all2 (closed_value_typing s) fields closed ->
  e_typing s C (v_to_e_list fields) (Closed_ft nil (lift_closed_result_type closed)).
Proof.
  move => Names Closed Typed.
  change ((match those0 (map (gc_type_context.close_value_type names 0) source) with
    | Some types => Some (Closed_ft types nil)
    | None => None end) = Some (Closed_ft closed nil)) in Closed.
  destruct (those0 (map (gc_type_context.close_value_type names 0) source))
    as [types|] eqn:Types; last discriminate.
  injection Closed as <-.
  apply et_values_typing. exact Typed.
Qed.

Theorem instance_closed_values_emission s inst C fields source closed :
  inst_typing s inst = Some C ->
  gc_type_context.close_function_type inst.(inst_defined_types) 0 (Tf source nil) =
    Some (Closed_ft closed nil) ->
  all2 (closed_value_typing s) fields closed ->
  exists closedC, close_t_context C = Some closedC /\
    e_typing s closedC (v_to_e_list fields)
      (Closed_ft nil (lift_closed_result_type closed)).
Proof.
  move => Instance Closed Typed.
  destruct (inst_typing_context_closes s inst C Instance) as [closedC Context].
  exists closedC. split; first exact Context.
  by apply et_values_typing.
Qed.

(* Helpers for more efficiently dealing with these due to subtyping *)
Lemma et_value_typing': forall s C v t tf,
    closed_value_typing s v t ->
    closed_instr_subtyping s.(s_types) (Closed_ft nil [::CO_value t]) tf ->
    e_typing s C [::v_to_e v] tf.
Proof.
  move => s C v t [tx ty] Hvaltype Hsub.
  eapply ety_subtyping; eauto; by apply et_value_typing; eauto.
Qed.

Lemma et_values_typing': forall s C vs ts tf,
    closed_values_typing s vs ts ->
    closed_instr_subtyping s.(s_types) (Closed_ft nil (lift_closed_result_type ts)) tf ->
    e_typing s C (v_to_e_list vs) tf.
Proof.
  move => s C v t [tx ty] Hvaltype Hsub.
  eapply ety_subtyping; eauto; by apply et_values_typing; eauto.
Qed.

Lemma et_thread_typing: forall s f es rs ts,
    thread_typing s rs (f, es) ts ->
    exists C,
      closed_frame_typing s f C /\
      e_typing s (upd_return C rs) es (Closed_ft nil ts).
Proof.
  intros ????? Htype.
  inversion Htype; subst; clear Htype.
  by exists C.
Qed.
  
End Typing_inversion_e.

Ltac invert_e_typing :=
  repeat match goal with
  | H: thread_typing _ _ _ _ |- _ =>
    let C := fresh "C" in
    let H1 := fresh "Hframetype" in
    let H2 := fresh "Hetype" in
    apply et_thread_typing in H as [C [H1 H2]]; subst;
    try repeat rewrite -catA in H1;
    try repeat rewrite -catA in H2
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts3 := fresh "ts3_comp" in
    let H1 := fresh "H1_comp" in
    let H2 := fresh "H2_comp" in
    apply e_composition_typing in H as [ts3 [H1 H2]]; subst;
    try repeat rewrite -catA in H1;
    try repeat rewrite -catA in H2
  | H: e_typing _ _ [:: AI_basic _] _ |- _ =>
    apply et_to_bet in H => //; simpl in H; invert_be_typing; subst
  | H: e_typing _ _ [::$V _] _ |- _ =>
    let ts := fresh "ts_value" in
    let H1 := fresh "H1_value" in
    let H2 := fresh "H2_value" in
    eapply Value_typing_inversion in H => //; eauto => //;
    destruct H as [ts [H1 H2]]; subst
  | H: e_typing _ _ (v_to_e_list _) _ |- _ =>
    let ts := fresh "ts_values" in
    let H1 := fresh "H1_values" in
    let H2 := fresh "H2_values" in
    apply Values_typing_inversion in H as [ts [H1 H2]]; subst
  | H : e_typing _ _ [:: _] _ |- _ =>
    let tf_principal := fresh "tf_principal" in
    let Htisub := fresh "Htisub" in
    let Hinvgoal := fresh "Hinvgoal" in
    apply e_typing_inversion in H as [tf_principal [Htisub Hinvgoal]]; simpl in Hinvgoal; extract_premise
  | H: e_typing _ _ nil _ |- _ =>
    apply empty_e_typing in H
  | H: e_typing _ _ (cons ?x _) _ |- _ =>
    rewrite -(cat1s x) in H
  end; invert_be_typing; resolve_list_eq.

(* Some more complicated lemmas *)
Section Typing_inversion_e.

Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.
  
(* inst_typing inversion *)
Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i = Some C ->
    tc_locals C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i = Some C ->
    tc_labels C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma inst_t_context_return_None: forall s i C,
    inst_typing s i = Some C ->
    tc_return C = None.
Proof.
  move => s i C HInstType.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct i => //=.
  by remove_bools_options.
Qed.

Lemma frame_typing_label_empty: forall s f C,
    frame_typing s f C ->
    tc_labels C = nil.
Proof.
  move => s f C Hftype.
  unfold frame_typing in Hftype; remove_bools_options.
  destruct Hftype as [ts [-> Hvt]] => /=.
  by eapply inst_t_context_label_empty; eauto.
Qed.

Lemma frame_typing_return_None: forall s f C,
    frame_typing s f C ->
    tc_return C = None.
Proof.
  move => s f C Hftype.
  unfold frame_typing in Hftype; remove_bools_options.
  destruct Hftype as [ts [-> Hvt]] => /=.
  by eapply inst_t_context_return_None; eauto.
Qed.

Lemma frame_typing_defined_types s f C :
  frame_typing s f C ->
  tc_defined_types C = inst_defined_types (f_inst f).
Proof.
  unfold frame_typing.
  destruct (inst_typing s (f_inst f)) as [base|] eqn:Instance; last contradiction.
  move => [locals [-> _]]; simpl.
  exact (inst_typing_defined_types Instance).
Qed.

Lemma closed_frame_typing_label_empty s f C :
  closed_frame_typing s f C -> tc_labels C = nil.
Proof.
  move => [source [base [locals [Instance [Context [-> Values]]]]]].
  simpl. rewrite (closing_context_label_values _ _ Context).
  by rewrite (inst_t_context_label_empty Instance).
Qed.

Lemma closed_frame_typing_return_None s f C :
  closed_frame_typing s f C -> tc_return C = None.
Proof.
  move => [source [base [locals [Instance [Context [-> Values]]]]]].
  simpl. rewrite (closing_context_return_values _ _ Context).
  by rewrite (inst_t_context_return_None Instance).
Qed.

Lemma closed_frame_locals_length s f C :
  closed_frame_typing s f C ->
  length C.(tc_locals) = length f.(f_locs).
Proof.
  move => [source [base [locals [Instance [Context [-> Values]]]]]].
  have Closed := close_context_locals source base Context.
  rewrite (inst_t_context_local_empty Instance) in Closed.
  simpl in Closed. injection Closed as <-.
  simpl. rewrite cats0.
  symmetry. exact (closed_values_length s (f_locs f) locals Values).
Qed.

Lemma global_type_reference: forall s i j C v t,
    store_typing s ->
    inst_typing s i = Some C ->
    sglob_val s i j = Some v ->
    option_map tg_t (lookup_N (tc_globals C) j) = Some t ->
    source_value_typing s i v t.
Proof.
  move => s i j C v t Hst HInstType Hvref Htref.
  destruct (lookup_N (tc_globals C) j) as [source|] eqn:Source; last discriminate.
  injection Htref as <-.
  destruct (inst_typing_global_lookup_inv HInstType Source) as [address [View Address]].
  unfold sglob_val, sglob, sglob_ind in Hvref.
  rewrite Address in Hvref; simpl in Hvref.
  destruct (lookup_N (s_globals s) address) as [global|] eqn:Global; last discriminate.
  simpl in Hvref. injection Hvref as <-.
  destruct (store_typing_global_lookup Hst Global) as [actual Typed].
  have Valid : canonical_registry_valid s.(s_types).
  { apply canonical_registry_validb_sound. exact (proj1 Hst). }
  unfold instance_global_view, ext_global_typing in View.
  rewrite Global in View.
  destruct (close_global_type (inst_defined_types i) source) as [expected|] eqn:Closed;
    last discriminate.
  unfold globalinst_typing in Typed.
  destruct global as [descriptor value]; simpl in *.
  remove_bools_options.
  unfold source_value_typing, value_typing.
  unfold close_global_type in Closed.
  destruct (gc_type_context.close_value_type (inst_defined_types i) 0 (tg_t source))
    as [closed|] eqn:Expected; last discriminate.
  injection Closed as <-; simpl in *.
  eapply closed_value_typing_subsumption; eauto.
Qed.

Lemma func_context_store: forall s i C j x,
    inst_typing s i = Some C ->
    lookup_N (tc_funcs C) j = Some x ->
    exists a, lookup_N i.(inst_funcs) j = Some a.
Proof.
  move => s i C j x HIT HN.
  destruct (inst_typing_func_lookup_inv HIT HN) as [a [_ Address]].
  by exists a.
Qed.

Lemma glob_context_store: forall s i C j g,
    inst_typing s i = Some C ->
    lookup_N (tc_globals C) j = Some g ->
    sglob s i j <> None.
Proof.
  move => s i C j g HIT HN.
  destruct (inst_typing_global_lookup_inv HIT HN) as [a [View Address]].
  unfold instance_global_view, ext_global_typing in View.
  unfold sglob, sglob_ind.
  rewrite Address; simpl.
  destruct (lookup_N (s_globals s) a); last discriminate.
  discriminate.
Qed.

Lemma mem_context_store: forall s i C,
    inst_typing s i = Some C ->
    tc_mems C <> [::] ->
    exists (n: memaddr), smem_ind s i = Some n /\
              lookup_N (s_mems s) n <> None.
Proof.
  move => s i C HIT HMemory.
  destruct (tc_mems C) as [|t rest] eqn:Memories; first contradiction.
  have Head : lookup_N (tc_mems C) 0 = Some t by rewrite Memories.
  destruct (inst_typing_mem_lookup_inv HIT Head) as [a [Typed Address]].
  exists a. split.
  - unfold smem_ind. exact Address.
  - unfold ext_mem_typing in Typed.
    destruct (lookup_N (s_mems s) a); discriminate.
Qed.

Lemma cbet_branch_inversion registry C index signature :
  closed_be_typing registry C [::BI_br index] signature ->
  exists before after types,
    closed_instr_subtyping registry (Closed_ft (before ++ types) after) signature /\
    lookup_N C.(tc_labels) index = Some types.
Proof.
  move => Typed. gen_ind_subst Typed => //.
  - apply be_typing_inversion in H as [raw [Subtype Principal]].
    simpl in Principal. destruct Principal as [before [after [types [-> Lookup]]]].
    exists (interpret_operand_results (tc_defined_types source) before),
      (interpret_operand_results (tc_defined_types source) after),
      (interpret_operand_results (tc_defined_types source) types).
    split.
    + have Translated := interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype.
      unfold interpret_instr_type, interpret_operand_results in Translated.
      rewrite List.map_app in Translated. exact Translated.
    + exact (closing_context_label_lookup _ _ _ _ H1 Lookup).
  - extract_listn; extract_premise.
    exists extr, extr0, extr1. split; last exact Hconjr.
    eapply closed_instr_trans; first exact Hconjl.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise.
    exists extr, extr0, extr1. split; last exact Hconjr.
    by eapply closed_instr_trans; eauto.
Qed.

Lemma cbet_nop_inversion registry C signature :
  closed_be_typing registry C [::BI_nop] signature ->
  closed_instr_subtyping registry (Closed_ft nil nil) signature.
Proof.
  move => Typed. gen_ind_subst Typed => //.
  - inversion Econs; subst instruction.
    apply be_typing_inversion in H as [raw [Subtype Principal]].
    simpl in Principal. subst raw.
    exact (interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype).
  - apply closed_instr_refl.
  - extract_listn; extract_premise.
    eapply closed_instr_trans; first eassumption.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise. by eapply closed_instr_trans; eauto.
Qed.

Lemma cbet_drop_inversion registry C signature :
  closed_be_typing registry C [::BI_drop] signature ->
  exists operand, closed_instr_subtyping registry (Closed_ft [::operand] nil) signature.
Proof.
  move => Typed. gen_ind_subst Typed => //.
  - inversion Econs; subst instruction.
    apply be_typing_inversion in H as [raw [Subtype Principal]].
    destruct Principal as [operand ->].
    exists (interpret_operand_type (tc_defined_types source) operand).
    exact (interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype).
  - eexists. apply closed_instr_refl.
  - extract_listn; extract_premise.
    exists extr. eapply closed_instr_trans; first eassumption.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise.
    exists extr. by eapply closed_instr_trans; eauto.
Qed.

Lemma cbet_select_inversion registry C annotation signature :
  closed_be_typing registry C [::BI_select annotation] signature ->
  exists operand, closed_instr_subtyping registry
    (Closed_ft [::operand; operand; CO_value (CV_num T_i32)] [::operand]) signature.
Proof.
  move => Typed. gen_ind_subst Typed => //.
  - apply be_typing_inversion in H as [raw [Subtype Principal]].
    destruct Principal as [operand [-> Annotation]].
    exists (interpret_operand_type (tc_defined_types source) operand).
    exact (interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype).
  - eexists. apply closed_instr_refl.
  - extract_listn; extract_premise.
    exists extr. eapply closed_instr_trans; first eassumption.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise.
    exists extr. by eapply closed_instr_trans; eauto.
Qed.

Definition source_only_instruction instruction : bool :=
  match instruction with
  | BI_const_num _ | BI_const_vec _ | BI_unreachable | BI_nop | BI_drop
  | BI_select _ | BI_block _ _ | BI_loop _ _ | BI_if _ _ _ => false
  | _ => true
  end.

Definition nested_control_instruction instruction : bool :=
  match instruction with
  | BI_block _ _ | BI_loop _ _ | BI_if _ _ _ => true
  | _ => false
  end.

Definition closed_control_principal registry C instruction signature : Prop :=
  match instruction with
  | BI_block tb body =>
      exists inputs outputs,
        signature = interpret_instr_type C.(tc_defined_types) (Tf inputs outputs) /\
        expand_t C tb = Some (Tf inputs outputs) /\
        closed_be_typing registry
          (upd_label C (interpret_operand_results C.(tc_defined_types) outputs :: C.(tc_labels)))
          body (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs))
  | BI_loop tb body =>
      exists inputs outputs,
        signature = interpret_instr_type C.(tc_defined_types) (Tf inputs outputs) /\
        expand_t C tb = Some (Tf inputs outputs) /\
        closed_be_typing registry
          (upd_label C (interpret_operand_results C.(tc_defined_types) inputs :: C.(tc_labels)))
          body (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs))
  | BI_if tb yes no =>
      exists inputs outputs,
        signature = interpret_instr_type C.(tc_defined_types)
          (Tf (inputs ++ [::T_num T_i32]) outputs) /\
        expand_t C tb = Some (Tf inputs outputs) /\
        closed_be_typing registry
          (upd_label C (interpret_operand_results C.(tc_defined_types) outputs :: C.(tc_labels)))
          yes (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs)) /\
        closed_be_typing registry
          (upd_label C (interpret_operand_results C.(tc_defined_types) outputs :: C.(tc_labels)))
          no (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs))
  | _ => False
  end.

Lemma cbet_control_inversion registry C instruction signature :
  closed_be_typing registry C [::instruction] signature ->
  nested_control_instruction instruction = true ->
  exists principal,
    closed_instr_subtyping registry principal signature /\
    closed_control_principal registry C instruction principal.
Proof.
  move => Typed Control. gen_ind_subst Typed; try discriminate.
  - destruct instruction0; simpl in Control, H0; try discriminate; contradiction.
  - eexists. split; first apply closed_instr_refl.
    exists inputs, outputs. repeat split; eauto.
  - eexists. split; first apply closed_instr_refl.
    exists inputs, outputs. repeat split; eauto.
  - eexists. split; first apply closed_instr_refl.
    exists inputs, outputs. repeat split; eauto.
  - extract_listn; extract_premise.
    destruct (IHTyped2 _ Control (Logic.eq_refl _) _ (Logic.eq_refl _))
      as [principal [Subtype Principal]].
    exists principal. split; last exact Principal.
    eapply closed_instr_trans; first exact Subtype.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise.
    destruct (IHTyped _ Control (Logic.eq_refl _) _ (Logic.eq_refl _))
      as [principal [Subtype Principal]].
    exists principal. split; last exact Principal.
    by eapply closed_instr_trans; eauto.
Qed.

Lemma cbet_source_inversion registry C instruction signature :
  closed_be_typing registry C [::instruction] signature ->
  source_only_instruction instruction = true ->
  exists source principal,
    close_t_context source = Some C /\
    be_principal_typing source instruction principal /\
    closed_instr_subtyping registry
      (interpret_instr_type source.(tc_defined_types) principal) signature.
Proof.
  move => Typed Only. gen_ind_subst Typed; try discriminate.
  - apply be_typing_inversion in H as [principal [Subtype Principal]].
    exists source, principal. repeat split => //.
    exact (interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype).
  - extract_listn; extract_premise.
    destruct (IHTyped2 _ Only (Logic.eq_refl _) _ (Logic.eq_refl _))
      as [source [principal [Context [Principal Subtype]]]].
    exists source, principal. repeat split => //.
    eapply closed_instr_trans; first exact Subtype.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise.
    destruct (IHTyped _ Only (Logic.eq_refl _) _ (Logic.eq_refl _))
      as [source [principal [Context [Principal Subtype]]]].
    exists source, principal. repeat split => //.
    by eapply closed_instr_trans; eauto.
Qed.

Lemma Lfilled_break_typing: forall n m k (lh: lholed n) vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_labels C)) LI (Closed_ft [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfill lh (vs ++ [::AI_basic (BI_br m)]) = LI ->
    length tss = k ->
    N.of_nat (n + k) = m ->
    e_typing s C vs (Closed_ft [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF <- HSum.
  subst m.
  apply const_es_exists in HConst as [xs ->].
  generalize dependent ts.
  move: ts2.
  generalize dependent LI.
  move: lh tss.
  elim.
  - move => vs es tss LI /= <- ts2 ts HType HTSSLength.
    rewrite add0n in HType.
    repeat rewrite catA in HType.
    invert_e_typing.
    apply cbet_branch_inversion in H2_comp1 as [before [after [types [Subtype Lookup]]]].
    unfold lookup_N in Lookup; simpl in Lookup.
    rewrite Nat2N.id list_nth_prefix in Lookup; injection Lookup as <-.
    destruct (closed_instr_required_inputs _ _ _ _ _ Subtype) as [prefix Required].
    apply closed_instr_empty_input_elim in H1_values0, H1_values.
    have Whole : closed_stack_results_subtyping (s_types s)
      (lift_closed_result_type ts_values0 ++ lift_closed_result_type ts_values)
      ts3_comp1.
    { eapply closed_stack_results_trans; last exact H1_values.
      apply closed_stack_results_append; first exact H1_values0.
      apply closed_stack_results_refl. }
    have Tail : closed_stack_results_subtyping (s_types s)
      (lift_closed_result_type ts_values) ts.
    { eapply closed_stack_suffix with
        (a := lift_closed_result_type ts_values0) (c := prefix ++ before).
      - rewrite <-List.app_assoc.
        eapply closed_stack_results_trans; eauto.
      - unfold lift_closed_result_type. rewrite List.length_map.
        have ValuesLength := closed_values_length s xs ts_values H2_values.
        rewrite v_to_e_length in HTSSLength. by lias. }
    eapply ety_subtyping; first exact (et_values_typing C H2_values).
    by apply closed_instr_empty_input_intro.
  - move => k0 vs m es lh' IH es' tss LI /= <- ts2 ts HType HTSSLength.
    rewrite - (cat1s _ es') in HType.
    invert_e_typing.
    rewrite upd_label_overwrite -cat1s catA in Hconjl1.
    remember ([::extr] ++ tss) as tss'.
    eapply IH.
    + reflexivity.
    + subst tss'. uapply Hconjl1; repeat f_equal; by lias.
    + done.
Qed.
  
Lemma cbet_return_inversion registry C signature :
  closed_be_typing registry C [::BI_return] signature ->
  exists before after types,
    closed_instr_subtyping registry (Closed_ft (before ++ types) after) signature /\
    C.(tc_return) = Some types.
Proof.
  move => Typed. gen_ind_subst Typed => //.
  - inversion Econs; subst instruction.
    apply be_typing_inversion in H as [raw [Subtype Principal]].
    simpl in Principal. destruct Principal as [before [after [types [-> Return]]]].
    exists (interpret_operand_results (tc_defined_types source) before),
      (interpret_operand_results (tc_defined_types source) after),
      (interpret_operand_results (tc_defined_types source) types).
    split.
    + have Translated := interpret_instr_subtyping registry (tc_defined_types source) _ _ Subtype.
      unfold interpret_instr_type, interpret_operand_results in Translated.
      rewrite List.map_app in Translated. exact Translated.
    + rewrite (closing_context_return_values _ _ H1) Return. reflexivity.
  - extract_listn; extract_premise.
    exists extr, extr0, extr1. split; last exact Hconjr.
    eapply closed_instr_trans; first exact Hconjl.
    exists nil, nil, inputs, outputs.
    repeat split => //; try apply closed_stack_results_refl.
    by eapply empty_closed_be_typing; eauto.
  - extract_premise.
    exists extr, extr0, extr1. split; last exact Hconjr.
    by eapply closed_instr_trans; eauto.
Qed.

Lemma Lfilled_return_typing {k}: forall (lh: lholed k) vs LI ts s C0 C t2s,
    e_typing s C0 LI (Closed_ft [::] t2s) ->
    tc_return C = tc_return C0 ->
    const_list vs ->
    length ts = length vs ->
    lfill lh (vs ++ [::AI_basic BI_return]) = LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Closed_ft [::] ts).
Proof.
  induction lh; move => vs LI ts s C0 C t2s HType Heqret HConst HLength /=HLF HReturn; subst => //=; invert_e_typing.
  - apply const_es_exists in HConst as [vs0 ->].
    invert_e_typing.
    apply cbet_return_inversion in H1_comp1 as [before [after [types [Subtype Return]]]].
    rewrite Return in Heqret. rewrite -HReturn in Heqret.
    injection Heqret as <-.
    destruct (closed_instr_required_inputs _ _ _ _ _ Subtype) as [prefix Required].
    apply closed_instr_empty_input_elim in H1_values, H1_values0.
    have Whole : closed_stack_results_subtyping (s_types s)
      (lift_closed_result_type ts_values ++ lift_closed_result_type ts_values0)
      ts3_comp0.
    { eapply closed_stack_results_trans; last exact H1_values0.
      apply closed_stack_results_append; first exact H1_values.
      apply closed_stack_results_refl. }
    have Tail : closed_stack_results_subtyping (s_types s)
      (lift_closed_result_type ts_values0) ts.
    { eapply closed_stack_suffix with
        (a := lift_closed_result_type ts_values) (c := prefix ++ before).
      - rewrite <-List.app_assoc.
        eapply closed_stack_results_trans; eauto.
      - unfold lift_closed_result_type. rewrite List.length_map.
        have ValuesLength := closed_values_length s vs0 ts_values0 H2_values0.
        rewrite v_to_e_length in HLength. by lias. }
    eapply ety_subtyping; first exact (et_values_typing C H2_values0).
    by apply closed_instr_empty_input_intro.
  - by eapply IHlh; eauto.
Qed.

Lemma Frame_return_typing {k}: forall s C vs f LI tf (lh: lholed k),
    e_typing s C [:: AI_frame (length vs) f LI] tf ->
    const_list vs ->
    lfill lh (vs ++ [::AI_basic BI_return]) = LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf lh HType HConst Hlf.
  destruct tf as [t1s t2s].
  invert_e_typing.
  apply const_es_exists in HConst as [? ->].
  have Length := List.Forall2_length Hconjl2.
  have Inner : e_typing s (upd_return C0 (Some extr0)) (v_to_e_list x)
      (Closed_ft nil extr0).
  { eapply Lfilled_return_typing with (lh := lh); eauto;
      try reflexivity; try apply v_to_e_const.
    by rewrite Length. }
  destruct (Values_typing_inversion Inner) as [types [Subtype Values]].
  apply closed_instr_empty_input_elim in Subtype; simpl in Subtype.
  eapply ety_subtyping; last exact Htisub.
  eapply ety_subtyping; first exact (et_values_typing C Values).
  apply closed_instr_empty_input_intro.
  eapply closed_stack_results_trans; eauto.
Qed.

(* Auxiliary lemmas for the tactics resolving e_typing *)
Lemma value_cons_e_typing: forall s C v t es tx ty,
    closed_value_typing s v t ->
    e_typing s C es (Closed_ft (tx ++ [::CO_value t]) ty) ->
    e_typing s C (cons ($V v) es) (Closed_ft tx ty).
Proof.
  move => s C v t es tx ty Hvt Het.
  rewrite -cat1s; eapply et_composition'; eauto.
  eapply et_value_typing'; eauto.
  apply closed_instr_empty_input_intro. apply closed_stack_results_refl.
Qed.

Lemma values_cat_e_typing: forall s C vs ts es tx ty,
    closed_values_typing s vs ts ->
    e_typing s C es (Closed_ft (tx ++ lift_closed_result_type ts) ty) ->
    e_typing s C (v_to_e_list vs ++ es) (Closed_ft tx ty).
Proof.
  move => s C vs ts es tx ty Hvt Het.
  eapply et_composition'; eauto.
  eapply et_values_typing'; eauto.
  apply closed_instr_empty_input_intro. apply closed_stack_results_refl.
Qed.

Lemma value_num_cons_e_typing: forall s C v es tx ty,
    e_typing s C es (Closed_ft (tx ++ [::CO_value (CV_num (typeof_num v))]) ty) ->
    e_typing s C (cons ($VN v) es) (Closed_ft tx ty).
Proof.
  intros.
  replace ($VN v) with ($V (VAL_num v)) => //.
  eapply value_cons_e_typing; eauto.
  by destruct v.
Qed.

Lemma value_vec_cons_e_typing: forall s C v es tx ty,
    e_typing s C es (Closed_ft (tx ++ [::CO_value (CV_vec (typeof_vec v))]) ty) ->
    e_typing s C (cons ($V (VAL_vec v)) es) (Closed_ft tx ty).
Proof.
  intros.
  eapply value_cons_e_typing; eauto.
  by destruct v.
Qed.

End Typing_inversion_e.

(** Control-flow operands are canonical; no source-name transport is needed. *)
Ltac invert_e_typing ::=
  repeat match goal with
  | H: thread_typing _ _ _ _ |- _ =>
    let C := fresh "C" in
    let Frame := fresh "Hframetype" in
    let Body := fresh "Hetype" in
    apply et_thread_typing in H as [C [Frame Body]]; subst
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let middle := fresh "ts3_comp" in
    let Left := fresh "H1_comp" in
    let Right := fresh "H2_comp" in
    apply e_composition_typing in H as [middle [Left Right]]; subst
  | H: e_typing ?s ?C [::AI_basic (BI_const_num ?number)] ?signature |- _ =>
    let t := fresh "ts_value" in
    let Sub := fresh "H1_value" in
    let Value := fresh "H2_value" in
    change (e_typing s C [::v_to_e (VAL_num number)] signature) in H;
    apply Value_typing_inversion in H as [t [Sub Value]]
  | H: e_typing ?s ?C [::AI_basic (BI_const_vec ?vector)] ?signature |- _ =>
    let t := fresh "ts_value" in
    let Sub := fresh "H1_value" in
    let Value := fresh "H2_value" in
    change (e_typing s C [::v_to_e (VAL_vec vector)] signature) in H;
    apply Value_typing_inversion in H as [t [Sub Value]]
  | H: e_typing _ _ [::$V _] _ |- _ =>
    let t := fresh "ts_value" in
    let Sub := fresh "H1_value" in
    let Value := fresh "H2_value" in
    apply Value_typing_inversion in H as [t [Sub Value]]; subst
  | H: e_typing _ _ [::AI_basic _] _ |- _ =>
    apply et_to_bet in H => //; simpl in H
  | H: closed_be_typing _ _ [::BI_br _] _ |- _ =>
    apply cbet_branch_inversion in H; extract_premise
  | H: closed_be_typing _ _ [::BI_return] _ |- _ =>
    apply cbet_return_inversion in H; extract_premise
  | H: closed_be_typing _ _ [::BI_drop] _ |- _ =>
    apply cbet_drop_inversion in H; extract_premise
  | H: closed_be_typing _ _ [::BI_nop] _ |- _ =>
    apply cbet_nop_inversion in H
  | H: closed_be_typing _ _ [::BI_select _] _ |- _ =>
    apply cbet_select_inversion in H; extract_premise
  | H: closed_be_typing _ _ [::?instruction] _ |- _ =>
    let Only := fresh "SourceOnly" in
    assert (Only : source_only_instruction instruction = true) by reflexivity;
    let Source := fresh "SourceContext" in
    let Raw := fresh "SourceSignature" in
    let Context := fresh "HSourceContext" in
    let Principal := fresh "HSourcePrincipal" in
    let Subtype := fresh "Htisub" in
    apply cbet_source_inversion in H as
      [Source [Raw [Context [Principal Subtype]]]]; last exact Only;
    clear Only;
    simpl in Principal; extract_premise; subst;
    cbn [interpret_instr_type interpret_operand_results] in Subtype
  | H: closed_be_typing _ _ [::?instruction] _ |- _ =>
    let Control := fresh "Control" in
    assert (Control : nested_control_instruction instruction = true) by reflexivity;
    let principal := fresh "principal" in
    let Subtype := fresh "Htisub" in
    let View := fresh "Hcontrol" in
    apply cbet_control_inversion in H as [principal [Subtype View]]; last exact Control;
    clear Control; simpl in View; extract_premise; subst;
    cbn [interpret_instr_type interpret_operand_results] in Subtype
  | H: e_typing _ _ (v_to_e_list _) _ |- _ =>
    let ts := fresh "ts_values" in
    let Sub := fresh "H1_values" in
    let Values := fresh "H2_values" in
    apply Values_typing_inversion in H as [ts [Sub Values]]; subst
  | H: e_typing _ _ [::_] _ |- _ =>
    let principal := fresh "tf_principal" in
    let Sub := fresh "Htisub" in
    let View := fresh "Hinvgoal" in
    apply e_typing_inversion in H as [principal [Sub View]];
      simpl in View; extract_premise
  | H: e_typing _ _ nil _ |- _ => apply empty_e_typing in H
  | H: e_typing _ _ (cons ?x _) _ |- _ => rewrite -(cat1s x) in H
  end; resolve_list_eq.
