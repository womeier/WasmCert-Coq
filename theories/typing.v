(** Wasm typing rules **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations subtyping.
From Wasm Require Import gc_declaration_typing.
From Stdlib Require Import NArith.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Context `{hfc: host_function_class} `{memory: BlockUpdateMemory}.

(** std-doc:
For the purpose of checking external values against imports, such values are classified by external types. The following auxiliary typing rules specify this typing relation relative to a store S in which the referenced instances live.
 **)
Definition ext_func_typing (s: store_record) (addr: funcaddr) : option function_type :=
  match lookup_N s.(s_funcs) addr with
  | Some x => Some (cl_type x)
  | None => None
  end.

Definition ext_table_typing (s: store_record) (addr: tableaddr) : option closed_table_type :=
  match lookup_N s.(s_tables) addr with
  | Some x => Some (tableinst_type x)
  | None => None
  end.
  
Definition ext_mem_typing (s: store_record) (addr: memaddr) : option memory_type :=
  match lookup_N s.(s_mems) addr with
  | Some x => Some (meminst_type x)
  | None => None
  end.

Definition ext_global_typing (s: store_record) (addr: globaladdr) : option closed_global_type :=
  match lookup_N s.(s_globals) addr with
  | Some x => Some (g_type x)
  | None => None
  end.

Definition ext_typing (s: store_record) (v: extern_value) : option closed_extern_type :=
  match v with
  | EV_func a => option_map CET_func (lookup_func_defined_type s a)
  | EV_table a => option_map CET_table (ext_table_typing s a)
  | EV_mem a => option_map CET_mem (ext_mem_typing s a)
  | EV_global a => option_map CET_global (ext_global_typing s a)
   end.                                 

(** std-doc:
For the purpose of checking argument values against the parameter types of exported functions, values are classified by value types. The following auxiliary typing rules specify this typing relation relative to a store S in which possibly referenced addresses live.
 **)

Definition typeof_ref (s: store_record) (v: value_ref) : option reference_type :=
  match v with
  | VAL_ref_null t => Some (Ref_type true t)
  | VAL_ref_func addr =>
      match ext_func_typing s addr with
      | Some ft => Some T_funcref
      | _ => None
      end
  | VAL_ref_extern eaddr => Some T_externref
  | VAL_ref_i31 _ => Some (Ref_type false HT_i31)
  end.

Definition typeof_value (s: store_record) (v: value) : option value_type :=
  match v with
  | VAL_num v' => Some (T_num (typeof_num v'))
  | VAL_vec v' => Some (T_vec (typeof_vec v'))
  | VAL_ref v' => option_map T_ref (typeof_ref s v')
  end.                      

(** Closed runtime classification. A source HT_type is never a runtime null
    annotation: it must be lowered in its producer instance before storage.
    The compatibility classifier above remains for the ongoing source-context
    proof migration; canonical storage must use these closed descriptors. *)
Definition typeof_closed_ref (s : store_record) (v : value_ref) :
    option closed_reference_type :=
  match v with
  | VAL_ref_null h =>
      match h with
      | HT_type _ => None
      | _ => Some (Closed_ref true (CH_abstract h))
      end
  | VAL_ref_func address =>
      option_map (fun id => Closed_ref false (CH_defined (CT_def id)))
        (lookup_func_defined_type s address)
  | VAL_ref_extern _ => Some (Closed_ref false (CH_abstract HT_extern))
  | VAL_ref_i31 _ => Some (Closed_ref false (CH_abstract HT_i31))
  end.

Definition typeof_closed_value (s : store_record) (v : value) : option closed_value_type :=
  match v with
  | VAL_num n => Some (CV_num (typeof_num n))
  | VAL_vec v => Some (CV_vec (typeof_vec v))
  | VAL_ref r => option_map closed_reference_value (typeof_closed_ref s r)
  end.

Definition closed_value_typing (s : store_record) (v : value) (expected : closed_value_type) : bool :=
  match typeof_closed_value s v with
  | None => false
  | Some actual =>
      closed_value_validb s.(s_types) actual &&
      closed_value_validb s.(s_types) expected &&
      closed_value_matchesb s.(s_types) actual expected
  end.

Definition value_typing (s : store_record) (names : list defined_type)
    (v : value) (expected : value_type) : bool :=
  match gc_type_context.close_value_type names 0 expected with
  | None => false
  | Some closed => closed_value_typing s v closed
  end.

Definition source_value_typing (s : store_record) (inst : moduleinst)
    (v : value) (expected : value_type) : bool :=
  value_typing s inst.(inst_defined_types) v expected.

(** Indexed nulls are lowered in the producing instance. Bottom heaps retain
    their hierarchy (nofunc versus none); no producer-local index escapes. *)
Definition lower_source_null (s : store_record) (inst : moduleinst)
    (source : heap_type) : option value_ref :=
  match gc_type_context.close_heap_type inst.(inst_defined_types) 0 source with
  | None => None
  | Some expected => lower_closed_null s.(s_types) expected
  end.

Definition values_typing (s: store_record) (names : list defined_type)
    (vs: list value) (tf: list value_type) : bool :=
  all2 (value_typing s names) vs tf.

Definition result_types_agree (s: store_record) (names : list defined_type)
    (ts : result_type) r : bool :=
  match r with
  | result_values vs => values_typing s names vs ts
  | result_trap => true
  end.

(** std-doc:
https://www.w3.org/TR/wasm-core-2/exec/runtime.html#exec-expand
**)
Definition expand_t {V R F O : Set} (C: t_context_gen V R F O)
    (tb: block_type) : option instr_type :=
  match tb with
  | BT_id n => lookup_function_type C.(tc_types) n
  | BT_valtype (Some t) => Some (Tf [::] [::t])
  | BT_valtype None => Some (Tf [::] [::])
  end.

Definition convert_helper (sxo : option sx) t1 t2 : bool :=
  match (sxo, t1, t2) with
  | (Some SX_U, T_i32, T_i64)  (* i32.wrap_i64 *)
  | (Some SX_S, T_i32, T_f32)  (* i32.trunc_f32_s *)
  | (Some SX_U, T_i32, T_f32)  (* i32.trunc_f32_u *)
  | (Some SX_S, T_i32, T_f64)  (* i32.trunc_f64_s *)
  | (Some SX_U, T_i32, T_f64)  (* i32.trunc_f64_u *)
  | (Some SX_S, T_i64, T_i32)  (* i64.extend_i32_s *)
  | (Some SX_U, T_i64, T_i32)  (* i64.extend_i32_u *)
  | (Some SX_S, T_i64, T_f32)  (* i64.trunc_f32_s *)
  | (Some SX_U, T_i64, T_f32)  (* i64.trunc_f32_u *)
  | (Some SX_S, T_i64, T_f64)  (* i64.trunc_f64_s *)
  | (Some SX_U, T_i64, T_f64)  (* i64.trunc_f64_u *)
  | (Some SX_S, T_f32, T_i32)  (* f32.convert_i32_s *)
  | (Some SX_U, T_f32, T_i32)  (* f32.convert_i32_u *)
  | (Some SX_S, T_f32, T_i64)  (* f32.convert_i64_s *)
  | (Some SX_U, T_f32, T_i64)  (* f32.convert_i64_u *)
  | (None, T_f32, T_f64)       (* f32.demote_f64 *)
  | (Some SX_S, T_f64, T_i32)  (* f64.convert_i32_s *)
  | (Some SX_U, T_f64, T_i32)  (* f64.convert_i32_u *)
  | (Some SX_S, T_f64, T_i64)  (* f64.convert_i64_s *)
  | (Some SX_U, T_f64, T_i64)  (* f64.convert_i64_u *)
  | (None, T_f64, T_f32)       (* f64.promote_f32 *)
  | (None, T_i32, T_f32)       (* i32.reinterpret_f32 *)
  | (None, T_i64, T_f64)       (* i64.reinterpret_f64 *)
  | (None, T_f32, T_i32)       (* f32.reinterpret_i32 *)
  | (None, T_f64, T_i64)       (* f64.reinterpret_i64 *)
      => true
  | _ => false
  end.

Definition upd_local_label_return {V R F O : Set} (C : t_context_gen V R F O)
    (loc : list V) (lab : list (list O)) (ret : option (list O)) :=
  Build_t_context
    (tc_types C)
    (tc_funcs C)
    (tc_tables C)
    (tc_mems C)
    (tc_globals C)
    (tc_elems C)
    (tc_datas C)
    loc
    lab
    ret
    (tc_refs C)
    (tc_defined_types C).

Definition upd_refs {V R F O : Set} (C : t_context_gen V R F O) refs :=
{|
  tc_types := tc_types C;
  tc_funcs := tc_funcs C;
  tc_tables := tc_tables C;
  tc_mems := tc_mems C;
  tc_globals := tc_globals C;
  tc_elems := tc_elems C;
  tc_datas := tc_datas C;
  tc_locals := tc_locals C;
  tc_labels := tc_labels C;
  tc_return := tc_return C;
  tc_refs := refs;
  tc_defined_types := C.(tc_defined_types)
|}.

Definition upd_local {V R F O : Set} (C : t_context_gen V R F O) loc :=
  upd_local_label_return C loc (tc_labels C) (tc_return C).

Definition upd_label {V R F O : Set} (C : t_context_gen V R F O) lab :=
  upd_local_label_return C (tc_locals C) lab (tc_return C).

Definition upd_return {V R F O : Set} (C : t_context_gen V R F O) ret :=
  upd_local_label_return C (tc_locals C) (tc_labels C) ret.

(* Helper for typing Select. Needs to get an update when updating to GC to implement
   subtyping *)
Definition is_numeric_type (t: value_type) : bool :=
  match t with
  | T_num _ => true
  | T_vec _ => true
  | T_bot => true
  | _ => false
  end.

(** std-doc:
Instructions are classified by stack types that describe how instructions manipulate the operand stack.

The types describe the required input stack with operand types that an instruction pops off and
the provided output stack with result values of types that it pushes back. Stack types are akin 
to function types, except that they allow individual operands to be classified as ⊥ (bottom), 
indicating that the type is unconstrained. As an auxiliary notion, an operand type t1
matches another operand type t2, if t1 is either ⊥ or equal to t2. This is extended to stack
types in a point-wise manner.

https://www.w3.org/TR/wasm-core-2/valid/instructions.html
 **)
Definition source_heap_scopedb (types : type_context) (heap : heap_type) : bool :=
  match heap with
  | HT_type index => match lookup_N types index with Some _ => true | None => false end
  | _ => true
  end.

Lemma source_heap_scopedb_map f types heap :
  source_heap_scopedb (List.map f types) heap = source_heap_scopedb types heap.
Proof.
  destruct heap; simpl; try reflexivity.
  unfold lookup_N. rewrite List.nth_error_map.
  by destruct (List.nth_error types (N.to_nat t)).
Qed.

Inductive be_typing : t_context -> seq basic_instruction -> instr_type -> Prop :=
| bet_const_num : forall C v, be_typing C [::BI_const_num v] (Tf [::] [::T_num (typeof_num v)])
| bet_const_vec : forall C v, be_typing C [::BI_const_vec v] (Tf [::] [::T_vec (typeof_vec v)])
| bet_ref_null: forall C t,
    source_heap_scopedb C.(tc_types) t ->
    be_typing C [::BI_ref_null t] (Tf [::] [::T_ref (Ref_type true t)])
| bet_ref_is_null: forall C t, be_typing C [::BI_ref_is_null] (Tf [::T_ref t] [::T_num T_i32])
| bet_ref_func: forall C t x,
    lookup_N (tc_funcs C) x = Some t ->
    List.In x (tc_refs C) ->
    be_typing C [::BI_ref_func x] (Tf [::] [::T_ref T_funcref])
| bet_unop : forall C t op,
    unop_type_agree t op -> be_typing C [::BI_unop t op] (Tf [::T_num t] [::T_num t])
| bet_binop : forall C t op,
    binop_type_agree t op -> be_typing C [::BI_binop t op] (Tf [::T_num t; T_num t] [::T_num t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::BI_testop t op] (Tf [::T_num t] [::T_num T_i32])
| bet_relop: forall C t op,
    relop_type_agree t op -> be_typing C [::BI_relop t op] (Tf [::T_num t; T_num t] [::T_num T_i32])
| bet_cvtop : forall C op t1 t2 sx,
    cvtop_valid t2 op t1 sx ->
    be_typing C [::BI_cvtop t2 op t1 sx] (Tf [::T_num t1] [::T_num t2])
| bet_vunop: forall C op,
    be_typing C [::BI_vunop op] (Tf [::T_vec T_v128] [::T_vec T_v128])
| bet_vbinop: forall C op,
    vbinop_valid op -> (* Check against laneids for shuffle *)
    be_typing C [::BI_vbinop op] (Tf [::T_vec T_v128; T_vec T_v128] [::T_vec T_v128])
| bet_vternop: forall C op,
    be_typing C [::BI_vternop op] (Tf [::T_vec T_v128; T_vec T_v128; T_vec T_v128] [::T_vec T_v128])
| bet_vtestop: forall C op,
    be_typing C [::BI_vtestop op] (Tf [::T_vec T_v128] [::T_num T_i32])
| bet_vshiftop: forall C op,
    be_typing C [::BI_vshiftop op] (Tf [::T_vec T_v128; T_num T_i32] [::T_vec T_v128])
| bet_splat_vec: forall C sh,
    be_typing C [::BI_splat_vec sh] (Tf [::T_num (typeof_shape_unpacked sh)] [::T_vec T_v128])
| bet_extract_vec: forall C sh sx x,
    N.ltb x (shape_dim sh) = true ->
    be_typing C [::BI_extract_vec sh sx x] (Tf [::T_vec T_v128] [::T_num (typeof_shape_unpacked sh)])
| bet_replace_vec: forall C shape x,
    N.ltb x (shape_dim shape) = true ->
    be_typing C [::BI_replace_vec shape x] (Tf [::T_vec T_v128; T_num (typeof_shape_unpacked shape)] [::T_vec T_v128])
| bet_unreachable : forall C ts ts',
  be_typing C [::BI_unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::BI_nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::BI_drop] (Tf [::t] [::])
| bet_select_Some : forall C t, be_typing C [::BI_select (Some [::t])] (Tf [:: t; t; T_num T_i32] [::t])
| bet_select_None : forall C t, is_numeric_type t -> be_typing C [::BI_select None] (Tf [:: t; t; T_num T_i32] [::t])
| bet_block : forall C tb tn tm es,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_labels C))) es (Tf tn tm) ->
  be_typing C [::BI_block tb es] (Tf tn tm)
| bet_loop : forall C tb tn tm es,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tn] ++ (tc_labels C))) es (Tf tn tm) ->
  be_typing C [::BI_loop tb es] (Tf tn tm)
| bet_if_wasm : forall C tb tn tm es1 es2,
  expand_t C tb = Some (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_labels C))) es1 (Tf tn tm) ->
  be_typing (upd_label C ([::tm] ++ (tc_labels C))) es2 (Tf tn tm) ->
  be_typing C [::BI_if tb es1 es2] (Tf (tn ++ [::T_num T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  lookup_N C.(tc_labels) i = Some ts ->
  be_typing C [::BI_br i] (Tf (t1s ++ ts) t2s)
| bet_br_if : forall C i ts,
  lookup_N C.(tc_labels) i = Some ts ->
  be_typing C [::BI_br_if i] (Tf (ts ++ [::T_num T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  List.Forall (fun i => (exists ts', lookup_N C.(tc_labels) i = Some ts' /\ ts <ts: ts')) (ins ++ [::i]) ->
  be_typing C [::BI_br_table ins i] (Tf (t1s ++ (ts ++ [::T_num T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::BI_return] (Tf (t1s ++ ts) t2s)
| bet_call : forall C i tf,
  lookup_N (tc_funcs C) i = Some tf ->
  be_typing C [::BI_call i] tf
| bet_call_indirect : forall C x y tabtype t1s t2s,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = T_funcref ->
   lookup_function_type (tc_types C) y = Some (Tf t1s t2s) ->
  be_typing C [::BI_call_indirect x y] (Tf (t1s ++ [::T_num T_i32]) t2s)
| bet_return_call : forall C x t1s t2s t3s t4s,
  lookup_N (tc_funcs C) x = Some (Tf t1s t2s) ->
  tc_return C = Some t2s ->
  be_typing C [::BI_return_call x] (Tf (t3s ++ t1s) t4s)
| bet_return_call_indirect : forall C x y tabt t1s t2s t3s t4s,
  lookup_N (tc_tables C) x = Some tabt ->
  tabt.(tt_elem_type) = T_funcref ->
   lookup_function_type (tc_types C) y = Some (Tf t1s t2s) ->
  tc_return C = Some t2s ->
  be_typing C [::BI_return_call_indirect x y] (Tf (t3s ++ t1s ++ [::T_num T_i32]) t4s)
| bet_local_get : forall C x t,
  lookup_N (tc_locals C) x = Some t ->
  be_typing C [::BI_local_get x] (Tf [::] [::t])
| bet_local_set : forall C x t,
  lookup_N (tc_locals C) x = Some t ->
  be_typing C [::BI_local_set x] (Tf [::t] [::])
| bet_local_tee : forall C x t,
  lookup_N (tc_locals C) x = Some t ->
  be_typing C [::BI_local_tee x] (Tf [::t] [::t])
| bet_global_get : forall C x gt t,
  lookup_N (tc_globals C) x = Some gt ->  
  tg_t gt = t ->
  be_typing C [::BI_global_get x] (Tf [::] [::t])
| bet_global_set : forall C x gt t,
  lookup_N (tc_globals C) x = Some gt ->  
  tg_t gt = t ->
  is_mut gt ->
  be_typing C [::BI_global_set x] (Tf [::t] [::])
| bet_table_get : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_get x] (Tf [::T_num T_i32] [::T_ref t])
| bet_table_set : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_set x] (Tf [::T_num T_i32; T_ref t] [::])
| bet_table_size : forall C x tabtype,
  lookup_N (tc_tables C) x = Some tabtype ->
  be_typing C [::BI_table_size x] (Tf [::] [::T_num T_i32])
| bet_table_grow : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_grow x] (Tf [::T_ref t; T_num T_i32] [::T_num T_i32])
| bet_table_fill : forall C x tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  be_typing C [::BI_table_fill x] (Tf [::T_num T_i32; T_ref t; T_num T_i32] [::])
| bet_table_copy : forall C x y tabtype1 tabtype2 t,
  lookup_N (tc_tables C) x = Some tabtype1 ->
  tabtype1.(tt_elem_type) = t ->
  lookup_N (tc_tables C) y = Some tabtype2 ->
  tabtype2.(tt_elem_type) = t ->
  be_typing C [::BI_table_copy x y] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_table_init : forall C x y tabtype t,
  lookup_N (tc_tables C) x = Some tabtype ->
  tabtype.(tt_elem_type) = t ->
  lookup_N (tc_elems C) y = Some t ->
  be_typing C [::BI_table_init x y] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_elem_drop : forall C x t,
  lookup_N (tc_elems C) x = Some t ->
  be_typing C [::BI_elem_drop x] (Tf [::] [::])
| bet_load : forall C m_arg tp_sx t mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_t_bounds m_arg.(memarg_align) (option_projl tp_sx) t ->
  be_typing C [::BI_load t tp_sx m_arg] (Tf [::T_num T_i32] [::T_num t])
| bet_load_vec : forall C lv_arg m_arg mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_vec_bounds lv_arg m_arg ->
  be_typing C [::BI_load_vec lv_arg m_arg] (Tf [::T_num T_i32] [::T_vec T_v128])
| bet_load_vec_lane : forall C width m_arg x mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_vec_lane_bounds width m_arg x ->
  be_typing C [::BI_load_vec_lane width m_arg x] (Tf [::T_num T_i32; T_vec T_v128] [::T_vec T_v128])
| bet_store : forall C m_arg tp t mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_t_bounds m_arg.(memarg_align) tp t ->
  be_typing C [::BI_store t tp m_arg] (Tf [::T_num T_i32; T_num t] [::])
| bet_store_vec : forall C m_arg mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  store_vec_bounds m_arg ->
  be_typing C [::BI_store_vec m_arg] (Tf [::T_num T_i32; T_vec T_v128] [::])
| bet_store_vec_lane : forall C width m_arg x mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  load_store_vec_lane_bounds width m_arg x ->
  be_typing C [::BI_store_vec_lane width m_arg x] (Tf [::T_num T_i32; T_vec T_v128] [::])
| bet_memory_size : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_size] (Tf [::] [::T_num T_i32])
| bet_memory_grow : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_grow] (Tf [::T_num T_i32] [::T_num T_i32])
| bet_memory_fill : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_fill] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_memory_copy : forall C mem,
  lookup_N (tc_mems C) 0%N = Some mem ->
  be_typing C [::BI_memory_copy] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_memory_init : forall C x mem dat,
  lookup_N (tc_mems C) 0%N = Some mem ->
  lookup_N (tc_datas C) x = Some dat ->
  be_typing C [::BI_memory_init x] (Tf [::T_num T_i32; T_num T_i32; T_num T_i32] [::])
| bet_data_drop : forall C x dat,
  lookup_N (tc_datas C) x = Some dat ->
  be_typing C [::BI_data_drop x] (Tf [::] [::])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (es ++ [::e]) (Tf t1s t3s)
(** Subtyping rule from the upcoming GC proposal
[https://github.com/WebAssembly/gc/blob/main/proposals/gc/Overview.md]
**)
| bet_subtyping : forall C es t1s t2s t1s' t2s',
  be_typing C es (Tf t1s t2s) ->
  (Tf t1s t2s) <ti: (Tf t1s' t2s') ->
  be_typing C es (Tf t1s' t2s')
(* Erased compatibility rule: nullability refinement will become explicit
   when the shared reference type representation is extended. *)
| bet_ref_as_non_null : forall C t,
  is_ref_t t ->
  be_typing C [::BI_ref_as_non_null] (Tf [::t] [::t])
| bet_br_on_non_null : forall C x ts t,
  lookup_N C.(tc_labels) x = Some (ts ++ [::t]) ->
  is_ref_t t ->
  be_typing C [::BI_br_on_non_null x] (Tf (ts ++ [::t]) ts)
| bet_ref_i31 : forall C,
  be_typing C [::BI_ref_i31]
    (Tf [::T_num T_i32] [::T_ref (Ref_type false HT_i31)])
| bet_i31_get : forall C signed nullable,
  be_typing C [::BI_i31_get signed]
    (Tf [::T_ref (Ref_type nullable HT_i31)] [::T_num T_i32])
.

Definition expr_typing (C: t_context) (bes: list basic_instruction) (ts: result_type) : Prop :=
  be_typing C bes (Tf nil ts).

Definition func_typing (C: t_context) (code: module_func) (tf: function_type) : Prop :=
  let: {| modfunc_type := x; modfunc_locals := ts; modfunc_body := bes |} := code in
  match lookup_function_type C.(tc_types) x with
  | Some (Tf ts1 ts2) =>
      tf = (Tf ts1 ts2) /\
      let C' := upd_local_label_return C (ts1 ++ ts) [:: ts2] (Some ts2) in
      expr_typing C' bes ts2 /\
      (* This is an artificial restriction added due to the implementation of subtyping from the future GC proposal, but without the implementing non-defaultable locals *)
      default_vals ts <> None
  | None => False
  end.
    
(** std-doc:
The following typing rules specify when a runtime store S is valid. A valid store must consist of
 function, table, memory, global, and module instances that are themselves valid, relative to S.

To that end, each kind of instance is classified by a respective function, table, memory, or global
 type. Module instances are classified by module contexts, which are regular contexts repurposed as
 module types describing the index spaces defined by a module.
https://www.w3.org/TR/wasm-core-2/appendix/properties.html#store-validity
**)

Section Store_validity. 

(* funcinst typing is dependent on a later definition, although stated before it in the spec document. *)
  
Definition tableinst_typing (s: store_record) (ti: tableinst) : option closed_table_type :=
  let '{| tableinst_type := ti_type; tableinst_elem := refs |} := ti in
  if closed_ref_nullable ti_type.(tt_elem_type) &&
      limit_valid_range ti_type.(tt_limits) table_limit_bound then
    if N.of_nat (length refs) == ti_type.(tt_limits).(lim_min) then
      if all (fun ref => closed_value_typing s (VAL_ref ref)
          (closed_reference_value ti_type.(tt_elem_type))) refs then
        Some ti_type
      else None
    else None
  else None.

Definition meminst_typing (s: store_record) (mi: meminst) : option memory_type :=
  let '{| meminst_type := mi_type; meminst_data := ds |} := mi in
  if memtype_valid mi_type then
    if mem_length mi == N.mul (mi_type.(lim_min)) page_size then
      Some mi_type
    else None
  else None.

Definition globalinst_typing (s: store_record) (gi: globalinst) : option closed_global_type :=
  let '{| g_type := gi_type; g_val := gv |} := gi in
  if closed_value_validb s.(s_types) gi_type.(tg_t) then
    if closed_value_typing s gv (gi_type.(tg_t)) then
      Some gi_type
    else None
  else None.

Definition eleminst_typing (s: store_record) (ei: eleminst) : option closed_reference_type :=
  let '{| eleminst_type := ei_type; eleminst_elem := refs |} := ei in
  if closed_value_validb s.(s_types) (closed_reference_value ei_type) &&
      all (fun ref => closed_value_typing s (VAL_ref ref) (closed_reference_value ei_type)) refs then
    Some ei_type
  else None.

Definition datainst_typing (s: store_record) (di: datainst): option ok :=
  Some tt.

Definition exportinst_typing (s: store_record) (expi: exportinst) : option ok :=
  let '{| exportinst_name := e_name; exportinst_val := e_val |} := expi in
  if ext_typing s e_val != None then
    Some tt
  else None.

(** std-doc:
[https://webassembly.github.io/spec/core/appendix/properties.html#module-instances-xref-exec-runtime-syntax-moduleinst-mathit-moduleinst]

This definition is currently computable -- hopefully it remains so in the future; otherwise we need to make it back to a Prop/Bool.
 **)
Definition instance_function_view s names address source : bool :=
  match lookup_func_defined_type s address,
        gc_type_context.close_function_type names 0 source with
  | Some id, Some expected =>
      match gc_type_context.expand_function_type s.(s_types) id with
      | Some actual =>
          closed_composite_matchesb s.(s_types) (Comp_func actual) (Comp_func expected)
      | None => false
      end
  | _, _ => false
  end.

Definition instance_table_view s names address source : bool :=
  match ext_table_typing s address, close_table_type names source with
  | Some actual, Some expected =>
      closed_value_validb s.(s_types) (closed_reference_value actual.(tt_elem_type)) &&
      closed_value_validb s.(s_types) (closed_reference_value expected.(tt_elem_type)) &&
      closed_value_matchesb s.(s_types) (closed_reference_value actual.(tt_elem_type))
        (closed_reference_value expected.(tt_elem_type)) &&
      closed_value_matchesb s.(s_types) (closed_reference_value expected.(tt_elem_type))
        (closed_reference_value actual.(tt_elem_type)) &&
      N.leb expected.(tt_limits).(lim_min) actual.(tt_limits).(lim_min) &&
      match expected.(tt_limits).(lim_max), actual.(tt_limits).(lim_max) with
      | None, _ => true
      | Some maximum, Some actual_maximum => N.leb actual_maximum maximum
      | Some _, None => false
      end
  | _, _ => false
  end.

Definition instance_global_view s names address source : bool :=
  match ext_global_typing s address, close_global_type names source with
  | Some actual, Some expected =>
      (actual.(tg_mut) == expected.(tg_mut)) &&
      closed_value_validb s.(s_types) actual.(tg_t) &&
      closed_value_validb s.(s_types) expected.(tg_t) &&
      closed_value_matchesb s.(s_types) actual.(tg_t) expected.(tg_t) &&
      match expected.(tg_mut) with
      | MUT_const => true
      | MUT_var => closed_value_matchesb s.(s_types) expected.(tg_t) actual.(tg_t)
      end
  | _, _ => false
  end.

Definition instance_element_view s names address source : bool :=
  match lookup_N s.(s_elems) address, close_reference_type names source with
  | Some element, Some expected =>
      match eleminst_typing s element with
      | Some actual =>
          closed_value_validb s.(s_types) (closed_reference_value expected) &&
          closed_value_matchesb s.(s_types) (closed_reference_value actual)
            (closed_reference_value expected) &&
          closed_value_matchesb s.(s_types) (closed_reference_value expected)
            (closed_reference_value actual)
      | None => false
      end
  | _, _ => false
  end.

Definition inst_typing (s : store_record) (inst : moduleinst) : option t_context :=
  let source := inst.(inst_context) in
  let names := inst.(inst_defined_types) in
  if all source_subtype_valid inst.(inst_types) &&
      source_type_identitiesb s.(s_types) names inst.(inst_types) names &&
      all2 (instance_function_view s names) inst.(inst_funcs) source.(tc_funcs) &&
      all2 (instance_table_view s names) inst.(inst_tables) source.(tc_tables) &&
      all2 (instance_global_view s names) inst.(inst_globals) source.(tc_globals) &&
      all2 (instance_element_view s names) inst.(inst_elems) source.(tc_elems)
  then
    match those (map (ext_mem_typing s) inst.(inst_mems)),
          those (map (fun a => match lookup_N s.(s_datas) a with
                             | Some di => datainst_typing s di
                             | None => None end) inst.(inst_datas)) with
    | Some memories, Some datas =>
        Some (Build_t_context inst.(inst_types) source.(tc_funcs) source.(tc_tables)
          memories source.(tc_globals) source.(tc_elems) datas
          nil nil None (iota_N 0 (length inst.(inst_funcs))) names)
    | _, _ => None
    end
  else None.

Definition inst_typecheck (s: store_record) (inst: moduleinst) (C: t_context) : bool :=
  inst_typing s inst == Some C.

Definition frame_typing (s: store_record) (f: frame) (C: t_context): Prop :=
  match inst_typing s f.(f_inst) with
  | Some C0 =>
      exists ts, C = upd_local C0 (ts ++ tc_locals C0) /\
              values_typing s f.(f_inst).(inst_defined_types) f.(f_locs) ts
  | None => False
  end.

(** Storable types and internal operand slots have separate closing functions.
    Only the latter represents the source checker's polymorphic bottom. *)
Definition close_result_type names (ts : result_type) : option closed_result_type :=
  those (List.map (gc_type_context.close_value_type names 0) ts).

Definition close_operand_type names (t : value_type) : option closed_operand_type :=
  match t with
  | T_bot => Some CO_bot
  | _ => option_map CO_value (gc_type_context.close_value_type names 0 t)
  end.

Definition close_operand_result_type names (ts : result_type) :
    option closed_operand_result_type :=
  those (List.map (close_operand_type names) ts).

Definition close_instr_type names (tf : instr_type) : option closed_instr_type :=
  let '(Tf inputs outputs) := tf in
  match close_operand_result_type names inputs, close_operand_result_type names outputs with
  | Some ins, Some outs => Some (Closed_ft ins outs)
  | _, _ => None
  end.

(** Interpretation of proof-only stack slots. An unresolvable source type has
    no accepted runtime values, just as T_bot has none. This total operation
    is used only on source typing derivations, never for stored descriptors,
    declared signatures, imports, runtime nulls, or actual value acceptance.
    Its exact agreement with value_typing is proved in
    closed_operand_properties; there is no source-index-as-ID fallback. *)
Definition interpret_operand_type names t : closed_operand_type :=
  match close_operand_type names t with
  | Some operand => operand
  | None => CO_bot
  end.

Definition interpret_operand_results names ts : closed_operand_result_type :=
  List.map (interpret_operand_type names) ts.

Definition interpret_instr_type names (tf : instr_type) : closed_instr_type :=
  let '(Tf inputs outputs) := tf in
  Closed_ft (interpret_operand_results names inputs)
    (interpret_operand_results names outputs).

Definition close_return_type names (ret : option result_type) :
    option (option closed_operand_result_type) :=
  match ret with
  | None => Some None
  | Some ts => Some (Some (interpret_operand_results names ts))
  end.

Definition close_t_context (C : t_context) : option closed_t_context :=
  let names := C.(tc_defined_types) in
  match those (List.map (gc_type_context.close_function_type names 0) C.(tc_funcs)),
        those (List.map (close_table_type names) C.(tc_tables)),
        those (List.map (close_global_type names) C.(tc_globals)),
        those (List.map (close_reference_type names) C.(tc_elems)),
        close_result_type names C.(tc_locals),
        Some (List.map (interpret_operand_results names) C.(tc_labels)),
        close_return_type names C.(tc_return) with
  | Some funcs, Some tables, Some globals, Some elems,
    Some locals, Some labels, Some ret =>
      Some (Build_t_context C.(tc_types) funcs tables C.(tc_mems)
        globals elems C.(tc_datas) locals labels ret C.(tc_refs) names)
  | _, _, _, _, _, _, _ => None
  end.

Definition closed_values_typing s (vs : list value) (ts : closed_result_type) : bool :=
  all2 (closed_value_typing s) vs ts.

Definition closed_operand_typing s value operand : bool :=
  match operand with
  | CO_value t => closed_value_typing s value t
  | CO_bot => false
  end.

Definition closed_operands_typing s (values : list value)
    (operands : closed_operand_result_type) : bool :=
  all2 (closed_operand_typing s) values operands.

Definition closed_frame_typing (s : store_record) (f : frame)
    (C : closed_t_context) : Prop :=
  exists source base locals,
    inst_typing s f.(f_inst) = Some source /\
    close_t_context source = Some base /\
    C = upd_local base (locals ++ base.(tc_locals)) /\
    closed_values_typing s f.(f_locs) locals.

Definition closed_results_matchb registry :=
  declaration_list_matchesb (closed_value_matchesb registry).

(** Declarative stack subtyping has the usual structural identity and
    transitivity rules. Runtime matching remains the checked boolean relation
    above. On a valid registry, and for a valid operand type, the declarative
    relation reflects back into that checker (proved downstream). *)
Inductive closed_stack_value_subtyping registry :
    closed_operand_type -> closed_operand_type -> Prop :=
| csv_refl : forall t, closed_stack_value_subtyping registry t t
| csv_bot : forall t, closed_stack_value_subtyping registry CO_bot t
| csv_match : forall a b, closed_value_matchesb registry a b = true ->
    closed_stack_value_subtyping registry (CO_value a) (CO_value b)
| csv_trans : forall a b c,
    closed_stack_value_subtyping registry a b ->
    closed_stack_value_subtyping registry b c ->
    closed_stack_value_subtyping registry a c.

Definition closed_stack_results_subtyping registry :=
  List.Forall2 (closed_stack_value_subtyping registry).

Definition closed_instr_subtyping registry (actual expected : closed_instr_type) : Prop :=
  let '(Closed_ft inputs outputs) := actual in
  let '(Closed_ft inputs' outputs') := expected in
  exists prefix prefix' inputs_sub outputs_sub,
    inputs' = prefix ++ inputs_sub /\
    outputs' = prefix' ++ outputs_sub /\
    closed_stack_results_subtyping registry prefix prefix' /\
    closed_stack_results_subtyping registry inputs_sub inputs /\
    closed_stack_results_subtyping registry outputs outputs_sub.

Definition closed_function_view s address (expected : closed_function_type) : bool :=
  match lookup_func_defined_type s address with
  | Some id =>
      match gc_type_context.expand_function_type s.(s_types) id with
      | Some (Closed_ft inputs outputs) =>
          let '(Closed_ft inputs' outputs') := expected in
          closed_results_matchb s.(s_types) inputs' inputs &&
          closed_results_matchb s.(s_types) outputs outputs'
      | None => false
      end
  | None => false
  end.

(** Only source instructions use this boundary. Administrative operands,
    invocations, labels, and frames never need a source spelling. *)
Inductive closed_be_typing (registry : canonical_registry) : closed_t_context -> list basic_instruction ->
    closed_instr_type -> Prop :=
| close_be_typing : forall source C instruction signature,
    be_typing source [::instruction] signature ->
    (match instruction with
     | BI_block _ _ | BI_loop _ _ | BI_if _ _ _ => False
     | _ => True
     end) ->
    close_t_context source = Some C ->
    closed_be_typing registry C [::instruction]
      (interpret_instr_type source.(tc_defined_types) signature)
| cbet_empty : forall C,
    closed_be_typing registry C [::] (Closed_ft [::] [::])
| cbet_num : forall C number,
    closed_be_typing registry C [::BI_const_num number]
      (Closed_ft [::] [::CO_value (CV_num (typeof_num number))])
| cbet_vec : forall C vector,
    closed_be_typing registry C [::BI_const_vec vector]
      (Closed_ft [::] [::CO_value (CV_vec T_v128)])
| cbet_unreachable : forall C inputs outputs,
    closed_be_typing registry C [::BI_unreachable] (Closed_ft inputs outputs)
| cbet_nop : forall C,
    closed_be_typing registry C [::BI_nop] (Closed_ft [::] [::])
| cbet_drop : forall C operand,
    closed_be_typing registry C [::BI_drop] (Closed_ft [::operand] [::])
| cbet_select : forall C annotation operand,
    (match annotation with
     | Some [::source] => close_operand_type C.(tc_defined_types) source = Some operand
     | None => match operand with
               | CO_value (CV_num _) | CO_value (CV_vec _) | CO_bot => True
               | _ => False
               end
     | _ => False
     end) ->
    closed_be_typing registry C [::BI_select annotation]
      (Closed_ft [::operand; operand; CO_value (CV_num T_i32)] [::operand])
| cbet_block : forall C tb body inputs outputs,
    expand_t C tb = Some (Tf inputs outputs) ->
    closed_be_typing registry
      (upd_label C (interpret_operand_results C.(tc_defined_types) outputs :: C.(tc_labels)))
      body (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs)) ->
    closed_be_typing registry C [::BI_block tb body]
      (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs))
| cbet_loop : forall C tb body inputs outputs,
    expand_t C tb = Some (Tf inputs outputs) ->
    closed_be_typing registry
      (upd_label C (interpret_operand_results C.(tc_defined_types) inputs :: C.(tc_labels)))
      body (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs)) ->
    closed_be_typing registry C [::BI_loop tb body]
      (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs))
| cbet_if : forall C tb yes no inputs outputs,
    expand_t C tb = Some (Tf inputs outputs) ->
    closed_be_typing registry
      (upd_label C (interpret_operand_results C.(tc_defined_types) outputs :: C.(tc_labels)))
      yes (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs)) ->
    closed_be_typing registry
      (upd_label C (interpret_operand_results C.(tc_defined_types) outputs :: C.(tc_labels)))
      no (interpret_instr_type C.(tc_defined_types) (Tf inputs outputs)) ->
    closed_be_typing registry C [::BI_if tb yes no]
      (interpret_instr_type C.(tc_defined_types) (Tf (inputs ++ [::T_num T_i32]) outputs))
| cbet_composition : forall C left instruction inputs middle outputs,
    closed_be_typing registry C left (Closed_ft inputs middle) ->
    closed_be_typing registry C [::instruction] (Closed_ft middle outputs) ->
    closed_be_typing registry C (left ++ [::instruction]) (Closed_ft inputs outputs)
| cbet_subtyping : forall C bes inputs outputs inputs' outputs',
    closed_be_typing registry C bes (Closed_ft inputs outputs) ->
    closed_instr_subtyping registry (Closed_ft inputs outputs) (Closed_ft inputs' outputs') ->
    closed_be_typing registry C bes (Closed_ft inputs' outputs').

Definition source_value_matchesb registry actual_names expected_names actual expected : bool :=
  match gc_type_context.close_value_type actual_names 0 actual,
        gc_type_context.close_value_type expected_names 0 expected with
  | Some a, Some b =>
      closed_value_validb registry a && closed_value_validb registry b &&
      closed_value_matchesb registry a b
  | _, _ => false
  end.

Definition source_results_matchb registry actual_names expected_names :=
  declaration_list_matchesb (source_value_matchesb registry actual_names expected_names).

(** std-doc:
Typing rules for administrative instructions are specified as follows. In addition to the context C, typing
 of these instructions is defined under a given store S. To that end, all previous typing judgements are 
generalized to include the store by implicitly adding S to all rules – S is never modified by the 
pre-existing rules, but it is accessed in the extra rules for administrative instructions given below.

https://www.w3.org/TR/wasm-core-2/appendix/properties.html#administrative-instructions
**)
Inductive e_typing : store_record -> closed_t_context -> seq administrative_instruction -> closed_instr_type -> Prop :=
| ety_a : forall s C bes tf,
  closed_be_typing s.(s_types) C bes tf -> e_typing s C (to_e_list bes) tf
| ety_empty : forall s C,
  e_typing s C [::] (Closed_ft [::] [::])
| ety_composition : forall s C es e t1s t2s t3s,
    e_typing s C es (Closed_ft t1s t2s) ->
  e_typing s C [::e] (Closed_ft t2s t3s) ->
  e_typing s C (es ++ [::e]) (Closed_ft t1s t3s)
| ety_subtyping : forall s C es t1s t2s t1s' t2s',
  e_typing s C es (Closed_ft t1s t2s) ->
  closed_instr_subtyping s.(s_types) (Closed_ft t1s t2s) (Closed_ft t1s' t2s') ->
  e_typing s C es (Closed_ft t1s' t2s')
| ety_trap : forall s C tf,
  e_typing s C [::AI_trap] tf
| ety_num : forall s C number,
  e_typing s C [::AI_basic (BI_const_num number)]
    (Closed_ft [::] [::CO_value (CV_num (typeof_num number))])
| ety_vec : forall s C vector,
  e_typing s C [::AI_basic (BI_const_vec vector)]
    (Closed_ft [::] [::CO_value (CV_vec T_v128)])
| ety_ref_extern : forall s C a t,
  closed_value_typing s (VAL_ref (VAL_ref_extern a)) (closed_reference_value t) ->
  e_typing s C [::AI_ref_extern a] (Closed_ft [::] [::CO_value (closed_reference_value t)])
| ety_invoke : forall s (a: funcaddr) C tf,
  closed_function_view s a tf ->
  e_typing s C [::AI_invoke a] (lift_closed_function_type tf)
(* The soundness section of the tail call proposal doesn't contain a rule for return_invoke; this typing rule is a placeholder and will be decided later. *)
| ety_return_invoke : forall s (a: funcaddr) C ts1 ts2 ts3 ts4,
  closed_function_view s a (Closed_ft ts1 ts2) ->
  C.(tc_return) = Some (lift_closed_result_type ts2) ->
  e_typing s C [::AI_return_invoke a] (Closed_ft (ts3 ++ lift_closed_result_type ts1) ts4)
| ety_label : forall s C e0s es ts t2s n,
  e_typing s C e0s (Closed_ft ts t2s) ->
  e_typing s (upd_label C ([::ts] ++ tc_labels C)) es (Closed_ft [::] t2s) ->
  length ts = n ->
  e_typing s C [::AI_label n e0s es] (Closed_ft [::] t2s)
| ety_frame : forall s C n f es ts actual_ts,
  thread_typing s (Some actual_ts) (f, es) actual_ts ->
  canonical_registry_validb s.(s_types) ->
  closed_stack_results_subtyping s.(s_types) actual_ts ts ->
  length ts = n ->
  e_typing s C [::AI_frame n f es] (Closed_ft [::] ts)
| ety_ref_i31 : forall s C n t,
  closed_value_typing s (VAL_ref (VAL_ref_i31 n)) (closed_reference_value t) ->
  e_typing s C [::AI_ref_i31 n] (Closed_ft [::] [::CO_value (closed_reference_value t)])
| ety_ref_null : forall s C h t,
  closed_value_typing s (VAL_ref (VAL_ref_null h)) (closed_reference_value t) ->
  e_typing s C [::AI_ref_null h] (Closed_ft [::] [::CO_value (closed_reference_value t)])
| ety_ref : forall s C address t,
  closed_value_typing s (VAL_ref (VAL_ref_func address)) (closed_reference_value t) ->
  e_typing s C [::AI_ref address] (Closed_ft [::] [::CO_value (closed_reference_value t)])

with thread_typing : store_record -> option closed_operand_result_type -> thread -> closed_operand_result_type -> Prop :=
| mk_thread_typing : forall s f es rs ts C C',
  closed_frame_typing s f C ->
  C' = upd_return C rs ->
  e_typing s C' es (Closed_ft nil ts) ->
  thread_typing s rs (f, es) ts
.

Scheme e_typing_ind' := Induction for e_typing Sort Prop
  with thread_typing_ind' := Induction for thread_typing Sort Prop.

Definition funcinst_typing (s: store_record) (fi: funcinst) (tf0: function_type): Prop :=
  cl_type fi = tf0 /\
  match fi with
  | FC_func_native tf inst code =>
      functype_valid tf /\
        match inst_typing s inst with
        | Some C => func_typing C code tf /\
            runtime_default_vals s.(s_types) inst.(inst_defined_types) code.(modfunc_locals) <> None
        | None => False
        end
  | FC_func_host tf hf =>
      functype_valid tf /\
      gc_type_context.canonical_function_identityb s.(s_types) tf = true
  end.

Definition store_typing (s : store_record) : Prop :=
  canonical_registry_validb s.(s_types) = true /\
  match s with
  | Build_store_record fs tabs ms gs es ds types =>
    (List.Forall (fun x => exists t, funcinst_typing s x t) fs) /\
    (List.Forall (fun x => exists t, tableinst_typing s x = Some t) tabs) /\
    (List.Forall (fun x => exists t, meminst_typing s x = Some t) ms) /\
    (List.Forall (fun x => exists t, globalinst_typing s x = Some t) gs) /\
    (List.Forall (fun x => exists t, eleminst_typing s x = Some t) es) /\
    (List.Forall (fun x => exists t, datainst_typing s x = Some t) ds)
  end.

Definition config_typing (s: store_record) (th: thread) (ts: closed_operand_result_type) : Prop :=
  store_typing s /\ thread_typing s None th ts.

End Store_validity.

End Host.
