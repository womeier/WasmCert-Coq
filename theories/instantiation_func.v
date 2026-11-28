(** Executable instantiation **)

From Stdlib Require Import ZArith String List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Export opsem interpreter_ctx instantiation_spec.
From Wasm Require Import gc_declaration_typing.

(* see common.v *)
Set SsrOldRewriteGoalsOrder.

Open Scope string_scope.
Open Scope seq_scope.

Section Instantiation_func.

Context `{ho: host}.
  
Definition gather_m_f_type (tfs : type_context) (m_f : module_func) : option function_type :=
  lookup_function_type tfs m_f.(modfunc_type).

Definition gather_m_f_types (tfs : type_context) (m_fs : list module_func) : option (list function_type) :=
  those (map (gather_m_f_type tfs) m_fs).

Definition module_import_desc_typer (tfs: type_context) (imp_desc : module_import_desc) : option extern_type :=
  match imp_desc with
  | MID_func i => option_map ET_func (lookup_function_type tfs i)
  | MID_table t_t =>
    if tabletype_valid t_t then Some (ET_table t_t) else None
  | MID_mem mt =>
    if memtype_valid mt then Some (ET_mem mt) else None
  | MID_global gt => Some (ET_global gt)
  end.

(* breaking circularity, therefore only taking the function types *)
Definition module_imports_typer (tfs: type_context) (imps : list module_import) : option (list extern_type) :=
  those (map (fun imp => module_import_desc_typer tfs imp.(imp_desc)) imps).

(* prepass *)
Definition gather_m_e_type (tts: list table_type) (el: module_element): option reference_type :=
  match el.(modelem_mode) with
  | ME_passive => Some el.(modelem_type)
  | ME_active x offset =>
      match option_map tt_elem_type (lookup_N tts x) with
      | Some tref =>
          if tref == el.(modelem_type)
          then Some tref
          else None
      | None => None
      end
  | ME_declarative => Some el.(modelem_type)
  end.

Definition gather_m_e_types (tts: list table_type) (els: list module_element) : option (list reference_type) :=
  those (map (fun elem => gather_m_e_type tts elem) els).

Definition gather_m_d_type (mts: list memory_type) (dmode: module_datamode) : option ok :=
  match dmode with
  | MD_passive => Some tt
  | MD_active x offset => option_map (fun _ => tt) (lookup_N mts x)
  end.

Definition gather_m_d_types (mts: list memory_type) (els: list module_data) : option (list ok) :=
  those (map (fun data => gather_m_d_type mts data.(moddata_mode)) els).

Definition module_export_typer (C : t_context) (exp : module_export_desc) : option extern_type :=
  match exp with
  | MED_func i => option_map ET_func (lookup_N C.(tc_funcs) i)
  | MED_table i => option_map ET_table (lookup_N C.(tc_tables) i)
  | MED_mem i => option_map ET_mem (lookup_N C.(tc_mems) i)
  | MED_global i => option_map ET_global (lookup_N C.(tc_globals) i)
  end.

Definition module_exports_typer (c : t_context) exps :=
  those (map (fun exp => module_export_typer c exp.(modexp_desc)) exps).

Definition gather_m_g_types (mgs : list module_global) : list global_type :=
  map (fun mg => mg.(modglob_type)) mgs.

Definition module_func_type_checker (c : t_context) (m : module_func) : bool :=
  let '{| modfunc_type := i; modfunc_locals := t_locs; modfunc_body := b_es |} := m in
  match lookup_function_type c.(tc_types) i with
  | None => false
  | Some (Tf tn tm) =>
    let c' := {|
      tc_types := c.(tc_types);
      tc_funcs := c.(tc_funcs);
      tc_globals := c.(tc_globals);
      tc_tables := c.(tc_tables);
      tc_mems := c.(tc_mems);
      tc_elems := c.(tc_elems);
      tc_datas := c.(tc_datas);
      tc_locals := List.app c.(tc_locals) (List.app tn t_locs);
      tc_labels := tm :: c.(tc_labels);
      tc_return := Some tm;
      tc_refs := c.(tc_refs)
    |} in
    type_checker.b_e_type_checker c' b_es (Tf [::] tm) && (default_vals t_locs != None)
  end.

Definition module_table_type_checker (C: t_context) mt := tabletype_valid mt.(modtab_type).

Definition module_mem_type_checker (C: t_context) mm := memtype_valid mm.(modmem_type).

Definition module_global_type_checker (c : t_context) (mg : module_global) : bool :=
  let '{| modglob_type := tg; modglob_init := es |} := mg in
  const_exprs c es &&
  type_checker.b_e_type_checker c es (Tf nil [::tg.(tg_t)]).

Definition extended_global_type_checker (c : t_context) (g : module_global) : bool :=
  extended_const_exprs c g.(modglob_init) &&
  type_checker.b_e_type_checker c g.(modglob_init) (Tf nil [::g.(modglob_type).(tg_t)]).

Fixpoint extended_globals_type_checker (c : t_context) (gs : list module_global) : bool :=
  match gs with
  | nil => true
  | g :: gs' =>
      extended_global_type_checker c g &&
      extended_globals_type_checker (const_context_add_global c g.(modglob_type)) gs'
  end.

Definition module_elem_mode_checker (c: t_context) (emode: module_elemmode) (reftype: reference_type) : bool :=
  match emode with
  | ME_passive => true
  | ME_active x offset =>
      match lookup_N c.(tc_tables) x with
      | Some tab =>
          (tab.(tt_elem_type) == reftype) &&
          type_checker.b_e_type_checker c offset (Tf nil [::T_num T_i32]) &&
            const_exprs c offset
      | None => false
      end
  | ME_declarative => true
  end.

Definition module_elem_type_checker (c : t_context) (e : module_element) : bool :=
  let '{| modelem_type := t; modelem_init := e_inits; modelem_mode := emode |} := e in
  all (const_exprs c) e_inits &&
  all (fun es => type_checker.b_e_type_checker c es (Tf nil [::T_ref t])) e_inits &&
  module_elem_mode_checker c emode t.  

Definition module_data_mode_checker (C: t_context) (dmode: module_datamode): bool :=
  match dmode with
  | MD_passive => true
  | MD_active x offset =>
      match lookup_N C.(tc_mems) x with
      | Some _ =>
          (type_checker.b_e_type_checker C offset (Tf nil [::T_num T_i32])) &&
            const_exprs C offset
      | None => false
      end
  end.

Definition module_data_type_checker (c : t_context) (d : module_data) : bool :=
  let '{| moddata_init := bs; moddata_mode := dmode |} := d in
  module_data_mode_checker c dmode.

Definition module_start_type_checker (c : t_context) (ms : module_start) : bool :=
  module_start_typing c ms.

Definition module_components_type_checker (m : module) : option ((list extern_type) * (list extern_type)) * string :=
  let '{|
    mod_types := groups;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elems := els;
    mod_datas := ds;
    mod_start := i_opt;
    mod_imports := imps;
    mod_exports := exps;
  |} := m in
  let tfs := List.concat groups in
  match (gather_m_f_types tfs fs, module_imports_typer tfs imps) with
  | (Some fts, Some impts) =>
    let ifts := ext_t_funcs impts in
    let its := ext_t_tables impts in
    let ims := ext_t_mems impts in
    let igs := ext_t_globals impts in
    let gts := gather_m_g_types gs in
    let tts := its ++ (map modtab_type ts) in
    let mts := ims ++ (map modmem_type ms) in
    match (gather_m_e_types tts els, gather_m_d_types mts ds) with
    | (Some rts, Some dts) =>
    let xs := module_filter_funcidx m in
    let c := {|
      tc_types := tfs;
      tc_funcs := ifts ++ fts;
      tc_globals := igs ++ gts;
      tc_tables := tts;
      tc_mems := mts;
      tc_elems := rts;
      tc_datas := dts;
      tc_locals := nil;
      tc_labels := nil;
      tc_return := None;
      tc_refs := xs
            |} in
    let c' := {|
      tc_types := nil;
      tc_funcs := c.(tc_funcs);
      tc_globals := igs;
      tc_tables := c.(tc_tables);
      tc_mems := c.(tc_mems);
      tc_elems := nil;
      tc_datas := nil;
      tc_locals := nil;
      tc_labels := nil;
      tc_return := None;
      tc_refs := c.(tc_refs)
    |} in
    if seq.all (module_func_type_checker c) fs &&
       seq.all (module_table_type_checker c) ts &&
       seq.all (module_mem_type_checker c) ms &&
       wasm_2_memory_count_check ms ims &&  
        extended_globals_type_checker c' gs &&
        seq.all (module_elem_type_checker (const_context_add_globals c' gts)) els &&
        seq.all (module_data_type_checker (const_context_add_globals c' gts)) ds &&
       pred_option (module_start_type_checker c) i_opt &&
       export_name_unique exps
      then
       match module_exports_typer c exps with
       | Some expts => (Some (impts, expts), "ok")
       | None => (None, "invalid module export type")
       end
    else (None, "invalid module components")
    | _ => (None, "invalid module elem or data types")
    end
  | (Some _, None) | (None, Some _) | (None, None) => (None, "invalid module function or import references")
  end.

Definition module_type_checker (m : module) : option ((list extern_type) * (list extern_type)) * string :=
  match close_and_validate_type_groups nil (module_type_groups m) with
  | Some (registry, ids) =>
      if source_type_identitiesb registry ids (List.concat m.(mod_types)) ids
      then module_components_type_checker m
      else (None, "inconsistent closed module type signatures")
  | None => (None, "invalid module type declarations")
  end.

Definition external_type_checker (s : store_record) (v : extern_value): option extern_type :=
  ext_typing s v.

(* Stack head is the most recently produced value.  Unlike the full interpreter,
   this evaluator needs no fuel: every recursive call consumes an instruction. *)
Definition interp_const_step (s : store_record) (f : frame)
    (e : basic_instruction) (vs : list value) : option (list value) :=
      match e with
      | BI_const_num v => Some (VAL_num v :: vs)
      | BI_const_vec v => Some (VAL_vec v :: vs)
      | BI_ref_null t => Some (VAL_ref (VAL_ref_null t) :: vs)
      | BI_ref_func i =>
          match lookup_N f.(f_inst).(inst_funcs) i with
          | Some addr => Some (VAL_ref (VAL_ref_func addr) :: vs)
          | None => None
          end
      | BI_global_get i =>
          match sglob_val s f.(f_inst) i with
          | Some v => Some (v :: vs)
          | None => None
          end
      | BI_ref_i31 =>
          match vs with
          | VAL_num (VAL_int32 n) :: vs' =>
              Some (VAL_ref (VAL_ref_i31 (i31bits_of_i32 n)) :: vs')
          | _ => None
          end
      | BI_binop t op =>
          if const_binop t op then
            match vs with
            | VAL_num v2 :: VAL_num v1 :: vs' =>
                if binop_typecheck v1 v2 t op then
                  match app_binop op v1 v2 with
                  | Some v => Some (VAL_num v :: vs')
                  | None => None
                  end
                else None
            | _ => None
            end
          else None
      | _ => None
      end.

Fixpoint interp_const_stack (s : store_record) (f : frame)
    (es : list basic_instruction) (vs : list value) : option (list value) :=
  match es with
  | nil => Some vs
  | e :: es' =>
      match interp_const_step s f e vs with
      | Some vs' => interp_const_stack s f es' vs'
      | None => None
      end
  end.

(* Auxiliary definition for evaluating constant expressions, instead of using
   the full interpreter.  A complete initializer must produce exactly one value. *)
Definition interp_get_const (s : store_record) (f : frame) (b_es : list basic_instruction) : option value :=
  match b_es with
  | [::BI_const_num v] => Some (VAL_num v)
  | [::BI_const_vec v] => Some (VAL_vec v)
  | [::BI_ref_null t] => Some (VAL_ref (VAL_ref_null t))
  | [::BI_ref_func i] =>
      match lookup_N f.(f_inst).(inst_funcs) i with
      | Some addr => Some (VAL_ref (VAL_ref_func addr))
      | None => None
      end
  | [::BI_global_get i] => sglob_val s f.(f_inst) i
  | _ =>
      match interp_const_stack s f b_es nil with
      | Some [::v] => Some v
      | _ => None
      end
  end.

Definition interp_get_vref (s : store_record) (f: frame) (b_es : list basic_instruction) : option value_ref :=
  match interp_get_const s f b_es with
  | Some (VAL_ref vref) => Some vref
  | _ => None
  end.

Definition interp_get_i32 (s : store_record) (f: frame) (b_es : list basic_instruction) : option i32 :=
  match interp_get_const s f b_es with
  | Some (VAL_num (VAL_int32 c)) => Some c
  | _ => None
  end.

Definition get_global_inits (s: store_record) (f: frame) (gs: list module_global) : option (list value):=
  those (map (fun g => interp_get_const s f g.(modglob_init)) gs).

Fixpoint interp_global_chain (s : store_record) (f : frame) (gs : list module_global)
    : option (store_record * frame * list value) :=
  match gs with
  | nil => Some (s, f, nil)
  | g :: gs' =>
      match interp_get_const s f g.(modglob_init) with
      | None => None
      | Some v =>
          let '(s1, addr) := alloc_glob s (g, v) in
          match interp_global_chain s1 (const_frame_add_global f addr) gs' with
          | None => None
          | Some (s2, f2, vs) => Some (s2, f2, v :: vs)
          end
      end
  end.

Definition get_elem_inits (s: store_record) (f: frame) (els: list module_element) : option (list (list value_ref)):=
  those (map (fun el => those (map (fun e => interp_get_vref s f e) el.(modelem_init))) els).

Definition interp_alloc_module (s : store_record) (m : module) (imps : list extern_value) (gvs : list value) (rvs: list (list value_ref))
    (registry : canonical_registry) (typeids : list defined_type) : (store_record * moduleinst) :=
  let i_fs := iota_N (length s.(s_funcs)) (length m.(mod_funcs)) in
  let i_ts := iota_N (length s.(s_tables)) (length m.(mod_tables)) in
  let i_ms := iota_N (length s.(s_mems)) (length m.(mod_mems)) in
  let i_gs := iota_N (length s.(s_globals)) (length m.(mod_globals)) in
  let i_es := iota_N (length s.(s_elems)) (length m.(mod_elems)) in
  let i_ds := iota_N (length s.(s_datas)) (length m.(mod_datas)) in
  let inst := {|
    inst_defined_types := typeids;
    inst_types := List.concat m.(mod_types);
    inst_funcs := (ext_funcs imps ++ i_fs);
    inst_tables := (ext_tables imps ++ i_ts);
    inst_mems := (ext_mems imps ++ i_ms);
    inst_globals := (ext_globals imps ++ i_gs);
    inst_elems := (i_es);
    inst_datas := (i_ds);
    inst_exports := (map (get_exportinst (Build_moduleinst nil (ext_funcs imps ++ i_fs) (ext_tables imps ++ i_ts) (ext_mems imps ++ i_ms) (ext_globals imps ++ i_gs) nil nil nil nil)) m.(mod_exports))
  |} in
  let '(s1, _) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, _) := alloc_tabs s1 (map modtab_type m.(mod_tables)) in
  let '(s3, _) := alloc_mems s2 (map modmem_type m.(mod_mems)) in
  let '(s4, i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  let '(s5, i_es) := alloc_elems s4 m.(mod_elems) rvs in
  let '(s', i_ds) := alloc_datas s5 m.(mod_datas) in
  (upd_s_types s' registry, inst).

Definition module_init_frame (s : store_record) (m : module) (v_imps : list extern_value) : frame :=
  Build_frame nil
    (Build_moduleinst nil
      (ext_funcs v_imps ++ iota_N (length s.(s_funcs)) (length m.(mod_funcs)))
      nil nil (ext_globals v_imps) nil nil nil nil).

(* Use a monad for error reporting at some point? *)
Definition interp_instantiate (hs: host_state) (s : store_record) (m : module) (v_imps : list extern_value) : option (host_state * store_record * frame * list basic_instruction) * string :=
  match module_type_checker m with
  | (None, str) => (None, ("Module type checking failure:" ++ str)%string)
  | (Some (t_imps_mod, t_exps), _) =>
      match close_and_validate_type_groups s.(s_types) (module_type_groups m) with
      | None => (None, "Error in closing module types against store registry")
      | Some (registry, typeids) =>
      if source_type_identitiesb registry typeids (List.concat m.(mod_types)) typeids then
      match those (map (external_type_checker s) v_imps) with
      | Some t_imps =>
          if all2 import_subtyping t_imps t_imps_mod then
            let f_init := module_init_frame s m v_imps in
            match interp_global_chain s f_init m.(mod_globals) with
            | None => (None, "Error in evaluating global initialisers")
            | Some (s_init, f_init_final, g_inits) =>
                match get_elem_inits s_init f_init_final m.(mod_elems) with
                | Some r_inits =>
                     let '(s', inst_final) := interp_alloc_module s m v_imps g_inits r_inits registry typeids in
                    let f_final := Build_frame nil inst_final in
                    (Some (hs, s', f_final, get_init_expr_elems m.(mod_elems) ++ get_init_expr_datas m.(mod_datas) ++ get_init_expr_start m.(mod_start)), "")
                | None => (None, "Error in evaluating elem initialisers")
                end
            end
          else (None, "Import type checking failure")
      | None => (None, "Bad external values for imports")
      end
      else (None, "Error in resolving closed module signatures")
      end
  end.

End Instantiation_func.
