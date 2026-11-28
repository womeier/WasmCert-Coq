(** Execution of Wast testing script **)

open Execute
open Execute.Host
open Execute.Interpreter
open Output
open Utils

open Wasm.Source
open Wasm.Values
open Wasm.Script

exception Timeout

let with_timeout timeout f =
  let _ =
    Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout))
  in
  ignore (Unix.alarm timeout);
  try
    let r = f () in
    ignore (Unix.alarm 0); r
  with
  | e -> ignore (Unix.alarm 0); raise e

let ovar_to_name default hs ovar = 
  match ovar with
  | Some v -> 
    let (_, varmap) = hs in
    begin match StringMap.find_opt v.it varmap with
    | Some s -> pure s
    | None -> error ("Invalid module variable name: " ^ v.it)
    end
  | None -> pure default

let wasm_num_to_hexstring num = 
  (* This somehow doesn't include the type signature. *)
  let val_string = hex_string_of_num num in
    Wasm.Types.string_of_num_type (type_of_num num) ^ ".const " ^ val_string

let wasm_ref_to_string = function
  | NullRef t -> "ref.null " ^ Wasm.Types.string_of_refed_type t
  | ExternRef n -> "ref.extern " ^ Wasm.I32.to_string_u n
  | _ -> assert false

let wasm_val_to_string wval = 
  match wval.it with
  | Num num -> Some (wasm_num_to_hexstring num)
  | Ref ref -> Some (wasm_ref_to_string ref)
  | Vec _vec -> 
    (* Wasm ref interpreter always prints v128 as I32x4. *)
    let vec_string = "v128.const i32x4 " ^ string_of_value wval.it in
    (* Printf.printf "%s" vec_string; *)
    Some vec_string

let wasm_numpat_to_string numpat =
  match numpat with
  | NumPat num -> wasm_num_to_hexstring num.it
  | NanPat _nanop -> "Nan"

let wasm_refpat_to_string refpat = 
  match refpat with
  | RefPat ref -> string_of_ref ref.it
  | _ -> "Unsupported refpat printout"

let wast_shape_to_coq sh = 
  match sh with
  | Wasm.V128.I8x16 _ -> Extract.VS_i (Extract.VSI_8_16)
  | Wasm.V128.I16x8 _ -> Extract.VS_i (Extract.VSI_16_8)
  | Wasm.V128.I32x4 _ -> Extract.VS_i (Extract.VSI_32_4)
  | Wasm.V128.I64x2 _ -> Extract.VS_i (Extract.VSI_64_2)
  | Wasm.V128.F32x4 _ -> Extract.VS_f (Extract.VSF_32_4)
  | Wasm.V128.F64x2 _ -> Extract.VS_f (Extract.VSF_64_2)

let wasm_vecpat_to_string vecpat = 
  match vecpat with
  | VecPat (V128 (_sh, numpats)) -> "\x1b[36mv128\x1b[0m: [" ^ String.concat "; " (List.map wasm_numpat_to_string numpats) ^ "]"

let wasm_result_to_string ret = 
  match ret.it with
  | NumResult numpat -> wasm_numpat_to_string numpat
  | RefResult refpat -> wasm_refpat_to_string refpat
  | VecResult vecpat -> wasm_vecpat_to_string vecpat

let wasm_results_to_string rets = 
  String.concat "; " (List.map wasm_result_to_string rets)

let wasm_val_to_coq wval = 
  match wasm_val_to_string wval with
  | Some valstr -> Parse.parse_arg valstr
  | None -> None

let rec wasm_vals_to_coq_aux args acc = 
  (match args with
  | [] -> pure acc
  | a :: args' -> 
    (match wasm_val_to_coq a with
    | Some a' -> wasm_vals_to_coq_aux args' (acc @ [a'])
    | None -> Execute.Host.from_out (Error ("Invalid argument in Wast script"))
    )
  )

let wasm_vals_to_coq args = 
  wasm_vals_to_coq_aux args []

let wasm_num_to_coq wnum = 
    wasm_val_to_coq ((Num wnum) @@ no_region)

let wasm_assert_nanpat ret nanop =
  match nanop.it with
  | F32 CanonicalNan -> Interpreter.is_canonical_nan Extract.T_f32 ret
  | F64 CanonicalNan -> Interpreter.is_canonical_nan Extract.T_f64 ret
  | F32 ArithmeticNan -> Interpreter.is_arithmetic_nan Extract.T_f32 ret
  | F64 ArithmeticNan -> Interpreter.is_arithmetic_nan Extract.T_f64 ret
  | _ -> false

let wasm_assert_numpat ret numpat = 
  match numpat with
  | NumPat num -> wasm_num_to_coq num.it = Some ret
  | NanPat nanop -> wasm_assert_nanpat ret nanop

let wasm_assert_refpat ret refpat =
  match refpat with
  | RefPat r -> (wasm_val_to_coq ((Ref r.it) @@ no_region) = Some ret)
  | RefTypePat Wasm.Types.FuncRefType -> Interpreter.is_funcref ret
  | RefTypePat Wasm.Types.ExternRefType -> Interpreter.is_externref ret

let wasm_assert_vecpat verbosity ret vecpat =
  match vecpat, ret with
  | VecPat (V128 (sh, numpats)), Extract.VAL_vec vret -> 
    let coq_sh = wast_shape_to_coq sh in 
    let coq_vals = List.map (fun v -> Extract.VAL_num v) (Interpreter.v128_extract_lanes coq_sh vret) in
    debug_info verbosity intermediate (fun _ -> "The returned v128 extracts to: [" ^ (pp_values coq_vals) ^ "].\n");
    if List.length coq_vals = List.length numpats then 
      List.for_all2 wasm_assert_numpat coq_vals numpats
    else 
      false
  | _, _-> assert false

let wasm_assert_ret verbosity ret ret_exp = 
  match ret_exp.it with
  | NumResult numpat -> wasm_assert_numpat ret numpat
  | RefResult refpat -> wasm_assert_refpat ret refpat
  | VecResult vecpat -> wasm_assert_vecpat verbosity ret vecpat

let wasm_assert_rets verbosity rets ret_exps = 
  let assert_results = List.map2 (fun x y -> wasm_assert_ret verbosity x y) rets ret_exps in
  List.fold_left (fun a b -> a && b) true assert_results

(* Keep parsing separate from validation/linking. A failure in a later phase
   must not satisfy assert_malformed (or a parse failure assert_invalid). *)
let parse_wast_module verbosity moddef =
  try
    match moddef.it with
    | Textual ast_module ->
      Parse.parse_module verbosity false (Wasm.Encode.encode ast_module)
    | Encoded (_, bin_module) ->
      Parse.parse_module verbosity false bin_module
    | Quoted (_, text_module) ->
      Parse.parse_module verbosity true text_module
  with Wasm.Parse_error.Syntax (_, message) -> error message

let require_valid_module m =
  match Extract.module_type_checker m with
  | (Some _, _) -> pure ()
  | (None, _) -> error "Expected a valid module before linking/instantiation"

let instantiate_wast_module verbosity hs s ovar m mod_counter =
  let modname = "default_module_" ^ string_of_int mod_counter in
  let* varname = match ovar with
    | None -> pure None
    | Some v ->
        let (_, varmap) = hs in
        if StringMap.mem v.it varmap then
          error ("Module variable name " ^ v.it ^ " already exists")
        else pure (Some v.it) in
  let* (hs', s', inst_res) = Execute.instantiate_host verbosity hs s modname m in
  let hs' = match varname with
    | None -> hs'
    | Some name ->
        let (exts, varmap) = hs' in
        (exts, StringMap.add name modname varmap) in
  pure (hs', s', inst_res, mod_counter + 1, modname)

let print_wast_command cmd = 
  let cmd_sexpr = Wasm.Arrange.script `Textual [cmd] in
  let cmd_string = String.concat "" (List.map (Wasm.Sexpr.to_string 200) cmd_sexpr) in
  cmd_string

let wasm_name_to_raw_string n = 
  Wasm.Utf8.encode n

let run_invoke verbosity act_invoke hs s default_module_name max_call_depth = 
  match act_invoke with
  | (ovar, funcname_utf8, val_args) ->
    let* modname = ovar_to_name default_module_name hs ovar in
    let funcname = wasm_name_to_raw_string funcname_utf8 in 
    let* args = wasm_vals_to_coq val_args in
    let* res = invoke_func verbosity hs (s, Extract.empty_frame) args modname funcname max_call_depth in 
      debug_info verbosity stage (fun _ -> "Successfully executed function " ^ funcname ^ " of module: " ^ modname ^ ".\n");
      pure res

let run_get act_get hs s default_module_name = 
  match act_get with
  | (ovar, extname_utf8) ->
    let* modname = ovar_to_name default_module_name hs ovar in
    let extname = wasm_name_to_raw_string extname_utf8 in
      global_get hs s modname extname

type verdict_detail = 
  | Verdict_OK
  | Verdict_inst_trap

type binary_definitions = {
  mutable named_definitions : Extract.module0 StringMap.t;
  mutable latest_definition : Extract.module0 option;
}

let remember_definition definitions name m =
  definitions.latest_definition <- Some m;
  match name with
  | None -> ()
  | Some name ->
      definitions.named_definitions <- StringMap.add name m definitions.named_definitions

let finish_instantiation (hs, s, inst_res, counter, name) =
  match inst_res with
  | Cfg_trap _ -> pure (hs, s, counter, name, Verdict_inst_trap)
  | Cfg_res _ -> pure (hs, s, counter, name, Verdict_OK)
  | _ -> error "Post instantiation execution resulted in unexpected error"

let run_wast_command verbosity max_call_depth definitions (directive, cmd) hs s mod_counter default_module_name test_counter =
  debug_info verbosity stage 
  (fun _ -> 
    "\n\n----------\nTest " ^ string_of_int test_counter ^ "\n----------\n" ^ print_wast_command cmd ^ "\n"
    );
 begin try
  begin match directive with
  | Wast_binary_script.Define name ->
      begin match cmd.it with
      | Module (_, ({it = Encoded _; _} as moddef)) ->
          let* m = parse_wast_module verbosity moddef in
          let* () = require_valid_module m in
          remember_definition definitions name m;
          pure (hs, s, mod_counter, default_module_name, Verdict_OK)
      | _ -> error "Expected a binary module definition"
      end
  | Wast_binary_script.Instantiate target ->
      let found = match target with
        | None -> definitions.latest_definition
        | Some name -> StringMap.find_opt name definitions.named_definitions in
      begin match cmd.it, found with
      | Module (ovar, _), Some m ->
          let* result = instantiate_wast_module verbosity hs s ovar m mod_counter in
          finish_instantiation result
      | _, None -> error "Unknown binary module definition"
      | _ -> error "Expected a binary module instance directive"
      end
  | Wast_binary_script.Ordinary ->
  begin match cmd.it with
  | Module (ovar, moddef) -> 
    let* m = parse_wast_module verbosity moddef in
    let* () = require_valid_module m in
    remember_definition definitions (Option.map (fun v -> v.it) ovar) m;
    let* result = instantiate_wast_module verbosity hs s ovar m mod_counter in
    finish_instantiation result
  | Action act ->
    begin match act.it with
    | Invoke (ovar, funcname_utf8, val_args) ->
      let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name max_call_depth in 
      begin match res with
      | Cfg_err -> error "Invocation error"
      | Cfg_trap _ -> error "Unexpected trap"
      | Cfg_res (s', _, _) ->
        pure (hs, s', mod_counter, default_module_name, Verdict_OK)
      | Cfg_exhaustion -> error "Unexpected exhaustion"
      end
    | Get (ovar, extname_utf8) ->
        let* _ = run_get (ovar, extname_utf8) hs s default_module_name in
        debug_info verbosity stage (fun _ -> "Test passed: successfully retrieved the value " ^ wasm_name_to_raw_string extname_utf8);
        pure (hs, s, mod_counter, default_module_name, Verdict_OK)
    end
  | Assertion asrt -> 
    begin match asrt.it with 
    | AssertReturn (act, expect_rets) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name max_call_depth in 
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_exhaustion -> error "Unexpected exhaustion"
        | Cfg_res (s', _, vs) ->
          debug_info verbosity stage (fun _ -> "Returned: ");
          debug_info verbosity stage (fun _ -> Execute.print_invoke_result verbosity res; "");
          debug_info verbosity stage (fun _ -> "Expected: " ^ wasm_results_to_string expect_rets ^ "\n");
          let assert_result = wasm_assert_rets verbosity vs expect_rets in
            if assert_result then
              (debug_info verbosity stage (fun _ -> "Test passed: result matches asserted value\n");
              pure (hs, s', mod_counter, default_module_name, Verdict_OK))
            else 
              error "Result mismatches"
        | Cfg_trap _ -> 
              error "Unexpected trap"
        end
      | Get (ovar, extname_utf8) ->
        let* res_v = run_get (ovar, extname_utf8) hs s default_module_name in
        let assert_result = wasm_assert_rets verbosity [res_v] expect_rets in
          if assert_result then
            (debug_info verbosity stage (fun _ -> "Test passed: result matches asserted value\n");
              pure (hs, s, mod_counter, default_module_name, Verdict_OK))
          else
            error "Result mismatches"
      end
    | AssertTrap (act, _) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name max_call_depth in
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_exhaustion -> error "Unexpected exhaustion when trap is expected"
        | Cfg_res _ ->
          error "Unexpected successful execution when trap is expected"
        | Cfg_trap (s', _) -> 
          debug_info verbosity stage (fun _ -> "Test passed: execution trapped as expected\n");
          pure (hs, s', mod_counter, default_module_name, Verdict_OK)
        end
      | Get (_ovar, _funcname) ->
        error "Unsupported wast action: Get"
      end
    | AssertExhaustion (act, _) ->
      begin match act.it with
      | Invoke (ovar, funcname_utf8, val_args) ->
        let* res = run_invoke verbosity (ovar, funcname_utf8, val_args) hs s default_module_name max_call_depth in
        begin match res with
        | Cfg_err -> error "Invocation error"
        | Cfg_res _ ->
          error "Unexpected successful execution when exhaustion is expected"
        | Cfg_trap _ -> 
          error "Unexpected trap when exhaustion is expected"
        | Cfg_exhaustion ->
          debug_info verbosity stage (fun _ -> "Test passed: correctly exhausted\n");
          pure (hs, s, mod_counter, default_module_name, Verdict_OK)
        end
      | Get (_ovar, _funcname) ->
        error "Unsupported wast action: Get"
      end
    | AssertInvalid (moddef, _str) ->
      let* m = parse_wast_module verbosity moddef in
      begin match Extract.module_type_checker m with
      | (Some _, _) ->
        error "Unexpected successful validation of an invalid module"
      | (None, _) ->
        debug_info verbosity stage (fun _ -> "Test passed: correctly rejected an invalid module\n");
        pure (hs, s, mod_counter, default_module_name, Verdict_OK)
      end
    | AssertMalformed (moddef, _str) ->
      begin match to_out (parse_wast_module verbosity moddef) with
      | OK _ ->
        error "Unexpected successful parsing of a malformed module"
      | Error _ ->
        debug_info verbosity stage (fun _ -> "Test passed: correctly rejected a malformed module\n");
        pure (hs, s, mod_counter, default_module_name, Verdict_OK)
      end
    | AssertUnlinkable (moddef, _str) ->
      let* m = parse_wast_module verbosity moddef in
      let* () = require_valid_module m in
      begin match to_out (Execute.instantiate verbosity hs s m) with
      | Error _ ->
        debug_info verbosity stage (fun _ -> "Test passed: correctly rejected an unlinkable module\n");
        pure (hs, s, mod_counter, default_module_name, Verdict_OK)
      | OK _ -> error "Unexpected successful linking of an unlinkable module"
      end
    | AssertUninstantiable (moddef, _str) ->
      let* m = parse_wast_module verbosity moddef in
      let* () = require_valid_module m in
      let* res = Execute.instantiate verbosity hs s m in
      begin match res with
      | Cfg_trap (s', _) ->
        debug_info verbosity stage (fun _ -> "Test passed: instantiation trapped as expected\n");
        pure (hs, s', mod_counter, default_module_name, Verdict_OK)
      | _ -> error "Expected an instantiation trap"
      end
    end
  | Register (newname_utf8, ovar) ->
    let newname = wasm_name_to_raw_string newname_utf8 in
    let (exts, varmap) = hs in
    (* Updating the varmap, if a varname is specified. Also retrieving the module name in the export store to be updated later *)
    let* (oldname, varmap') = begin match ovar with
    | Some v -> 
      let varname = v.it in
      begin match StringMap.find_opt varname varmap with
      | Some oldname ->
        (* Updating the module varmap *)
        pure (oldname, StringMap.add varname newname varmap)
      | None -> error ("Nonexistent module variable " ^ varname ^ " to be registered")
      end
    | None -> 
      (* No varname is specified; registering the default module. The varmap does not need to be updated *)
      pure (default_module_name, varmap)
    end in
    (* Updating the module exports map *)
    let exts' = begin match StringMap.find_opt oldname exts with 
    | Some modmap -> exts |> StringMap.remove oldname |> StringMap.add newname modmap
    | None -> 
      (* This must mean that whatever module being registered has no export, so the registration is technically redundant. *)
      debug_info verbosity intermediate (fun _ -> "Warning: potential redundant registration since no export is found\n");
      exts
    end in
      debug_info verbosity stage (fun _ -> "Test passed: successfully registered module previously named " ^ oldname ^ " with new name: " ^ newname ^ "\n");
      pure ((exts', varmap'), s, mod_counter, newname, Verdict_OK)
  | _ -> error "Unsupported wast command"
  end
  end
  with 
  | _ -> error "Unknown exception"
end

let rec run_wast_commands verbosity timeout max_call_depth definitions cmds hs s mod_counter default_module_name assert_ok assert_total =
  match cmds with
  | [] -> 
    pure (assert_ok, assert_total)
  | cmd :: cmds' ->
      let verdict = 
        try
          (with_timeout timeout (fun _ -> run_wast_command verbosity max_call_depth definitions cmd hs s mod_counter default_module_name (assert_total+1))) with
          | Timeout -> error "Execution exceeded time limit"
         in
        begin match to_out verdict with
        | OK eve -> 
          let* (hs', s', mod_counter', default_module_name', vd) = eve in
          begin match vd with
          | Verdict_OK ->
            let new_ok = assert_ok + 1 in
            let new_total = assert_total + 1 in
              Printf.printf "\rTests passed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
              flush stdout;
              run_wast_commands verbosity timeout max_call_depth definitions cmds' hs' s' mod_counter' default_module_name' new_ok new_total
          | Verdict_inst_trap ->
            let new_ok = assert_ok in
            let new_total = assert_total + 1 in
              debug_info verbosity stage (fun _ -> "Successfully loaded module, but post-instantiation initialisation trapped\n");
              Printf.printf "\rTests failed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
              flush stdout;
              run_wast_commands verbosity timeout max_call_depth definitions cmds' hs' s' mod_counter' default_module_name' new_ok new_total
          end
        | Error msg ->
            debug_info verbosity stage ~style:red (fun _ -> "Test failed: " ^ msg ^ "\n");
            let new_ok = assert_ok in
            let new_total = assert_total + 1 in
            Printf.printf "\rTests passed: %d/%d (%.2f%%) " new_ok new_total (float_of_int new_ok *. 100.0 /. float_of_int new_total);
            flush stdout;
            run_wast_commands verbosity timeout max_call_depth definitions cmds' hs s mod_counter default_module_name new_ok new_total
          end

(* SpecTest host module for Wast test suite *)
let spectest_host_str = 
  "(module
  (global (export \"global_i32\") i32 (i32.const 666))      ;; value 666
  (global (export \"global_i64\") i64 (i64.const 666))      ;; value 666
  (global (export \"global_f32\") f32 (f32.const 666.6))      ;; value 666.6
  (global (export \"global_f64\") f64 (f64.const 666.6))      ;; value 666.6

  (table (export \"table\") 10 20 funcref)  ;; null-initialized

  (memory (export \"memory\") 1 2)          ;; zero-initialized

  (func (export \"print\"))
  (func (export \"print_i32\") (param i32))
  (func (export \"print_i64\") (param i64))
  (func (export \"print_f32\") (param f32))
  (func (export \"print_f64\") (param f64))
  (func (export \"print_i32_f32\") (param i32 f32))
  (func (export \"print_f64_f64\") (param f64 f64))
)"

let register_spectest_host verbosity hs s = 
  let* m = Parse.parse_module verbosity true spectest_host_str in
  (* Add the Wasm 3.0 host table in the core AST: the deferred text module
     frontend is neither extended nor asked to understand an i64 table. *)
  let table64 = Extract.{
    tt_limits = {lim_min = Big_int_Z.big_int_of_int 10;
                 lim_max = Some (Big_int_Z.big_int_of_int 20)};
    tt_elem_type = T_funcref; tt_address_type = Addressing.AT_i64 } in
  let table64_name = List.init 7 (String.get "table64") in
  let table64_index = Big_int_Z.big_int_of_int (List.length m.Extract.mod_tables) in
  let m = Extract.{ m with
    mod_tables = m.mod_tables @ [table64];
    mod_exports = m.mod_exports @
      [{modexp_name = table64_name; modexp_desc = MED_table table64_index}] } in
  let modname = "spectest" in
  let* (hs', s') = Execute.instantiate_modules verbosity hs s [modname] [m] in
    debug_info verbosity stage (fun _ -> "Successfully instantiated module " ^ modname ^ ".\n");
    pure (hs', s')

let run_wast_script verbosity timeout max_call_depth script =
  let starting_host_store = (StringMap.empty, StringMap.empty) in
  let starting_store = empty_store_record in
  let* (hs, s) = register_spectest_host verbosity starting_host_store starting_store in
  let definitions = {named_definitions = StringMap.empty; latest_definition = None} in
  let* ret = run_wast_commands verbosity timeout max_call_depth definitions script hs s 0 "" 0 0 in
  match ret with
    | (assert_ok, assert_total) -> 
      debug_info verbosity result (fun _ -> "\n");
      let color = if (assert_ok = assert_total) then Output.green else Output.red in
        debug_info verbosity result ~style:color (fun _ -> Printf.sprintf "Result: %d/%d (%.2f%%)\n" assert_ok assert_total (float_of_int assert_ok *. 100.0 /. float_of_int assert_total));
      pure ()
    

let run_wast_string verbosity timeout max_call_depth scriptstr = 
  let script = Parse.parse_wast_dispatch scriptstr in
  run_wast_script verbosity timeout max_call_depth script
