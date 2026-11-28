(* Binary-script test driver. wasm-tools owns text encoding; all module parsing,
   validation, linking and evaluation below use the actual extracted runtime.
   Unsupported commands fail; no assertion stage or exception is conflated. *)
open Yojson.Basic.Util
open Execute
module I = Execute.Interpreter
module M = Utils.StringMap
module Big = Z

let field name json = member name json |> to_string
let optional name json =
  match member name json with `Null -> None | value -> Some (to_string value)
let fail stage message = failwith (stage ^ ": " ^ message)
let require stage message = function Some x -> x | None -> fail stage message
let read_binary path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let numeric json =
  let bits () = Z.of_string (field "value" json) in
  match field "type" json with
  | "i32" -> Extract.Utility.vali32_of_Z (bits ())
  | "i64" -> Extract.Utility.vali64_of_Z (bits ())
  | "f32" -> Extract.VAL_num (Extract.VAL_float32 (Extract.b32_of_bits (bits ())))
  | "f64" -> Extract.VAL_num (Extract.VAL_float64 (Extract.b64_of_bits (bits ())))
  | kind -> fail "argument" ("unsupported value type " ^ kind)

let value json =
  let open Extract in
  match field "type" json, field "value" json with
  | "exnref", "null" -> VAL_ref (VAL_ref_null HT_exn)
  | "externref", "null" -> VAL_ref (VAL_ref_null HT_extern)
  | "funcref", "null" -> VAL_ref (VAL_ref_null HT_func)
  | "externref", n -> VAL_ref (VAL_ref_extern (Big.of_string n))
  | _ -> numeric json

let matches actual expected =
  let open Extract in
  match field "type" expected, field "value" expected, actual with
  | "f32", "nan:canonical", _ -> I.is_canonical_nan T_f32 actual
  | "f32", "nan:arithmetic", _ -> I.is_arithmetic_nan T_f32 actual
  | "f64", "nan:canonical", _ -> I.is_canonical_nan T_f64 actual
  | "f64", "nan:arithmetic", _ -> I.is_arithmetic_nan T_f64 actual
  | "f32", bits, VAL_num (VAL_float32 f) ->
      Big.equal (bits_of_b32 f) (Big.of_string bits)
  | "f64", bits, VAL_num (VAL_float64 f) ->
      Big.equal (bits_of_b64 f) (Big.of_string bits)
  | "exnref", "null", VAL_ref (VAL_ref_null (HT_exn | HT_noexn)) -> true
  | "externref", "null", VAL_ref (VAL_ref_null (HT_extern | HT_noextern)) -> true
  | "funcref", "null", VAL_ref (VAL_ref_null (HT_func | HT_nofunc)) -> true
  | _, _, _ -> actual = value expected

let run projection =
  let document = Yojson.Basic.from_file projection in
  let source = field "source" document in
  let commands = member "commands" document |> to_list in
  let directory = Filename.dirname projection in
  let proceed (hs, initial_store) =
  let host = ref hs and store = ref initial_store in
  let bindings = ref M.empty and default = ref None in
  let diagnostics = ref [] in
  let at values index =
    if Z.fits_int index then List.nth_opt values (Z.to_int index) else None
  in
  let id_json id = `List [`String (Z.to_string id.Extract.defined_group);
                         `String (Z.to_string id.Extract.defined_member)] in
  let tag_diagnostics m =
    match Extract.close_and_validate_type_groups (!store).Extract.s_types m.Extract.mod_types with
    | None -> []
    | Some (registry, names) ->
        List.filter_map (fun imp ->
          match imp.Extract.imp_desc with
          | Extract.MID_tag index ->
              let raw name = String.of_seq (List.to_seq name) in
              let supplied = Execute.get_ext_import !host
                (raw imp.Extract.imp_module, raw imp.Extract.imp_name) in
              let actual = match supplied with
                | Some (Extract.EV_tag address) -> at (!store).Extract.s_tag_ids address
                | _ -> None in
              let expected = at names index in
              let equivalent = match actual, expected with
                | Some a, Some e -> Extract.defined_type_equiv registry a e
                | _ -> false in
              let portable = match supplied,
                Extract.module_import_desc_typer (List.concat m.Extract.mod_types) imp.Extract.imp_desc with
                | Some (Extract.EV_tag address), Some (Extract.ET_tag expected_ps) ->
                    (match at (!store).Extract.s_tags address with
                     | Some actual_ps -> Extract.portable_tag_parameters actual_ps expected_ps
                     | None -> false)
                | _ -> false in
              Some (`Assoc [
                "source_type_index", `String (Z.to_string index);
                "actual_id", (match actual with None -> `Null | Some id -> id_json id);
                "expected_id", (match expected with None -> `Null | Some id -> id_json id);
                "canonical_equivalent", `Bool equivalent;
                "portable_payloads", `Bool portable])
          | _ -> None) m.Extract.mod_imports
  in
  let resolve_module json key =
    match optional key json with
    | Some name -> require "action" ("unknown module " ^ name) (M.find_opt name !bindings)
    | None -> require "action" "no default module" !default
  in
  let exported module_name name =
    let exports, _ = !host in
    let exports = require "action" ("unknown instance " ^ module_name)
      (M.find_opt module_name exports) in
    require "action" ("unknown export " ^ name) (M.find_opt name exports)
  in
  let parse command =
    (match optional "module_type" command with
     | None | Some "binary" -> ()
     | Some kind -> fail "projection" ("not a binary module: " ^ kind));
    let path = Filename.concat directory (field "filename" command) in
    let parsed = I.run_parse_module_str (read_binary path) in
    (match parsed with Some m -> diagnostics := tag_diagnostics m | None -> ());
    parsed
  in
  let validate m =
    match Extract.module_type_checker m with
    | None, message -> fail "validation" message
    | Some _, _ -> ()
  in
  let imports m =
    List.map (fun path ->
      require "imports" "unknown import" (Execute.get_ext_import !host path))
      (I.get_import_path m)
  in
  let instantiate m =
    let imps = imports m in
    match I.interp_instantiate_wrapper !store m imps with
    | None, message -> fail "instantiation" message
    | Some cfg, _ -> Execute.eval_wasm_cfg Output.none 1000 cfg
  in
  let update_store = function
    | Cfg_res (s, _, _) | Cfg_trap (s, _) | Cfg_exception (s, _, _) -> store := s
    | Cfg_err | Cfg_exhaustion -> ()
  in
  let action command =
    let module_name = resolve_module command "module" in
    let ext = exported module_name (field "field" command) in
    match field "type" command with
    | "get" ->
        let v = require "action" "not a global" (I.wasm_global_get !store ext) in
        Cfg_res (!store, Extract.empty_frame, [v])
    | "invoke" ->
        let args = member "args" command |> to_list |> List.map value in
        let es = require "action" "not a function or invalid arguments"
          (I.invoke_extern !store ext args) in
        let result = Execute.eval_wasm_cfg Output.none 1000
          (!store, (Extract.empty_frame, es)) in
        update_store result;
        result
    | kind -> fail "action" ("unsupported action " ^ kind)
  in
  let describe = function
    | Cfg_res _ -> "return" | Cfg_trap _ -> "trap"
    | Cfg_exception _ -> "exception" | Cfg_err -> "invalid runtime configuration"
    | Cfg_exhaustion -> "exhaustion"
  in
  let execute ordinal command =
    match field "type" command with
    | "module" ->
        let m = require "parse" "module rejected" (parse command) in
        validate m;
        let result = instantiate m in
        update_store result;
        (match result with
         | Cfg_res (_, frame, _) ->
             let id = "eh_module_" ^ string_of_int ordinal in
             let exports = I.get_exports frame |> List.to_seq |> M.of_seq in
             let old_exports, variables = !host in
             host := M.add id exports old_exports, variables;
             default := Some id;
             (match optional "name" command with
              | None -> () | Some name -> bindings := M.add name id !bindings)
         | _ -> fail "module" ("unexpected " ^ describe result))
    | "register" ->
        let id = resolve_module command "name" in
        let exports, variables = !host in
        let instance = require "register" "missing instance" (M.find_opt id exports) in
        (* Registration adds an alias; it neither deletes the original binding
           nor changes the default instance. *)
        host := M.add (field "as" command) instance exports, variables
    | "assert_malformed" ->
        (match parse command with None -> ()
         | Some _ -> fail "parse" "malformed module unexpectedly parsed")
    | "assert_invalid" ->
        let m = require "parse" "invalid assertion failed before validation" (parse command) in
        (match Extract.module_type_checker m with
         | None, _ -> () | Some _, _ -> fail "validation" "invalid module accepted")
    | "assert_unlinkable" ->
        let m = require "parse" "unlinkable assertion failed before validation" (parse command) in
        validate m;
        let paths = I.get_import_path m in
        let imps = List.map (Execute.get_ext_import !host) paths in
        if List.exists Option.is_none imps then ()
        else
          (match I.interp_instantiate_wrapper !store m (List.map Option.get imps) with
           | None, "Import type checking failure" -> ()
           | None, message -> fail "instantiation" ("not import matching: " ^ message)
           | Some _, _ -> fail "imports" "unlinkable module linked")
    | "assert_return" | "assert_trap" | "assert_exception" | "assert_exhaustion" as kind ->
        let result = action (member "action" command) in
        (match kind, result with
         | "assert_return", Cfg_res (_, _, values) ->
             let expected = member "expected" command |> to_list in
             if List.length values <> List.length expected ||
                not (List.for_all2 matches values expected)
             then fail "result" "return values mismatch"
         | "assert_trap", Cfg_trap _ | "assert_exception", Cfg_exception _
         | "assert_exhaustion", Cfg_exhaustion -> ()
         | _ -> fail "outcome" (kind ^ " got " ^ describe result))
    | "action" ->
        let result = action (member "action" command) in
        (match result with Cfg_res _ -> () | _ -> fail "action" (describe result))
    | kind -> fail "command" ("unsupported command " ^ kind)
  in
  let passed = ref 0 in
  let results = List.mapi (fun i command ->
    diagnostics := [];
    let provenance = member "provenance" command in
    let ordinal = match member "ordinal" provenance with
      | `Int n -> n | _ -> i + 1 in
    let ok, message =
      try Wast_execute.with_timeout 10 (fun () -> execute ordinal command);
        incr passed; true, ""
      with exception_ -> false, Printexc.to_string exception_
    in
    `Assoc ["provenance", provenance; "type", member "type" command;
      "passed", `Bool ok; "error", `String message;
      "tag_import_diagnostics", `List !diagnostics]
  ) commands in
  let report = `Assoc ["source", `String source; "passed", `Int !passed;
    "total", `Int (List.length commands); "commands", `List results] in
  Yojson.Basic.pretty_to_channel stdout report; print_newline ();
  if !passed <> List.length commands then exit 1
  in
  ignore (Execute.Host.pmatch proceed (fail "spectest")
    (Wast_execute.register_spectest_host Output.none
      (M.empty, M.empty) I.empty_store_record))

let () =
  if Array.length Sys.argv <> 2 then
    (prerr_endline "usage: eh_script projection.json"; exit 2);
  try run Sys.argv.(1)
  with exception_ -> prerr_endline (Printexc.to_string exception_); exit 2
