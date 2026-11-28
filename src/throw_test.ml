(* Binary-path tests for actual extracted throwing and administrative unwinding. *)
let check condition message = if not condition then failwith message
let integer = Z.of_int
let index = Z.to_int

let bytes hex =
  String.init (String.length hex / 2) (fun i ->
    Char.chr (int_of_string ("0x" ^ String.sub hex (2 * i) 2)))

let small n =
  check (n < 128) "test fixture exceeds single-byte LEB range";
  String.make 1 (Char.chr n)

let vector xs = small (List.length xs) ^ String.concat "" xs
let section id payload = small id ^ small (String.length payload) ^ payload

let module_bytes ?(start = false) imports parameters bodies =
  bytes "0061736d01000000"
  ^ section 1 (vector [bytes "600000"; bytes "60" ^ vector parameters ^ bytes "00"])
  ^ (if imports = [] then "" else section 2 (vector imports))
  ^ section 3 (vector (List.map (fun _ -> bytes "00") bodies))
  ^ section 13 (vector [bytes "0001"])
  ^ section 7 (vector [bytes "046d61696e00"
      ^ small (List.length imports + List.length bodies - 1)])
  ^ (if start then section 8 (small (List.length imports + List.length bodies - 1))
     else "")
  ^ section 10
      (vector (List.map (fun body ->
         let code = bytes "00" ^ bytes body ^ bytes "0b" in
         small (String.length code) ^ code) bodies))

let instantiate ?(store = Execute.Interpreter.empty_store_record)
    ?(imports = []) ?(values = []) parameters bodies =
  let open Execute.Interpreter in
  let m = match run_parse_module_str (module_bytes imports parameters bodies) with
    | None -> failwith "throw binary failed parsing"
    | Some m -> m
  in
  match interp_instantiate_wrapper store m values with
  | (None, error) -> failwith error
  | (Some (s, (f, initializers)), _) ->
    check (initializers = []) "unexpected initializer instructions";
    (s, f.Extract.f_inst)

let invoke s inst =
  let address = List.hd (List.rev inst.Extract.inst_funcs) in
  Execute.eval_wasm_cfg Output.none (-1)
    (s, (Extract.empty_frame, [Extract.AI_invoke address]))

let expect_exception result inst fields =
  match result with
  | Execute.Cfg_exception (s, _, a) ->
    let e = List.nth s.Extract.s_exns (index a) in
    check (e.Extract.exninst_tag = List.hd inst.Extract.inst_tags)
      "exception tag identity";
    check (e.Extract.exninst_fields = fields) "exception payload/order";
    (s, a)
  | _ -> failwith "throw did not produce a distinct exception outcome"

let () =
  let s, inst = instantiate [] ["0800"] in
  let s1, a1 = expect_exception (invoke s inst) inst [] in
  check (a1 = integer 0) "first exception address";
  let s2, a2 = expect_exception (invoke s1 inst) inst [] in
  check (a2 = integer 1) "exception identity reused";
  check (List.hd s1.Extract.s_exns = List.hd s2.Extract.s_exns)
    "old exception changed";

  let fields =
    [Extract.Utility.vali32_of_Z (integer 11);
     Extract.Utility.vali64_of_Z (integer 22)]
  in
  let s, inst = instantiate [bytes "7f"; bytes "7e"] ["410b42160800"] in
  ignore (expect_exception (invoke s inst) inst fields);

  (* Extra operands and later instructions must not escape an exception. *)
  let s, inst = instantiate [bytes "7f"] ["4163410b080000"] in
  ignore (expect_exception (invoke s inst) inst [List.hd fields]);

  (* Labels/loops and native call frames are crossed, rather than trapping. *)
  let s, inst = instantiate [] ["0240034008000b0b"] in
  ignore (expect_exception (invoke s inst) inst []);
  let s, inst = instantiate [] ["0800"; "1000"] in
  ignore (expect_exception (invoke s inst) inst []);

  (* Function imports must execute under the callee's tag identity, even when
     the caller defines a structurally identical tag at another address. *)
  let s, callee = instantiate [] ["0800"] in
  let function_address = List.hd callee.Extract.inst_funcs in
  let s, caller =
    instantiate ~store:s ~imports:[bytes "016d01660000"]
      ~values:[Extract.EV_func function_address] [] ["1000"]
  in
  check (caller.Extract.inst_tags <> callee.Extract.inst_tags)
    "test did not allocate distinct module tags";
  ignore (expect_exception (invoke s caller) callee []);

  let start_module =
    match Execute.Interpreter.run_parse_module_str
      (module_bytes ~start:true [] [] ["0800"]) with
    | Some m -> m
    | None -> failwith "start-throw binary failed parsing"
  in
  (match Execute.Interpreter.interp_instantiate_wrapper
      Execute.Interpreter.empty_store_record start_module [] with
  | (Some ((_, (frame, _)) as cfg), _) ->
    ignore (expect_exception (Execute.eval_wasm_cfg Output.none (-1) cfg)
      frame.Extract.f_inst [])
  | (None, error) -> failwith error);
  print_endline "Extracted throwing tests: 8/8"
