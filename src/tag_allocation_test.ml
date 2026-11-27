(* Tests the actual extracted parser and instantiation path, not EH helpers. *)
let check condition message = if not condition then failwith message

let of_hex hex =
  String.init (String.length hex / 2) (fun i ->
    Char.chr (int_of_string ("0x" ^ String.sub hex (2 * i) 2)))

let instantiate s hex =
  let open Execute.Interpreter in
  match run_parse_module_str (of_hex hex) with
  | None -> failwith "valid tag module failed parsing"
  | Some m ->
    match interp_instantiate_wrapper s m [] with
    | (None, message) -> failwith message
    | (Some (s', (f, initializers)), _) ->
      check (initializers = []) "unexpected initialization instructions";
      (s', f.Extract.f_inst)

let addresses ns = List.map Z.of_int ns

let () =
  let open Extract in
  let empty = Execute.Interpreter.empty_store_record in
  let single = "0061736d010000000104016000000d03010000" in
  let s1, i1 = instantiate empty single in
  check (i1.inst_tags = addresses [0]) "first tag address";
  check (s1.s_tags = [[]]) "first tag type";

  let s2, i2 = instantiate s1 single in
  check (i2.inst_tags = addresses [1]) "second module reused first tag identity";
  check (s2.s_tags = [[]; []]) "second allocation lost an old tag";

  let mixed = "0061736d0100000001090260000060027f7e000d050200010000" in
  let s3, i3 = instantiate s2 mixed in
  check (i3.inst_tags = addresses [2; 3]) "multiple tag address order";
  check (s3.s_tags = [[]; []; [T_num T_i32; T_num T_i64]; []])
    "tag type-index resolution or parameter order";

  let native =
    "0061736d010000000108026000017f600000030201000d030100010a06010400412a0b"
  in
  let s4, i4 = instantiate s3 native in
  check (i4.inst_tags = addresses [4]) "native module tag address";
  check (List.length s4.s_tags = 5) "native module tag allocation";
  (match s4.s_funcs with
  | [FC_func_native (_, inst, _)] ->
    check (inst.inst_tags = i4.inst_tags) "native closure lost its tag addresses"
  | _ -> failwith "expected exactly one native function");
  print_endline "Extracted tag allocation tests: 4/4"
