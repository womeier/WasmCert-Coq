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
  check (s1.s_tag_ids = [List.hd i1.inst_defined_types])
    "first tag did not retain its canonical type identity";

  let s2, i2 = instantiate s1 single in
  check (i2.inst_tags = addresses [1]) "second module reused first tag identity";
  check (s2.s_tags = [[]; []]) "second allocation lost an old tag";
  check (s2.s_tag_ids = [List.hd s1.s_tag_ids; List.hd s1.s_tag_ids])
    "equal canonical tag types were not reused across distinct tag addresses";

  let mixed = "0061736d0100000001090260000060027f7e000d050200010000" in
  let s3, i3 = instantiate s2 mixed in
  check (i3.inst_tags = addresses [2; 3]) "multiple tag address order";
  check (s3.s_tags = [[]; []; [T_num T_i32; T_num T_i64]; []])
    "tag type-index resolution or parameter order";
  check (List.nth s3.s_tag_ids 2 = List.nth i3.inst_defined_types 1
         && List.nth s3.s_tag_ids 3 = List.nth i3.inst_defined_types 0)
    "canonical tag types did not follow the module's closed type-index map";

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

  let old_exception = {exninst_tag = List.hd i1.inst_tags; exninst_fields = []} in
  let seeded = {s1 with s_exns = [old_exception]} in
  let s5, i5 = instantiate seeded single in
  check (i5.inst_tags = addresses [1]) "exception store disturbed tag allocation";
  check (s5.s_exns = [old_exception]) "module allocation changed an exception";
  check (List.hd s5.s_tag_ids = List.hd s1.s_tag_ids)
    "module allocation changed an existing tag's canonical identity";
  print_endline "Extracted tag allocation tests: 5/5"
