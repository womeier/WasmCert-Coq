module BigZ = Z
open Extract

module No_host = struct
  type host_function = unit
  let host_function_eq_dec a b = a = b
  let hfc = host_function_eq_dec
  type host_state_type = unit
  let host_apply_pure hs _ _ _ _ = hs, None
end

module Runtime = Extraction_instance (No_host)

let checks = ref 0

let check name condition =
  incr checks;
  if not condition then failwith ("GC extraction regression: " ^ name)

let check_z name actual expected = check name (BigZ.equal actual (BigZ.of_string expected))

let i32 = Wasm_int.Int32.repr

let () =
  let open Utility.GC in
  List.iter
    (fun (input, unsigned, signed) ->
      let p = ref_i31 (i32 (BigZ.of_string input)) in
      check_z ("i31 unsigned " ^ input) (Wasm_int.Int32.unsigned (i31_get SX_U p)) unsigned;
      check_z ("i31 signed " ^ input) (Wasm_int.Int32.signed (i31_get SX_S p)) signed)
    [ "0", "0", "0";
      "1073741823", "1073741823", "1073741823";
      "1073741824", "1073741824", "-1073741824";
      "2147483647", "2147483647", "-1";
      "2147483648", "0", "0";
      "-1", "2147483647", "-1" ];
  check "null i31.get_u traps" (i31_get_nullable SX_U None = None);
  check "null i31.get_s traps" (i31_get_nullable SX_S None = None);
  List.iter
    (fun (t, input, unsigned, signed) ->
      let p = pack_field t (i32 (BigZ.of_string input)) in
      check_z "packed unsigned" (Wasm_int.Int32.unsigned (unpack_field t SX_U p)) unsigned;
      check_z "packed signed" (Wasm_int.Int32.signed (unpack_field t SX_S p)) signed)
    [ PT_i8, "511", "255", "-1";
      PT_i8, "128", "128", "-128";
      PT_i16, "65536", "0", "0";
      PT_i16, "32768", "32768", "-32768";
      PT_i16, "-1", "65535", "-1" ];
  let heaps =
    [ AH_any; AH_eq; AH_i31; AH_struct; AH_array; AH_none;
      AH_func; AH_nofunc; AH_extern; AH_noextern ]
  in
  List.iter
    (fun heap ->
      check "heap reflexivity" (heap_subtyping heap heap);
      List.iter
        (fun nullable ->
          let t = { art_nullable = nullable; art_heap = heap } in
          let bytes = encode_reference t in
          check "reference codec suffix roundtrip"
            (decode_reference (bytes @ ['z']) = Some (t, ['z'])))
        [false; true])
    heaps;
  check "none is not function bottom" (not (heap_subtyping AH_none AH_func));
  check "nofunc is not internal bottom" (not (heap_subtyping AH_nofunc AH_any));
  check "noextern is not internal bottom" (not (heap_subtyping AH_noextern AH_eq));
  let encodings =
    [ '\x6a', AH_array; '\x6b', AH_struct; '\x6c', AH_i31;
      '\x6d', AH_eq; '\x6e', AH_any; '\x6f', AH_extern;
      '\x70', AH_func; '\x71', AH_none; '\x72', AH_noextern;
      '\x73', AH_nofunc ]
  in
  for code = 0 to 255 do
    let b = Char.chr code in
    let expected nullable =
      Stdlib.Option.map
        (fun heap -> ({ art_nullable = nullable; art_heap = heap }, ['\x0b']))
        (List.assoc_opt b encodings)
    in
    check "one-byte reference opcode table"
      (decode_reference [b; '\x0b'] = expected true);
    check "explicit nullable reference opcode table"
      (decode_reference ['\x63'; b; '\x0b'] = expected true);
    check "explicit nonnull reference opcode table"
      (decode_reference ['\x64'; b; '\x0b'] = expected false);
    let expected_packed =
      match code with 0x78 -> Some PT_i8 | 0x77 -> Some PT_i16 | _ -> None
    in
    check "packed opcode table" (decode_packed b = expected_packed)
  done;
  check "truncated nullable reference" (decode_reference ['\x63'] = None);
  check "truncated nonnull reference" (decode_reference ['\x64'] = None);
  check "empty reference" (decode_reference [] = None);
  check "overlong abstract heap encoding is not an abstract heap type"
    (decode_reference ['\xee'; '\x7f'] = None);
  (* Exercise the actual extracted whole-module parser, rather than a second
     decoder.  Every vector-bearing empty section permits a padded zero count. *)
  let header = ['\x00'; '\x61'; '\x73'; '\x6d'; '\x01'; '\x00'; '\x00'; '\x00'] in
  let empty_module = run_parse_module header in
  check "empty module fixture parses" (empty_module <> None);
  let section id payload =
    header @ [Char.chr id; Char.chr (List.length payload)] @ payload
  in
  List.iter
    (fun id ->
      for padding = 0 to 4 do
        let zero = List.init padding (fun _ -> '\x80') @ ['\x00'] in
        check "module padded empty vector"
          (run_parse_module (section id zero) = empty_module)
      done;
      check "module overlong zero vector rejected"
        (run_parse_module (section id ['\x80'; '\x80'; '\x80'; '\x80'; '\x80'; '\x00']) = None);
      check "module overflowing vector count rejected"
        (run_parse_module (section id ['\x80'; '\x80'; '\x80'; '\x80'; '\x10']) = None);
      check "module truncated vector count rejected"
        (run_parse_module (section id ['\x80']) = None))
    [1; 2; 3; 4; 5; 6; 7; 9; 10; 11];
  List.iter
    (fun (bytes, expected) ->
      let expected = Stdlib.Option.map BigZ.of_string expected in
      let actual = decode_typeidx bytes in
      check "signed-33 heap index"
        (match actual, expected with
         | Some x, Some y -> BigZ.equal x y
         | None, None -> true
         | _, _ -> false))
    [ ['\x00'], Some "0";
      ['\x3f'], Some "63";
      ['\xc0'; '\x00'], Some "64";
      ['\xff'; '\x00'], Some "127";
      ['\x80'; '\x01'], Some "128";
      ['\xff'; '\xff'; '\xff'; '\xff'; '\x07'], Some "2147483647";
      ['\xff'; '\xff'; '\xff'; '\xff'; '\x0f'], Some "4294967295";
      ['\x80'; '\x80'; '\x80'; '\x80'; '\x00'], Some "0";
      ['\xc0'; '\x80'; '\x80'; '\x80'; '\x00'], Some "64";
      ['\x40'], None;
      ['\x70'], None;
      ['\x7f'], None;
      ['\x80'; '\x80'; '\x80'; '\x80'; '\x10'], None;
      ['\x80'; '\x80'; '\x80'; '\x80'; '\x70'], None;
      ['\x80'; '\x80'; '\x80'; '\x80'; '\x80'; '\x00'], None;
      ['\x80'], None;
      ['\x00'; '\x00'], None;
      [], None ];
  List.iter
    (fun x ->
      let x = BigZ.of_string x in
      check "ordinary unsigned type-index actual printer/parser roundtrip"
        (match decode_immediate_typeidx (encode_immediate_typeidx x) with
         | Some y -> BigZ.equal x y
         | None -> false);
      match encode_typeidx x with
      | None -> check "heap index printer unexpectedly rejected" false
      | Some bytes ->
          check "heap index actual printer/parser roundtrip"
            (match decode_typeidx bytes with
             | Some y -> BigZ.equal x y
             | None -> false);
          check "heap index printer five-byte limit" (List.length bytes <= 5))
    ["0"; "63"; "64"; "127"; "128"; "8191"; "8192"; "16383"; "16384";
     "1048575"; "1048576"; "2147483647"; "2147483648"; "4294967295"];
  check "heap index printer rejects overflow"
    (encode_typeidx (BigZ.of_string "4294967296") = None);
  check "ordinary index encoding is not heap signed encoding"
    (encode_immediate_typeidx (BigZ.of_int 64) = ['\x40'] &&
      encode_typeidx (BigZ.of_int 64) = Some ['\xc0'; '\x00']);
  let id group member =
    { defined_group = BigZ.of_int group; defined_member = BigZ.of_int member }
  in
  let field index =
    { field_mutability = MUT_const;
      field_storage = ST_value
        (T_ref { ref_nullable = true; ref_heap = HT_type (BigZ.of_int index) }) }
  in
  let st final supers composite =
    { subtype_final = final; subtype_supers = List.map BigZ.of_int supers;
      subtype_composite = composite }
  in
  let recursive_group base =
    [st true [] (Comp_struct [field (base + 1)]);
     st true [] (Comp_struct [field base])]
  in
  let registry, ids =
    match Types.close [] [recursive_group 0] with
    | Some result -> result
    | None -> failwith "Closing a mutually recursive group failed"
  in
  check "recursive group member identities" (ids = [id 0 0; id 0 1]);
  check "recursive group closes as one registry entry" (List.length registry = 1);
  check "recursive expansion resolves member binder"
    (Types.struct_type registry (id 0 0) =
      Some [{ field_mutability = MUT_const;
              field_storage = ST_value
                (CV_ref (true, CH_defined (CT_def (id 0 1)))) }]);
  check "recursive second member expansion"
    (Types.struct_type registry (id 0 1) =
      Some [{ field_mutability = MUT_const;
              field_storage = ST_value
                (CV_ref (true, CH_defined (CT_def (id 0 0)))) }]);
  check "equal recursive groups reuse canonical identity"
    (Types.close registry [recursive_group 0] = Some (registry, ids));
  let function_group = [st false [] (Comp_func (Tf ([], [])))] in
  begin match Types.close registry [function_group; recursive_group 1] with
  | None -> check "shifted recursive group closes" false
  | Some (registry', ids') ->
      check "module source index shift preserves canonical identity"
        (ids' = [id 1 0; id 0 0; id 0 1]);
      check "index shift does not duplicate recursive group" (List.length registry' = 2);
      check "function expansion"
        (Types.function_type registry' (id 1 0) = Some (Closed_ft ([], [])));
      check "struct type is not a function"
        (Types.function_type registry' (id 0 0) = None)
  end;
  let parent = [st false [] (Comp_func (Tf ([], [])))] in
  let child = [st true [0] (Comp_func (Tf ([], [])))] in
  begin match Types.close [] [parent; child] with
  | None -> check "declared subtype closing" false
  | Some (types, names) ->
      check "declared subtype identities" (names = [id 0 0; id 1 0]);
      check "declared child matches parent" (Types.matches types (id 1 0) (id 0 0));
      check "declared parent does not match child" (not (Types.matches types (id 0 0) (id 1 0)));
      check "bidirectional matching excludes strict subtype"
        (not (Types.equivalent types (id 0 0) (id 1 0)));
      check "bidirectional reflexivity" (Types.equivalent types (id 1 0) (id 1 0))
  end;
  check "out-of-scope reference rejected"
    (Types.close [] [[st true [] (Comp_struct [field 1])]] = None);
  check "cyclic declared supertype rejected"
    (Types.close [] [[st false [0] (Comp_func (Tf ([], [])))]] = None);
  check "multiple declared supertypes rejected"
    (Types.close [] [parent; [st true [0; 0] (Comp_func (Tf ([], [])))]] = None);
  check "bottom type excluded from declaration"
    (Types.close [] [[st true [] (Comp_func (Tf ([], [T_bot])))]] = None);
  check "invalid canonical group lookup" (Types.expand [] (id 0 0) = None);
  check "invalid canonical member lookup" (Types.expand registry (id 0 2) = None);
  let invalid_parent p =
    [{ subtype_final = false; subtype_supers = [CT_def p];
       subtype_composite = Comp_func (Closed_ft ([], [])) }]
  in
  check "canonical closer rejects cyclic input registry"
    (Types.close [invalid_parent (id 0 0)] [] = None);
  check "canonical closer rejects dangling parent identity"
    (Types.close [invalid_parent (id 1 0)] [] = None);
  let chain =
    List.init 64
      (fun i -> [st false (if i = 0 then [] else [i - 1]) (Comp_func (Tf ([], [])))])
  in
  begin match Types.close [] chain with
  | None -> check "long declared subtype chain closes" false
  | Some (types, names) ->
      check "long declared subtype chain identities" (List.length names = 64);
      check "matching traverses the entire declared chain"
        (Types.matches types (id 63 0) (id 0 0));
      check "long declared subtype chain direction"
        (not (Types.matches types (id 0 0) (id 63 0)))
  end;
  let abstract h = CV_ref (true, CH_abstract h) in
  let any = abstract HT_any and eq = abstract HT_eq and i31 = abstract HT_i31 in
  let cf mut ty = { field_mutability = mut; field_storage = ST_value ty } in
  let packed p = { field_mutability = MUT_const; field_storage = ST_packed p } in
  let cm = Types.composite_matches [] in
  check "closed function arguments are contravariant"
    (cm (Comp_func (Closed_ft ([any], [i31])))
        (Comp_func (Closed_ft ([eq], [eq]))));
  check "closed function rejects reversed argument variance"
    (not (cm (Comp_func (Closed_ft ([i31], [])))
             (Comp_func (Closed_ft ([eq], [])))));
  check "closed function rejects reversed result variance"
    (not (cm (Comp_func (Closed_ft ([], [any])))
             (Comp_func (Closed_ft ([], [eq])))));
  check "closed function rejects arity mismatch"
    (not (cm (Comp_func (Closed_ft ([], [])))
             (Comp_func (Closed_ft ([eq], [])))));
  check "immutable fields are covariant with struct width"
    (cm (Comp_struct [cf MUT_const i31; packed PT_i8])
        (Comp_struct [cf MUT_const eq]));
  check "struct rejects insufficient width"
    (not (cm (Comp_struct []) (Comp_struct [cf MUT_const eq])));
  check "mutable fields reject covariance"
    (not (cm (Comp_array (cf MUT_var i31)) (Comp_array (cf MUT_var eq))));
  check "mutable fields accept identical types"
    (cm (Comp_array (cf MUT_var i31)) (Comp_array (cf MUT_var i31)));
  check "field mutability must agree"
    (not (cm (Comp_array (cf MUT_const i31)) (Comp_array (cf MUT_var i31))));
  check "packed fields require identical widths"
    (not (cm (Comp_array (packed PT_i8)) (Comp_array (packed PT_i16))));
  check "packed identical fields match"
    (cm (Comp_array (packed PT_i8)) (Comp_array (packed PT_i8)));
  check "composite kinds must agree"
    (not (cm (Comp_struct []) (Comp_func (Closed_ft ([], [])))));
  check "validated self recursive group"
    (Types.close_validated [] [recursive_group 0] = Some (registry, ids));
  let declares final supers comp =
    { subtype_final = final; subtype_supers = supers; subtype_composite = comp }
  in
  let closed_parent = declares false [] (Comp_struct [cf MUT_const eq]) in
  let closed_child =
    declares true [CT_def (id 0 0)]
      (Comp_struct [cf MUT_const i31; packed PT_i16])
  in
  check "validated structural subtype"
    (Types.validate [[closed_parent]; [closed_child]]);
  check "final declared parent rejected"
    (not (Types.validate
      [[{ closed_parent with subtype_final = true }]; [closed_child]]));
  check "declared mixed composite kinds rejected"
    (not (Types.validate [[closed_parent];
      [declares true [CT_def (id 0 0)] (Comp_array (cf MUT_const i31))]]));
  check "dangling closed field identity rejected"
    (not (Types.validate
      [[declares true [] (Comp_array
        (cf MUT_const (CV_ref (true, CH_defined (CT_def (id 2 0))))))]]));
  check "unresolved binder accepted only through expansion"
    (Types.validate registry);
  check "indexed source masquerading as abstract heap rejected"
    (not (Types.validate
      [[declares true [] (Comp_array (cf MUT_const (abstract (HT_type BigZ.zero))))]]));
  check "duplicate canonical groups rejected by validator"
    (not (Types.validate [[closed_parent]; [closed_parent]]));
  check "validated closing rejects final parent"
    (Types.close_validated []
      [[st true [] (Comp_func (Tf ([], [])))]; child] = None);
  let nullable t = CV_ref (true, CH_defined (CT_def t)) in
  let nonnull t = CV_ref (false, CH_defined (CT_def t)) in
  let cm_defined = Types.composite_matches [[closed_parent]; [closed_child]] in
  check "closed defined reference follows declared edge"
    (cm_defined (Comp_array (cf MUT_const (nonnull (id 1 0))))
      (Comp_array (cf MUT_const (nullable (id 0 0)))));
  check "nullable defined reference does not match non-null"
    (not (cm_defined (Comp_array (cf MUT_const (nullable (id 1 0))))
      (Comp_array (cf MUT_const (nonnull (id 0 0))))));
  check "defined struct matches abstract eq"
    (cm_defined (Comp_array (cf MUT_const (nullable (id 0 0))))
      (Comp_array (cf MUT_const eq)));
  check "none matches defined struct"
    (cm_defined (Comp_array (cf MUT_const (abstract HT_none)))
      (Comp_array (cf MUT_const (nullable (id 0 0)))));
  check "nofunc does not match defined struct"
    (not (cm_defined (Comp_array (cf MUT_const (abstract HT_nofunc)))
      (Comp_array (cf MUT_const (nullable (id 0 0))))));
  check "none does not match abstract function"
    (not (cm (Comp_array (cf MUT_const (abstract HT_none)))
      (Comp_array (cf MUT_const (abstract HT_func)))));
  check "exception bottom matches exception"
    (cm (Comp_array (cf MUT_const (abstract HT_noexn)))
      (Comp_array (cf MUT_const (abstract HT_exn))));
  check "exception root does not match GC root"
    (not (cm (Comp_array (cf MUT_const (abstract HT_exn)))
      (Comp_array (cf MUT_const any))));
  let blank =
    match empty_module with Some m -> m | None -> failwith "empty binary module"
  in
  let func index =
    { modfunc_type = BigZ.of_int index; modfunc_locals = []; modfunc_body = [] }
  in
  let function_groups functions =
    List.map (fun f -> [st true [] (Comp_func f)]) functions in
  let m1 = { blank with mod_types = function_groups [Tf ([], []); Tf ([], [])];
                       mod_funcs = [func 1] } in
  let instantiate store m =
    match Runtime.interp_instantiate_wrapper (Obj.magic ()) store m [] with
    | Some (s, (frame, _)), _ -> s, frame.f_inst
    | None, _ -> failwith "production canonical module instantiation failed"
  in
  let s1, inst1 = instantiate Runtime.empty_store_record m1 in
  check "production instantiation interns repeated type declarations"
    (List.length s1.s_types = 1 && inst1.inst_defined_types = [id 0 0; id 0 0]);
  check "production instance resolves source type through canonical names"
    (Runtime.resolve_type inst1 BigZ.one = Some (id 0 0));
  check "production instance expands closed function"
    (Runtime.expand_function s1 inst1 BigZ.one = Some (Closed_ft ([], [])));
  check "production native function carries canonical identity"
    (Runtime.native_function_type (List.hd s1.s_funcs) = Some (id 0 0));
  let m2 = { blank with mod_types = function_groups [Tf ([T_num T_i32], []); Tf ([], [])];
                       mod_funcs = [func 0; func 1] } in
  let s2, inst2 = instantiate s1 m2 in
  check "production second module extends shared canonical store"
    (List.length s2.s_types = 2 && inst2.inst_defined_types = [id 1 0; id 0 0]);
  check "production earlier identity expands after later instantiation"
    (Runtime.expand_function s2 inst1 BigZ.one = Some (Closed_ft ([], [])));
  check "production closed expansion distinguishes signatures"
    (Runtime.expand_function s2 inst2 BigZ.zero =
      Some (Closed_ft ([CV_num T_i32], [])));
  check "production modules with different local indices share identity"
    (Runtime.resolve_type inst1 BigZ.zero = Runtime.resolve_type inst2 BigZ.one);
  check "production out-of-bounds type resolution fails"
    (Runtime.resolve_type inst2 (BigZ.of_int 2) = None);
  let bad = { blank with mod_types = function_groups [Tf ([], [T_bot])] } in
  check "production module validation rejects invalid type declaration"
    (match Runtime.interp_instantiate_wrapper (Obj.magic ()) s2 bad [] with
     | None, _ -> true | Some _, _ -> false);
  let corrupt = { s2 with s_types = [invalid_parent (id 0 0)] } in
  check "production instantiation rejects invalid store type registry"
    (match Runtime.interp_instantiate_wrapper (Obj.magic ()) corrupt blank [] with
     | None, _ -> true | Some _, _ -> false);
  check "main instance typing accepts matching closed map"
    (Runtime.instance_context s2 inst2 <> None);
  check "main instance typing rejects forged closed signature"
    (Runtime.instance_context s2
      { inst2 with inst_defined_types = [id 0 0; id 0 0] } = None);
  check "main instance typing rejects truncated closed map"
    (Runtime.instance_context s2 { inst2 with inst_defined_types = [] } = None);
  check "main instance typing rejects dangling closed identity"
    (Runtime.instance_context s2
      { inst2 with inst_defined_types = [id 12 0; id 0 0] } = None);
  let typed_param index = Tf ([T_ref { ref_nullable = true;
                                      ref_heap = HT_type (BigZ.of_int index) }], []) in
  let typed_a = { blank with mod_types = function_groups [Tf ([], []); typed_param 0];
                            mod_funcs = [func 1] } in
  let sa, ia = instantiate Runtime.empty_store_record typed_a in
  let typed_b = { blank with mod_types =
                  function_groups [Tf ([T_num T_i32], []); Tf ([], []); typed_param 1];
                            mod_funcs = [func 2] } in
  let sb, ib = instantiate sa typed_b in
  check "production closes typed function parameters through map"
    (Runtime.expand_function sa ia BigZ.one =
      Some (Closed_ft ([CV_ref (true, CH_defined (CT_def (id 0 0)))], [])));
  check "source-index-shifted typed function signatures share canonical identity"
    (Runtime.resolve_type ia BigZ.one = Runtime.resolve_type ib (BigZ.of_int 2));
  check "earlier typed native expansion stays valid after store extension"
    (Runtime.instance_context sb ia <> None &&
     Runtime.expand_function sb ia BigZ.one = Runtime.expand_function sa ia BigZ.one);
  let self = { blank with mod_types = function_groups [typed_param 0]; mod_funcs = [func 0] } in
  let ss, iself = instantiate Runtime.empty_store_record self in
  check "production self-reference source-resolution agrees with closed expansion"
    (Runtime.instance_context ss iself <> None &&
     Runtime.expand_function ss iself BigZ.zero =
       Some (Closed_ft ([CV_ref (true, CH_defined (CT_def (id 0 0)))], [])));
  let host_signature = Tf ([T_num T_i32], [T_num T_i32]) in
  let host_registry =
    match Types.close_functions [] [host_signature] with
    | Some (registry, _) -> registry
    | None -> failwith "host canonical registration failed"
  in
  let host_store =
    { Runtime.empty_store_record with
      s_funcs = [FC_func_host (host_signature, Obj.magic ())];
      s_types = host_registry }
  in
  check "production host function resolves canonical defining identity"
    (Runtime.lookup_function_type host_store BigZ.zero = Some (id 0 0));
  let importer =
    { blank with mod_types = function_groups [host_signature];
      mod_imports = [{ imp_module = []; imp_name = []; imp_desc = MID_func BigZ.zero }] }
  in
  let imported_store, imported_instance =
    match Runtime.interp_instantiate_wrapper (Obj.magic ()) host_store importer
      [EV_func BigZ.zero] with
    | Some (s, (frame, _)), _ -> s, frame.f_inst
    | None, _ -> failwith "production host canonical import failed"
  in
  check "production host import agrees with module closed identity"
    (Runtime.lookup_function_type imported_store BigZ.zero =
     Runtime.resolve_type imported_instance BigZ.zero);
  let host_extended, _ = instantiate imported_store m2 in
  check "host canonical identity is stable across later module instantiation"
    (Runtime.lookup_function_type host_extended BigZ.zero = Some (id 0 0));
  check "host canonical identity has closed function expansion"
    (Types.function_type host_extended.s_types (id 0 0) =
      Some (Closed_ft ([CV_num T_i32], [CV_num T_i32])));
  check "host source indices cannot masquerade as module-local identities"
    (Runtime.lookup_function_type
      { host_store with s_funcs = [FC_func_host (typed_param 0, Obj.magic ())] }
      BigZ.zero = None);
  let mixed =
    { blank with mod_types =
      [[st false [] (Comp_struct [field 1]);
        st true [] (Comp_array (packed PT_i16))];
       [st true [] (Comp_func (Tf ([], [])))]];
      mod_funcs = [func 2] }
  in
  let mixed_store, mixed_instance = instantiate Runtime.empty_store_record mixed in
  check "production composite contexts retain all source indices"
    (List.length mixed_instance.inst_types = 3 &&
     mixed_instance.inst_defined_types = [id 0 0; id 0 1; id 1 0]);
  check "production main instance typing accepts recursive aggregate context"
    (Runtime.instance_context mixed_store mixed_instance <> None);
  check "production struct expansion resolves recursive array field"
    (Types.struct_type mixed_store.s_types (id 0 0) =
      Some [{ field_mutability = MUT_const; field_storage =
        ST_value (CV_ref (true, CH_defined (CT_def (id 0 1)))) }]);
  check "production array expansion retains packed storage"
    (Types.array_type mixed_store.s_types (id 0 1) = Some (packed PT_i16));
  check "aggregate source index cannot expand as function"
    (Runtime.expand_function mixed_store mixed_instance BigZ.zero = None);
  check "production native identity uses uncompressed mixed source index"
    (Runtime.lookup_function_type mixed_store BigZ.zero = Some (id 1 0));
  let repeated_store, repeated_instance = instantiate mixed_store mixed in
  check "production identical recursive groups reuse global identities"
    (List.length repeated_store.s_types = 2 &&
     repeated_instance.inst_defined_types = mixed_instance.inst_defined_types);
  let forged_source =
    match mixed_instance.inst_types with
    | t :: rest -> { t with subtype_final = true } :: rest
    | [] -> failwith "missing composite source context"
  in
  check "main instance typing checks source finality agreement"
    (Runtime.instance_context mixed_store
      { mixed_instance with inst_types = forged_source } = None);
  let forward_base =
    [[declares true [] (Comp_struct
       [cf MUT_const (CV_ref (true, CH_defined (CT_def (id 1 0))))])];
     [declares true [] (Comp_struct [])]]
  in
  check "portability permits valid forward destination field references"
    (Types.validate forward_base);
  let portable =
    { blank with mod_types =
      [[st true [] (Comp_struct [])];
       [st true [] (Comp_struct [field 0])];
       [st true [] (Comp_func
         (Tf ([T_ref { ref_nullable = true; ref_heap = HT_type BigZ.zero }],
              [T_ref { ref_nullable = true; ref_heap = HT_type BigZ.one }])))]];
      mod_funcs = [] }
  in
  let ported_store, ported_instance =
    instantiate { Runtime.empty_store_record with s_types = forward_base } portable
  in
  check "production portability reuses groups in reverse destination order"
    (ported_instance.inst_defined_types = [id 1 0; id 0 0; id 2 0]);
  check "production portability appends only the fresh function group"
    (List.length ported_store.s_types = 3 &&
     List.filteri (fun i _ -> i < 2) ported_store.s_types = forward_base);
  check "production portability preserves full source identity agreement"
    (Runtime.instance_context ported_store ported_instance <> None);
  check "production portability substitutes payload source indices"
    (Runtime.expand_function ported_store ported_instance (BigZ.of_int 2) =
      Some (Closed_ft
        ([CV_ref (true, CH_defined (CT_def (id 1 0)))],
         [CV_ref (true, CH_defined (CT_def (id 0 0)))])));
  Printf.printf "GC extraction: %d/%d checks passed\n" !checks !checks
