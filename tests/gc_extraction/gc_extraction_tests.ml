module BigZ = Z
open Extract

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
  Printf.printf "GC extraction: %d/%d checks passed\n" !checks !checks
