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
  Printf.printf "GC extraction: %d/%d checks passed\n" !checks !checks
