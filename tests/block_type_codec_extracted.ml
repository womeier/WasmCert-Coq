(* Signed s33 indices in the actual recursive instruction codec. *)
open Extract
module B = Utility.Binary
let n = Big_int_Z.big_int_of_string
let count = ref 0
let check label ok =
  if not ok then failwith ("block-type codec regression: " ^ label);
  incr count
let () =
  List.iter (fun text ->
    let ty = BT_id (n text) in
    List.iter (fun instruction ->
      check "recursive instruction roundtrip"
        (B.parse_instruction (B.print_instruction instruction) = Some instruction)
    ) [BI_block (ty, []); BI_loop (ty, []);
       BI_if (ty, [BI_nop], [BI_nop])]
  ) ["0"; "63"; "64"; "65"; "111"; "112"; "123"; "124"; "125"; "126";
     "127"; "128"; "16383"; "16384"; "2147483648"; "4294967295"];
  check "64 does not collide with empty block type"
    (B.print_instruction (BI_block (BT_id (n "64"), [])) =
      List.map Char.chr [2; 192; 0; 11]);
  check "unsigned 0x40 still denotes empty type"
    (B.parse_instruction (List.map Char.chr [2; 64; 11]) =
      Some (BI_block (BT_valtype None, [])));
  check "reject s33 index overflow"
    (B.parse_instruction (List.map Char.chr [2; 128; 128; 128; 128; 16; 11]) = None);
  check "reject overlong signed block index"
    (B.parse_instruction (List.map Char.chr [2; 128; 128; 128; 128; 128; 0; 11]) = None);
  Printf.printf "Block-type extracted codec checks: %d/%d\n" !count !count
