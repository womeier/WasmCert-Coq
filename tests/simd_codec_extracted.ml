(* Ordinary SIMD production printer/parser regressions; no relaxed SIMD. *)
open Extract
module B = Utility.Binary

let n x = Big_int_Z.big_int_of_int x
let count = ref 0
let check label condition =
  if not condition then failwith ("SIMD codec regression: " ^ label);
  incr count

let () =
  List.iteri (fun i shape ->
    let instruction = BI_splat_vec shape in
    let bytes = B.print_instruction instruction in
    check "splat exact opcode" (bytes = [Char.chr 253; Char.chr (15 + i)]);
    check "splat roundtrip" (B.parse_instruction bytes = Some instruction)
  ) [VS_i VSI_8_16; VS_i VSI_16_8; VS_i VSI_32_4; VS_i VSI_64_2;
     VS_f VSF_32_4; VS_f VSF_64_2];
  for shift = 0 to 31 do
    let lanes = List.init 16 (fun i -> (i + shift) mod 32) in
    let instruction = BI_vbinop (n 13, List.map n lanes) in
    let bytes = B.print_instruction instruction in
    check "shuffle 16 raw bytes"
      (bytes = [Char.chr 253; Char.chr 13] @ List.map Char.chr lanes);
    check "shuffle roundtrip" (B.parse_instruction bytes = Some instruction)
  done;
  let high = [Char.chr 253; Char.chr 13] @ List.init 16 (fun _ -> Char.chr 255) in
  check "raw high lanes decode before validation"
    (B.parse_instruction high =
      Some (BI_vbinop (n 13, List.init 16 (fun _ -> n 255))));
  check "truncated shuffle fails"
    (B.parse_instruction ([Char.chr 253; Char.chr 13] @ List.init 15 (fun _ -> Char.chr 0)) = None);
  Printf.printf "SIMD extracted codec checks: %d/%d\n" !count !count
