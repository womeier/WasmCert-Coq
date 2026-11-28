(* Actual extracted scalar codecs; no independent decoder is used as oracle. *)
open Extract
module B = Utility.Binary

let n = Big_int_Z.big_int_of_string
let count = ref 0
let check label condition =
  if not condition then failwith ("scalar codec regression: " ^ label);
  incr count

let i32 z = match Utility.vali32_of_Z z with
  | VAL_num (VAL_int32 i) -> i
  | _ -> failwith "unexpected i32 constructor"
let i64 z = match Utility.vali64_of_Z z with
  | VAL_num (VAL_int64 i) -> i
  | _ -> failwith "unexpected i64 constructor"

let () =
  for x = -4096 to 4096 do
    let z = n (string_of_int x) in
    let v32 = i32 z and v64 = i64 z in
    check "i32 printer/parser" (B.parse_i32 (B.print_i32 v32) = Some v32);
    check "i64 printer/parser" (B.parse_i64 (B.print_i64 v64) = Some v64)
  done;
  List.iter (fun text ->
    let z = n text in
    let v32 = i32 z and v64 = i64 z in
    check "i32 boundary" (B.parse_i32 (B.print_i32 v32) = Some v32);
    check "i64 boundary" (B.parse_i64 (B.print_i64 v64) = Some v64)
  ) ["-9223372036854775808"; "-2147483648"; "2147483647";
     "4294967295"; "9223372036854775807"];
  List.iter (fun text ->
    let z = n text in
    check "unbounded signed codec"
      (B.parse_signed (B.print_signed z) = Some z)
  ) ["-1267650600228229401496703205376"; "1267650600228229401496703205376"];
  List.iter (fun text ->
    let x = n text in
    check "u32 printer/production bounded parser"
      (B.parse_u32 (B.print_u32 x) = Some x)
  ) ["0"; "1"; "127"; "128"; "16383"; "16384"; "2147483648"; "4294967295"];
  check "reject u32 overflow"
    (B.parse_u32 (B.print_u32 (n "4294967296")) = None);
  check "reject overlong u32"
    (B.parse_u32 (List.init 5 (fun _ -> Char.chr 128) @ [Char.chr 0]) = None);
  check "reject trailing byte" (B.parse_u32 [Char.chr 0; Char.chr 0] = None);
  check "accept legal padded zero" (B.parse_u32 [Char.chr 128; Char.chr 0] = Some (n "0"));
  Printf.printf "Scalar extracted codec checks: %d/%d\n" !count !count
