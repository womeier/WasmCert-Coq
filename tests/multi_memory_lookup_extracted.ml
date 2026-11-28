(* Exercise the actual exported lookup selected by extraction, not a mock.
   The independent reference uses native indices only for this small test list.
   Missing unbounded indices must return None, never raise Z.Overflow. *)
open Extract

let checks = ref 0
let check label test =
  if not test then failwith ("multi-memory lookup: " ^ label);
  incr checks

let n = Big_int_Z.big_int_of_int
let big = Big_int_Z.big_int_of_string

let () =
  for len = 0 to 32 do
    let xs = List.init len (fun i -> 7 * i + 3) in
    for index = 0 to len + 2 do
      check "finite lookup equation"
        (lookup_N xs (n index) = List.nth_opt xs index)
    done;
    List.iter (fun index ->
      check ("unbounded missing index " ^ index)
        (lookup_N xs (big index) = None))
      ["4294967295"; "4611686018427387903"; "4611686018427387904";
       "18446744073709551615"; "340282366920938463463374607431768211455"]
  done;
  Printf.printf "Multi-memory extracted lookup: %d/%d checks passed\n"
    !checks !checks
