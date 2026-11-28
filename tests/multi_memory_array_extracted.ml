(* The actual selected/extracted Memory_vec API and Parray_shim, with independent
   immutable byte-list expectations. Finite regressions do not prove native code. *)
open Extract
exception Injected_failure

let checks = ref 0
let check label condition =
  if not condition then failwith ("multi-memory array: " ^ label);
  incr checks

let n = Big_int_Z.big_int_of_int
let byte i = Byte.repr (n i)
let some = function Some value -> value | None -> failwith "unexpected memory failure"
let read memory i = some (mv_lookup (n i) memory)
let bytes memory size = List.init size (fun i -> Big_int_Z.int_of_big_int (Byte.unsigned (read memory i)))
let initialized values =
  let length = List.length values in
  some (mv_update_gen (n 0) (n length)
    (fun i -> byte (List.nth values (Big_int_Z.int_of_big_int i))) (mv_make (n length)))

let () =
  check "64-bit native argument domain" (Sys.word_size = 64);
  let source = initialized [1; 2; 3; 4] in
  let copied = some (mv_update_gen (n 1) (n 3)
    (fun i -> read source (Big_int_Z.int_of_big_int i)) source) in
  check "actual extracted overlapping snapshot" (bytes copied 4 = [1; 1; 2; 3]);
  check "actual extracted original persists" (bytes source 4 = [1; 2; 3; 4]);
  let updated = some (mv_update (n 0) (byte 90) source) in
  let cross = some (mv_update_gen (n 1) (n 3)
    (fun i -> read updated (Big_int_Z.int_of_big_int i)) source) in
  check "actual extracted cross-version generator" (bytes cross 4 = [1; 90; 2; 3]);
  check "actual extracted alternate source" (bytes updated 4 = [90; 2; 3; 4]);
  check "actual extracted old shared source" (bytes source 4 = [1; 2; 3; 4]);
  let trapped = ref false in
  (try
     ignore (mv_update_gen (n 0) (n 3) (fun i ->
       let offset = Big_int_Z.int_of_big_int i in
       let b = read copied offset in
       if offset = 1 then raise Injected_failure else b) cross)
   with Injected_failure -> trapped := true);
  check "actual extracted callback exception propagates" !trapped;
  check "actual extracted exception destination unchanged" (bytes cross 4 = [1; 90; 2; 3]);
  check "actual extracted exception other versions unchanged"
    (bytes copied 4 = [1; 1; 2; 3] && bytes source 4 = [1; 2; 3; 4]);
  let calls = ref 0 in
  List.iter (fun (start, length) ->
    check "actual extracted invalid range rejected before native callback"
      (mv_update_gen start length (fun _ -> incr calls; byte 8) source = None);
    check "actual extracted invalid range no callback" (!calls = 0))
    [n 5, n 0; n 4, n 1;
     Big_int_Z.big_int_of_string "340282366920938463463374607431768211455", n 0;
     n 0, Big_int_Z.big_int_of_string "340282366920938463463374607431768211455"];
  check "actual extracted huge lookup returns None before native conversion"
    (mv_lookup (Big_int_Z.big_int_of_string "340282366920938463463374607431768211455") source = None);
  let empty = some (mv_update_gen (n 4) (n 0) (fun _ -> incr calls; byte 8) source) in
  check "actual extracted zero at end succeeds without callback"
    (!calls = 0 && bytes empty 4 = [1; 2; 3; 4]);
  let grown = some (mv_grow (n 3) updated) in
  check "actual extracted growth preserves prefix and initializes zero"
    (bytes grown 7 = [90; 2; 3; 4; 0; 0; 0]);
  check "actual extracted growth source persists" (bytes updated 4 = [90; 2; 3; 4]);
  let regrown = some (mv_grow (n 1) grown) in
  check "actual extracted in-capacity growth initializes zero"
    (bytes regrown 8 = [90; 2; 3; 4; 0; 0; 0; 0]);
  check "actual extracted length observations"
    (Big_int_Z.eq_big_int (mv_length source) (n 4) &&
     Big_int_Z.eq_big_int (mv_length grown) (n 7) &&
     Big_int_Z.eq_big_int (mv_length regrown) (n 8));
  let modified_spare = some (mv_update_gen (n 7) (n 1) (fun _ -> byte 99) regrown) in
  check "newly exposed capacity can be updated in its own version"
    (bytes modified_spare 8 = [90; 2; 3; 4; 0; 0; 0; 99]);
  check "old in-capacity grown version retains default byte"
    (bytes regrown 8 = [90; 2; 3; 4; 0; 0; 0; 0]);
  check "older shorter version still rejects spare capacity lookup"
    (mv_lookup (n 7) grown = None);
  let grown_again = some (mv_grow (n 1) grown) in
  check "growth from an older snapshot restores its own initialized-zero invariant"
    (bytes grown_again 8 = [90; 2; 3; 4; 0; 0; 0; 0]);
  check "rerooting older growth does not destroy later modified version"
    (bytes modified_spare 8 = [90; 2; 3; 4; 0; 0; 0; 99]);
  Printf.printf "Multi-memory extracted array: %d/%d checks passed\n" !checks !checks
