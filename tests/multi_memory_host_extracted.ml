(* Test the actual host dispatcher and generated, proved clock-result code.
   A host must not bypass its result-type contract by ignoring the requested
   signature. Its successful callback must preserve the exact store object. *)
open Extract
module H = Ocaml_host.Ocaml_host

let count = ref 0
let check label test =
  if not test then failwith ("multi-memory host: " ^ label);
  incr count

let () =
  let n = Big_int_Z.big_int_of_int in
  let s, _ = Ocaml_host.starting_wasm_host_store in
  let memories = List.init 3 (fun i ->
    { meminst_type = { lim_min = n 0; lim_max = None };
      meminst_data = Obj.magic (mv_make (n (i + 1))) }) in
  let s = { s with s_mems = memories } in
  let good = Tf ([], [T_num T_i64]) in
  List.iter (fun bad ->
    check "wrong requested signature returns failure, not ill-typed success"
      (H.host_apply_pure () s bad 0 [] = ((), None)))
    [Tf ([], []); Tf ([], [T_num T_i32]); Tf ([T_num T_i32], [T_num T_i64])];
  check "unexpected arguments return failure"
    (H.host_apply_pure () s good 0 [Utility.vali32_of_Z (n 1)] = ((), None));
  List.iter (fun id ->
    check "unknown host ID returns failure, not an assertion exception"
      (H.host_apply_pure () s good id [] = ((), None)))
    [1; -1; max_int; min_int];
  check "clock result is i64 and preserves every memory/store component"
    (match H.host_apply_pure () s good 0 [] with
     | (), Some (s', Result_values [VAL_num (VAL_int64 _)]) -> s' == s
     | _ -> false);
  Printf.printf "Multi-memory extracted host: %d/%d checks passed\n" !count !count
