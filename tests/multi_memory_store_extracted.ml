(* Actual extracted store operations over the selected memory class. Distinct
   store addresses may initially hold the same persistent memory value; imported
   memory indices may also alias one address. Neither case is mocked. *)
open Extract

let checks = ref 0
let check label condition =
  if not condition then failwith ("multi-memory store: " ^ label);
  incr checks

let n = Big_int_Z.big_int_of_int
let byte i = Byte.repr (n i)
let some = function Some value -> value | None -> failwith "unexpected store failure"
let memory = memory_instance
let hfc = Ocaml_host.Ocaml_host.hfc
let first_bytes mi =
  List.init 4 (fun i ->
    let b = some (memory.m.mem_lookup (n i) mi.meminst_data) in
    Big_int_Z.int_of_big_int (Byte.unsigned b))
let size mi = Big_int_Z.int_of_big_int (mem_size memory mi)
let selected store inst index = some (smem memory hfc store inst (n index))
let make values =
  let data = memory.m.mem_make (n 65536) in
  let data = some (memory.mem_update_gen (n 0) (n 4)
    (fun i -> byte (List.nth values (Big_int_Z.int_of_big_int i))) data) in
  { meminst_type = { lim_min = n 1; lim_max = Some (n 3) }; meminst_data = data }

let () =
  let shared_value = make [1; 2; 3; 4] in
  let other = make [9; 8; 7; 6] in
  let store, _ = Ocaml_host.starting_wasm_host_store in
  let store = { store with s_mems = [shared_value; shared_value; other] } in
  let inst = { empty_moduleinst with inst_mems = List.map n [2; 0; 2; 1] } in
  let a = some (smem_store_packed memory hfc store inst
    (n 2) (n 1) (n 0) (VAL_int32 (Wasm_int.Int32.repr (n 170))) Tp_i8) in
  check "nonzero memory index selects address two"
    (first_bytes (selected a inst 2) = [9; 170; 7; 6]);
  check "duplicate imported address observes the same update"
    (first_bytes (selected a inst 0) = [9; 170; 7; 6]);
  check "distinct address zero remains unchanged"
    (first_bytes (selected a inst 1) = [1; 2; 3; 4]);
  check "distinct address one remains unchanged"
    (first_bytes (selected a inst 3) = [1; 2; 3; 4]);
  check "old store snapshot remains unchanged"
    (first_bytes (selected store inst 2) = [9; 8; 7; 6]);
  let b = some (smem_store_packed memory hfc a inst
    (n 1) (n 0) (n 2) (VAL_int32 (Wasm_int.Int32.repr (n 204))) Tp_i8) in
  check "packed store offset selects the correct byte"
    (first_bytes (selected b inst 1) = [1; 2; 204; 4]);
  check "equal persistent value at another store address is not mutated"
    (first_bytes (selected b inst 3) = [1; 2; 3; 4]);
  check "retained intermediate store snapshot is not mutated"
    (first_bytes (selected a inst 1) = [1; 2; 3; 4]);
  check "previous update in another memory is retained"
    (first_bytes (selected b inst 2) = [9; 170; 7; 6]);
  let grown, previous = some (smem_grow memory hfc b inst (n 2) (n 1)) in
  check "grow returns the selected memory's previous size" (Big_int_Z.eq_big_int previous (n 1));
  check "grow updates both aliased memory indices"
    (size (selected grown inst 0) = 2 && size (selected grown inst 2) = 2);
  check "grow leaves distinct addresses at old size"
    (size (selected grown inst 1) = 1 && size (selected grown inst 3) = 1);
  check "grow preserves selected initialized prefix"
    (first_bytes (selected grown inst 2) = [9; 170; 7; 6]);
  check "grow initializes the added page"
    (memory.m.mem_lookup (n 65536) (selected grown inst 2).meminst_data = Some (byte 0));
  check "grow retains old store size and bytes"
    (size (selected b inst 2) = 1 && first_bytes (selected b inst 2) = [9; 170; 7; 6]);
  check "grow respects selected maximum"
    (smem_grow memory hfc grown inst (n 2) (n 2) = None);
  check "grow/store preserve non-memory store components"
    (grown.s_funcs == store.s_funcs && grown.s_tables == store.s_tables &&
     grown.s_globals == store.s_globals && grown.s_elems == store.s_elems &&
     grown.s_datas == store.s_datas);
  let huge = Big_int_Z.big_int_of_string "340282366920938463463374607431768211455" in
  check "unbounded missing memory index returns None"
    (smem memory hfc grown inst huge = None);
  let bad_inst = { inst with inst_mems = [huge] } in
  check "unbounded missing imported memory address returns None"
    (smem memory hfc grown bad_inst (n 0) = None);
  check "grow rejects unbounded missing imported memory address"
    (smem_grow memory hfc grown bad_inst (n 0) (n 1) = None);
  check "store rejects unbounded missing imported memory address"
    (smem_store_packed memory hfc grown bad_inst (n 0) (n 0) (n 0)
      (VAL_int32 (Wasm_int.Int32.repr (n 1))) Tp_i8 = None);
  check "failed invalid-address operations preserve old memory snapshots"
    (first_bytes (selected store inst 2) = [9; 8; 7; 6] &&
     first_bytes (selected a inst 1) = [1; 2; 3; 4] &&
     first_bytes (selected b inst 1) = [1; 2; 204; 4]);
  Printf.printf "Multi-memory extracted store: %d/%d checks passed\n" !checks !checks
