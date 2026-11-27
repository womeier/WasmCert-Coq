(* Exercise the actual extracted definitions, including the selected vector
   memory backend.  These are API regressions, not Wasm module conformance. *)
open Extract
module A = Addressing
module B = AddressingBinary
module M = AddressingMemory
module T = AddressingTable
module U = AddressingBulk
module P = AddressingParseque

let n = Big_int_Z.big_int_of_string
let z = n "0"
let one = n "1"
let equal = Big_int_Z.eq_big_int
let value a s = A.value_of_address a (n s)
let limits minimum maximum =
  { lim_min = n minimum; lim_max = Stdlib.Option.map n maximum }

let count = ref 0
let check name condition =
  if not condition then failwith ("addressing regression: " ^ name);
  incr count

let some name = function
  | Some result -> result
  | None -> failwith ("addressing regression: " ^ name ^ " unexpectedly failed")

module No_host : Parametric_host = struct
  type host_function = unit
  let host_function_eq_dec _ _ = true
  let hfc = host_function_eq_dec
  type host_state_type = unit
  let host_apply_pure hs _ _ _ _ = hs, None
end

module Runner = Extraction_instance (No_host)

let storage_program result_type memories tables instructions : module0 =
  { mod_types = [Tf ([], [T_num result_type])];
    mod_funcs = [{ modfunc_type = z; modfunc_locals = [];
                   modfunc_body = instructions }];
    mod_tables = tables;
    mod_mems = memories;
    mod_globals = []; mod_elems = []; mod_datas = []; mod_start = None;
    mod_imports = []; mod_exports = [] }

let storage_module result_type memories tables instruction =
  storage_program result_type memories tables [instruction]

let execute_storage_module module_ =
  let host_state = Obj.repr () in
  let instantiated, message =
    Runner.interp_instantiate_wrapper host_state Runner.empty_store_record module_ []
  in
  let store, (frame, _) = match instantiated with
    | Some cfg -> cfg
    | None -> failwith ("core storage module instantiation: " ^ message)
  in
  let cfg = Runner.interp_cfg_of_wasm (store, (frame, [AI_invoke z])) in
  let rec step fuel hs cfg depth =
    if fuel = 0 then failwith "core storage module did not terminate";
    match Runner.run_one_step hs cfg depth with
    | RSC_normal (hs', cfg', depth') -> step (fuel - 1) hs' cfg' depth'
    | RSC_value (_, _, values) -> values
    | RSC_trap _ -> failwith "core storage module unexpectedly trapped"
    | RSC_invalid -> failwith "core storage module became invalid"
    | RSC_error -> failwith "core storage module execution error"
  in
  step 100 host_state cfg (n "100")

let () =
  let max64 = n "18446744073709551615" in
  let bytes = List.init 9 (fun _ -> Char.chr 255) @ [Char.chr 1] in
  check "decode u64 maximum"
    (match B.decode_address A.AT_i64 bytes with
     | Some (v, []) -> equal v max64 | _ -> false);
  check "actual parser u64 maximum"
    (match P.run_prefix A.AT_i64 bytes with
     | Some (v, []) -> equal v max64 | _ -> false);
  check "actual parser preserves suffix"
    (P.run_prefix A.AT_i64 (bytes @ [Char.chr 255]) =
       Some (max64, [Char.chr 255]));
  check "actual parser rejects excessive length"
    (P.run_prefix A.AT_i64
       (List.init 10 (fun _ -> Char.chr 128) @ [Char.chr 0]) = None);
  check "reject u64 overflow"
    (B.decode_address A.AT_i64
       (List.init 9 (fun _ -> Char.chr 128) @ [Char.chr 2]) = None);
  check "reject excessive LEB length"
    (B.decode_address A.AT_i64
       (List.init 10 (fun _ -> Char.chr 128) @ [Char.chr 0]) = None);
  check "accept legal noncanonical zero"
    (match B.decode_address A.AT_i64
       (List.init 9 (fun _ -> Char.chr 128) @ [Char.chr 0]) with
     | Some (v, []) -> equal v z | _ -> false);
  let lim = limits "4294967296" (Some "18446744073709551615") in
  check "wide limits round trip"
    (B.decode_limits (B.encode_limits A.AT_i64 lim) =
       Some ((A.AT_i64, lim), []));
  check "reject shared-memory flag in non-shared codec"
    (B.decode_limits [Char.chr 6; Char.chr 0; Char.chr 1] = None);
  check "address addition does not wrap"
    (A.effective_address A.AT_i64 max64 one one
       (n "18446744073709551616") = None);
  check "zero length past end is not in bounds"
    (not (A.range_valid (n "4294967297") z (n "4294967296")));
  check "mixed copy length is i32"
    (A.copy_address_type A.AT_i64 A.AT_i32 = A.AT_i32);
  let memory = memory_instance.m in
  let mt = A.{ memory_address_type = AT_i64;
               memory_limits = limits "1" (Some "2") } in
  let m = some "memory64 allocation" (M.allocate memory mt) in
  check "memory64 initial size" (equal (M.size memory m) one);
  check "memory64 high address bounds failure"
    (M.load_byte memory m (value A.AT_i64 "4294967296") z = None);
  check "memory64 rejects i32 operand"
    (M.load_byte memory m (value A.AT_i32 "0") z = None);
  check "memory64 reads zero-initialized bytes"
    (M.load_byte memory m (value A.AT_i64 "0") z =
       Some wasm_memory_default_byte);
  let m', old = some "memory64 growth"
      (M.grow memory m (value A.AT_i64 "1")) in
  check "memory64 growth size" (equal (M.size memory m') (n "2"));
  check "memory64 growth result"
    (A.address_of_value A.AT_i64 old = Some one);
  check "memory64 growth respects declared maximum"
    (M.grow memory m' (value A.AT_i64 "1") = None);
  check "memory64 growth rejects i32 operand"
    (M.grow memory m' (value A.AT_i32 "0") = None);
  check "memory64 new page initialized"
    (M.load_byte memory m' (value A.AT_i64 "65536") z =
       Some wasm_memory_default_byte);
  let large = some "memory64 sparse allocation above 4 GiB"
      (M.allocate memory A.{ memory_address_type = AT_i64;
       memory_limits = limits "65537" None }) in
  check "large allocation is exact, not truncated"
    (equal (M.size memory large) (n "65537"));
  check "large allocation reads above 4 GiB"
    (M.load_byte memory large (value A.AT_i64 "4294967296") z =
       Some wasm_memory_default_byte);
  let full = some "memory64 full-address-space allocation"
      (M.allocate memory A.{ memory_address_type = AT_i64;
       memory_limits = limits "281474976710656" None }) in
  check "full allocation has 2^48 pages"
    (equal (M.size memory full) (n "281474976710656"));
  check "full allocation reads last u64 byte"
    (M.load_byte memory full (value A.AT_i64 "18446744073709551615") z =
       Some wasm_memory_default_byte);
  check "full allocation rejects wrapping effective address"
    (M.load_byte memory full (value A.AT_i64 "18446744073709551615") one = None);
  check "full memory cannot grow beyond address width"
    (M.grow memory full (value A.AT_i64 "1") = None);
  (* These use the actual core type/allocation/growth/import operations,
     rather than the transitional AddressingMemory/AddressingTable wrappers. *)
  let core64 : memory_type =
    { mt_limits = limits "65537" (Some "65538"); mt_address_type = A.AT_i64 } in
  let core32 : memory_type =
    { mt_limits = core64.mt_limits; mt_address_type = A.AT_i32 } in
  check "core memory64 limits above 4 GiB are valid" (memtype_valid core64);
  check "core memory32 limits above 4 GiB are invalid" (not (memtype_valid core32));
  check "core memory imports distinguish address widths"
    (not (import_mem_subtyping core64 core32) &&
     not (import_mem_subtyping core32 core64));
  let core_instance = gen_mem_instance memory_instance core64 in
  check "core instantiation retains memory64 address type"
    (core_instance.meminst_type.mt_address_type = A.AT_i64);
  check "core instantiation does not truncate wide memory"
    (equal (memory.mem_length core_instance.meminst_data) (n "4295032832"));
  let core_grown = some "core memory64 growth above 4 GiB"
      (mem_grow0 memory_instance core_instance one) in
  check "core growth retains memory64 address type"
    (core_grown.meminst_type.mt_address_type = A.AT_i64);
  check "core growth respects memory64 maximum"
    (mem_grow0 memory_instance core_grown one = None);
  let core_tt64 : table_type =
    { tt_limits = limits "1" (Some "2"); tt_elem_type = T_funcref;
      tt_address_type = A.AT_i64 } in
  let core_tt32 : table_type =
    { core_tt64 with tt_address_type = A.AT_i32 } in
  check "core table imports distinguish address widths"
    (not (import_table_subtyping core_tt64 core_tt32) &&
     not (import_table_subtyping core_tt32 core_tt64));
  let core_table = gen_table_instance core_tt64 (VAL_ref_null T_funcref) in
  let core_table_grown = some "core table64 growth"
      (growtable core_table one (VAL_ref_func (n "8"))) in
  check "core table growth retains address type"
    (core_table_grown.tableinst_type.tt_address_type = A.AT_i64);
  check "core table64 growth rejects address overflow before allocation"
    (growtable core_table max64 (VAL_ref_null T_funcref) = None);
  let full_core64 : memory_type =
    { mt_limits = limits "281474976710656" None; mt_address_type = A.AT_i64 } in
  check "actual core interpreter memory64.size returns i64 without narrowing"
    (execute_storage_module
       (storage_module T_i64 [full_core64] [] (BI_memory_size z)) =
       [Utility.vali64_of_Z (n "281474976710656")]);
  check "actual core interpreter table64.size returns i64"
    (execute_storage_module
       (storage_module T_i64 [] [core_tt64] (BI_table_size z)) =
       [Utility.vali64_of_Z one]);
  let bad_size, _ =
    Runner.interp_instantiate_wrapper (Obj.repr ()) Runner.empty_store_record
      (storage_module T_i32 [core64] [] (BI_memory_size z)) []
  in
  check "core validator rejects i32 result for memory64.size" (bad_size = None);
  let bad_table_size, _ =
    Runner.interp_instantiate_wrapper (Obj.repr ()) Runner.empty_store_record
      (storage_module T_i32 [] [core_tt64] (BI_table_size z)) []
  in
  check "core validator rejects i32 result for table64.size" (bad_table_size = None);
  let delta64 s = BI_const_num (value A.AT_i64 s) in
  check "actual core memory64.grow returns previous size as i64"
    (execute_storage_module
       (storage_program T_i64 [core64] []
          [delta64 "1"; BI_memory_grow z]) =
       [Utility.vali64_of_Z (n "65537")]);
  check "actual core memory64.grow updates size above 4 GiB"
    (execute_storage_module
       (storage_program T_i64 [core64] []
          [delta64 "1"; BI_memory_grow z; BI_drop; BI_memory_size z]) =
       [Utility.vali64_of_Z (n "65538")]);
  check "actual core memory64.grow failure returns i64 minus one"
    (execute_storage_module
       (storage_program T_i64 [core64] []
          [delta64 "2"; BI_memory_grow z]) =
       [Utility.vali64_of_Z (n "-1")]);
  check "actual core memory64.grow does not narrow a large delta"
    (execute_storage_module
       (storage_program T_i64 [core64] []
          [delta64 "4294967296"; BI_memory_grow z]) =
       [Utility.vali64_of_Z (n "-1")]);
  check "actual core memory64.grow zero at full capacity is exact"
    (execute_storage_module
       (storage_program T_i64 [full_core64] []
          [delta64 "0"; BI_memory_grow z]) =
       [Utility.vali64_of_Z (n "281474976710656")]);
  let bad_delta, _ =
    Runner.interp_instantiate_wrapper (Obj.repr ()) Runner.empty_store_record
      (storage_program T_i64 [core64] []
         [BI_const_num (value A.AT_i32 "1"); BI_memory_grow z]) []
  in
  check "core validator rejects i32 delta for memory64.grow" (bad_delta = None);
  let byte s = Byte.repr (n s) in
  let fill_one data at b = some "memory64 fill"
      (U.fill memory_instance data (value A.AT_i64 at)
         (value A.AT_i64 "1") (byte b)) in
  let filled = fill_one (fill_one (fill_one m' "0" "1") "1" "2") "2" "3" in
  check "memory64 fill writes selected byte"
    (M.load_byte memory filled (value A.AT_i64 "1") z = Some (byte "2"));
  check "memory64 fill rejects i32 length"
    (U.fill memory_instance filled (value A.AT_i64 "0")
       (value A.AT_i32 "1") (byte "4") = None);
  let copied = some "overlapping self-copy"
      (U.copy memory_instance filled filled (value A.AT_i64 "1")
         (value A.AT_i64 "0") (value A.AT_i64 "3")) in
  check "overlapping self-copy uses original source"
    (M.load_byte memory copied (value A.AT_i64 "2") z = Some (byte "2") &&
     M.load_byte memory copied (value A.AT_i64 "3") z = Some (byte "3"));
  check "copy source bounds checked before writes"
    (U.copy memory_instance filled filled (value A.AT_i64 "0")
       (value A.AT_i64 "131072") (value A.AT_i64 "1") = None);
  check "zero-length copy at end"
    (U.copy memory_instance filled filled (value A.AT_i64 "131072")
       (value A.AT_i64 "131072") (value A.AT_i64 "0") <> None);
  check "zero-length copy past end traps"
    (U.copy memory_instance filled filled (value A.AT_i64 "131072")
       (value A.AT_i64 "131073") (value A.AT_i64 "0") = None);
  let m32 = some "memory32 allocation"
      (M.allocate memory A.{ memory_address_type = AT_i32;
                            memory_limits = limits "1" None }) in
  let m32 = some "memory32 fill"
      (U.fill memory_instance m32 (value A.AT_i32 "0")
         (value A.AT_i32 "1") (byte "7")) in
  let mixed = some "mixed-width copy"
      (U.copy memory_instance filled m32 (value A.AT_i64 "5")
         (value A.AT_i32 "0") (value A.AT_i32 "1")) in
  check "mixed-width copy result"
    (M.load_byte memory mixed (value A.AT_i64 "5") z = Some (byte "7"));
  check "mixed-width copy rejects i64 length"
    (U.copy memory_instance filled m32 (value A.AT_i64 "5")
       (value A.AT_i32 "0") (value A.AT_i64 "1") = None);
  let tt = A.{ table_address_type = AT_i64;
               table_limits = limits "2" (Some "3");
               table_element_type = T_funcref } in
  let t = some "table64 allocation" (T.allocate tt) in
  check "table64 null initialization"
    (T.get t (value A.AT_i64 "1") = Some (VAL_ref_null T_funcref));
  check "table64 high index bounds failure"
    (T.get t (value A.AT_i64 "18446744073709551615") = None);
  check "table64 rejects i32 index"
    (T.get t (value A.AT_i32 "1") = None);
  let t' = some "table64 set"
      (T.set t (value A.AT_i64 "1") (VAL_ref_func (n "7"))) in
  check "table64 get after set"
    (T.get t' (value A.AT_i64 "1") = Some (VAL_ref_func (n "7")));
  let t'', old = some "table64 grow"
      (T.grow t' (value A.AT_i64 "1") (VAL_ref_func (n "8"))) in
  check "table64 grow result"
    (A.address_of_value A.AT_i64 old = Some (n "2"));
  check "table64 growth preserves old elements"
    (T.get t'' (value A.AT_i64 "1") = Some (VAL_ref_func (n "7")));
  check "table64 growth initializes new elements"
    (T.get t'' (value A.AT_i64 "2") = Some (VAL_ref_func (n "8")));
  check "table64 growth respects declared maximum"
    (T.grow t'' (value A.AT_i64 "1") (VAL_ref_null T_funcref) = None);
  let original = Parray.set_gen (Parray.make 4 0) 0 4 (fun i -> i + 1) in
  let snapshot_copy = Parray.set_gen original 1 3 (Parray.get original) in
  check "native block generator sees source snapshot"
    (List.init 4 (Parray.get snapshot_copy) = [1; 1; 2; 3]);
  check "native block update preserves source version"
    (List.init 4 (Parray.get original) = [1; 2; 3; 4]);
  let newer = Parray.set original 0 9 in
  let rerooted = Parray.set_gen newer 1 2 (Parray.get original) in
  check "native generator can read another persistent version"
    (List.init 4 (Parray.get rerooted) = [9; 1; 2; 4]);
  let failed =
    try
      ignore (Parray.set_gen newer 1 2
        (fun i -> if i = 1 then failwith "generator exception" else 7));
      false
    with Failure _ -> true
  in
  check "native generator exception leaves destination unchanged"
    (failed && List.init 4 (Parray.get newer) = [9; 2; 3; 4]);
  check "native block bounds do not overflow"
    (List.init 4 (Parray.get (Parray.set_gen newer max_int 2 (fun _ -> 7))) =
       [9; 2; 3; 4]);
  Printf.printf "Addressing extracted API regressions: %d/%d passed\n" !count !count
