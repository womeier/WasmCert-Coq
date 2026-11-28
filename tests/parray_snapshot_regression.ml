(* Actual mutable Parray implementation versus immutable list snapshots.
   These regressions are not a proof of OCaml/Obj/reroot semantics. *)
exception Injected_failure

let checks = ref 0
let check name condition =
  if not condition then failwith ("Parray snapshot: " ^ name);
  incr checks

let contents p = List.init (Parray.length p) (Parray.get p)
let write before dst values =
  List.mapi (fun i old ->
    if i >= dst && i - dst < List.length values
    then List.nth values (i - dst) else old) before

let snapshot name actual expected =
  check (name ^ " contents") (contents actual = expected);
  check (name ^ " length") (Parray.length actual = List.length expected);
  check (name ^ " default") (Parray.default actual = 0);
  check (name ^ " out of bounds")
    (Parray.get actual (-1) = 0 && Parray.get actual (List.length expected) = 0)

let () =
  (* This exact first check fails on the pre-44270f7 production implementation:
     its result is [1;1;1;1], even though it recovers the original source. *)
  let p = Parray.of_array [|1; 2; 3; 4|] 0 in
  let q = Parray.set_gen p 1 3 (fun i -> Parray.get p i) in
  snapshot "old overlapping-copy corruption" q [1; 1; 2; 3];
  snapshot "overlapping source persists" p [1; 2; 3; 4];

  for size = 0 to 12 do
    let before = List.init size (fun i -> i + 1) in
    for src = 0 to size do
      for dst = 0 to size do
        for len = 0 to size - max src dst do
          let base = Parray.of_array (Array.of_list before) 0 in
          let values = List.init len (fun i -> List.nth before (src + i)) in
          let result = Parray.set_gen base dst len (fun i -> Parray.get base (src + i)) in
          snapshot "exhaustive small self-copy" result (write before dst values);
          snapshot "exhaustive retained source" base before
        done
      done
    done
  done;

  (* Updated and BlockUpdated edges share backing storage. Each generator read
     may reroot a different node, including its last read before the write. *)
  let base = Parray.of_array [|1; 2; 3; 4; 5; 6; 7; 8|] 0 in
  let point = Parray.set base 0 40 in
  let block = Parray.set_gen point 4 2 (fun i -> 50 + i) in
  let result = Parray.set_gen point 1 4 (fun i ->
    if i mod 2 = 0 then Parray.get base (i + 1) else Parray.get block (i + 2)) in
  snapshot "cross-version generated result" result [40; 2; 4; 4; 51; 6; 7; 8];
  snapshot "cross-version old root" base [1; 2; 3; 4; 5; 6; 7; 8];
  snapshot "cross-version point" point [40; 2; 3; 4; 5; 6; 7; 8];
  snapshot "cross-version block" block [40; 2; 3; 4; 50; 51; 7; 8];
  snapshot "cross-version reroot result again" result [40; 2; 4; 4; 51; 6; 7; 8];

  (* A callback exception must not leave partial destination writes. Reads of
     shared versions are included so recovery cannot rely on a root staying put. *)
  let failed = ref false in
  (try
     ignore (Parray.set_gen point 1 4 (fun i ->
       let value = Parray.get block (i + 1) in
       if i = 2 then raise Injected_failure else value + 100))
   with Injected_failure -> failed := true);
  check "injected exception propagated" !failed;
  snapshot "exception destination atomicity" point [40; 2; 3; 4; 5; 6; 7; 8];
  snapshot "exception source persistence" block [40; 2; 3; 4; 50; 51; 7; 8];
  snapshot "exception retained result" result [40; 2; 4; 4; 51; 6; 7; 8];
  snapshot "exception oldest source" base [1; 2; 3; 4; 5; 6; 7; 8];

  let calls = ref 0 in
  List.iter (fun (start, len) ->
    let before = contents point in
    let after = Parray.set_gen point start len (fun _ -> incr calls; 99) in
    check "invalid/empty range does not invoke generator" (!calls = 0);
    check "invalid/empty range returns original version" (after == point);
    snapshot "invalid/empty range preserves data" after before)
    [(-1, 1); (9, 1); (8, 1); (7, 2); (max_int, 1);
     (1, max_int); (max_int, max_int); (min_int, max_int);
     (0, 0); (8, 0); (max_int, 0); (0, -1)];

  let copied = Parray.copy block in
  let grown = Parray.make_copy 12 0 block 6 in
  snapshot "copy content" copied [40; 2; 3; 4; 50; 51; 7; 8];
  snapshot "growth copied only initialized prefix" grown
    [40; 2; 3; 4; 50; 51; 0; 0; 0; 0; 0; 0];
  let changed = Parray.set_gen copied 0 3 (fun i -> Parray.get grown (i + 3)) in
  snapshot "independent backing copy update" changed [4; 50; 51; 4; 50; 51; 7; 8];
  snapshot "independent backing old copy" copied [40; 2; 3; 4; 50; 51; 7; 8];
  snapshot "independent backing original" block [40; 2; 3; 4; 50; 51; 7; 8];

  (* Deterministic branching histories; verify every retained version repeatedly
     in alternating orders, not just the most recent root. *)
  let random = Random.State.make [|0x44270; 0x3|] in
  let versions = ref [base, [1; 2; 3; 4; 5; 6; 7; 8]] in
  for step = 0 to 95 do
    let pick () = List.nth !versions (Random.State.int random (List.length !versions)) in
    let dest, before = pick () in
    let source, model_source = pick () in
    let start = Random.State.int random 9 in
    let len = Random.State.int random (9 - start) in
    let offset = Random.State.int random (9 - len) in
    let actual, expected =
      if step mod 3 = 0 then
        let at = Random.State.int random 8 in
        let byte = 1000 + step in
        Parray.set dest at byte, write before at [byte]
      else
        Parray.set_gen dest start len (fun i -> Parray.get source (offset + i)),
        write before start (List.init len (fun i -> List.nth model_source (offset + i)))
    in
    versions := (actual, expected) :: !versions;
    let order = if step mod 2 = 0 then !versions else List.rev !versions in
    List.iter (fun (p, model) -> snapshot "branching retained history" p model) order
  done;
  Printf.printf "Parray snapshot regression: %d/%d checks passed\n" !checks !checks
