(* Binary-only script dispatch for module definitions and instances. This
   does not parse or extend text-format module fields/instructions. The
   legacy script parser still parses every command and every binary string.
   Neutralised tokens retain their width, so source locations are preserved. *)
type directive =
  | Ordinary
  | Define of string option
  | Instantiate of string option
  | Expect_null of int list

let prepare source =
  let length = String.length source in
  let output = Bytes.of_string source in
  let directives = ref [] in
  let depth = ref 0 in
  let heads = ref [] in
  let direct_group = ref (-1) in
  let group_atoms = ref [] in
  let null_results = ref [] in
  let starts i s =
    i + String.length s <= length &&
    String.sub source i (String.length s) = s in
  let erase (_, start, stop) =
    for i = start to stop - 1 do Bytes.set output i ' ' done in
  let is_var (s, _, _) = String.length s > 0 && s.[0] = '$' in
  let word (s, _, _) = s in
  let finish () =
    let directive = match List.rev !heads with
    | ("module", _, _) :: (("definition", _, _) as keyword) :: rest ->
        begin match rest with
        | ("binary", _, _) :: _ -> erase keyword; Define None
        | name :: ("binary", _, _) :: _ when is_var name ->
            erase keyword; Define (Some (word name))
        | _ -> Ordinary (* Deferred text definitions remain unsupported. *)
        end
    | ("module", _, _) :: (("instance", _, _) as keyword) :: rest ->
        begin match rest with
        | [] -> erase keyword; Instantiate None
        | [target] when is_var target ->
            erase keyword; erase target; Instantiate (Some (word target))
        | [name; target] when is_var name && is_var target ->
            erase keyword; erase target; Instantiate (Some (word target))
        | _ -> Ordinary
        end
    | ("assert_return", _, _) :: _ when !null_results <> [] ->
        Expect_null (List.rev !null_results)
    | _ -> Ordinary in
    directives := directive :: !directives;
    heads := [];
    direct_group := -1;
    group_atoms := [];
    null_results := [] in
  let finish_group () =
    match List.rev !heads, !group_atoms with
    | ("assert_return", _, _) :: _, [("ref.null", start, stop)]
      when !direct_group > 0 ->
        (* Legacy RefTypePat is only a syntactic carrier. Dispatch matches
           the original any-null result, not the non-null placeholder. *)
        assert (stop - start = 8);
        Bytes.blit_string "ref.func" 0 output start 8;
        null_results := (!direct_group - 1) :: !null_results
    | _ -> () in
  let rec string i =
    if i >= length then failwith "Unterminated WAST string"
    else match source.[i] with
    | '"' -> i + 1
    | '\\' -> string (i + 2)
    | _ -> string (i + 1) in
  let rec comment nesting i =
    if i >= length then failwith "Unterminated WAST block comment"
    else if starts i "(;" then comment (nesting + 1) (i + 2)
    else if starts i ";)" then
      if nesting = 1 then i + 2 else comment (nesting - 1) (i + 2)
    else comment nesting (i + 1) in
  let rec line i =
    if i >= length || source.[i] = '\n' then i else line (i + 1) in
  let rec atom i =
    if i >= length then i
    else match source.[i] with
    | ' ' | '\t' | '\n' | '\r' | '(' | ')' | '"' -> i
    | _ -> atom (i + 1) in
  let rec scan i =
    if i >= length then ()
    else if starts i ";;" then scan (line (i + 2))
    else if starts i "(;" then scan (comment 1 (i + 2))
    else match source.[i] with
    | '"' -> scan (string (i + 1))
    | '(' ->
        if !depth = 1 then begin incr direct_group; group_atoms := [] end;
        incr depth; scan (i + 1)
    | ')' ->
        if !depth = 2 then finish_group ();
        decr depth;
        if !depth < 0 then failwith "Unmatched WAST closing parenthesis";
        if !depth = 0 then finish ();
        scan (i + 1)
    | ' ' | '\t' | '\n' | '\r' -> scan (i + 1)
    | _ ->
        let stop = atom i in
        if !depth = 1 then
          heads := (String.sub source i (stop - i), i, stop) :: !heads;
        if !depth = 2 then
          group_atoms := (String.sub source i (stop - i), i, stop) :: !group_atoms;
        scan stop in
  scan 0;
  if !depth <> 0 then failwith "Unterminated WAST command";
  Bytes.to_string output, List.rev !directives
