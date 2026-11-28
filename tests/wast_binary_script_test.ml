open Wast_binary_script

let check name condition =
  if not condition then failwith ("binary script dispatch: " ^ name)

let () =
  let original = "(module definition $D binary \"\\00\\61\\73\\6d\")" in
  let prepared, directives = prepare original in
  check "definition recognised" (directives = [Define (Some "$D")]);
  check "locations retained" (String.length original = String.length prepared);
  check "legacy parser still parses the command"
    (List.length (Wasm.Parse.Script.parse_string prepared) = 1);
  let source = ";; (module definition)\n(; (; module definition ;) ;)\n\
    (register \"(module definition)\")\n\
    (module definition binary \"\\00\")" in
  let _, directives = prepare source in
  check "comments and strings are not directives" (directives = [Ordinary; Define None]);
  let prepared, directives = prepare
    "(module instance $A $D)\n(module instance $D)\n(module instance)" in
  check "all instance dispatch forms retained"
    (directives = [Instantiate (Some "$D"); Instantiate (Some "$D"); Instantiate None]);
  check "instance placeholders parse"
    (List.length (Wasm.Parse.Script.parse_string prepared) = 3);
  let source = "(module definition $D (memory i64 1))" in
  check "text module definitions are not extended" (prepare source = (source, [Ordinary]));
  List.iter (fun source ->
    let rejected = try ignore (prepare source); false with Failure _ -> true in
    check "malformed script fails" rejected)
    ["(module"; "(;"; "(module binary \"unterminated)"; ")"];
  Printf.printf "Binary script dispatch regressions passed\n"
