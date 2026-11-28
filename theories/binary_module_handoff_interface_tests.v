(** Applied-interface audit of the selective ea96c78/bc7c190 integration.
    These statements mention the actual production parser/printer and the
    extraction functor's entry point. There is no Atom or memory-parser
    correctness premise left to instantiate. Encodability is not validation. *)
From Stdlib Require Import List Strings.String Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_parser_combinator_properties binary_format_dispatch_properties
  binary_format_module_grammar binary_format_module_roundtrip
  binary_format_module_complete binary_memory_grammar_properties
  extraction_instance.

Theorem integrated_memory_dispatch_sound n :
  parser_sound
    (parse_memory_instruction
      (Toks := SizedList Byte.byte) (M := option) (n := n))
    binary_memory_instruction.
Proof. exact (parse_memory_instruction_binary_sound n). Qed.

Theorem integrated_module_bytes_iff bytes modul :
  binary_format_parser.run_parse_module bytes = Some modul <->
  module_binary_encoding bytes modul.
Proof. exact (run_parse_module_general_correct bytes modul). Qed.

Theorem integrated_module_bytes_rejected bytes :
  binary_format_parser.run_parse_module bytes = None <->
  forall modul, ~ module_binary_encoding bytes modul.
Proof. exact (run_parse_module_general_rejected bytes). Qed.

Theorem integrated_module_printer_roundtrip modul :
  module_binary_wf modul ->
  binary_format_parser.run_parse_module (binary_of_module modul) = Some modul.
Proof. exact (binary_of_module_roundtrip modul). Qed.

Module AppliedExtractionParserAudit (PH : Parametric_host).
  Module Runtime := Extraction_instance PH.

  Theorem actual_extraction_parser_iff source modul :
    Runtime.run_parse_module_str source = Some modul <->
    module_binary_encoding (String.list_byte_of_string source) modul.
  Proof. exact (run_parse_module_str_general_correct source modul). Qed.

  Theorem actual_extraction_parser_rejected source :
    Runtime.run_parse_module_str source = None <->
    forall modul,
      ~ module_binary_encoding (String.list_byte_of_string source) modul.
  Proof. exact (run_parse_module_str_general_rejected source). Qed.

  Theorem actual_extraction_printer_roundtrip modul :
    module_binary_wf modul ->
    Runtime.run_parse_module_str
      (String.string_of_list_byte (binary_of_module modul)) = Some modul.
  Proof. exact (binary_of_module_string_roundtrip modul). Qed.
End AppliedExtractionParserAudit.
