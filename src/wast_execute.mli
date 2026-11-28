(** Execution of Wast testing script from string. **)
val run_wast_string: Output.verbosity -> int -> int -> string -> unit Execute.Host.host_event

(** Reuse the existing spectest host and command timeout in binary-script tests. *)
val register_spectest_host :
  Output.verbosity -> Execute.host_extern_store -> Execute.Interpreter.store_record ->
  (Execute.host_extern_store * Execute.Interpreter.store_record) Execute.Host.host_event
val with_timeout : int -> (unit -> 'a) -> 'a
