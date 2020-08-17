
module type Host = sig
    include Extract.Executable_Host
    val show_host_function : host_function -> string
  end

module DummyHost = struct
    include Extract.DummyHost
    let show_host_function _ = assert false
  end

module type InterpreterType = sig

    module Host : Host
    include module type of Host

    type store_record = host_function Extract.store_record
    type config_tuple = host_function Extract.config_tuple
    type res_tuple = host_function Extract.res_tuple

    val run_v :
      int -> Extract.instance -> config_tuple ->
      (store_record * Extract.res) host_event

    val run_step :
      int -> Extract.instance -> config_tuple ->
      host_function Extract.res_tuple host_event

    val lookup_exported_function :
      string -> ((store_record * Extract.instance) * Extract.module_export list) ->
      config_tuple option

    val interp_instantiate_wrapper :
      Extract.module0 ->
      (((store_record * Extract.instance) * Extract.module_export list) * int option) option

    val pp_values : Extract.value0 list -> string
    val pp_store : int -> store_record -> string
    val pp_res_tuple_except_store : res_tuple -> string
    val pp_config_tuple_except_store : config_tuple -> string

  end


(** We set the target monad to be exactly the host events.
   This is not possible in Coq due to universe inconsistencies as it might in some very specific
   cases yield an infinite computation.
   It is not an issue in OCaml to have infinite computations. *)
module TargetMonad =
  functor (EH : Extract.Executable_Host) -> struct

    type 'v monad = 'v EH.host_event

    let monad_ret = EH.host_ret
    let monad_bind = EH.host_bind

    let convert x = x

    let rec monad_iter f x =
      monad_bind (f x) (function
        | Extract.Inl y -> monad_iter f y
        | Extract.Inr r -> monad_ret r)

  end

module Interpreter =
  functor (EH : Host) -> struct

    module Host = EH
    include Host

    module Interpreter = Extract.Interpreter (EH) (TargetMonad (EH))
    module Instantiation = Extract.Instantiation (EH)
    module PP = Extract.PP (EH)

    type store_record = host_function Extract.store_record
    type config_tuple = host_function Extract.config_tuple
    type res_tuple = host_function Extract.res_tuple

    let run_v d i cfg = Interpreter.run_v (Convert.to_nat d) i cfg

    let run_step d i cfg = Interpreter.run_step (Convert.to_nat d) i cfg

    let lookup_exported_function name =
      Instantiation.lookup_exported_function (Utils.explode name)

    let interp_instantiate_wrapper m =
      Option.map (fun (store_inst_exps, start) ->
          (store_inst_exps, Option.map Convert.from_nat start))
        (Interpreter.itree_to_option (fun _ _ _ ->
          (* Normally, this interaction tree should already have been evaluated at this point. *)
            assert false)
          (Instantiation.interp_instantiate_wrapper m))

    let show_host_function_char_list h = Utils.explode (show_host_function h)

    let pp_values l =
      Utils.implode (PP.pp_values l)

    let pp_store i st =
      Utils.implode (PP.pp_store (Convert.to_nat i) st)

    let pp_res_tuple_except_store r =
      Utils.implode (PP.pp_res_tuple_except_store show_host_function_char_list r)

    let pp_config_tuple_except_store cfg =
      Utils.implode (PP.pp_config_tuple_except_store show_host_function_char_list cfg)

  end

