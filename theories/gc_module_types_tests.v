From Wasm Require Import datatypes binary_format_parser binary_format_printer
  gc_type_context gc_declaration_typing.
From Stdlib Require Import List NArith.
Import ListNotations.
Open Scope N_scope.

Definition gc_recursive_module : module := {|
  mod_types :=
    [[Sub_type false [] (Comp_struct
        [{| field_mutability := MUT_const;
            field_storage := ST_value (T_ref (Ref_type true (HT_type 1))) |}]);
      Sub_type true [] (Comp_array
        {| field_mutability := MUT_var;
           field_storage := ST_packed PT_i16 |})];
     [Sub_type true [] (Comp_func (Tf [] [T_num T_i32]))]];
  mod_funcs := []; mod_tables := []; mod_mems := []; mod_globals := [];
  mod_elems := []; mod_datas := []; mod_start := None;
  mod_imports := []; mod_exports := []; mod_tags := [];
|}.

Example gc_recursive_module_actual_binary_roundtrip :
  run_parse_module (binary_of_module gc_recursive_module) = Some gc_recursive_module.
Proof. vm_compute. reflexivity. Qed.

Example gc_recursive_module_closes :
  exists registry ids,
    close_and_validate_type_groups [] gc_recursive_module.(mod_types) =
      Some (registry, ids) /\
    ids = [Def_type 0 0; Def_type 0 1; Def_type 1 0] /\
    source_type_identitiesb registry ids
      (List.concat gc_recursive_module.(mod_types)) ids = true.
Proof. vm_compute. eexists. eexists. repeat split; reflexivity. Qed.

Definition gc_declared_module : module := {|
  mod_types :=
    [[Sub_type false [] (Comp_struct [])];
     [Sub_type true [0] (Comp_struct
       [{| field_mutability := MUT_const; field_storage := ST_packed PT_i8 |}])]];
  mod_funcs := []; mod_tables := []; mod_mems := []; mod_globals := [];
  mod_elems := []; mod_datas := []; mod_start := None;
  mod_imports := []; mod_exports := []; mod_tags := [];
|}.

Example gc_declared_module_actual_binary_roundtrip :
  run_parse_module (binary_of_module gc_declared_module) = Some gc_declared_module.
Proof. vm_compute. reflexivity. Qed.
