(** Structural-domain regression: mixed recursive code, nonempty rich locals,
    an indexed call opcode and a maximum u64 offset. This is a byte-codec
    theorem, NOT validation of this deliberately untyped source body. *)
From Stdlib Require Import List NArith Lia.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  gc_types binary_locals_printer_properties binary_memory_properties
  binary_format_type_properties binary_format_print_encoding
  binary_format_expression_print tail_call_code_properties.
Close Scope N_scope.

Definition shared_composition_locals :=
  T_ref (Ref_type false HT_i31) :: T_num T_i32 :: nil.

Definition shared_composition_body :=
  BI_block (BT_id 64%N) nil ::
  BI_load T_i32 None (Build_memarg 18446744073709551615%N 0%N 0%N) ::
  BI_call_ref 0%N :: BI_return_call_indirect 1%N 128%N :: nil.

Lemma shared_composition_body_structural_domain :
  expression_binary_wf shared_composition_body.
Proof.
  apply EBW_cons.
  - apply IBW_block; [unfold block_type_binary_wf; lia |constructor].
  - apply EBW_cons.
    + apply IBW_atomic, ABW_memory.
      change (encodable_memory_instruction
        (scalar_memop_build SM_i32_load
          (Build_memarg 18446744073709551615%N 0%N 0%N))).
      apply EMI_scalar; vm_compute; reflexivity.
    + apply EBW_cons.
      * apply IBW_atomic, ABW_call_ref; unfold binary_index_wf; lia.
      * apply EBW_cons.
        -- apply IBW_atomic, ABW_return_call_indirect; unfold binary_index_wf; lia.
        -- constructor.
Qed.

Example shared_mixed_nonempty_local_code_roundtrip :
  binary_format_parser.run
    (binary_of_code (Build_module_func 0%N
      shared_composition_locals shared_composition_body))
    (fun _ => parse_code) =
  Some (shared_composition_locals, shared_composition_body).
Proof.
  apply code_locals_roundtrip_from_shared.
  - vm_compute; reflexivity.
  - constructor.
    + exists {| art_nullable := false; art_heap := AH_i31 |}. reflexivity.
    + constructor; [exact I |constructor].
  - exact shared_composition_body_structural_domain.
  - vm_compute; discriminate.
Qed.
