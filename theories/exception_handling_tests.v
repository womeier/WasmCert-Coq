(** Kernel and binary-immediate tests, not end-to-end EH conformance tests. *)
From Stdlib Require Import List NArith Init.Byte.
From Wasm Require Import operations exception_handling exception_binary.
Import ListNotations EH EHBinary.
Open Scope N_scope.

Definition sample_exception : exception nat :=
  {| exception_tag := 7%N; exception_fields := [11; 22]%nat |}.

Example catch_payload :
  dispatch 3 sample_exception [Handle 7 2] =
  Some {| branch_label := 2%N;
          branch_values := [Payload 11%nat; Payload 22%nat] |}.
Proof. vm_compute; reflexivity. Qed.

Example catch_reference_after_payload :
  dispatch 3 sample_exception [Handle_ref 7 2] =
  Some {| branch_label := 2%N;
          branch_values := [Payload 11%nat; Payload 22%nat; Exn_ref 3%N] |}.
Proof. vm_compute; reflexivity. Qed.

Example catch_all_discards_payload :
  dispatch 3 sample_exception [Handle_all 5] =
  Some {| branch_label := 5%N; branch_values := [] |}.
Proof. vm_compute; reflexivity. Qed.

Example catch_all_ref_discards_payload :
  dispatch 3 sample_exception [Handle_all_ref 5] =
  Some {| branch_label := 5%N; branch_values := [Exn_ref 3%N] |}.
Proof. vm_compute; reflexivity. Qed.

Example catch_skips_wrong_identity :
  dispatch 3 sample_exception [Handle 0 0; Handle_all 5] =
  Some {| branch_label := 5%N; branch_values := [] |}.
Proof. vm_compute; reflexivity. Qed.

Example first_clause_wins :
  dispatch 3 sample_exception [Handle_all 5; Handle_ref 7 2] =
  Some {| branch_label := 5%N; branch_values := [] |}.
Proof. vm_compute; reflexivity. Qed.

Example duplicate_tag_first_wins :
  dispatch 3 sample_exception [Handle 7 2; Handle 7 4] =
  Some {| branch_label := 2%N;
          branch_values := [Payload 11%nat; Payload 22%nat] |}.
Proof. vm_compute; reflexivity. Qed.

Example unmatched_exception_propagates :
  dispatch 3 sample_exception [Handle 6 0; Handle_ref 8 1] = None.
Proof. vm_compute; reflexivity. Qed.

Example nearest_table_wins :
  unwind 3 sample_exception [[Handle_ref 7 2]; [Handle_all 5]] =
  Some (0%nat, {| branch_label := 2%N;
                  branch_values :=
                    [Payload 11%nat; Payload 22%nat; Exn_ref 3%N] |}).
Proof. vm_compute; reflexivity. Qed.

Example unwind_empty_and_unmatched_tables :
  unwind 3 sample_exception [ []; [Handle 0 0]; [Handle_all_ref 5] ] =
  Some (2%nat, {| branch_label := 5%N; branch_values := [Exn_ref 3%N] |}).
Proof. vm_compute; reflexivity. Qed.

Example no_enclosing_handler :
  unwind 3 sample_exception [ []; [Handle 0 0] ] = None.
Proof. vm_compute; reflexivity. Qed.

Example null_throw_ref_traps : throw_ref None = Throw_trap.
Proof. reflexivity. Qed.

Example throw_ref_preserves_identity :
  throw_ref (Some 37%N) = Throw_exception 37%N.
Proof. reflexivity. Qed.

Example resolve_module_indices :
  resolve_catches [42%N; 7%N] [Catch_ref 1 2; Catch_all 3] =
  Some [Handle_ref 7 2; Handle_all 3].
Proof. vm_compute; reflexivity. Qed.

Example imported_tag_aliases :
  resolve_catches [7%N; 7%N] [Catch 0 2; Catch 1 3] =
  Some [Handle 7 2; Handle 7 3].
Proof. vm_compute; reflexivity. Qed.

Example unknown_tag_rejected :
  resolve_catches [7%N] [Catch_all 0; Catch 1 2] = None.
Proof. vm_compute; reflexivity. Qed.

Example tag_signature_without_results :
  tag_parameters (Tf [T_num T_i32] []) = Some [T_num T_i32].
Proof. reflexivity. Qed.

Example tag_signature_results_rejected :
  tag_parameters (Tf [] [T_num T_i32]) = None.
Proof. reflexivity. Qed.

Example unresolved_type_rejected : resolve_tag_type [] 0 = None.
Proof. reflexivity. Qed.

Example tag_import_checks_signature :
  tag_import_matches [[T_num T_i32]] 0 [T_num T_i32] = true /\
  tag_import_matches [[T_num T_i32]] 0 [] = false /\
  tag_import_matches [[T_num T_i32]] 1 [T_num T_i32] = false.
Proof. vm_compute; auto. Qed.

Example equal_signatures_distinct_identities :
  snd (alloc_tag [] []) = 0%N /\
  snd (alloc_tag (fst (alloc_tag [] [])) []) = 1%N.
Proof. vm_compute; auto. Qed.

Example allocate_exception :
  alloc_exception [sample_exception] sample_exception =
  ([sample_exception; sample_exception], 1%N).
Proof. vm_compute; reflexivity. Qed.

Example read_unsigned_zero : read_u32 [x00; xff] = Some (0%N, [xff]).
Proof. vm_compute; reflexivity. Qed.

Example read_unsigned_nonminimal_zero :
  read_u32 [x80; x80; x80; x80; x00; xff] = Some (0%N, [xff]).
Proof. vm_compute; reflexivity. Qed.

Example read_unsigned_max :
  read_u32 [xff; xff; xff; xff; x0f; xaa] =
  Some (4294967295%N, [xaa]).
Proof. vm_compute; reflexivity. Qed.

Example reject_unsigned_overflow :
  read_u32 [xff; xff; xff; xff; x10] = None.
Proof. vm_compute; reflexivity. Qed.

Example reject_unsigned_six_bytes :
  read_u32 [x80; x80; x80; x80; x80; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example reject_unsigned_truncation : read_u32 [x80] = None.
Proof. vm_compute; reflexivity. Qed.

Example catch_binary_roundtrip :
  read_catch (binary_of_catch (Catch 128 4294967295) ++ [xff]) =
  Some (Catch 128 4294967295, [xff]).
Proof. vm_compute; reflexivity. Qed.

Example catch_ref_binary_roundtrip :
  read_catch (binary_of_catch (Catch_ref 16384 127)) =
  Some (Catch_ref 16384 127, []).
Proof. vm_compute; reflexivity. Qed.

Example catch_all_binary_roundtrip :
  read_catch (binary_of_catch (Catch_all 0)) = Some (Catch_all 0, []).
Proof. vm_compute; reflexivity. Qed.

Example catch_all_ref_binary_roundtrip :
  read_catch (binary_of_catch (Catch_all_ref 4294967295)) =
  Some (Catch_all_ref 4294967295, []).
Proof. vm_compute; reflexivity. Qed.

Example reject_unknown_catch_discriminant :
  read_catch [x04; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example reject_legacy_catch_opcode :
  read_catch [x07; x00; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example reject_missing_catch_label : read_catch [x00; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example reject_oversized_catch_tag :
  read_catch [x00; xff; xff; xff; xff; x10; x00] = None.
Proof. vm_compute; reflexivity. Qed.

Example reject_oversized_catch_label :
  read_catch [x03; xff; xff; xff; xff; x10] = None.
Proof. vm_compute; reflexivity. Qed.
