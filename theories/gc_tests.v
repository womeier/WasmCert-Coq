(** Executable regression checks for the GC foundation, not a claim that the
    module parser/interpreter accepts GC modules yet. *)
From Wasm Require Import datatypes gc_types gc_numerics gc_binary.
From Stdlib Require Import ZArith Strings.Byte List.
Import ListNotations.

Example none_matches_array :
  abstract_heap_subtyping AH_none AH_array = true.
Proof. reflexivity. Qed.

Example separate_heap_hierarchies :
  abstract_heap_subtyping AH_none AH_func = false /\
  abstract_heap_subtyping AH_nofunc AH_any = false /\
  abstract_heap_subtyping AH_noextern AH_eq = false.
Proof. repeat split; reflexivity. Qed.

Example nullability_covariance :
  abstract_reference_subtyping
    {| art_nullable := false; art_heap := AH_struct |}
    {| art_nullable := true; art_heap := AH_eq |} = true.
Proof. reflexivity. Qed.

Example nullable_not_nonnull :
  abstract_reference_subtyping
    {| art_nullable := true; art_heap := AH_none |}
    {| art_nullable := false; art_heap := AH_any |} = false.
Proof. reflexivity. Qed.

Definition heap_field_matches :=
  @field_matchesb abstract_heap_type abstract_heap_subtyping abstract_heap_type_beq.

Example immutable_fields_covariant :
  heap_field_matches
    {| field_mutability := MUT_const; field_storage := ST_value AH_struct |}
    {| field_mutability := MUT_const; field_storage := ST_value AH_eq |} = true.
Proof. reflexivity. Qed.

Example mutable_fields_invariant :
  heap_field_matches
    {| field_mutability := MUT_var; field_storage := ST_value AH_struct |}
    {| field_mutability := MUT_var; field_storage := ST_value AH_eq |} = false.
Proof. reflexivity. Qed.

Example packed_types_invariant :
  heap_field_matches
    {| field_mutability := MUT_const; field_storage := ST_packed PT_i8 |}
    {| field_mutability := MUT_const; field_storage := ST_packed PT_i16 |} = false.
Proof. reflexivity. Qed.

Example field_mutability_must_agree :
  heap_field_matches
    {| field_mutability := MUT_var; field_storage := ST_packed PT_i8 |}
    {| field_mutability := MUT_const; field_storage := ST_packed PT_i8 |} = false.
Proof. reflexivity. Qed.

Definition test_i32 (z : Z) : i32 := Wasm_int.Int32.repr z.
Definition read_i32_u (n : i32) : Z := Wasm_int.Int32.unsigned n.
Definition read_i32_s (n : i32) : Z := Wasm_int.Int32.signed n.

Example i8_truncates :
  read_i32_u (unpack_field PT_i8 SX_U (pack_field PT_i8 (test_i32 511))) = 255%Z.
Proof. vm_compute. reflexivity. Qed.

Example i8_sign_extends :
  read_i32_s (unpack_field PT_i8 SX_S (pack_field PT_i8 (test_i32 128))) = (-128)%Z.
Proof. vm_compute. reflexivity. Qed.

Example i16_truncates :
  read_i32_u (unpack_field PT_i16 SX_U (pack_field PT_i16 (test_i32 65536))) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Example i16_sign_extends :
  read_i32_s (unpack_field PT_i16 SX_S (pack_field PT_i16 (test_i32 65535))) = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

Example i31_discards_top_bit :
  read_i32_u (i31_get SX_U (ref_i31 (test_i32 2147483648))) = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Example i31_unsigned_minus_one :
  read_i32_u (i31_get SX_U (ref_i31 (test_i32 (-1)))) = 2147483647%Z.
Proof. vm_compute. reflexivity. Qed.

Example i31_signed_minus_one :
  read_i32_s (i31_get SX_S (ref_i31 (test_i32 (-1)))) = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

Example i31_sign_boundary :
  read_i32_s (i31_get SX_S (ref_i31 (test_i32 1073741824))) = (-1073741824)%Z.
Proof. vm_compute. reflexivity. Qed.

Example i31_positive_boundary :
  read_i32_s (i31_get SX_S (ref_i31 (test_i32 1073741823))) = 1073741823%Z.
Proof. vm_compute. reflexivity. Qed.

Example i31_null_trap :
  i31_get_nullable SX_U None = None /\ i31_get_nullable SX_S None = None.
Proof. split; reflexivity. Qed.

Example decode_explicit_nullable :
  decode_abstract_reference [x63; x6a; x0b] =
  Some ({| art_nullable := true; art_heap := AH_array |}, [x0b]).
Proof. reflexivity. Qed.

Example decode_short_nullable :
  decode_abstract_reference [x6a; x0b] =
  Some ({| art_nullable := true; art_heap := AH_array |}, [x0b]).
Proof. reflexivity. Qed.

Example decode_nonnull :
  decode_abstract_reference [x64; x6c; x0b] =
  Some ({| art_nullable := false; art_heap := AH_i31 |}, [x0b]).
Proof. reflexivity. Qed.

Example reject_truncated_reference :
  decode_abstract_reference [x63] = None /\
  decode_abstract_reference [x64] = None.
Proof. split; reflexivity. Qed.

Example reject_non_heap_reference :
  decode_abstract_reference [x64; x7f] = None /\
  decode_abstract_reference [x63; x78] = None /\
  decode_abstract_reference [xee; x7f] = None.
Proof. repeat split; reflexivity. Qed.
