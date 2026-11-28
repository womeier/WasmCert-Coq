(** Properties of i31 values in the actual runtime representation. *)
From Wasm Require Import numerics datatypes subtyping_properties
  gc_numerics binary_format_parser binary_format_printer.
From Stdlib Require Import ZArith Lia Strings.Byte.

Lemma i31bits_payload_range n :
  (0 <= Wasm_int.Int31.unsigned n < 2147483648)%Z.
Proof. exact (Wasm_int.Int31.unsigned_range n). Qed.

(** The integrated integer representation implements the same truncation as
    the previously checked numeric foundation; no unchecked i32 tag is used. *)
Lemma i31bits_matches_payload n :
  Wasm_int.Int31.unsigned (i31bits_of_i32 n) =
  payload_unsigned (ref_i31 n).
Proof.
  unfold i31bits_of_i32, ref_i31, payload_of_i32.
  rewrite Wasm_int.Int31.unsigned_repr_eq. reflexivity.
Qed.

Lemma i31bits_get_unsigned n :
  Wasm_int.Int32.unsigned (i32_of_i31bits false n) = Wasm_int.Int31.unsigned n.
Proof.
  unfold i32_of_i31bits.
  apply Wasm_int.Int32.unsigned_repr.
  pose proof (Wasm_int.Int31.unsigned_range n) as Range.
  change (0 <= Wasm_int.Int31.unsigned n < 2147483648)%Z in Range.
  change (0 <= Wasm_int.Int31.unsigned n <= 4294967295)%Z. lia.
Qed.

Lemma i31bits_get_signed n :
  Wasm_int.Int32.signed (i32_of_i31bits true n) = Wasm_int.Int31.signed n.
Proof.
  unfold i32_of_i31bits.
  apply Wasm_int.Int32.signed_repr.
  pose proof (Wasm_int.Int31.signed_range n) as Range.
  change (-1073741824 <= Wasm_int.Int31.signed n <= 1073741823)%Z in Range.
  change (-2147483648 <= Wasm_int.Int31.signed n <= 2147483647)%Z. lia.
Qed.

Lemma ref_i31_binary_roundtrip :
  run_parse_be (binary_of_be BI_ref_i31) = Some BI_ref_i31.
Proof. vm_compute. reflexivity. Qed.

Lemma i31_get_binary_roundtrip signed :
  run_parse_be (binary_of_be (BI_i31_get signed)) = Some (BI_i31_get signed).
Proof. destruct signed; vm_compute; reflexivity. Qed.

Lemma gc_abstract_ref_null_binary_roundtrip h :
  run_parse_be
    (binary_of_be (BI_ref_null (gc_types.shared_heap_of_abstract h))) =
  Some (BI_ref_null (gc_types.shared_heap_of_abstract h)).
Proof. destruct h; vm_compute; reflexivity. Qed.
