(** Exact-width GC payloads, using the existing Wasm/CompCert i32 operations.
    These are mathematical payloads, not an implementation of tagged pointers.
    [ref.i31] keeps 31 low bits; packed fields keep 8 or 16 low bits.
    Signed extraction sign-extends the payload, not the original i32.

    Specification: WebAssembly Core 3.0, Execution / Numerics and
    Execution / Reference Instructions (https://www.w3.org/TR/wasm-core-3/). *)
From Wasm Require Import datatypes gc_types.
From Stdlib Require Import ZArith Lia.

Inductive payload_width : Set := PW8 | PW16 | PW31.

Definition payload_bits (w : payload_width) : Z :=
  match w with PW8 => 8 | PW16 => 16 | PW31 => 31 end.

Definition payload_modulus (w : payload_width) : Z :=
  (2 ^ payload_bits w)%Z.

Definition payload_half (w : payload_width) : Z :=
  (payload_modulus w / 2)%Z.

Lemma payload_modulus_positive w : (0 < payload_modulus w)%Z.
Proof. destruct w; compute; reflexivity. Qed.

Lemma payload_modulus_twice_half w :
  payload_modulus w = (2 * payload_half w)%Z.
Proof. destruct w; reflexivity. Qed.

Record payload (w : payload_width) : Set := {
  payload_unsigned : Z;
  payload_range : (0 <= payload_unsigned < payload_modulus w)%Z;
}.

Arguments payload_unsigned {w} _.

Definition payload_of_Z (w : payload_width) (z : Z) : payload w.
Proof.
  refine {| payload_unsigned := (z mod payload_modulus w)%Z |}.
  apply Z.mod_pos_bound. apply payload_modulus_positive.
Defined.

Definition payload_signed {w} (p : payload w) : Z :=
  if (payload_unsigned p <? payload_half w)%Z
  then payload_unsigned p
  else (payload_unsigned p - payload_modulus w)%Z.

Lemma payload_signed_range w (p : payload w) :
  (-payload_half w <= payload_signed p < payload_half w)%Z.
Proof.
  unfold payload_signed.
  pose proof (payload_range w p).
  pose proof (payload_modulus_twice_half w).
  destruct (Z.ltb_spec (payload_unsigned p) (payload_half w)); lia.
Qed.

Lemma payload_of_Z_small w z :
  (0 <= z < payload_modulus w)%Z ->
  payload_unsigned (payload_of_Z w z) = z.
Proof. intro H. simpl. now apply Z.mod_small. Qed.

Lemma payload_of_Z_idempotent w z :
  payload_unsigned (payload_of_Z w
    (payload_unsigned (payload_of_Z w z))) =
  payload_unsigned (payload_of_Z w z).
Proof. simpl. apply Z.mod_mod. pose proof (payload_modulus_positive w); lia. Qed.

Lemma payload_signed_mod w (p : payload w) :
  (payload_signed p mod payload_modulus w)%Z = payload_unsigned p.
Proof.
  unfold payload_signed.
  destruct (Z.ltb_spec (payload_unsigned p) (payload_half w)).
  - apply Z.mod_small. apply payload_range.
  - replace (payload_unsigned p - payload_modulus w)%Z
      with (payload_unsigned p + (-1) * payload_modulus w)%Z by ring.
    rewrite Z.mod_add.
    + apply Z.mod_small. apply payload_range.
    + pose proof (payload_modulus_positive w); lia.
Qed.

(** Erasing range proofs is intentional.  Observable equalities below concern
    the bits and do not require proof irrelevance or new axioms. *)
Definition payload_of_i32 (w : payload_width) (n : i32) : payload w :=
  payload_of_Z w (Wasm_int.Int32.unsigned n).

Definition payload_to_i32 {w} (signedness : sx) (p : payload w) : i32 :=
  Wasm_int.Int32.repr
    (match signedness with
     | SX_U => payload_unsigned p
     | SX_S => payload_signed p
     end).

Lemma payload_to_i32_unsigned w (p : payload w) :
  Wasm_int.Int32.unsigned (payload_to_i32 SX_U p) = payload_unsigned p.
Proof.
  unfold payload_to_i32.
  apply Wasm_int.Int32.unsigned_repr.
  pose proof (payload_range w p).
  destruct w; cbv [payload_modulus payload_bits] in *;
    change (0 <= payload_unsigned p <= 4294967295)%Z; lia.
Qed.

Lemma payload_to_i32_signed w (p : payload w) :
  Wasm_int.Int32.signed (payload_to_i32 SX_S p) = payload_signed p.
Proof.
  unfold payload_to_i32.
  apply Wasm_int.Int32.signed_repr.
  pose proof (payload_signed_range w p) as H.
  destruct w; change (-2147483648 <= payload_signed p <= 2147483647)%Z.
  - change (-128 <= payload_signed p < 128)%Z in H. lia.
  - change (-32768 <= payload_signed p < 32768)%Z in H. lia.
  - change (-1073741824 <= payload_signed p < 1073741824)%Z in H. lia.
Qed.

Lemma payload_unsigned_roundtrip w (p : payload w) :
  payload_unsigned (payload_of_i32 w (payload_to_i32 SX_U p)) =
  payload_unsigned p.
Proof.
  unfold payload_of_i32.
  rewrite payload_to_i32_unsigned.
  apply payload_of_Z_small. apply payload_range.
Qed.

Definition packed_width (t : packed_type) : payload_width :=
  match t with PT_i8 => PW8 | PT_i16 => PW16 end.

Definition pack_field (t : packed_type) (n : i32) : payload (packed_width t) :=
  payload_of_i32 (packed_width t) n.

Definition unpack_field (t : packed_type) (signedness : sx)
    (p : payload (packed_width t)) : i32 :=
  payload_to_i32 signedness p.

Definition i31 := payload PW31.

Definition ref_i31 (n : i32) : i31 := payload_of_i32 PW31 n.

Definition i31_get (signedness : sx) (p : i31) : i32 :=
  payload_to_i32 signedness p.

(** [None] in the argument represents the null reference; [None] in the
    result represents the mandatory null trap.  Non-i31 references must be
    excluded by validation before using this primitive. *)
Definition i31_get_nullable (signedness : sx) (p : option i31) : option i32 :=
  match p with
  | Some p => Some (i31_get signedness p)
  | None => None
  end.

Lemma i31_get_unsigned_range p :
  (0 <= Wasm_int.Int32.unsigned (i31_get SX_U p) < 2147483648)%Z.
Proof.
  unfold i31_get. rewrite payload_to_i32_unsigned.
  exact (payload_range PW31 p).
Qed.

Lemma i31_get_signed_range p :
  (-1073741824 <= Wasm_int.Int32.signed (i31_get SX_S p) < 1073741824)%Z.
Proof.
  unfold i31_get. rewrite payload_to_i32_signed.
  exact (payload_signed_range PW31 p).
Qed.

Lemma i31_get_null_traps signedness :
  i31_get_nullable signedness None = None.
Proof. reflexivity. Qed.

Lemma i31_get_nonnull_progress signedness p :
  exists n, i31_get_nullable signedness (Some p) = Some n.
Proof. eexists; reflexivity. Qed.
