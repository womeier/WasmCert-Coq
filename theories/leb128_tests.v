From Wasm Require Import leb128 check_toks.
From Wasm Require Import binary_format_parser leb128_properties.
From Stdlib Require Import Init.Byte ZArith List.
From parseque Require Import Running Induction.
Import ListNotations.

(** Example from Wikipedia article: https://en.wikipedia.org/wiki/LEB128#Unsigned_LEB128
   This is the representation of the number [624485]. **)
Definition test_wikipedia : list Byte.byte :=
  xe5 :: x8e :: x26 :: nil.

Definition encode_unsigned_check (k : N) :=
  Singleton (encode_unsigned k).

Lemma test_wikipedia_encode :
  encode_unsigned_check 624485%N = Singleton test_wikipedia.
Proof.
  vm_compute. reflexivity.
Qed.

Definition test_wikipedia_decode :
  check_toks test_wikipedia parse_unsigned = Singleton 624485%N.
Proof.
  vm_compute. reflexivity.
Qed.

Definition test_wikipedia_signed: list Byte.byte :=
  xc0 :: xbb :: x78 :: nil.

Definition encode_signed_check (k : Z) :=
  Singleton (encode_signed k).

Lemma test_wikipedia_signed_encode:
  encode_signed_check (-123456)%Z = Singleton test_wikipedia_signed.
Proof.
  vm_compute. reflexivity.
Qed.

(* https://github.com/WasmCert/WasmCert-Coq/issues/83 *)
Lemma encode_signed_minus65 :
  encode_signed (-65)%Z = (xbf :: x7f :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma encode_signed_plus63 :
  encode_signed 63%Z = (x3f :: nil).
Proof. vm_compute. reflexivity. Qed.

(** Injectivity at boundary *)
Lemma encode_signed_collision :
  encode_signed (-65)%Z <> encode_signed 63%Z.
Proof. vm_compute. intros Heq; inversion Heq. Qed.

Lemma encode_signed_minus8193 :
  encode_signed (-8193)%Z <> encode_signed 8191%Z.
Proof. vm_compute. intros Heq; inversion Heq. Qed.

(** Boundary value -64 still encodes to canonical instead of c0 7f ---- *)
Lemma encode_signed_minus64 :
  encode_signed (-64)%Z = (x40 :: nil).
Proof. vm_compute. reflexivity. Qed.

Lemma encode_signed_minus8192 :
  encode_signed (-8192)%Z = (x80 :: x40 :: nil).
Proof. vm_compute. reflexivity. Qed.

(** Use the general parser/grammar theorem, rather than evaluating a second
    decoder, to establish a GC heap-index boundary. *)
Lemma heap_index_128_from_encoding :
  run_parse_heap_typeidx (x80 :: x01 :: nil) = Some 128%N.
Proof.
  apply run_heap_typeidx_leb_complete.
  - change (signed_leb (x80 :: x01 :: nil)
      (Z.of_N (Byte.to_N x80) - 128 + 128 * Z.of_N (Byte.to_N x01))).
    apply sleb_more.
    + vm_compute. congruence.
    + apply sleb_end_pos. vm_compute. reflexivity.
  - vm_compute. congruence.
  - repeat constructor.
Qed.
