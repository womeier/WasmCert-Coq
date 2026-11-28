(** Address widths are shared by core memory and table types.  Module/store
    indices remain u32 and are independent of these widths. *)
From Stdlib Require Import NArith.

Module AddressTypes.
Inductive address_type : Set :=
| AT_i32
| AT_i64.

Definition address_bits (a: address_type) : N :=
  match a with AT_i32 => 32 | AT_i64 => 64 end.

Definition address_bound (a: address_type) : N :=
  2 ^ address_bits a.
End AddressTypes.

Export AddressTypes.
