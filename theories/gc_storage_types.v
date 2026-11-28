(** Shared storage syntax, below source and closed type declarations.
    These are the GC storage/field definitions previously in gc_types.v.
    Keeping them independent of value_type lets both declaration phases
    reuse exactly the same packed-field and mutability representation. *)
From Wasm Require Import common.

Inductive mutability : Set :=
| MUT_const
| MUT_var.

Inductive gc_packed_type : Set := PT_i8 | PT_i16.
Scheme Equality for gc_packed_type.

Inductive storage_type (V : Type) : Type :=
| ST_value : V -> storage_type V
| ST_packed : gc_packed_type -> storage_type V.

Arguments ST_value {V} _.
Arguments ST_packed {V} _.

Record field_type (V : Type) : Type := {
  field_mutability : mutability;
  field_storage : storage_type V;
}.

Arguments field_mutability {V} _.
Arguments field_storage {V} _.
