Require Import binary.
Require Import bytes.
Require Import wasm.
Require Import Byte.
From parseque Require Import Parseque Running.
Require Import check_toks.

Definition test_unreachable : check_toks (cons x00 nil) be := MkSingleton Unreachable.

Definition test_nop : check_toks (cons x01 nil) be := MkSingleton Nop.