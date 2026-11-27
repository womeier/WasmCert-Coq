(** Decoder regression discovered by strict invalid/malformed stage checking. *)
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From Wasm Require Import datatypes binary_format_parser.
From Stdlib Require Import Strings.Byte NArith.

Theorem parse_laneidx_byte b :
  run [::b] (fun n => parse_laneidx) = Some (to_N b).
Proof. by destruct b; vm_compute. Qed.

Example decode_invalid_lane_byte :
  run_parse_be [::xfd; x15; xff] =
  Some (BI_extract_vec (VS_i VSI_8_16) (Some SX_S) 255%N).
Proof. by vm_compute. Qed.
