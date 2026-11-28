(** Binary local-declaration grammars for the concrete types currently modeled.
    Typed reference encodings require the shared function-reference extension. *)
From Stdlib Require Import List Strings.Byte NArith.
From parseque Require Import Parseque Success.
From Wasm Require Import datatypes_properties binary_format_parser
  binary_format_parser_properties binary_vector_properties binary_uleb128.

Inductive concrete_valtype_prefix :
    list Byte.byte -> value_type -> list Byte.byte -> Prop :=
| valtype_i32 : forall suffix,
    concrete_valtype_prefix (x7f :: suffix) (T_num T_i32) suffix
| valtype_i64 : forall suffix,
    concrete_valtype_prefix (x7e :: suffix) (T_num T_i64) suffix
| valtype_f32 : forall suffix,
    concrete_valtype_prefix (x7d :: suffix) (T_num T_f32) suffix
| valtype_f64 : forall suffix,
    concrete_valtype_prefix (x7c :: suffix) (T_num T_f64) suffix
| valtype_v128 : forall suffix,
    concrete_valtype_prefix (x7b :: suffix) (T_vec T_v128) suffix
| valtype_funcref : forall suffix,
    concrete_valtype_prefix (x70 :: suffix) (T_ref T_funcref) suffix
| valtype_externref : forall suffix,
    concrete_valtype_prefix (x6f :: suffix) (T_ref T_externref) suffix.

Lemma parse_concrete_valtype_prefix : forall n m (input : SizedList Byte.byte m)
    type suffix (Hle : (m <= n)%nat),
    concrete_valtype_prefix (@Sized.value _ _ _ input) type suffix ->
    option_map observe_reader
      (runParser (parse_value_type :
        Parser (SizedList Byte.byte) Byte.byte option value_type n)
        Hle input) = Some (type, suffix).
Proof.
  intros n m [input Hlength] type suffix Hle Hgrammar.
  cbn [Sized.value] in Hgrammar.
  inversion Hgrammar; subst; reflexivity.
Qed.

Inductive local_decl_prefix :
    list Byte.byte -> (N * value_type) -> list Byte.byte -> Prop :=
| local_decl_bytes : forall input count middle type suffix,
    u32_prefix input count middle ->
    concrete_valtype_prefix middle type suffix ->
    local_decl_prefix input (count, type) suffix.

Lemma parse_local_decl_prefix : forall n m (input : SizedList Byte.byte m)
    decl suffix (Hle : (m <= n)%nat),
    local_decl_prefix (@Sized.value _ _ _ input) decl suffix ->
    option_map observe_reader
      (runParser (parse_locals :
        Parser (SizedList Byte.byte) Byte.byte option (N * value_type) n)
        Hle input) = Some (decl, suffix).
Proof.
  intros n m input decl suffix Hle Hgrammar.
  inversion Hgrammar as [bytes count middle type rest Hcount Htype]; subst.
  unfold parse_locals.
  eapply parser_and_prefix with (a := count) (middle := middle).
  - now apply parse_u32_as_N_correct.
  - intros k Hkn tokens Htokens.
    apply parse_concrete_valtype_prefix. now rewrite Htokens.
Qed.

Theorem parse_local_vector_prefix :
    forall n m (input : SizedList Byte.byte m)
      decls suffix (Hle : (m <= n)%nat),
    vector_prefix local_decl_prefix (@Sized.value _ _ _ input) decls suffix ->
    option_map observe_reader
      (runParser (parse_vec parse_locals :
        Parser (SizedList Byte.byte) Byte.byte option (list (N * value_type)) n)
        Hle input) = Some (decls, suffix).
Proof.
  intros n m input decls suffix Hle Hgrammar.
  apply parse_vec_complete with (element := local_decl_prefix).
  - intros. now apply parse_local_decl_prefix.
  - exact Hgrammar.
Qed.

Definition locals_total (decls : list (N * value_type)) :=
  List.fold_left (fun a b => N.add a b) (List.map fst decls) 0%N.

Definition locals_expansion (decls : list (N * value_type)) :=
  List.concat
    (List.map (fun '(count, type) => List.repeat type (N.to_nat count)) decls).

Lemma verify_locals_accept : forall decls,
    (locals_total decls < 4294967296)%N ->
    verify_locals decls = Some (locals_expansion decls).
Proof.
  intros decls Hbound.
  unfold verify_locals, locals_total, locals_expansion in *.
  cbn zeta.
  rewrite (proj2 (N.ltb_lt _ _) Hbound). reflexivity.
Qed.

Lemma verify_locals_reject : forall decls,
    (4294967296 <= locals_total decls)%N ->
    verify_locals decls = None.
Proof.
  intros decls Hbound.
  unfold verify_locals, locals_total in *.
  cbn zeta.
  rewrite (proj2 (N.ltb_ge _ _) Hbound). reflexivity.
Qed.
