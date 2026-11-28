(** Actual recursive printer encoding and arbitrary-suffix parser handoff. *)
From Stdlib Require Import List Strings.Byte.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser binary_format_printer
  binary_format_parser_properties binary_parser_combinator_properties
  binary_format_language_properties binary_format_dispatch_properties
  binary_format_block_properties binary_format_type_properties
  binary_format_print_encoding binary_format_recursive_complete.
Local Notation byte := Byte.byte.
Local Notation Instruction := (instruction_encoding wasm_atomic_encoding block_type_encoding).
Local Notation Expression := (expression_encoding wasm_atomic_encoding block_type_encoding).
Local Notation IfBody := (if_body_encoding wasm_atomic_encoding block_type_encoding).

(** No byte grammar or parser premise occurs in this domain.  All leaf
    index/length/type/opcode/lane/memarg bounds are in [atomic_binary_wf]. *)
Inductive instruction_binary_wf : basic_instruction -> Prop :=
| IBW_atomic : forall be, atomic_binary_wf be -> instruction_binary_wf be
| IBW_block : forall bt body,
    block_type_binary_wf bt -> expression_binary_wf body ->
    instruction_binary_wf (BI_block bt body)
| IBW_loop : forall bt body,
    block_type_binary_wf bt -> expression_binary_wf body ->
    instruction_binary_wf (BI_loop bt body)
| IBW_if : forall bt left right,
    block_type_binary_wf bt -> expression_binary_wf left ->
    expression_binary_wf right -> instruction_binary_wf (BI_if bt left right)
with expression_binary_wf : list basic_instruction -> Prop :=
| EBW_nil : expression_binary_wf nil
| EBW_cons : forall be rest,
    instruction_binary_wf be -> expression_binary_wf rest ->
    expression_binary_wf (be :: rest).

Scheme instruction_binary_wf_mut := Induction for instruction_binary_wf Sort Prop
with expression_binary_wf_mut := Induction for expression_binary_wf Sort Prop.
Combined Scheme binary_wf_mutind from instruction_binary_wf_mut, expression_binary_wf_mut.

Lemma printed_expression_encoding es :
  Forall (fun be => Instruction (binary_of_be be) be) es ->
  Expression (binary_of_expr es) es.
Proof.
  intro Items; unfold binary_of_expr.
  induction Items; simpl.
  - constructor.
  - rewrite <- app_assoc; now apply expression_cons.
Qed.

Definition printed_if_body left right :=
  concat (List.map binary_of_be left) ++
  match right with
  | nil => x0b :: nil
  | _ => x05 :: binary_of_expr right
  end.

Lemma printed_if_body_encoding left right :
  Forall (fun be => Instruction (binary_of_be be) be) left ->
  Forall (fun be => Instruction (binary_of_be be) be) right ->
  IfBody (printed_if_body left right) (left, right).
Proof.
  intros Left Right; unfold printed_if_body.
  induction Left; simpl.
  - destruct right as [|be rest].
    + constructor.
    + apply if_body_else; now apply printed_expression_encoding.
  - rewrite <- app_assoc; now apply if_body_cons.
Qed.

Theorem binary_of_instruction_and_sequence_encoding :
  (forall be, instruction_binary_wf be ->
    Instruction (binary_of_be be) be) /\
  (forall es, expression_binary_wf es ->
    Forall (fun be => Instruction (binary_of_be be) be) es).
Proof.
  apply binary_wf_mutind.
  - intros be Wf. apply instruction_atom; now apply binary_of_atomic_encoding.
  - intros bt body TypeWf Wf Items; cbn [binary_of_be].
    apply instruction_block; [now apply binary_of_block_type_encoding |].
    now apply printed_expression_encoding.
  - intros bt body TypeWf Wf Items; cbn [binary_of_be].
    apply instruction_loop; [now apply binary_of_block_type_encoding |].
    now apply printed_expression_encoding.
  - { intros bt left right TypeWf WfLeft Left WfRight Right.
    pose proof (printed_if_body_encoding left right Left Right) as Body.
    destruct right as [|be rest]; cbn [binary_of_be].
    all: apply instruction_if; [now apply binary_of_block_type_encoding |exact Body]. }
  - constructor.
  - intros be rest WfBe Be WfRest Rest; now constructor.
Qed.

Theorem binary_of_expr_encoding es :
  expression_binary_wf es ->
  Expression (binary_of_expr es) es.
Proof.
  intro Wf; apply printed_expression_encoding.
  exact (proj2 binary_of_instruction_and_sequence_encoding es Wf).
Qed.

(** This has the exact [expression_print_prefix es] type used by the tail
    owner's code/local composition, without importing its dependency stack
    or duplicating that public definition. *)
Theorem wasm_expression_print_prefix es :
  expression_binary_wf es ->
  forall n m (bound : m <= n) (input : SizedList byte m) suffix,
    @Sized.value _ _ _ input = binary_of_expr es ++ suffix ->
    option_map (fun s => (Success.value s,
      @Sized.value _ _ _ (Success.leftovers s)))
      (runParser (parse_expr (M := option) (n := n)) bound input) = Some (es, suffix).
Proof.
  intros Wf n m bound input suffix Bytes.
  destruct (wasm_production_parse_expr_complete n m bound input
    (binary_of_expr es) suffix es Bytes (binary_of_expr_encoding es Wf))
    as [s [Run [Value Rest]]].
  rewrite Run.
  change (Some (Success.value s, output_bytes s) = Some (es, suffix)).
  now rewrite Value, Rest.
Qed.

Corollary binary_of_expr_roundtrip es :
  expression_binary_wf es -> run_parse_expr (binary_of_expr es) = Some es.
Proof.
  intro Wf; apply (run_parser_complete _ Expression).
  - exact wasm_production_parse_expr_complete.
  - now apply binary_of_expr_encoding.
Qed.
