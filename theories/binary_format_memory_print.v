(** Wire bounds for the existing memory-zero/u32-offset AST. *)
From Stdlib Require Import List Strings.Byte NArith Lia.
From Wasm Require Import datatypes binary_format_printer binary_format_memory_properties
  binary_format_vector_print.
Local Notation byte := Byte.byte.

Definition memory_arg_binary_wf marg :=
  (marg.(memarg_align) < 64)%N /\ binary_index_wf marg.(memarg_offset).

Inductive memory_binary_wf : basic_instruction -> Prop :=
| MBW_scalar : forall op make marg,
    In (op, make) scalar_memory_opcodes -> memory_arg_binary_wf marg ->
    memory_binary_wf (make marg)
| MBW_vector : forall code make marg,
    In (code, make) vector_memarg_opcodes -> memory_arg_binary_wf marg ->
    memory_binary_wf (make marg)
| MBW_lane : forall code make marg lane,
    In (code, make) vector_memory_lane_opcodes -> memory_arg_binary_wf marg ->
    (lane < 256)%N -> memory_binary_wf (make marg lane)
| MBW_size : memory_binary_wf BI_memory_size
| MBW_grow : memory_binary_wf BI_memory_grow
| MBW_init : forall x, binary_index_wf x -> memory_binary_wf (BI_memory_init x)
| MBW_drop : forall x, binary_index_wf x -> memory_binary_wf (BI_data_drop x)
| MBW_copy : memory_binary_wf BI_memory_copy
| MBW_fill : memory_binary_wf BI_memory_fill.

Lemma binary_of_memarg_encoding marg :
  memory_arg_binary_wf marg -> memarg_encoding (binary_of_memarg marg) marg.
Proof.
  destruct marg as [offset align]; intros [Align Offset].
  exists (binary_of_u32 align), (binary_of_u32 offset), align.
  split; [reflexivity |]. split.
  - apply binary_of_index_encoding; unfold binary_index_wf; cbn in Align; lia.
  - unfold memarg_tail_encoding; cbn in Align, Offset.
    rewrite (proj2 (N.ltb_lt _ _) Align).
    exists offset; split; [now apply binary_of_index_encoding |reflexivity].
Qed.

Lemma scalar_memory_print op make marg :
  In (op, make) scalar_memory_opcodes ->
  binary_of_be (make marg) = op :: binary_of_memarg marg.
Proof.
  unfold scalar_memory_opcodes; cbn [In]; intro Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; reflexivity.
Qed.

Lemma vector_memory_print code make marg :
  In (code, make) vector_memarg_opcodes ->
  binary_of_be (make marg) = xfd :: binary_of_idx code ++ binary_of_memarg marg.
Proof.
  unfold vector_memarg_opcodes; cbn [In]; intro Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; reflexivity.
Qed.

Lemma vector_memory_lane_print code make marg lane :
  In (code, make) vector_memory_lane_opcodes ->
  binary_of_be (make marg lane) =
    xfd :: binary_of_idx code ++ binary_of_memarg marg ++ binary_of_laneidx lane.
Proof.
  unfold vector_memory_lane_opcodes; cbn [In]; intro Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; reflexivity.
Qed.

Lemma vector_memarg_code_bound code make :
  In (code, make) vector_memarg_opcodes -> binary_index_wf code.
Proof.
  unfold vector_memarg_opcodes; cbn [In]; intro Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst code; unfold binary_index_wf; lia.
Qed.

Lemma vector_lane_code_bound code make :
  In (code, make) vector_memory_lane_opcodes -> binary_index_wf code.
Proof.
  unfold vector_memory_lane_opcodes; cbn [In]; intro Member.
  repeat destruct Member as [Member|Member]; try contradiction;
    inversion Member; subst code; unfold binary_index_wf; lia.
Qed.

Theorem binary_of_memory_encoding be :
  memory_binary_wf be -> memory_instruction_encoding (binary_of_be be) be.
Proof.
  intro Wf; destruct Wf.
  - rewrite (scalar_memory_print _ _ marg H).
    apply memory_scalar with (make := make); [exact H |now apply binary_of_memarg_encoding].
  - rewrite (vector_memory_print _ _ marg H).
    apply memory_vector; eapply vector_memory_memarg; [exact H | |now apply binary_of_memarg_encoding].
    apply binary_of_index_encoding; now apply (vector_memarg_code_bound _ make).
  - rewrite (vector_memory_lane_print _ _ marg lane H).
    unfold binary_of_laneidx.
    destruct (Byte.of_N lane) as [b|] eqn:Byte.
    + pose proof (Byte.to_of_N _ Byte) as Value; rewrite <- Value.
      apply memory_vector; eapply vector_memory_lane; [exact H | |now apply binary_of_memarg_encoding].
      apply binary_of_index_encoding; now apply (vector_lane_code_bound _ make).
    + apply Byte.of_N_None_iff in Byte; lia.
  - constructor.
  - constructor.
  - apply (memory_init (binary_of_idx 8%N) (binary_of_idx x) x).
    + apply binary_of_index_encoding; unfold binary_index_wf; lia.
    + now apply binary_of_index_encoding.
  - apply (memory_drop (binary_of_idx 9%N) (binary_of_idx x) x).
    + apply binary_of_index_encoding; unfold binary_index_wf; lia.
    + now apply binary_of_index_encoding.
  - apply (memory_copy (binary_of_idx 10%N)); apply binary_of_index_encoding; unfold binary_index_wf; lia.
  - apply (memory_fill (binary_of_idx 11%N)); apply binary_of_index_encoding; unfold binary_index_wf; lia.
Qed.
