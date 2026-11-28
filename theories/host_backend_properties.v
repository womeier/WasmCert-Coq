(** The production clock host result is generated from this function.
    Time acquisition supplies an arbitrary Z; neither its value nor calling
    the clock may change any memory/store component. Unknown host IDs are
    rejected by the OCaml dispatcher before reaching this function. *)
From Wasm Require Import datatypes operations properties typing.
From mathcomp Require Import ssreflect ssrbool.
From Stdlib Require Import List ZArith.

Module ClockHostBackend.
Section Backend.
Context `{memory: BlockUpdateMemory} `{hfc: host_function_class}.

Definition clock_result (ticks: Z) (s: store_record)
  (ft: function_type) (args: list value) : option (store_record * result) :=
  match ft, args with
  | Tf nil (T_num T_i64 :: nil), nil =>
      Some (s, result_values
        (VAL_num (VAL_int64 (Wasm_int.int_of_Z i64m ticks)) :: nil))
  | _, _ => None
  end.

Theorem clock_result_shape : forall ticks s ft args s' r,
  clock_result ticks s ft args = Some (s', r) ->
  s' = s /\ ft = Tf nil (T_num T_i64 :: nil) /\
  args = nil /\
  r = result_values (VAL_num (VAL_int64 (Wasm_int.int_of_Z i64m ticks)) :: nil).
Proof.
  intros ticks s [params results] args s' r H.
  unfold clock_result in H.
  destruct params as [|p params]; [|discriminate].
  destruct results as [|t rest]; [discriminate|].
  destruct t as [nt|vt|rt|]; try discriminate.
  destruct nt; try discriminate.
  destruct rest; [|discriminate].
  destruct args; inversion H; subst; repeat split; reflexivity.
Qed.

Theorem clock_result_preserves_store : forall ticks s ft args s' r,
  clock_result ticks s ft args = Some (s', r) ->
  s' = s /\ store_extension s s' /\ (store_typing s -> store_typing s').
Proof.
  intros ticks s ft args s' r H.
  apply clock_result_shape in H. destruct H as [-> _].
  split; [reflexivity|]. split; [apply store_extension_same|auto].
Qed.

Theorem clock_result_respects_type : forall ticks s params results args s' r,
  clock_result ticks s (Tf params results) args = Some (s', r) ->
  result_types_agree s' results r.
Proof.
  intros ticks s params results args s' r H.
  apply clock_result_shape in H.
  destruct H as [-> [Hft [-> ->]]]. inversion Hft; subst.
  reflexivity.
Qed.

End Backend.
End ClockHostBackend.
