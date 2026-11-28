(** Correspondence for the actual Rocq wrapper selected by extraction.
    This does not verify OCaml extraction overrides, Parray_shim or SIMD_ops.
    The host is exactly the existing Parametric_host interface. *)
From Wasm Require Import extraction_instance instantiation_runtime_complete
  interp_instantiate_sound instantiation_spec instantiation_func operations.
From Stdlib Require Import String List.

Module ExtractionInstantiationProperties (PH: Parametric_host).
Module E := Extraction_instance PH.
Import E.

Theorem instantiate_wrapper_complete : forall hs s m imps s' f bes,
  instantiate s m imps (s', f, bes) ->
  E.interp_instantiate_wrapper hs s m imps =
    (Some (s', (f, to_e_list bes)), ""%string).
Proof.
  intros hs s m imps s' f bes H.
  unfold E.interp_instantiate_wrapper.
  rewrite (interp_instantiate_complete hs H). reflexivity.
Qed.

Theorem instantiate_wrapper_spec : forall hs s m imps s' f es message,
  E.interp_instantiate_wrapper hs s m imps = (Some (s', (f, es)), message) <->
  exists bes, es = to_e_list bes /\
    instantiate s m imps (s', f, bes) /\ message = ""%string.
Proof.
  intros hs s m imps s' f es message. split.
  - unfold E.interp_instantiate_wrapper.
    destruct (interp_instantiate hs s m imps) as [result msg] eqn:Hrun.
    destruct result as [[[[hs0 s0] f0] bes]|]; [|discriminate].
    intros Hout. inversion Hout; subst s0 f0 es msg.
    assert (Hdecl: instantiate s m imps (s', f, bes)).
    { eapply interp_instantiate_imp_instantiate; exact Hrun. }
    assert (Hcanonical: interp_instantiate hs s m imps =
      (Some (hs, s', f, bes), ""%string)).
    { now apply interp_instantiate_complete. }
    rewrite Hrun in Hcanonical. inversion Hcanonical.
    exists bes. auto.
  - intros [bes [-> [Hdecl ->]]].
    now apply instantiate_wrapper_complete.
Qed.

End ExtractionInstantiationProperties.
