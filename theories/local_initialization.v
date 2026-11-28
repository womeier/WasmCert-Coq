(* Definite initialization is scoped to an instruction sequence. Structured
   instructions validate their bodies with the incoming state, but discard
   body-local effects at the enclosing boundary, as in the core typing rules. *)
From Wasm Require Import datatypes_properties operations.
From Stdlib Require Import NArith.
From mathcomp Require Import ssreflect ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition local_init_state := list bool.

Definition local_init_le (I J : local_init_state) : Prop :=
  List.Forall2 (fun a b => a = true -> b = true) I J.

Definition initialized_slots {A : Type} (slots : list (option A)) : local_init_state :=
  map (fun slot => match slot with Some _ => true | None => false end) slots.

Definition local_init_plain (e : basic_instruction) : bool :=
  match e with
  | BI_local_get _ | BI_local_set _ | BI_local_tee _
  | BI_block _ _ | BI_loop _ _ | BI_if _ _ _ => false
  | _ => true
  end.

Inductive local_init_instruction :
    local_init_state -> basic_instruction -> local_init_state -> Prop :=
| li_plain : forall I e,
    local_init_plain e ->
    local_init_instruction I e I
| li_get : forall I x,
    lookup_N I x = Some true ->
    local_init_instruction I (BI_local_get x) I
| li_set : forall I x b,
    lookup_N I x = Some b ->
    local_init_instruction I (BI_local_set x)
      (set_nth false I (N.to_nat x) true)
| li_tee : forall I x b,
    lookup_N I x = Some b ->
    local_init_instruction I (BI_local_tee x)
      (set_nth false I (N.to_nat x) true)
| li_block : forall I J bt es,
    local_init_sequence I es J ->
    local_init_instruction I (BI_block bt es) I
| li_loop : forall I J bt es,
    local_init_sequence I es J ->
    local_init_instruction I (BI_loop bt es) I
| li_if : forall I J1 J2 bt es1 es2,
    local_init_sequence I es1 J1 ->
    local_init_sequence I es2 J2 ->
    local_init_instruction I (BI_if bt es1 es2) I
with local_init_sequence :
    local_init_state -> list basic_instruction -> local_init_state -> Prop :=
| li_nil : forall I, local_init_sequence I nil I
| li_cons : forall I J K e es,
    local_init_instruction I e J ->
    local_init_sequence J es K ->
    local_init_sequence I (e :: es) K.

Fixpoint check_local_init_instruction (e : basic_instruction)
    (I : local_init_state) : option local_init_state :=
  let check_sequence :=
    fix check_sequence (es : list basic_instruction) I :=
      match es with
      | nil => Some I
      | e :: es =>
          match check_local_init_instruction e I with
          | Some J => check_sequence es J
          | None => None
          end
      end in
  match e with
  | BI_local_get x =>
      match lookup_N I x with
      | Some true => Some I
      | _ => None
      end
  | BI_local_set x | BI_local_tee x =>
      match lookup_N I x with
      | Some _ => Some (set_nth false I (N.to_nat x) true)
      | None => None
      end
  | BI_block _ es | BI_loop _ es =>
      match check_sequence es I with Some _ => Some I | None => None end
  | BI_if _ es1 es2 =>
      match check_sequence es1 I, check_sequence es2 I with
      | Some _, Some _ => Some I
      | _, _ => None
      end
  | _ => Some I
  end.

Fixpoint check_local_init_sequence (es : list basic_instruction)
    (I : local_init_state) : option local_init_state :=
  match es with
  | nil => Some I
  | e :: es =>
      match check_local_init_instruction e I with
      | Some J => check_local_init_sequence es J
      | None => None
      end
  end.

Definition initial_local_state (params locals : list value_type) : local_init_state :=
  List.repeat true (List.length params) ++
    List.map (fun t => default_val t != None) locals.

Section Administrative.
Context `{hfc : host_function_class}.

(* Administrative labels restore the enclosing static state. A nested frame
   checks against its own slots, never the caller's initialized-local bits.
   Trap is terminal; its unreachable suffix may assume all slots initialized. *)
Fixpoint check_administrative_local_init (e : administrative_instruction)
    (I : local_init_state) : option local_init_state :=
  let check_sequence :=
    fix check_sequence (es : list administrative_instruction) I :=
      match es with
      | nil => Some I
      | e :: es =>
          match check_administrative_local_init e I with
          | Some J => check_sequence es J
          | None => None
          end
      end in
  match e with
  | AI_basic e => check_local_init_instruction e I
  | AI_trap => Some (List.repeat true (List.length I))
  | AI_label _ continuation body =>
      match check_sequence body I, check_sequence continuation I with
      | Some _, Some _ => Some I
      | _, _ => None
      end
  | AI_frame _ f body =>
      match check_sequence body (initialized_slots f.(f_locs)) with
      | Some _ => Some I
      | None => None
      end
  | _ => Some I
  end.

Fixpoint check_administrative_local_init_sequence (es : list administrative_instruction)
    (I : local_init_state) : option local_init_state :=
  match es with
  | nil => Some I
  | e :: es =>
      match check_administrative_local_init e I with
      | Some J => check_administrative_local_init_sequence es J
      | None => None
      end
  end.

End Administrative.
