(** Bounded unsigned LEB128 decoding for address-dependent limits and offsets.

    Unlike an unbounded LEB128 parser followed by a numeric range check, this
    decoder rejects encodings exceeding ceil(width/7) bytes even when their
    numeric value fits.  Non-canonical encodings within that bound are legal.

    The proofs below describe the actual executable prefix decoder, including
    its remainder.  Integration into the module parser is a separate step;
    importing this file does not enable memory64 in the legacy module AST. *)
From Wasm Require Import datatypes addressing leb128.
From Stdlib Require Import Strings.Byte NArith List Lia Bool.
Import ListNotations.
Import Addressing.

Module AddressingBinary.

Definition address_bytes (a: address_type) : nat :=
  match a with AT_i32 => 5 | AT_i64 => 10 end.

Fixpoint decode_uleb (fuel: nat) (input: list byte)
    : option (N * list byte) :=
  match fuel, input with
  | S fuel', b :: input' =>
      let digit := Byte.to_N b in
      if N.ltb digit 128 then Some (digit, input')
      else
        match decode_uleb fuel' input' with
        | Some (n, rest) => Some ((digit - 128 + 128 * n)%N, rest)
        | None => None
        end
  | _, _ => None
  end.

(** Unsigned LEB128 grammar, independent of the decoder's recursion bound. *)
Inductive unsigned_leb : list byte -> N -> Prop :=
| unsigned_last b :
    (Byte.to_N b < 128)%N ->
    unsigned_leb [b] (Byte.to_N b)
| unsigned_more b bs n :
    (128 <= Byte.to_N b)%N ->
    unsigned_leb bs n ->
    unsigned_leb (b :: bs) (Byte.to_N b - 128 + 128 * n)%N.

Lemma decode_uleb_sound fuel input n rest :
  decode_uleb fuel input = Some (n, rest) ->
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= fuel)%nat /\
    unsigned_leb prefix n.
Proof.
  revert input n rest.
  induction fuel as [|fuel IH]; intros input n rest Hdecode;
    [discriminate |].
  destruct input as [|b input]; [discriminate |].
  cbn [decode_uleb] in Hdecode.
  destruct (N.ltb (Byte.to_N b) 128) eqn:Hlast.
  - inversion Hdecode; subst. exists [b].
    split; [reflexivity |]. split; [simpl; lia |].
    constructor. now apply N.ltb_lt.
  - destruct (decode_uleb fuel input) as [[tail tail_rest]|] eqn:Htail;
      [|discriminate].
    inversion Hdecode; subst.
    apply IH in Htail as [prefix [Hinput [Hlength Hleb]]].
    exists (b :: prefix). split; [simpl; now rewrite Hinput |].
    split; [simpl; lia |].
    constructor; [now apply N.ltb_ge | assumption].
Qed.

Lemma decode_uleb_complete prefix n :
  unsigned_leb prefix n ->
  forall fuel rest,
    (List.length prefix <= fuel)%nat ->
    decode_uleb fuel (prefix ++ rest) = Some (n, rest).
Proof.
  intros Hleb. induction Hleb as [b Hlast|b bs n Hmore Hleb IH];
    intros fuel rest Hlength;
    destruct fuel as [|fuel]; simpl in Hlength; [lia | |lia |].
  - cbn [List.app decode_uleb].
    assert (N.ltb (Byte.to_N b) 128 = true) as -> by
      (apply N.ltb_lt; assumption).
    reflexivity.
  - cbn [List.app decode_uleb].
    assert (N.ltb (Byte.to_N b) 128 = false) as -> by
      (apply N.ltb_ge; assumption).
    rewrite IH; [reflexivity | lia].
Qed.

Lemma decode_uleb_spec fuel input n rest :
  decode_uleb fuel input = Some (n, rest) <->
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= fuel)%nat /\
    unsigned_leb prefix n.
Proof.
  split; [apply decode_uleb_sound |].
  intros [prefix [-> [Hlength Hleb]]].
  now apply decode_uleb_complete.
Qed.

Definition decode_address (a: address_type) (input: list byte)
    : option (N * list byte) :=
  match decode_uleb (address_bytes a) input with
  | Some (n, rest) =>
      if N.ltb n (address_bound a) then Some (n, rest) else None
  | None => None
  end.

Lemma decode_address_spec a input n rest :
  decode_address a input = Some (n, rest) <->
  (n < address_bound a)%N /\
  exists prefix,
    input = prefix ++ rest /\
    (List.length prefix <= address_bytes a)%nat /\
    unsigned_leb prefix n.
Proof.
  unfold decode_address.
  destruct (decode_uleb (address_bytes a) input) as [[k tail]|] eqn:Hdec.
  - destruct (N.ltb k (address_bound a)) eqn:Hbound.
    + apply N.ltb_lt in Hbound. split.
      * intros H. inversion H; subst.
        split; [assumption | now apply decode_uleb_spec].
      * intros [_ Hleb].
        apply decode_uleb_spec in Hleb.
        rewrite Hdec in Hleb. inversion Hleb. reflexivity.
    + split; [discriminate |].
      intros [Hlt Hleb]. apply decode_uleb_spec in Hleb.
      rewrite Hdec in Hleb. inversion Hleb; subst.
      apply N.ltb_ge in Hbound. lia.
  - split; [discriminate |].
    intros [_ Hleb]. apply decode_uleb_spec in Hleb.
    rewrite Hdec in Hleb. discriminate.
Qed.

(** Flags 0/1 are i32; 4/5 are i64.  Shared memory is a different proposal,
    so flags 2/3/6/7 are deliberately not accepted here. *)
Definition decode_limits_flag (b: byte) : option (address_type * bool) :=
  match b with
  | x00 => Some (AT_i32, false)
  | x01 => Some (AT_i32, true)
  | x04 => Some (AT_i64, false)
  | x05 => Some (AT_i64, true)
  | _ => None
  end.

Definition encode_limits_flag (a: address_type) (has_max: bool) : byte :=
  match a, has_max with
  | AT_i32, false => x00
  | AT_i32, true => x01
  | AT_i64, false => x04
  | AT_i64, true => x05
  end.

Lemma limits_flag_round_trip a has_max :
  decode_limits_flag (encode_limits_flag a has_max) = Some (a, has_max).
Proof. destruct a, has_max; reflexivity. Qed.

Lemma limits_flag_canonical b a has_max :
  decode_limits_flag b = Some (a, has_max) ->
  b = encode_limits_flag a has_max.
Proof.
  destruct b; simpl; intros H; try discriminate;
    inversion H; reflexivity.
Qed.

Definition decode_limits (input: list byte)
    : option (address_type * limits * list byte) :=
  match input with
  | [] => None
  | flag :: input' =>
      match decode_limits_flag flag with
      | None => None
      | Some (a, has_max) =>
          match decode_address a input' with
          | None => None
          | Some (minimum, input'') =>
              if has_max then
                match decode_address a input'' with
                | None => None
                | Some (maximum, rest) =>
                    Some (a, {| lim_min := minimum;
                                 lim_max := Some maximum |}, rest)
                end
              else Some (a, {| lim_min := minimum; lim_max := None |}, input'')
          end
      end
  end.

(** This is a binary-format judgment, not a validation judgment.  In
    particular, min > max and overlarge memory page counts are decoded here
    and rejected by [memory_type_valid]/[table_type_valid], not misclassified
    as malformed byte sequences. *)
Inductive limits_encoding :
    list byte -> address_type -> limits -> list byte -> Prop :=
| limits_without_max a flag input minimum rest :
    decode_limits_flag flag = Some (a, false) ->
    (minimum < address_bound a)%N ->
    (exists prefix, input = prefix ++ rest /\
      (List.length prefix <= address_bytes a)%nat /\
      unsigned_leb prefix minimum) ->
    limits_encoding (flag :: input) a
      {| lim_min := minimum; lim_max := None |} rest
| limits_with_max a flag input minimum middle maximum rest :
    decode_limits_flag flag = Some (a, true) ->
    (minimum < address_bound a)%N ->
    (exists prefix, input = prefix ++ middle /\
      (List.length prefix <= address_bytes a)%nat /\
      unsigned_leb prefix minimum) ->
    (maximum < address_bound a)%N ->
    (exists prefix, middle = prefix ++ rest /\
      (List.length prefix <= address_bytes a)%nat /\
      unsigned_leb prefix maximum) ->
    limits_encoding (flag :: input) a
      {| lim_min := minimum; lim_max := Some maximum |} rest.

Lemma decode_limits_sound input a lim rest :
  decode_limits input = Some (a, lim, rest) ->
  limits_encoding input a lim rest.
Proof.
  destruct input as [|flag input]; [discriminate |].
  cbn [decode_limits].
  destruct (decode_limits_flag flag) as [[width has_max]|] eqn:Hflag;
    [|discriminate].
  destruct (decode_address width input) as [[minimum middle]|] eqn:Hmin;
    [|discriminate].
  apply decode_address_spec in Hmin as [Hmin Hmin_encoding].
  destruct has_max.
  - destruct (decode_address width middle) as [[maximum tail]|] eqn:Hmax;
      [|discriminate].
    intros H. inversion H; subst.
    apply decode_address_spec in Hmax as [Hmax Hmax_encoding].
    eapply limits_with_max; eassumption.
  - intros H. inversion H; subst.
    eapply limits_without_max; eassumption.
Qed.

Lemma decode_limits_complete input a lim rest :
  limits_encoding input a lim rest ->
  decode_limits input = Some (a, lim, rest).
Proof.
  intros Henc. destruct Henc as
    [a flag input minimum rest Hflag Hmin Hmin_enc |
     a flag input minimum middle maximum rest Hflag Hmin Hmin_enc Hmax Hmax_enc];
    cbn [decode_limits]; rewrite Hflag;
    assert (decode_address a input = Some (minimum, _)) as Hdecode_min by
      (apply decode_address_spec; split; eassumption);
    rewrite Hdecode_min.
  - reflexivity.
  - assert (decode_address a middle = Some (maximum, rest)) as Hdecode_max by
      (apply decode_address_spec; split; eassumption).
    now rewrite Hdecode_max.
Qed.

Definition encode_limits (a: address_type) (lim: limits) : list byte :=
  encode_limits_flag a
    (match lim.(lim_max) with Some _ => true | None => false end) ::
  (encode_unsigned lim.(lim_min) ++
   match lim.(lim_max) with
   | None => []
   | Some maximum => encode_unsigned maximum
   end).

End AddressingBinary.
